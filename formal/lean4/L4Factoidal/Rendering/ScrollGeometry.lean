import L4Factoidal.Rendering.Fragment
import L4Factoidal.Rendering.ScrollExtent
import L4Factoidal.Rendering.LogicalAxes

/-! `scrollWidth` and `scrollHeight` (CSSOM View §6.1) from the boxes of a layout. The
arithmetic and its theorems are in `Rendering/ScrollExtent.lean`; this module finds the
boxes inside an element. -/
namespace L4Factoidal.Rendering.Layout
open DOM CSS

/-- `node` is inside `ancestor` in the tree, and is not `ancestor` itself. A loop up the
parents. -/
def insideOf (dom : Dom) (ancestor node : Nat) : Bool := Id.run do
  let mut cur := node
  for _ in [0:dom.size] do
    match (dom.get cur).parent with
    | some parent => if parent == ancestor then return true else cur := parent
    | none => return false
  return false

/-- For an element, which edges are reachable from the scroll origin. The writing
mode decides the physical axes. A reversed flex direction or wrapping direction
reverses the corresponding logical axis (CSS Overflow 3 §2.3). -/
def scrollAxes (s : Computed) : Bool × Bool :=
  let frame := Logical.Frame.of (s.pos.writingMode == .verticalRl) (s.pos.writingMode == .verticalLr)
    (s.direction == .rtl)
  let flex := s.display == .flex || s.display == .inlineFlex
  let reverseWrap := flex && s.flex.wrap == .wrapReverse
  let reverseMain := flex && s.flex.reverse
  let inlineFromEnd := frame.inlineFlip != (if s.flex.column then reverseWrap else reverseMain)
  let blockFromEnd := frame.blockFlip != (if s.flex.column then reverseMain else reverseWrap)
  if frame.vertical then (blockFromEnd,inlineFromEnd) else (inlineFromEnd,blockFromEnd)

#guard scrollAxes {} == (false,false)
#guard scrollAxes {direction := .rtl} == (true,false)
#guard scrollAxes {direction := .rtl, pos := {writingMode := .verticalRl}} == (true,true)
#guard scrollAxes {display := .flex, flex := {column := true, reverse := true, wrap := .wrapReverse}} ==
  (true,true)

/-- CSSOM View §6.1: the `scrollWidth` and `scrollHeight` of the element `node`, in whole
CSS px, from the border boxes of a layout: the element's padding box (`border` are its
border widths) extended towards the reachable edges of its descendants
(`ScrollExtent.extent`). For the root element it is the viewport, `vw` by `vh`, extended
to every box of the page. `none` when the element has no box. Cost: one pass over the
boxes, with a walk up the tree for each; nothing is computed until a script asks. -/
def scrollSize (dom : Dom) (boxes : Array Box) (border : CSS.Edges) (vw vh : Float) (node : Nat)
    (fromEnd : Bool × Bool := (false,false)) :
    Option (Float × Float) :=
  let isRoot := dom.documentElement 0 == some node
  match boxes.find? (·.source == node) with
  | none => if isRoot then some (vw,vh) else none
  | some b =>
    let leftward := !isRoot && fromEnd.1
    let upward := !isRoot && fromEnd.2
    let left := if isRoot then 0 else b.x+border.left
    let top := if isRoot then 0 else b.y+border.top
    let right := b.x+b.width-border.right
    let bottom := b.y+b.height-border.bottom
    let client : Float × Float := if isRoot then (vw,vh)
      else (max 0 (b.width-border.left-border.right),max 0 (b.height-border.top-border.bottom))
    let inside := boxes.toList.filter fun k => isRoot || (k.source != node && insideOf dom node k.source)
    -- a box of no width and no height gives nothing to scroll to (`ScrollExtent.areaEdges`)
    let edges := ScrollExtent.areaEdges (inside.map fun k =>
      let x := if leftward then right-k.x else k.x+k.width-left
      let y := if upward then bottom-k.y else k.y+k.height-top
      (LU.ofPx x,LU.ofPx y,LU.ofPx k.width,LU.ofPx k.height))
    let size := ScrollExtent.extent (LU.ofPx client.1) (LU.ofPx client.2) edges
    some ((LU.toPx size.1).round,(LU.toPx size.2).round)

end L4Factoidal.Rendering.Layout
