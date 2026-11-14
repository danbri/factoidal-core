import L4Factoidal.Rendering.Fragment
import L4Factoidal.Rendering.ScrollExtent

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

/-- CSSOM View §6.1: the `scrollWidth` and `scrollHeight` of the element `node`, in whole
CSS px, from the border boxes of a layout: the element's padding box (`border` are its
border widths) extended to the right and bottom edges of the boxes of its descendants
(`ScrollExtent.extent`). For the root element it is the viewport, `vw` by `vh`, extended
to every box of the page. `none` when the element has no box. Cost: one pass over the
boxes, with a walk up the tree for each; nothing is computed until a script asks. -/
def scrollSize (dom : Dom) (boxes : Array Box) (border : CSS.Edges) (vw vh : Float) (node : Nat) :
    Option (Float × Float) :=
  let isRoot := dom.documentElement 0 == some node
  match boxes.find? (·.source == node) with
  | none => if isRoot then some (vw,vh) else none
  | some b =>
    let corner : Float × Float := if isRoot then (0,0) else (b.x+border.left,b.y+border.top)
    let client : Float × Float := if isRoot then (vw,vh)
      else (max 0 (b.width-border.left-border.right),max 0 (b.height-border.top-border.bottom))
    let inside := boxes.toList.filter fun k => isRoot || (k.source != node && insideOf dom node k.source)
    -- a box of no area gives nothing to scroll to (`ScrollExtent.areaEdges`)
    let edges := ScrollExtent.areaEdges (inside.map fun k =>
      (LU.ofPx (k.x+k.width-corner.1),LU.ofPx (k.y+k.height-corner.2),LU.ofPx k.width,LU.ofPx k.height))
    let size := ScrollExtent.extent (LU.ofPx client.1) (LU.ofPx client.2) edges
    some ((LU.toPx size.1).round,(LU.toPx size.2).round)

end L4Factoidal.Rendering.Layout
