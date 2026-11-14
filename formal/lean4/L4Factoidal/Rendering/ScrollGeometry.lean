import L4Factoidal.Rendering.Fragment
import L4Factoidal.Rendering.ScrollExtent
import L4Factoidal.Rendering.Scroll

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
    -- a box of no width and no height gives nothing to scroll to (`ScrollExtent.areaEdges`)
    let edges := ScrollExtent.areaEdges (inside.map fun k =>
      (LU.ofPx (k.x+k.width-corner.1),LU.ofPx (k.y+k.height-corner.2),LU.ofPx k.width,LU.ofPx k.height))
    let size := ScrollExtent.extent (LU.ofPx client.1) (LU.ofPx client.2) edges
    some ((LU.toPx size.1).round,(LU.toPx size.2).round)

/-! ### Scroll positions of scroll containers

A layout is made with every scroll container at its start. The scroll positions are kept
beside it (node, x, y in px): they are never an input of the layout, so **a scroll lays
nothing out**. `scrolledBoxes` gives the boxes where they are with those positions: each
box moved back by the positions of the scroll containers around it. It changes the place
of a box and nothing else (`scrolledBoxes_keeps`), and with no position it is the layout's
own boxes (`scrolledBoxes_none`). Cost: one pass down the tree and one over the boxes, only
when a container is scrolled. -/

/-- The scroll positions of a page: node, and how far its content is scrolled right and
down, in px. Few: the containers that are not at their start. -/
abbrev ScrollOffsets := Array (Nat × Float × Float)

/-- The position of `node`; `(0,0)` when it has none. -/
def ScrollOffsets.at (offsets : ScrollOffsets) (node : Nat) : Float × Float :=
  match offsets.find? (·.1 == node) with
  | some (_,x,y) => (x,y)
  | none => (0,0)

/-- The pass down the tree: `total[n]` is the sum of the positions of the scroll containers
that `n` is inside (not its own). One step a node; `fuel` is the number of nodes. -/
def scrollTotalsLoop (dom : Dom) (offsets : ScrollOffsets) :
    Nat → List (Nat × Float × Float) → Array (Float × Float) → Array (Float × Float)
  | 0, _, out => out
  | _+1, [], out => out
  | fuel+1, (id,x,y) :: rest, out =>
    let own := offsets.at id
    let inside := (x+own.1,y+own.2)
    scrollTotalsLoop dom offsets fuel ((dom.get id).kids.toList.map (fun k => (k,inside.1,inside.2)) ++ rest) (out.set! id (x,y))

/-- For each node, how far it is moved by the scroll containers around it. -/
def scrollTotals (dom : Dom) (offsets : ScrollOffsets) : Array (Float × Float) :=
  scrollTotalsLoop dom offsets (dom.size+1) [(0,0,0)] (Array.replicate dom.size (0,0))

/-- The boxes of a layout with the scroll positions `offsets`: each moved back by the
positions of the scroll containers it is inside. -/
def scrolledBoxes (dom : Dom) (offsets : ScrollOffsets) (boxes : Array Box) : Array Box :=
  if offsets.isEmpty then boxes else
  let totals := scrollTotals dom offsets
  boxes.map fun b =>
    let (dx,dy) := totals.getD b.source (0,0)
    {b with x := b.x-dx, y := b.y-dy}

/-- Kind: frame. Says: with no scroll position the boxes are the layout's own. -/
theorem scrolledBoxes_none (dom : Dom) (boxes : Array Box) : scrolledBoxes dom #[] boxes = boxes := rfl

/-- Kind: frame. Says: **a scroll changes where boxes are and nothing else**: as many
boxes, in the same order, each for the same node and of the same size. -/
theorem scrolledBoxes_keeps (dom : Dom) (offsets : ScrollOffsets) (boxes : Array Box) :
    (scrolledBoxes dom offsets boxes).size = boxes.size ∧
    (scrolledBoxes dom offsets boxes).map (fun b => (b.source,b.width,b.height)) =
      boxes.map (fun b => (b.source,b.width,b.height)) := by
  unfold scrolledBoxes
  split
  · exact ⟨rfl, rfl⟩
  · simp [Array.map_map, Function.comp_def]

/-- The scroll position `wanted` of `node` as the layout allows it (CSSOM View §4.2: a
position is clamped to the scrolling area): between 0 and what of the scrollable overflow
(`scrollSize`) is past the padding box, on each axis, in whole layout units
(`Scroll.clamp`). `(0,0)` for an element with no box. -/
def scrollPosition (dom : Dom) (boxes : Array Box) (border : CSS.Edges) (vw vh : Float) (node : Nat)
    (wanted : Float × Float) : Float × Float :=
  match boxes.find? (·.source == node), scrollSize dom boxes border vw vh node with
  | some b, some (w,h) =>
    let clientW := max 0 (b.width-border.left-border.right)
    let clientH := max 0 (b.height-border.top-border.bottom)
    (LU.toPx (Scroll.clamp (LU.ofPx w) (LU.ofPx clientW) (LU.ofPx wanted.1)),
     LU.toPx (Scroll.clamp (LU.ofPx h) (LU.ofPx clientH) (LU.ofPx wanted.2)))
  | _, _ => (0,0)

end L4Factoidal.Rendering.Layout
