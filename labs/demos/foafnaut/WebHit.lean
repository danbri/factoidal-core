import WebRenderSVG
import WebRender
import L4Factoidal.Rendering.FloatFormat

/-!
# WebHit: the element under a pointer inside inline SVG

The layout's boxes end at an embedded `svg` element: its shapes have no CSS box. A
pointer on a shape targets that shape (SVG 2 §15.6, UI Events §3.1), so the element
under a point inside an outer `svg` comes from the SVG scene that the page drew, not
from the boxes. Each SVG primitive keeps the source path of the element that painted it
(`NativeSVG.Primitive.element`, a `use` instance's own `use` element), and
`NativeSVG.Scene.hitTestWith` finds the topmost primitive at the point in painter order,
with the coverage predicates of the sampler, the clips, the transforms, and the
primitive's `pointer-events`. Its path names the DOM element: source paths count the
children of the arena's nodes from the root element (`WebRender.documentNamespaceTree`
keeps every child, text and comments too).
-/

namespace WebHit
open L4Factoidal

/-- The root element of the document (`html`): the origin of SVG source paths. -/
def rootElement (dom : DOM.Dom) : Option Nat :=
  (dom.get 0).kids.find? (fun id => DOM.Dom.isHtmlElement (dom.get id) "html")

/-- The element at a source path from the root element. A path that goes on into a text
node (SVG text is lowered to glyph paths below its element) or past the children ends at
the last element it reached. -/
def nodeOfPath (dom : DOM.Dom) (path : List Nat) : Option Nat := do
  let root ← rootElement dom
  return (path.foldl (fun (state : Nat × Bool) i =>
    if !state.2 then state else
    match (dom.get state.1).kids[i]? with
    | some k => if (dom.get k).type == .element then (k,true) else (state.1,false)
    | none => (state.1,false)) (root,true)).1

/-- The outermost `svg` element that holds `id` (itself included), when `id` is SVG
content: the walk goes up while the nodes are SVG elements. -/
def outerSvg (dom : DOM.Dom) (id : Nat) : Option Nat := Id.run do
  let mut k := id
  let mut found := none
  for _ in [0:dom.size+1] do
    if k ≥ dom.size then break
    let n := dom.get k
    if !(n.type == .element && n.ns == some DOM.svgNS) then break
    if n.lname == "svg" then found := some k
    match n.parent with
    | some p => k := p
    | none => break
  return found

/-- A primitive painted by the element at `root` or by one inside it. -/
def under (root element : List Nat) : Bool := !element.isEmpty && root.isPrefixOf element

/-- The scene nodes that hold a primitive of the element at `root` or inside it, with
their groups and clips; every other paint item is dropped. -/
def keepNode (root : List Nat) : Rendering.Node → Option Rendering.Node
  | .paint item => if under root item.primitive.element then some (.paint item) else none
  | .group id t children =>
    match children.filterMap (keepNode root) with
    | [] => none
    | kept => some (.group id t kept)
  | .clipped id t clip children =>
    match children.filterMap (keepNode root) with
    | [] => none
    | kept => some (.clipped id t clip kept)
termination_by n => sizeOf n

/-- The SVG scene of the element `id` within a page scene, in page coordinates: an
admitted `NativeSVG.Scene` (painter order, compiled coverage) of its primitives only.
`rows` is at least the page row of the question, so no point of the page is outside
its viewport. -/
def sceneOf (dom : DOM.Dom) (scene : Rendering.Scene) (id : Nat) (rows : Float) : Option NativeSVG.Scene := do
  let root ← rootElement dom
  let path ← (WebRender.sourcePath dom root (dom.size+1) id []).toOption
  let tree := scene.tree.filterMap (keepNode path)
  if tree.isEmpty then none
  let height := max scene.height (rows.ceil.toUInt32.toNat + 1)
  let mapping := {scene.mapping with viewportHeight := Float.ofNat height}
  (WebRenderSVG.toScene {scene with tree, height, mapping, glyphRuns := #[], links := #[]}).toOption

/-- The SVG element under the page point (`px`, `py`) inside the outer `svg` element
`svg`: the topmost primitive there whose `pointer-events` accepts the point. `none` when
no shape takes the point (the `svg` element is then the target). -/
def svgTarget (dom : DOM.Dom) (scene : Rendering.Scene) (svg : Nat) (px py : Float) : Option Nat := do
  let native ← sceneOf dom scene svg py
  let index ← native.hitTestWith px py
  nodeOfPath dom (native.primitives.get index).element

/-- The target of a pointer at the page point (`px`, `py`): the smallest layout box that
holds the point, and inside an embedded `svg` the shape under it (`svgTarget`). The
answer has the box the offsets count from: the target's own box, else the `svg`'s. -/
def target (dom : DOM.Dom) (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box) (px py : Float) :
    Option (Nat × Rendering.Layout.Box) := do
  let inside := boxes.filter fun b => b.x ≤ px && px < b.x + b.width && b.y ≤ py && py < b.y + b.height
  let best ← inside.foldl (init := none) fun acc b => match acc with
    | some (a : Rendering.Layout.Box) => if b.width * b.height ≤ a.width * a.height then some b else some a
    | none => some b
  let node := ((outerSvg dom best.source).bind fun svg => svgTarget dom scene svg px py).getD best.source
  return (node,(boxes.find? (·.source == node)).getD best)

private def num (x : Float) : JSON.Json := .number (Rendering.FloatFormat.format x)

/-- The `nodeAt` answer: the target node and the coordinates of the pointer for its
mouse and pointer events (UI Events §5.3, CSSOM View §10): `client` in the page's
viewport, `page` in the document (`client` plus the scroll), `offset` from the target's
box (an SVG shape's box is its outer `svg`'s). `x` and `y` are in the window; the page
starts `top` rows down and is scrolled `scroll` rows. -/
def nodeAtAnswer (dom : DOM.Dom) (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (x y top scroll : Float) : JSON.Json :=
  let clientX := x
  let clientY := y - top
  let px := clientX
  let py := clientY + scroll
  match target dom scene boxes px py with
  | some (node,box) => .object [("node",.number (toString node)),("clientX",num clientX),("clientY",num clientY),
      ("pageX",num px),("pageY",num py),("offsetX",num (px-box.x)),("offsetY",num (py-box.y))]
  | none => .object [("node",.null),("clientX",num clientX),("clientY",num clientY),("pageX",num px),("pageY",num py)]

end WebHit
