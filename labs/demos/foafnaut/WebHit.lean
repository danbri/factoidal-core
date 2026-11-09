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

The same scene answers the bounds of an SVG element for page scripts
(`getBoundingClientRect`, `getBBox`): the union of the bounds of its primitives.
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

/-! ### Bounds of an SVG element -/

/-- A rectangle as `(x0, y0, x1, y1)`. -/
abbrev Bounds := Float × Float × Float × Float

def Bounds.union (a b : Bounds) : Bounds := (min a.1 b.1,min a.2.1 b.2.1,max a.2.2.1 b.2.2.1,max a.2.2.2 b.2.2.2)

private def joined (a : Option Bounds) (b : Bounds) : Option Bounds := some ((a.map (·.union b)).getD b)

private def ofPoints : List Rendering.Point → Option Bounds
  | [] => none
  | p :: ps => some (ps.foldl (fun (b : Bounds) q => b.union (q.x,q.y,q.x,q.y)) (p.x,p.y,p.x,p.y))

private def segmentPoints : Rendering.PathSegment → List Rendering.Point
  | .line e => [e]
  | .quadratic c e => [c,e]
  | .cubic c d e => [c,d,e]
  | .arc rx ry _ _ _ e => [⟨e.x-rx,e.y-ry⟩,⟨e.x+rx,e.y+ry⟩]

/-- The bounds of a geometry in its own frame: exact for rectangles, circles, ellipses,
lines and polygons; for a path, its points and control points (a cover of the curve). -/
def geometryBounds : Rendering.Geometry → Option Bounds
  | .rect x y w h => some (min x (x+w),min y (y+h),max x (x+w),max y (y+h))
  | .circle cx cy r => some (cx-r,cy-r,cx+r,cy+r)
  | .ellipse cx cy rx ry => some (cx-rx,cy-ry,cx+rx,cy+ry)
  | .line x1 y1 x2 y2 => some (min x1 x2,min y1 y2,max x1 x2,max y1 y2)
  | .polygon points => ofPoints points
  | .path contours => ofPoints (contours.flatMap fun
      | .empty _ => []
      | .path start segments _ => start :: segments.flatMap segmentPoints)

/-- The bounds of a rectangle after a transform: of its four corners. -/
def Bounds.through (t : Rendering.Transform) (b : Bounds) : Bounds :=
  let at_ := fun (x y : Float) => Math.Affine2.applyPoint .float t x y
  let (x0,y0,x1,y1) := b
  let corners := [at_ x0 y0,at_ x1 y0,at_ x0 y1,at_ x1 y1]
  corners.foldl (fun (r : Bounds) (x,y) => r.union (x,y,x,y)) (let (x,y) := at_ x0 y0; (x,y,x,y))

/-- The bounds of the element at source path `path`, from the primitives it and its
descendants painted in `tree`: in the page (`getBoundingClientRect`), and in its own user
space (`getBBox`, SVG 2 §8.10). For the user space a primitive of a descendant goes
through the groups between the element and it: one group for each container element
between them (`g`, `svg`, `use`, and the runs of lowered text), then its own transform.
A primitive whose groups do not count so is left out of the user-space bounds. -/
def elementBounds (tree : List Rendering.Node) (path : List Nat) : Option Bounds × Option Bounds := Id.run do
  let mut work : List (Rendering.Node × List Rendering.Transform) := tree.map (·,[])
  let mut page : Option Bounds := none
  let mut user : Option Bounds := none
  for _ in [0:4194304] do
    match work with
    | [] => break
    | (node,stack) :: rest =>
      work := rest
      match node with
      | .group _ t children | .clipped _ t _ children => work := children.map (·,t :: stack) ++ work
      | .paint item =>
        let p := item.primitive
        if !under path p.element then continue
        let some local_ := geometryBounds p.geometry | continue
        let toPage := stack.foldl (fun acc s => Math.Affine2.compose .float s acc) p.transform
        page := joined page (local_.through toPage)
        if p.element == path then user := joined user local_
        else
          let between := p.element.length - path.length - 1
          if stack.length ≥ between then
            let toUser := (stack.take between).foldl (fun acc s => Math.Affine2.compose .float s acc) p.transform
            user := joined user (local_.through toUser)
  return (page,user)

/-- `elementBounds` of the SVG element `id` of the arena. -/
def boundsOf (dom : DOM.Dom) (scene : Rendering.Scene) (id : Nat) : Option Bounds × Option Bounds := Id.run do
  let some root := rootElement dom | return (none,none)
  let .ok path := WebRender.sourcePath dom root (dom.size+1) id [] | return (none,none)
  return elementBounds scene.tree path

private def num (x : Float) : JSON.Json := .number (Rendering.FloatFormat.format x)

/-- The `nodeAt` answer: the target node and the coordinates of the pointer for its
mouse and pointer events (UI Events §5.3, CSSOM View §10): `client` in the page's
viewport, `page` in the document (`client` plus the scroll), `offset` from the target's
box (an SVG shape's box is its outer `svg`'s). `x` and `y` are in the window; the page
starts `top` rows down and is scrolled `scroll` rows. The window is in device pixels; the
answer's coordinates are CSS pixels, at `ratio` device pixels for each (1 by default). -/
def nodeAtAnswer (dom : DOM.Dom) (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (x y top scroll : Float) (ratio : Float := 1) : JSON.Json :=
  let clientX := x
  let clientY := y - top
  let px := clientX
  let py := clientY + scroll
  let css := fun (v : Float) => num (if ratio == 1 then v else v / ratio)
  match target dom scene boxes px py with
  | some (node,box) => .object [("node",.number (toString node)),("clientX",css clientX),("clientY",css clientY),
      ("pageX",css px),("pageY",css py),("offsetX",css (px-box.x)),("offsetY",css (py-box.y))]
  | none => .object [("node",.null),("clientX",css clientX),("clientY",css clientY),("pageX",css px),("pageY",css py)]

end WebHit
