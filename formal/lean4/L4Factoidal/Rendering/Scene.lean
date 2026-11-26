import L4Factoidal.Math.Affine
import L4Factoidal.Rendering.Path

/-! Shared retained vector model for SVG and HTML layout. Coordinates use
binary64 Float. The native GPU adapter uses binary32; equality of rasterized
pixels does not follow from the exact structural adapter theorems. -/
namespace L4Factoidal.Rendering

abbrev Transform := Math.Affine2 Float
def identity : Transform := Math.Affine2.identity .float
structure Color where
  r : Float
  g : Float
  b : Float
  deriving Repr
/-- Path controls remain canonical until checked backend compilation. -/
inductive Geometry where
  | rect (x y width height : Float)
  | circle (cx cy radius : Float)
  | ellipse (cx cy rx ry : Float)
  | line (x1 y1 x2 y2 : Float)
  | polygon (points : List Point)
  | path (contours : List Contour)
  deriving Repr
/-- Limit on the stops of one gradient. The shader walks them for each sample. -/
def maxGradientStops : Nat := 64
/-- SVG Tiny 1.2 §11.16: colour and opacity at an offset along the gradient. -/
structure GradientStop where
  offset : Float
  color : Color
  opacity : Float
  deriving Repr
/-- The gradient vector or circle, in the gradient's own coordinate system. -/
inductive GradientShape where
  | linear (x1 y1 x2 y2 : Float)
  | radial (cx cy r : Float)
  deriving Repr
/-- SVG Tiny 1.2 §11.3: the paint after an IRI, used when the server paints nothing. -/
inductive FallbackPaint where
  | none | current | solid (color : Color)
  deriving Repr
/-- A paint server as the document states it, for any element that uses it. -/
structure Gradient where
  shape : GradientShape
  boundingBoxUnits : Bool
  transform : Transform := identity
  stops : List GradientStop
  fallback : FallbackPaint := .none
  /-- From the primitive's local frame to the user space of the painted element.
      It differs from the identity for a glyph, which is one primitive of a text. -/
  frame : Transform := identity
  /-- Bounding box x, y, width, height in `frame`, when the primitive's own bounds
      are not the element's. -/
  box : Option (Float × Float × Float × Float) := none
  deriving Repr
/-- A gradient lowered for one primitive: `map` goes from the primitive's local
frame to a space where the parameter is the x coordinate (linear) or the
distance from the origin (radial). -/
structure GradientRecord where
  map : Transform
  radial : Bool
  stops : List GradientStop
  deriving Repr
/-- A decoded raster image: rows from the top, four bytes for each pixel: red,
green, blue, opacity, not premultiplied. -/
structure Bitmap where
  width : Nat
  height : Nat
  rgba : ByteArray
instance : Repr Bitmap where
  reprPrec b _ := .text s!"Bitmap {b.width}x{b.height}"
/-- A raster image as paint. `map` goes from the primitive's local frame to pixel
coordinates of the bitmap: pixel (i,j) covers i..i+1 and j..j+1. Two records with
one `id` have one bitmap, so the paint table holds its pixels once. -/
structure ImageRecord where
  map : Transform
  id : Nat
  bitmap : Bitmap
  repeatX : Bool := false
  repeatY : Bool := false
  deriving Repr
inductive Paint where
  | none | solid (color : Color) | current
  | gradient (source : Gradient)
  /-- A lowered gradient and its word offset in the paint table of the scene. -/
  | gradientRecord (cursor : Nat) (record : GradientRecord)
  | image (record : ImageRecord)
  /-- An image and the word offset of its header in the paint table of the scene. -/
  | imageRecord (cursor : Nat) (record : ImageRecord)
  deriving Repr

def gradientRecordHeaderWords : Nat := 8
def gradientStopWords : Nat := 5
def GradientStop.words (s : GradientStop) : List Float :=
  [s.offset,s.color.r,s.color.g,s.color.b,s.opacity]
/-- Wire form: the map's x row and the radial flag, its y row and the stop count,
then the stops. The shader reads this layout. -/
def GradientRecord.words (g : GradientRecord) : List Float :=
  [g.map.a,g.map.c,g.map.e,if g.radial then 1 else 0,
   g.map.b,g.map.d,g.map.f,Float.ofNat g.stops.length] ++ g.stops.flatMap GradientStop.words
def GradientRecord.wordCount (g : GradientRecord) : Nat :=
  gradientRecordHeaderWords+g.stops.length*gradientStopWords
theorem GradientRecord.words_length (g : GradientRecord) : g.words.length = g.wordCount := by
  have stops : (g.stops.flatMap GradientStop.words).length = g.stops.length*gradientStopWords := by
    induction g.stops with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.flatMap_cons,List.length_append,ih,List.length_cons,Nat.add_mul]
      simp [GradientStop.words,gradientStopWords,Nat.add_comm]
  simp [GradientRecord.words,GradientRecord.wordCount,stops,gradientRecordHeaderWords]
  omega

/-- SVG Tiny 1.2 §11.16: each offset clamps to 0..1, and to no less than any
earlier offset. -/
def normalizeStops (stops : List GradientStop) : List GradientStop :=
  (stops.foldl (fun (state : List GradientStop × Float) stop =>
    let offset := max state.2 (max 0 (min 1 stop.offset))
    ({stop with offset}::state.1,offset)) ([],0)).1.reverse
private theorem normalizeStops_fold_length (stops : List GradientStop)
    (state : List GradientStop × Float) :
    (stops.foldl (fun (state : List GradientStop × Float) stop =>
      let offset := max state.2 (max 0 (min 1 stop.offset))
      ({stop with offset}::state.1,offset)) state).1.length = state.1.length+stops.length := by
  induction stops generalizing state with
  | nil => rfl
  | cons head tail ih => simp [List.foldl_cons,ih]; omega
theorem normalizeStops_length (stops : List GradientStop) :
    (normalizeStops stops).length = stops.length := by
  simpa [normalizeStops] using normalizeStops_fold_length stops ([],0)

private def GradientStop.rgba (s : GradientStop) : List Float :=
  [s.color.r,s.color.g,s.color.b,s.opacity]
private def mixStops (a b : GradientStop) (f : Float) : List Float :=
  [a.color.r*(1-f)+b.color.r*f,a.color.g*(1-f)+b.color.g*f,
   a.color.b*(1-f)+b.color.b*f,a.opacity*(1-f)+b.opacity*f]
/-- Pad spread. Colour and opacity interpolate as stated, not premultiplied. Of
stops at one offset, the last one controls that offset. -/
private def stopValue (t : Float) (current : GradientStop) : List GradientStop → List Float
  | [] => current.rgba
  | next::rest =>
    if t >= next.offset then stopValue t next rest
    else if t > current.offset then mixStops current next ((t-current.offset)/(next.offset-current.offset))
    else current.rgba
/-- Colour and opacity at a point of the primitive's local frame, as `[r,g,b,a]`.
No stops give zero; lowering does not make such a record. -/
def GradientRecord.colorAt (g : GradientRecord) (x y : Float) : List Float :=
  let (u,v) := Math.Affine2.applyPoint .float g.map x y
  let t := if g.radial then Float.sqrt (u*u+v*v) else u
  match g.stops with
  | [] => [0,0,0,0]
  | first::rest => stopValue t first rest
/-- SVG Tiny 1.2 §11.16: one stop paints one colour at every point. -/
theorem GradientRecord.colorAt_single_stop (map : Transform) (radial : Bool) (stop : GradientStop)
    (x y : Float) :
    GradientRecord.colorAt ⟨map,radial,[stop]⟩ x y =
      [stop.color.r,stop.color.g,stop.color.b,stop.opacity] := rfl

/-- Linear parameter, or unit circle, from gradient coordinates. `none` means a
degenerate vector or circle: SVG Tiny 1.2 §11.15 paints the last stop's colour. -/
private def GradientShape.unitMap : GradientShape → Option (Transform × Bool)
  | .linear x1 y1 x2 y2 =>
    let dx := x2-x1; let dy := y2-y1; let squared := dx*dx+dy*dy
    if squared == 0 then none
    else some (⟨dx/squared,0,dy/squared,0,-(x1*dx+y1*dy)/squared,0⟩,false)
  | .radial cx cy r =>
    if r == 0 then none else some (⟨1/r,0,0,1/r,-cx/r,-cy/r⟩,true)
/-- Lower a gradient for a primitive with these local bounds. `none` means that
the server paints nothing: the box of a bounding-box gradient has no width or no
height, or its transform is singular. Stops must not be empty. -/
def Gradient.lower (g : Gradient) (bounds : Float × Float × Float × Float) : Option GradientRecord := do
  let (x,y,w,h) := g.box.getD bounds
  let toUser : Transform ← if g.boundingBoxUnits then
      if w <= 0 || h <= 0 then none
      else pure ⟨1/w,0,0,1/h,-x/w,-y/h⟩
    else pure identity
  let inverse ← Math.Affine2.inverse? .float g.transform
  let toGradient := Math.Affine2.compose .float inverse (Math.Affine2.compose .float toUser g.frame)
  match g.shape.unitMap with
  | some (unit,radial) =>
    pure ⟨Math.Affine2.compose .float unit toGradient,radial,g.stops⟩
  | none => pure ⟨identity,false,g.stops.getLast?.toList⟩

def imageRecordHeaderWords : Nat := 9
/-- Wire form: the map's x row and the width, its y row and the height, then the
word offset of the pixels from the start of the paint table. A negative dimension
marks a repeating axis. Each pixel is one word, red in the low byte. -/
def ImageRecord.words (g : ImageRecord) (pixels : Nat) : List Float :=
  let width := Float.ofNat g.bitmap.width
  let height := Float.ofNat g.bitmap.height
  [g.map.a,g.map.c,g.map.e,if g.repeatX then -width else width,
   g.map.b,g.map.d,g.map.f,if g.repeatY then -height else height,Float.ofNat pixels]
theorem ImageRecord.words_length (g : ImageRecord) (pixels : Nat) :
    (g.words pixels).length = imageRecordHeaderWords := rfl

/-- The pixel as four words, in one word for the table. -/
def Bitmap.word (b : Bitmap) (index : Nat) : Nat :=
  let at_ := fun (k : Nat) => (b.rgba.get! (index*4+k)).toNat
  at_ 0+at_ 1*256+at_ 2*65536+at_ 3*16777216

/-- The pixels of the rectangle from column `x0` and row `y0`, `w` wide and `h` high, as a bitmap
of their own; the rectangle is first cut to the bitmap. A record that draws the result samples
only these pixels: at its edges the sampler takes the edge pixel, not a pixel beyond it. The
nine parts of a border image are drawn so (CSS Backgrounds 3 §6.2), each from its own slice. -/
def Bitmap.crop (b : Bitmap) (x0 y0 w h : Nat) : Bitmap := Id.run do
  let x0 := min x0 b.width
  let y0 := min y0 b.height
  let w := min w (b.width-x0)
  let h := min h (b.height-y0)
  let mut out := ByteArray.emptyWithCapacity (w*h*4)
  for j in [0:h] do
    let start := ((y0+j)*b.width+x0)*4
    out := b.rgba.copySlice start out out.size (w*4)
  return {width := w, height := h, rgba := out}

#guard let b : Bitmap := ⟨3,2,⟨#[1,1,1,1, 2,2,2,2, 3,3,3,3, 4,4,4,4, 5,5,5,5, 6,6,6,6]⟩⟩
  let c := b.crop 1 0 2 2
  c.width == 2 && c.height == 2 && c.rgba.toList == [2,2,2,2, 3,3,3,3, 5,5,5,5, 6,6,6,6]
#guard let b : Bitmap := ⟨3,2,⟨#[1,1,1,1, 2,2,2,2, 3,3,3,3, 4,4,4,4, 5,5,5,5, 6,6,6,6]⟩⟩
  let c := b.crop 2 1 5 5
  c.width == 1 && c.height == 1 && c.rgba.toList == [6,6,6,6]

/-- Index of a sample on one axis: the nearest pixel beyond the edge. -/
private def edgeIndex (v : Float) (size : Nat) : Nat :=
  if v <= 0 then 0 else min (size-1) v.toUInt64.toNat
/-- Premultiplied colour of one pixel, in 0..1. -/
private def Bitmap.texel (b : Bitmap) (x y : Nat) : Float × Float × Float × Float :=
  let i := (y*b.width+x)*4
  let a := (b.rgba.get! (i+3)).toFloat/255
  ((b.rgba.get! i).toFloat/255*a,(b.rgba.get! (i+1)).toFloat/255*a,
   (b.rgba.get! (i+2)).toFloat/255*a,a)
private def mixTexel (p q : Float × Float × Float × Float) (f : Float) : Float × Float × Float × Float :=
  (p.1*(1-f)+q.1*f,p.2.1*(1-f)+q.2.1*f,p.2.2.1*(1-f)+q.2.2.1*f,p.2.2.2*(1-f)+q.2.2.2*f)
/-- Select the position within one tile before sampling texels. Subtracting a
floored multiple also handles points before the origin. -/
private def tileCoordinate (repeats : Bool) (size : Nat) (p : Float) : Float :=
  if repeats then
    let period := Float.ofNat size
    p - (p/period).floor*period
  else p

#guard tileCoordinate true 69 (-0.5) == 68.5
#guard tileCoordinate true 69 69.5 == 0.5
#guard tileCoordinate false 69 69.5 == 69.5

/-- Colour and opacity at a point of the primitive's local frame, as `[r,g,b,a]`:
bilinear on premultiplied pixels with edge sampling within each tile. The shader
states the same steps in `imageSample`. -/
def ImageRecord.colorAt (g : ImageRecord) (x y : Float) : List Float :=
  let (u,v) := Math.Affine2.applyPoint .float g.map x y
  let u := tileCoordinate g.repeatX g.bitmap.width u
  let v := tileCoordinate g.repeatY g.bitmap.height v
  -- An image drawn at its own size on whole pixels (unit scale, no rotation, a whole-pixel
  -- offset) shows its pixels as they are, as browsers draw it: each sample takes the pixel it
  -- falls in. Before 2026-11-22 bilinear sampling at the raster's sub-pixel samples mixed each
  -- pixel with its neighbours (a 2 by 2 checker drew 78% of each colour).
  if g.map.a == 1 && g.map.b == 0 && g.map.c == 0 && g.map.d == 1 &&
      g.map.e == g.map.e.round && g.map.f == g.map.f.round then
    let b := g.bitmap
    let (r,gr,bl,a) := b.texel (edgeIndex u.floor b.width) (edgeIndex v.floor b.height)
    if a <= 0 then [0,0,0,0] else [r/a,gr/a,bl/a,a]
  else
  let fx := u-0.5
  let fy := v-0.5
  let x0 := fx.floor
  let y0 := fy.floor
  let b := g.bitmap
  let left := edgeIndex x0 b.width
  let right := edgeIndex (x0+1) b.width
  let top := edgeIndex y0 b.height
  let bottom := edgeIndex (y0+1) b.height
  let upper := mixTexel (b.texel left top) (b.texel right top) (fx-x0)
  let lower := mixTexel (b.texel left bottom) (b.texel right bottom) (fx-x0)
  let (r,gr,bl,a) := mixTexel upper lower (fy-y0)
  if a <= 0 then [0,0,0,0] else [r/a,gr/a,bl/a,a]

inductive FillRule where | nonzero | evenodd
  deriving Repr, BEq
inductive LineCap where | butt | round | square
  deriving Repr, BEq
inductive LineJoin where | miter | round | bevel
  deriving Repr, BEq
structure Length where
  value : Float
  percentage : Bool
  deriving Repr
inductive StrokePiece where
  | strip (first last : Point)
  | disk (center : Point) (radius : Float)
  | triangle (a b c : Point)
  deriving Repr
structure Style where
  fill : Paint := .solid ⟨0,0,0⟩
  stroke : Paint := .none
  currentColor : Color := ⟨0,0,0⟩
  strokeWidth : Float := 1
  dashArray : List Length := []
  dashOffset : Length := ⟨0,false⟩
  fillOpacity : Float := 1
  strokeOpacity : Float := 1
  visible : Bool := true
  rule : FillRule := .nonzero
  lineCap : LineCap := .butt
  lineJoin : LineJoin := .miter
  miterLimit : Float := 4
  /-- SVG 2 §15.6 `pointer-events` of an SVG shape (HTML paint keeps the initial
  value). It changes no pixel; hit testing reads it. -/
  pointerEvents : String := "visiblePainted"
  deriving Repr
/-- Rectangular clip in an independent local frame. Content and clip frames
remain distinct so a viewport can clip before a viewBox mapping. -/
structure ClipRect where
  x : Float
  y : Float
  width : Float
  height : Float
  transform : Transform := identity
  deriving Repr

def ClipRect.lowerUnder (parent : Transform) (clip : ClipRect) : ClipRect :=
  {clip with transform := Math.Affine2.compose .float parent clip.transform}

structure Primitive where
  geometry : Geometry
  style : Style := {}
  opacity : Float := 1
  transform : Transform := identity
  dashParts : Option (List StrokePiece) := none
  groupPath : List (Option String) := []
  clips : List ClipRect := []
  pathLength : Option Float := none
  /-- The source path of the SVG element that painted it, from the root element of its
  document (`NativeSVG.Primitive.element`); empty for HTML paint. Not drawn. -/
  element : List Nat := []
  deriving Repr
structure PaintItem where
  /-- Index in the source DOM arena, shared by boxes, glyphs and input targets. -/
  source : Option Nat := none
  primitive : Primitive
  deriving Repr
inductive Node where
  | paint (item : PaintItem)
  | group (id : Option String) (transform : Transform) (children : List Node)
  | clipped (id : Option String) (contentTransform : Transform) (clip : ClipRect) (children : List Node)
  deriving Repr
structure Mapping where
  sx : Float := 1
  sy : Float := 1
  tx : Float := 0
  ty : Float := 0
  minX : Float := 0
  minY : Float := 0
  viewportWidth : Float
  viewportHeight : Float
  deriving Repr
/-- Glyph positions preserve source clusters even when rasterized to vector
cells by the temporary ASCII font adapter. Font-backed shaping is separate. -/
structure Glyph where
  index : Nat
  x : Float
  y : Float
  advance : Float
  clusterStart : Nat
  clusterEnd : Nat
  deriving Repr
structure GlyphRun where
  source : Nat
  font : String
  fontSize : Float
  text : String
  glyphs : Array Glyph
  /-- First source and cluster of this layout line (or an atomic source at its
  start). Independent of vertical alignment, transforms and device scale. -/
  lineKey : Option (Nat × Nat) := none
  deriving Repr
/-- An inline/block link fragment in scene coordinates. Source is the stable
DOM anchor node, not a paint-list index. The href is data, never navigation. -/
structure LinkRegion where
  sourceNode : Nat
  href : String
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr

def LinkRegion.contains (r : LinkRegion) (x y : Float) : Bool :=
  r.width > 0 && r.height > 0 && x >= r.x && y >= r.y &&
    x < r.x+r.width && y < r.y+r.height

def hitLink (regions : List LinkRegion) (x y : Float) : Option LinkRegion :=
  regions.reverse.find? (fun r => r.contains x y)

theorem hitLink_mem (regions : List LinkRegion) (x y : Float) (target : LinkRegion)
    (hit : hitLink regions x y = some target) : target ∈ regions := by
  have member := List.mem_of_find?_eq_some hit
  simpa using member

/-- The region moved down the page by `f` (a band of the page, a page below a chrome):
the same source, address, column and size. -/
def LinkRegion.moveY (f : Float → Float) (r : LinkRegion) : LinkRegion := {r with y := f r.y}

/-- Every region moved by `f`, in the same order. `WebDocument.pageLayer` and
`WebShell.compose` move the page's links with this. -/
def moveLinks (f : Float → Float) (regions : Array LinkRegion) : Array LinkRegion :=
  regions.map (LinkRegion.moveY f)

/-- A hit on moved regions is the hit on the regions themselves at another row, when each
region holds the point after the move exactly when it held the point at `y'` before it. -/
theorem hitLink_moveY (f : Float → Float) (regions : List LinkRegion) (x y y' : Float)
    (agree : ∀ r ∈ regions, (r.moveY f).contains x y = r.contains x y') :
    hitLink (regions.map (LinkRegion.moveY f)) x y = (hitLink regions x y').map (LinkRegion.moveY f) := by
  unfold hitLink
  rw [← List.map_reverse]
  have agree' : ∀ r ∈ regions.reverse, (r.moveY f).contains x y = r.contains x y' := by
    intro r m; exact agree r (List.mem_reverse.mp m)
  generalize regions.reverse = rs at agree'
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons]
    rw [agree' r (List.mem_cons_self ..)]
    split
    · rfl
    · exact ih (fun q m => agree' q (List.mem_cons_of_mem _ m))

structure Scene where
  width : Nat
  height : Nat
  mapping : Mapping
  tree : List Node
  glyphRuns : Array GlyphRun := #[]
  links : Array LinkRegion := #[]
  deriving Repr

def Primitive.lowerUnder (parent : Transform) (groups : List (Option String))
    (p : Primitive) : Primitive :=
  {p with transform := Math.Affine2.compose .float parent p.transform,
          groupPath := groups ++ p.groupPath, clips := p.clips.map (ClipRect.lowerUnder parent)}
def Primitive.addClip (clip : ClipRect) (primitive : Primitive) : Primitive :=
  {primitive with clips := clip :: primitive.clips}

def PaintItem.addClip (clip : ClipRect) (item : PaintItem) : PaintItem :=
  {item with primitive := item.primitive.addClip clip}

mutual
  def Node.lower (parent : Transform) (groups : List (Option String)) : Node → List PaintItem
    | .paint item => [{item with primitive := item.primitive.lowerUnder parent groups}]
    | .group id transform children =>
        Node.lowerList (Math.Affine2.compose .float parent transform) (groups ++ [id]) children
    | .clipped id content clip children =>
        (Node.lowerList (Math.Affine2.compose .float parent content) (groups ++ [id]) children).map
          (PaintItem.addClip (clip.lowerUnder parent))
  termination_by node => sizeOf node
  def Node.lowerList (parent : Transform) (groups : List (Option String)) : List Node → List PaintItem
    | [] => []
    | node :: rest => node.lower parent groups ++ Node.lowerList parent groups rest
  termination_by nodes => sizeOf nodes
end
/-- A pending sibling list and its inherited frames. Reversed group/clip paths
share their tails across sibling frames; only a paint item needs forward order. -/
private structure LowerFrame where
  nodes : List Node
  parent : Transform
  groupsRev : List (Option String)
  clipsRev : List ClipRect

private def addClips (clips : List ClipRect) (item : PaintItem) : PaintItem :=
  {item with primitive := {item.primitive with clips := clips ++ item.primitive.clips}}

-- These definitions are proof-only: the executable loop never traverses a
-- subtree to measure it, or calls the recursive reference lowering functions.
private noncomputable def lowerWeight (pending : List LowerFrame) : Nat :=
  ((pending.map fun frame => 1 + sizeOf frame.nodes)).sum

private noncomputable def lowerPending (pending : List LowerFrame) : List PaintItem :=
  pending.flatMap fun frame =>
    (Node.lowerList frame.parent frame.groupsRev.reverse frame.nodes).map
      (addClips frame.clipsRev.reverse)

/-- Explicit depth-first work stack. Each recursive call is a direct tail call;
neither a sibling fold nor a clip map calls back into the traversal. -/
private def lowerLoop (pending : List LowerFrame) (acc : List PaintItem) : List PaintItem :=
  match pending with
  | [] => acc.reverse
  | ⟨[],_,_,_⟩ :: rest => lowerLoop rest acc
  | ⟨.paint item :: siblings,parent,groups,clips⟩ :: rest =>
    lowerLoop (⟨siblings,parent,groups,clips⟩ :: rest)
      (addClips clips.reverse {item with primitive := item.primitive.lowerUnder parent groups.reverse} :: acc)
  | ⟨.group id transform children :: siblings,parent,groups,clips⟩ :: rest =>
    lowerLoop (⟨children,Math.Affine2.compose .float parent transform,id :: groups,clips⟩ ::
      ⟨siblings,parent,groups,clips⟩ :: rest) acc
  | ⟨.clipped id content clip children :: siblings,parent,groups,clips⟩ :: rest =>
    lowerLoop (⟨children,Math.Affine2.compose .float parent content,id :: groups,
      clip.lowerUnder parent :: clips⟩ :: ⟨siblings,parent,groups,clips⟩ :: rest) acc
termination_by lowerWeight pending
decreasing_by
  all_goals simp_all [lowerWeight, List.cons.sizeOf_spec, Node.paint.sizeOf_spec,
    Node.group.sizeOf_spec, Node.clipped.sizeOf_spec]
  all_goals omega

private theorem addClips_addClip (clips : List ClipRect) (clip : ClipRect) (item : PaintItem) :
    addClips clips (item.addClip clip) = addClips (clips ++ [clip]) item := by
  simp [addClips, PaintItem.addClip, Primitive.addClip, List.append_assoc]

private theorem addClips_nil : addClips [] = id := by
  funext item
  cases item with
  | mk source primitive => cases primitive; rfl

private theorem lowerLoop_eq (pending : List LowerFrame) (acc : List PaintItem) :
    lowerLoop pending acc = acc.reverse ++ lowerPending pending := by
  induction pending, acc using lowerLoop.induct with
  | case1 acc => simp [lowerLoop, lowerPending]
  | case2 acc parent groups clips rest ih =>
    rw [lowerLoop, ih]
    simp [lowerPending, Node.lowerList]
  | case3 acc item siblings parent groups clips rest ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [lowerLoop, ih]
    simp [lowerPending, Node.lowerList, Node.lower, List.append_assoc]
  | case4 acc id transform children siblings parent groups clips rest ih =>
    rw [lowerLoop, ih]
    simp [lowerPending, Node.lowerList, Node.lower, List.map_append, List.append_assoc]
  | case5 acc id content clip children siblings parent groups clips rest ih =>
    rw [lowerLoop, ih]
    simp [lowerPending, Node.lowerList, Node.lower, List.map_append, List.map_map,
      Function.comp_def, addClips_addClip, List.append_assoc]

def Node.lowerListTR (parent : Transform) (groups : List (Option String))
    (nodes : List Node) : List PaintItem :=
  lowerLoop [⟨nodes,parent,groups.reverse,[]⟩] []

def Node.lowerTR (parent : Transform) (groups : List (Option String))
    (node : Node) : List PaintItem :=
  Node.lowerListTR parent groups [node]

theorem Node.lowerListTR_eq (nodes : List Node) (parent : Transform)
    (groups : List (Option String)) :
    Node.lowerListTR parent groups nodes = Node.lowerList parent groups nodes := by
  simp [Node.lowerListTR, lowerLoop_eq, lowerPending, addClips_nil]

theorem Node.lowerTR_eq (node : Node) :
    ∀ parent groups, node.lowerTR parent groups = node.lower parent groups := by
  intro parent groups
  simp [Node.lowerTR, Node.lowerListTR_eq, Node.lowerList]

@[csimp] theorem Node.lower_eq_lowerTR : @Node.lower = @Node.lowerTR := by
  funext parent groups node
  exact (Node.lowerTR_eq node parent groups).symm

@[csimp] theorem Node.lowerList_eq_lowerListTR : @Node.lowerList = @Node.lowerListTR := by
  funext parent groups nodes
  exact (Node.lowerListTR_eq nodes parent groups).symm


/-- Partitioning an ordered scene into batches preserves its precise painter
list. This theorem does not permit reordering or Float reassociation. -/
theorem Node.lowerList_append (parent : Transform) (groups : List (Option String))
    (a b : List Node) :
    Node.lowerList parent groups (a ++ b) =
      Node.lowerList parent groups a ++ Node.lowerList parent groups b := by
  induction a with
  | nil => simp [Node.lowerList]
  | cons n ns ih => simp [Node.lowerList, ih, List.append_assoc]

end L4Factoidal.Rendering

namespace L4Factoidal.Rendering.Corners

/-- Quantities in nonnegative layout units. -/
structure Radius where
  x : Nat := 0
  y : Nat := 0
  deriving Inhabited, Repr, BEq

structure Radii where
  topLeft : Radius := {}
  topRight : Radius := {}
  bottomRight : Radius := {}
  bottomLeft : Radius := {}
  deriving Inhabited, Repr, BEq

structure Scale where
  num : Nat
  den : Nat
  positive : 0 < den

def Scale.atMost (a b : Scale) : Prop :=
  a.num * b.den ≤ b.num * a.den

def Scale.min (a b : Scale) : Scale :=
  if a.num * b.den ≤ b.num * a.den then a else b

theorem Scale.refl (s : Scale) : s.atMost s := Nat.le_refl _

theorem Scale.min_le_left (a b : Scale) : (a.min b).atMost a := by
  unfold Scale.min
  split
  · exact a.refl
  · rename_i h
    exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem Scale.min_le_right (a b : Scale) : (a.min b).atMost b := by
  unfold Scale.min
  split
  · assumption
  · exact b.refl

theorem Scale.trans {a b c : Scale} (ab : a.atMost b) (bc : b.atMost c) :
    a.atMost c := by
  unfold Scale.atMost at *
  apply Nat.le_of_mul_le_mul_right (c := b.den) _ b.positive
  calc
    a.num * c.den * b.den = (a.num * b.den) * c.den := by ac_rfl
    _ ≤ (b.num * a.den) * c.den := Nat.mul_le_mul_right _ ab
    _ = (b.num * c.den) * a.den := by ac_rfl
    _ ≤ (c.num * b.den) * a.den := Nat.mul_le_mul_right _ bc
    _ = c.num * a.den * b.den := by ac_rfl

def Scale.fitSide (limit total : Nat) : Scale :=
  if h : total ≤ limit then ⟨1,1,by decide⟩ else ⟨limit,total,by omega⟩

def Scale.fits (s : Scale) (limit total : Nat) : Prop :=
  s.num * total ≤ s.den * limit

theorem Scale.fitSide_fits (limit total : Nat) : (fitSide limit total).fits limit total := by
  unfold fitSide fits
  split
  · rename_i h
    simpa using h
  · exact Nat.le_of_eq (Nat.mul_comm _ _)

theorem Scale.fits_of_atMost {a b : Scale} {limit total : Nat}
    (h : a.atMost b) (fits : b.fits limit total) : a.fits limit total := by
  unfold Scale.atMost Scale.fits at *
  apply Nat.le_of_mul_le_mul_right (c := b.den) _ b.positive
  calc
    a.num * total * b.den = (a.num * b.den) * total := by ac_rfl
    _ ≤ (b.num * a.den) * total := Nat.mul_le_mul_right _ h
    _ = (b.num * total) * a.den := by ac_rfl
    _ ≤ (b.den * limit) * a.den := Nat.mul_le_mul_right _ fits
    _ = a.den * limit * b.den := by ac_rfl

def Scale.component (s : Scale) (n : Nat) : Nat :=
  s.num * n / s.den

theorem Scale.pair_fits {s : Scale} {limit a b : Nat} (fit : s.fits limit (a+b)) :
    s.component a + s.component b ≤ limit := by
  unfold Scale.fits at fit
  unfold Scale.component
  apply Nat.le_of_mul_le_mul_right (c := s.den) _ s.positive
  calc
    (s.num*a/s.den + s.num*b/s.den)*s.den =
        s.num*a/s.den*s.den + s.num*b/s.den*s.den := Nat.add_mul _ _ _
    _ ≤ s.num*a+s.num*b := Nat.add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)
    _ = s.num*(a+b) := (Nat.mul_add _ _ _).symm
    _ ≤ s.den*limit := fit
    _ = limit*s.den := Nat.mul_comm _ _

/-- CSS Backgrounds 3 §4.5. Take the least usable scale of the four sides.
Each component is rounded down to a layout unit after choosing the common scale. -/
def Radii.scaleFor (r : Radii) (w h : Nat) : Scale :=
  let top := Scale.fitSide w (r.topLeft.x+r.topRight.x)
  let right := Scale.fitSide h (r.topRight.y+r.bottomRight.y)
  let bottom := Scale.fitSide w (r.bottomLeft.x+r.bottomRight.x)
  let left := Scale.fitSide h (r.topLeft.y+r.bottomLeft.y)
  (top.min right).min (bottom.min left)

def Radius.scaled (p : Radius) (s : Scale) : Radius :=
  ⟨s.component p.x,s.component p.y⟩

def Radii.normalize (r : Radii) (w h : Nat) : Radii :=
  let s := r.scaleFor w h
  ⟨r.topLeft.scaled s,r.topRight.scaled s,r.bottomRight.scaled s,r.bottomLeft.scaled s⟩

def Radii.fits (r : Radii) (w h : Nat) : Prop :=
  r.topLeft.x+r.topRight.x ≤ w ∧ r.topRight.y+r.bottomRight.y ≤ h ∧
    r.bottomLeft.x+r.bottomRight.x ≤ w ∧ r.topLeft.y+r.bottomLeft.y ≤ h

/-- The four used corner curves do not overlap on any side. -/
theorem Radii.normalize_fits (r : Radii) (w h : Nat) :
    (r.normalize w h).fits w h := by
  let top := Scale.fitSide w (r.topLeft.x+r.topRight.x)
  let right := Scale.fitSide h (r.topRight.y+r.bottomRight.y)
  let bottom := Scale.fitSide w (r.bottomLeft.x+r.bottomRight.x)
  let left := Scale.fitSide h (r.topLeft.y+r.bottomLeft.y)
  let k := (top.min right).min (bottom.min left)
  have toTopRight : k.atMost (top.min right) := Scale.min_le_left _ _
  have toBottomLeft : k.atMost (bottom.min left) := Scale.min_le_right _ _
  have topFits : k.fits w (r.topLeft.x+r.topRight.x) :=
    Scale.fits_of_atMost (Scale.trans toTopRight (Scale.min_le_left _ _)) (Scale.fitSide_fits _ _)
  have rightFits : k.fits h (r.topRight.y+r.bottomRight.y) :=
    Scale.fits_of_atMost (Scale.trans toTopRight (Scale.min_le_right _ _)) (Scale.fitSide_fits _ _)
  have bottomFits : k.fits w (r.bottomLeft.x+r.bottomRight.x) :=
    Scale.fits_of_atMost (Scale.trans toBottomLeft (Scale.min_le_left _ _)) (Scale.fitSide_fits _ _)
  have leftFits : k.fits h (r.topLeft.y+r.bottomLeft.y) :=
    Scale.fits_of_atMost (Scale.trans toBottomLeft (Scale.min_le_right _ _)) (Scale.fitSide_fits _ _)
  exact ⟨Scale.pair_fits topFits,Scale.pair_fits rightFits,
    Scale.pair_fits bottomFits,Scale.pair_fits leftFits⟩

/-- Outer radii that already fit keep every authored layout unit. -/
theorem Radii.normalize_of_fits (r : Radii) (w h : Nat) (fit : r.fits w h) :
    r.normalize w h = r := by
  obtain ⟨top,right,bottom,left⟩ := fit
  rcases r with ⟨a,b,c,d⟩
  rcases a with ⟨ax,ay⟩
  rcases b with ⟨bx,by_⟩
  rcases c with ⟨cx,cy⟩
  rcases d with ⟨dx,dy⟩
  simp only at top right bottom left
  simp [Radii.normalize,Radii.scaleFor,Scale.fitSide,Scale.min,Radius.scaled,Scale.component,
    top,right,bottom,left]

#print axioms Radii.normalize_of_fits

#print axioms Radii.normalize_fits

#guard (Radii.normalize ⟨⟨600,400⟩,⟨200,100⟩,⟨500,600⟩,⟨0,0⟩⟩ 500 500) ==
  ⟨⟨375,250⟩,⟨125,62⟩,⟨312,375⟩,⟨0,0⟩⟩

end L4Factoidal.Rendering.Corners
namespace L4Factoidal.Rendering.Corners

structure Insets where
  top : Nat := 0
  right : Nat := 0
  bottom : Nat := 0
  left : Nat := 0

/-- CSS Backgrounds 3 §4.2. Radii for a rectangular inset of the border box. -/
def Radii.inset (r : Radii) (i : Insets) : Radii :=
  ⟨⟨r.topLeft.x-i.left,r.topLeft.y-i.top⟩,
   ⟨r.topRight.x-i.right,r.topRight.y-i.top⟩,
   ⟨r.bottomRight.x-i.right,r.bottomRight.y-i.bottom⟩,
   ⟨r.bottomLeft.x-i.left,r.bottomLeft.y-i.bottom⟩⟩

theorem Radii.inset_zero (r : Radii) : r.inset {} = r := by
  rcases r with ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩,⟨g,h⟩⟩
  simp [Radii.inset]

def Radius.isSquare (r : Radius) : Bool := r.x == 0 || r.y == 0

def Radii.isSquare (r : Radii) : Bool :=
  r.topLeft.isSquare && r.topRight.isSquare && r.bottomRight.isSquare && r.bottomLeft.isSquare

private def Radius.effective (r : Radius) : Radius :=
  if r.isSquare then {} else r

private def toPx (n : Nat) : Float := Float.ofNat n / 64

private def corner (r : Radius) (endPoint : Point) : PathSegment :=
  if r.isSquare then .line endPoint
  else .arc (toPx r.x) (toPx r.y) 0 false true endPoint

/-- An arc that reaches across the inset box leaves a square corner on the
other side. This follows from the two outer radii fitting their common edge. -/
theorem inset_overrun_opposite_square (span near far a b : Nat)
    (outer : a + b ≤ span) (overrun : a - near > span - near - far) :
    b - far = 0 := by omega

/-- A rounded outline, before clipping to the rectangle. An inset arc can
extend beyond the opposite edge. Move the adjacent square vertex outward in
that case to connect the arc outside the rectangle. The caller clips the
outline to the rectangle, leaving the required shorter arc on that edge. -/
def Radii.outline (r : Radii) (left top width height : Float) : Option Contour :=
  if r.isSquare then none else
  let a := r.topLeft.effective
  let b := r.topRight.effective
  let c := r.bottomRight.effective
  let d := r.bottomLeft.effective
  let right := left+width
  let bottom := top+height
  let beyond := fun n span => max 0 (toPx n-span)
  let tl := ⟨left-beyond b.x width,top-beyond d.y height⟩
  let tr := ⟨right+beyond a.x width,top-beyond c.y height⟩
  let br := ⟨right+beyond d.x width,bottom+beyond b.y height⟩
  let bl := ⟨left-beyond c.x width,bottom+beyond a.y height⟩
  let aStart : Point := if a.isSquare then tl else ⟨left,top+toPx a.y⟩
  let aEnd : Point := if a.isSquare then tl else ⟨left+toPx a.x,top⟩
  let bStart : Point := if b.isSquare then tr else ⟨right-toPx b.x,top⟩
  let bEnd : Point := if b.isSquare then tr else ⟨right,top+toPx b.y⟩
  let cStart : Point := if c.isSquare then br else ⟨right,bottom-toPx c.y⟩
  let cEnd : Point := if c.isSquare then br else ⟨right-toPx c.x,bottom⟩
  let dStart : Point := if d.isSquare then bl else ⟨left+toPx d.x,bottom⟩
  let dEnd : Point := if d.isSquare then bl else ⟨left,bottom-toPx d.y⟩
  some (.path aEnd [.line bStart,corner b bEnd,.line cStart,corner c cEnd,
    .line dStart,corner d dEnd,.line aStart,corner a aEnd] true)

#print axioms inset_overrun_opposite_square

/-- The square fast path needs no ellipse or path flattening. -/
theorem Radii.outline_square (r : Radii) (x y w h : Float) (hSquare : r.isSquare = true) :
    r.outline x y w h = none := by
  simp [Radii.outline,hSquare]

#print axioms Radii.inset_zero
#print axioms Radii.outline_square

#guard ((Radii.normalize ⟨⟨4480,4480⟩,⟨4480,4480⟩,⟨4480,4480⟩,⟨4480,4480⟩⟩
    (140*64) (140*64)).inset ⟨640,640,640,640⟩).topLeft == ⟨3840,3840⟩
#guard (Radii.outline {} 0 0 120 120).isNone
#guard match Radii.outline ⟨⟨640,1280⟩,{}, {}, {}⟩ 0 0 120 120 with
  | some (.path _ segments true) =>
    segments.toArray[7]?.any fun
      | .arc rx ry _ false true p => rx == 10 && ry == 20 && p.x == 10 && p.y == 0
      | _ => false
  | _ => false

-- For a 125px corner inside a 100px padding box the quarter ellipse
-- starts 25px outside two opposite edges. The crop leaves shorter arcs.
#guard match Radii.outline ⟨⟨8000,8000⟩,{},{},{}⟩ 0 0 100 100 with
  | some (.path start segments true) =>
    start.x == 125 && segments.head?.any (fun
      | .line p => p.x == 125 && p.y == 0
      | _ => false)
  | _ => false

end L4Factoidal.Rendering.Corners
