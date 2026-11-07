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
inductive Paint where
  | none | solid (color : Color) | current
  | gradient (source : Gradient)
  /-- A lowered gradient and its word offset in the paint table of the scene. -/
  | gradientRecord (cursor : Nat) (record : GradientRecord)
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
inductive FillRule where | nonzero | evenodd
  deriving Repr, BEq
inductive LineCap where | butt | round
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
