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
inductive Paint where
  | none | solid (color : Color) | current
  deriving Repr
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
