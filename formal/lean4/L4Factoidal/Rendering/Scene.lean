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
/-- One DFS frame retains a cursor over siblings. Pushing a group does not copy
its subtree or flatten its children; its untouched siblings keep their frame. -/
private structure LowerFrame where
  parent : Transform
  /-- Innermost first; descent conses one ID and shares the outer path. -/
  revGroups : List (Option String)
  /-- Innermost first: folding `addClip` restores outermost-first clip order. -/
  clips : List ClipRect
  nodes : List Node

private def applyClips (clips : List ClipRect) (item : PaintItem) : PaintItem :=
  clips.foldl (fun p clip => PaintItem.addClip clip p) item

/-- Only the termination proof examines this weight. It is independent of the
possibly growing transform/group/clip context; no runtime fuel cutoff is used. -/
private noncomputable def lowerWeight (todo : List LowerFrame) : Nat :=
  (todo.map (fun frame => sizeOf frame.nodes + 1)).sum

/-- Tail calls for children *and* siblings; neither the input tree depth nor
its width is recursion depth on the native/WASM call stack. -/
private def lowerStack (todo : List LowerFrame) (out : List PaintItem) : List PaintItem :=
  match todo with
  | [] => out.reverse
  | ⟨_, _, _, []⟩ :: more => lowerStack more out
  | ⟨p, gs, clips, .paint item :: ns⟩ :: more =>
    lowerStack (⟨p, gs, clips, ns⟩ :: more)
      (applyClips clips {item with primitive := item.primitive.lowerUnder p gs.reverse} :: out)
  | ⟨p, gs, clips, .group id tx cs :: ns⟩ :: more =>
    lowerStack (⟨Math.Affine2.compose .float p tx, id :: gs, clips, cs⟩ ::
      ⟨p, gs, clips, ns⟩ :: more) out
  | ⟨p, gs, clips, .clipped id tx clip cs :: ns⟩ :: more =>
    lowerStack (⟨Math.Affine2.compose .float p tx, id :: gs, clip.lowerUnder p :: clips, cs⟩ ::
      ⟨p, gs, clips, ns⟩ :: more) out
termination_by lowerWeight todo
decreasing_by all_goals simp [lowerWeight] <;> omega

private def LowerFrame.paints (f : LowerFrame) : List PaintItem :=
  (Node.lowerList f.parent f.revGroups.reverse f.nodes).map (applyClips f.clips)

/-- The reverse accumulator followed by the reference meaning of all pending
frames is invariant. In particular the clip applied by a group uses its
parent's transform, independently of its children's content transform. -/
private theorem lowerStack_eq : ∀ (todo : List LowerFrame) (out : List PaintItem),
    lowerStack todo out = out.reverse ++ todo.flatMap LowerFrame.paints
  | [], out => by simp [lowerStack]
  | ⟨p, gs, clips, []⟩ :: more, out => by
    rw [lowerStack, lowerStack_eq]
    simp [LowerFrame.paints, Node.lowerList]
  | ⟨p, gs, clips, .paint item :: ns⟩ :: more, out => by
    rw [lowerStack, lowerStack_eq]
    simp [LowerFrame.paints, Node.lowerList, Node.lower, List.append_assoc]
  | ⟨p, gs, clips, .group id tx cs :: ns⟩ :: more, out => by
    rw [lowerStack, lowerStack_eq]
    simp [LowerFrame.paints, Node.lowerList, Node.lower, List.append_assoc]
  | ⟨p, gs, clips, .clipped id tx clip cs :: ns⟩ :: more, out => by
    rw [lowerStack, lowerStack_eq]
    simp [LowerFrame.paints, Node.lowerList, Node.lower, List.append_assoc,
      applyClips, List.map_map, Function.comp_def]
termination_by todo _ => lowerWeight todo
decreasing_by all_goals simp [lowerWeight] <;> omega

/-- Lower the complete ordered forest in one traversal, including deep groups. -/
def Node.lowerListTR (parent : Transform) (groups : List (Option String))
    (nodes : List Node) : List PaintItem :=
  lowerStack [⟨parent, groups.reverse, [], nodes⟩] []

def Node.lowerTR (parent : Transform) (groups : List (Option String))
    (node : Node) : List PaintItem :=
  Node.lowerListTR parent groups [node]

private theorem lowerListTR_eq (nodes : List Node) (parent : Transform)
    (groups : List (Option String)) :
    Node.lowerListTR parent groups nodes = Node.lowerList parent groups nodes := by
  rw [Node.lowerListTR, lowerStack_eq]
  simp [LowerFrame.paints, applyClips]

theorem Node.lowerTR_eq (node : Node) :
    ∀ parent groups, node.lowerTR parent groups = node.lower parent groups := by
  intro parent groups
  rw [Node.lowerTR, lowerListTR_eq]
  simp [Node.lowerList]

@[csimp] theorem Node.lower_eq_lowerTR : @Node.lower = @Node.lowerTR := by
  funext parent groups node
  exact (Node.lowerTR_eq node parent groups).symm

@[csimp] theorem Node.lowerList_eq_lowerListTR : @Node.lowerList = @Node.lowerListTR := by
  funext parent groups nodes
  exact (lowerListTR_eq nodes parent groups).symm


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
