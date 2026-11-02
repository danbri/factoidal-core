import L4Factoidal.Math.Affine

/-! Shared retained vector model for SVG and HTML layout. Coordinates use
binary64 Float. The native GPU adapter uses binary32; equality of rasterized
pixels does not follow from the exact structural adapter theorems. -/
namespace L4Factoidal.Rendering

abbrev Transform := Math.Affine2 Float
def identity : Transform := Math.Affine2.identity .float
structure Point where
  x : Float
  y : Float
  deriving Repr
structure Color where
  r : Float
  g : Float
  b : Float
  deriving Repr
structure Contour where
  points : List Point
  closed : Bool
  deriving Repr
/-- The current path profile is polygonal. Future curved segments extend this
algebra; producers must refuse curves until a backend admits their semantics. -/
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
structure Primitive where
  geometry : Geometry
  style : Style := {}
  opacity : Float := 1
  transform : Transform := identity
  dashParts : Option (List StrokePiece) := none
  groupPath : List (Option String) := []
  deriving Repr
structure PaintItem where
  /-- Index in the source DOM arena, shared by boxes, glyphs and input targets. -/
  source : Option Nat := none
  primitive : Primitive
  deriving Repr
inductive Node where
  | paint (item : PaintItem)
  | group (id : Option String) (transform : Transform) (children : List Node)
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
          groupPath := groups ++ p.groupPath}
mutual
  def Node.lower (parent : Transform) (groups : List (Option String)) : Node → List PaintItem
    | .paint item => [{item with primitive := item.primitive.lowerUnder parent groups}]
    | .group id transform children =>
        Node.lowerList (Math.Affine2.compose .float parent transform) (groups ++ [id]) children
  termination_by node => sizeOf node
  def Node.lowerList (parent : Transform) (groups : List (Option String)) : List Node → List PaintItem
    | [] => []
    | node :: rest => node.lower parent groups ++ Node.lowerList parent groups rest
  termination_by nodes => sizeOf nodes
end
def Node.lowerTR (parent : Transform) (groups : List (Option String))
    (node : Node) : List PaintItem :=
  match node with
  | .paint item => [{item with primitive := item.primitive.lowerUnder parent groups}]
  | .group id transform children =>
      (children.foldl (fun acc child =>
        (child.lowerTR (Math.Affine2.compose .float parent transform) (groups ++ [id])).reverse ++ acc) []).reverse
termination_by sizeOf node


theorem Node.lowerTR_eq (node : Node) :
    ∀ parent groups, node.lowerTR parent groups = node.lower parent groups := by
  refine Node.rec
    (motive_1 := fun node => ∀ parent groups,
      node.lowerTR parent groups = node.lower parent groups)
    (motive_2 := fun (nodes : List Node) => ∀ (parent : Transform) (groups : List (Option String)) (acc : List PaintItem),
      (nodes.foldl (fun acc child => (child.lowerTR parent groups).reverse ++ acc) acc).reverse =
        acc.reverse ++ Node.lowerList parent groups nodes)
    ?_ ?_ ?_ ?_ node
  · intro primitive parent groups
    simp [Node.lowerTR, Node.lower]
  · intro id transform children ih parent groups
    simpa [Node.lowerTR, Node.lower] using
      ih (Math.Affine2.compose .float parent transform) (groups ++ [id]) []
  · intro parent groups acc
    simp [Node.lowerList]
  · intro head tail ihHead ihTail parent groups acc
    simp only [List.foldl_cons]
    rw [ihTail, List.reverse_append, List.reverse_reverse, ihHead]
    simp only [Node.lowerList, List.append_assoc]

/-- Reverse-accumulator sibling lowering using the fast recursive group twin. -/
def Node.lowerListTR (parent : Transform) (groups : List (Option String))
    (nodes : List Node) : List PaintItem :=
  (nodes.foldl (fun acc node => (node.lowerTR parent groups).reverse ++ acc) []).reverse

private theorem lowerFold_eq (nodes : List Node) (parent : Transform)
    (groups : List (Option String)) (acc : List PaintItem) :
    (nodes.foldl (fun acc node => (node.lowerTR parent groups).reverse ++ acc) acc).reverse =
      acc.reverse ++ Node.lowerList parent groups nodes := by
  induction nodes generalizing acc with
  | nil => simp [Node.lowerList]
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih, List.reverse_append, List.reverse_reverse, Node.lowerTR_eq]
      simp only [Node.lowerList, List.append_assoc]


@[csimp] theorem Node.lower_eq_lowerTR : @Node.lower = @Node.lowerTR := by
  funext parent groups node
  exact (Node.lowerTR_eq node parent groups).symm

@[csimp] theorem Node.lowerList_eq_lowerListTR : @Node.lowerList = @Node.lowerListTR := by
  funext parent groups nodes
  exact (show Node.lowerListTR parent groups nodes = Node.lowerList parent groups nodes by
    simpa only [Node.lowerListTR, List.reverse_nil, List.nil_append] using
      lowerFold_eq nodes parent groups []).symm


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
