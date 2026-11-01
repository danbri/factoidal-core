import Init

/- Reusable homogeneous affine algebra. Explicit scalar operations keep exact
   rational, floating and future backends distinct. No ring laws, numerical
   stability, Float/Rat refinement or GPU equivalence follow from this record.
   Column vectors: compose p q applies q first and then p. -/
namespace L4Factoidal.Math

structure AffineScalarOps (α : Type) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div? : α → α → Option α

/-- IEEE Float backend. Exact rational callers supply their existing arithmetic
    instead. Division failure denotes a zero divisor, not a stability proof. -/
def AffineScalarOps.float : AffineScalarOps Float :=
  ⟨0,1,(·+·),(·-·),(·*·),fun a b => if b == 0 then none else some (a/b)⟩

structure Affine2 (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α
  deriving Repr

/-- Two padded rows for GPU-friendly affine storage. Each row has four scalar
    slots; byte width/alignment depends on the host scalar encoding. Padding
    is not a coefficient and must not enter evaluation. -/
structure AffineRows (α : Type) where
  xx : α
  xy : α
  tx : α
  pad0 : α
  yx : α
  yy : α
  ty : α
  pad1 : α
  deriving Repr

namespace AffineRows

def vec4RowCount : Nat := 2
def vec4LaneCount : Nat := 4

def toList (r : AffineRows α) : List α :=
  [r.xx,r.xy,r.tx,r.pad0,r.yx,r.yy,r.ty,r.pad1]

/-- The two four-lane records consumed by the current WGSL affine path. This
    names the lane boundary in Lean instead of relying on an implicit
    `chunked 4` convention in a host adapter. It is a logical packing shape,
    not a claim about byte alignment or a particular GPU ABI. -/
def toVec4Rows (r : AffineRows α) : List (List α) :=
  [[r.xx,r.xy,r.tx,r.pad0],[r.yx,r.yy,r.ty,r.pad1]]

/-- Flattening the two WGSL lanes recovers the canonical scalar payload. -/
theorem toVec4Rows_flatten (r : AffineRows α) :
    r.toVec4Rows.flatten = r.toList := rfl

theorem toVec4Rows_flatten_length (r : AffineRows α) :
    r.toVec4Rows.flatten.length = vec4RowCount * vec4LaneCount := by
  rw [toVec4Rows_flatten]
  simp [toList, vec4RowCount, vec4LaneCount]

theorem toVec4Rows_length (r : AffineRows α) : r.toVec4Rows.length = vec4RowCount := rfl

theorem toVec4Rows_lane_lengths (r : AffineRows α) :
    r.toVec4Rows.map List.length = [vec4LaneCount,vec4LaneCount] := rfl

def decode (r : AffineRows α) : Affine2 α :=
  ⟨r.xx,r.yx,r.xy,r.yy,r.tx,r.ty⟩

/-- Same operation order as the affine reference; no reassociation or FMA
    assumption. This models scalar evaluation, not a GPU floating ABI. -/
def applyPoint (s : AffineScalarOps α) (r : AffineRows α) (x y : α) : α × α :=
  (s.add (s.add (s.mul r.xx x) (s.mul r.xy y)) r.tx,
   s.add (s.add (s.mul r.yx x) (s.mul r.yy y)) r.ty)

theorem toList_length (r : AffineRows α) : r.toList.length = 8 := rfl

theorem applyPoint_ignores_padding (s : AffineScalarOps α) (r : AffineRows α)
    (p q x y : α) :
    applyPoint s {r with pad0 := p, pad1 := q} x y = applyPoint s r x y := rfl

end AffineRows

namespace Affine2

/-- Row-major padded affine payload: [a,c,e,0,b,d,f,0]. The final
    homogeneous row [0,0,1] is implicit. Shared by SVG and other consumers. -/
def toPackedRows (s : AffineScalarOps α) (m : Affine2 α) : AffineRows α :=
  ⟨m.a,m.c,m.e,s.zero,m.b,m.d,m.f,s.zero⟩

theorem packed_decode (s : AffineScalarOps α) (m : Affine2 α) :
    (toPackedRows s m).decode = m := by cases m; rfl

def identity (s : AffineScalarOps α) : Affine2 α :=
  ⟨s.one,s.zero,s.zero,s.one,s.zero,s.zero⟩

def compose (s : AffineScalarOps α) (p q : Affine2 α) : Affine2 α :=
  ⟨s.add (s.mul p.a q.a) (s.mul p.c q.b),
   s.add (s.mul p.b q.a) (s.mul p.d q.b),
   s.add (s.mul p.a q.c) (s.mul p.c q.d),
   s.add (s.mul p.b q.c) (s.mul p.d q.d),
   s.add (s.add (s.mul p.a q.e) (s.mul p.c q.f)) p.e,
   s.add (s.add (s.mul p.b q.e) (s.mul p.d q.f)) p.f⟩

def determinant (s : AffineScalarOps α) (m : Affine2 α) : α :=
  s.sub (s.mul m.a m.d) (s.mul m.b m.c)

def inverse? (s : AffineScalarOps α) (m : Affine2 α) : Option (Affine2 α) := do
  let det := determinant s m
  let a ← s.div? m.d det
  let b ← s.div? (s.sub s.zero m.b) det
  let c ← s.div? (s.sub s.zero m.c) det
  let d ← s.div? m.a det
  let e ← s.div? (s.sub (s.mul m.c m.f) (s.mul m.d m.e)) det
  let f ← s.div? (s.sub (s.mul m.b m.e) (s.mul m.a m.f)) det
  return ⟨a,b,c,d,e,f⟩

def applyPoint (s : AffineScalarOps α) (m : Affine2 α) (x y : α) : α × α :=
  (s.add (s.add (s.mul m.a x) (s.mul m.c y)) m.e,
   s.add (s.add (s.mul m.b x) (s.mul m.d y)) m.f)

def applyDirection (s : AffineScalarOps α) (m : Affine2 α) (x y : α) : α × α :=
  (s.add (s.mul m.a x) (s.mul m.c y),s.add (s.mul m.b x) (s.mul m.d y))

/-- Packing preserves the exact scalar expression used for point mapping.
    Holds for every scalar backend, including Float; does not equate f64 CPU
    arithmetic with f32 GPU arithmetic or permit shader reassociation. -/
theorem packed_applyPoint (s : AffineScalarOps α) (m : Affine2 α) (x y : α) :
    (toPackedRows s m).applyPoint s x y = applyPoint s m x y := rfl

/-- Unnormalized normal covectors use the inverse transpose, not the point
    or direction transform. This can fail for a singular matrix/backend. -/
def applyNormal? (s : AffineScalarOps α) (m : Affine2 α) (x y : α) : Option (α × α) := do
  let inverse ← inverse? s m
  return (s.add (s.mul inverse.a x) (s.mul inverse.b y),
    s.add (s.mul inverse.c x) (s.mul inverse.d y))

/-- Four transformed corners for a future ordered-scalar bounding-box adapter.
    Does not claim that arbitrary scalar operations preserve affine extrema. -/
def boxCorners (s : AffineScalarOps α) (m : Affine2 α) (left top right bottom : α) : List (α × α) :=
  [applyPoint s m left top,applyPoint s m right top,
   applyPoint s m right bottom,applyPoint s m left bottom]

/-- Row-major homogeneous embedding; translation is the last column. -/
def toRows (s : AffineScalarOps α) (m : Affine2 α) : List (List α) :=
  [[m.a,m.c,m.e],[m.b,m.d,m.f],[s.zero,s.zero,s.one]]

/-- Direction vectors do not acquire a position's translation. This theorem
    states the concrete implementation dependency, not general scalar algebra. -/
theorem direction_ignores_translation (s : AffineScalarOps α) (m : Affine2 α)
    (e f x y : α) :
    applyDirection s {m with e,f} x y = applyDirection s m x y := rfl

/-- The homogeneous embedding always has exactly three rows of three scalars;
    unlike a general list matrix, no ragged affine value can be constructed. -/
theorem toRows_shape (s : AffineScalarOps α) (m : Affine2 α) :
    (toRows s m).length = 3 ∧ ((toRows s m).map List.length) = [3,3,3] := by
  simp [toRows]

/-- The actual Float backend refuses a determinant which its zero test accepts.
    This does not assert invertibility or stability for nonzero determinants. -/
theorem inverse_float_zero_det (m : Affine2 Float)
    (h : (determinant AffineScalarOps.float m == 0) = true) :
    inverse? AffineScalarOps.float m = none := by
  have first : AffineScalarOps.float.div? m.d (determinant AffineScalarOps.float m) = none := by
    change (if determinant AffineScalarOps.float m == 0 then none else
      some (m.d / determinant AffineScalarOps.float m)) = none
    simp [h]
  simp [inverse?, first]

end Affine2
end L4Factoidal.Math
