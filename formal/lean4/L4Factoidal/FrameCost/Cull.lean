/-! # Culling by intervals and boxes: when a filtered list gives the full answer

The tile lists of the scene (`labs/demos/foafnaut/SVG.lean`: `edgesMeeting`, `binPieces`,
`Primitive.paintBox`) leave out the edges, stroke pieces and primitives whose stored interval
or box does not meet a band, a cell or a tile. This module holds the order reasoning those
lists rest on, for any ordered type whose comparisons obey `Laws`. `Int` obeys them (proved
below, so the laws are consistent and every theorem here is unconditional for exact integer
or fixed-point geometry). For `Float` the laws are those of IEEE 754 comparison; Lean's `Float`
is opaque, so there they are a stated hypothesis (`IncrementalProofs.lean`).

Only Lean core. -/
namespace L4Factoidal.FrameCost.Cull

/-- The comparison laws the culling theorems use. Each holds of IEEE 754 binary64 `<=` and `<`
for every pair of values, NaN and the infinities included: a comparison with NaN is false,
and `le_refl`-style facts are asked only of values `x` with `x ≤ x` (not NaN). -/
structure Laws (α : Type) [LE α] [LT α] : Prop where
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
  lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c
  le_of_lt : ∀ {a b : α}, a < b → a ≤ b
  not_le_of_lt : ∀ {a b : α}, a < b → ¬ b ≤ a
  /-- Two values that are not NaN are comparable. -/
  lt_of_not_le : ∀ {a b : α}, a ≤ a → b ≤ b → ¬ a ≤ b → b < a

/-- Kind: consistency. Says: `Int` with its own order obeys `Laws`, so the laws are not
contradictory and the theorems below hold with no hypothesis for integer geometry.
Does not say: anything of `Float`. -/
theorem intLaws : Laws Int where
  le_trans := Int.le_trans
  lt_of_lt_of_le := Int.lt_of_lt_of_le
  lt_of_le_of_lt := Int.lt_of_le_of_lt
  le_of_lt := Int.le_of_lt
  not_le_of_lt := fun h => Int.not_le.mpr h
  lt_of_not_le := fun _ _ h => Int.not_le.mp h

section
variable {α : Type} [LE α] [LT α] [DecidableLE α] [DecidableLT α]

/-- The larger and the smaller of two values as `maxOfLe` and `minOfLe` give them (the `max`
and `min` of `Float`). -/
def hiOf (a b : α) : α := if a ≤ b then b else a
def loOf (a b : α) : α := if a ≤ b then a else b

/-- An edge with end values `a` and `b` spans the line at `p`: its ends compare differently
with `p` (the form of `NativeSVG.pathEdgeSpans`). -/
def spans (a b p : α) : Bool := decide (a ≤ p) != decide (b ≤ p)

/-- An edge with end values `a` and `b` is kept for the interval `lo .. hi`: its ends are not
both below `lo` nor both above `hi` (the form of `NativeSVG.edgeMeets`). -/
def meets (a b lo hi : α) : Bool := !decide (hiOf a b < lo) && !decide (hi < loOf a b)

/-- Kind: soundness of a filter (over-approximation). Says: an edge whose ends are not NaN and
that spans the line at `p` is kept for every interval `lo .. hi` that holds `p`. So a list
filtered by `meets` loses no edge that can change a winding number on a line inside the
interval. Does not say: that a given sample's `p` is inside the interval (for `Float` that is
a statement about rounding), nor anything of an edge with a NaN end. -/
theorem meets_of_spans (L : Laws α) {a b lo hi p : α} (ha : a ≤ a) (hb : b ≤ b)
    (hlo : lo ≤ p) (hhi : p ≤ hi) (h : spans a b p = true) : meets a b lo hi = true := by
  have key : ¬ hiOf a b < lo ∧ ¬ hi < loOf a b := by
    unfold hiOf loOf
    unfold spans at h
    by_cases hap : a ≤ p <;> by_cases hbp : b ≤ p <;> simp [hap, hbp] at h
    · -- a ≤ p, ¬ b ≤ p
      by_cases hab : a ≤ b
      · simp only [hab, if_true]
        exact ⟨fun hlt => hbp (L.le_of_lt (L.lt_of_lt_of_le hlt hlo)),
               fun hlt => L.not_le_of_lt hlt (L.le_trans hap hhi)⟩
      · simp only [hab, if_false]
        have hba : b < a := L.lt_of_not_le ha hb hab
        exact ⟨fun _ => hbp (L.le_trans (L.le_of_lt hba) hap),
               fun hlt => L.not_le_of_lt (L.lt_of_lt_of_le hlt (L.le_of_lt hba)) (L.le_trans hap hhi)⟩
    · -- ¬ a ≤ p, b ≤ p
      by_cases hab : a ≤ b
      · simp only [hab, if_true]
        exact ⟨fun _ => hap (L.le_trans hab hbp),
               fun hlt => L.not_le_of_lt (L.lt_of_lt_of_le hlt hab) (L.le_trans hbp hhi)⟩
      · simp only [hab, if_false]
        exact ⟨fun hlt => hap (L.le_of_lt (L.lt_of_lt_of_le hlt hlo)),
               fun hlt => L.not_le_of_lt hlt (L.le_trans hbp hhi)⟩
  simp [meets, key.1, key.2]

end

/-- Kind: soundness of a box test (over-approximation), one axis. Says: when a point `p` lies
in a stored interval `lo .. hi` and in a cell `c0 .. c1`, the interval is not wholly before
or after the cell: the test "stored box meets cell" cannot leave out a piece whose stored box
holds a point of the cell. Does not say: that the stored box holds every point the piece
covers. -/
theorem overlap_of_common_point {α : Type} [LE α] [LT α] (L : Laws α) {lo hi c0 c1 p : α}
    (hlo : lo ≤ p) (hhi : p ≤ hi) (h0 : c0 ≤ p) (h1 : p ≤ c1) : ¬ hi < c0 ∧ ¬ c1 < lo :=
  ⟨fun h => L.not_le_of_lt (L.lt_of_lt_of_le h h0) hhi,
   fun h => L.not_le_of_lt (L.lt_of_lt_of_le h hlo) h1⟩

/-- Kind: soundness of binning. Says: for a cell index `idx` that is monotone in the
coordinate, a point `p` of a stored interval `lo .. hi` whose cell is one of the `n` cells
from `first` lies in a cell from `max (idx lo) first` to `min (idx hi) (first+n-1)`: the range
of cells `NativeSVG.binPieces` puts the piece in. Does not say: that `idx` is monotone (for
`Float` division and `floor` that is a rounding fact; for `Int` see `bin_holds_int`). -/
theorem bin_holds {α : Type} [LE α] {idx : α → Nat} (mono : ∀ {x y : α}, x ≤ y → idx x ≤ idx y)
    {lo hi p : α} {first n : Nat} (hlo : lo ≤ p) (hhi : p ≤ hi)
    (inFirst : first ≤ idx p) (inLast : idx p ≤ first+n-1) :
    max (idx lo) first ≤ idx p ∧ idx p ≤ min (idx hi) (first+n-1) := by
  have a := mono hlo
  have b := mono hhi
  omega
/-- Kind: instance of `bin_holds` for exact arithmetic. Says: with integer pixel coordinates
and cells of `size > 0` pixels (cell of `x` is `(x/size).toNat`), a piece is listed in the
cell of every point of its stored interval, with no hypothesis. -/
theorem bin_holds_int {size lo hi p : Int} (pos : 0 < size) {first n : Nat}
    (hlo : lo ≤ p) (hhi : p ≤ hi)
    (inFirst : first ≤ (p/size).toNat) (inLast : (p/size).toNat ≤ first+n-1) :
    max (lo/size).toNat first ≤ (p/size).toNat ∧ (p/size).toNat ≤ min (hi/size).toNat (first+n-1) :=
  bin_holds (idx := fun x : Int => (x/size).toNat)
    (fun h => Int.toNat_le_toNat (Int.ediv_le_ediv pos h)) hlo hhi inFirst inLast

/-- Kind: instance for exact arithmetic. Says: `meets_of_spans` for `Int`, no hypothesis on the
order. -/
theorem meets_of_spans_int {a b lo hi p : Int} (hlo : lo ≤ p) (hhi : p ≤ hi)
    (h : spans a b p = true) : meets a b lo hi = true :=
  meets_of_spans intLaws (Int.le_refl a) (Int.le_refl b) hlo hhi h

#print axioms meets_of_spans
#print axioms overlap_of_common_point
#print axioms bin_holds
#print axioms bin_holds_int
#print axioms meets_of_spans_int
end L4Factoidal.FrameCost.Cull
