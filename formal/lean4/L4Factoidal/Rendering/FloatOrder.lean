/-! # The order of `Float`, as far as the link theorems need it

Lean's `Float` has a logical model (`Float.Model`, IEEE 754 binary64 unpacked into
`Float.Model.UnpackedFloat`), and `<` and `≤` on `Float` are defined through it. Core has
no order lemmas for it, so this file proves the two the link theorems use: `≤` is
transitive, and `a < b ≤ c` gives `a < c`. `NaN` is below, above and equal to nothing, so
both hold for every `Float`, `NaN` included.

The proof maps each number that is not `NaN` to a key in `Int × Int × Int` (sign class,
then exponent, then mantissa, negated below zero) whose lexicographic order is the IEEE
comparison of `UnpackedFloat.compare`. Only Lean core; no `native_decide`, no `bv_decide`.
Issue 1268; record `docs/designissues/2026-11-08-cost-theorems.md`. -/
set_option linter.unusedSimpArgs false
namespace L4Factoidal.Rendering.FloatOrder
open Float.Model Float.Model.UnpackedFloat

private theorem isLE_then (o p : Ordering) :
    (o.then p).isLE = true ↔ o = .lt ∨ (o = .eq ∧ (p = .lt ∨ p = .eq)) := by
  cases o <;> cases p <;> decide
private theorem isGE_then (o p : Ordering) :
    (o.then p).isGE = true ↔ o = .gt ∨ (o = .eq ∧ (p = .gt ∨ p = .eq)) := by
  cases o <;> cases p <;> decide
private theorem then_lt (o p : Ordering) : o.then p = .lt ↔ o = .lt ∨ (o = .eq ∧ p = .lt) := by
  cases o <;> cases p <;> decide
private theorem then_gt (o p : Ordering) : o.then p = .gt ↔ o = .gt ∨ (o = .eq ∧ p = .gt) := by
  cases o <;> cases p <;> decide
private theorem sign_nn : compare Sign.negative Sign.negative = .eq := by decide
private theorem sign_np : compare Sign.negative Sign.positive = .lt := by decide
private theorem sign_pn : compare Sign.positive Sign.negative = .gt := by decide
private theorem sign_pp : compare Sign.positive Sign.positive = .eq := by decide

/-- The place of a number on the line: sign class, then exponent, then mantissa (both
negated below zero). `NaN` has a key too, but every comparison with it is false. -/
def key : UnpackedFloat → Int × Int × Int
  | .infinity .negative => (-2,0,0)
  | .finite .negative m e _ => (-1,-e,-(m : Int))
  | .zero _ => (0,0,0)
  | .finite .positive m e _ => (1,e,m)
  | .infinity .positive => (2,0,0)
  | .notANumber => (0,0,0)

/-- The lexicographic order of keys, not strict. -/
def KeyLE (k l : Int × Int × Int) : Prop :=
  k.1 < l.1 ∨ (k.1 = l.1 ∧ (k.2.1 < l.2.1 ∨ (k.2.1 = l.2.1 ∧ k.2.2 ≤ l.2.2)))

/-- The lexicographic order of keys, strict. -/
def KeyLT (k l : Int × Int × Int) : Prop :=
  k.1 < l.1 ∨ (k.1 = l.1 ∧ (k.2.1 < l.2.1 ∨ (k.2.1 = l.2.1 ∧ k.2.2 < l.2.2)))

theorem unpacked_le_iff {a b : UnpackedFloat} :
    a.le b = true ↔ a ≠ .notANumber ∧ b ≠ .notANumber ∧ KeyLE (key a) (key b) := by
  rcases a with (_|_) | _ | (_|_) | ⟨(_|_), m, e, h⟩ <;>
  rcases b with (_|_) | _ | (_|_) | ⟨(_|_), m', e', h'⟩ <;>
  simp [UnpackedFloat.le, UnpackedFloat.compare, Option.any, isLE_then, isGE_then,
    sign_nn, sign_np, sign_pn, sign_pp, key, KeyLE, Int.compare_eq_lt, Int.compare_eq_eq,
    Int.compare_eq_gt, Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_gt] <;> omega

theorem unpacked_lt_iff {a b : UnpackedFloat} :
    a.lt b = true ↔ a ≠ .notANumber ∧ b ≠ .notANumber ∧ KeyLT (key a) (key b) := by
  rcases a with (_|_) | _ | (_|_) | ⟨(_|_), m, e, h⟩ <;>
  rcases b with (_|_) | _ | (_|_) | ⟨(_|_), m', e', h'⟩ <;>
  simp [UnpackedFloat.lt, UnpackedFloat.compare, then_lt, then_gt, sign_nn, sign_np, sign_pn,
    sign_pp, key, KeyLT, Int.compare_eq_lt, Int.compare_eq_eq, Int.compare_eq_gt,
    Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_gt] <;> omega

theorem le_iff {a b : Float} : a ≤ b ↔ a.toModel.unpack.le b.toModel.unpack = true := by
  show Float.le a b = true ↔ _
  unfold Float.le; rw [decide_eq_true_iff]; exact Iff.rfl

theorem lt_iff {a b : Float} : a < b ↔ a.toModel.unpack.lt b.toModel.unpack = true := by
  show Float.lt a b = true ↔ _
  unfold Float.lt; rw [decide_eq_true_iff]; exact Iff.rfl

/-- `≤` on `Float` is transitive. -/
theorem le_trans {a b c : Float} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  rw [le_iff, unpacked_le_iff] at *
  obtain ⟨a1, _, k1⟩ := h₁
  obtain ⟨_, c1, k2⟩ := h₂
  refine ⟨a1, c1, ?_⟩
  unfold KeyLE at *; omega

/-- `a < b ≤ c` gives `a < c` on `Float`. -/
theorem lt_of_lt_of_le {a b c : Float} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  rw [lt_iff, unpacked_lt_iff] at *
  rw [le_iff, unpacked_le_iff] at h₂
  obtain ⟨a1, _, k1⟩ := h₁
  obtain ⟨_, c1, k2⟩ := h₂
  refine ⟨a1, c1, ?_⟩
  unfold KeyLT KeyLE at *; omega

/-- A bottom `b` below the foot `H` of the document survives the cut at `max v H`, for any
viewport `v` (`NaN` included): whatever was below `t` stays below `t`. -/
theorem lt_min_max {t b v H : Float} (below : t < b) (inside : b ≤ H) : t < min (max v H) b := by
  show t < (if (if v ≤ H then H else v) ≤ b then (if v ≤ H then H else v) else b)
  by_cases hv : v ≤ H
  · simp only [hv, ite_true]
    by_cases hb : H ≤ b
    · simp only [hb, ite_true]; exact lt_of_lt_of_le below inside
    · simp only [hb, ite_false]; exact below
  · simp only [hv, ite_false]
    by_cases hb : v ≤ b
    · exact absurd (le_trans hb inside) hv
    · simp only [hb, ite_false]; exact below

end L4Factoidal.Rendering.FloatOrder
