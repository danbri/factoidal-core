/-
L4Factoidal.Unicode.BidiTheorems — properties of the UAX #9 (revision 52,
Unicode 18.0.0) implementation in `L4Factoidal.Unicode.Bidi`
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

`revRange` is the reversal step of rule L2 (UAX #9 §3.4). It keeps the size of
the array, and its result is a permutation of its input, so each L2 step
neither loses nor duplicates a character position.
-/
import L4Factoidal.Unicode.Bidi

namespace L4Factoidal.Unicode

theorem revRange_go_size {α : Type} (a : Array α) (i j f : Nat) :
    (revRange.go a i j f).size = a.size := by
  induction f generalizing a i j with
  | zero => rfl
  | succ f ih =>
    unfold revRange.go
    split
    · rw [ih]; simp
    · rfl

theorem revRange_size {α : Type} (a : Array α) (i j : Nat) :
    (revRange a i j).size = a.size :=
  revRange_go_size a i j (j - i)

theorem revRange_go_perm {α : Type} (a : Array α) (i j f : Nat) :
    (revRange.go a i j f).Perm a := by
  induction f generalizing a i j with
  | zero => exact Array.Perm.refl a
  | succ f ih =>
    unfold revRange.go
    split
    · exact (ih _ _ _).trans (Array.swap_perm _ _)
    · exact Array.Perm.refl a

/-- The L2 reversal step permutes its input. -/
theorem revRange_perm {α : Type} (a : Array α) (i j : Nat) :
    (revRange a i j).Perm a :=
  revRange_go_perm a i j (j - i)

end L4Factoidal.Unicode
