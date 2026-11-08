/-
L4Factoidal.Unicode.BidiTheorems — properties of the UAX #9 (revision 52,
Unicode 18.0.0) implementation in `L4Factoidal.Unicode.Bidi`
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

`revRange` is the reversal step of rule L2 (UAX #9 §3.4). It keeps the size of
the array, and its result is a permutation of its input, so each L2 step
neither loses nor duplicates a character position. `reorderByLevels_even`: a
line with no odd level keeps its order, so text with no right-to-left content
is laid out as before bidi (https://github.com/danbri/factoidal/issues/1275).
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

theorem lowestOdd_list_even (l : List Nat) (h : ∀ x ∈ l, x % 2 = 0) (a : Nat) :
    l.foldl (fun acc l => if l % 2 == 1 then min acc l else acc) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hx : x % 2 = 0 := h x (by simp)
    simp only [List.foldl, hx]
    exact ih (fun y hy => h y (by simp [hy])) a

/-- With no odd level, `lowestOdd` finds none. -/
theorem lowestOdd_even (ls : Array Nat) (h : ∀ x ∈ ls.toList, x % 2 = 0) (a : Nat) :
    lowestOdd ls a = a := by
  unfold lowestOdd
  rw [← Array.foldl_toList]
  exact lowestOdd_list_even ls.toList h a

/-- L2 keeps the order of a line whose levels are all even: left-to-right text,
and left-to-right text with left-to-right embeddings, is drawn in logical order. -/
theorem reorderByLevels_even (ord ls : Array Nat) (h : ∀ x ∈ ls.toList, x % 2 = 0) :
    reorderByLevels ord ls = ord := by
  unfold reorderByLevels
  simp only [lowestOdd_even ls h]
  exact if_pos (Nat.lt_add_one _)

/-- A line all at level 0 (left to right, no right-to-left character) keeps its order. -/
theorem reorderByLevels_ltr (n : Nat) :
    reorderByLevels (Array.range n) (Array.replicate n 0) = Array.range n :=
  reorderByLevels_even _ _ (by simp)

end L4Factoidal.Unicode
