/-
L4Factoidal.Storage.Sbm11.OverlayTheorems — the delta overlay of SBM11 stage 5
(https://github.com/danbri/factoidal/issues/791; lemma L7 of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`).

* `filterDel_eq`: for sorted `base` and `del`, `filterDel cl base del` is
  `base.filter` of the rows not in `del` whose graph is not cleared.
* `unionRows_mem`, `unionRows_sorted`: the union holds the rows of both
  lists, and is strictly sorted when both are.
* `mergeRows_spec`: for strictly sorted `base`, `del` and `ins`, the merged
  rows are strictly sorted and `r ∈ mergeRows cl base del ins ↔
  (r ∈ base ∧ r ∉ del ∧ cl r.g = false) ∨ r ∈ ins`.
* `sorted_eq_of_mem_iff`: two strictly sorted lists with the same members are
  equal; with `mergeRows_spec` the merge is THE sorted list of that set (so,
  as a multiset, every member once).
* `step_add`, `step_remove`, `step_clear`: one replay step changes the
  denoted quad set as INSERT DATA, DELETE DATA and CLEAR/DROP say;
  `replay_append` lets a log be replayed batch by batch.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Overlay
import L4Factoidal.Storage.Sbm11.ScanTheorems

namespace L4Factoidal.Storage.Sbm11.OverlayTheorems

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Overlay

/-! ## The row order is a strict total order -/

/-- Strictly increasing by `Row.lt`. -/
abbrev Sorted (l : List Row) : Prop := l.Pairwise (fun a b => a.lt b = true)

theorem lt_irrefl (r : Row) : r.lt r = false := by
  cases h : r.lt r
  · rfl
  · rw [ScanTheorems.lt_iff] at h; omega

theorem lt_asymm {a b : Row} (h : a.lt b = true) : b.lt a = false := by
  cases h2 : b.lt a
  · rfl
  · have := ScanTheorems.lt_trans h h2
    rw [lt_irrefl] at this; cases this

theorem lt_total (a b : Row) : a.lt b = true ∨ a = b ∨ b.lt a = true := by
  rw [ScanTheorems.lt_iff, ScanTheorems.lt_iff, ScanTheorems.row_eq_iff]
  omega

theorem ne_of_lt {a b : Row} (h : a.lt b = true) : a ≠ b := by
  intro e; subst e; rw [lt_irrefl] at h; cases h

/-! ## Deletes and cleared graphs -/

/-- The rows `filterDel` keeps. -/
def keepRow (cl : Nat → Bool) (del : List Row) (r : Row) : Bool := !del.contains r && !cl r.g

theorem filterDelGo_eq (cl : Nat → Bool) :
    ∀ (base del acc : List Row), Sorted base → Sorted del →
      filterDelGo cl base del acc = acc.reverse ++ base.filter (keepRow cl del) := by
  intro base del acc
  fun_induction filterDelGo cl base del acc with
  | case1 _ acc => intro _ _; simp
  | case2 b bs acc ih =>
    simp only [dite_eq_ite] at ih
    intro hb _
    rw [Sorted, List.pairwise_cons] at hb
    rw [ih hb.2 List.Pairwise.nil]
    by_cases hc : cl b.g = true
    · simp [hc, keepRow]
    · simp [hc, keepRow]
  | case3 b bs d ds acc hdb ih =>
    intro hb hd
    rw [Sorted, List.pairwise_cons] at hd
    rw [ih hb hd.2]
    congr 1
    apply List.filter_congr
    intro r hr
    have hne : r ≠ d := by
      rcases List.mem_cons.mp hr with e | e
      · subst e; exact (ne_of_lt hdb).symm
      · rw [Sorted, List.pairwise_cons] at hb
        exact (ne_of_lt (ScanTheorems.lt_trans hdb (hb.1 r e))).symm
    simp [keepRow, hne]
  | case4 b bs d ds acc hdb heq ih =>
    intro hb hd
    have heq' : d = b := by simpa using heq
    subst heq'
    rw [Sorted, List.pairwise_cons] at hb hd
    rw [ih hb.2 hd.2]
    have hkb : keepRow cl (d :: ds) d = false := by simp [keepRow]
    rw [List.filter_cons, hkb]
    simp only [Bool.false_eq_true, if_false]
    congr 1
    apply List.filter_congr
    intro r hr
    have hne : r ≠ d := (ne_of_lt (hb.1 r hr)).symm
    simp [keepRow, hne]
  | case5 b bs d ds acc hdb heq ih =>
    simp only [dite_eq_ite] at ih
    intro hb hd
    have hbd : b.lt d = true := by
      rcases lt_total b d with h | h | h
      · exact h
      · subst h; simp at heq
      · exact absurd h hdb
    rw [Sorted, List.pairwise_cons] at hb
    rw [ih hb.2 hd]
    have hnot : (d :: ds).contains b = false := by
      rw [Sorted, List.pairwise_cons] at hd
      cases hcon : (d :: ds).contains b
      · rfl
      · exfalso
        have hm : b ∈ d :: ds := by simpa using hcon
        rcases List.mem_cons.mp hm with e | e
        · exact ne_of_lt hbd e
        · have := ScanTheorems.lt_trans hbd (hd.1 b e)
          rw [lt_irrefl] at this; cases this
    have hkb : keepRow cl (d :: ds) b = !cl b.g := by
      unfold keepRow; rw [hnot]; rfl
    rw [List.filter_cons, hkb]
    cases hc : cl b.g <;> simp

theorem filterDel_eq (cl : Nat → Bool) (base del : List Row) (hb : Sorted base) (hd : Sorted del) :
    filterDel cl base del = base.filter (keepRow cl del) := by
  unfold filterDel; rw [filterDelGo_eq cl base del [] hb hd]; simp

/-! ## The union -/

theorem unionGo_mem : ∀ (xs ys acc : List Row) (r : Row),
    r ∈ unionGo xs ys acc ↔ r ∈ acc ∨ r ∈ xs ∨ r ∈ ys := by
  intro xs ys acc r
  fun_induction unionGo xs ys acc with
  | case1 ys acc => simp [List.reverseAux_eq]
  | case2 x xs acc => simp [List.reverseAux_eq]
  | case3 x xs y ys acc _ ih => rw [ih]; simp; grind
  | case4 x xs y ys acc _ _ ih => rw [ih]; simp; grind
  | case5 x xs y ys acc hxy hyx ih =>
    have e : x = y := by
      rcases lt_total x y with h | h | h
      · simp [h] at hxy
      · exact h
      · simp [h] at hyx
    subst e
    rw [ih]; simp; grind

theorem unionGo_sorted : ∀ (xs ys acc : List Row), Sorted xs → Sorted ys → Sorted acc.reverse →
    (∀ a ∈ acc, ∀ z, z ∈ xs ∨ z ∈ ys → a.lt z = true) → Sorted (unionGo xs ys acc) := by
  intro xs ys acc
  fun_induction unionGo xs ys acc with
  | case1 ys acc =>
    intro _ hy ha hlt
    rw [List.reverseAux_eq, Sorted, List.pairwise_append]
    exact ⟨ha, hy, fun a ha' z hz => hlt a (List.mem_reverse.mp ha') z (Or.inr hz)⟩
  | case2 x xs acc =>
    intro hx _ ha hlt
    rw [List.reverseAux_eq, Sorted, List.pairwise_append]
    exact ⟨ha, hx, fun a ha' z hz => hlt a (List.mem_reverse.mp ha') z (Or.inl hz)⟩
  | case3 x xs y ys acc hxy ih =>
    intro hx hy ha hlt
    rw [Sorted, List.pairwise_cons] at hx
    apply ih hx.2 hy
    · rw [List.reverse_cons, Sorted, List.pairwise_append]
      exact ⟨ha, List.pairwise_singleton _ _, fun a ha' z hz => by
        rw [List.mem_singleton] at hz; subst hz
        exact hlt a (List.mem_reverse.mp ha') z (Or.inl (List.mem_cons_self))⟩
    · intro a ha' z hz
      rcases List.mem_cons.mp ha' with e | e
      · subst e
        rcases hz with hz | hz
        · exact hx.1 z hz
        · rcases List.mem_cons.mp hz with e2 | e2
          · subst e2; exact hxy
          · rw [Sorted, List.pairwise_cons] at hy
            exact ScanTheorems.lt_trans hxy (hy.1 z e2)
      · rcases hz with hz | hz
        · exact hlt a e z (Or.inl (List.mem_cons_of_mem _ hz))
        · exact hlt a e z (Or.inr hz)
  | case4 x xs y ys acc _ hyx ih =>
    intro hx hy ha hlt
    rw [Sorted, List.pairwise_cons] at hy
    apply ih hx hy.2
    · rw [List.reverse_cons, Sorted, List.pairwise_append]
      exact ⟨ha, List.pairwise_singleton _ _, fun a ha' z hz => by
        rw [List.mem_singleton] at hz; subst hz
        exact hlt a (List.mem_reverse.mp ha') z (Or.inr (List.mem_cons_self))⟩
    · intro a ha' z hz
      rcases List.mem_cons.mp ha' with e | e
      · subst e
        rcases hz with hz | hz
        · rcases List.mem_cons.mp hz with e2 | e2
          · subst e2; exact hyx
          · rw [Sorted, List.pairwise_cons] at hx
            exact ScanTheorems.lt_trans hyx (hx.1 z e2)
        · exact hy.1 z hz
      · rcases hz with hz | hz
        · exact hlt a e z (Or.inl hz)
        · exact hlt a e z (Or.inr (List.mem_cons_of_mem _ hz))
  | case5 x xs y ys acc hxy hyx ih =>
    have e : x = y := by
      rcases lt_total x y with h | h | h
      · simp [h] at hxy
      · exact h
      · simp [h] at hyx
    subst e
    intro hx hy ha hlt
    rw [Sorted, List.pairwise_cons] at hx hy
    apply ih hx.2 hy.2
    · rw [List.reverse_cons, Sorted, List.pairwise_append]
      exact ⟨ha, List.pairwise_singleton _ _, fun a ha' z hz => by
        rw [List.mem_singleton] at hz; subst hz
        exact hlt a (List.mem_reverse.mp ha') z (Or.inl (List.mem_cons_self))⟩
    · intro a ha' z hz
      rcases List.mem_cons.mp ha' with e | e
      · subst e
        rcases hz with hz | hz
        · exact hx.1 z hz
        · exact hy.1 z hz
      · rcases hz with hz | hz
        · exact hlt a e z (Or.inl (List.mem_cons_of_mem _ hz))
        · exact hlt a e z (Or.inr (List.mem_cons_of_mem _ hz))

theorem unionRows_mem (xs ys : List Row) (r : Row) : r ∈ unionRows xs ys ↔ r ∈ xs ∨ r ∈ ys := by
  unfold unionRows; rw [unionGo_mem]; simp

theorem unionRows_sorted (xs ys : List Row) (hx : Sorted xs) (hy : Sorted ys) : Sorted (unionRows xs ys) :=
  unionGo_sorted xs ys [] hx hy List.Pairwise.nil (fun _ h => by cases h)

/-! ## The merge -/

theorem mergeRows_spec (cl : Nat → Bool) (base del ins : List Row)
    (hb : Sorted base) (hd : Sorted del) (hi : Sorted ins) :
    Sorted (mergeRows cl base del ins) ∧
      ∀ r, r ∈ mergeRows cl base del ins ↔ (r ∈ base ∧ r ∉ del ∧ cl r.g = false) ∨ r ∈ ins := by
  unfold mergeRows
  rw [filterDel_eq cl base del hb hd]
  refine ⟨unionRows_sorted _ _ (hb.filter _) hi, fun r => ?_⟩
  rw [unionRows_mem, List.mem_filter]
  simp [keepRow]

/-- A strictly sorted list is determined by its members. -/
theorem sorted_eq_of_mem_iff : ∀ (l1 l2 : List Row), Sorted l1 → Sorted l2 →
    (∀ r, r ∈ l1 ↔ r ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: as, b :: bs, h1, h2, h => by
    rw [Sorted, List.pairwise_cons] at h1 h2
    have hab : a = b := by
      rcases lt_total a b with c | c | c
      · -- b ∈ a :: as and b ≠ a, so a < b... contradiction with a ∈ b :: bs
        have ha := (h a).mp List.mem_cons_self
        rcases List.mem_cons.mp ha with e | e
        · exact e
        · have := ScanTheorems.lt_trans c (h2.1 a e)
          rw [lt_irrefl] at this; cases this
      · exact c
      · have hb := (h b).mpr List.mem_cons_self
        rcases List.mem_cons.mp hb with e | e
        · exact e.symm
        · have := ScanTheorems.lt_trans c (h1.1 b e)
          rw [lt_irrefl] at this; cases this
    subst hab
    congr 1
    apply sorted_eq_of_mem_iff as bs h1.2 h2.2
    intro r
    constructor
    · intro hr
      rcases List.mem_cons.mp ((h r).mp (List.mem_cons_of_mem _ hr)) with e | e
      · subst e; have := h1.1 r hr; rw [lt_irrefl] at this; cases this
      · exact e
    · intro hr
      rcases List.mem_cons.mp ((h r).mpr (List.mem_cons_of_mem _ hr)) with e | e
      · subst e; have := h2.1 r hr; rw [lt_irrefl] at this; cases this
      · exact e

/-- The merge is the one strictly sorted list of the rows
    `(r ∈ base ∧ r ∉ del ∧ cl r.g = false) ∨ r ∈ ins`. -/
theorem mergeRows_eq_of_spec (cl : Nat → Bool) (base del ins out : List Row)
    (hb : Sorted base) (hd : Sorted del) (hi : Sorted ins) (ho : Sorted out)
    (hmem : ∀ r, r ∈ out ↔ (r ∈ base ∧ r ∉ del ∧ cl r.g = false) ∨ r ∈ ins) :
    mergeRows cl base del ins = out := by
  obtain ⟨hs, hm⟩ := mergeRows_spec cl base del ins hb hd hi
  exact sorted_eq_of_mem_iff _ _ hs ho fun r => by rw [hm, hmem]

/-! ## Replay -/

theorem step_add (base : Row → Bool) (st : State) (q r : Row) :
    denote base (step st (.add q)) r = (denote base st r || q == r) := by
  simp only [denote, step, Std.HashSet.contains_insert, Std.HashSet.contains_erase]
  by_cases h : q = r
  · subst h; simp
  · have : (q == r) = false := by simpa using h
    simp [this]

theorem step_remove (base : Row → Bool) (st : State) (q r : Row) :
    denote base (step st (.remove q)) r = (denote base st r && !(q == r)) := by
  simp only [denote, step, Std.HashSet.contains_insert, Std.HashSet.contains_erase]
  by_cases h : q = r
  · subst h; simp
  · have : (q == r) = false := by simpa using h
    simp [this]

theorem contains_filter (m : Std.HashSet Row) (f : Row → Bool) (r : Row) :
    (m.filter f).contains r = (m.contains r && f r) := by
  cases hc : (m.filter f).contains r
  · cases hm : m.contains r
    · rfl
    · cases hf : f r
      · rfl
      · exfalso
        have hmem : r ∈ m := Std.HashSet.mem_iff_contains.mpr hm
        have : r ∈ m.filter f := Std.HashSet.mem_filter.mpr ⟨hmem, by rw [Std.HashSet.get_eq]; exact hf⟩
        rw [Std.HashSet.mem_iff_contains, hc] at this; cases this
  · have hmem : r ∈ m.filter f := Std.HashSet.mem_iff_contains.mpr hc
    obtain ⟨h, hf⟩ := Std.HashSet.mem_filter.mp hmem
    rw [Std.HashSet.get_eq] at hf
    rw [Std.HashSet.mem_iff_contains.mp h, hf]; rfl

theorem step_clear (base : Row → Bool) (st : State) (g : Nat) (r : Row) :
    denote base (step st (.clear g)) r = (denote base st r && r.g != g) := by
  have hcl : ∀ x, (if st.cleared.contains g = true then st.cleared else g :: st.cleared).contains x
      = (st.cleared.contains x || x == g) := by
    intro x
    by_cases h : st.cleared.contains g = true
    · rw [if_pos h]
      by_cases hx : x = g
      · subst hx; rw [h]; simp
      · have : (x == g) = false := by simpa using hx
        simp [this]
    · rw [if_neg h, List.contains_cons, Bool.or_comm]
  simp only [denote, step]
  rw [contains_filter, hcl]
  cases h1 : base r <;> cases h2 : st.del.contains r <;> cases h3 : st.cleared.contains r.g <;>
    cases h4 : st.ins.contains r <;> cases h5 : (r.g == g) <;> simp_all

theorem replay_append (st : State) (a b : List Op) :
    Overlay.replay st (a ++ b) = Overlay.replay (Overlay.replay st a) b := by
  simp [Overlay.replay, List.foldl_append]

/-- An empty state denotes the base. -/
theorem denote_empty (base : Row → Bool) (r : Row) : denote base {} r = base r := by
  simp [denote]

#print axioms filterDel_eq
#print axioms unionRows_sorted
#print axioms mergeRows_spec
#print axioms mergeRows_eq_of_spec
#print axioms step_add
#print axioms step_remove
#print axioms step_clear

end L4Factoidal.Storage.Sbm11.OverlayTheorems
