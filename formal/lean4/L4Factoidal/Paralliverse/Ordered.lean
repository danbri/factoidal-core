/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/

/-!
Import this module for the collector and its sequential evaluation theorem. The CPU packing
application is in `L4Factoidal.Paralliverse.OrderedPackTheorems`. The selected-block scan
application is in `L4Factoidal.Storage.Sbm11.OrderedScanTheorems`.
-/

namespace L4Factoidal.Paralliverse.Ordered

/-- Restore planned task order. Every ordinal below `n` must occur exactly once.
Values need no equality test. Ordinals are local to the supplied job. -/
def collect? {α : Type} (n : Nat) (replies : List (Nat × α)) : Option (List α) :=
  let sorted := replies.mergeSort (fun a b => decide (a.1 ≤ b.1))
  if sorted.map Prod.fst = List.range n then some (sorted.map Prod.snd) else none

/-- Kind: invariant.
Says: an ordinal in the planned list identifies a unique pair.
Does not say: that the values at distinct ordinals differ. -/
private theorem range_zip_unique {α : Type} {n : Nat} {values : List α} {a b : Nat × α}
    (ha : a ∈ (List.range n).zip values) (hb : b ∈ (List.range n).zip values)
    (hkey : a.1 = b.1) : a = b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  have hij : i = j := by simpa only [List.getElem_zip, List.getElem_range] using hkey
  subst j
  rfl

/-- Kind: exact success criterion.
Says: collection returns exactly the planned values when the replies are any permutation
of those values paired with all task ordinals, once each.
Does not say: who computed the values, which job sent them or when they arrive. -/
theorem collect?_eq_some_iff {α : Type} (n : Nat) (replies : List (Nat × α)) (values : List α) :
    collect? n replies = some values ↔
      values.length = n ∧ replies.Perm ((List.range n).zip values) := by
  let cmp := fun (a b : Nat × α) => decide (a.1 ≤ b.1)
  let sorted := replies.mergeSort cmp
  have hp : sorted.Perm replies := List.mergeSort_perm replies cmp
  change (if sorted.map Prod.fst = List.range n then some (sorted.map Prod.snd) else none)
    = some values ↔ _
  constructor
  · intro h
    split at h
    next hk =>
      cases h
      refine ⟨?_, hp.symm.trans (List.Perm.of_eq (List.zip_of_prod hk rfl))⟩
      simpa only [List.length_map, List.length_range] using congrArg List.length hk
    next => contradiction
  · rintro ⟨hlen, hd⟩
    let planned := (List.range n).zip values
    have hperm : sorted.Perm planned := hp.trans hd
    have hkeys : planned.map Prod.fst = List.range n := List.map_fst_zip (by simp [hlen])
    have hvalues : planned.map Prod.snd = values := List.map_snd_zip (by simp [hlen])
    have ht (a b c : Nat × α) (hab : cmp a b) (hbc : cmp b c) : cmp a c :=
      decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    have hall (a b : Nat × α) : cmp a b || cmp b a := by
      simpa [cmp] using Nat.le_total a.1 b.1
    have hs : sorted.Pairwise (fun a b => a.1 ≤ b.1) := by
      simpa only [cmp, decide_eq_true_eq] using List.pairwise_mergeSort ht hall replies
    have hc : planned.Pairwise (fun a b => a.1 ≤ b.1) := by
      apply (List.pairwise_map (f := Prod.fst) (R := (· ≤ ·))).mp
      rw [hkeys]
      exact List.pairwise_le_range
    have heq : sorted = planned := List.Perm.eq_of_pairwise
      (fun a b ha hb hab hba => range_zip_unique (hperm.mem_iff.mp ha) hb (Nat.le_antisymm hab hba))
      hs hc hperm
    rw [heq, if_pos hkeys, hvalues]

/-- Kind: invariant.
Says: agreement at each corresponding position lifts to successful sequential traversal.
Does not say: that a failing or incomplete traversal produced all values. -/
private theorem mapM_eq_ok_of_get {α β ε : Type} (run : α → Except ε β) (tasks : List α) :
    ∀ (values : List β), values.length = tasks.length →
      (∀ (i : Nat) (t : α) (v : β), tasks[i]? = some t → values[i]? = some v → run t = .ok v) →
      tasks.mapM run = .ok values := by
  induction tasks with
  | nil =>
    intro values hlen _
    cases values with
    | nil => rfl
    | cons => simp at hlen
  | cons t ts ih =>
    intro values hlen hvalid
    cases values with
    | nil => simp at hlen
    | cons v vs =>
      have hhead := hvalid 0 t v rfl rfl
      have htail := ih vs (Nat.succ.inj hlen)
        (fun i a b ha hb => hvalid (i + 1) a b ha hb)
      simp only [List.mapM_cons, hhead, htail]
      rfl

/-- Kind: refinement.
Says: a complete collection of replies that agree with the evaluator on their assigned
tasks gives exactly the sequential successful traversal, in planned order.
Does not say: that execution terminates or that transported answers satisfy the evaluator. -/
theorem mapM_eq_of_collect? {α β ε : Type} (tasks : List α) (run : α → Except ε β)
    (replies : List (Nat × β)) (values : List β)
    (hcollected : collect? tasks.length replies = some values)
    (hvalid : ∀ i t v, tasks[i]? = some t → (i, v) ∈ replies → run t = .ok v) :
    tasks.mapM run = .ok values := by
  obtain ⟨hlen, hp⟩ := (collect?_eq_some_iff _ _ _).mp hcollected
  apply mapM_eq_ok_of_get run tasks values hlen
  intro i t v ht hv
  apply hvalid i t v ht
  apply hp.mem_iff.mpr
  obtain ⟨hvi, he⟩ := List.getElem?_eq_some_iff.mp hv
  have hz : i < ((List.range tasks.length).zip values).length := by simpa [hlen] using hvi
  exact List.mem_iff_getElem.mpr ⟨i, hz, by simp only [List.getElem_zip, List.getElem_range, he]⟩

#print axioms collect?_eq_some_iff
#print axioms mapM_eq_of_collect?

end L4Factoidal.Paralliverse.Ordered
