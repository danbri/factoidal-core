import Init

namespace L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin

def entryLe (a b : UInt64 × Nat) : Bool := decide (a.1 ≤ b.1)

def sortEntries (entries : List (UInt64 × Nat)) : List (UInt64 × Nat) :=
  entries.mergeSort entryLe

theorem entryLe_trans (a b c : UInt64 × Nat)
    (hab : entryLe a b) (hbc : entryLe b c) : entryLe a c := by
  simp only [entryLe, decide_eq_true_eq] at *
  exact UInt64.le_trans hab hbc

theorem entryLe_total (a b : UInt64 × Nat) : entryLe a b || entryLe b a := by
  simp only [entryLe, Bool.or_eq_true, decide_eq_true_eq]
  exact UInt64.le_total a.1 b.1

/-- Kind: implementation permutation.
    Says: the actual stable index constructor retains every input occurrence.
    Does not say: a GPU runtime implements the index search. -/
theorem sortEntries_perm (entries : List (UInt64 × Nat)) :
    (sortEntries entries).Perm entries := List.mergeSort_perm _ _

/-- Kind: sorted-index invariant.
    Says: keys produced by the actual constructor are nondecreasing.
    Does not say: an independently supplied index is sorted. -/
theorem sortEntries_sorted (entries : List (UInt64 × Nat)) :
    (sortEntries entries).Pairwise (fun a b => a.1 ≤ b.1) := by
  have h := List.pairwise_mergeSort entryLe_trans entryLe_total entries
  simpa only [sortEntries, entryLe, decide_eq_true_eq] using h

/-- Kind: ordered join refinement.
    Says: selecting one equality key after the actual index sort returns
    exactly the original ordered occurrences, not merely the same set.
    Does not say: a query can replace RDF equality by an arbitrary hash. -/
theorem filter_sortEntries (entries : List (UInt64 × Nat)) (key : UInt64) :
    (sortEntries entries).filter (fun x => x.1 == key) =
      entries.filter (fun x => x.1 == key) := by
  let keep := fun x : UInt64 × Nat => x.1 == key
  have hs : (entries.filter keep).Pairwise (fun a b => entryLe a b = true) := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have ha' : a.1 = key := by
      simpa only [keep, beq_iff_eq] using (List.mem_filter.mp ha).2
    have hb' : b.1 = key := by
      simpa only [keep, beq_iff_eq] using (List.mem_filter.mp hb).2
    simp [entryLe, ha', hb']
  have hsub := List.sublist_mergeSort entryLe_trans entryLe_total
    hs (List.filter_sublist (p := keep) (l := entries))
  have hsub' := hsub.filter keep
  simp only [List.filter_filter, Bool.and_self] at hsub'
  have hp := List.Perm.filter keep (sortEntries_perm entries)
  exact (hsub'.eq_of_length hp.length_eq.symm).symm

#print axioms sortEntries_perm
#print axioms sortEntries_sorted
#print axioms filter_sortEntries

end L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin
