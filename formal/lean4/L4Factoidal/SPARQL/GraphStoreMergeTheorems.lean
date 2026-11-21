import L4Factoidal.SPARQL.GraphStoreService
import L4Factoidal.RDF.DocumentScope

namespace L4Factoidal.SPARQL.GraphStoreService

open L4Factoidal.RDF

private abbrev candidatePrefix (stem : String) (k : Nat) : String :=
  stem ++ toString k ++ "_"

private theorem candidateIndex_eq {stem label : String} {k j : Nat}
    (hk : label.startsWith (candidatePrefix stem k) = true)
    (hj : label.startsWith (candidatePrefix stem j) = true) : k = j := by
  obtain ⟨ks, hks⟩ := String.startsWith_string_iff.mp hk
  obtain ⟨js, hjs⟩ := String.startsWith_string_iff.mp hj
  have h := hks.trans hjs.symm
  simp only [candidatePrefix, String.toList_append, List.append_assoc] at h
  have ht := (List.append_right_inj stem.toList).mp h
  have hd : docLabel k (String.ofList ks) = docLabel j (String.ofList js) := by
    apply String.toList_inj.mp
    simpa only [docLabel, docScope, String.toList_append, String.toList_ofList,
      List.append_assoc] using congrArg (fun xs => "d".toList ++ xs) ht
  exact (docLabel_inj hd).1

private theorem freshPrefix_search_ne_none (stem : String) (labels : List BNodeId) :
    ((List.range (labels.length + 1)).map (candidatePrefix stem)).find?
      (fun c => !labels.any (fun l => l.startsWith c)) ≠ none := by
  classical
  intro hnone
  have covered (k : Fin (labels.length + 1)) :
      ∃ l ∈ labels, l.startsWith (candidatePrefix stem k.val) = true := by
    have hm : candidatePrefix stem k.val ∈
        (List.range (labels.length + 1)).map (candidatePrefix stem) :=
      List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩
    have hn := List.find?_eq_none.mp hnone _ hm
    apply List.any_eq_true.mp
    cases ha : labels.any (fun l => l.startsWith (candidatePrefix stem k.val)) <;>
      simp [ha] at hn ⊢
  let chooseLabel (k : Fin (labels.length + 1)) := Classical.choose (covered k)
  have labelSpec (k : Fin (labels.length + 1)) :
      chooseLabel k ∈ labels ∧ (chooseLabel k).startsWith (candidatePrefix stem k.val) = true :=
    Classical.choose_spec (covered k)
  have hinj : Function.Injective chooseLabel := by
    intro i j h
    apply Fin.ext
    have hj : (chooseLabel i).startsWith (candidatePrefix stem j.val) = true := by
      rw [h]
      exact (labelSpec j).2
    exact candidateIndex_eq (labelSpec i).2 hj
  have hnd : ((List.finRange (labels.length + 1)).map chooseLabel).Nodup :=
    List.Pairwise.map chooseLabel (fun _ _ hne he => hne (hinj he)) (List.nodup_finRange _)
  have hsub : (List.finRange (labels.length + 1)).map chooseLabel ⊆ labels := by
    intro l hl
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hl
    exact (labelSpec k).1
  have hlen : labels.length + 1 ≤ labels.length := by
    simpa only [List.length_map, List.length_finRange] using hnd.length_le_of_subset hsub
  exact Nat.not_succ_le_self _ hlen

private theorem freshPrefix_spec (stem : String) (labels : List BNodeId) :
    (∃ k < labels.length + 1, freshPrefix stem labels = candidatePrefix stem k) ∧
    ∀ l ∈ labels, l.startsWith (freshPrefix stem labels) = false := by
  let candidates := (List.range (labels.length + 1)).map (candidatePrefix stem)
  let unused (c : String) := !labels.any (fun l => l.startsWith c)
  cases hfind : candidates.find? unused with
  | none => exact (freshPrefix_search_ne_none stem labels hfind).elim
  | some c =>
    have hresult : freshPrefix stem labels = c := by
      change (candidates.find? unused).getD (stem ++ "_") = c
      simp only [hfind, Option.getD_some]
    have hm : c ∈ candidates := List.mem_of_find?_eq_some hfind
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (show c ∈
      (List.range (labels.length + 1)).map (candidatePrefix stem) from hm)
    refine ⟨⟨k, List.mem_range.mp hk, hresult⟩, ?_⟩
    rw [hresult]
    have hu : unused (candidatePrefix stem k) = true := List.find?_some hfind
    have ha : (labels.any (fun l => l.startsWith (candidatePrefix stem k))) = false := by
      simpa [unused] using hu
    intro l hl
    exact Bool.eq_false_iff.mpr (List.any_eq_false.mp ha l hl)

/-- Kind: allocator postcondition.
Says: no supplied label starts with the prefix chosen by the graph store.
Does not say: that a caller supplied every label in an RDF dataset. -/
theorem freshPrefix_fresh (stem : String) (labels : List BNodeId) :
    ∀ l ∈ labels, l.startsWith (freshPrefix stem labels) = false :=
  (freshPrefix_spec stem labels).2

/-- Kind: allocator bound.
Says: the chosen prefix comes from the first `labels.length + 1` numbered
candidates, so the fallback is unreachable.
Does not say: that constructing or comparing an individual string takes
constant time. -/
theorem freshPrefix_candidate (stem : String) (labels : List BNodeId) :
    ∃ k < labels.length + 1, freshPrefix stem labels = stem ++ toString k ++ "_" :=
  (freshPrefix_spec stem labels).1

#print axioms freshPrefix_fresh
#print axioms freshPrefix_candidate

end L4Factoidal.SPARQL.GraphStoreService
