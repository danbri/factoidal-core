import L4Factoidal.SPARQL.StoreEndpoint
import L4Factoidal.RDF.DatasetSet

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF
open L4Factoidal.Storage (DeltaEntry)

/-- Kind: representation bridge.
Says: the hash fold used by the endpoint detects membership in the starting
set or the list of inserted triples.
Does not say: that the list has no duplicates. -/
private theorem replay_raw_contains (g : Graph) (s : Std.HashSet Triple) (t : Triple) :
    (g.foldl (fun acc u => acc.insert u) s).contains t = true ↔
      s.contains t = true ∨ t ∈ g := by
  induction g generalizing s with
  | nil => simp
  | cons u us ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
      List.mem_cons, eq_comm (a := u) (b := t), or_assoc]
    exact or_left_comm

private theorem replay_raw_empty_contains (g : Graph) (t : Triple) :
    (g.foldl (fun acc u => acc.insert u) (∅ : Std.HashSet Triple)).contains t = true ↔
      t ∈ g := by
  rw [replay_raw_contains g ∅ t, Std.HashSet.contains_empty]
  simp

/-- Kind: replay invariant.
Says: a batch of default removals preserves existing key uniqueness and
removes exactly the triples in the removal list.
Does not say: anything about the persistence of the batch. -/
private theorem replay_default_removes (ds : Dataset) (removed : Graph) :
    let r := applyDeltaEntries ds (removed.map (fun u => DeltaEntry.remove u none))
    (ds.default.KeyNodup → r.default.KeyNodup) ∧
      (∀ t, t ∈ r.default ↔ t ∈ ds.default ∧ t ∉ removed) := by
  induction removed generalizing ds with
  | nil => simp [applyDeltaEntries]
  | cons u us ih =>
    let next := applyDeltaEntry ds (.remove u none)
    have hnext : next.default = ds.default.remove u := rfl
    change (ds.default.KeyNodup →
      (applyDeltaEntries next (us.map (fun v => .remove v none))).default.KeyNodup) ∧
      (∀ t, t ∈ (applyDeltaEntries next (us.map (fun v => .remove v none))).default ↔ _)
    refine ⟨?_, ?_⟩
    · intro h
      apply (ih next).1
      rw [hnext]
      exact List.Nodup.sublist (List.filter_sublist.map Triple.key) h
    · intro t
      rw [(ih next).2 t, hnext]
      simp only [Graph.remove, List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff,
        List.mem_cons, not_or, and_assoc]
      change (t ∈ ds.default ∧ ¬(t.eqb u = true) ∧ t ∉ us) ↔
        (t ∈ ds.default ∧ t ≠ u ∧ t ∉ us)
      rw [Triple.eqb_iff_eq t u]

/-- Kind: replay invariant.
Says: a batch of default additions preserves existing key uniqueness and
retains the triples from the initial default graph and the addition list.
Does not say: anything about the order of the result. -/
private theorem replay_default_adds (ds : Dataset) (added : Graph) :
    let r := applyDeltaEntries ds (added.map (fun u => DeltaEntry.add u none))
    (ds.default.KeyNodup → r.default.KeyNodup) ∧
      (∀ t, t ∈ r.default ↔ t ∈ ds.default ∨ t ∈ added) := by
  induction added generalizing ds with
  | nil => simp [applyDeltaEntries]
  | cons u us ih =>
    let next := applyDeltaEntry ds (.add u none)
    have hnext : next.default = ds.default.add u := rfl
    change (ds.default.KeyNodup →
      (applyDeltaEntries next (us.map (fun v => .add v none))).default.KeyNodup) ∧
      (∀ t, t ∈ (applyDeltaEntries next (us.map (fun v => .add v none))).default ↔ _)
    refine ⟨?_, ?_⟩
    · intro h
      exact (ih next).1 (h.add u)
    · intro t
      rw [(ih next).2 t, hnext, List.mem_cons, ← Graph.mem_iff t (ds.default.add u),
        mem_graph_add, Bool.or_eq_true, Graph.mem_iff t ds.default, Triple.eqb_iff_eq,
        eq_comm (a := u) (b := t), or_assoc]

/-- Kind: graph delta and replay correspondence.
Says: default replay matches target membership and preserves existing key
uniqueness.
Does not say: that replay eliminates duplicates among retained triples. -/
private theorem replay_graphDelta_default (ds : Dataset) (target : Graph) :
    let r := applyDeltaEntries ds (graphDelta none ds.default target)
    (ds.default.KeyNodup → r.default.KeyNodup) ∧
      (∀ t, Graph.mem t r.default = Graph.mem t target) := by
  have hjoin (removed added : Graph) :
      applyDeltaEntries ds
          (removed.map (fun u => .remove u none) ++ added.map (fun u => .add u none)) =
        applyDeltaEntries (applyDeltaEntries ds (removed.map (fun u => .remove u none)))
          (added.map (fun u => .add u none)) := by
    simp only [applyDeltaEntries, List.foldl_append]
  change (ds.default.KeyNodup →
    (applyDeltaEntries ds (graphDelta none ds.default target)).default.KeyNodup) ∧ _
  by_cases hclear : (target.isEmpty && !ds.default.isEmpty) = true
  · have hempty : target = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp hclear).1
    have hdelta : graphDelta none ds.default target = [.clear none] := by
      simp only [graphDelta, if_pos hclear] <;> rfl
    rw [hdelta]
    change (ds.default.KeyNodup → Graph.KeyNodup []) ∧
      (∀ t, Graph.mem t [] = Graph.mem t target)
    subst target
    exact ⟨fun _ => Graph.keyNodup_nil, fun _ => rfl⟩
  · let removed := ds.default.filter fun u =>
      !(target.foldl (fun (s : Std.HashSet Triple) v => s.insert v) {}).contains u
    let added := target.filter fun u =>
      !(ds.default.foldl (fun (s : Std.HashSet Triple) v => s.insert v) {}).contains u
    have hdelta : graphDelta none ds.default target =
        removed.map (fun u => .remove u none) ++ added.map (fun u => .add u none) := by
      simp only [graphDelta, if_neg hclear] <;> rfl
    have hremoved (u : Triple) : u ∈ removed ↔ u ∈ ds.default ∧ u ∉ target := by
      simp only [removed, List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff]
      change (u ∈ ds.default ∧
        ¬((target.foldl (fun acc v => acc.insert v) (∅ : Std.HashSet Triple)).contains u = true)) ↔ _
      rw [replay_raw_empty_contains target u]
    have hadded (u : Triple) : u ∈ added ↔ u ∈ target ∧ u ∉ ds.default := by
      simp only [added, List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff]
      change (u ∈ target ∧
        ¬((ds.default.foldl (fun acc v => acc.insert v) (∅ : Std.HashSet Triple)).contains u = true)) ↔ _
      rw [replay_raw_empty_contains ds.default u]
    let kept := applyDeltaEntries ds (removed.map (fun u => .remove u none))
    have hremoves := replay_default_removes ds removed
    have hadds := replay_default_adds kept added
    rw [hdelta, hjoin]
    refine ⟨fun h => hadds.1 (hremoves.1 h), ?_⟩
    intro t
    apply Bool.eq_iff_iff.mpr
    change Graph.mem t (applyDeltaEntries kept (added.map (fun u => .add u none))).default = true ↔ _
    rw [Graph.mem_iff t (applyDeltaEntries kept (added.map (fun u => .add u none))).default,
      Graph.mem_iff t target, hadds.2 t, hremoves.2 t, hremoved t, hadded t]
    constructor
    · rintro (⟨hold, hnremove⟩ | ⟨hnew, _⟩)
      · by_cases hnew : t ∈ target
        · exact hnew
        · exact False.elim (hnremove ⟨hold, hnew⟩)
      · exact hnew
    · intro hnew
      by_cases hold : t ∈ ds.default
      · exact Or.inl ⟨hold, fun hr => hr.2 hnew⟩
      · exact Or.inr ⟨hnew, hold⟩

/-- Kind: graph delta and replay correspondence (factoidal-core issue 620).
Says: replaying the actual default graph delta matches target RDF membership
for every triple, even if either input list has duplicates.
Does not say: that the lists agree in order or multiplicity, or that the
host persists and reads back the batch. -/
theorem graphDelta_default_replay_mem (ds : Dataset) (target : Graph) :
    ∀ t, Graph.mem t (applyDeltaEntries ds (graphDelta none ds.default target)).default =
      Graph.mem t target :=
  (replay_graphDelta_default ds target).2

/-- Kind: graph delta and replay invariant (factoidal-core issue 620).
Says: when the old default graph has unique RDF keys, default replay has
unique keys and matches target RDF membership, even for a target with
duplicates.
Does not say: that the old graph of every request is key-unique or that
the live target has unique keys. -/
theorem graphDelta_default_replay_default
    (ds : Dataset) (target : Graph) (hold : ds.default.KeyNodup) :
    let r := applyDeltaEntries ds (graphDelta none ds.default target)
    r.default.KeyNodup ∧ ∀ t, Graph.mem t r.default = Graph.mem t target :=
  ⟨(replay_graphDelta_default ds target).1 hold, graphDelta_default_replay_mem ds target⟩

#print axioms graphDelta_default_replay_mem
#print axioms graphDelta_default_replay_default

end L4Factoidal.SPARQL.StoreEndpoint
