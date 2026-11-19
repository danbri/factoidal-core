import L4Factoidal.SPARQL.StoreEndpointTheorems
import L4Factoidal.SPARQL.StoreReplayTheorems

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF
open L4Factoidal.Storage (DeltaEntry)

private abbrev IsDefault (e : DeltaEntry) : Prop :=
  match e with
  | .add _ none | .remove _ none | .clear none => True
  | _ => False

/-- Kind: delta entry classification.
Says: a named graph delta has only named operations.
Does not say: that the named graph exists in the input. -/
private theorem graphDelta_named_excludes_default (key : Iri) (old new : Graph) :
    ∀ e ∈ graphDelta (some key) old new, ¬ IsDefault e := by
  intro e he
  simp only [graphDelta] at he
  split at he
  · have heq := List.mem_singleton.mp he
    subst e
    intro h
    exact h
  · rcases List.mem_append.mp he with hm | hm
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
      intro h
      exact h
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
      intro h
      exact h

/-- Kind: list invariant.
Says: a wholly default-only batch cannot contain a named-only suffix.
Does not say: which function produced the lists. -/
private theorem append_eq_prefix_of_default
    (pre tail : List DeltaEntry)
    (ha : ∀ e ∈ pre ++ tail, IsDefault e)
    (ht : ∀ e ∈ tail, ¬ IsDefault e) :
    pre ++ tail = pre := by
  cases tail with
  | nil => exact List.append_nil pre
  | cons first rest =>
    have hm : first ∈ first :: rest := List.mem_cons_self
    exact False.elim (ht first hm (ha first (List.mem_append.mpr (Or.inr hm))))

/-- Kind: dataset delta decomposition.
Says: a successful default-only batch is exactly the default graph delta.
Does not say: that arbitrary input datasets produce a default-only batch. -/
private theorem datasetDelta_default_entries {old new : Dataset} {entries : List DeltaEntry}
    (hd : datasetDelta old new = .ok entries)
    (ha : ∀ e ∈ entries, IsDefault e) :
    entries = graphDelta none old.default new.default := by
  unfold datasetDelta at hd
  split at hd
  · cases hd
  · have heq : _ ++ _ ++ _ ++ _ = entries := Except.ok.inj hd
    rw [← heq] at ha ⊢
    have hchanges := append_eq_prefix_of_default _ _ ha (by
      intro e he
      obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp he
      split at hp
      · exact graphDelta_named_excludes_default _ _ _ e hp
      · cases hp)
    rw [hchanges] at ha ⊢
    have hcreates := append_eq_prefix_of_default _ _ ha (by
      intro e he
      obtain ⟨_, _, hp⟩ := List.mem_flatMap.mp he
      rcases List.mem_cons.mp hp with rfl | hm
      · intro h
        exact h
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
        intro h
        exact h)
    rw [hcreates] at ha ⊢
    exact append_eq_prefix_of_default _ _ ha (by
      intro e he
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
      intro h
      exact h)

/-- Kind: endpoint correspondence.
Says: an admitted default-only commit carries the exact computed dataset delta.
Does not say: that a successful dataset delta is always admitted. -/
private theorem datasetDelta_ok_of_commit {old new committed : Dataset}
    {response : HTTP.Response} {entries : List DeltaEntry}
    (h : (commitOutcome .defaultGraph old new response).commit = some (entries, committed)) :
    datasetDelta old new = .ok entries := by
  cases hd : datasetDelta old new with
  | error why => simp [commitOutcome, hd, text] at h
  | ok delta =>
    cases delta with
    | nil => simp [commitOutcome, hd] at h
    | cons first rest =>
      cases hs : scopeRefusal .defaultGraph (first :: rest) with
      | some why => simp [commitOutcome, hd, hs, text] at h
      | none =>
        have heq : some (first :: rest, new) = some (entries, committed) := by
          simpa only [commitOutcome, hd, hs] using h
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rw [heq.1]

/-- Kind: endpoint and replay correspondence (factoidal-core issue 620).
Says: an admitted default-only commit's actual batch is the default graph
delta. Replaying it preserves the exact old named list and matches target
default-graph membership for every triple, including with duplicate triples.
Does not say: that replay preserves default list order or multiplicity,
that the target has the same named list, or that the host persisted the batch. -/
theorem commitOutcome_defaultGraph_replay {old new committed : Dataset}
    {response : HTTP.Response} {entries : List DeltaEntry}
    (h : (commitOutcome .defaultGraph old new response).commit = some (entries, committed)) :
    entries = graphDelta none old.default new.default ∧
      (applyDeltaEntries old entries).named = old.named ∧
      ∀ t, Graph.mem t (applyDeltaEntries old entries).default = Graph.mem t new.default := by
  obtain ⟨_, _, hall, hnamed⟩ := commitOutcome_defaultGraph_replay_named h
  have hentries := datasetDelta_default_entries (datasetDelta_ok_of_commit h) hall
  refine ⟨hentries, hnamed, ?_⟩
  rw [hentries]
  exact graphDelta_default_replay_mem old new.default

#print axioms commitOutcome_defaultGraph_replay

end L4Factoidal.SPARQL.StoreEndpoint
