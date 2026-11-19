import L4Factoidal.SPARQL.StoreEndpoint

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF
open L4Factoidal.Storage (DeltaEntry)

private abbrev DefaultEntry (e : DeltaEntry) : Prop :=
  match e with
  | .add _ none | .remove _ none | .clear none => True
  | _ => False

private theorem defaultEntries_of_scopeRefusal_none {entries : List DeltaEntry}
    (h : scopeRefusal .defaultGraph entries = none) (e : DeltaEntry) (he : e ∈ entries) :
    DefaultEntry e := by
  have hn : (entries.any fun entry => match entry with
      | .add _ (some _) | .remove _ (some _) | .clear (some _) | .drop _ | .create _ => true
      | _ => false) = false := by
    apply Bool.eq_false_iff.mpr
    intro hguard
    unfold scopeRefusal at h
    rw [hguard] at h
    cases h
  have hentry := List.any_eq_false.mp hn e he
  cases e with
  | add _ g | remove _ g | clear g =>
    cases g
    · trivial
    · exact False.elim (hentry rfl)
  | drop _ | create _ => exact False.elim (hentry rfl)

private theorem applyDeltaEntry_named (ds : Dataset) (e : DeltaEntry) (h : DefaultEntry e) :
    (applyDeltaEntry ds e).named = ds.named := by
  cases e with
  | add _ g | remove _ g | clear g =>
    cases g
    · rfl
    · cases h
  | drop _ | create _ => cases h

private theorem applyDeltaEntries_named (ds : Dataset) (entries : List DeltaEntry)
    (h : ∀ e ∈ entries, DefaultEntry e) :
    (applyDeltaEntries ds entries).named = ds.named := by
  induction entries generalizing ds with
  | nil => rfl
  | cons e rest ih =>
    have head := h e List.mem_cons_self
    have tail : ∀ entry ∈ rest, DefaultEntry entry :=
      fun entry he => h entry (List.mem_cons_of_mem e he)
    calc
      (applyDeltaEntries ds (e :: rest)).named = (applyDeltaEntry ds e).named :=
        ih (applyDeltaEntry ds e) tail
      _ = ds.named := applyDeltaEntry_named ds e head

/-- Kind: adapter and replay invariant.
Says: an admitted default-only commit carries the requested dataset and a
nonempty batch of default-graph operations. Applying that batch preserves the
old named graph list exactly.
Does not say: that the live target's named list is identical as a list, that
the whole replay equals the target, or that the host appended the batch. -/
theorem commitOutcome_defaultGraph_replay_named {old new committed : Dataset}
    {response : HTTP.Response} {entries : List DeltaEntry}
    (h : (commitOutcome .defaultGraph old new response).commit = some (entries, committed)) :
    committed = new ∧ entries ≠ [] ∧
      (∀ e ∈ entries, match e with
        | .add _ none | .remove _ none | .clear none => True
        | _ => False) ∧
      (applyDeltaEntries old entries).named = old.named := by
  cases hdelta : datasetDelta old new with
  | error why => simp [commitOutcome, hdelta, text] at h
  | ok delta =>
    cases delta with
    | nil => simp [commitOutcome, hdelta] at h
    | cons first rest =>
      cases hscope : scopeRefusal .defaultGraph (first :: rest) with
      | some why => simp [commitOutcome, hdelta, hscope, text] at h
      | none =>
        have hinj : some (first :: rest, new) = some (entries, committed) := by
          simpa only [commitOutcome, hdelta, hscope] using h
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj
        obtain ⟨rfl, rfl⟩ := hinj
        have hentries : ∀ e ∈ first :: rest, DefaultEntry e :=
          defaultEntries_of_scopeRefusal_none hscope
        exact ⟨rfl, List.cons_ne_nil first rest, hentries, applyDeltaEntries_named old _ hentries⟩

/-- Kind: adapter invariant.
Says: the read-only endpoint profile emits no commit for a write attempt,
including a write whose computed delta is empty.
Does not say: that the host's durable state is unchanged by unrelated actions. -/
theorem commitOutcome_readOnly_no_commit (old new : Dataset) (response : HTTP.Response) :
    (commitOutcome .readOnly old new response).commit = none := by
  cases hdelta : datasetDelta old new with
  | error why => simp [commitOutcome, hdelta, text]
  | ok delta =>
    cases delta with
    | nil => simp [commitOutcome, hdelta, text]
    | cons first rest => simp [commitOutcome, hdelta, scopeRefusal, text]

#print axioms commitOutcome_defaultGraph_replay_named
#print axioms commitOutcome_readOnly_no_commit

end L4Factoidal.SPARQL.StoreEndpoint
