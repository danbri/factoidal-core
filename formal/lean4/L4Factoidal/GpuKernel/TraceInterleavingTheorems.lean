import L4Factoidal.GpuKernel.Race

/-! # Interleaving individual stores with distinct addresses

A trace is a list of word-address/value pairs. Each element is one store.
Different lanes can supply the input traces, and the schedule can reorder the
individual stores across all lanes. The memory is observed after any prefix.
-/

namespace L4Factoidal.GpuKernel

/-- Kind: store footprint composition.
Says: if each lane writes each of its addresses once and different lane traces
have disjoint addresses, their complete list of stores has unique addresses.
Does not say: that an arbitrary shader has those footprints. -/
theorem keys_flatten_nodup {α : Type} (lanes : List (List (Nat × α)))
    (within : ∀ lane ∈ lanes, (keys lane).Nodup) (across : lanes.Pairwise Disjoint) :
    (keys lanes.flatten).Nodup := by
  induction lanes with
  | nil => exact List.nodup_nil
  | cons lane lanes ih =>
    obtain ⟨apart, rest⟩ := List.pairwise_cons.mp across
    have head := within lane List.mem_cons_self
    have tail := ih (fun other h => within other (List.mem_cons_of_mem _ h)) rest
    have split : keys (lane ++ lanes.flatten) = keys lane ++ keys lanes.flatten := List.map_append
    rw [List.flatten_cons, split]
    refine List.nodup_append.mpr ⟨head, tail, ?_⟩
    intro i hi j hj same
    subst j
    obtain ⟨event, member, address⟩ := List.mem_map.mp hj
    obtain ⟨other, inLanes, inOther⟩ := List.mem_flatten.mp member
    exact apart other inLanes i hi (List.mem_map.mpr ⟨event, inOther, address⟩)

/-- Kind: individual store observation.
Says: the last write at an event's address is that event's value whenever the
address occurs once in the trace.
Does not say: how a chosen ordering resolves conflicting writes. -/
private theorem lastWrite_at_event {α : Type} (stores : List (Nat × α)) (event : Nat × α)
    (unique : (keys stores).Nodup) (member : event ∈ stores) :
    lastWrite stores event.1 = some event.2 := by
  induction stores with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    change (key :: keys tail).Nodup at unique
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | inTail
    · subst event
      rw [lastWrite, lastWrite_none tail key fresh] <;> simp
    · rw [lastWrite, ih tailUnique inTail]

/-- Kind: individual-store prefix refinement.
Says: after any prefix of any permutation of uniquely addressed stores, each
visited event's address contains its value, which is also the value in the
complete reference memory. Every unvisited address retains its initial value.
Does not say: that a device has executed the prefix or will finish its suffix. -/
theorem applyWrites_perm_prefix {α : Type} (initial : Mem α)
    {issued seen pending : List (Nat × α)} (unique : (keys issued).Nodup)
    (order : (seen ++ pending).Perm issued) :
    (∀ event ∈ seen, applyWrites initial seen event.1 = event.2 ∧
      applyWrites initial issued event.1 = event.2) ∧
    (∀ i, i ∉ keys seen → applyWrites initial seen i = initial i) := by
  have reordered : (keys (seen ++ pending)).Nodup := (order.map Prod.fst).nodup_iff.mpr unique
  have seenUnique : (keys seen).Nodup :=
    List.Nodup.sublist ((List.sublist_append_left seen pending).map Prod.fst) reordered
  constructor
  · intro event inSeen
    have inIssued := order.mem_iff.mp (List.mem_append_left pending inSeen)
    constructor
    · rw [applyWrites_apply, lastWrite_at_event seen event seenUnique inSeen] <;> rfl
    · rw [applyWrites_apply, lastWrite_at_event issued event unique inIssued] <;> rfl
  · intro i untouched
    rw [applyWrites_apply, lastWrite_none seen i untouched] <;> rfl

/-- Kind: individual-store permutation refinement.
Says: every permutation of the individual stores to unique addresses gives the
same whole memory on any initial contents. Stores from different lanes may be
interleaved, and the statement also permits reordering within a lane.
Does not say: that arbitrary GPU instruction executions produce this list of stores. -/
theorem applyWrites_perm_of_nodup_keys {α : Type} (initial : Mem α)
    {issued actual : List (Nat × α)} (unique : (keys issued).Nodup) (order : actual.Perm issued) :
    applyWrites initial actual = applyWrites initial issued := by
  obtain ⟨visited, untouched⟩ := applyWrites_perm_prefix initial (seen := actual) (pending := [])
    unique (by simpa only [List.append_nil] using order)
  funext i
  by_cases hit : i ∈ keys actual
  · obtain ⟨event, member, rfl⟩ := List.mem_map.mp hit
    obtain ⟨after, reference⟩ := visited event member
    exact after.trans reference.symm
  · have absent : i ∉ keys issued := fun h => hit ((order.map Prod.fst).mem_iff.mpr h)
    rw [untouched i hit, applyWrites_apply issued initial i, lastWrite_none issued i absent] <;> rfl

#print axioms keys_flatten_nodup
#print axioms applyWrites_perm_prefix
#print axioms applyWrites_perm_of_nodup_keys

end L4Factoidal.GpuKernel
