import EthereumConsensus.ForkChoice.LatestMessage

/-!
# Guarded store-level LMD vote update

A deliberately small functional map from ValidatorIndex (here Nat) to
LatestMessage. This is a direct adapter to the executable updateLatest rule;
it is NOT the consensus-spec Store, validator-registry lookup, attestation
validation, equivocation detection, or a serialisable bounded map.

The admission flag is supplied by a trusted caller. False MUST refuse the
update. True is not evidence of a checked signature or well-formed attestation.
-/

namespace EthereumConsensus.ForkChoice

/-- Abstract keyed latest-message state and read-only equivocation flags.
    The map is extensional and presently unbounded: no SSZ codec is supplied. -/
structure VoteStore where
  latest : Nat → Option LatestMessage
  equivocating : Nat → Bool

/-- Update only the target validator, through the existing helper, after
    trusted admission; all other entries and equivocation flags are untouched. -/
def updateStore (store : VoteStore) (validator : Nat)
    (candidate : LatestMessage) (admitted : Bool) : VoteStore :=
  if admitted then
    { store with
      latest := fun index =>
        if index = validator then
          updateLatest (store.latest index) (store.equivocating index) candidate
        else store.latest index }
  else store

/-- Says: rejected admission preserves the entire executable store.
    Does not say: admission validation is currently implemented. -/
theorem invalid_refused (store : VoteStore) (validator : Nat)
    (candidate : LatestMessage) :
    updateStore store validator candidate false = store := by
  rfl

/-- Says: the real store update leaves a different validator's vote unchanged.
    Does not say: validator indices have been authenticated. -/
theorem other_validator_unchanged (store : VoteStore) (validator index : Nat)
    (candidate : LatestMessage) (admitted : Bool) (h : index ≠ validator) :
    (updateStore store validator candidate admitted).latest index =
      store.latest index := by
  cases admitted <;> simp [updateStore, h]

/-- Says: the update never edits the equivocation flags (at any key).
    Does not say: the flags themselves were correctly constructed. -/
theorem equivocation_flags_preserved (store : VoteStore) (validator index : Nat)
    (candidate : LatestMessage) (admitted : Bool) :
    (updateStore store validator candidate admitted).equivocating index =
      store.equivocating index := by
  cases admitted <;> rfl

/-- Says: an admitted target applies precisely the existing per-validator
    updateLatest definition. Does not say: candidate is a valid attestation. -/
theorem target_uses_updateLatest (store : VoteStore) (validator : Nat)
    (candidate : LatestMessage) :
    (updateStore store validator candidate true).latest validator =
      updateLatest (store.latest validator) (store.equivocating validator) candidate := by
  simp [updateStore]

/-- Says: equivocating target retains its old latest message, even when
    admission is true. Does not say: equivocations are detected locally. -/
theorem equivocating_target_refused (store : VoteStore) (validator : Nat)
    (candidate : LatestMessage) (admitted : Bool)
    (h : store.equivocating validator = true) :
    (updateStore store validator candidate admitted).latest validator =
      store.latest validator := by
  cases admitted with
  | false => rfl
  | true =>
      rw [target_uses_updateLatest, h]
      exact equivocating_refused (store.latest validator) candidate

/-- Says: admitted non-equivocating target replaces a prior message when
    the candidate target epoch is strictly higher. Does not check BLS/FFG. -/
theorem newer_target_replaces (store : VoteStore) (validator : Nat)
    (previous candidate : LatestMessage)
    (hOld : store.latest validator = some previous)
    (hEquiv : store.equivocating validator = false)
    (hEpoch : previous.epoch < candidate.epoch) :
    (updateStore store validator candidate true).latest validator =
      some candidate := by
  rw [target_uses_updateLatest, hOld, hEquiv]
  exact newer_epoch_replaces previous candidate hEpoch

/-- Says: admitted non-equivocating target cannot replace a prior message
    at an equal or lower epoch, regardless of root. Does not prove finality. -/
theorem stale_target_refused (store : VoteStore) (validator : Nat)
    (previous candidate : LatestMessage)
    (hOld : store.latest validator = some previous)
    (hEquiv : store.equivocating validator = false)
    (hEpoch : candidate.epoch ≤ previous.epoch) :
    (updateStore store validator candidate true).latest validator =
      some previous := by
  rw [target_uses_updateLatest, hOld, hEquiv]
  exact stale_or_equal_refused previous candidate hEpoch

/-- Says: a present target latest message is never erased by this update.
    Does not cover pruning, state reconstruction or another transition. -/
theorem existing_target_never_erased (store : VoteStore) (validator : Nat)
    (previous candidate : LatestMessage) (admitted : Bool)
    (hOld : store.latest validator = some previous) :
    ((updateStore store validator candidate admitted).latest validator).isSome =
      true := by
  cases admitted with
  | false => simp [updateStore, hOld]
  | true =>
      rw [target_uses_updateLatest, hOld]
      exact updateLatest_never_erases previous candidate (store.equivocating validator)

private def sampleStore : VoteStore := {
  latest := fun index =>
    if index = 0 then some ⟨4, 100⟩
    else if index = 2 then some ⟨6, 500⟩
    else none
  equivocating := fun index => decide (index = 2)
}

#guard (updateStore sampleStore 0 ⟨5, 200⟩ true).latest 0 == some ⟨5, 200⟩
#guard (updateStore sampleStore 0 ⟨3, 200⟩ true).latest 0 == some ⟨4, 100⟩
#guard (updateStore sampleStore 0 ⟨4, 200⟩ true).latest 0 == some ⟨4, 100⟩
#guard (updateStore sampleStore 2 ⟨9, 900⟩ true).latest 2 == some ⟨6, 500⟩
#guard (updateStore sampleStore 0 ⟨9, 900⟩ false).latest 0 == some ⟨4, 100⟩
#guard (updateStore sampleStore 0 ⟨9, 900⟩ true).latest 2 == some ⟨6, 500⟩
#guard (updateStore sampleStore 3 ⟨1, 300⟩ true).latest 3 == some ⟨1, 300⟩
#guard (updateStore sampleStore 3 ⟨1, 300⟩ true).equivocating 2

#print axioms EthereumConsensus.ForkChoice.invalid_refused
#print axioms EthereumConsensus.ForkChoice.other_validator_unchanged
#print axioms EthereumConsensus.ForkChoice.equivocation_flags_preserved
#print axioms EthereumConsensus.ForkChoice.target_uses_updateLatest
#print axioms EthereumConsensus.ForkChoice.equivocating_target_refused
#print axioms EthereumConsensus.ForkChoice.newer_target_replaces
#print axioms EthereumConsensus.ForkChoice.stale_target_refused
#print axioms EthereumConsensus.ForkChoice.existing_target_never_erased

end EthereumConsensus.ForkChoice
