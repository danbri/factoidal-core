import Lean

/-!
# Latest-message replacement for beacon fork choice

Normative slice: ethereum/consensus-specs, specs/phase0/fork-choice.md,
commit 498449f83228304263b05cce1b052f44b7531d8c,
`update_latest_messages`. This is exactly the *per-validator replacement
decision*, not the full Store or any attestation-validation path.

The caller MUST first check attestation signature, FFG target consistency,
known beacon block, timing/slot, and validator identity, and obtain the
equivocation flag from an authenticated store. `root : Nat` is a temporary
opaque identifier, NOT a 32-byte SSZ Root or its validated representation.
-/

namespace EthereumConsensus.ForkChoice

/-- The vote retained for one validator by the LMD update rule.
    A future codec must replace `root : Nat` with a checked 32-byte Root. -/
structure LatestMessage where
  epoch : Nat
  root : Nat
  deriving Repr, BEq, Inhabited

/-- Actual per-validator update decision from consensus-spec fork choice:
    equivocators are ignored; the first vote is accepted; a later vote is
    accepted only if its target epoch is *strictly* greater. A different
    root at the same epoch does NOT supersede the stored message. -/
def updateLatest (old : Option LatestMessage) (equivocating : Bool)
    (candidate : LatestMessage) : Option LatestMessage :=
  if equivocating then old
  else
    match old with
    | none => some candidate
    | some previous =>
        if previous.epoch < candidate.epoch then some candidate
        else old

/-- Says: the executable update does not change the last vote of an
    equivocating validator. Does not say: equivocation detection is sound. -/
theorem equivocating_refused (old : Option LatestMessage)
    (candidate : LatestMessage) :
    updateLatest old true candidate = old := by
  rfl

/-- Says: an initial vote is admitted when the equivocation flag is false.
    Does not say: an unvalidated attestation may enter the store. -/
theorem first_message_accepted (candidate : LatestMessage) :
    updateLatest none false candidate = some candidate := by
  rfl

/-- Says: for one validator the executable update replaces a message
    when (and only in this arm when) its epoch strictly increases.
    Does not say: the vote or its block root has been authenticated. -/
theorem newer_epoch_replaces (previous candidate : LatestMessage)
    (h : previous.epoch < candidate.epoch) :
    updateLatest (some previous) false candidate = some candidate := by
  simp [updateLatest, h]

/-- Says: stale and equal-epoch candidate votes preserve the original,
    even if the root differs. Does not say: equivocation can be diagnosed
    from two roots alone without full attestation semantics. -/
theorem stale_or_equal_refused (previous candidate : LatestMessage)
    (h : candidate.epoch ≤ previous.epoch) :
    updateLatest (some previous) false candidate = some previous := by
  have hNot : ¬ previous.epoch < candidate.epoch := Nat.not_lt.mpr h
  simp [updateLatest, hNot]

/-- Says: updating a present latest message never changes it into none.
    Does not say: the state can never be reset by a separate transition. -/
theorem updateLatest_never_erases (previous candidate : LatestMessage)
    (equivocating : Bool) :
    (updateLatest (some previous) equivocating candidate).isSome = true := by
  cases equivocating with
  | true => rfl
  | false =>
      by_cases h : previous.epoch < candidate.epoch
      · simp [updateLatest, h]
      · simp [updateLatest, h]

private def first : LatestMessage := ⟨4, 100⟩
private def stale : LatestMessage := ⟨3, 300⟩
private def tied : LatestMessage := ⟨4, 200⟩
private def later : LatestMessage := ⟨5, 500⟩

#guard updateLatest none false first == some first
#guard updateLatest none true first == none
#guard updateLatest (some first) true later == some first
#guard updateLatest (some first) false stale == some first
#guard updateLatest (some first) false tied == some first
#guard updateLatest (some first) false later == some later
#guard (updateLatest (some first) false later).isSome
#guard (updateLatest (some first) true later).isSome

#print axioms EthereumConsensus.ForkChoice.equivocating_refused
#print axioms EthereumConsensus.ForkChoice.first_message_accepted
#print axioms EthereumConsensus.ForkChoice.newer_epoch_replaces
#print axioms EthereumConsensus.ForkChoice.stale_or_equal_refused
#print axioms EthereumConsensus.ForkChoice.updateLatest_never_erases

end EthereumConsensus.ForkChoice
