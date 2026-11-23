import EthereumConsensus.ForkChoice.VoteStore

/-!
# Finite LMD attestation score and optional proposer-boost adapter

Normative source (read 2026-11-23):
ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md, get_attestation_score and get_weight.

The input roster MUST be constructed from the active, unslashed validators of
the justified checkpoint state, with each effective balance in Gwei. A repeated
validator index is rejected instead of counted twice. The ancestor predicate
MUST be computed against authenticated blocks (supported vote node first,
candidate ancestor second). Neither obligation is discharged here.

A supplied proposer score is not a calculation of PROPOSER_SCORE_BOOST.
The abstract Nat roots and balances, unchecked ancestry, external roster and
boost are NOT a complete or security-qualified fork-choice implementation.
-/

namespace EthereumConsensus.ForkChoice

/-- A finite roster entry: validator index and its effective balance in Gwei.
    Membership in this roster means active and unslashed only by caller contract. -/
abbrev EligibleWeight := Nat × Nat

/-- Reject duplicate validator indices, including repeats with different balances. -/
def uniqueRoster (roster : List EligibleWeight) : Bool :=
  decide ((roster.map Prod.fst).Nodup)

/-- A single validator's weight in the candidate subtree. The predicate's
    arguments are supported vote root first, candidate ancestor root second. -/
def voteCredit (store : VoteStore) (isAncestor : Nat → Nat → Bool)
    (node : Nat) (entry : EligibleWeight) : Nat :=
  if store.equivocating entry.1 then 0
  else
    match store.latest entry.1 with
    | none => 0
    | some message =>
        if isAncestor message.root node then entry.2 else 0

/-- The attestation component of get_weight. A malformed roster is refused,
    not assigned an apparently valid zero weight. -/
def attestationScore (store : VoteStore) (isAncestor : Nat → Nat → Bool)
    (node : Nat) (roster : List EligibleWeight) : Option Nat :=
  if uniqueRoster roster then
    some ((roster.map (voteCredit store isAncestor node)).sum)
  else none

/-- Candidate-node score. The optional supplied pair contains the proposer
    boost root and already-calculated boost Gwei; no boost means zero.
    In both cases a malformed roster remains a refusal. -/
def weight (store : VoteStore) (isAncestor : Nat → Nat → Bool)
    (node : Nat) (roster : List EligibleWeight)
    (boost : Option (Nat × Nat)) : Option Nat :=
  match attestationScore store isAncestor node roster with
  | none => none
  | some score =>
      match boost with
      | none => some score
      | some (boostRoot, boostGwei) =>
          some (score + if isAncestor boostRoot node then boostGwei else 0)

/-- Says: an equivocating validator contributes zero to the executable
    accumulator regardless of ancestry or a stored vote.
    Does not say: equivocation detection is implemented. -/
theorem credit_equivocating_zero (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node validator balance : Nat)
    (h : store.equivocating validator = true) :
    voteCredit store isAncestor node (validator, balance) = 0 := by
  simp [voteCredit, h]

/-- Says: a validator without a latest message contributes zero.
    Does not say: a missing vote can be treated as a verified absence. -/
theorem credit_absent_zero (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node validator balance : Nat)
    (h : store.latest validator = none) :
    voteCredit store isAncestor node (validator, balance) = 0 := by
  cases he : store.equivocating validator <;> simp [voteCredit, he, h]

/-- Says: a valid empty roster yields zero weight.
    Does not say: a real checkpoint may omit eligible validators. -/
theorem attestationScore_empty (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat) :
    attestationScore store isAncestor node [] = some 0 := by
  rfl

/-- Says: a duplicate validator index cannot contribute twice, even if the
    two entries claim different balances. Does not validate registry provenance. -/
theorem attestationScore_duplicate_refused (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node validator first second : Nat)
    (rest : List EligibleWeight) :
    attestationScore store isAncestor node
      ((validator, first) :: (validator, second) :: rest) = none := by
  simp [attestationScore, uniqueRoster, List.nodup_cons]

/-- Says: one uniquely listed active, unslashed validator with a stored
    eligible descendant vote contributes exactly its supplied balance.
    Does not validate signature, status, effective balance or ancestry. -/
theorem attestationScore_single_vote (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node validator balance : Nat)
    (message : LatestMessage)
    (hEq : store.equivocating validator = false)
    (hLatest : store.latest validator = some message)
    (hAncestor : isAncestor message.root node = true) :
    attestationScore store isAncestor node [(validator, balance)] =
      some balance := by
  simp [attestationScore, uniqueRoster, voteCredit, hEq, hLatest, hAncestor]

/-- Says: a rejected store admission cannot affect the actual score.
    Does not establish sound admission of any real attestation. -/
theorem attestationScore_rejected_update (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node validator : Nat)
    (candidate : LatestMessage) (roster : List EligibleWeight) :
    attestationScore (updateStore store validator candidate false)
      isAncestor node roster = attestationScore store isAncestor node roster := by
  rfl

/-- Says: absent proposer boost leaves the actual attestation score.
    Does not calculate the proposer boost amount. -/
theorem weight_without_boost (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) :
    weight store isAncestor node roster none =
      attestationScore store isAncestor node roster := by
  cases h : attestationScore store isAncestor node roster <;> simp [weight, h]

/-- Says: a matching supplied proposer boost is added exactly once.
    Does not prove that the input boost root or Gwei is authentic. -/
theorem weight_with_matching_boost (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (score boostRoot boostGwei : Nat)
    (hScore : attestationScore store isAncestor node roster = some score)
    (hAncestor : isAncestor boostRoot node = true) :
    weight store isAncestor node roster (some (boostRoot, boostGwei)) =
      some (score + boostGwei) := by
  simp [weight, hScore, hAncestor]

/-- Says: a boost outside this candidate subtree does not alter the score.
    Does not validate proposer timing or boost calculation. -/
theorem weight_with_nonmatching_boost (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (score boostRoot boostGwei : Nat)
    (hScore : attestationScore store isAncestor node roster = some score)
    (hAncestor : isAncestor boostRoot node = false) :
    weight store isAncestor node roster (some (boostRoot, boostGwei)) =
      some score := by
  simp [weight, hScore, hAncestor]

private def testStore : VoteStore := {
  latest := fun i =>
    if i = 0 then some ⟨4, 7⟩
    else if i = 1 then some ⟨5, 8⟩
    else if i = 2 then some ⟨6, 9⟩
    else none
  equivocating := fun i => i == 1
}

private def sampleAncestor (voteRoot node : Nat) : Bool :=
  voteRoot % 3 == node % 3

#guard uniqueRoster ([] : List EligibleWeight)
#guard uniqueRoster [(0, 10), (1, 20)]
#guard !(uniqueRoster [(0, 10), (0, 200)])
#guard voteCredit testStore sampleAncestor 6 (1, 20) == 0
#guard voteCredit testStore sampleAncestor 6 (3, 40) == 0
#guard voteCredit testStore sampleAncestor 6 (2, 30) == 30
#guard voteCredit testStore sampleAncestor 6 (0, 10) == 0
#guard attestationScore testStore sampleAncestor 6 [] == some 0
#guard attestationScore testStore sampleAncestor 6
  [(0, 10), (1, 20), (2, 30), (3, 40)] == some 30
#guard attestationScore testStore sampleAncestor 6
  [(2, 30), (2, 99)] == none
#guard weight testStore sampleAncestor 6 [(2, 30)] none == some 30
#guard weight testStore sampleAncestor 6 [(2, 30)] (some (12, 5)) == some 35
#guard weight testStore sampleAncestor 6 [(2, 30)] (some (11, 5)) == some 30
#guard weight testStore sampleAncestor 6 [(2, 30), (2, 99)]
  (some (12, 5)) == none
#guard attestationScore (updateStore testStore 2 ⟨99, 12⟩ false)
  sampleAncestor 6 [(2, 30)] == some 30

#print axioms EthereumConsensus.ForkChoice.credit_equivocating_zero
#print axioms EthereumConsensus.ForkChoice.credit_absent_zero
#print axioms EthereumConsensus.ForkChoice.attestationScore_empty
#print axioms EthereumConsensus.ForkChoice.attestationScore_duplicate_refused
#print axioms EthereumConsensus.ForkChoice.attestationScore_single_vote
#print axioms EthereumConsensus.ForkChoice.attestationScore_rejected_update
#print axioms EthereumConsensus.ForkChoice.weight_without_boost
#print axioms EthereumConsensus.ForkChoice.weight_with_matching_boost
#print axioms EthereumConsensus.ForkChoice.weight_with_nonmatching_boost

end EthereumConsensus.ForkChoice
