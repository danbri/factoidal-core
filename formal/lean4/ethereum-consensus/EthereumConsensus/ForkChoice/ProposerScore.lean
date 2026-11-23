import EthereumConsensus.ForkChoice.AttestationScore

/-!
# Source-connected proposer-score computation for LMD fork choice

Normative pin: ethereum/consensus-specs@
d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md, compute_proposer_score and get_weight.
This profile uses SLOTS_PER_EPOCH = 32 and PROPOSER_SCORE_BOOST = 40.

The input totalActiveBalance MUST come from get_total_active_balance of the
JUSTIFIED checkpoint state: it includes all active validators, including
slashed-but-active ones. It is not the sum of the unslashed vote-credit roster.
The caller still supplies this amount and authenticates state, active status,
proposer timing/root and ancestry. All values here are unbounded Nat, not
checked Gwei, Uint64 or a fixed-width 32-byte Root.
-/

namespace EthereumConsensus.ForkChoice

/-- Exact integer-rounding order in compute_proposer_score:
    floor(totalActiveBalance / SLOTS_PER_EPOCH) first, then the percentage.
    In particular this is NOT floor(totalActiveBalance * 40 / 3200). -/
def computeProposerScore (totalActiveBalance : Nat) : Nat :=
  ((totalActiveBalance / 32) * 40) / 100

/-- Actual LMD score with locally calculated (rather than supplied) proposer
    boost amount. An absent boost root means no proposer boost. An invalid
    eligible-validator roster still gives none, not a valid score of zero. -/
def weightWithComputedBoost (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) : Option Nat :=
  weight store isAncestor node roster
    (boostRoot.map (fun root => (root, computeProposerScore totalActiveBalance)))

/-- Says: the executable two-stage division distinguishes the incorrect
    single-stage quotient on a concrete boundary (80 gives 0, not 1).
    Does not say: an unbounded Nat is a checked consensus Gwei. -/
theorem computeProposerScore_two_rounds :
    computeProposerScore 80 = 0 := by
  decide

/-- Says: without a boost root, derived computation delegates to the
    actual admitted attestation score. Does not authenticate that roster. -/
theorem computedBoost_without_root (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (totalActiveBalance : Nat) :
    weightWithComputedBoost store isAncestor node roster none totalActiveBalance =
      attestationScore store isAncestor node roster := by
  simp [weightWithComputedBoost, weight_without_boost]

/-- Says: the executable scoring path adds exactly the Lean-computed
    proposer amount when the supplied ancestor predicate matches.
    Does not prove source balance, block identity or timely admission. -/
theorem computedBoost_matching (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (boostRoot totalActiveBalance score : Nat)
    (hScore : attestationScore store isAncestor node roster = some score)
    (hAncestor : isAncestor boostRoot node = true) :
    weightWithComputedBoost store isAncestor node roster
      (some boostRoot) totalActiveBalance =
        some (score + computeProposerScore totalActiveBalance) := by
  simpa [weightWithComputedBoost] using
    (weight_with_matching_boost store isAncestor node roster score
      boostRoot (computeProposerScore totalActiveBalance) hScore hAncestor)

/-- Says: a boost outside the subtree contributes nothing, even when
    the locally calculated amount is nonzero. Does not check the ancestry. -/
theorem computedBoost_nonmatching (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (boostRoot totalActiveBalance score : Nat)
    (hScore : attestationScore store isAncestor node roster = some score)
    (hAncestor : isAncestor boostRoot node = false) :
    weightWithComputedBoost store isAncestor node roster
      (some boostRoot) totalActiveBalance = some score := by
  simpa [weightWithComputedBoost] using
    (weight_with_nonmatching_boost store isAncestor node roster score
      boostRoot (computeProposerScore totalActiveBalance) hScore hAncestor)

/-- Says: the new bridge never interprets the existing roster refusal
    as a successful zero-weight computation. Does not validate provenance. -/
theorem computedBoost_refuses_invalid_roster (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat)
    (hScore : attestationScore store isAncestor node roster = none) :
    weightWithComputedBoost store isAncestor node roster
      boostRoot totalActiveBalance = none := by
  simp [weightWithComputedBoost, weight, hScore]

/-- Says: rejected latest-message admission cannot change the computed
    weight path. Does not establish actual attestation admission rules. -/
theorem computedBoost_rejected_update (store : VoteStore)
    (isAncestor : Nat → Nat → Bool) (node validator : Nat)
    (candidate : LatestMessage) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat) :
    weightWithComputedBoost (updateStore store validator candidate false)
      isAncestor node roster boostRoot totalActiveBalance =
    weightWithComputedBoost store isAncestor node roster boostRoot totalActiveBalance := by
  rw [invalid_refused]

private def sampleStore : VoteStore := {
  latest := fun i => if i == 1 then some ⟨5, 12⟩ else none
  equivocating := fun _ => false
}
private def sampleAncestor (supported node : Nat) : Bool :=
  supported % 7 == node % 7

#guard computeProposerScore 0 == 0
#guard computeProposerScore 31 == 0
#guard computeProposerScore 79 == 0
#guard computeProposerScore 80 == 0
#guard computeProposerScore 100 == 1
#guard computeProposerScore 3200 == 40
#guard computeProposerScore 1000000000 == 12500000
#guard weightWithComputedBoost sampleStore sampleAncestor 5
  [(1, 8)] none 3200 == some 0
#guard weightWithComputedBoost sampleStore sampleAncestor 5
  [(1, 8)] (some 12) 3200 == some 40
#guard weightWithComputedBoost sampleStore sampleAncestor 5
  [(1, 8)] (some 11) 3200 == some 0
#guard weightWithComputedBoost sampleStore sampleAncestor 5
  [(1, 8), (1, 9)] (some 12) 3200 == none
#guard weightWithComputedBoost sampleStore sampleAncestor 5
  [(1, 8)] (some 12) 80 == some 0

#print axioms EthereumConsensus.ForkChoice.computeProposerScore_two_rounds
#print axioms EthereumConsensus.ForkChoice.computedBoost_without_root
#print axioms EthereumConsensus.ForkChoice.computedBoost_matching
#print axioms EthereumConsensus.ForkChoice.computedBoost_nonmatching
#print axioms EthereumConsensus.ForkChoice.computedBoost_refuses_invalid_roster
#print axioms EthereumConsensus.ForkChoice.computedBoost_rejected_update

end EthereumConsensus.ForkChoice
