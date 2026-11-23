# Lean LMD attestation scoring — 23 November 2026

Tracked by [issue #815](https://github.com/danbri/factoidal-core/issues/815)
under [strict Ethereum goal #725](https://github.com/danbri/factoidal-core/issues/725).
Draft stack: [#800](https://github.com/danbri/factoidal-core/pull/800) →
[#808](https://github.com/danbri/factoidal-core/pull/808) →
[#812](https://github.com/danbri/factoidal-core/pull/812) →
[#814](https://github.com/danbri/factoidal-core/pull/814) → this change.

## Normative slice and trust boundary

Pinned specification:
[ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3/specs/phase0/fork-choice.md](https://github.com/ethereum/consensus-specs/blob/d2021d2719235f0df4726a1d330502cb15aa8ea3/specs/phase0/fork-choice.md),
`get_attestation_score`, `get_weight`. In the pinned Python algorithm, an
eligible validator contributes `effective_balance` precisely when it has a
latest head vote, is not equivocating and the supported node descends from the
candidate. A proposer boost applies if its boosted node descends from the
candidate. A validator must contribute only once.

`ForkChoice.AttestationScore` implements this finite-roster **adapter** over
the existing executable `VoteStore`. The roster is caller supplied and must
consist of *exactly* the active and unslashed validator indices and effective
balances from the justified-checkpoint state. The adapter refuses duplicate
indices rather than double-counting. The supplied predicate's arguments are
`isAncestor supportedRoot candidateRoot`; it is a toy function in fixtures,
**not** a verified block DAG. The supplied optional boost contains its root
and already computed score. No Lean proof here validates its timing, percent
or balance source.

All indices, roots, balances and total scores are currently `Nat`, not
Ethereum bounded integer or 32-byte `Root` types. No authenticated validator
registry, checkpoint state, fork-specific constants, BLS, SSZ or networking is
implemented here. Errors are explicit `none`, not a valid zero-weight score.
This is not a complete `get_head`, fork-choice, or Casper-FFG implementation.

## Implemented theorem contracts

These declarations are in the same module as the executable scoring path,
stated in issue #815 before implementation:

- `credit_equivocating_zero` and `credit_absent_zero`: no contribution
  from equivocators or absent votes.
- `attestationScore_empty`: an admitted empty roster scores zero.
- `attestationScore_duplicate_refused`: two records with a common validator
  index cause refusal, even if balances differ.
- `attestationScore_single_vote`: a uniquely listed eligible descendant vote
  contributes exactly its effective balance.
- `attestationScore_rejected_update`: rejected `updateStore` admission
  leaves the executable score unchanged.
- `weight_without_boost`, `weight_with_matching_boost`,
  `weight_with_nonmatching_boost`: the optional supplied boost is counted
  once only if the candidate is its ancestor.

The nine proof declarations each carry `#print axioms`. The module has
fifteen `#guard` executable controls. These source declarations are not
theorem-checking evidence until compiled on this exact commit.

## Independent differential corpus

From `formal/lean4/ethereum-consensus` with the repository build lock
and Lean 4.33.1:

```sh
lake build
lake env lean EthereumConsensus/ForkChoice/AttestationScore.lean
set -o pipefail
lake exe lmd-score | python3 scripts/check-attestation-score.py
```

The CLI emits 1,024 ordered cases. Python independently derives weights and
admitted-vote effects from synthetic input rules. It requires exactly 1,024
rows, 79 duplicate-roster refusals, positive proposer-boost and update cases,
and no mismatches. The reference corpus has 95 positive boost cases and 156
cases whose score changes after a candidate update; **these are reference
inventory counts, not passing Lean observations until CI executes**.
The ancestry stand-in groups roots modulo seven. It intentionally does not
claim consensus DAG correctness or live-chain oracle agreement.

Exact-source hosted CI in
[ethereum-consensus.yml](../.github/workflows/ethereum-consensus.yml)
recompiles proof files, audits axioms and runs the existing SSZ/LMD gates plus
this new independent comparison. The isolated runtime used to author this
branch has GitHub connector access but no local repository checkout, Lean/Lake,
or lower-cost Codex/Claude worker. Therefore no local Lean build, checker
success, axioms output, performance timings or broader Linux/npm passes are
claimed from this authoring environment. No execution-layer source changes
were made. Any later hosted verdict must be linked to its exact source head.

## Further acceptance obligations

The next meaningful strengthening is a bounded, source-pinned justified
checkpoint-state validator roster and authenticated ancestry, followed by
the fork-specific proposer score and actual GHOST head selection. The
specification also includes viability filtering, proposer timing/boost
rules, on-attestation validation, equivocation/slashing, BLS, FFG finality,
typed SSZ hashing and networking. In particular, an independent consensus
client is an intermediate interoperability aid, not a replacement for Lean
protocol-critical consensus.

Upstream `ethereum/EthLib@6b87b0d4951766864af432455c44344fd12b5cdc`
has existing concrete SSZ SHA-256 support, but its pinned toolchain is Lean
4.35.0, whereas this package is required to use 4.33.1. That is a
compatibility decision to test, not a reason to silently downgrade or vendor
unreviewed cryptographic sources.
