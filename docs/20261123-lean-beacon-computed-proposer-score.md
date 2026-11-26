# Source-connected proposer score for Lean beacon LMD — 23 November 2026

Track: [issue #818](https://github.com/danbri/factoidal-core/issues/818),
under [full Ethereum goal #725](https://github.com/danbri/factoidal-core/issues/725).
Stacked on draft [PR #816](https://github.com/danbri/factoidal-core/pull/816).
This is a stand-alone consensus-package change, **not** an execution-layer
update or a main-branch merge.

## Normative source and exact semantics

Pinned consensus source:
`ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3`,
`specs/phase0/fork-choice.md`, `compute_proposer_score`,
`get_proposer_score`, `get_weight`.
The selected profile has `SLOTS_PER_EPOCH = 32` and
`PROPOSER_SCORE_BOOST = 40`. The mathematical source expression is

`committee_weight = total_active_balance // 32;`
`proposer_score = (committee_weight * 40) // 100`.

The first integer division is **not interchangeable** with dividing the
product by 3200: for synthetic total active balance 80, the normative
two-stage result is 0 while the one-stage expression yields 1.
`computeProposerScore` and `weightWithComputedBoost` are executable
Lean definitions. The bridge calls the **existing** verified
`weight`/ `attestationScore` path, rather than adding a separate
host-language implementation.

Critically, `get_total_active_balance` is from the *justified checkpoint
state* and includes **all active validators**, including those which are
slashed but still active. It is **not** the sum of the narrower
active-and-unslashed voting roster. The caller must supply this total
from the correct state. The new Lean code no longer trusts a
host-supplied proposer *score*, but it still trusts the host-supplied
total active balance and boost-root admission. These inputs are
not yet authenticated or extracted from a checked SSZ checkpoint.

## Theorems versus remaining trust

The six source-connected proof contracts in
`EthereumConsensus/ForkChoice/ProposerScore.lean` are:

1. `computeProposerScore_two_rounds`: discriminator for integer-rounding order.
2. `computedBoost_without_root`: absent boost delegates to existing score.
3. `computedBoost_matching`: matching supplied ancestry adds the exact
   computed boost, once.
4. `computedBoost_nonmatching`: non-descendant boost contributes zero.
5. `computedBoost_refuses_invalid_roster`: malformed roster stays `none`.
6. `computedBoost_rejected_update`: rejected admission preserves weight.

Each declaration has a source `#print axioms`. The code has twelve
source `#guard` controls, including both a duplicated-roster refusal
and the rounding boundary. Theorems require actual compilation, actual
printed axiom audit and source-pinned CI before reporting success.
No `sorry`, user axioms, `native_decide`, `unsafe`, or proof bypass.

## Differential corpus and reproducibility

The new `lmd-computed-boost` executable emits **1,024** deterministic
input/output rows containing the synthetic input total balance, computed
score, admitted attestation weight, derived weight and weight after
one candidate store update. `scripts/check-proposer-score.py` is
a standalone Python implementation of the source formula, latest
vote replacement, eligible roster, ancestry and boost rule. It
checks every field, refuses missing/malformed/out-of-order rows,
and checks coverage of duplicates, positive boosts, updates and
two-stage rounding boundaries. It has no Lean interpreter fallback.

The test input deliberately includes synthetically small (even zero)
totals to exercise raw arithmetic, despite genuine
`get_total_active_balance` returning an increment-clamped consensus
value. These controls do **not** validate checkpoint admission.

Run with Lean 4.33.1 in the standalone package, under the repository
single-build lock and bounded memory:

```sh
# Working directory: formal/lean4/ethereum-consensus
lake build
lake env lean EthereumConsensus/ForkChoice/ProposerScore.lean
set -o pipefail
lake exe lmd-computed-boost | python3 scripts/check-proposer-score.py
```

The deterministic **Python/JS design-time reference inventory**, not
observed Lean output, is 79 duplicate-roster refusals, 94 positive
computed boosts, 156 observable post-update weight changes and
137 inputs distinguishing two-stage from one-stage rounding.
These are expected quantities until an exact-head hosted result
executes the Lean emitter. The existing SSZ/LMD tests remain
mandatory; neither old green CI nor an unexecuted fixture is
counted as a new pass.

## Open assurance obligations

This does not construct or validate `BeaconState`, `get_total_active_balance`,
the justified checkpoint, validator activity/activation/slashing,
fork-indexed constants, a proposer-boost root and arrival timeliness,
authenticated block ancestry, BLS signatures, 32-byte SSZ roots,
bounded `Gwei`/`Uint64` arithmetic, a block DAG, `get_head`, FFG
finality or consensus networking. There is no global security or
conformance claim. The next required bridge is a typed authenticated
checkpoint-state input and block ancestry, before treating computed
scores as independently verifiable fork choice.

This isolated GitHub-connector authoring environment has no local
Lean 4.33.1/Lake, shared Mac build lock or lower-cost coding worker.
Source checks here are static; exact-head hosted compilation and
independent Python test are required before any executed pass
can be reported. No local benchmark/performance statement is made.
