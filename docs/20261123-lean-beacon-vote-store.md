# Lean beacon vote-store update adapter — 23 November 2026

Tracking: https://github.com/danbri/factoidal-core/issues/811
Parent: https://github.com/danbri/factoidal-core/issues/725
Per-validator foundation: https://github.com/danbri/factoidal-core/pull/808
SSZ positional foundation: https://github.com/danbri/factoidal-core/pull/800

## Normative target and exact scope

Ethereum consensus-specs `specs/phase0/fork-choice.md`,
`update_latest_messages`, source pin
`ethereum/consensus-specs@498449f83228304263b05cce1b052f44b7531d8c`.
This change is an **adapter to the existing executable per-validator LMD
`updateLatest`**, not a proof of the upstream whole `Store.on_attestation`
or `on_block` processing.

`VoteStore.latest : Nat → Option LatestMessage` is an extensional functional
map. `equivocating : Nat → Bool` is read-only for this operation.
`updateStore store validator candidate admitted` requires admission from an
upstream trusted validator. False leaves the store entirely unchanged.
True changes only the specified validator via the already implemented
`updateLatest` function. It cannot set equivocation flags.

The following intended declarations were posted **before source changes**
in issue #811. The implementation is in
`formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/VoteStore.lean`:

- `invalid_refused`: whole-store identity on rejection.
- `other_validator_unchanged`: non-target lookup preservation.
- `equivocation_flags_preserved`: read-only flag function.
- `target_uses_updateLatest`: actual executable composition.
- `equivocating_target_refused`: flagged target remains unchanged.
- `newer_target_replaces`: strictly newer admitted target is stored.
- `stale_target_refused`: stale/equal target is not stored.
- `existing_target_never_erased`: previously present entry remains present.

Each theorem is attached to executable source and has a `#print axioms`
directive. Actual axiom output and compilation must be observed on the
**exact published head**; a source declaration is not itself proof evidence.

## Falsification gate

Eight `#guard` vectors cover admission, cross-key isolation, conflicting
equal epoch, stale epoch, first entry, equivocation and other-key effects.
The standalone `lmd-store` executable emits 1,024 **sequential** store
updates, not independent fresh-store test cases. The Python implementation
in `scripts/check-lmd-store.py` uses a separate dictionary representation,
reconstructs every synthetic input, verifies prior and resulting target
values and a distinct neighbour after every update, and checks all six
result categories were exercised. It consumes actual Lean stdout.

The deterministic generator has 94 invalid admissions, 117 flagged
equivocator refusals, six first admissions, 640 newer admissions, 165 stale
refusals and two equal-epoch refusals by independent Python simulation.
These figures are generator predictions, **not passing Lean comparisons**
until CI actually runs.

Reproduce from `formal/lean4/ethereum-consensus/` only:

```sh
lake build
lake env lean EthereumConsensus/ForkChoice/VoteStore.lean
set -o pipefail
lake exe lmd-store | python3 scripts/check-lmd-store.py
```

Hosted gate: `.github/workflows/ethereum-consensus.yml`, exact-head build
with pinned Lean `leanprover/lean4:v4.33.1`, axiom audit and independent
check alongside existing 2,048-row LMD and 1,025-row SSZ positional checks.
This session's container lacks Lake and access to the source checkout.
Consequently local Lean and binary timings are **not** claimed.

## Trust boundary and remaining obligations

The `admitted : Bool` and `equivocating : Nat → Bool` inputs are
untrusted **unless supplied by a future authenticated and validated
consensus transition**. No BLS signature checking, FFG, fork choice
`get_head`, proposer boost, 32-byte root type, SSZ serialisation,
deduplicated finite validator registry, fork-dependent attestation data,
networking, or EL integration has been implemented here.

Functional-map closure chains are not an efficient persistent finite map.
The test bounds updates to 1,024, but the production function has no
allocation/fuel bound or networking-safe input admission. Do not use it as
an exposed untrusted-input node API. This commit changes no existing EVM
execution path. Performance parity is not established by a small test.

No merge, funds, transactions or messages to third parties.
