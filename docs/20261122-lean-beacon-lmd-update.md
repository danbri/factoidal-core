# Beacon fork-choice LMD latest-message gate (22 November 2026)

Tracking: [#806](https://github.com/danbri/factoidal-core/issues/806), [#725](https://github.com/danbri/factoidal-core/issues/725). Stacked on [#800](https://github.com/danbri/factoidal-core/pull/800), not integrated with the EVM transaction work [#796](https://github.com/danbri/factoidal-core/issues/796).

## Upstream model

Ethereum consensus-specs `specs/phase0/fork-choice.md`, `update_latest_messages`:
https://github.com/ethereum/consensus-specs/blob/498449f83228304263b05cce1b052f44b7531d8c/specs/phase0/fork-choice.md

The helper replaces the **single validator** latest message precisely if the validator is not marked equivocating, and the previous message is absent or has a strictly smaller *target epoch*. This is LMD vote replacement, **not** `get_head`, proposer boost, FFG, attestation verification, or full fork-choice. The stubbed `Nat` root is a synthetic identifier, not an SSZ `Root` or an authenticated beacon block hash.

## Connected source and theorem statements

File: `formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/LatestMessage.lean`.

The following five named theorem declarations explicitly involve the **executable** `updateLatest`:

1. `equivocating_refused`: flagged validators retain the prior value.
2. `first_message_accepted`: with no old value and no equivocation, admit the new message.
3. `newer_epoch_replaces`: strictly higher target epoch replaces the previous message.
4. `stale_or_equal_refused`: lower or equal target epoch cannot replace a previous message, even with different roots.
5. `updateLatest_never_erases`: a present previous message does not become absent.

The implementation uses explicit `Option LatestMessage` and `Bool` inputs; a future complete transition must connect it to the actual `Store.latest_messages` mapping and validate the incoming vote and equivocation state *before* calling this function. The five `#print axioms` statements are in the module; their **actual output remains unclaimed until exact-head CI**. The five proof statements were first specified in issue #806, before source implementation.

## Executable comparisons

- Eight Lean `#guard` vectors target first-vote admission, equivocation, stale epochs, conflicting equal-epoch votes, strictly newer epochs, and non-erasure.
- `LatestMain.lean` emits 2,048 bounded, deterministic cases from the **actual** Lean helper; `scripts/check-lmd-latest.py` independently derives every field and expected update in Python. Synthetic reference population contains 293 equivocating cases, 438 initial votes, 515 newer replacements, 494 stale refusals, 308 equal-epoch refusals; all 308 equal-epoch cases have different roots. Those are generator counts calculated separately, **not** test passes until the Lean executable is run.
- CI `.github/workflows/ethereum-consensus.yml` builds both modules with Lean 4.33.1, prints axioms and pipes actual output into the independent checker. The inherited SSZ 1,025-row comparison remains enabled.

Local runtime limitation: this authoring environment has neither the repository checkout nor Lean 4.33.1 installed, so no local Lean or timing results can be claimed. The GitHub Actions checks on the exact PR head are required for even the scoped Lean-build claim. This is a new helper and new executable, not a performance comparison against an existing implementation; no p50/p95/p99 or resource-performance inference is made.

## Next proof obligations

- Connect to a concrete bounded/serializable validator `Store`, with lookup, deduplication, equivocation set and no unbounded input-controlled allocation.
- Prove store-level per-index preservation and latest-epoch monotonicity after validated attestations; ensure invalid validation calls leave store unchanged.
- Introduce fixed-length 32-byte roots and authenticated BLS/SSZ/FFG checks, epoch/fork-aware state transitions, fork-choice tree filtering and head selection.
- Differentially execute consensus-spec state-vector fixtures and mature independent beacon clients. Until then this is a **narrow proof-connected building block**, not consensus conformance.

No changes to execution-layer sources, no main merge and no wallet or network transaction operations.
