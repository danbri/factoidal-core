# Bounded checked fork-choice ancestry — 23 November 2026

Track [issue #820](https://github.com/danbri/factoidal-core/issues/820) under [full Ethereum acceptance #725](https://github.com/danbri/factoidal-core/issues/725).
Stacked on draft [PR #819](https://github.com/danbri/factoidal-core/pull/819), not merged to main.

## Normative source and semantics

Pinned reference: `ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3`, `specs/phase0/fork-choice.md`: `get_ancestor`, `is_ancestor`, `get_weight`. The reference starts at the supported node and follows parent roots while the block slot exceeds the candidate ancestor's slot; the returned node must equal the candidate.

`EthereumConsensus.ForkChoice.CheckedAncestry` adds a finite-fuel traversal from a supplied `Nat → Option BlockPosition`. It refuses an unknown supported/candidate root, a required missing parent, insufficient fuel and a non-decreasing slot edge. `checkedDescends` has three observable outcomes: `some true` (confirmed by supplied lookup), `some false` (resolved but different branch), `none` (inconclusive). The lookup is **not** authenticated: `confirmed` here only means consistent with the supplied synthetic block map.

`weightWithCheckedAncestry` first checks uniqueness of the caller-supplied active/unslashed validator roster. It first requires that the candidate node itself exists in the supplied block map (including the empty-roster/no-boost case), then requires all ancestry queries that can affect vote credit and the optional proposer boost to resolve. If not, it refuses the full score. When known, it calls the **existing executable Lean** `weightWithComputedBoost` with the now-resolved predicate. No host language substitutes for that computation. The `totalActiveBalance` still comes from the caller and must represent all active validators of the justified checkpoint state, not the unslashed vote roster.

## Intended theorems and source evidence

Eleven attached `#print axioms` declarations:
1. `checkedDescends_zero_fuel`
2. `checkedDescends_unknown_candidate`
3. `ancestorAtSlot_at_or_below`
4. `checkedDescends_self`
5. `ancestorAtSlot_missing_parent`
6. `ancestorAtSlot_non_decreasing_parent`
7. `checkedWeight_duplicate_refused`
8. `checkedWeight_unknown_node_refused`
9. `checkedWeight_unknown_boost_refused`
10. `checkedWeight_agrees_when_known` — direct call bridge to the existing executable weight computation
11. `checkedWeight_rejected_update`

There are 17 source `#guard` cases. They cover branch distinctions, insufficient fuel, absent block roots, malformed parent edges, positive boost, absent boost, malformed eligible-validator roster and unknown score refusals. All theorem/proof claims remain **unverified until the exact-head Lean 4.33.1 CI runs**. Source text is not compiler evidence. The independent Python oracle cannot validate Lean theorems.

## Synthetic differential gate

From `formal/lean4/ethereum-consensus`:

```sh
lake build
lake env lean EthereumConsensus/ForkChoice/CheckedAncestry.lean
lake exe lmd-checked-ancestry | python3 scripts/check-ancestry.py
```

The new source-emitting Lean executable produces exactly 1,024 tab-separated rows. The standalone Python reference constructs parent maps, strictly decreasing-slot checks, candidate comparisons, vote updates, duplicate rosters and two-stage proposer boosts independently. It includes absent roots, missing parents, non-decreasing edges, depth exhaustion, known non-ancestry, true ancestry and conditional score changes. It requires both refusals and successful score results. The rows/counts are **expected test design, not observed Lean results** until hosted CI passes. Python is an oracle only, not an Ethereum executor.

## Remaining trust/acceptance limits

The block map is externally provided and not linked to authenticated signed beacon blocks, verified block roots, SSZ, BLS signatures, justified/finalized checkpoint state, filtered viable branches, proposer timeliness, or general `get_head`. `Nat` values do not implement checked 32-byte `Root`, `Slot` or Gwei. The lookup is a functional callback, not persisted or network-synced state. The fuel is caller-selected. A successful synthetic score is **not** full beacon fork choice, finality or Ethereum consensus. Complete EL+CL goal #725 remains open; no deployment or wallet use. Local Lean compilation, source axiom auditing and benchmarks are unavailable in this runtime, so hosted exact-source results are required.

## Exact-source hosted verification (23 November 2026, 05:02 UTC)

The implementation/test source head `705b28e7275a84bbba50e39199066d7b3a629fe7` passed the dedicated [Linux consensus workflow 45115215128](https://github.com/danbri/factoidal-core/actions/runs/45115215128), with **all steps successful** under pinned Lean **4.33.1**. The job compiled the library and the CLI, re-ran all theorem source files and their guards, ran the axiom audit and executed independent source-emitted differential tests. This is actual Lean execution, not just Python prediction.

The **11 actual new `#print axioms` sets**, audited against the source in that job, are: **one empty** (`checkedWeight_rejected_update`), **nine with only `propext`** and **one** (`checkedDescends_self`) with `propext`, `Classical.choice`, `Quot.sound`. No selected claim reports `sorryAx` or a new user axiom. The `lean-action` configuration explicitly allows those three standard axioms; this is **not** a proof of kernel/runtime or crypto correctness.

Independent Python reference matched **all 1,024 of the actual Lean rows**: **556 refusals**, **468 completed synthetic scores**, **288 inconclusive ancestor probes**, **32 positive boosts**, **36 observable latest-vote update effects**, **0 mismatches**. The 17 guards compile in the source. Inherited gates also passed: 1,025 SSZ positional, 1,025 checked-branch, 2,048 LMD latest-message, 1,024 VoteStore, 1,024 attestation weight and 1,024 computed-boost cases.

This report update itself changes documentation only, not the native Lean library, CLI, Python oracle, Lake configuration or workflow verified in the source-head run. A subsequent HEAD-specific CI run, if present, is separate evidence; the implementation claim is anchored to `705b28e7275a84bbba50e39199066d7b3a629fe7`. Broader corpus Lean, npm, execution-layer, premerge, Linux multi-job and performance gates are **not** inferred from this dedicated job. No local Lean build, lower-cost coding-agent dispatch or paired benchmark occurred in this runtime. Review and merge remain deferred.
