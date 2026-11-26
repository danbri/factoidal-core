# Stored finite inventory and bounded LMD-GHOST head (23 November 2026)

Tracking [issue #824](https://github.com/danbri/factoidal-core/issues/824), full Ethereum goal [#725](https://github.com/danbri/factoidal-core/issues/725), and the stacked child selector [PR #823](https://github.com/danbri/factoidal-core/pull/823). This is a **draft, unmerged consensus-only** change.

## Specification and executable path

Pinned normative starting point: `ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3/specs/phase0/fork-choice.md`, `get_head`, `get_node_children`, `get_weight`, `get_filtered_node_tree`.

The previous executable `selectCheckedChild` accepted a separate, caller-supplied finite child list. If that list omitted a viable child, it could return a completed but incorrect winner. `StoredHead.lean` now enumerates candidate children **from the same finite block inventory used for node lookup**. The finite scan refuses a direct-child slot reversal and an unresolved viability classification, rejects duplicate stored roots and missing parents, then calls exactly the existing `selectCheckedChild` and `weightWithCheckedAncestry`. The `getHeadStored` recursion follows selected children with an explicit remaining-decision budget; it only succeeds after a known leaf and refuses if fuel runs out.

**The important boundary remains:** the complete inventory of all canonical blocks is externally supplied; an omitted block from the inventory can still cause a wrong final head. The `viable : Nat → Option Bool` input is also externally supplied; the real justified/finalized checkpoint and viability filter have not been implemented. This change connects the child inventory and traversal to existing Lean scoring, not to cryptographically authenticated BeaconBlocks.

## Proof obligations and scope

The new source-connected theorem declarations are `scanStored_empty`, `scanStored_non_child`, `scanStored_bad_slot`, `scanStored_unknown_viability`, `scanStored_includes_viable_head`, `scanStored_excludes_unviable_head`, `stored_duplicate_refused`, `stored_unknown_parent_refused`, `stored_unknown_scan_refused`, `stored_selection_bridge`, `stored_head_zero_budget`, `stored_head_leaf`, `stored_head_unknown`, `stored_head_child`, and `stored_head_rejected_update`. They establish compositional properties of the **actual executable helpers**, not full Ethereum fork-choice refinement. `scanStored_includes_viable_head` establishes that each admitted direct-child entry is retained by the scan constructor. A full theorem quantifying over all members of an arbitrary stored inventory and an authenticated database-completeness claim remain outstanding.

There are 22 source `#guard` cases covering direct inventory lookup, viable children, exclusion, unresolved viability, invalid slot, duplicate roots, missing roots, one-step ties, leaf completion and exhausted budgets. The `StoredHeadMain.lean` executable emits 1,024 synthetic inputs; `scripts/check-stored-head.py` independently reconstructs stored block records, viable-child scanning, tie selection, recursive head movement and rejection-on-exhaustion, then compares the actual Lean output. The synthetic run deliberately has an **empty vote roster and no proposer boost**; inherited standalone differential suites continue to test non-empty LMD scoring and proposer boosts. These 1,024 rows do not establish real checkpoint or BLS behaviour.

## Verification and reproduction

CI is configured in `.github/workflows/ethereum-consensus.yml` to build Lean 4.33.1, rerun `StoredHead.lean` with all 15 `#print axioms` statements, and pipe `lake exe lmd-stored-head` through the independent Python checker. **Hosted source-head validation passed:** [specialised Linux consensus CI run 45128969487](https://github.com/danbri/factoidal-core/actions/runs/45128969487) on source+documentation head `201f7cc9721cf52dd3713acc635b10f85f2dcee1`, 23 November 2026. Lean 4.33.1 built the library and executable (12 library jobs, 18 executable jobs) and rechecked all 15 actual theorem declarations with printed axiom sets: 1 empty set (`scanStored_empty`), 14 sets containing only `propext`. All 22 source guards passed. The independent Python checker matched **1,024/1,024 Lean rows**, 0 mismatches: 369 refused one-step selections, 499 selected root 2, 156 selected root 1; 760 traversal refusals and 264 completed heads (250 root 4, 14 root 3). All inherited specialised SSZ, LMD, VoteStore, proposer score, ancestry and child-selection comparisons passed. **No local Lean build, benchmark or broad premerge/full corpus claim** is made.

Reproduce from `formal/lean4/ethereum-consensus` after taking the repository build lock with bounded memory:

```sh
lake build
lake env lean EthereumConsensus/ForkChoice/StoredHead.lean
lake exe lmd-stored-head | python3 scripts/check-stored-head.py
```

These results cover finite synthetic cases, not authenticated beacon attestations, live head choice, BLS or FFG. No local compiler was available in this runtime; no paired performance result or independent external expert review is claimed. Subsequent source edits require a new exact-source proof and oracle run.

## Outstanding work

- Authenticate roots and parent pointers with fork-indexed SSZ and SHA-256.
- Replace supplied viability and checkpoint balances with Lean beacon state and finalized/justified filtering.
- Implement signed attestation admission, BLS, FFG, full beacon state transitions, fork choice and networking.
- Eliminate externally omitted block and validator inputs through audited persistent store and synchronization.
- Meet **all** execution requirements in #652, Engine API integration, EELS/Hive, historical replay and independent review required by #725.

An independent consensus client remains an intermediate interoperability route, not a replacement for protocol-critical Lean consensus.
