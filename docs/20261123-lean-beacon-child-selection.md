# Checked one-step LMD-GHOST child selection — 23 November 2026

Tracking issue [#822](https://github.com/danbri/factoidal-core/issues/822) and strict Ethereum EL+CL acceptance [#725](https://github.com/danbri/factoidal-core/issues/725). Draft [PR #823](https://github.com/danbri/factoidal-core/pull/823) is stacked on draft [#821](https://github.com/danbri/factoidal-core/pull/821); it is not on main.

## Normative pin and executable path

Source: `ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3/specs/phase0/fork-choice.md`, `get_head`, `get_weight`, `get_node_children`, `get_filtered_node_tree`. The normative rule takes the maximum of `(get_weight(child), child.root)` from the **already filtered** direct children of the current fork-choice head. A larger root breaks ties. The rules for checkpoint viability and constructing that filtered node tree remain **unimplemented** here.

`EthereumConsensus.ForkChoice.ChildSelection` introduces `selectBestScored`, `checkedDirectChild`, and `selectCheckedChild` on **the existing checked ancestry/LMD score** from PR #821. No JavaScript or Python fallback executes the production Lean choice. The finite candidate list is required to be unique, all children must point directly to the known parent with strictly increasing slot, and every needed child score must be determined. Three results remain distinct:
- `none`: invalid input or unresolved required score — refusal;
- `some none`: admitted, explicitly empty candidate inventory;
- `some (some root)`: selected child.

In the standalone maximum helper, `some (some (root,score))` also reports the selected weight. Ties use larger `Nat` root **only as a provisional stand-in** for the canonical lexicographic comparison of 32-byte Roots. A future checked Root codec must prove that its numeric ordering preserves that comparison.

## Stated and discharged local proof obligations

The nine source-connected theorem names, in `ChildSelection.lean`, are `bestScored_empty`, `bestScored_single`, `bestScored_unknown_refused`, `bestScored_tie_break`, `checkedChild_unknown_parent_refused`, `checkedChild_duplicate_refused`, `checkedChild_invalid_edge_refused`, `checkedChild_agrees_when_admitted`, and `checkedChild_rejected_update`. The adapter-refinement theorem links to the **actual executable** `weightWithCheckedAncestry`; it is not a normative fork-choice refinement theorem. These theorems do not prove completeness of supplied viable children, validity of scores, cryptographic roots or full `get_head`.

The implementation-source head is `22fc2596a07074d5be1f6f6ad3902a5cc8bdbb1b` (the last source/config/CI commit before this documentation). The [exact-head Linux specialised consensus CI](https://github.com/danbri/factoidal-core/actions/runs/45121962632) **passed** on 23 November 2026 (job `ssz`, all steps). Lean **4.33.1** compiled library and CLI, checked all **18 source `#guard` cases** and the nine theorem declarations, re-ran the exact source file and printed their axioms. The actual nine printed axiom sets each contain only `propext`. No new `sorryAx`, `native_decide`, `unsafe`, user axioms, `@[implemented_by]` or proof bypass were introduced in these sources. The rest of Lean's trusted compiler/runtime, kernel and toolchain remain trusted components.

The independent `scripts/check-child-selection.py` reconstructs every synthetic block, vote, validator roster, tie, score and proposer boost in Python, then compares the **actual 1,024 Lean emitted rows** from `lake exe lmd-checked-child`. Exact matching results: **527 refusals, 83 admitted empty inventories, 414 selected heads, 5 selected-score ties, 92 boost-induced winner changes, 63 admitted-vote winner changes, 0 mismatches**. The checker checks the observable rejected-admission no-change field in every row. All inherited specialised gates passed: SSZ index 1,025, checked SSZ branch 1,025, latest-message 2,048, and 1,024 each for VoteStore, attestation score, proposer score and checked ancestry. This is finite synthetic agreement, not Ethereum fork-choice conformance.

Reproduction from `formal/lean4/ethereum-consensus/` with the repository's pinned toolchain and a bounded-memory single-build lock:
```sh
lake build
lake env lean EthereumConsensus/ForkChoice/ChildSelection.lean
lake exe lmd-checked-child | python3 scripts/check-child-selection.py
```
The commands above describe reproduction; the observed green results are from hosted Linux, not from a local build. No paired performance benchmark was available in this runtime. Do not infer a performance improvement or tail parity from this change.

## Review findings and outstanding work

An independent source review compared the implementation directly to the pinned `get_head` choice rule and the Python reference. The strict child-edge predicate and the refusal-vs-empty distinction were checked as additional boundary conditions, but no independent human expert review has occurred. A trusted caller could omit a legitimate viable child (even pass an empty list); this helper would then select the wrong head while returning a completed result. Therefore complete viable-child enumeration and canonical justified/finalized checkpoint filtering must be proved and linked before using this in a real client. Other work still required includes root serialization and SHA-256/SSZ verification, BLS, attestation admission, verified ancestry, beacon state transitions, FFG/finality, complete iterative `get_head` with a bounded store, networking and integrated EL+CL operation.

The source does not touch the EVM, execution fixtures or timing hot paths. The open execution performance issue [#739](https://github.com/danbri/factoidal-core/issues/739) remains separate. Broad repository Lean/npm, Linux/premerge, full EELS, Hive, historical mainnet and external-review gates are not implied by this specialised green run. Full acceptance [#725](https://github.com/danbri/factoidal-core/issues/725) and execution-client goal [#652](https://github.com/danbri/factoidal-core/issues/652) remain open.
