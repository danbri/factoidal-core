# Independent Ethereum slashing preparation integration — 24 November 2026

Tracks #946 under #725. The two independently built paths are now assembled in a new draft branch, not main. No predecessor branch was edited.

## Checked predecessor evidence

- Proposer path #939 head `f154bb5e208062d51a0981f3e9a8d408b38bcb20`, tree `e000f72334e89624dc821d16f3f1f1fc657a31b2`: the [actual hosted job](https://github.com/danbri/factoidal-core/actions/runs/45456210259/job/138666220851) built Lean 4.33.1, audited sources, compiled imports and native link, and matched 1218/1218 independent cases (46 candidates), with three comparator controls. Twelve actual axiom reports: one (sameProposerRootFields_iff) uses propext, Classical.choice and Quot.sound; eleven use propext and Quot.sound. The CI test merge tree was identical to the published head tree.
- All-signers path #924 head `2872855c21c5935f0a56b5926767f75c3e0f895b`, tree `629d30efecf9e4404596e68354aba95cead3526f`: [actual hosted job](https://github.com/danbri/factoidal-core/actions/runs/45444936725/job/138625971439) matched 9293/9293 actual Lean registry cases, with all 35 required axiom reports and dependency checks. CI test merge tree was identical to the published head tree.
- The [retained SSZ job](https://github.com/danbri/factoidal-core/actions/runs/45456210252/job/138666223029) stopped at a source pin mismatch after emitting the five actual AttestationData axiom reports. Both affected ledgers still expected lakefile blob `dbac6d2d2081ec960fadbe701c2f093be17cd0e3`. The proposer branch adds exactly four lines declaring its native executable; the new lakefile blob is `b08203129886735a8fbfc2c31fb7027024665d1f`. Checked all 20 distinct pinned blob paths via exact source refs: 19 unchanged; lakefile only differs. Neither SHA2, Lean toolchain, external manifest nor any prior attestation/slashing theorem changes.

## Integration and verification

The branches share base `7c7e53f1d343274cf54acc55cf3506af452fc3f3`; their five and six changed paths are disjoint. Preserve the exact five #924 blobs on the #939 tree and both parent histories. Repin only the reviewed lakefile in the two existing checker scripts. Preserve checks of the committed and working-tree blobs, exact theorem inventory, duplicate rejection and permitted axiom policy.

New regression controls run the production checkers on actual freshly generated reports in a temporary Git repository containing the exact pinned source bytes. Each must accept the unmodified fixture and reject missing, duplicate, unexpected and unpermitted-axiom reports, plus separate working-tree and committed-blob mutations. The scratch repository is removed and never modifies the original checkout. These controls test evidence integrity, not protocol semantics.

Fresh combined native compilation, 47 selected proposer/registry reports, both independent suites, all retained SSZ suites and source/link audits are required. Predecessor results are not claimed for the combined tree until its own runs complete. The full corpus separately failed on non-Ethereum CSS Calc.simpWith recursion ([job](https://github.com/danbri/factoidal-core/actions/runs/45456210111/job/138666221185)); no relaxation or unrelated fix is made here.

## Boundary

Both paths prepare commitment-bound candidates and signing roots. They do not authenticate a canonical BeaconState, verify BLS signatures, apply slashing penalties/exit state changes or implement a complete beacon transition. No new runtime implementation dependency or crypto fallback; compiler/runtime trust remains. No new protocol theorem is asserted merely by assembling the two source paths. Full #725 remains open. No release or main merge.
