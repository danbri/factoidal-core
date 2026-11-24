# Validator registry typed transport — 24 November 2026

Pre-code issue: https://github.com/danbri/factoidal-core/issues/889. Parent draft #888 head de6dc3ad10182af3baa328b1e89a7205cc0f6758. New isolated branch; no main changes.

## Actual prior compilation evidence

https://github.com/danbri/factoidal-core/actions/runs/45379996894/job/138396238969
(checked merge commit 022dea8f702fa469db34aba7333aea7a8791d961, tree d2eb92d93c5f4bbdf9dcad40790647baa22049ef).
At 11:00:11 UTC the oracle prepared 1,528 rows and detected four comparator controls. At 11:00:29 the compiler built EthereumConsensus.SSZ.ValidatorRegistry, including the eight printed theorem reports below. At 11:00:30 it failed in RegistryProofMain.lean:60: an anonymous constructor was elaborated as ByteArray.IsValidUTF8.intro rather than RegistryValidator. No executable registry comparison, compiled/native linkage audit or complete job pass occurred. See the raw logs and https://github.com/danbri/factoidal-core/actions/runs/45379996894/artifacts/14913640752.

Actual reports (qualified by EthereumConsensus.SSZ.) from that source-pinned build:
- verifyValidatorAt_over_length: [propext, Quot.sound]
- verifyValidatorAt_outside: [propext, Quot.sound]
- verifyValidatorAt_bad_branch: [propext, Quot.sound]
- verifyValidatorAt_delegates: [propext, Quot.sound]
- isSlashableValidator_iff: [propext]
- checkCommonValidator_not_common: [propext, Quot.sound]
- checkCommonValidator_mismatch: [propext, Quot.sound]
- checkCommonValidator_candidate: [propext, Quot.sound]

The module blob 4382daf829b898c3865810faccdc7ec1b9546a2b appears in the CI source pin record and remains unchanged in implementation commit 546cebb3a26bc5cab045af1d7f6b224202dd39b7. The eight theorems constrain membership admission, delegation, eligibility and candidate verdicts, not authentic BeaconState or signature verification. Full recheck of the new tree is required.

## Changes and local checks

RegistryProofMain.lean (blob d3a0ebc4b26ca59b51f0d626cae33af518d1de09) binds every decoded field separately and uses named fields in both registry and synthetic slashing records. No protocol implementation or theorem edits. No new dependency. Lean pin blob a8afa7d1b02d96f0671eba854a8dc4b416beb473 is v4.33.1; empty package manifest blob 15728fe01a01ed2369565ec5be9afdf6abcf2f91.

Oracle script blob 0063a02da26f0cb97aba15e933a1746a90af5b9c retains the 1,528 prior rows and adds 128 field-mutation rows (64 leaf roots and 64 proof mismatches), plus 13 malformed or unknown operation rows. Expected total 1,669; actual new oracle inventory and native comparison pending. An independent local Python hashlib check using sparse heap-indexed Merkle reconstruction passed eight materialised registry roots, 64 altered leaf roots and 64 altered reconstructed registry roots. This checks the expectations, not Lean execution.

Compared the two implementation commits against the exact parent: only the transport and oracle changed. No Lean toolchain available locally; hosted build must check the new executable under the unchanged 8 GiB cap and explicit stack limit. Repeat actual axiom audit, compiled import/native linkage audit, full registry oracle and retained consensus regressions; no timing or full conformance claim before measured. The line reader still allocates before the line-length guard. The compiler/runtime remain trusted. All state anchoring, BLS signature checks and actual slashing state transitions remain open under #725.
