# Indexed-attestation native transport repair — 24 November 2026

Tracks #879 under #725, stacked on #878 at f6c7f9c7470728f284c134723c8d665dc834a7ff. Hosted run [45345524991](https://github.com/danbri/factoidal-core/actions/runs/45345524991/job/138279002558) passed source dependencies, focused build, root compilation, printed inherited axiom checks, byte proof executable/oracle, basic scalar and vector gates. It failed compiling ContainerRootsMain.lean at lines 73 and 92 because the binder `prefix` is reserved; later unknown identifiers are cascading failures. Native container/slashing differential tests and the later retained suites did not run in this failed job.

Actual Lean build output from that job, for unchanged AttesterSlashing.lean blob 33a09146651425b78a5f9d860d58704fe0520d8b:

| Statement (EthereumConsensus.SSZ) | Actual axioms |
| --- | --- |
| sameAttestationFields_iff | propext, Classical.choice, Quot.sound |
| isSlashableData_iff | propext, Classical.choice, Quot.sound |
| isSlashableData_self | propext, Classical.choice, Quot.sound |
| mem_commonSlashingIndices | propext |
| checkSlashingIndices_over_limit | propext |
| prepareAttesterSlashing_bad_left | propext, Quot.sound |
| prepareAttesterSlashing_bad_right | propext, Quot.sound |
| prepareAttesterSlashing_of_ok | propext, Quot.sound |

These eight reports were observed in compiler output, not the later dedicated ledger step (skipped). They establish model/linkage properties, not signature or state-transition conformance.

Repair: rename exactly ten whole-token occurrences of the local binder to keyPrefix in the two JSON reader helpers. Reverse substitution reproduces the original source exactly; the Lean protocol module, statements and guards are unchanged. Transport blob fbe57e5f33933314564ca0d9d456825b3f29fdc0 becomes cc3635b29abf0905fa1e4eab318602ac18c196e9. Update only that pin in each of the two active fixed-pin ledgers. At 95f479ac08dff7acd136b6f60f26df83c31b4d6c, all 20 distinct active slashing pins were compared with fetched Git blob metadata and matched; all 15 attestation pins are an exact subset. This is a source metadata check, not a fresh compiled audit.

Independent local Python hashlib calculation of the published known-answer vector returned 4af74e8a7bbe68a8300a6f017951b74f9a7e35fd3ec8be32911b455697722b9b, matching the test expectation. This is a test-only reference check, not a native Lean result. The local environment has no Lean, Lake, Codex worker or accessible Git checkout (network resolution failed). No local timing or native test pass is claimed. The existing hosted gates are required on this new branch, with no step skipped or removed. No new package or toolchain, no main merge.

Remaining: native evidence on the repaired head, authenticated validator registry, independent BLS, fork-specific index limits, full state transition, consensus and interoperability. Resource refusal remains distinct from protocol invalidity. Compiler/runtime and input transport trust are unchanged.
