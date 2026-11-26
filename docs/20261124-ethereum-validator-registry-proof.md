# Independent Ethereum validator registry membership — 2026-11-24

Parent #725; pre-code model #881. Base #880 at 4f33710de1dfdca31609514168de3de8181ea051. Hosted run 45352091548 job 138300786398 completed every step, including native indexed-attester slashing and retained consensus regressions. Its reported test commit ca164cc0705699c165b427257db7b2aeedda6493, tree 951d4526ce545afab757ab626c86b3ce81561175, actual eight theorem reports: sameAttestationFields_iff, isSlashableData_iff, isSlashableData_self use propext, Classical.choice, Quot.sound; mem_commonSlashingIndices and checkSlashingIndices_over_limit use propext; prepareAttesterSlashing_bad_left, bad_right and of_ok use propext, Quot.sound. These are prior results, not results for the new source.

New executable path computes the eight-field Validator root, then verifies a 40-sibling list element witness with a locally computed length mix-in. The candidate adapter consumes PreparedAttesterSlashing.commonIndices, verifies the leaf/index/count against a supplied registry root, then checks the activation/withdrawable interval and slashed flag. It never authorises a mutation. No external implementation or toolchain change. Existing independent SHA2 and byte-proof path reused. The runner's synthetic prepared records are test input only.

Source candidate before this worknote: 2e1f58e3c5d34a347fbbfeba8351fc6fb70ecd82. Git blob pins:
- ValidatorRegistry.lean f561e66cc1d3a529c5325bbef15dcd36dcfa1daf
- RegistryProofMain.lean 5289bab9a4213523b6f3917f22d722e91ddf511d
- scripts/check-validator-registry.py 2033542b59549b8286516220873498bfc5594817
- workflow 0b02b195cdfea9560b214f99e871bd51e98e80c6

Independent local Python check: 128 sparse-tree roots reconstructed by a separate ordered branch fold, 497 changed-witness controls produced different roots. This verifies test-reference arithmetic, not Lean. Prepared differential inventory 1,528 rows, including malformed inputs, wrong widths, index and count boundaries, changed leaf/sibling/root, common-set membership and eligibility. Actual runner output, all six new theorem statements and axiom reports, compiled import audit and retained CI on this head are pending. No local Lean or networked git checkout was available. Dedicated hosted job uses pinned Lean and lake env lean --run; this is not a native executable benchmark. No performance improvement claimed. Limits: fixed 40 siblings, 4,096-byte line cap after stdin allocation, 20-character numeric token cap. Runtime/allocator and SHA2 refinement remain trusted/open. The branch is a draft candidate, not a passing checkpoint.

Remaining: authenticate registry root under fork-indexed BeaconState root, bind every attesting index and public key to one state, independently verify BLS, and apply actual slash transition with fork-specific penalties, rewards, and balance effects. Keep this candidate out of consensus-valid verdicts until then. #725 remains open.
