# State-bound vote signing context — 24 November 2026

Issue #908, parent #725. Branch based on verified #902 at fc6c606207e88d61fff1a06b943c8f4af31fa616, not the withdrawn EthLib work. No main merge.

## Prior actual execution evidence
Hosted run https://github.com/danbri/factoidal-core/actions/runs/45408944235 (job 138497180829) passed all steps. Its actual log contains PASS 4613/4613 native registry cases, six comparator controls and 21 printed axiom reports (three empty, three propext, fifteen propext and Quot.sound); source, compiled import and native link checks passed. This evidence is for #902, not this change. The earlier full corpus gate remains a separate blocker.

## New entry
The pinned normative reference is ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3, phase0 beacon-chain.md: Fork, BeaconState fields 1 and 3, get_domain, is_valid_indexed_attestation. The existing mainnet slot/layout checker is reused. The Fork root is computed from two padded Bytes4 fields and the uint64 epoch, with zero padding to four fields. Verify both the Fork and genesis_validators_root branches against the same supplied state root; only then derive the two signing roots from actual attestation data and ordered index lists; finally invoke existing slot and validator registry verification. No synthetic prepared record is supplied in the fullstate transport. The previous synthetic helper remains for retained regressions. Outputs are unauthenticated candidate verdicts with computed signing roots, not a signature check.

Five new theorem selections: stateSigning_gindices, verifyStateSigningContext_bad_branch, checkStateVotes_bad_context, checkStateVotes_bad_preparation, checkStateVotes_delegates. They express local admission and executable composition, not a full consensus refinement. New actual Lean compile/axiom/native test passes not claimed yet. Existing gate expects exactly 26 reports.

Independent local Python hashlib test passed 512 branch reconstructions across 128 synthetic trees, 3200 separate leaf/sibling mutation controls, and 256 signing-root cross-checks comparing recursive Merkle and heap construction. This was a separate reference check, not the new Lean executable or full repository oracle. The committed generator adds 2560 expected fullstate rows to retained 4613; expected total 7173, seven comparator controls. Hosted gate must execute them. No local Lean compiler or subagent CLI available; no shared worktree used. The fullstate transport has an 8192-byte guard after line allocation; existing operations retain 4096. Performance and new native regressions not yet measured.

## Exact source pins
- `formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ValidatorRegistry.lean`: db8ad5a73553398279f183b45bca644b79122fed
- `formal/lean4/ethereum-consensus/RegistryProofMain.lean`: e150b2292c98446106c74b7c0247d557614e0bba
- `formal/lean4/ethereum-consensus/scripts/check-validator-registry.py`: b903efc85ea6686f8636aca2a720ca4bb60f8912
- `.github/workflows/ethereum-validator-registry.yml`: ab2a88bcb339eac9f33f204e091bef611e148cf2
- `formal/lean4/ethereum-consensus/lake-manifest.json`: 15728fe01a01ed2369565ec5be9afdf6abcf2f91
- `formal/lean4/ethereum-consensus/lean-toolchain`: a8afa7d1b02d96f0671eba854a8dc4b416beb473
- `formal/lean4/L4Factoidal/Crypto/SHA2.lean`: 92737f4d83035745dba29ef2c3867b01b8dfa50f
Manifest, toolchain and SHA2 source blobs match base. No new imports or implementation dependency; compiler/runtime and test transport remain trusted. Fresh hosted build uses existing cap and source/import/link audits.

## Limits
Caller-supplied state root is not a canonical chain authentication. This path checks one common validator, not all signers; no BLS authentication, full indexed-attestation signature validation, complete fork-indexed state validation or state mutation. The previous/current versions are selected by target epoch against the committed state Fork, not by a global history lookup. Local 32-index bound remains a resource refusal. Future layout changes need explicit support. No readiness or release claim.
