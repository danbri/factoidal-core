# Mainnet state slot and registry commitment — 24 November 2026

Issue #901; parent #725, execution subgoal #652 remains separately owned. New isolated branch based on #897 ac68d87158b4326bd04089aad1b2c923f39ac908. No main merge.

## Prior verified checkpoint

Hosted registry run 45398603037, job 138460941669, passed all steps. Its actual log reports 3,077/3,077 Lean registry rows, five comparator controls, 14 named axiom reports (two no axioms; one propext; eleven propext and Quot.sound), source/compiled module/native link audits. The source registry blob is 4b866923b80201b9cd8cf0d1a6458905f33b5942. Artifact https://github.com/danbri/factoidal-core/actions/runs/45398603037/artifacts/14921289093. This is predecessor evidence, not evidence for the edited code.

## New executable model

The prior candidate checker accepted an independently supplied eligibility epoch and SSZ layout. The new mainnet-only entry point derives epoch from uint64 slot (integer division by 32), uses the Electra epoch 364032 to select the known container depth, and verifies the slot leaf at field 2 (gindices 34 and 66) against the same supplied BeaconState root used in the existing registry proof. Only a matching slot branch reaches the prior checker, with the derived epoch and layout. Slot mismatch has a separate verdict. The legacy explicitly supplied layout/epoch path remains for retained tests, not canonical validation. No signature or canonical root authentication or state mutation.

Normative source ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3: phase0/beacon-chain.md blob fd3548bf8455bdc96597d2c551cb1c1eee1f8986 (slot field, get_current_epoch), electra/beacon-chain.md blob 13a1c4752975fa43a0a5dab36249b59f8698f2f7 (slot field), presets/mainnet/phase0.yaml blob 44030cc5b9c19b80cc72639ba348c226c34aa88e, configs/mainnet.yaml blob 3dadbd7433b69a45669cdd2459fee41653cd2ac1. The later layout is only intended for Electra/Fulu as pinned, not arbitrary future forks.

Seven new statements (pending Lean check): registrySlot_gindices, mainnetRegistryLayout_before/after, verifyMainnetStateSlot_bad_branch/delegates, checkMainnetSlotCommonValidator_mismatch/delegates. Hosted gate requires the exact 21 names and actual allowed axiom reports. These concern admission and concrete verifier linkage, not full normative transition refinement or SHA collision resistance.

## Verification on this slice

An independent local Python hashlib layer-tree/fold test passed 256 branch reconstructions (slot and registry for 128 trees), detected 1,636 individual altered-leaf/sibling controls. That was reference-model execution, not Lean execution. Native oracle adds 1,536 rows to the retained 3,077 (4,613 expected); includes slot boundaries, activation/withdrawable boundaries, Electra first slot and uint64 max, wrong branch lengths and slot/registry/root/leaf mutations; six comparator controls expected. All new Lean compile, axiom and native differential results pending fresh hosted job. No local Lean compiler or subagent CLI available; no shared Mac worktree or builds used. Source blobs: ValidatorRegistry.lean 94b73bc0d7e9d1fafcfbbc87a77e00b7fa6aaf4e; RegistryProofMain.lean 5f5ee0a7f9ad31d913d52f621ec06ede8d0d19ca; check-validator-registry.py 47c9950dd4491ccac9e0b97e2dc2b0c40dcf1680; workflow 544f61eee8e87002ef2fd7e51229c74406cebd95. Toolchain, package manifests and crypto implementation untouched. The existing 4096-byte transport limit runs after line allocation. No new performance numbers, full retained-suite pass, Linux release or premerge gate claimed. Compiler/runtime remain trusted.

Next: canonical chain state-root authentication, independent BLS validation, actual slashing transition, full fork-indexed state codecs and consensus integration.
