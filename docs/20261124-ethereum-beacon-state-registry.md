# BeaconState registry proof composition — 24 November 2026

Pre-code obligation: #896. Base #890, c5513dc1578f04e53d46f5e412a8b769076e9ac1, separate wip branch. No main or other branch edits.

## Verified preceding checkpoint

Hosted run https://github.com/danbri/factoidal-core/actions/runs/45389156914/job/138427965442 completed all registry job steps. Checked merge d60600bb5916321ba2dfce9a7ecec48bdd0dcc35, tree e4fc1f5a5433a2ce9099784c21aa32253e3dc067. Source-pinned registry module 4382daf829b898c3865810faccdc7ec1b9546a2b. All eight prior registry axiom reports passed; isSlashableValidator_iff uses propext, the other seven use propext and Quot.sound. 1,669/1,669 actual Lean rows passed; four comparator controls detected, seven source dependency negative controls rejected; native link audit checked bundled crypto link flags against executable symbols. This is earlier-tree evidence, not a pass of the changes below.

## Implementation

Read pinned ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3 specs/{phase0,altair,bellatrix,capella,deneb,electra,fulu}/beacon-chain.md. BeaconState field counts are 21,24,25,28,28,37,38. Validators is zero-based field 11. The container depths are 5 and 6, and generalised indices 43 and 75. Layout is explicitly supplied; no inference of fork activation or trusted state root is made.

The actual registry adapter now first checks a fixed-layout state branch with the existing concrete Lean SHA-256 verifier, and only on a matching result calls the existing common-validator proof and eligibility path. State-root mismatch is distinct from registry mismatch and from malformed input. A match remains candidate_not_authenticated. BLS, canonical head/finality, slot/fork/epoch anchoring, full BeaconState codec and state mutation are open. The CLI test transport uses 40 registry siblings, then state root, then 5 or 6 state siblings.

New theorem statements (not yet checked): registryState_phase0Deneb, registryState_electraFulu, verifyRegistryInState_bad_branch, verifyRegistryInState_delegates, checkStateCommonValidator_mismatch, checkStateCommonValidator_delegates. The gate now requires all 14 exact reports. The statements concern layout, admission and executable delegation, not normative complete consensus refinement or cryptographic collision resistance.

## Evidence on this slice

Local independent Python hashlib layer-tree check (not Lean execution) passed 128 synthetic container root reconstructions (92 depth-5, 36 depth-6), 676 individual sibling mutations and 128 registry-root mutations. All detected a different root. New oracle source preserves prior 1,669 rows and adds 1,408 composed rows across the seven field counts, with positive/negative candidate outcomes, wrong state root, registry root, siblings, validator fields, layouts, lengths and malformed chunk widths. Expected 3,077 rows and five comparator controls; actual new oracle and native results pending.

Implementation blobs: ValidatorRegistry.lean 4b866923b80201b9cd8cf0d1a6458905f33b5942; RegistryProofMain.lean 40eb35d8b4ec7e41df8b0d44fdb6111678d09340; check-validator-registry.py e301b263a2efd5cacdc44f0b53e86fa25db37fa9; registry workflow c144cf8071fbcb93566bc5fab31d2e164650216f. No new dependencies, unchanged toolchain/package config. No local Lean compiler or Codex worker is available. Hosted job must check all 14 actual axiom reports, compile, source/import/link audits and native comparison. The existing 4096-byte line check still runs after read allocation. No new performance numbers, full retained-suite pass, premerge gate or release gate claimed. Compiler/runtime remain trusted.
