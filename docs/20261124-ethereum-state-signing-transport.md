# Raw attester vote transport repair — 2026-11-24

Issue #915, parent #725, continuation of #909. Base `d62cd0a95fe52f3bd7e5a56c337367337d82cf58`. Changes tested by source review at `b331015e03139bb57fbd862b4f980d9a04b2c041` only; no local Lean compiler or Codex worker available. No shared Mac access. No new implementation dependency or change to toolchain or protocol logic.

## Observed hosted evidence before repair

[Registry run 45420537158, job 138538518481](https://github.com/danbri/factoidal-core/actions/runs/45420537158/job/138538518481) checked merge commit `c2a14930978a2b155a3a1c1b3a2fa828413c2405`, tree `db41536105f7f73c1039e3229514668f16b6c861`. GitHub compare of the base head to the merge commit reports zero changed files. The source check passed and Python prepared 7,173 rows with seven comparator corruption controls. The library compiled; ValidatorRegistry compiled and printed all 26 reports below. The native build failed at RegistryProofMain.lean:64, where the nested signing constructor was parsed as a function argument instead of a constructed error. The subsequent dedicated theorem audit, native linkage audit and native oracle did not execute; do not treat the 7,173 prepared rows as native passes.

Source `ValidatorRegistry.lean` blob `db8ad5a73553398279f183b45bca644b79122fed` matches the hosted source pin and remains unchanged on the repair. Actual reports from the build log, with the timestamps and log prefix removed:

```text
'EthereumConsensus.SSZ.verifyValidatorAt_over_length' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.verifyValidatorAt_outside' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.verifyValidatorAt_bad_branch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.verifyValidatorAt_delegates' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.isSlashableValidator_iff' depends on axioms: [propext]
'EthereumConsensus.SSZ.checkCommonValidator_not_common' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkCommonValidator_mismatch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkCommonValidator_candidate' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.registryState_phase0Deneb' does not depend on any axioms
'EthereumConsensus.SSZ.registryState_electraFulu' does not depend on any axioms
'EthereumConsensus.SSZ.verifyRegistryInState_bad_branch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.verifyRegistryInState_delegates' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkStateCommonValidator_mismatch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkStateCommonValidator_delegates' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.registrySlot_gindices' does not depend on any axioms
'EthereumConsensus.SSZ.mainnetRegistryLayout_before' depends on axioms: [propext]
'EthereumConsensus.SSZ.mainnetRegistryLayout_after' depends on axioms: [propext]
'EthereumConsensus.SSZ.verifyMainnetStateSlot_bad_branch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.verifyMainnetStateSlot_delegates' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkMainnetSlotCommonValidator_mismatch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkMainnetSlotCommonValidator_delegates' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.stateSigning_gindices' does not depend on any axioms
'EthereumConsensus.SSZ.verifyStateSigningContext_bad_branch' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkStateVotes_bad_context' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkStateVotes_bad_preparation' depends on axioms: [propext, Quot.sound]
'EthereumConsensus.SSZ.checkStateVotes_delegates' depends on axioms: [propext, Quot.sound]
```

All 26 names match the source inventory. 4 reports are axiom-free; 3 depend on propext alone; 19 depend on propext and Quot.sound. (These counts are from the above reports.) The entire prior source graph is pinned in the hosted report:

```json
{
  "head": "c2a14930978a2b155a3a1c1b3a2fa828413c2405",
  "source_pins": {
    "formal/lean4/L4Factoidal/Crypto/SHA2.lean": "92737f4d83035745dba29ef2c3867b01b8dfa50f",
    "formal/lean4/L4Factoidal/Crypto/SHA2Tests.lean": "7ac4c2235566cd636d85848241fbbd1f3a1b246b",
    "formal/lean4/L4Factoidal/Crypto/SHA2Theorems.lean": "b878ce9d43eeeb77f06598fd55d9c01d9c62597c",
    "formal/lean4/ethereum-consensus/AncestryMain.lean": "f8ed01bc64de9a80a3f72fe972f00d70c15ebc3f",
    "formal/lean4/ethereum-consensus/BasicMain.lean": "e72494bc9de26db7a467309eb005458228fa163e",
    "formal/lean4/ethereum-consensus/BoostMain.lean": "5c3ba0e872bb2daab3beb01985092b564894d976",
    "formal/lean4/ethereum-consensus/ByteProofMain.lean": "6bfa47f5e15cb2e8d00422dbad2363cbdf551fd5",
    "formal/lean4/ethereum-consensus/CheckedMain.lean": "eedd064c4e88ff6d69811f4d31bbcbbbaf205a01",
    "formal/lean4/ethereum-consensus/ChildMain.lean": "d9081dc3783730f34f5c401720f3f26fc2b4ab1a",
    "formal/lean4/ethereum-consensus/ContainerRootsMain.lean": "cc3635b29abf0905fa1e4eab318602ac18c196e9",
    "formal/lean4/ethereum-consensus/EthereumConsensus.lean": "e697564e6eae6ccf7c5942ace1a3feaa470935ec",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/AttestationScore.lean": "e148ccef216287b2757f618603a2a822276b1c88",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/CheckedAncestry.lean": "3fb8b92abd221a48c5b4ae80bd55c498b24ab012",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/ChildSelection.lean": "aa1a8a5e5e3927151be718e8a1da5a6a122523f4",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/LatestMessage.lean": "917320d526e073a2a1780d2c030a40b6cd0adf07",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/ProposerScore.lean": "e329f342be77ff1519d357b72d63b36123040f85",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/StoredHead.lean": "671f3808f6e4f5b17994f97ea6bdef4f15f22a2e",
    "formal/lean4/ethereum-consensus/EthereumConsensus/ForkChoice/VoteStore.lean": "20b5e7d0b37a08d09402b9f3af9af66db62b9f29",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/AttestationData.lean": "066e9adcb47a0beed6ce9258722b9beb2ef8fd7f",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/AttesterSlashing.lean": "33a09146651425b78a5f9d860d58704fe0520d8b",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/BasicTypes.lean": "e2d3b3e2b4eb29c0ed2cea820a36713ae93ebb6d",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ByteProof.lean": "ff547b1c8547769ec36673c0f6dde3fb29bf40a1",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ByteProofTheorems.lean": "2fd9c36db65c98f6e7895696762cab3856bc7d53",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/CheckedBranch.lean": "9c3ebadf0100b86d4e6f9d20b87d6d0311a6e734",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ContainerRoots.lean": "c26954c1514b0d216f4aa4a3918a1bc4291af93c",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/GIndex.lean": "ec69368d7bf3d4ec1bbe533560ae93e3aaecbb2b",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/MultiProofHelpers.lean": "3bb33d5661020979c55ca7d188bc8af20054132d",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/SigningDomains.lean": "f3195b4b96a80ea2b5ba86317b1d89052594a1c0",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ValidatorRegistry.lean": "db8ad5a73553398279f183b45bca644b79122fed",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/VectorU64.lean": "d84159c860a5e2b41debe3e1d994a315259bb844",
    "formal/lean4/ethereum-consensus/LatestMain.lean": "48e6ab53c9cd7ba7be303c66101c3969723004cb",
    "formal/lean4/ethereum-consensus/Main.lean": "ad4a72fceebf79ba4c54808ff234970df5f5b9b3",
    "formal/lean4/ethereum-consensus/MultiProofMain.lean": "01e43bd4ecc2fc03de068459304383c5c8b69de1",
    "formal/lean4/ethereum-consensus/RegistryProofMain.lean": "e150b2292c98446106c74b7c0247d557614e0bba",
    "formal/lean4/ethereum-consensus/StoreMain.lean": "405522d5f2f0c9923e46581beff341cda9699bf3",
    "formal/lean4/ethereum-consensus/StoredHeadMain.lean": "3911bc1836ac3efa0edfa33678d80e3a4e93d31a",
    "formal/lean4/ethereum-consensus/VectorU64Main.lean": "684f80d38be6e6240f7504e7df61cdcfd3da6eaf",
    "formal/lean4/ethereum-consensus/WeightMain.lean": "43a1c0995096c74cc27697a8bb5a29b1f4dfe86f",
    "formal/lean4/ethereum-consensus/lake-manifest.json": "15728fe01a01ed2369565ec5be9afdf6abcf2f91",
    "formal/lean4/ethereum-consensus/lakefile.toml": "dbac6d2d2081ec960fadbe701c2f093be17cd0e3",
    "formal/lean4/ethereum-consensus/lean-toolchain": "a8afa7d1b02d96f0671eba854a8dc4b416beb473",
    "formal/lean4/ethereum-consensus/scripts/check-pure-lean-dependencies.py": "746a8fd4f8f16c4d474655e0f3ac3747d9723e64",
    "formal/lean4/ethereum-consensus/scripts/check-validator-registry.py": "b903efc85ea6686f8636aca2a720ca4bb60f8912"
  },
  "tree": "db41536105f7f73c1039e3229514668f16b6c861"
}
```

## Repair and checks

- Parenthesise the nested signing pattern in the transport; seven direct Lean guards cover the preparation error labels, including each DomainError constructor. New transport blob `559659dd98b7bab9fe65e64837c47358c0e33ca9`.
- Keep every previous oracle case; add eight malformed fullstate wire controls (flag, vote width, uint64 overflow, invalid hex, right-list resource refusal, missing/extra token, line cap). New Python oracle blob `9ead3dfe875be40ae3a320f5aaa2077793d9e237`. Expected total 7,181; execution pending.
- Local independent standard-library Python calculation reconstructed the first fullstate reference root `7701c6835385707c03fd56d2239be1590a3660e2326542cac3e102825b95f29b`, verified its 95-token geometry (14 header, 61 proof, 20 context/vote/list tokens), the negative indices -16 and -14, missing/extra token counts, and the oversized line boundary. This is a fixture/wire check, not a Lean execution result.
- GitHub compare shows only two files changed before this worknote: RegistryProofMain.lean and the Python oracle. All theorem source, SHA-256, manifest, toolchain and CI gates are unchanged. Fresh hosted compile, guards, exact axiom audit, native dependencies and full differential run are required. No like-for-like runtime measurement from this repair yet.

## Limits

Mainnet layout through Fulu only; supplied state commitment not canonical; no independent BLS, all-signer registry check, slashing transition or full consensus. The local 32-index admission limit is not a consensus rule. Full #725 and #652 remain open. No merge, release, wallet or network transaction.
