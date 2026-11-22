# Verified RISC Zero ASK attestation

Tracking: <https://github.com/danbri/factoidal-core/issues/745> (ASK attestation
work); <https://github.com/danbri/factoidal-core/pull/759> (checked pipeline and
RISC Zero integration).

This records the evidence snapshot at **2026-11-22 19:15 UTC**. A genuine
RISC Zero 3.1.0 composite receipt was produced with development mode disabled.
A separate verifier invocation accepted the receipt against the expected
image and independently authorised 128-byte journal. All nine tampering
controls passed. The subsequent conversion and local Solidity verification
also completed successfully; their separate evidence is recorded below.

## Fixture and statement

The proved fixture has two input triples, `urn:a urn:p urn:b` and
`urn:b urn:p urn:c`. Its positive rules copy `urn:p` edges to `urn:reach`,
then extend a `urn:reach` edge through a following `urn:p` edge. The query
`ASK { <urn:a> <urn:reach> <urn:c> }` returns true. It uses the simple RDF
regime followed by the admitted positive rule fragment. This one receipt
does not establish proof coverage for the other test fixtures.

The input, query, rules, fixed 32-byte salt and context are deliberately
public. The context is
`beneficiary=public-fixture;action=check;nonce=1`. This records byte binding;
it makes no salt-entropy, data-authority or application nonce-consumption
claim. The journal contains the original-byte commitment, policy hash,
context hash and canonical Boolean, as specified by the
[checked pipeline](20261122-ask-attestation-pipeline.md).

Verified guest image ID:

```text
c6d11ad4ba2b40d049bd3c117779816c73b3247d7bc50bb00e1c5c898618239b
```

## Observed proof and verification

| Measurement | Recorded value |
| --- | ---: |
| Proof start, UTC | 2026-11-22 18:07:00 |
| Outer wall time | 3,941.714 seconds |
| User cycles | 11,888,533 |
| Total cycles | 17,563,648 |
| Segments | 34 |
| Receipt size | 9,104,164 bytes |
| Separate successful verification | 0.596 seconds |
| Configured Rayon threads | 8 |
| Configured segment limit | 2^19 rows |
| Configured address-space ceiling | 8 GiB |
| External wrapper timeout | 10,800 seconds |
| Peak prover RSS | Not measured |

The host's session ceiling is 64 Mi **user cycles**. The address-space
ceiling and timeout were imposed by the run wrapper; they are configuration,
not measured memory use or guarantees supplied by the host CLI.

The nine rejection controls changed the expected image, graph commitment,
policy hash, context hash or Boolean; supplied a noncanonical Boolean;
damaged the receipt seal; appended a byte; or truncated the receipt. Each
returned failure. Changing the expected Boolean of this true receipt tests
statement binding; valid false ASK answers remain a separate supported
result. The separate invocation uses the same pinned SDK verifier, not an
independent implementation of the proof system.

All **28 guest execution controls passed** against the same packaged program:
11 successful journals, including two valid false answers, and 17 refusals.
They include RDFS-before-rules ordering, retained base triples, duplicate
RDF triples, blank-node independence and scope, strict UTF-8 and N-Triples,
excluded query forms, frame errors and resource limits. These are execution
and native-parity results; only the positive rule-inference fixture above
has the cryptographic receipt recorded here.

## Exact source and build mapping

The evidence inventory records these local-to-published commit mappings.
The tree identifies the exact Git contents for each stage.

| Stage | Local commit | Published commit | Tree |
| --- | --- | --- | --- |
| Guest build | `85f4f26c1d819134f339c9e42e25943104926453` | `1bf9c1b430f7ddc3489d72991c82b01bd625600c` | `985a6bd54f57da71530fc24f84b54bcd3e9f2192` |
| Proving host | `d0011535116617460e1b8615c060233c4fc512e7` | `3cf6ccb83fea652753f9e6c8c0c380a924bc1c74` | `134b23c42a2296527ed80078541c44539df322e9` |
| Integration record | `a041e83979e2c8f72bc52d7bfcd5cf55b049697d` | `37a28c478fa2a89264629503eb73c7a4ab1c6043` | `92f0520cbb2c66b1b0ebf8057d30f1cf6a76208e` |

The recorded integration check finds the guest sources and compiled input
closure unchanged across these integration commits. The retained build
manifest, ELF and instruction checks, immutable archive snapshot and
corrected compiler-cache rebuild identify the actual build inputs and
linked result. The archive, ELF, packaged program and image were unchanged
after the corrected rebuild. This is same-environment reproducibility;
independent clean-host reproduction remains untested. See the
[link and cache provenance record](20261122-risc0-link-provenance.md).

## Retained evidence

`EVIDENCE.json`, format `factoidal-ask-evidence-v1`, records
the snapshot and complete inventory. Paths below are relative to that
external evidence bundle. Compiled binaries and receipts are not added to
Git by this work note.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `program/ask.bin` | 12,364,400 | `b62a0fbaf80f1660e75a9df2143c2ca540d7755db6481daf49e3d7eeb21cf56b` |
| `program/guest.elf` | 12,331,976 | `7ac93a820c99ff6737ed08406c5e08b2a069d7416f5066a39f2d9131b3c0343c` |
| `program/libfactoidal_ask.a` | 76,403,898 | `be857b40649925c33de5f9a0d30e0fee077ab74d05b37163683feb8ae933a294` |
| `proof/composite.receipt` | 9,104,164 | `47f60cc9df7610211e5e8116664dac5a60506f0e9f374c8f3e4ac57ab7f4c654` |
| `statement/journal.bin` | 128 | `5f01400e92038a3656503249767456de6ebdf2d7e7c8b967b1afcdb69054b32d` |
| `statement/expected-statement.json` | 360 | `d1d91158797ff535a33134b165c9da07c97323fa296be639225c409e35d298ef` |
| `build/manifest.json` | 686,776 | `6c943875c91d6bed1c5133849ceb4b408e95ccc85da2dc5fcd0bfc00f5eb0880` |
| `verification/composite/result.json` | 5,018 | `830dd552ae82c270b3ee935064c21d6cc09313a5176a28a59937ea8d4767cbb7` |
| `verification/guest/result.json` | 61,889 | `7682da818f81b7956fe0135ba800d116c31ca1e9657ad1005618393dc09c4472` |

The inventory also retains fixture bytes, proof metrics and log, the
native source/axiom/hygiene reports, all receipt-control logs, and toolchain,
ELF, instruction and integration-input checks. The metrics originate in
`zk-ask-prove-19-metrics.json`; the separate receipt and guest checks
originate in `zk-receipt-validation/result.json` and
`zk-guest-runner-evidence/result.json` respectively.

## Completed Groth16 and local Solidity verification

The official SDK compressed the 34 segments to a verified succinct receipt.
The first attempt then refused the identity conversion because the adapter
used the BN254 identity program's control ID as its verifier root. The SDK
expects the root of a depth-eight Merkle tree containing that ID and zero
padding. The corrected adapter derives this fixed root using the SDK's
unmodified Poseidon254 `hash_pair`, registers only `poseidon_254`, and retains
full integrity verification and equality with the originally authorised
claim. Its parameters come from pinned constants, not the returned receipt.
An additional regression checks the resulting parameter digest:

```text
8dfe5a6be7860f94a46ad4dd69483b3d2b11ea9bae656e86027e893879586b6b
```

All nine Rust tests passed. Resuming from the saved succinct receipt then
produced a verified identity checkpoint in 81.368 seconds. The guest proof
and its compression were not repeated. The official CPU witness generator
and gnark prover completed sequentially in 6.904 and 23.700 seconds. The
setup is `v2026-10-20.1`, with the verified amd64 OCI manifest
`49093ed164b82aca9305dd80e4a6eb996bd443201ac7bd50b52909b2761ef583`.

SDK finalisation and export verified the actual ASK image and exact journal.
A separate host invocation verified the saved Groth16 receipt in 0.011
seconds. The exported EVM seal is 260 bytes and uses the patched official
selector `0xe71e6620`.

| Checkpoint | Bytes | SHA-256 |
| --- | ---: | --- |
| Succinct receipt | 223,482 | `ef650a0bf8f5b94d06c42dd3cac66e571fdca25eb4b749a7b0d1c95aa3a6f616` |
| Identity receipt | 223,313 | `8b2f21dfd786baa7b9be34187c8e711f37f4026a88edbb331a94a2e6992a814c` |
| Identity seal | 222,668 | `c7114bb176f5d92b773dd0fbe4fbe18264cb5ad1662a08cbac6d7ac921e2c73c` |
| Native Groth16 proof JSON | 724 | `68b7dbd4040cd3a4622c3881c35177bf26e22a3af61786cdfc6d643cd518684f` |
| Verified Groth16 receipt | 753 | `e65a6fd2385d97c9d3f4a7c33c9dee11e7257484cb6f2b2e53ccd2a4abcaa55d` |
| Exported ASK EVM fixture | 1,072 | `2aa8f0ddc1191aa07bdfff812af573849d840e0c360ac0892c8fd6fbca868783` |

All seven actual ASK proof tests passed in Foundry, with no failures or
skips: the genuine proof succeeds, and changes to image, graph commitment,
authorised policy, authorised context, Boolean or seal fail. All 18
admission tests also passed. A fresh selected fixture directory passed the
same seven tests; a different selected directory with an altered expected
image failed setup while the retained default fixture remained unchanged.
The selection therefore did not silently fall back to the retained proof.

The instrumented successful `verifyTrue` external call used **230,839 gas**.
This includes ABI/STATICCALL/return overhead, and excludes deployment,
setup, input copies made before the timer, logging and transaction intrinsic
gas. The complete positive test used 273,492 gas. This successful-call
measurement is not a malformed-proof worst-case bound: the altered seal
reached the official pairing precompile's error path, and the test consumed
1,008,173,841 gas under Foundry's large harness budget before the wrapper
reverted `VerificationFailed`. Application call budgets remain separate.

The small genuine proof and independently prepared statement are retained
in [`evm/fixtures`](../zkvm/risc0/evm/fixtures/README.md), with provenance and
scoped CI. CI re-verifies this recorded image and statement; it does not
generate a new proof for later guest changes. Binary receipts and build
artifacts remain in the separate evidence bundle. The CPU runner's report
records an unverified native proof JSON; SDK finalisation and the separate
verification record establish acceptance of the resulting receipt.

## Remaining work and scope

The [checked saturation record](20261122-checked-saturation.md) and
[backend README](../zkvm/risc0/README.md) retain the ordered RDFS/rule and
full-seed completeness qualifications, admitted fragment and runtime trust
boundaries. The receipt does not extend those claims.

The recorded fixture now has an end-to-end local proof and EVM result.
The original issue's wider Phase 4 measurements and failure coverage,
allocation/hash-failure fault injection, independent
clean-host reproduction, and application nonce/action/beneficiary handling
remain tracked work. No external-chain transaction or stateful application
action was performed.
