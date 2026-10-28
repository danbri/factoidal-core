# Data Integrity cryptosuites as one table (2026-10-28)

Workstream: the Verifiable Credentials family of
https://github.com/danbri/factoidal/issues/1165. Related:
https://github.com/danbri/factoidal/issues/286 (Ed25519 through HACL\*),
https://github.com/danbri/factoidal/issues/578 (Lean crypto parity),
https://github.com/danbri/factoidal/issues/1164 (`factoidal sign` / `verify`),
https://github.com/danbri/factoidal/issues/1166 (P-384).

## Result

Step 1 of the workstream: `ecdsa-rdfc-2019` and `ecdsa-jcs-2019` (Data
Integrity ECDSA Cryptosuites v1.0, W3C Recommendation 2025-05-15) with P-256.
P-384 is refused on every target, with an expected-failure test, because
HACL\* has no P-384 (https://github.com/danbri/factoidal/issues/1166).

## How it works

A cryptosuite is a row of a table in
`formal/lean4/L4Factoidal/VC/Cryptosuite.lean`: a name, a family (EdDSA or
ECDSA: which curves it takes) and a transform (RDFC-1.0 or RFC 8785 JCS).
Every row runs the same steps:

| Step | Definition | Spec |
| --- | --- | --- |
| Transform | `Cryptosuite.transform`: JSON-LD toRdf then RDFC-1.0 with the hash of the key's curve, or `JSONLD.jcsDocument` | VC DI ECDSA 1.0 "Algorithms"; RDFC-1.0; RFC 8785 |
| Proof configuration | `configOf`, `verifyInputs` (the context rule) | VC DI 1.0 §4.3, §4.4 |
| Hash | `DataIntegrity.hashData`: H(configuration) then H(document) | the "Hashing" step of each suite |
| Sign / verify | a `Signer` and `Primitives`, parameters | FIPS 186-5 ECDSA (IEEE P1363 `r || s`), RFC 8032 |
| Serialise | `DataIntegrity.createFromCanonical` / `verifyFromCanonical`: base58-btc Multibase | the "Proof Serialization" step |

The hash follows the key: SHA-256 for Ed25519 and P-256, SHA-384 for P-384,
for the hash data and for RDFC-1.0 ("For P-384 keys, SHA-2 with 384-bits of
output MUST be used, specified via the RDFC-1.0 implementation-specific
parameter").

Keys: `resolvePublicKey` reads a did:key on the three curves (CID 1.0 §2.2.2
Multikey headers 0xed01, 0x8024, 0x8124) or, for an `https` method, the
controlled identifier document the host fetched (CID 1.0 §3.3), with a
Multikey or a JWK.

The context rule (VC DI 1.0, Verify Proof): a proof with its own `@context`
needs the document's `@context` to start with it; the document is then
canonicalised under the proof's context. A proof without `@context` uses
`proofContextFor` (RDFC; it adds the Data Integrity context to a VC 1.1
document so that the proof terms are not dropped) or the document's context
(JCS, the spec's Proof Configuration step).

## The signer is the custodian of the key

`Signer` (in `Cryptosuite.lean`) has a curve, a verification method and a
`sign` function. The library never sees a secret key. The one place a secret
key becomes a `Signer` is `diSigner` in `VC/CryptosuiteNative.lean`
(principle: `docs/web/hub/webdav-lws-design.md`, "One custodian per
privileged resource"). The wasm ops `vcDiKey` and `vcDiSecure` call it; the
key stays in the signer's closure. The ECDSA nonce comes from the host's
random source (node:crypto in the VC API shim) and is passed in; this tree
derives no nonce. VC DI ECDSA 1.0 says signatures "SHOULD use the
deterministic variant"; HACL\* has no RFC 6979 nonce derivation, so the
signatures are randomised. Verifiers cannot tell the difference.

## Theorems (`VC/CryptosuiteTheorems.lean`)

- `vcDiEcdsa10_ecdsaRdfc2019_p256_shares_eddsaRdfc2022`: ecdsa-rdfc-2019
  with P-256 and eddsa-rdfc-2022 have the same transform and hash.
- `verifyDataset_eddsaRdfc2022`, `verifyDataset_ecdsaRdfc2019_p256`: both
  are `DataIntegrity.verifyProofValue` at SHA-256, with different primitives.
- `transform_rdfc10_sha256`: the table's RDFC transform at SHA-256 is the
  transform of the eddsa-rdfc-2022 code that existed before the table.
- `verifyDataset_canonical_only`: verification reads the document only
  through its canonical form.
- `vcDi10_rdfc10_isomorphic_verify_alike`: two RDF-isomorphic credentials
  verify alike, PROVIDED `RDF.Canonical.RelabellingInvariance`. That RDFC-1.0
  property is stated in `RDF/CanonicalTheorems.lean` and not proved; this
  theorem reduces the VC property to it and does not prove it.
- `verifyJcs_canonical_only`: the same for RFC 8785.

## JCS key order: a repair

RFC 8785 §3.2.3 sorts member names as arrays of UTF-16 code units. The
existing JCS writer (`JSONLD/ToRdf.lean`, used by JSON-LD `@json` literals
and flattening) sorted by code point. The two orders differ when a name has a
character above U+FFFF and another has one in U+E000 to U+FFFF, and the RFC's
own §3.2.3 example is such a case. `jcsSortKey` now maps each character so
that code-point order of the images is UTF-16 order of the originals; the
RFC example is a `#guard`. The sort proofs are unchanged (they were stated
for any key function).

## Tests

- Build-time: `VC/CryptosuiteTests.lean`, over copies of the spec vectors:
  JCS documents, hash data for P-256 and P-384, did:key decoding, the context
  rule, the full verify pipeline with a stub primitive that accepts only the
  published (key, hash data, signature).
- Run time: `lake exe l4vc-probe`, section `vc-di-ecdsa-spec-vectors`,
  through HACL\*. Vectors: `third_party/testing/vc-di-ecdsa-vectors/`.
- Interoperability: the W3C vc-di-ecdsa-test-suite
  (`third_party/testing/vc-di-ecdsa/`), `tests/vc-di-ecdsa/run.sh`, through
  `bin/vc-api-shim` routes `/<cryptosuite>/credentials/{issue,verify}`.
  Scores: `docs/claude-rules/w3c-completeness-ledger.md`, row "VC 2.0 + Data
  Integrity".

## Not done

- P-384: https://github.com/danbri/factoidal/issues/1166 (decision needed).
- Proof chains (`previousProof`) in the table: refused, as in
  `DataIntegrity`. The shim's eddsa routes still verify chains.
- The npm package has no typed functions for the table yet; the shim uses the
  raw dispatch (`loadEngine().call`).
