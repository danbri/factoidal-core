# VC-JOSE-COSE: plan and checklist (2026-10-28)

Step 4 of the VC family workstream of
https://github.com/danbri/factoidal/issues/1165. Specification: Securing
Verifiable Credentials using JOSE and COSE, W3C Recommendation 2025-05-15
(VC-JOSE-COSE 1.0). Status: not started beyond this plan.

## What exists to reuse

- `L4Factoidal/JOSE/Jws.lean`: JWS Compact Serialization (RFC 7515 §3.1),
  an algorithm allowlist (`ES256`, `RS256`, `EdDSA`), the `crit` refusal, and
  the theorems that a refused token never reaches a verifier and that the key
  type matches the algorithm. Verifiers are a parameter (HACL\* at the edge).
- `L4Factoidal/JOSE/Jwk.lean`: JWK parsing, EC P-256 `x || y`.
- `L4Factoidal/VC/Cryptosuite.lean`: `Signer` (the custodian of a key) and
  key resolution for did:key and CID 1.0 methods; `CryptosuiteNative.diSigner`.
- `L4Factoidal/VC/Credential.lean`: VCDM 2.0 checks for the payload.

## Plan

1. `VC/Jose.lean`: secure a VCDM 2.0 credential or presentation as a JWS
   (VC-JOSE-COSE §3.1.1, §3.1.2): protected header with `alg`, `kid`,
   `typ` `vc+jwt` or `vp+jwt`, `cty` `vc` or `vp`; payload the unsecured
   document; the signature from a `Signer`. Verify: `JOSE.verifyCompact`,
   the `typ`/`cty` checks of §3.1.3, then the VCDM 2.0 checks on the payload.
   Reuse, do not copy, the JWS code; add the `JOSE.Alg` signing direction if
   it is missing.
2. Theorems: a JWS-secured credential's payload is the unsecured document
   byte for byte (no canonicalization); a token refused by the header checks
   is refused for every key (the existing JWS theorem, restated for the VC
   media types).
3. COSE (§3.3): COSE_Sign1 (RFC 9052) needs a CBOR codec (RFC 8949). The
   tree has none. A Lean CBOR codec is a separate piece of work and also
   serves CBOR-LD (https://github.com/danbri/factoidal/issues/1165, the
   CBOR-LD item). Decide its scope there first.
4. SD-JWT (§3.2): needs RFC 9901 SD-JWT; later.

## The W3C test suite

w3c/vc-jose-cose-test-suite (commit cf4c93dd, 2026-09-01): 35 tests. Each
implementation is a command-line tool run by `docker compose`
(`tests/test-util.js`); a local adapter can call the factoidal engine in the
same way without Docker. Keys of the tests: P-256 (6), P-384 (11), P-521 (5),
Ed25519 (12), did:key Ed25519 (1). P-384 and P-521 depend on
https://github.com/danbri/factoidal/issues/1166 (HACL\* has no P-384 and no
P-521); they are expected failures until that is decided.

## Checklist

- [ ] `VC/Jose.lean`: secure and verify, JWS, ES256 and EdDSA
- [ ] Theorems as in plan item 2
- [ ] Wasm ops and a command-line adapter for the W3C suite (no Docker)
- [ ] Vendor w3c/vc-jose-cose-test-suite with provenance; score in the ledger
- [ ] P-384 and P-521 as expected failures naming issue 1166
- [ ] COSE: CBOR codec scope decided; COSE_Sign1
- [ ] SD-JWT
