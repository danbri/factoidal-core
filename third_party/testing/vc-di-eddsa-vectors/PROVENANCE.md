# Vendored: test vectors of Data Integrity EdDSA Cryptosuites v1.0

- **Upstream:** https://github.com/w3c/vc-di-eddsa, directory `TestVectors/`
- **Commit:** `13e7070534d1ba1c2987cb26bfb1535e0f15bb72` (2026-09-01T16:44:45-04:00)
- **Retrieved:** 2026-10-28, `git clone --depth 1`
- **Licence:** `LICENSE.md` of the upstream repository, copied here unchanged.

Copied unchanged: `eddsa-jcs-2022/`, `keyPair.json`, `unsigned.json`. The
eddsa-rdfc-2022 vectors of the same appendix are in
`formal/lean4/L4Factoidal/VC/Tests.lean` (since 2026-08-22).

Read by `lake exe l4vc-probe` (section `vc-di-ecdsa-spec-vectors`, which also
holds the eddsa-jcs-2022 checks of `VC/Cryptosuite.lean`);
`formal/lean4/L4Factoidal/VC/CryptosuiteTests.lean` has copies of the JCS and
hash strings as build-time `#guard`s.
