# Vendored: test vectors of Data Integrity ECDSA Cryptosuites v1.0

- **Upstream:** https://github.com/w3c/vc-di-ecdsa, directory `TestVectors/`
- **Commit:** `59df72ca8cdb275d97eb496086fea6fac4fa7f0f` (2026-09-16T10:20:31-07:00)
- **Retrieved:** 2026-10-28, `git clone --depth 1`
- **Licence:** W3C Software and Document License (`LICENSE.md` of the
  upstream repository, copied here unchanged).

Copied unchanged: `ecdsa-rdfc-2019-p256/`, `ecdsa-rdfc-2019-p384/`,
`ecdsa-jcs-2019-p256/`, `ecdsa-jcs-2019-p384/`, `p256KeyPair.json`,
`p384KeyPair.json`, `unsigned.json`. Not copied: the `ecdsa-sd-2023/`
vectors and the employment and permanent-resident examples (the
selective-disclosure step will vendor what it needs).

These are the vectors of the specification's "Test Vectors" appendix. They
are read by `lake exe l4vc-probe` (section `vc-di-ecdsa-spec-vectors`), and
`formal/lean4/L4Factoidal/VC/CryptosuiteTests.lean` has copies of the
JCS and hash strings as build-time `#guard`s.

The interoperability suite of the same working group is vendored apart, in
`third_party/testing/vc-di-ecdsa/`.
