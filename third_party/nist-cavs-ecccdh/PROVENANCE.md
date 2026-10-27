# NIST CAVP ECC CDH primitive test vectors, P-256 section — provenance

`KAS_ECC_CDH_PrimitiveTest_P-256.txt` is the `[P-256]` section (lines
412 to 614, 25 cases, COUNT 0 to 24) of `KAS_ECC_CDH_PrimitiveTest.txt`,
copied byte for byte. No other change.

- Source: NIST Cryptographic Algorithm Validation Program (CAVP),
  "ECC CDH Primitive (SP800-56A Section 5.7.1.2)", CAVS 14.1, generated
  2012-11-19.
- URL: https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/components/ecccdhtestvectors.zip
- Fetched: 2026-10-27.
- sha256 of `ecccdhtestvectors.zip`:
  `5fff092551f2d72e89a3d9362711878708f9a14b502f0dfae819649105b0ea39`
- sha256 of `KAS_ECC_CDH_PrimitiveTest.txt` in that zip:
  `456068d3f8aad8ac62a03d19ed3173f00ad51f42b51aeab4753c20f30c01cf23`
- sha256 of the extract here:
  `bfaacd959823eaa35c2b9f64c0c4b983c210fe9f643c8ea3f3a925e5ce91c005`
- Reproduce: `unzip ecccdhtestvectors.zip && sed -n 412,614p KAS_ECC_CDH_PrimitiveTest.txt`
- Licence: a work of the United States Government (NIST), not subject to
  copyright protection in the United States (17 U.S.C. 105).

Fields per case: `QCAVSx`, `QCAVSy` (the peer public key), `dIUT` (the
private key), `QIUTx`, `QIUTy` (its public key), `ZIUT` (the shared
secret, the x coordinate of `dIUT * QCAVS`).

Used by `lake exe l4crypto-probe`, section `p256-ecdh`
(`formal/lean4/Harness/CryptoProbe.lean`), for
https://github.com/danbri/factoidal/issues/1083.
