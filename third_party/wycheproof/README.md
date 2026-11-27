# Wycheproof test vectors (ECDSA, secp256k1, SHA-256, P1363 signatures)

One file of test vectors, used only as a test oracle for the signature
verification in `formal/lean4/ethereum-wallet`. No code is taken.

- File: `ecdsa_secp256k1_sha256_p1363_test.json` (252 tests: 167 valid, 85 invalid)
- Source: https://github.com/C2SP/wycheproof, `testvectors_v1/ecdsa_secp256k1_sha256_p1363_test.json`
- Commit: 878e5366008753df2064d40c49f8e2f50f9c6af7
- SHA-256: 7a339efc7134fb2495cd32afdbd692e0f86427d3c24e9073f6a7d858bb8788d2
- Licence: Apache-2.0 (`LICENSE` beside this file), unmodified.
