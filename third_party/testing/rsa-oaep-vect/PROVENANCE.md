# RSA-OAEP test vectors (RSA Laboratories `oaep-vect.txt`): provenance

- File: `oaep-vect.txt`, the PKCS #1 v2.1 RSAES-OAEP test vectors that RSA
  Laboratories published with PKCS #1 v2.1 (`pkcs-1v2-1d2-vec.zip`). Ten key
  pairs (1024, 1025, ..., 1031, 1536 and 2048 bits), six messages each, 60
  vectors. Hash SHA-1, MGF1 with SHA-1, empty label. Each vector gives the
  message, the 20-octet seed and the ciphertext, so the encoding is
  deterministic and checks encryption as well as decryption.
- Copied from the pyca/cryptography test-vector tree:
  https://github.com/pyca/cryptography/blob/4ce3aa2cd8c41d688c7f1a3e5f886445ee50b508/vectors/cryptography_vectors/asymmetric/RSA/pkcs-1v2-1d2-vec/oaep-vect.txt
  (commit `4ce3aa2cd8c41d688c7f1a3e5f886445ee50b508`, the head of `main` on
  2026-10-27).
- sha256 of the copied file:
  `abca68e5176027ac98af1a4100b73e06bf2b36054d3f13f6a10e2fe603e8af4f`.
  The file is unchanged.
- Licence: the pyca/cryptography vectors are under Apache-2.0 or BSD-3-Clause,
  at the user's choice (`vectors/LICENSE` of that commit). This copy is used
  under Apache-2.0.
- Used by: section `rsa-oaep` of `formal/lean4/Harness/CryptoProbe.lean`
  (`lake exe l4crypto-probe`) and, for Example 1.1, the build-time `#guard`s
  of `formal/lean4/L4Factoidal/Crypto/RsaOaepTests.lean`.
  Tracking: https://github.com/danbri/factoidal/issues/1082.
- The Wycheproof RSA-OAEP vectors used by the same probe section are in the
  `third_party/testing/wycheproof` submodule (`testvectors_v1/rsa_oaep_*`),
  not copied here.
