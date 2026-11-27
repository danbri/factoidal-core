# bitcoinjs-lib ECDSA fixtures (RFC 6979 on secp256k1)

One fixture file, used only as a test oracle for the deterministic signing in
`formal/lean4/ethereum-wallet`. No code is taken. RFC 6979 itself publishes
no secp256k1 vectors; these are the widely reproduced ones (private key,
message, nonce, signature, and the 1st, 2nd and 16th nonce candidates).

- File: `ecdsa.json`
- Source: https://github.com/bitcoinjs/bitcoinjs-lib, tag v3.3.2, `test/fixtures/ecdsa.json`
- SHA-256: 63475f7539040d41760619ade10e4000794b12ffea2f7c4165d026cc37ca1f3f
- Licence: MIT (`LICENSE` beside this file), unmodified.
- The private keys in this file are published test values. They must never hold funds.
