---
title: "crypto.subtle over HACL*"
date: 2026-11-09T03:52:48Z
category: "Web APIs"
commit: "e80ae6ff8"
summary: "Page scripts have crypto.subtle: SHA digests, HMAC, HKDF, PBKDF2, ECDSA and ECDH on P-256, Ed25519, X25519 and ChaCha20-Poly1305. Lean holds the WebCrypto rules; HACL*, verified C from Project Everest, computes the primitives."
---

Lean checks every parameter, key usage and key format, and gives the error of every
refusal. Keys stay behind handles in Lean. The native engine and the Hub's WebAssembly
engine compile the same portable HACL* C, with no assembly.

- Web platform tests `WebCryptoAPI` (134 pages, QuickJS-NG): 12,660 of 34,580
  subtests pass, up from 3,260. No subtest that passed before fails.
- A page that does not use `crypto` pays nothing.

Off, because the HACL* we use has no such primitive: AES, P-384, P-521, Ed448 and
X448. RSA is future work. Each of them is refused with NotSupportedError.

Numbers: the design record
[2026-11-09-hacl-web-crypto.md, section 10](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-09-hacl-web-crypto.md#10-wpt).
