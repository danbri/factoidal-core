# Web Crypto API: inventory, what HACL\* allows, and the theorems

Date: 2026-11-14. Records it joins: `2026-11-09-hacl-web-crypto.md` (the layers, the C
boundary, randomness, secret lifetime), `2026-11-13-wpt-small-fixes.md` (the order of the
refusals' errors). Policy: `skills/crypto-policy`, `skills/lean-risk-flags`.

## 1. Where the WPT subtests are

Main 19fb349c1, Linux x86-64 full run 43550560855, BubblePopJS: 48,428 of the 70,798 subtests
Chrome reports in `WebCryptoAPI/` (68.4%). The scale counts Chrome's subtests per test, not
Chrome's passes, so a subtest Chrome fails still counts when Foafnaut passes it. The 22,370
lost subtests, by cause (both variants, window and worker):

| Cause | Lost | Verified implementation in HACL\* at the pin (05c3d8fb) |
|---|---|---|
| AES key objects with no AES operation: generateKey, importKey, deriveKey into an AES key, serialization | 6,120 | none needed; the keys are refused because AES is |
| AES-GCM/CBC/CTR/KW encrypt, decrypt, wrap | 2,574 | no portable AES; EverCrypt AES-GCM is Vale assembly for x86-64 only |
| AES-OCB | 1,254 | no |
| RSA with imported keys: import/export, sign/verify, encrypt/decrypt | 2,620 | yes: `Hacl_Bignum64`, `Hacl_RSAPSS` |
| RSA generateKey (456) and the wrapKey page, which generates its wrapping keys (722) | 1,178 | no prime generation |
| ECDSA, ECDH on P-384 and P-521 | 1,282 | no (P-256 only) |
| Ed448, X448 | 468 | no |
| ML-KEM (1,752), hybrid KEMs (1,530), ML-DSA (804), encapsulation into AES keys (384) | 4,470 | no |
| KMAC | 792 | no: needs the Keccak sponge with another domain byte, which `Hacl_Hash_SHA3` does not expose |
| TurboSHAKE, KangarooTwelve, Argon2 | 658 | no |
| SHA3-256/384/512, cSHAKE with empty name and customization | 272 | yes: `Hacl_Hash_SHA3` |
| `SubtleCrypto.supports`, `getPublicKey` | 780 | not a primitive |
| idlharness, getRandomValues, script errors in two pages, small API gaps | about 175 | not a primitive |

Everything without a verified implementation stays refused with NotSupportedError, after the
argument checks the specification puts first. Nothing here adds a primitive of our own.

## 2. What this change adds

### 2.1 Without any new binding (branch `wip/webcrypto`)

- **`SubtleCrypto.supports(operation, algorithm, lengthOrAdditionalAlgorithm)`**:
  `WebCryptoKeys.supports`. prelude.js makes the WebIDL conversions and normalizes the
  algorithm for the operation (an algorithm that does not normalize is not supported); Lean
  answers from the same tables the operations use, including the parameter checks that do not
  depend on a key or on data (an HMAC length of 0, an HKDF length above 255 blocks or not whole
  octets, a null length, a ChaCha20-Poly1305 nonce or tag length, an ECDH public key of the
  wrong kind, a derived key longer than the derivation can give). It is truthful about what
  the engine refuses: AES, P-384 and P-521, Ed448, X448, ML-KEM, ML-DSA and KMAC answer false,
  where the WPT pages expect true for them.
- **`subtle.getPublicKey(key, usages)`**: `WebCryptoKeys.getPublicKey`. The public key is
  built from the public key a private key already carries; no primitive runs.
- wrapKey takes the bytes it encrypts through `wrapPlain`, which is `exportKey` and nothing
  else, so the extractability theorems cover it by name.

### 2.2 With new HACL\* bindings (branch `wip/webcrypto-hacl`, not on main)

- **RSA for imported keys** (RSASSA-PKCS1-v1_5, RSA-PSS, RSA-OAEP): import and export as SPKI,
  PKCS #8 and JWK, sign, verify, encrypt, decrypt, wrapKey and unwrapKey with an imported
  RSA-OAEP key. From `wip/haclweb-2` (9dc4d564d), brought onto current main. Primitives:
  `Hacl_Bignum64_mod_exp_vartime` (public operation), `Hacl_Bignum64_mod_exp_consttime`
  (private operation, d padded to |n| octets), `Hacl_RSAPSS` (sign and verify, SHA-2 only).
  Encodings in Lean: EMSA-PKCS1-v1_5 (`JOSE.Pkcs1`) and EME-OAEP (`Crypto/OaepEncoding.lean`,
  split out of `Crypto/RsaOaep.lean` unchanged so that the engine does not link that module's
  two externs). Moduli of 1024 to 4096 bits in whole 64-bit limbs. generateKey still makes no
  key: HACL\* has no prime generation (`generateKey_rsa_refused`). RSA-PSS with SHA-1 is
  refused at import.
- **SHA3-256, SHA3-384, SHA3-512 and cSHAKE128/256 digests**: `Hacl_Hash_SHA3.c` vendored from
  the same pin (`third_party/hacl/PROVENANCE.md`). cSHAKE is served only with an empty function
  name and customization, where it is SHAKE; otherwise NotSupportedError
  (`cshakeLen_named_refused`). There is no pure-Lean SHA-3 and so no fallback: where HACL\*
  cannot answer, `sha3?` answers nothing and the digest is an OperationError.
- **The hygiene ratchet.** A new verified primitive is a new `@[extern]`. `LabHygiene`'s
  `lab_ratchet` caps the engine's closure at 22 externs and says raising it needs the owner.
  These two features need 27 (five entry points: `rsaPublicRaw`, `rsaPrivateRaw`,
  `rsaPssSignRaw`, `rsaPssVerifyRaw`, `sha3Raw`). The raise is a separate, marked commit on the
  branch. It is not merged without that decision.

## 3. The C boundary (branch `wip/webcrypto-hacl`)

`ffi/hacl_webcrypto.c` gains five entry points of the shape the 2026-11-09 record describes
(length checks, a fresh output of the primitive's size, one HACL\* call, refused outputs zeroed
and never answered). `tools/hacl-web-glue-audit.py`: 24 C entry points, 24 Lean externs, clean.
`tests/crypto/run-kat.sh`: 67 checks pass (44 before). New: FIPS 202 values for SHA3-256/384/512
and SHAKE128/256; an RSA 2048-bit test key made for the test, where RSASP1 of the
EMSA-PKCS1-v1_5 encoding of "abc" equals OpenSSL's signature and RSAVP1 of that signature gives
the encoding back; `rsapss_verify` accepts OpenSSL's PSS signature and refuses a wrong message,
salt length, signature length and SHA-1; the refusals of each entry point.

## 4. Theorems

Proved (no `sorry`, no axiom beyond Lean's three):

| Theorem | Says |
|---|---|
| `keyFor_no_usage`, `sign_no_usage`, `verify_no_usage`, `deriveBits_no_usage`, `crypt_no_usage` | an operation whose usage the key lacks IS the InvalidAccessError, for all other arguments: the answer is a constant, so no primitive ran |
| `keyFor_wrong_alg`, `sign_wrong_alg` | the same for a key of another algorithm |
| `wrapPlain_extractable`, `wrapPlain_blind` | wrapKey gets bytes to encrypt only from an extractable key; for a non-extractable key the answer does not depend on its bytes |
| `keyFields_blind` (`Hosts/WebApi.lean`) | what the page receives for a key from generateKey, importKey, deriveKey, unwrapKey, cloneKey and getPublicKey (handle, type, extractable, usages, algorithm) is the same whatever the key's bytes |
| `getPublicKey_hidePrivate`, `getPublicKey_ok` | getPublicKey's answer is a function of the public parts only; it is public, extractable, with exactly the usages asked, each allowed for a public key |
| `supports_refused` | for a name with no keys here and no digest, `supports` is false for every operation and all arguments |
| `tlv_of_readTlv`, `tlv_of_expect` | DER reading is exact: what is accepted is the canonical encoding of what is answered, so non-minimal, indefinite and over-long lengths are refused and nothing is skipped |
| `readSpki_spkiOf`, `readSpki_spkiOf_params`, `readPkcs8_pkcs8Of` | reading what the SPKI and PKCS #8 writers wrote gives the parts back |
| `spkiOf_of_readSpki` | an accepted SPKI is exactly the canonical SPKI of its parts: export after import is the identity on accepted bytes |
| `unb64_b64` | the base64url of JWK members decodes to the bytes |
| `sha3?_size`, `sha3?_fixed`, `cshakeLen_named_refused` (hacl branch) | SHA-3 answers have the length asked; a fixed-length function is never answered at another length; a named cSHAKE is refused |

Already on main and still holding: `exportKey_extractable`, `exportKey_blind`,
`exportOp_extractable`, `exportOp_blind`, `keyOf_blind`, `sign_usage`, `verify_usage`,
`deriveBits_usage`, `crypt_usage`, `importKey_usages`, `generateKey_refused`,
`importMade_refused`, `readTlv_tlv`.

Tested only (`#guard`s and WPT): the answers of `supports` for the WPT cases; the order of
errors; cSHAKE lengths; the key formats at the level of whole keys.

Open:

- Whole-key round trips (`importKey` of `exportKey k` is `k`) are proved only as far as the
  containers: the EC and RSA imports call HACL\* to validate, which Lean cannot unfold, and
  the JWK path goes through prelude.js's object. They hold under the hypothesis that HACL\*
  accepts the key it made; stating that needs the key invariant as a predicate on the store.
- A PKCS #8 exactness theorem like `spkiOf_of_readSpki` (PKCS #8 allows attributes after the
  key, which the reader accepts and ignores, so the statement is not an equality).
- Constant time is HACL\*'s claim for its C (record 2026-11-09 §6); nothing here restates it.

## 5. Unverified or flagged lines (`skills/lean-risk-flags`)

- `hashFast` on the message of an RSA or ECDSA signature falls back to pure Lean above
  HACL\*'s bound (already in the register; never reached by a page's arguments).
- EME-OAEP decoding (`OaepEncoding.emeDecode`) runs in Lean on the output of the private
  operation. It is written in a constant shape with one refusal for every failure, but Lean's
  lists allocate: its timing is not shown independent of the padding. Existing code and an
  existing row of the policy's table; now also reachable from pages (branch only).
- The RSA private operation is HACL\*'s constant-time exponentiation without blinding and
  without CRT.
- JWK and DER parsing of private keys branches on structure and lengths (record 2026-11-09 §6).
- `supports` and `getPublicKey` follow the WICG "Modern Algorithms in the Web Cryptography
  API" draft as the WPT pages exercise it; the draft's text was not at hand, so the checks are
  from the tests.

## 6. Measurements

(filled in from the cloud checks; see section 7)

## 7. Cloud checks

(run ids and numbers)
