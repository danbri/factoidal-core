# HACL* in the web engine: crypto.subtle for page scripts

Date: 2026-11-09. Author: haclweb, a subagent of session depmap-0e.
Records it joins: `2026-11-08-page-scripts.md` (section 7, "Web APIs over Lean"),
`2026-07-08-self-hosted-hacl-wasm.md`, `2026-09-07-crypto-primitives.md`.
Vendored C: `third_party/hacl/` (cryspen/hacl-packages
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`, Apache-2.0; `third_party/hacl/PROVENANCE.md`).

## 1. Decision and result

The owner said yes to HACL* in the web engine, with theorems to tie it together and
with the integration points treated as the weak spots. This record describes that work.

Page scripts now have `crypto.subtle` with these algorithms:

- digest: SHA-1, SHA-256, SHA-384, SHA-512;
- HMAC, HKDF, PBKDF2;
- ECDSA and ECDH on P-256;
- Ed25519 and X25519;
- ChaCha20-Poly1305 (from the WICG modern algorithms draft).

The operations are `generateKey`, `importKey`, `exportKey` (raw, raw-public, raw-secret,
JWK, SPKI and PKCS #8), `sign`, `verify`, `deriveBits`, `deriveKey`, `encrypt`,
`decrypt`, `wrapKey` and `unwrapKey` (wrapping with ChaCha20-Poly1305).

They run natively (libweb-render.dylib), over the portable HACL* C (no Vale assembly, no
vector code). Since the follow-ups of section 13, the Hub (web-render.wasm) links no HACL*:
Lean makes the same decisions there and the browser's own crypto.subtle does the
primitives (13.4). RSA for imported keys came later the same day (13.1).

The work splits three ways:

- **Lean holds the WebCrypto algorithm logic** (`Crypto.WebCryptoKeys`): the registry,
  parameter validation, the key usages rules, extractability, the key formats and the
  error of every refusal.
- **HACL\* computes the primitives** (`Crypto.WebHacl`, `ffi/hacl_webcrypto.c`).
- **prelude.js converts and settles**: it does WebIDL conversion, shapes objects and
  settles promises in event-loop tasks (section `haclweb`).

## 2. The layers, and the trusted computing base

```
page JS ── prelude.js (glue) ── n.api ── Hosts.WebApi (op 30-32, 40-42) ── WebCryptoKeys ── WebHacl ── hacl_webcrypto.c ── HACL*
```

Trusted without proof:

1. **HACL\* itself.** The twelve units are SHA-1, SHA-2, HMAC (with the BLAKE2 units it
   links), Ed25519, Curve25519_51, P256, ChaCha20, Poly1305, the AEAD and Lib_Memzero0.
   They are KaRaMeL's C extraction of F*/Low* code that Project Everest proved:
   functionally correct against F* specifications, memory safe under its preconditions,
   and free of secret-dependent branches and memory accesses. Lean trusts these proofs
   at the FFI boundary. The `HashAgrees`, `HmacAgrees` and `CtEqAgrees` hypotheses of
   `WebHacl` are exactly the functional-correctness facts that the agreement theorems use.
2. **KaRaMeL's runtime headers and the C compiler** (cc natively, Emscripten for Wasm).
   HACL*'s verified constant-time property holds for the C, not for the machine code; no
   compiler is verified to keep it. Lib_Memzero0 uses `memset_s` on macOS and a volatile
   loop under Emscripten.
3. **`ffi/hacl_webcrypto.c`**, 260 lines. It holds no cryptographic logic, only length
   checks, allocation, one HACL* call per entry point and zeroing.
   `tools/hacl-web-glue-audit.py` checks its shape (section 4). Its known-answer test is
   `tests/crypto/run-kat.sh`.
4. **The Lean compiler and runtime.** They provide reference counting, the C code
   generated from Lean, and the erasure of the proofs passed to the externs.
5. **The entropy source.** Natively this is `IO.getRandomBytes`, which uses the
   operating system. Under Emscripten it is the browser's `crypto.getRandomValues`.
   WebScripts gives 32 bytes of it to each session.
6. **The two script engines.** QuickJS-NG in WasmVM, and BubblePopJS, only keep the
   page's JavaScript from reaching the prelude's closures (the WeakMap of keys and `n`).
   Even if one fails, Lean still refuses to export a non-extractable key, because the
   rule is in Lean (`exportOp_extractable`).

Not trusted, and proved or checked instead:

- the length preconditions at every call (types);
- the output sizes (theorems);
- the registry, usages, extractability and formats (Lean, with theorems where cheap);
- the DER reader (round-trip theorem);
- base64url (the existing `JOSE.Base64Url` with its theorems);
- the glue's shape (the audit).

## 3. Boundary guarantees

| Weak spot | Guarantee | How |
|---|---|---|
| Buffer lengths into HACL* | No call passes a buffer that breaks the primitive's precondition: key, nonce, tag, signature, point and message lengths, and the `uint32_t` bounds. | Every extern in `WebHacl` takes a proof of its precondition (`HashPre`, `HmacPre`, `Ed25519SignPre`, `X25519Pre`, `P256SignPre`, `P256VerifyPre`, `P256EcdhPre`, `ChaChaSealPre`, `ChaChaOpenPre`, …), and each precondition restates the F* one. Lean erases the proofs, but no call type-checks without one. The C checks the same lengths again before any HACL* call (audit rule 3). |
| Output sizes | Every answer has exactly the primitive's size. | The C allocates the output at that size. The Lean wrappers check it. Theorems: `hash?_size`, `hmac?_size`, `ed25519Sign?_size`, `ed25519Public?_size`, `x25519?_size`, `x25519Public?_size`, `p256Public?_size`, `p256Sign?_size`, `p256Ecdh?_size`, `p256Decompress?_size`, `chachaSeal?_size`, `p256MsgRep_size`. |
| Aliasing | No output overlaps an input. Inputs may alias each other; HACL* reads them only. | Every output is a fresh `lean_alloc_sarray` made in the entry point (audit rule 4). Lean byte arrays are immutable values, so borrowed inputs are never written. |
| Partial output | A C failure never leaves a partly written output visible. | On a HACL* refusal the output is zeroed with Lib_Memzero0, freed and replaced by an empty array (audit rule 5). Decryption that fails answers one status byte and nothing else. Lean maps an empty answer to an error. |
| Key material | Page JavaScript never holds key bytes; it holds a handle. | Keys live in `WebApi.State.keys` (a `KeyStore`). A CryptoKey's slots in the prelude are a handle, type, extractable flag, algorithm and usages. `exportOp_extractable`: an export that succeeds is of an extractable key. `exportOp_blind`: what exportKey answers does not depend on the bytes of any non-extractable key, whatever handles the page passes. `wrapKey` exports through `exportKey`, so the same rule applies. |
| Hostile inputs | Malformed JWKs, wrong curve points (invalid points and the point at infinity), short and long buffers, NaN or negative lengths, and detached buffers are all refused with the API's error. | Points: HACL*'s `Hacl_P256_validate_public_key` (not infinity, coordinates below p, on the curve) on every imported point, and `compressed_to_raw` for compressed points. Scalars: `validate_private_key` (0 < d < n). X25519: HACL*'s `ecdh` refuses the all-zero secret of a small-order point. Ed25519 verify refuses small-order keys and R values (libsodium's list, with the non-canonical encodings). DER: strict minimal lengths and no trailing bytes. JWK: strict base64url. Lengths: WebIDL [EnforceRange] in the glue, then Lean. Detached buffers read as empty. |
| Constant time | The glue branches on no secret. | Lean computes no primitive. HMAC verify compares in C with KaRaMeL's `FStar_UInt8_eq_mask` fold (`ctEq`; `ctEq_eq` proves that it is equality under `CtEqAgrees`). AEAD tags are checked by HACL*'s decrypt. The glue branches only on lengths and on HACL*'s public success flags. Audit rule 6 refuses `memcmp` and byte `==`. Section 6 lists what is not constant time. |
| Randomness | Every random byte comes from the session's HMAC_DRBG, which is seeded with at least 256 bits from the OS. No path uses an unseeded generator. | `WebApi.randomBytes` is the only caller of `Drbg.generate`. Theorem `randomBytes_seeded`: every draw that succeeds had `entropy.size ≥ 32` and fewer than 2^48 draws. Section 5 has the details. |
| Errors | Every refusal is one of the API's exceptions, and the page sees the one Lean chose. | `WebCryptoKeys.Err` has seven cases. `Err.code_injective` and `Err.code_neg` hold: codes are negative, so they are never lengths. The prelude maps each code to its DOMException name, and an unknown code becomes OperationError. |
| Secret lifetime | Key bytes are zeroed when a key is dropped, where Lean's memory model allows it. | Section 5. |

## 4. The C boundary (`ffi/hacl_webcrypto.c`)

Each of the 19 entry points has the same shape:

1. check every length;
2. allocate a fresh output of exactly the primitive's size;
3. make one HACL* call;
4. on a refusal, zero and free the output and answer an empty array;
5. zero the stack temporaries (the P-256 ECDH point; only its x leaves).

`tools/hacl-web-glue-audit.py` checks six rules:

1. the C symbols and the Lean externs are the same set;
2. every extern that takes a buffer takes a precondition proof;
3. sizes are checked before the first HACL* call;
4. outputs are fresh;
5. a failed HACL* call never answers its output;
6. there is no `memcmp` and no byte `==`.

A mutation check confirmed that the audit catches three faults:

- a removed size check;
- a `memcmp`;
- an answered refused output.

`tests/crypto/run-kat.sh` runs 44 checks at the C level. They cover:

- FIPS 180-2;
- RFC 2202, 4231, 8032, 7748, 6979 (A.2.5, signing with its own k) and 8439;
- the refusals: wrong lengths, a zero nonce, an off-curve point, the point at
  infinity, a bad compressed prefix, a small-order X25519 point, a forged tag.

## 5. Randomness and secret lifetime

**The generator.** HMAC_DRBG (SP 800-90A §10.1.2) runs over HACL*'s HMAC-SHA-256.

- It is instantiated on first use from the session's entropy: 32 bytes of the host
  generator plus the session number. No nonce or personalisation comes from the page.
- `Drbg.generate` updates the state after each call, which gives backtracking
  resistance.
- There is no reseed and no prediction resistance. A session runs one generator for
  its life. Someone who reads the generator's state in the engine's memory can predict
  the rest of that session's output, but not earlier output.
- After 2^48 generate calls (SP 800-90A's reseed interval) the session refuses with
  OperationError.

Every use draws from this generator:

- `getRandomValues` and `randomUUID`;
- HMAC and ChaCha20-Poly1305 keys;
- P-256 scalars (eight 32-byte candidates per key; one fails HACL*'s range check with
  probability below 2^-32);
- Ed25519 and X25519 seeds;
- ECDSA nonces (eight candidates per signature).

The DRBG's state is held by Lean in the session, never in the page.

**Where secrets live, and for how long.**

- **In Lean.** The key store is a `Std.HashMap` of `Key`s whose `material` and `pub` are
  Lean `ByteArray`s. When the page's CryptoKey is collected, QuickJS-NG's
  FinalizationRegistry calls op 42. Lean then removes the key and passes its byte arrays
  to `WebHacl.wipe`, which zeroes an array in place when the store held the last
  reference (Lean RC = 1).
- **What zeroing cannot reach.** A shared array cannot be zeroed without changing a value
  another holder sees, so it is only released. An example is an export whose answer
  still references the same bytes. Intermediate secrets in Lean are freed by reference
  counting without zeroing: an HMAC key block, derived bits, a decrypted plaintext.
  Lean's allocator may reuse that memory later. BubblePopJS has no garbage collector
  yet, so its keys live until the session ends. At session end the whole state is freed,
  not zeroed.
- **In the guest.** The QuickJS guest zeroes its argument block and answer buffer for
  ops 30-49 (`qjs_wasmvm_entry.c`). The prelude zeroes its copy of imported key data
  once Lean has it. Exported key bytes and derived bits are in page-owned ArrayBuffers,
  as the API intends.
- **On the Hub.** Everything is in WebAssembly linear memory, which the browser's page
  can read. web-render.wasm is no stronger a boundary there than the JavaScript heap.

## 6. Constant-time audit

Constant-time:

- every HACL* primitive (verified);
- `ctEq` for HMAC verify;
- the X25519 zero check (HACL*'s mask fold);
- AEAD tag checks.

Not constant-time, and why that is acceptable:

- **Lengths.** Lengths are public.
- **Public-key checks.** Point validity and the Ed25519 small-order list are computed
  over public keys.
- **Retry loops.** The scalar and nonce candidate loops end at the first candidate in
  range. They show whether a random candidate was at or above n, which happens with
  probability 2^-32 and reveals nothing about the value used.
- **JWK and DER parsing.** The parse of a private JWK or a PKCS #8 branches on the
  structure and the lengths, but not on the bytes of `d` beyond their length. Base64url
  decoding of `d` is a table walk with data-dependent control in Lean (`decodeDigit?`).
  This is an accepted gap: a page that imports a key already knows its bytes.
- **HMAC_DRBG.** It runs in HACL*'s HMAC. Lean only concatenates and splits arrays.

## 7. Theorems

`Crypto/WebHacl.lean`:

- **Precondition types.** The precondition types of the 17 externs that take buffers.
  Each extern's signature is the statement: no call without the proof.
- **Sizes.** `checkSize_size`, `hash?_size`, `hmac?_size`, `ed25519Sign?_size`,
  `ed25519Public?_size`, `x25519?_size`, `x25519Public?_size`, `p256Public?_size`,
  `p256Decompress?_size`, `p256Sign?_size`, `p256Ecdh?_size`, `chachaSeal?_size`,
  `p256MsgRep_size`.
- **Refusals and preconditions.** `hash?_none_of_not`, `hmac?_none_of_not`,
  `ed25519Sign?_pre`, `x25519?_pre`, `p256Sign?_pre`, `p256Ecdh?_pre`, `chachaSeal?_pre`,
  `chachaOpen?_pre`, `ed25519Verify_false_of_bad_sig`, `p256Verify_false_of_bad_sig`.
- **Agreement with the specification** (given HACL*'s correctness): `hashFast_eq_pure`,
  `hmacFast_eq_pure`, `haclHash_eq_pure`, `hkdf_hacl_eq`, `pbkdf2_hacl_eq`, `ctEq_eq`.
  So HKDF, PBKDF2, HMAC verify and HMAC_DRBG over HACL* are the pure-Lean specification
  functions of `Crypto.WebCrypto`, which carry the RFC vectors as `#guard`s.

`Crypto/WebCryptoKeys.lean`:

- **Errors.** `Err.code_injective`, `Err.code_neg`, `Err.mem_all`.
- **DER.** `readTlv_tlv`, the round trip: reading what `tlv` wrote gives the tag, the
  contents and the rest.
- **Export.** `exportKey_extractable`, `exportKey_blind`.
- **Usages.** `keyFor_of_bind`, `sign_usage`, `verify_usage`, `deriveBits_usage`,
  `crypt_usage`: each operation needs a key of its algorithm with its usage.
- **Imports.** `checkUsages_ok`, `finishKey_ok`, `importKey_usages`: an imported key
  has exactly the usages and extractability asked for, and a secret or private key has
  a usage.

`WasmVM/Hosts/WebApi.lean`:

- `exportOp_extractable`, `keyOf_blind`, `exportOp_blind`;
- `randomBytes_seeded`, `randomBytes_entropy`.

`#guard`s run the protocol in the interpreter, with no HACL* involved:

- registry answers;
- an HMAC key imported, exported raw and as JWK;
- export refused for a non-extractable key;
- SyntaxError for bad and for empty usages;
- TypeError for an unknown handle;
- no generator without entropy.

They also cover DER reads (non-minimal and indefinite lengths refused), the SPKI and
PKCS #8 shapes against the WPT fixtures' bytes, the Ed25519 small-order list and the
message representative.

## 8. Vectors

There are three levels of check.

1. **C known-answer tests**: `tests/crypto/run-kat.sh`, 44 checks (section 4).
2. **End to end in the engine**: `tests/crypto/webcrypto_engine.ts --vectors`. It runs
   the path page JS → prelude → Lean → C → HACL* on:
   - FIPS 180-2, RFC 4231, 5869 A.1, 6070, 7914 §11, 8032 §7.1, 7748 §6.1, 6979 A.2.5
     and 8439 §2.8.2;
   - hostile inputs: off-curve and infinity points, x ≥ p, a zero scalar, a small-order
     X25519 point, a 31-byte key, non-base64url JWK members, a JWK with no kty, NaN and
     negative lengths, non-DER and truncated PKCS #8, a detached buffer, a forged tag,
     sign with a verify key.
3. **The WPT WebCryptoAPI vectors** (section 10). They include the NIST and RFC vectors
   of `*_vectors.js`.

Agreement of HACL* with the pure-Lean references:

- the theorems of section 7 reduce it to `HashAgrees` and `HmacAgrees`;
- the pure references carry the RFC vectors as `#guard`s;
- the HACL* side passes the same vectors in the KAT.

Ed25519, X25519, P-256 and ChaCha20-Poly1305 have no pure-Lean reference, because the
crypto policy forbids one. They are checked on the vectors only.

Wycheproof is not used here. The `third_party/testing/wycheproof` submodule is empty in
these checkouts. `Harness/CryptoProbe.lean` runs the Wycheproof corpora against the
core CLI's HACL* externs when it is present.

## 9. What stays off, and why

- **AES (CTR, CBC, GCM, KW).** The pinned HACL* has no portable AES. Its only AES-GCM is
  EverCrypt over Vale x86-64 assembly (AES-NI). hacl-star `main` has none either
  (checked 2026-11-09: `dist/gcc-compatible` has only `Hacl_AES128.h`). This arm64 Mac
  and the Wasm engine therefore refuse with NotSupportedError, from the registry. The
  owner decides (section 12).
- **P-384 and P-521.** HACL* has only P-256. A normalized `namedCurve` of P-384 or P-521
  refuses with NotSupportedError, after the usages check that the specification puts
  first.
- **RSA (OAEP, PSS, PKCS #1 v1.5).** The pinned HACL* has the bignum operations
  (`Hacl_Bignum64`, used by `Crypto/RsaOaep.lean` and the JOSE RS256 path) but no prime
  generation, so `generateKey` is impossible. Import, sign, verify, encrypt and decrypt
  of imported keys are future work: they need the RSA DER key formats.
  `Hacl_RSAPSS.c` is upstream but not vendored.
- **Ed448 and X448.** Not in HACL*.
- **Modern-algorithm drafts other than ChaCha20-Poly1305** (ML-KEM, ML-DSA, SHA-3, KMAC,
  Argon2, AES-OCB). These are not done.

## 10. WPT

`tests/browser-wpt/testharness-run.ts` was run on 25 directories: WebCryptoAPI and its
subdirectories, with the window variant. The engine was native, the script engine
QuickJS-NG in WasmVM, and the WPT copy the pinned ce5ca396.

| Run | Pages | Subtests passed |
|---|---|---|
| Before (main d6de344a1), pbkdf2 and derived_bits excluded | 132 | 3,260 of 25,807 |
| After, the same 132 pages | 132 | 8,303 |
| After, `derived_bits_length` (excluded before) | 1 | 45 of 45 |
| After, `pbkdf2` (excluded before; 8,632 subtests in one page, no `?1-1000` split) | 1 | 4,312 of 8,632 |
| After, total | 134 | 12,660 of 34,580 |

- No subtest that passed before fails now.
- Chrome counts 70,798 subtests in WebCryptoAPI, across every variant and worker.
- BubblePopJS, the same directories: 2,837 before on the 132 pages, 7,439 after;
  11,350 of 32,061 with pbkdf2 and derived_bits; again none lost.

Where the gains are:

- `import_export`: 304 → 3,734;
- `derive_bits_keys` (hkdf);
- `generateKey` (ECDSA, ECDH, Ed25519, X25519 and the HMAC failures);
- `sign_verify`: 57 → 222 (ECDSA P-256, EdDSA, HMAC, the small-order points);
- `wrapKey_unwrapKey` (ChaCha20-Poly1305);
- `modern-algos` ChaCha20-Poly1305: the generateKey, importKey and encrypt/decrypt
  pages pass whole.

Most of what still fails is outside the algorithms this engine has:

- AES-CTR, AES-CBC, AES-GCM, AES-KW and AES-OCB: their generateKey, encrypt_decrypt
  and import pages, and the PBKDF2 and HKDF deriveKey to AES types;
- RSA, including `rsa_importKey` (1,056);
- P-384 and P-521: two thirds of `ec_importKey` and of the ECDSA vectors;
- Ed448 and X448;
- ML-KEM, ML-DSA, KMAC, SHA-3 and Argon2.

Other failures are the `idlharness` pages, `getRandomValues` (it expects the new
QuotaExceededError interface) and `algorithm-discards-context` (it expects a document
body).

The WPT run found one bug in the glue, now fixed. A CryptoKey the page no longer
referenced could be collected between a call and its task, and its handle dropped in
Lean. The prelude's `later` now holds the operation's keys until the task runs.

The record of this run: the after-run JSON files listed in the hand-back. They are not
committed: the baselines under `tests/browser-wpt/` cover other directories.

## 11. Performance and sizes

**Pages that do not use crypto pay nothing.** Nothing new runs at page start.

- `crypto` is a lazy getter, as before. HACL* needs no initialisation (no CPU feature
  probe: there is no Vale).
- The key store is an empty map in the session state.
- Measured on this machine, median of 15, native (QuickJS-NG):

  | | Before | After |
  |---|---|---|
  | Plain page start | 5.98 ms | 6.04 ms |
  | Script page start (timers-and-clicks) | 64.4 ms | 64.9 ms |

  A second pair of runs gave 6.12 / 6.47 ms and 65.2 / 70.4 ms while a WPT run
  shared the CPU.
- BubblePopJS: plain page start 0.55 / 0.54 ms, script page 6.65 / 6.37 ms.
- Advance turns 0.015 ms in both.
- Wasm: plain page start 43.9 / 44.8 ms and 44.5 / 45.9 ms; script page 546 / 548 ms
  and 547 / 566 ms. These ran with a WPT run alongside, within noise.
- `test.sh` passes on the after engine, including the frame-cost ratchet tests.
- check-budget: identical (default.html 703 paint items, status.html 13,382).

**Crypto costs, native engine** (`tests/crypto/webcrypto_engine.ts --bench`, page start
subtracted, median of 3, QuickJS-NG):

| Operation | Before (pure Lean) | After (HACL*) | HACL* alone (C) |
|---|---|---|---|
| digest SHA-256, 1 MiB | 79 ms | 43 ms | 3.9 ms |
| PBKDF2-SHA-256, 100,000 iterations | 1,232 ms | 110 ms | 95 ms (100,000 HMACs) |
| ChaCha20-Poly1305 encrypt, 1 MiB (AES-GCM is off) | not supported | 80 ms | 2.8 ms |
| Ed25519 sign + verify, ×100 | not supported | 167 ms | 11 ms |
| ECDSA P-256 sign + verify, ×100 | not supported | 342 ms | 62 ms |

On BubblePopJS, natively:

- PBKDF2 at 100,000 iterations: 116 ms (before: 1,288 ms);
- Ed25519 ×100: 35 ms;
- ECDSA ×100: 97 ms;
- digest of 1 MiB: 605 ms, and ChaCha of 1 MiB: 1,518 ms. Both are BubblePopJS making
  and copying the 1 MiB typed array, not crypto (before: 818 ms for the digest).

**Crypto costs, Wasm engine (Hub)**, QuickJS-NG:

| Operation | Before | After | HACL* alone (Wasm in Node) |
|---|---|---|---|
| digest SHA-256, 1 MiB | 319 ms | 254 ms | 4.6 ms |
| PBKDF2-SHA-256, 100,000 iterations | 2,216 ms | 336 ms | 113 ms |
| ChaCha20-Poly1305 encrypt, 1 MiB | not supported | 552 ms | 2.9 ms |
| Ed25519 sign + verify, ×100 | not supported | 1,827 ms | 55 ms |
| ECDSA P-256 sign + verify, ×100 | not supported | 3,122 ms | 154 ms |

**Where the rest of the time goes.** Outside PBKDF2, most of an operation's time is the
path around it, not HACL*:

- a promise settled in an event-loop task;
- the argument copies through the guest;
- `n.api` itself.

A 32-byte digest takes about 2.2 ms per operation natively, the same before and after
(measured: 100 digests 243-291 ms before, 235-258 ms after). In the Wasm engine it takes
about 15 ms. Operations are tasks by design (never inside a frame). Cutting the per-task
cost is event-loop work, not crypto work.

**Sizes:**

| Artefact | Before | After | Added |
|---|---|---|---|
| libweb-render.dylib | 45,492,688 | 45,975,840 | +483,152 (+1.1%) |
| web-render.wasm | 26,602,274 | 27,281,515 | +679,241 (+2.6%) |
| web-render.wasm, gzip -9 | 5,421,913 | 5,585,556 | +163,643 (+3.0%) |
| QuickJS guest (prelude bytecode) | 1,163,720 | 1,164,444 | +724 |

Native object sizes (text and data):

- HACL* units with the shim: 236 KB;
- the new Lean modules (WebCryptoKeys, WebHacl, WebCrypto, JOSE.Base64Url): 234 KB.

The HACL* precomputed tables (Ed25519 and P-256) are static data. In web-render.wasm
they are part of the data section, which the browser loads at instantiation. Making them
lazy would need a separate Wasm module, linked on first use (section 12).

## 12. Decisions taken (depmap-0e, for the owner), and what is still open

- **AES: open, for the owner.** HACL* has no portable AES. Natively it stays off; on the
  Hub it comes from the browser (section 13.4).
- **RSA for imported keys: done (13.1).** `Hacl_RSAPSS.c` is vendored. There is no
  generateKey.
- **P-384 and P-521: off natively.** On the Hub they come from the browser.
- **The Hub: the browser's crypto.subtle does the primitives, Lean decides (13.4).** This
  replaces "lazy HACL\* in Wasm": the Hub's web-render.wasm links no HACL\*.
- **Wycheproof: populated and run (13.2).**
- **Secret lifetime: the store is zeroed at session end (13.3).** On the Hub,
  WebAssembly memory is readable by the embedding page. That is the platform's limit. In
  host mode a key's bytes never enter it unless the page itself imports them.

## 13. Follow-ups (2026-11-09, after the merge)

### 13.1 RSA for imported keys

The algorithms are RSASSA-PKCS1-v1_5, RSA-PSS and RSA-OAEP, with keys imported as SPKI,
PKCS #8 or JWK, and exported in the same formats.

- **The primitive.** The C boundary gains four entries:
  - `rsa_public`: `Hacl_Bignum64_mod_exp_vartime`;
  - `rsa_private`: `mod_exp_consttime`. d is padded to |n| octets, so its bit length
    stays in Lean;
  - `rsapss_sign`: `Hacl_RSAPSS_new_rsapss_load_skey` and `rsapss_sign`. The
    secret-key limbs are zeroed and freed;
  - `rsapss_verify`.

  Each Lean extern takes a proof of `RsaOpPre`, `RsaPssSignPre` or `RsaPssVerifyPre`:
  moduli of 1024 to 4096 bits in whole limbs, exponent and operand lengths, salt at most
  |n|. The size theorems are `rsaPublic?_size`, `rsaPrivate?_size` and
  `rsaPssSign?_size`, and `rsaPssVerify_false_of_bad_sig` covers a bad signature.
- **The paddings are Lean's.** EMSA-PKCS1-v1_5 is `JOSE.Pkcs1.emsaEncodeGen`.
  EME-OAEP is `Crypto.RsaOaep`, with its single refusal for every decoding failure
  (Manger). The hashes are HACL*'s.
- **Not supported.** RSA-PSS with SHA-1 is refused with NotSupportedError at import:
  HACL*'s PSS is SHA-2 only. generateKey checks the usages and the parameters
  (OperationError for an exponent other than 3 or 65537, or a length outside 1024 to
  4096 in multiples of 64), then refuses with NotSupportedError: HACL* has no prime
  generation.
- **Key formats.** DER INTEGERs are read strictly: no negative and no non-minimal
  encoding. Export rewrites them canonically.
- **WPT** (native, QuickJS): 12,660 → 14,627 (+1,967), with no subtest lost.
  - `rsa_importKey`: 0 → 984 of 1,056;
  - `rsa_oaep`: +180;
  - `rsa_pss`: +112;
  - `rsa_pkcs`: +66;
  - wrapKey with RSA-OAEP: +65;
  - the RSA generateKey failures pages: +560.

### 13.2 Wycheproof

The `third_party/testing/wycheproof` submodule (C2SP/wycheproof `3fa63dd`, Apache-2.0,
test input only) is populated. `tests/crypto/wycheproof_engine.ts` runs each file
through crypto.subtle in the engine: page JS, prelude, Lean, C, HACL*.

| Corpus | Tests |
|---|---|
| Ed25519 | 151 |
| ECDSA P-256 SHA-256 and SHA-512 (P1363) | 594 |
| X25519 | 518 |
| ECDH P-256 (WebCrypto JWK) | 353 |
| HKDF (SHA-1, 256, 384, 512) | 339 |
| HMAC (SHA-1, 256, 384, 512) | 692 |
| PBKDF2 (SHA-1, 256, 384, 512) | 240 |
| ChaCha20-Poly1305 | 325 |
| RSA-PSS 2048 SHA-256 | 108 |
| RSASSA-PKCS1-v1_5 2048 SHA-256 and SHA-512 | 518 |
| RSA-OAEP 2048 (SHA-1 and SHA-256) | 73 |

All 3,911 pass, natively. A test passes when its outcome matches `valid`, `invalid` or
`acceptable`.

### 13.3 Secret lifetime at session end

`WebScripts` ends a session on close or on a new start. Each key's bytes are then zeroed
in place by `WebHacl.zeroNow`.

The reference-counted `wipe` zeroed none there. Measured: 1,600 key bytes handed over,
0 zeroed. While it ran, the store, the session and the held state all still referenced
each key. `zeroNow` zeroes whatever the count, because every holder goes with the
session, but it leaves compiled-in constants alone.

The close answer reports `keyBytesWiped` and `keyBytesZeroed`. A key dropped while its
session lives on keeps the reference-counted `wipe`, because a structuredClone copy may
share its bytes.

### 13.4 The Hub: the browser does the primitives, Lean decides

With `cryptoHost` in the start request (`Page.Limits.cryptoHost`, `WebApi` host mode),
an operation runs in four steps:

1. **Lean makes its checks**, as natively:
   - the registry;
   - the usages for the key type the format makes;
   - extractability, and export refused for HKDF and PBKDF2;
   - the JWK `use`, `key_ops` and `ext`;
   - the key's algorithm and usage for every key operation;
   - the public and private key types;
   - a P-256 public point on the curve (`p256OnCurve`, in Lean, over public values);
   - a P-256 private scalar with 0 < d < n.
2. **The primitive becomes a request in the turn answer** (`crypto`): JSON, with bytes
   in base64url.
3. **The host runs it on the browser's own crypto.subtle**
   (`docs/web/hub/foafnaut/crypto-host.mjs`, imported by `browser-worker.mjs`). Keys
   are the browser's CryptoKeys in the host's table. Lean holds their attributes and
   number, never their bytes.
4. **The host answers** with the `crypto` action. Lean turns the answer into the page's
   answer and queues the page's callback as a task (both engines, `WebApi.hostDone`).

Lean also checks that a secret or private key the host made has a usage.

AES-CTR, AES-CBC, AES-GCM and AES-KW are registered in host mode only.

The Hub's web-render.wasm links no HACL*. It links `hacl_webcrypto.c` with a core that
refuses every primitive (`hacl_webcrypto_nohacl.c`), and `l4wc_linked` answers 0.
Without a host (an insecure context), crypto.subtle is off. getRandomValues stays: its
HMAC_DRBG falls back to Lean's own HMAC (`WebHacl.hmacFast`).

Size of web-render.wasm, built from the follow-up tree:

| | Bytes | Gzip -9 |
|---|---|---|
| Linking HACL* (main) | 28,225,861 | 5,798,632 |
| Without HACL* | 27,968,048 | 5,707,201 |
| Saved | 257,813 | 91,431 |

A page without crypto loads and runs nothing more.

**Checks:**

- **Vectors on the Hub, in headless Chrome** (`labs/demos/foafnaut/hub_crypto_check.mjs`,
  both guest paths, AOT and WasmVM): 38 of 39. The difference was a zero P-256 private
  scalar in a JWK: Chrome answers OperationError, where natively the answer is
  DataError. Lean now checks the scalar first (the 0 < d < n check above).
- **Vectors in host mode with Deno's crypto.subtle as the host** (`webcrypto_engine.ts
  --crypto-host`, both script engines): 36 and 35 before Lean's point check. Deno
  accepts off-curve points and the point at infinity, which are now refused by Lean.
- **WPT WebCryptoAPI in host mode with Deno as the host** (`testharness-run.ts
  --crypto-host`, QuickJS, native engine): 22,876 of 34,968, against 14,627 natively.
  - **Gains** come from what the host has: AES (generateKey, encrypt_decrypt, the
    PBKDF2 and HKDF deriveKey to AES types), P-384 and P-521, RSA generateKey.
  - **Small losses** come from Deno's own behaviour: okp_importKey −20 to −24, and the
    Ed25519 small-order points −5.

  The real Hub uses Chrome, whose crypto.subtle is closer to the WPT expectations.
  Running the WPT pages through the Hub worker is not done yet.

### 13.5 The task overhead

The question was the 2.2 ms native and 15 ms Wasm per operation. Measured natively, on
merge build `059a5f7b5`:

| On QuickJS-NG in WasmVM, each | ms |
|---|---|
| `setTimeout(0)` round trip | 0.54 |
| microtask | 0.19 |
| `n.api` call (getRandomValues) | 0.45 (34,000 WasmVM instructions) |
| digest | 1.69 |

A JavaScript loop step costs about 730 WasmVM instructions, so the cost is QuickJS
interpreting the glue inside WasmVM.

- **BubblePopJS** (the native default) takes 0.10 ms for a whole digest operation and
  0.026 ms for a task.
- **Two changes to the glue:**
  - Lean's registry answer is asked once per (op, name);
  - operations started in one turn share one task.

  On QuickJS, 200 digests at once: 2.28 → 1.66 ms each; one after another: 1.80 → 1.77.
- **Further gains** are a question for the guest, not crypto: the Hub's AOT path, or
  BubblePopJS on the Hub.

## 14. The first round's open questions (2026-11-09, before the decisions of section 12)

1. **AES.** HACL* has no portable AES at this pin or on hacl-star `main`. The choices:
   - keep AES off (as now);
   - link EverCrypt and Vale for x86-64 hosts only (no use for the arm64 desktop or the
     Hub);
   - take a verified portable AES from another source (not HACL*), as a second pin.

   AES is the largest WPT block left: about 9,000 subtests across generateKey,
   encrypt_decrypt, import_export and wrapKey.
2. **RSA.** Import, sign, verify, encrypt and decrypt for imported RSA keys are possible
   over the vendored `Hacl_Bignum64` and the existing `Crypto/RsaOaep.lean`:
   - PSS needs `Hacl_RSAPSS.c`, which is upstream at the same pin but not vendored, or
     a Lean PSS encoding over the bignum;
   - generateKey needs prime generation, which HACL* lacks.

   Should RSA be done next, and should `Hacl_RSAPSS.c` be vendored?
3. **P-384 and P-521.** These are not in HACL*. They stay off unless another verified
   source is accepted.
4. **Lazy HACL\* in Wasm.** The Hub pays 164 KB gzipped of download for every page.
   A side module loaded on first use of `crypto.subtle` would move that off the
   start path. It is Emscripten dynamic linking, a build change of its own.
5. **Secret lifetime.**
   - Today: zeroing on drop where the store holds the last reference, and zeroed guest
     buffers.
   - Not done: zeroing intermediate Lean values (Lean's allocator) and zeroing the
     whole store at session end. The second needs a session close hook in WebScripts.
   - On the Hub, linear memory is readable by the embedding page.

   Is that the bar, or should crypto run in a separate Wasm instance per origin?
6. **Wycheproof.** The submodule is empty here. Populating it would let a probe run the
   Wycheproof ECDSA, ECDH, X25519, Ed25519, HKDF, HMAC and ChaCha corpora through the
   web externs, as `Harness/CryptoProbe.lean` does for the CLI's.
