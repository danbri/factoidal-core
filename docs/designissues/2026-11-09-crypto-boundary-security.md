# The crypto boundary: adversarial review, fixes and theorems

Date: 2026-11-09. Author: cryptosec, a subagent of session depmap-0e.
Joins: `2026-11-09-hacl-web-crypto.md` (the layers, TCB, threat model of `crypto.subtle`),
`2026-11-08-page-scripts.md`, `2026-11-08-shadow-dom-frames.md`.

## 1. What was asked, and how it was done

The owner asked for assurance that the crypto boundary is not a disaster waiting to
happen, remembering that security fails at weak links. The chain is:

```
page JS (hostile) ─ engine (QuickJS-NG in WasmVM, or BubblePopJS) ─ prelude.js (haclweb, basics)
  ─ n.api ─ Hosts.WebApi (dispatch, session State, HMAC_DRBG, key store)
  ─ Crypto.WebCryptoKeys (WebCrypto rules, keys, formats) ─ Crypto.WebHacl (wrappers, proofs)
  ─ ffi/hacl_webcrypto.c (+ _core.c) ─ HACL* (verified in F*)
```

The work had two phases.

1. **Adversarial review** of every link, with attacks run as page scripts in the engine on both
   script engines, `#guard`s in Lean, and a sanitizer fuzzer for the C. Each real problem was
   fixed in its own commit before the theorem work.
2. **Structure and theorems**:
   - a `Secret` type that Lean's privacy enforces;
   - noninterference by usage;
   - handles;
   - hedged RFC 6979 nonces, and sessions that start fresh;
   - algorithm and curve binding, and canonical DER;
   - a mechanical check of the C against HACL*'s own preconditions, and the fuzzer;
   - host-mode keys;
   - a work bound for every operation.

The threat model is the one in the HACL* record: page JavaScript is hostile; it may call any
`crypto.subtle` method with any arguments, any number of times, in any order, from the page or
from a sandboxed frame. It must not learn the bytes of a non-extractable key, break another
session's or origin's randomness or keys, or stall the engine. The engine, Lean, the C compiler
and HACL* are trusted (section 15).

## 2. Findings

| Id | Severity | Where | What | Fix |
|---|---|---|---|---|
| F1 | **High** (on `wip/shadowframes`, not on main) | `WebScripts.frameLimits` | Each sandboxed frame's session copied the page's `Limits`, so the frame's HMAC_DRBG started from the page's seed and repeated its stream. That included `getRandomValues` and `randomUUID` values, generated key bytes and ECDSA nonces. A frame that called `generateKey(…, true, …)` in the page's order reproduced the page's non-extractable keys and could export them. | `5a491828e` on branch `wip/cryptosec-frames` (= `wip/shadowframes` + 1): each frame gets 32 fresh bytes of the host generator and `frame:<el>` (`frameEntropy`). It is for shadowframes to take before merging. |
| F2 | **Medium** | `JS.HeapOf.rng`, the QuickJS guest | `Math.random` was the same sequence in every session of a process, on both engines. Measured in two sessions: QuickJS-NG gave 0.5457579157752497 and 0.5706820288638397 both times; BubblePopJS gave 0.4977440861790998 and 0.8923507647386716 both times. BubblePopJS's seed is a constant in the realm snapshot; QuickJS-NG takes its seed when the guest is prepared, and every session copies that memory. A page or frame could predict another's. | `ac08e26c3`: `WebApi.mathRandomSeed`, the first 8 bytes of SHA-256(`foafnaut Math.random` 0 entropy). It is domain-separated, so Math.random's outputs, which give xorshift's state away, reveal nothing of the DRBG seed. BubblePopJS sets it in `LeanJS.start`. The QuickJS guest asks web_api op 33 at page start and calls `JS_SetRandomSeed`, which `build-quickjs.sh` appends to the pinned `quickjs.c`. |
| F3 | **Medium** | `WebApi`, `WebCryptoKeys` | No crypto operation was charged to any budget, and some had no bound. An HMAC key of 2^31 bits took 9.2 s in one call, and 2^32 - 1 bits were allowed. PBKDF2 allowed 2^32 - 1 iterations, about an hour, and `Date.now()` did not move meanwhile. JWK `key_ops` were deduplicated by quadratic `List.eraseDups`: 4,000 entries took 165 ms on BubblePopJS, and half a million would take most of an hour. A 64 MiB SPKI became a 64-million-cell `List UInt8` before its first tag was read. | `0727c8435`: `opWork` bounds every call's work before it runs; calls above 2^24 units (about 4.5 s natively) are refused; the work is charged to script time (section 13). `6774471c5`: `noDups` is one pass; SPKI and PKCS #8 keys are at most 16 KiB. |
| F4 | Low | `KeyStore` | No byte bound: 65,536 keys of 64 MiB were allowed. | `6774471c5`: `maxStoreBytes`, 256 MiB a session (QuotaExceededError). |
| F6 | Low | `hacl_webcrypto.c` | Each failed ChaCha20-Poly1305 open leaked one Lean object (the empty array `l4w_refuse` answers). | `25da891bc`. The fuzzer's object count finds it: 71 leaked objects in 3,000 calls when the bug is put back. |
| F7 | Low (latent) | `HmacPre`, `ChaChaOpenPre`, and the C | Both preconditions were weaker than HACL*'s own: `keysized` (key_len + block < 2^32) and input_len + 16 ≤ max_size_t. No page could reach the gap, because arguments are at most 64 MiB. | `7e046a3a8`, in Lean and in the C. Audit rule 9 now checks each precondition. |
| F8 | Low | `readPkcs8`, ECPrivateKey | Any bytes were accepted after the private key, so one key had many encodings. | `6774471c5`: only `[0]` attributes, and in a v2 key a `[1]` public key, may follow. `#guard`s cover each case. |
| F10 | Low | `hostPlan` deriveBits (Hub) | ECDH with keys on different curves was left to the browser to refuse. | `487eca032`: Lean refuses it with InvalidAccessError, as natively. |
| F11 | Low | `qjs_wasmvm_entry.c` | The guest zeroed crypto argument and answer buffers with a `memset` just before `free`, a dead store that the compiler may remove. | `487eca032`: `zero_secret` calls `memset` through a volatile function pointer. |
| F14 | Low | prelude.js, haclweb section | A JWK's `oth` member was dropped, so a multi-prime RSA key was imported as two-prime, although Lean refuses `oth`. | `487eca032` (one line): the prelude now passes `j:oth` on. |
| F15 | Low | `jwkOfJson` (unwrapKey with format "jwk") | A JSON member given twice was read from its first occurrence, where JSON.parse and the IDL conversion take the last, so one wrapped key had two meanings. `oth` was dropped here too. | Committed with this record: the last member is taken (one pass over a hash set), and `oth` is kept so that Lean refuses it. `#guard`s cover both. |
| F5 | none | `dropKey` wiping | Checked in the generated C: the key's fields are taken and the key is erased before `wipe`, so the bytes are zeroed when the session's store is unshared. | — |
| F9 | none (functional) | QuickJS guest `n.api` | At most 64 arguments: an RSA private JWK with `key_ops` can exceed this and fail with OperationError, on QuickJS only. | Reported to haclweb. |
| F12 | Accepted | Lean intermediates | HMAC key blocks, PBKDF2 and HKDF intermediates, decrypted plaintexts, derived bits, and the `pending` answer are freed but not zeroed. They do not outlive Lean's allocator. This was already stated in the HACL* record (section 5). | — |
| F13 | Specification | unwrapKey, wrapKey, deriveKey | A key with `unwrapKey` can unwrap chosen bytes as an extractable key and read them: a decryption oracle. `wrapKey` is likewise an encryption oracle. `deriveKey` may make an extractable key from a non-extractable base key. WebCrypto defines all three. They are part of the declassification policy (section 5). | — |

**Logged at once:** the coordination log carries the "SECURITY:" lines for F1, F2 and F3.

### Attacks tried that the boundary held

These ran on both engines (`scratchpad/cryptosec/attack.ts`, through `native_html_engine.ts`):

- **Export:** `exportKey` raw and JWK of a non-extractable key give InvalidAccessError, and so
  does `wrapKey` of one.
- **Clones:** a `structuredClone` keeps `extractable: false` and the usages, and its export is
  refused too.
- **Inspection:** `JSON.stringify` of a CryptoKey is `{}`, it has no own properties, and
  `String` gives `[object CryptoKey]`.
- **Forgery:** a forged `Object.create(CryptoKey.prototype)` gives TypeError.
- **Mutation:** a mutated `key.algorithm` and a mutated `key.usages` array are ignored by
  Lean.
- **Algorithm confusion:** an ECDSA key used for ECDH, an HMAC key used for ECDSA, and verify
  with a private key each give InvalidAccessError.
- **Curve confusion:** a P-256 SPKI carrying the P-384 OID gives DataError.
- **base64url:** a non-canonical `d` (unused low bits set), a padded `d` and a `crv` mismatch
  each give DataError.
- **Nonces:** two ECDSA signatures of the same message have different r.
- **Frames:** postMessage between sessions carries JSON strings only (shadowframes), so no
  handle number crosses a session.
- **Hub host table:** numbers are never reused (`next` keeps growing across `clear()`).
- **Snapshots:** the BubblePopJS realm snapshot holds no crypto state, because `crypto` is
  installed lazily and the DRBG lives in `WebApi.State`.

## 3. The Secret type (WebHacl)

`Secret` is a **private** structure behind a definition that is made irreducible once the
wrappers are defined. This was checked in a separate module: outside `WebHacl.lean`, each of
the following fails to elaborate:

- the field;
- the anonymous constructor;
- `casesOn` (which a merely private constructor still allows);
- the projection `.1`;
- unfolding the definition.

`Secret` has no `Repr`, `ToString`, `BEq`, `Hashable` or `DecidableEq` instance, so no code
can print, log, compare or hash it.

Outside `WebHacl.lean`, code can do only these things with a secret:

- **make** one from bytes it has (`Secret.ofBytes`);
- **measure** it (`Secret.size`; lengths are public);
- **cut** it (`Secret.extract`);
- **give** it to a primitive (`Secret.hmac`, `hkdf`, `pbkdf2`, `ed25519Sign?`, `x25519?`,
  `p256Sign?`, `ecdsaSign?`, `p256Ecdh?`, `chachaSeal?`, `chachaOpen?`, `rsaPrivate?`,
  `rsaPssSign?`, and the public-key derivations);
- **reveal** it with `Secret.revealForExport`.

`revealForExport` is the one declassification point. Audit rule 12 checks that only
`WebCryptoKeys.exportBody` calls it, and `exportKey` reaches `exportBody` only for an
extractable key. The rule also refuses unsafe casts in the crypto files.

The fields changed as follows:

- `Key.material` became two fields: `Key.secret`, a `Secret`, and `Key.pub`, the public key
  as public bytes.
- RSA's `d`, `p`, `q`, `dp`, `dq` and `qi` are `Secret`s.

The theorems `Secret.hmac_eq`, `p256Sign?_eq` and `hkdf_eq` show that a secret adds no
behaviour, only the restriction on who may read it.

## 4. Handles

- **Given once.** A handle is given out once, and `next` only grows (`KeyStore.add_handle`,
  `add_fresh`, `add_wf`, `erase_wf`, with `KeyStore.Wf`).
- **Dropped handles.** A handle that was given out and has since been dropped is an
  **InvalidAccessError** (`keyOf_dropped`). A number never given out is a TypeError.
- **Cloning into another session.** `KeyStore.cloneInto` is the clone of a CryptoKey into
  another session's store. The copy's handle is the receiver's next one, whatever the sender's
  number was (`cloneInto_handle`), and it is the same key, never more extractable and never
  with more usages (`cloneInto_same`).
- **Cloning within a session.** `cloneKey` adds the same Lean key under a new handle; a
  `#guard` checks that a clone keeps `extractable: false` and that its export is refused.
- **Races.** The prelude's `later` holds an operation's CryptoKeys until its task runs
  (haclweb's fix). Host mode holds them in the callback's closure.

## 5. Noninterference and the declassification policy

`Key.SameButSecret k k'` holds when the two keys differ only in their secret bytes. With it:

- `sign_ni`, `verify_ni`, `crypt_ni` and `deriveBits_ni`: an operation whose usage the key
  lacks answers the same, error included, whatever the bytes are;
- `exportKey_ni` (and the earlier `exportKey_blind`, `exportOp_blind`): export of a
  non-extractable key answers the same whatever the bytes are.

**Declassification policy.** A key's secret bytes influence what the page sees only through
these routes:

1. **exportKey**, and wrapKey's export, of an extractable key. The answer is the bytes
   themselves.
2. **An operation with a usage the key has.** The answer is the primitive's output:
   - sign: the signature;
   - verify (HMAC): a boolean;
   - encrypt and decrypt: the ciphertext and the plaintext;
   - deriveBits and deriveKey: derived bits, or a key made from them;
   - wrapKey as the wrapping key: a ciphertext;
   - unwrapKey as the unwrapping key: a key made from the plaintext, which the page may ask to
     be extractable.

   A usage is therefore a grant of the corresponding oracle (F13).
3. **Lengths**, which are public. They are visible through timing and through `length` in an
   HMAC key's algorithm.

Constant time is HACL*'s throughout. Lean branches on no secret byte; the RFC 6979 code only
concatenates and cuts.

## 6. ECDSA nonces, Math.random, and fresh sessions

**Hedged RFC 6979.** `Secret.ecdsaSign?` uses RFC 6979 §3.2, with the HMAC of the
signature's own hash, the private key `x` and the message hash `h1`. Its additional data
(§3.6) is 32 bytes of the session's HMAC_DRBG.

- If the generator fails or repeats, signing degrades to deterministic RFC 6979: one
  message, one signature. It never uses one nonce for two messages, which would give `x`
  away.
- Lean does no arithmetic and no branch on a nonce. HACL*'s constant-time check decides
  whether a candidate is in [1, q-1]; if it is not, the next candidate follows step h.3.
- The `#guard`s check the deterministic `k` of RFC 6979 A.2.5, for "sample" and "test" with
  SHA-1, SHA-256, SHA-384 and SHA-512 (eight vectors), using the pure-Lean HMAC.
  `hmacFast_eq_pure` makes HACL*'s HMAC the same function, given `HmacAgrees`.
- `Secret.ecdsaSign?_eq` states that the signature is a function of the key, the hash and
  the 32 bytes alone. `rfc6979Go_size` bounds each candidate's size.
- A signature now draws 32 bytes, not 256.

**Fresh sessions.** All three engines start a session from `WebApi.State.fresh`.

- `State.fresh_clean`: a fresh state has no generator, no draws, no keys and no pending
  answer; handles start at 1 and work at 0.
- `randomBytes_fresh`: the first draw instantiates the generator from this session's
  entropy only.
- `LeanJS.Session.host_setHost`: at `start`, the realm's earlier host state is replaced.
- No DRBG state can come from a snapshot, a realm or another session. Math.random's seed is
  per session (F2), and a frame's entropy is its own (F1, once taken).

## 7. Algorithms and curves

- **The registered algorithm.** `op_algo_matches` and the usage theorems show that an
  operation ran on a key whose algorithm has the name the page gave. With
  `Alg.name_injective`, that name is one algorithm, and the branch taken is the key's own.
- **Curves.** ECDH checks the public key's curve, both natively and now in host mode.
- **SPKI curve OID.** `import_curve_matches_oid`: an EC SPKI is read only when its curve OID
  is the `namedCurve` asked for (`ecSpkiPoint`).
- **Point validation.** `decodePoint?_valid`: every imported EC point passed HACL*'s
  validation or HACL*'s decompression.

## 8. Encodings

- **DER and SPKI.** `readTlv_eq_tlv`, `expect_eq_tlv`, `readAlgId_eq` and `readSpki_eq`
  state canonical uniqueness: what the reader accepts is exactly what `tlv` and `spkiOf`
  write for what it read. With `readTlv_tlv`, the round trip, a key has exactly one SPKI
  encoding.
- **PKCS #8.** It is read strictly (F8).
- **base64url.** It is canonical: `JOSE.Base64Url.encode_decode` and the strict decoder.
- **JWK members.** A JWK is a JavaScript object, so it cannot repeat a member.

## 9. The C boundary, mechanically

`tools/hacl-web-glue-audit.py` gained four rules (9 to 12).

**Rule 9: HACL*'s preconditions.** A table lists 20 preconditions of the HACL* functions the
entry points reach. Each entry gives three things:

- where HACL* states the precondition: a phrase of the vendored Low* header, which the audit
  checks is still there, or the F* module (`Spec.Agile.HMAC.keysized`, `Hacl.Ed25519.sign`,
  `Hacl.AEAD.Chacha20Poly1305`, …);
- the conjunct of the Lean `…Pre` that implies it, so the kernel checks it at every call;
- the C guard that checks it again before the first HACL* call.

**Rule 10: no unchecked narrowing.** Every `(uint32_t)` cast of a length follows a check
against UINT32_MAX or a smaller bound. The only exceptions are names in `BOUNDED`, each with
the reason it is small.

**Rule 11: no kept pointers.** There is no file-scope or static pointer, so borrowed (`@&`)
arrays are read only during the call.

**Rule 12: who reads a secret.** This is the rule described in section 3.

**Mutation check.** Each of these faults was introduced and reported:

- a weakened `HmacPre`;
- a removed Ed25519 length check;
- a static pointer;
- `revealForExport` in sign.

Lean's emitted prototypes and the C signatures were already compared by rule 8 (haclweb).

## 10. Fuzzing the shim

`tests/crypto/run-fuzz.sh [ITERATIONS] [SEED]` builds `tests/crypto/hacl_webcrypto_fuzz.c`
with the shim, its core and the HACL* units, under `clang -fsanitize=address,undefined`.

**How it calls the entry points.** Every entry point is called with:

- arguments mostly of the size it takes;
- otherwise sizes at and around every length boundary, from 0 to 64 KiB, and up to 1 MiB;
- contents that are zero, 0xff, random, with a leading zero, odd, or with a SEC 1 prefix.

**How it checks.** Lean's runtime is not linked. The functions `lean.h` needs are defined
over `malloc`, so every Lean array is an ASan allocation with redzones. A count of live
objects stands in for the leak checker that macOS's ASan lacks. Each answer must be empty or
of a size the primitive writes, and each input must be unchanged.

**Results.** 3,000 calls (seed 1) and 4 × 50,000 calls (seeds 1-4) finished with no ASan or
UBSan report, no bad answer, no changed input and no leak. With F6 put back, the harness
reports 71 leaked objects in 3,000 calls.

## 11. The Hub (host mode)

- **No Lean-held bytes.** A host-mode key holds no Lean bytes: its secret is empty, it has no
  RSA parts, and it names the host's key (`hostKey_no_secret`, through `hostKeyOf?`).
- **Requests.** A host request is built from three things:
  - the page's own arguments;
  - key attributes;
  - host numbers.

  The store of a host-mode session has no secret to put in a request, because every key in it
  is a `hostKey` or a `cloneKey` copy of one.
- **Lean decides first.** Lean still makes every decision before the browser runs the
  primitive, including the P-256 point check and, now, the ECDH curve check.

## 12. What the page can still learn, by design

- the length of every key (through timing, and HMAC's `length`);
- whether a random P-256 candidate was rejected (probability below 2^-32);
- everything F13 grants.

## 13. Work: every call bounded and charged

`WebApi.opWork` is an upper bound on a call's work, decided from its arguments and the
session's keys before the call runs. The unit is one compression of a hash block by HACL*,
about 0.27 µs natively: PBKDF2-SHA-256 at 2,000,000 iterations is 8,000,000 units and took
2.2 s.

**What it counts:**

- hashes and HMACs, including long keys;
- HKDF;
- PBKDF2, as iterations × blocks;
- the DRBG;
- P-256, Ed25519 and X25519 operations;
- RSA, cubic in the modulus for a private operation;
- ChaCha20-Poly1305.

**Refusal.** `runCharged` refuses a call above `maxOpWork` (2^24 units) with -5, which is
OperationError in crypto.subtle; nothing runs.

**Charging.** Below the bound, the call's work goes into `State.work`, and
`Page.serveExtra` charges it to script time at 27 instructions a unit, as page WebAssembly
is charged. The fuel of the run is not reduced, so a long legitimate operation does not end
its task.

**Theorems:**

- `runCharged_refuses`;
- `runCharged_work`: a call is charged exactly its work, at most `maxOpWork`;
- `hmacWork_ge`;
- `deriveWork_pbkdf2`: PBKDF2 is charged at least four compressions per iteration per
  block.

`#guard`s check that PBKDF2 at 2^32 - 1 iterations and an HMAC key of 2^32 - 1 bits are
refused, and that 600,000 iterations are charged within the bound.

## 14. Theorems added

See the hand-back for file and line. In summary:

- **WebHacl:** the `Secret.*` lemmas, `Secret.ecdsaSign?_eq`, `rfc6979Go_size`, and the RFC
  6979 `#guard`s.
- **WebCryptoKeys:**
  - DER and SPKI uniqueness;
  - handles and clones;
  - noninterference;
  - algorithms;
  - `import_curve_matches_oid`;
  - `decodePoint?_valid`.
- **WebApi:**
  - `mathRandomSeed_ne_zero`;
  - `State.fresh_clean`;
  - `randomBytes_fresh`;
  - `runCharged_refuses`, `runCharged_work`;
  - `hmacWork_ge`, `deriveWork_pbkdf2`;
  - `hostKey_no_secret`.
- **LeanJS:** `Session.host_setHost`.

There is no new `partial def`, `sorry` or `axiom`.

## 15. The remaining TCB, precisely

1. **HACL\*'s C** for the units the shim calls: memory safety, functional correctness and
   secret independence, as proved in F* for the extracted C. Its preconditions are restated in
   Lean, and the audit ties each to a C guard. The agreement hypotheses `HashAgrees`,
   `HmacAgrees` and `CtEqAgrees` are tested by the KAT, not proved.
2. **The C compiler**, for keeping HACL*'s constant-time C constant-time and keeping the
   volatile zeroing.
3. **`hacl_webcrypto.c` and `hacl_webcrypto_core.c`**, 470 lines. They are checked by audit
   rules 1-11 and by the sanitizer fuzzer, not proved.
4. **Lean's compiler and runtime:**
   - the erasure of preconditions;
   - reference counting, on which `wipe` relies when it checks exclusivity;
   - the privacy of `Secret`, which unsafe code could break (audit rule 12).
5. **The entropy sources:** `IO.getRandomBytes` (the operating system, or the browser under
   Emscripten), 32 bytes per session and per frame.
6. **The two script engines**, which keep page JavaScript from the prelude's closures. Lean
   enforces every rule even if an engine fails.
7. **On the Hub:** the browser's own crypto.subtle and the worker's `crypto-host.mjs` table.
   WebAssembly linear memory is readable by the embedding page.
8. **What is not covered:**
   - zeroing of Lean intermediates (F12);
   - side channels of the machine (caches, speculation) beyond HACL*'s model.

## 16. For the owner

1. **F1 must land with shadowframes.** The fix is ready as `wip/cryptosec-frames`.
2. **Should crypto.subtle refuse work above about 4.5 s natively?** That is 2^24 units, and
   lets PBKDF2-SHA-256 run up to about 4.19 million iterations. Chrome has no such cap and
   runs crypto off the main thread. The alternative is a crypto worker thread in the engine.
3. **Are 256 MiB of keys enough for a session**, and 16 KiB for an SPKI or PKCS #8 key?
4. **Should unwrapKey refuse to make an extractable key** from a non-extractable unwrapping
   key? It would be stricter than the specification (F13), and would break pages that rely
   on the specified behaviour.
