# Vendored HACL\* extracted C — provenance

This directory contains a **minimal, curated subset** of the C code
extracted by [KaRaMeL](https://github.com/FStarLang/karamel) from the
[HACL\*](https://github.com/hacl-star/hacl-star) formally-verified
cryptographic library (Project Everest, written in F\*/Low\*). It
realises the Ed25519 and SHA-256 `assume val`s used by Factoidal's
Verifiable Credentials Data Integrity pipeline (`VC.DataIntegrity.fst`)
via the vendored-C route (adoption-order option 2 of
`skills/crypto-policy/SKILL.md`).

## Why vendored HACL\*

Per the owner directives recorded in `skills/crypto-policy/SKILL.md`
("Dont roll our own crypto!", "pursue HACL\*") this project never
implements a digest / curve / signature / RNG primitive itself. HACL\*
is the F\*/Low\*-verified library whose extracted C Mozilla ships inside
NSS — the only crypto source matching this project's own
"specs-not-assertions" standard, and literally written in the same
language. Ed25519 sign+verify has **no** acceptable pure-OCaml/F\*
fallback (the crypto-policy skill permits a pure-OCaml DIGEST fallback
for the wasm target only — never a hand-rolled SIGNATURE).

## Source

| Field | Value |
|---|---|
| Upstream repo | `cryspen/hacl-packages` (the maintained packaging home of the HACL\* OCaml/C distribution) |
| Clone URL | https://github.com/cryspen/hacl-packages.git |
| Commit | `05c3d8fb321ed65e3db3a6a8b853019e86fb40a2` (2024-09-30) |
| Extraction | Upstream `src/` + `include/` (already KaRaMeL-extracted C dist) |
| License | Apache-2.0 (see `LICENSE-APACHE`); HACL\* is dual Apache-2.0 / MIT |

## Files vendored (curated transitive closure)

Determined by taking the `#include` closure of the three C translation
units below; unrelated primitives (Blake2, HPKE, P-256, MD5, SHA-1,
SHA-3, vectorized variants, EverCrypt agile layer) were **not**
vendored.

C sources (`src/`):
- `Hacl_Ed25519.c` — Ed25519 `sign` / `verify` / `secret_to_public`
- `Hacl_Curve25519_51.c` — field arithmetic Ed25519 depends on
- `Hacl_Hash_SHA2.c` — SHA-256 (and SHA-512, used internally by Ed25519)

Headers (`include/`, `include/internal/`, `include/krml/`): the 26
public + internal HACL\* headers and the KaRaMeL runtime headers those
three units transitively require.

### JOSE addition, 2026-09-06 — P-256 and the bignum field

Added for the Solid-OIDC / JOSE token layer (`formal/lean4/L4Factoidal/
JOSE/`, design record `docs/designissues/2026-09-06-jose-dpop-over-hacl.md`):
JWS `ES256` needs ECDSA over NIST P-256, and JWS `RS256` needs the RSA
PUBLIC operation `s^e mod n`. Both come from the SAME pinned commit as
the files above; nothing was taken from a different release.

`Hacl_Bignum4096.c` was NOT vendored. The generic 64-bit field
(`Hacl_Bignum64.c`, over `Hacl_Bignum.c`) takes the limb count at run
time, so one translation unit serves 2048-, 3072- and 4096-bit moduli,
where `Hacl_Bignum4096.c` serves only the largest. Fewer files, one
code path, same verified arithmetic.

| Path | SHA-256 |
|---|---|
| `src/Hacl_P256.c` | `876b7bcc7824e2dae453466e782275e369f0ac561af8f769577e215ae715dae1` |
| `src/Hacl_Bignum64.c` | `a6b5f901bd08bd0317edb89c899e387e26baca3dfbadc3a4d4116dd30d81e04e` |
| `src/Hacl_Bignum.c` | `1648d0c094b52bd9c7a0aad74a38e8709ce68fb705d1604a9c58fbca7c5230d4` |
| `include/Hacl_P256.h` | `6d0114e328b20bad0866eb27949c18927bbbdd026b2449584307dedde63e83d2` |
| `include/Hacl_Bignum64.h` | `661a747cba13a7728ad52c6bd78f2fd8abe8dfce971d3716521856b7f369d882` |
| `include/Hacl_Bignum.h` | `cfd8124251d693be57b55d604eb466f687edf80b8c5abe49e4807bc61d5e562b` |
| `include/internal/Hacl_P256.h` | `379829b1d137348fb2ae1649db7a6457a9aea1bbab3e0dd47e35fca964a13e8b` |
| `include/internal/Hacl_P256_PrecompTable.h` | `33a88a31a8d43bfe0906ac4a28e49038dc43f16d0f9e0cd53b18b4a8d8be0aed` |
| `include/internal/Hacl_Bignum.h` | `d1413655685a20fda4368bd4f006d65595b7407f6b845ca666843e312d42505a` |

Reproduce: `git clone https://github.com/cryspen/hacl-packages.git`,
`git checkout 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`, then
`shasum -a 256` the same nine paths under `src/` and `include/`. The
three headers those units also need — `include/internal/Hacl_Bignum_Base.h`,
`include/Hacl_Krmllib.h`, `include/internal/Hacl_Krmllib.h` — were
already vendored for Ed25519 and were checked byte-identical to the same
commit when the P-256 files were added.

Still NOT vendored, AS OF THIS 2026-09-06 SECTION: Blake2, HPKE, MD5,
SHA-1, SHA-3, the vectorized variants, the EverCrypt agile layer, and every
fixed-width bignum (`Hacl_Bignum256*`, `Hacl_Bignum4096*`, `Hacl_Bignum32`).
SUPERSEDED IN PART by the 2026-09-07 section below, which adds HPKE, SHA-1
and both BLAKE2 units. MD5, SHA-3, the vectorized variants, the EverCrypt
agile layer and the fixed-width bignums remain not vendored.

### XMPP client-role and end-to-end encryption addition, 2026-09-07 — AEAD, KDF and HPKE

Added for the XMPP client role and group end-to-end encryption
(design record `docs/designissues/2026-09-07-attestation-and-adversarial-
server.md` section 6, and `docs/designissues/2026-09-07-crypto-primitives.md`):
OMEMO and MLS need an AEAD, a key-derivation function and a hybrid public-key
encryption scheme. All files below come from the SAME pinned commit
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2` as everything above; nothing was
taken from a different release. The previously vendored headers those units
also need were re-checked byte-identical to that commit while these were
added.

Upstream names differ from the older HACL* releases some documentation
quotes. In this release the ChaCha20-Poly1305 AEAD unit is
`Hacl_AEAD_Chacha20Poly1305.c` (not `Hacl_Chacha20Poly1305_32.c`) and the
Poly1305 MAC is `Hacl_MAC_Poly1305.c` (not `Hacl_Poly1305_32.c`). The
portable scalar variants were taken; `Hacl_AEAD_Chacha20Poly1305_Simd128.c`,
`_Simd256.c`, `Hacl_Chacha20_Vec128.c` and `Hacl_Chacha20_Vec256.c` were NOT
vendored, because they need `libintvector.h` and target intrinsics that
neither wasm32 nor a plain arm64 build has.

`Hacl_HMAC.c` is one translation unit covering every HMAC hash, so linking it
for HMAC-SHA-256 pulls in its SHA-1 and BLAKE2 call targets. That is why
`Hacl_Hash_SHA1.c`, `Hacl_Hash_Blake2s.c` and `Hacl_Hash_Blake2b.c` appear
here after the note above says BLAKE2 and SHA-1 are not vendored: they are
now, as link-closure of HMAC, and no Lean code calls them.

`Lib_Memzero0.c` realises the secret-erasure helper the BLAKE2 units call.

#### AES-GCM: NOT VENDORED in this 2026-09-07 landing, and why (SUPERSEDED 2026-10-27, see the AES-GCM section below)

OMEMO 0.8 uses AES-128-GCM, so AES-GCM was in scope for this landing. The
pinned release has NO PORTABLE AES-GCM. Its only AES-GCM is reached through
`src/EverCrypt_AEAD.c`, whose every AES-GCM branch is inside
`#if HACL_CAN_COMPILE_VALE` and calls Vale x86-64 assembly
(AES-NI plus PCLMULQDQ) that is not part of the C distribution; with Vale
absent, those entry points return `EverCrypt_Error_UnsupportedAlgorithm`.
`include/Hacl_AES128.h` declares `Hacl_AES128_*` symbols but the release
ships no C definition of them. There is no bitsliced constant-time AES in
this release.

Taking the AES-NI variant was refused: it does not build for wasm32 and does
not build on arm64 without intrinsics, so it would break the crypto policy's
wasm compatibility gate. Per the shortfall rule the gap carries an open issue
(https://github.com/danbri/factoidal/issues/677) and an expected-failure case in `lake exe l4crypto-probe`
(section `aes-gcm`), which reports the Wycheproof `aes_gcm_test.json` corpus
as NOT RUN rather than as passing.

| Path | SHA-256 |
|---|---|
| `include/Hacl_AEAD_Chacha20Poly1305.h` | `8abdf6d0130788df3a07af8a2ac11b580f95654ef5a6385f1b8f77de8e78c946` |
| `include/Hacl_Chacha20.h` | `05e28e4afc214055e538bf3617cdf51d512090992153eafddfa4222bf4efa1ca` |
| `include/Hacl_HKDF.h` | `2fa6f4faf9f602c6d89cb5582470b1e00e6580136b51968275dc7b9b9c18b6ac` |
| `include/Hacl_HMAC.h` | `18899e59f8c55204a35dd5679725fc53a01ab90202ca68062bca381b5881c090` |
| `include/Hacl_HPKE_Curve51_CP32_SHA256.h` | `53c09230960abaac6dfab617d504c81b7c02cad18055af8f7d044508eb253b2b` |
| `include/Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE.h` | `490199f10295e605275a88d9e0ee83e1eb4f8714e2149c22018056df0374da30` |
| `include/Hacl_Hash_Blake2b.h` | `b16479b50de26c0ada001c79597a0500682c83a181446fa8db65c8a50754245b` |
| `include/Hacl_Hash_Blake2s.h` | `e6645ecd3c286fdc9534bde22c25a1bbdf6bb1135c6d401e28b32fecdf8e31d2` |
| `include/Hacl_Hash_SHA1.h` | `f993ee91b245227cca8658e203276e13c35f6dc0a0f88e5d7126e4958ef7dc3d` |
| `include/Hacl_MAC_Poly1305.h` | `83b2361f2faaf884de9e9e199ba39985b7f270c52dd49a55796b9635a6ca961c` |
| `include/internal/Hacl_Chacha20.h` | `0a6593e95d34524f1729edc0757fa1f8ee8db538a94714782cd99066706d4574` |
| `include/internal/Hacl_HMAC.h` | `d453aed90691b35d12485cf8aa08f54e23a627585a7319541ae52d296e5a97cc` |
| `include/internal/Hacl_Hash_Blake2b.h` | `0938dd6c5689e82d4d9e129335b78b22c4d6baaf8f28965878140d0eea035e7d` |
| `include/internal/Hacl_Hash_Blake2s.h` | `2c61d4e9447b7dda7909d7f0f0779babe36a7000150a31edc52abb74281f96d2` |
| `include/internal/Hacl_Hash_SHA1.h` | `9473d8bc9506fe0053d7d98c225d4873011329863f1c4a8e93e43fc71bd1f314` |
| `include/internal/Hacl_Impl_Blake2_Constants.h` | `d8354a9b75e2470085fa7e538493130e81fa23a804a6a69d34da8fdcc941c038` |
| `include/internal/Hacl_MAC_Poly1305.h` | `77e4712ea5856ae1f67b8deb0388a52a36841ad6ecba7153be78112f0af87010` |
| `include/lib_memzero0.h` | `0f8d744620cf5f6b8450da187484b418d24dec7d8cf72b757b7080e84cb3ae5e` |
| `src/Hacl_AEAD_Chacha20Poly1305.c` | `e4cc1453264166316d65f0ed3ff8f9ec338e97b9cdce1574a586d904fefeccf1` |
| `src/Hacl_Chacha20.c` | `c9ecf4df617745715eb0dce89c9b92c8e24e35368a01fa25225d9b8736b6cd1e` |
| `src/Hacl_HKDF.c` | `fcde5b78de8f51a1d2cc132b3f4d6b59682e1793440e4776917cbd154aa62557` |
| `src/Hacl_HMAC.c` | `028e991ab4025e20b14da4859150af3f080d48043be4d9489c1500f8a41cf329` |
| `src/Hacl_HPKE_Curve51_CP32_SHA256.c` | `5159235aece13c44ce19836b549bf28755a3647530397016f1fd05661500e2a8` |
| `src/Hacl_Hash_Blake2b.c` | `83b2be067d7d48c31b32094ce38001bd05431d98ffecfb405c2b5b47d0fd31bf` |
| `src/Hacl_Hash_Blake2s.c` | `44b21ce13b2d14c7e12a5b0205741f1d351ba0997df3f1b980eada976187c36c` |
| `src/Hacl_Hash_SHA1.c` | `5b29bd9951646861e0e19427be5d923a5bab7a4516824ccc068f696469195eec` |
| `src/Hacl_MAC_Poly1305.c` | `a154a51bc6c70e523741a9650f474c4d4031ee71a437f6b221faac0b3a4d6ac4` |
| `src/Lib_Memzero0.c` | `c4424a4851cd2d4f27633ca19faf5cb1135a680443727a8d1b134737f9a71e62` |

Reproduce exactly as above: clone `cryspen/hacl-packages`, check out
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`, then `shasum -a 256` the same
paths under `src/` and `include/`.

### AES-GCM on x86-64, 2026-10-27 — EverCrypt AEAD over Vale assembly

For https://github.com/danbri/factoidal/issues/677 (AES-GCM) and the XML
Encryption 1.1 and JWE work of https://github.com/danbri/factoidal/issues/1081.
Owner, 2026-10-27, verbatim: "Ok for now: “My proposal is HACL* Vale on x86-64
and a refusal on other CPU”". This replaces the refusal of the AES-NI path in
the 2026-09-07 section above for NATIVE x86-64 executables only. The wasm
module and every other CPU still have no AES-GCM; on JavaScript hosts AES is
WebCrypto (`skills/crypto-policy/SKILL.md`, "AES through WebCrypto").

All files come from the SAME pinned commit
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`; there is no second pin. They are:

- `src/EverCrypt_AEAD.c` — the only AES-GCM in the release. Every AES-GCM
  branch is inside `#if HACL_CAN_COMPILE_VALE` and calls the Vale assembly.
- `src/EverCrypt_AutoConfig2.c` — the CPU feature test (`check_*` from the
  Vale `cpuid` assembly). `EverCrypt_AEAD_create_in` takes the Vale path only
  when AES-NI, PCLMULQDQ, AVX, SSE and MOVBE are all present.
- `src/EverCrypt_Chacha20Poly1305.c` — LINK CLOSURE of `EverCrypt_AEAD.c`,
  whose ChaCha20-Poly1305 branch calls it. With `HACL_CAN_COMPILE_VEC128` and
  `VEC256` undefined it calls only the portable `Hacl_AEAD_Chacha20Poly1305`
  unit already vendored; no Lean code reaches it. Its header needs the four
  Simd/Vec HEADERS below (declarations only); their `.c` units are not
  vendored.
- `vale/src/aesgcm-x86_64-linux.S`, `vale/src/aesgcm-x86_64-darwin.S` — Vale
  AES-GCM (key expansion, GHASH key init, `gcm128/256_encrypt_opt`,
  `gcm128/256_decrypt_opt`, `compute_iv_stdcall`).
- `vale/src/cpuid-x86_64-linux.S`, `vale/src/cpuid-x86_64-darwin.S` — the
  `check_*` CPU feature functions.
- Headers: `EverCrypt_AEAD.h`, `EverCrypt_AutoConfig2.h`,
  `EverCrypt_Chacha20Poly1305.h`, `EverCrypt_Error.h`, `Hacl_Spec.h`,
  `internal/Hacl_Spec.h`, `internal/Vale.h`, `evercrypt_targetconfig.h`,
  `Hacl_AEAD_Chacha20Poly1305_Simd128.h`, `Hacl_AEAD_Chacha20Poly1305_Simd256.h`,
  `Hacl_Chacha20_Vec128.h`, `Hacl_Chacha20_Vec256.h`.

Not vendored: the `-mingw.S`, `-msvc.asm` and `ppc64le.S` variants, and every
other Vale routine (Curve25519, Poly1305, SHA-256 assembly).

`config.h`: upstream generates it with CMake from `config/Config.h.in`. It is
not a vendored file. `formal/lean4/ffi/hacl_vale_config/config.h` is that
template filled in by hand: `HACL_CAN_COMPILE_VALE` 1 on x86-64 Linux and macOS
only, `TARGET_ARCHITECTURE` X64 there, no VEC128/VEC256.

The headers already vendored for the earlier sections were re-checked
byte-identical to the pinned commit when these files were added (every
`include/` and `src/` file present upstream compared with `cmp`).

| Path | SHA-256 |
|---|---|
| `src/EverCrypt_AEAD.c` | `6e7a5b17c7d987d6365246f0a1a5a415311735ae4658bf6ef3d3ce7f11d85eab` |
| `src/EverCrypt_AutoConfig2.c` | `2f784868ca0d61358759264a80c4639782627eeeb3a92116a8b59a415ff0c1b8` |
| `src/EverCrypt_Chacha20Poly1305.c` | `5e928fa0c83d894d331685baabbc21db481662e6b59d2d3ee518fb58bd484992` |
| `include/EverCrypt_AEAD.h` | `c76c6ab0fb833b893f3d0a888db62ca981b93c22d9f4eb8c265d9e5b4ba33101` |
| `include/EverCrypt_AutoConfig2.h` | `4828c851a791e37516a5c873f1ecf6542f0321df2ad679bed2606e0905675b2a` |
| `include/EverCrypt_Chacha20Poly1305.h` | `8f330a46f68b7c37e7e3b243de7a4794031855c227413261d65911192efd6c4e` |
| `include/EverCrypt_Error.h` | `072448a64588451bb191f0f71d45a7cd4a89ae7f042d802cadd37a72841876b1` |
| `include/Hacl_Spec.h` | `95c48b70eee64853adc266844f1da80829946f27c3b14aa450cff17371012b65` |
| `include/internal/Hacl_Spec.h` | `f4fbdaed2c9cea8f173757c58a84f56940b32af3ff45107ee9e6f3b8b05e359a` |
| `include/internal/Vale.h` | `74d410865e312042fe39f0b219928d64aa9d6b586d1b20dfa4c86ea50ffc59e0` |
| `include/evercrypt_targetconfig.h` | `5e2e94e02f758d7a399d58c92cd825332f266576b994f25719fa7c32ef95791b` |
| `include/Hacl_AEAD_Chacha20Poly1305_Simd128.h` | `e32d7e4c612fd65ff3970505b25d53abfcb849db72e63f384da85c22ffefecc2` |
| `include/Hacl_AEAD_Chacha20Poly1305_Simd256.h` | `190b55c32fd2b553ef9944b9a46b4895b7a527d3e24e4252a59813d2508d053d` |
| `include/Hacl_Chacha20_Vec128.h` | `b4a136eadc2f3009b3b95c8ac6317da156620c3aede9c9e8d1dc9d21ea104355` |
| `include/Hacl_Chacha20_Vec256.h` | `4c739289bd2838efdd686d669ad7b8de2d2237104073b9b38038ef21f1061665` |
| `vale/src/aesgcm-x86_64-linux.S` | `a378526daf7950127997c31a1c84fcfdf7e8efd990459a16594b4b54adb422ef` |
| `vale/src/aesgcm-x86_64-darwin.S` | `08ca8c174eefa6bc4804b5c9b0664ecd4f426da67d0b651587959ed4b95a5094` |
| `vale/src/cpuid-x86_64-linux.S` | `55c2b093ab90fc8385ccc63320f78c8832983f269fdff111c44c4263fd47c872` |
| `vale/src/cpuid-x86_64-darwin.S` | `427ccb7142944dc2918017c6749d715da559d96f39822dba36f033fd3b7cf2a3` |

Reproduce: clone `cryspen/hacl-packages`, check out
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`, then `sha256sum` the same paths
(the `.S` files are under `vale/src/` upstream and here). `SHA256SUMS` in this
directory lists them too (`sha256sum -c SHA256SUMS`).

## How it is wired in — Lean 4 tree (`formal/lean4/`)

- `ffi/hacl_ed25519.c` — Ed25519 and SHA-256 (`@[extern]` of
  `L4Factoidal/Crypto/Ed25519.lean`, `Crypto/SHA2Native.lean`).
- `ffi/hacl_p256.c` — P-256 ECDSA verification and public-key validity
  (`Crypto/P256Native.lean`). Two length checks and one pointer offset:
  the JWS `r || s` signature split.
- `ffi/hacl_rsa.c` — the RSA public operation only (`Crypto/RsaNative.lean`).
  No private operation, no padding logic; EMSA-PKCS1-v1_5 lives in
  `L4Factoidal/JOSE/Pkcs1.lean` in pure Lean, with theorems.
- `lakefile.lean`, `extern_lib libl4hacl` — compiles the six HACL\*
  translation units and the three shims into `libl4hacl.a`.
- `ffi/hacl_aesgcm.c` — AES-128-GCM and AES-256-GCM (`Crypto/AesGcmNative.lean`)
  through `EverCrypt_AEAD`. On an x86-64 Linux or macOS host the lakefile
  (`valeHost`) also links the three EverCrypt units and assembles the Vale
  `aesgcm` and `cpuid` `.S` files for the host OS. On every other host the
  shim compiles to stubs that refuse.
- `Wasm/build-wasm.sh` compiles the stub form of `ffi/hacl_aesgcm.c` only; it
  assembles no `.S` file and compiles no EverCrypt unit.
- `Wasm/build-wasm.sh` — the same six units and three shims, compiled for
  wasm32 by Emscripten. Crypto policy: every target links the same HACL\*.

## How it is wired in — F\* tree (`formal/fstar/`)

- `formal/fstar/experimental_ocaml_glue/hacl_stubs.c` — hand-written
  OCaml <-> C FFI (`CAMLprim`), hex-string boundary (same shape as
  `parquet_zstd_stubs.c`). No crypto logic — pure marshalling around
  the vendored `Hacl_*` calls.
- `formal/fstar/ocaml-output/fstar_hacl_crypto.ml` — the `external`
  declarations + thin hex wrappers that realise the F\* `assume val`s.
- `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`
  `286_vc_hacl_ed25519_sha256_stubs.sh` — the stub patch that rewrites
  the extracted `failwith` bodies to call the above.

## Updating

Re-run the curation: shallow-clone the pinned commit, copy the three
`src/*.c`, then keep only the transitive `#include` closure of headers.
Reverify with a driver that checks `Hacl_Hash_SHA2_hash_256("abc")`
begins `ba78...` and an Ed25519 sign/verify roundtrip returns true.
Never hand-edit the vendored `Hacl_*` C — it is extracted output.
