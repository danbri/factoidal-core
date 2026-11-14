# Vendored HACL\* extracted C — provenance

This directory holds a **minimal, curated subset** of the C code that
[KaRaMeL](https://github.com/FStarLang/karamel) extracts from the
[HACL\*](https://github.com/hacl-star/hacl-star) verified cryptographic
library (Project Everest, F\*/Low\*, with Vale assembly for AES-GCM on
x86-64). Every file is an unmodified copy of an upstream file; nothing here
is hand-edited. Policy: `skills/crypto-policy/SKILL.md` (never our own crypto
primitives; HACL\*) and `skills/aes-hardware-only/SKILL.md` (AES only as Vale
assembly on the CPU's AES instructions).

## Source

| Field | Value |
|---|---|
| Upstream repository | `hacl-star/hacl-star`, https://github.com/hacl-star/hacl-star.git |
| Commit | `f557259007db9933442dde10aa995c1b00bd3446` (main, committed 2026-10-29) |
| Last change to `dist/` at that commit | `2c323da84927d7342547dc981152af7b3fca7933` (2026-10-27) |
| Distribution | `dist/gcc-compatible/` (HACL\* and EverCrypt C, Vale `.S`), `dist/karamel/include/` and `dist/karamel/krmllib/dist/minimal/` (KaRaMeL runtime headers) |
| Toolchain (`dist/gcc-compatible/INFO.txt`) | F\* 2026.03.24~dev, KaRaMeL `bd2d4fa8a61344042c7cd7a31013d72bfe4568ce`, Vale 0.3.19 |
| Licences | `LICENSE-MIT` is `dist/LICENSE.txt` (MIT, the licence the C files carry in their headers); `LICENSE-APACHE` is the repository's `LICENSE` (Apache-2.0). HACL\* is dual-licensed Apache-2.0 / MIT. Both are permissive. |
| Checksums | `SHA256SUMS` lists every vendored file (`shasum -a 256 -c SHA256SUMS`) |

### Why this repository, this commit and this flavour

Until 2026-11-14 the source was `cryspen/hacl-packages` at
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2` (2024-09-30). That commit is the
newest commit of `cryspen/hacl-packages` (checked with `git ls-remote` on
2026-11-14): the repository no longer moves. It was a repackaging of
hacl-star's `dist/`. Its `info.txt` names HACL\* `ae5d839c2e1fa95055b618cda60aeb1c486c720c`,
and 76 of the 91 files vendored here at that time were byte-identical to
`dist/gcc-compatible` (or `dist/karamel`) of that hacl-star commit. Only 17
matched `dist/portable-gcc-compatible`, which differs from
`dist/gcc-compatible` only by `SNIPPET_START`/`SNIPPET_END` documentation
comments, and 69 matched `dist/msvc-compatible`. The other 15 were
hacl-packages' own regenerations: Ed25519 doc comments, BLAKE2 and SHA-3
units, a `Lib_Memzero0_memzero` macro arity, and a newer krmllib
`fstar_uint128_msvc.h`. So `dist/gcc-compatible` is the flavour we vendored,
and the one taken here.

hacl-star `main` regenerates `dist/` itself. At this commit it holds about
318 commits made since 2024-09-30. Among them are soundness fixes to admitted
group-law lemmas of P-256, Ed25519 and K-256 (hacl-star PRs 1080 and 1081). Those
fixes change proofs: the extracted C of `Hacl_P256.c` and `Hacl_Ed25519.c`
changes only in code generation and control-flow layout (see the design record).

### Path mapping (upstream → here)

| Upstream (at the commit) | Here |
|---|---|
| `dist/gcc-compatible/<name>.c` | `src/<name>.c` |
| `dist/gcc-compatible/<name>.h` | `include/<name>.h` |
| `dist/gcc-compatible/internal/<name>.h` | `include/internal/<name>.h` |
| `dist/gcc-compatible/{aesgcm,cpuid}-x86_64-{linux,darwin}.S` | `vale/src/` (same names) |
| `dist/karamel/include/krml/...` | `include/krml/...` |
| `dist/karamel/krmllib/dist/minimal/<name>.h` | `include/<name>.h` |
| `dist/LICENSE.txt` | `LICENSE-MIT` |
| `LICENSE` | `LICENSE-APACHE` |

## What is vendored (the curation)

The same primitives as before this re-pin; no new primitive was added.

| Primitive (consumer) | Translation units |
|---|---|
| Ed25519 (`Crypto/Ed25519.lean`, VC Data Integrity, did:key) | `Hacl_Ed25519.c`, `Hacl_Curve25519_51.c` (field arithmetic), `Hacl_Hash_SHA2.c` (SHA-512) |
| SHA-1, SHA-2 (`Crypto/SHA2Native.lean`, `Crypto/WebHacl.lean`) | `Hacl_Hash_SHA1.c`, `Hacl_Hash_SHA2.c` |
| SHA-3, SHAKE (`Crypto/WebHacl.lean`, crypto.subtle digest) | `Hacl_Hash_SHA3.c` (portable scalar unit) |
| ECDSA and ECDH P-256 (`Crypto/P256Native.lean`, JOSE ES256, ECDH-ES) | `Hacl_P256.c` |
| RSA: the public operation, the constant-time private operation, RSA-PSS (`Crypto/RsaNative.lean`, `Crypto/RsaOaep.lean`, crypto.subtle) | `Hacl_Bignum64.c`, `Hacl_Bignum.c`, `Hacl_RSAPSS.c` |
| ChaCha20-Poly1305 (`Crypto/ChaChaPoly.lean`) | `Hacl_AEAD_Chacha20Poly1305.c`, `Hacl_Chacha20.c`, `Hacl_MAC_Poly1305.c` (portable scalar units) |
| HMAC, HKDF (`Crypto/Hkdf.lean`) | `Hacl_HMAC.c`, `Hacl_HKDF.c` |
| X25519 (`Crypto/X25519.lean`) | `Hacl_Curve25519_51.c` |
| HPKE base mode, DHKEM(X25519, HKDF-SHA256), ChaCha20-Poly1305 (`Crypto/Hpke.lean`) | `Hacl_HPKE_Curve51_CP32_SHA256.c` |
| AES-128-GCM, AES-256-GCM, native x86-64 Linux and macOS only (`Crypto/AesGcmNative.lean`) | `EverCrypt_AEAD.c`, `EverCrypt_AutoConfig2.c`, `EverCrypt_Chacha20Poly1305.c`, `vale/src/aesgcm-x86_64-{linux,darwin}.S`, `vale/src/cpuid-x86_64-{linux,darwin}.S` |

**Link closure.** `Hacl_HMAC.c` is one translation unit for every HMAC hash,
so linking it for HMAC-SHA-256 also needs the units of its other hashes. At
this commit those are SHA-1, SHA-2, SHA-3, BLAKE2s, BLAKE2b and **MD5**. So
`Hacl_Hash_Blake2s.c`, `Hacl_Hash_Blake2b.c` and `Hacl_Hash_MD5.c` are
vendored, with `Lib_Memzero0.c` (secret erasure, called by BLAKE2), although no
Lean code calls BLAKE2 or MD5. `Hacl_Hash_MD5.c` is new with this re-pin: the
hacl-star `Hacl_HMAC.c` added HMAC-MD5 and HMAC-SHA-3. MD5 is broken for
collision resistance. Here it is link closure only, with no extern and no Lean
caller. `EverCrypt_Chacha20Poly1305.c` is link closure of `EverCrypt_AEAD.c`.
With `HACL_CAN_COMPILE_VEC128/256` off it calls only the portable
`Hacl_AEAD_Chacha20Poly1305`.

**Headers.** They are the transitive `#include` closure of the units above and
of the shims in `formal/lean4/ffi/hacl_*.c`, and nothing more. Compared with
the previous pin, the closure gained `internal/Hacl_Streaming_Types.h` (the
streaming state structs moved out of the public header),
`internal/EverCrypt_AEAD.h` (the AEAD state struct moved out of the `.c`),
`Hacl_Hash_MD5.h` and `internal/Hacl_Hash_MD5.h` (HMAC-MD5), and
`libintvector.h`, which `internal/Vale.h` now includes. With
`HACL_CAN_COMPILE_VEC128/256` undefined it declares one macro and includes
no intrinsics header. The closure lost `Hacl_Chacha20_Vec128.h` and
`Hacl_Chacha20_Vec256.h`: the AEAD headers no longer include them, so they
were removed.

**Not vendored:** the Simd128/Simd256/Vec128/Vec256 units (they need target
intrinsics that the Wasm build and a plain arm64 build lack), the EverCrypt
agile hash/HMAC/HKDF/DRBG layers, `Hacl_Streaming_HMAC.c`, every fixed-width
bignum (`Hacl_Bignum256*`, `Hacl_Bignum4096*`, `Hacl_Bignum32`),
`Hacl_GenericField*`, K-256, FFDHE, Frodo, NaCl, Salsa20, the other HPKE
ciphersuites, the Vale Curve25519/Poly1305/SHA-256 assembly, and the `-mingw.S`,
`-msvc.asm` and `ppc64le.S` Vale variants.

### AES

The commit has **no portable AES and no arm64 AES-GCM**. The only AES in
`dist/gcc-compatible` is Vale `aesgcm` assembly for x86-64 (Linux, macOS,
MinGW, MSVC) and ppc64le. `Hacl_AES128.h` declares functions that no `.c` file
defines. This re-pin therefore changes no platform's AES: native x86-64
Linux and macOS with AES-NI, PCLMULQDQ, AVX, SSE and MOVBE take the Vale path;
every other target refuses (https://github.com/danbri/factoidal/issues/677).
`EverCrypt_AEAD.c` still tests exactly those five CPU features before calling
Vale, and still answers `EverCrypt_Error_UnsupportedAlgorithm` when
`HACL_CAN_COMPILE_VALE` is unset. The four `.S` files are byte-identical to the
previous pin.

`config.h`: upstream's `dist/gcc-compatible/configure` writes it. It is not a
vendored file. `formal/lean4/ffi/hacl_vale_config/config.h` is that file
filled in by hand: `HACL_CAN_COMPILE_VALE` 1 on x86-64 Linux and macOS only,
`TARGET_ARCHITECTURE` X64 there, no VEC128/VEC256. The vendored code reads
the same configuration macros as at the previous pin.

## Reproduce

```sh
git clone --filter=blob:none --no-checkout --sparse https://github.com/hacl-star/hacl-star.git hs
cd hs
git sparse-checkout set --no-cone /dist/gcc-compatible/ /dist/karamel/ /dist/LICENSE.txt /LICENSE
git checkout f557259007db9933442dde10aa995c1b00bd3446
# copy each file listed in SHA256SUMS from the path in the mapping table above, then:
cd <repo>/third_party/hacl && shasum -a 256 -c SHA256SUMS
```

To check the curation, take the `#include` closure of the `src/*.c` files
listed above and of `formal/lean4/ffi/hacl_*.c`, with `include/` and
`formal/lean4/ffi/hacl_vale_config/` as the include path. Every vendored
header must be reached, and no header outside the directory may be missing
(only `libintvector_debug.h` and the platform `config.h`, both optional
through `__has_include`). Then check that every function a unit calls in
another unit is defined in a vendored `.c` file or a Vale `.S` file.

## History

- 2026-07-05 to 2026-09-02: Ed25519 and SHA-256, from `cryspen/hacl-packages`
  `05c3d8fb3`.
- 2026-09-06: P-256 and the generic 64-bit bignum (JOSE ES256, RS256).
  `Hacl_Bignum64.c` was chosen over `Hacl_Bignum4096.c` because it takes the
  limb count at run time (2048, 3072 and 4096 bits in one code path).
- 2026-09-07: ChaCha20-Poly1305, HMAC, HKDF, X25519, HPKE (XMPP end-to-end
  encryption); SHA-1 and BLAKE2 as HMAC link closure.
- 2026-10-27: EverCrypt AES-GCM over Vale on x86-64 (issue 677).
- 2026-11-09 and 2026-11-14: RSA-PSS and SHA-3/SHAKE for crypto.subtle.
- 2026-11-14: re-pinned to `hacl-star/hacl-star` `f557259007`, the same
  primitives, plus `Hacl_Hash_MD5.c` as HMAC link closure. Diff reading and
  evidence: `docs/designissues/2026-11-14-hacl-repin.md`.

## How it is wired in — Lean 4 tree (`formal/lean4/`)

- `ffi/hacl_ed25519.c`: Ed25519 and SHA-256 (`Crypto/Ed25519.lean`,
  `Crypto/SHA2Native.lean`).
- `ffi/hacl_p256.c`: P-256 ECDSA and ECDH (`Crypto/P256Native.lean`).
- `ffi/hacl_rsa.c`: the RSA public operation and the constant-time private
  operation (`Crypto/RsaNative.lean`, `Crypto/RsaOaep.lean`). The padding is
  in Lean.
- `ffi/hacl_chachapoly.c`, `ffi/hacl_kdf.c`, `ffi/hacl_hpke.c`:
  ChaCha20-Poly1305, HMAC/HKDF/X25519, HPKE.
- `ffi/hacl_webcrypto.c`: the web engine's crypto.subtle boundary
  (`Crypto/WebHacl.lean`).
- `ffi/hacl_aesgcm.c`: AES-GCM through `EverCrypt_AEAD`. On an x86-64 Linux or
  macOS host the lakefile (`valeHost`) also links the three EverCrypt units and
  assembles the Vale `aesgcm` and `cpuid` files for the host OS. On every
  other host the shim compiles to stubs that refuse.
- `lakefile.lean`, `extern_lib libl4hacl`: the portable units above, the
  shims, and on `valeHost` the EverCrypt units and Vale assembly.
- `Wasm/build-wasm.sh` (the Lean Wasm module) and
  `labs/demos/foafnaut/build-web-render.sh` (the web engine) compile the same
  portable units with Emscripten for wasm32. They compile no EverCrypt unit and
  no `.S` file; `ffi/hacl_aesgcm.c` there is the refusing stub. Every target
  links the same HACL\* from this directory.
- `deploy/units/l4factoidal.json`, `tests/crypto/run-kat.sh`: the same unit
  lists.

## How it is wired in — F\* tree (`formal/fstar/`)

- `formal/fstar/experimental_ocaml_glue/hacl_stubs.c`: OCaml ↔ C marshalling
  around `Hacl_Ed25519`, `Hacl_Curve25519_51` and `Hacl_Hash_SHA2` (built by
  `formal/fstar/build-ocaml.sh`), no crypto logic.
- `formal/fstar/ocaml-output/fstar_hacl_crypto.ml` and the stub patch
  `minimal_regrettable_glue_code_each_with_an_open_issue/286_vc_hacl_ed25519_sha256_stubs.sh`.
- The JavaScript path of that tree uses the prebuilt `hacl-wasm@1.4.0`
  modules in `third_party/hacl-wasm/`, a separate artifact with its own
  provenance (`third_party/hacl/wasm/PROVENANCE.md`). This re-pin did not
  change it.

## Updating

Pick one commit of hacl-star `main`, take the files of the mapping table
from it, and keep the curation rule above: the same primitives, their link
closure and their include closure. Never hand-edit a vendored file. Before
merging, diff every file against the previous pin and read the diffs (a
public prototype or a precondition in a header doc comment may change). Check
that the shims still match the prototypes. Run every known-answer and
Wycheproof probe: `lake exe l4vc-probe`, `l4jose-probe`, `l4crypto-probe`,
`tests/crypto/run-kat.sh`.
