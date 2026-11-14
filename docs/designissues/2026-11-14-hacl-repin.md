# Re-pin of the vendored HACL\* C to hacl-star f557259007

Date: 2026-11-14. Branch `wip/hacl-repin`. Provenance and the curation rule:
`third_party/hacl/PROVENANCE.md`.

## 1. What and why

`third_party/hacl/` was taken from `cryspen/hacl-packages` `05c3d8fb3` (2024-09-30).
That is the newest commit of `cryspen/hacl-packages` (`git ls-remote`, 2026-11-14): the
repository has stopped moving. hacl-star `main` is active. At `f557259007db9933442dde10aa995c1b00bd3446`
(2026-10-29) it has 318 commits made since 2024-09-30, and its `dist/` was regenerated
on 2026-10-27 (KaRaMeL `bd2d4fa8`, F\* 2026.03.24~dev, Vale 0.3.19). Among those commits
are fixes to admitted group-law lemmas of P-256, Ed25519 and K-256 (hacl-star PRs 1080,
1081).

**Flavour.** hacl-packages was a repackaging of hacl-star's `dist/`; its `info.txt`
names HACL\* `ae5d839c2`. Comparing the 91 files we vendored with that commit:
`dist/gcc-compatible` (plus `dist/karamel`) matched 76 byte for byte,
`dist/msvc-compatible` 69, and `dist/portable-gcc-compatible` 17. The portable flavour
equals gcc-compatible plus `SNIPPET_*` comment markers. The other 15 files were
hacl-packages' own regenerations (Ed25519 doc comments, BLAKE2, SHA-3,
`lib_memzero0.h`, krmllib `fstar_uint128_msvc.h`). The new files are therefore
taken from `dist/gcc-compatible` and `dist/karamel` at `f557259007`.

**Scope.** The same primitives. No new primitive is offered, no `@[extern]` is added
(the formal extern baseline stays 27), and no shim or Lean code changes beyond doc-comment
trust statements naming the new commit.

## 2. Diff of every vendored file (pinned → upstream f557259007)

Totals: 91 files vendored before. 8 identical, 83 changed (2 of them removed),
and 5 headers, 1 unit and 1 licence file added. The table gives the
lines added and removed of `diff -u`. Every changed file's diff was read: the
`src/` units of P-256, Ed25519, Curve25519, Bignum, Bignum64 and RSAPSS hunk by hunk
here, the hash/MAC/KDF units and the runtime/AEAD/HPKE files by two separate readers,
each checking every hunk, and the KaRaMeL runtime headers via a normalised diff (comments,
guards and parentheses removed) to find the lines that are not noise.

"Noise" means code generation of the newer KaRaMeL that computes the same thing:
include guards `__X_H` → `X_H`, `#include`s of dependencies moved from headers into
the `.c` files, parenthesised pointer arithmetic (`a + b + c` → `a + (b + c)`), `x = x op y`
→ `x op= y`, constant folding (`x[4U * 0U + 1U]` → `x[1U]`, `f0 + 0ULL` → `f0`), removed
temporary chains (`u = load(); r = u; x = r;` → `x = load();`), `if`/`else` assignments →
`?:`, and `(blt & 0xFF..) | (~blt & 0)` → `blt`.

| File | Pinned vs upstream | Lines +/− | What changed |
|---|---|---|---|
| `LICENSE-APACHE` | changed | +3 -3 | licence text: template brackets `[]`→`{}`, final newline |
| `include/EverCrypt_AEAD.h` | changed | +4 -6 | dropped includes; prototypes and doc comments identical |
| `include/EverCrypt_AutoConfig2.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/EverCrypt_Chacha20Poly1305.h` | changed | +4 -8 | dropped includes (no longer reaches the Vec headers) |
| `include/EverCrypt_Error.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/FStar_UInt128.h` | changed | +5 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/FStar_UInt128_Verified.h` | changed | +28 -49 | noise: guards, licence line, if/else→`?:` in shifts |
| `include/FStar_UInt_8_16_32_64.h` | changed | +23 -7 | noise + new declarations only (`*_fits`, `rotate_*`, `ne`, not called); 8/16-bit `eq_mask` rewritten, same values |
| `include/Hacl_AEAD_Chacha20Poly1305.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_AEAD_Chacha20Poly1305_Simd128.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_AEAD_Chacha20Poly1305_Simd256.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Bignum.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Bignum64.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Chacha20.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Chacha20_Vec128.h` | changed | +4 -4 | removed: no longer in the include closure |
| `include/Hacl_Chacha20_Vec256.h` | changed | +4 -4 | removed: no longer in the include closure |
| `include/Hacl_Curve25519_51.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Ed25519.h` | changed | +4 -7 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_HKDF.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_HMAC.h` | changed | +82 -8 | 6 functions added (HMAC-MD5, -SHA-224, -SHA3-224/256/384/512); existing 4 unchanged |
| `include/Hacl_HPKE_Curve51_CP32_SHA256.h` | changed | +4 -7 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Hash_Blake2b.h` | changed | +29 -30 | API reshaped (last_node flag, info, copy, renamed hash_with_key_and_params, opaque state); no Lean caller |
| `include/Hacl_Hash_Blake2s.h` | changed | +72 -46 | as Blake2b |
| `include/Hacl_Hash_SHA1.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Hash_SHA2.h` | changed | +4 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Hash_SHA3.h` | changed | +7 -20 | state struct made opaque (moved to internal header); one-shot prototypes unchanged |
| `include/Hacl_IntTypes_Intrinsics.h` | changed | +6 -6 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_IntTypes_Intrinsics_128.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Krmllib.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_MAC_Poly1305.h` | changed | +5 -13 | state struct made opaque (moved to internal header) |
| `include/Hacl_P256.h` | changed | +4 -6 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_RSAPSS.h` | changed | +4 -6 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Spec.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/Hacl_Streaming_Types.h` | changed | +7 -18 | MD streaming state structs made opaque (moved to new internal/Hacl_Streaming_Types.h); new OutOfMemory code |
| `include/LowStar_Endianness.h` | changed | +5 -5 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/evercrypt_targetconfig.h` | identical | 0 | |
| `include/fstar_uint128_gcc64.h` | changed | +1 -1 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/fstar_uint128_msvc.h` | changed | +2 -2 | fix for MSVC+SSE only (`lognot` was `andnot(a,a)`=0); not compiled by our gcc/clang/emcc builds |
| `include/fstar_uint128_struct_endianness.h` | changed | +1 -1 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Bignum.h` | changed | +4 -7 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Bignum25519_51.h` | changed | +7 -7 | noise (`f0 + 0ULL`→`f0`, `^=`) |
| `include/internal/Hacl_Bignum_Base.h` | changed | +37 -60 | noise: parenthesised pointer sums, if→`?:`, temp chains |
| `include/internal/Hacl_Chacha20.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Curve25519_51.h` | changed | +4 -6 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Ed25519.h` | changed | +4 -10 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Ed25519_PrecompTable.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_HMAC.h` | changed | +4 -9 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Hash_Blake2b.h` | changed | +23 -13 | `update_last` gains `last_node`; state struct moved here |
| `include/internal/Hacl_Hash_Blake2s.h` | changed | +26 -6 | as Blake2b |
| `include/internal/Hacl_Hash_SHA1.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Hash_SHA2.h` | changed | +5 -5 | adds `sha224_update_nblocks` (was static); sha256 init/update_nblocks/update_last/finish unchanged |
| `include/internal/Hacl_Hash_SHA3.h` | changed | +19 -4 | state struct moved here; `init_` added |
| `include/internal/Hacl_Impl_Blake2_Constants.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Krmllib.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_MAC_Poly1305.h` | changed | +19 -4 | state struct moved here |
| `include/internal/Hacl_P256.h` | changed | +4 -8 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_P256_PrecompTable.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Hacl_Spec.h` | changed | +4 -4 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/internal/Vale.h` | changed | +7 -5 | adds `#include "libintvector.h"`; same Vale declarations (one moved) |
| `include/krml/internal/compat.h` | changed | +1 -1 | noise: include guard `__X_H`→`X_H`, licence and comment lines, includes moved to the .c files |
| `include/krml/internal/target.h` | changed | +55 -11 | new macros (`KRML_MUSTINLINE`, `KRML_ATTRIBUTE_TARGET`, float32_t/float64_t typedefs, legacy-macOS aligned malloc); nothing for wasm32 or our targets |
| `include/krml/internal/types.h` | changed | +2 -2 | guard name it tests changed (must match FStar_UInt_8_16_32_64.h: updated together) |
| `include/krml/lowstar_endianness.h` | changed | +5 -5 | guard rename, ESP_PLATFORM branch |
| `include/lib_intrinsics.h` | identical | 0 | |
| `include/lib_memzero0.h` | identical | 0 | |
| `src/EverCrypt_AEAD.c` | changed | +98 -141 | state struct moved to internal/EverCrypt_AEAD.h; `(*s).x`→`s->x`; `create_in_*` now checks malloc (NULL state + Success on OOM; shim already checks NULL); same CPU-feature test, same Vale calls, no new AES path |
| `src/EverCrypt_AutoConfig2.c` | identical | 0 | |
| `src/EverCrypt_Chacha20Poly1305.c` | changed | +4 -0 | includes only |
| `src/Hacl_AEAD_Chacha20Poly1305.c` | changed | +9 -16 | noise |
| `src/Hacl_Bignum.c` | changed | +129 -210 | noise (mask algebra `(blt & 0xFF..)|(~blt & 0)`→`blt`, `?:`, temps) |
| `src/Hacl_Bignum64.c` | changed | +26 -29 | noise + `mont_ctx_init` checks malloc (not called by our shims) |
| `src/Hacl_Chacha20.c` | changed | +5 -11 | noise |
| `src/Hacl_Curve25519_51.c` | changed | +3 -4 | noise (`& 1U`→`(& 1U) & 0xFFU`, temps) |
| `src/Hacl_Ed25519.c` | changed | +125 -195 | noise + control flow: point decompression and the scalar range check `s < q` rewritten with early returns / one boolean expression; read hunk by hunk: same results |
| `src/Hacl_HKDF.c` | changed | +6 -5 | noise |
| `src/Hacl_HMAC.c` | changed | +740 -128 | 6 new HMAC variants (MD5, SHA-224, SHA3-*); SHA-1/256/384/512 bodies same up to VLA→fixed arrays and `?:`; key handling unchanged; NEW link deps MD5 and SHA-3 |
| `src/Hacl_HPKE_Curve51_CP32_SHA256.c` | changed | +46 -38 | noise: literal offsets named, early returns in the sequence-overflow check, same bytes |
| `src/Hacl_Hash_Blake2b.c` | changed | +526 -347 | BLAKE2 last-node flag added (off on every path we reach); API reshaping; malloc checks |
| `src/Hacl_Hash_Blake2s.c` | changed | +570 -361 | as Blake2b |
| `src/Hacl_Hash_SHA1.c` | changed | +174 -152 | noise (if-chains→`?:`); malloc/copy NULL checks |
| `src/Hacl_Hash_SHA2.c` | changed | +496 -373 | noise; `sha224_update_nblocks` made non-static; malloc/copy NULL checks |
| `src/Hacl_Hash_SHA3.c` | changed | +711 -993 | noise in Keccak-f; squeeze loop of the streaming digest moved into `squeeze()` (same body); one-shot SHA3/SHAKE unchanged up to noise; `init_` added |
| `src/Hacl_MAC_Poly1305.c` | changed | +152 -128 | noise; malloc check |
| `src/Hacl_P256.c` | changed | +140 -161 | noise only (constant folding `4U * 0U`, temps, `return f(..)`); the 2026 group-law soundness fixes changed proofs, not this C |
| `src/Hacl_RSAPSS.c` | changed | +40 -66 | noise; `pss_verify` two early returns merged into one condition (same reads, same result) |
| `src/Lib_Memzero0.c` | changed | +23 -6 | platform selection: Apple uses memset_s only when AvailabilityMacros says it exists (true on our targets); Cygwin/OpenBSD explicit_bzero; wasm32 unchanged (volatile loop) |
| `vale/src/aesgcm-x86_64-darwin.S` | identical | 0 | |
| `vale/src/aesgcm-x86_64-linux.S` | identical | 0 | |
| `vale/src/cpuid-x86_64-darwin.S` | identical | 0 | |
| `vale/src/cpuid-x86_64-linux.S` | identical | 0 | |

Added: `src/Hacl_Hash_MD5.c`, `include/Hacl_Hash_MD5.h`, `include/internal/Hacl_Hash_MD5.h`,
`include/internal/Hacl_Streaming_Types.h`, `include/internal/EverCrypt_AEAD.h`,
`include/libintvector.h`, `LICENSE-MIT`. Removed: `include/Hacl_Chacha20_Vec128.h`,
`include/Hacl_Chacha20_Vec256.h`. No vendored file is missing upstream.

### 2.1 Changes that are not code-generation noise

1. **`Hacl_HMAC.c` covers more hashes.** It adds HMAC-MD5, HMAC-SHA-224 and HMAC-SHA3-224/256/384/512,
   so the unit now calls `Hacl_Hash_MD5_*` and `Hacl_Hash_SHA3_*`. `Hacl_Hash_MD5.c` is
   added as link closure (as SHA-1 and BLAKE2 already were). SHA-3 was already vendored.
   HMAC-SHA-1/256/384/512 are computed as before: the same block sizes (64/128), and long
   keys hashed with the same functions.
2. **BLAKE2 last-node flag.** `update_block` gains a `last_node` argument (tree-hashing flag
   f1). Every path inside HACL\* and HMAC passes `false`, so plain BLAKE2 is unchanged. The
   public BLAKE2 API changed shape (`malloc_with_params_and_key` gains `last_node`,
   `digest` returns the length, `hash_with_key_and_paramas` → `hash_with_key_and_params`,
   `info`, `copy`). Nothing in this repository calls BLAKE2 directly.
3. **Opaque streaming state.** The SHA-1/SHA-2/MD5 streaming state, SHA-3, Poly1305 and BLAKE2 state
   structs left the public headers for internal ones (`internal/Hacl_Streaming_Types.h` is
   new). The shims use only one-shot functions and the internal SHA-256 block
   functions, whose prototypes are unchanged.
4. **Allocation checks.** `malloc`/`copy` of the streaming hashes, `Hacl_Bignum64_mont_ctx_init`
   and `EverCrypt_AEAD_create_in` now check `malloc` for NULL. On out-of-memory `create_in`
   answers Success with a NULL state (before: a write through NULL). `ffi/hacl_aesgcm.c`
   already treats a NULL state as a failure.
5. **`Lib_Memzero0.c` platform selection.** On Apple, `memset_s` is used when
   `AvailabilityMacros.h` says it exists (all our deployment targets), else a volatile
   loop. Linux keeps `explicit_bzero`, and wasm32 keeps the volatile loop.
6. **Control flow in `Hacl_Ed25519.c`.** Point decompression uses early returns in place of
   a result variable, and the scalar check `s < q` became one boolean expression. Both were
   read against the old code branch by branch: same results. The latter is variable-time
   on the public `s`, as before.
7. **`fstar_uint128_msvc.h`**: `FStar_UInt128_lognot` under MSVC with SSE was wrong
   (`_mm_andnot_si128(a, a)` is 0) and is fixed. None of our builds use MSVC.
8. **`krml/internal/target.h`**: new macros only, no change for our targets.
9. **Headers no longer include their dependencies.** `Hacl_Ed25519.h` no longer includes
   `Hacl_Hash_SHA2.h`, for example. Every shim already includes what it uses: all of
   `formal/lean4/ffi/hacl_*.c` compile (syntax check, section 4).
10. **Doc comments.** The prototypes and doc comments of every function the shims call are
    unchanged, with one exception: `Hacl_Ed25519.h` loses hacl-packages' own `@param`
    wording ("must not overlap"); upstream's text is the older wording. The F\*
    precondition is the same; the shims always pass freshly allocated output arrays.

### 2.2 The 2026 soundness fixes

hacl-star PRs 1080 and 1081 (issue 1079) fix admitted group-law lemmas of P-256,
Ed25519 and K-256. In the extracted C, `Hacl_P256.c` changes only by noise (constant
folding, temporaries, direct returns). `Hacl_Ed25519.c` changes by noise and the control
flow of item 6. The fixes removed unproved assumptions from the proofs. The code those
proofs cover computes the same function as before.

## 3. Shims and externs

Prototypes compared by script and by reading, old against new, for every HACL\*
function the shims call. All are unchanged:
`EverCrypt_AEAD_{create_in,encrypt,decrypt,free}`, `EverCrypt_AutoConfig2_{init,has_aesni,
has_avx,has_movbe,has_pclmulqdq,has_sse}`, the `EverCrypt_Error` values,
`Hacl_AEAD_Chacha20Poly1305_{encrypt,decrypt}`, `Hacl_Bignum64_{new_bn_from_bytes_be,
bn_to_bytes_be,mod_exp_vartime,mod_exp_consttime}`, `Hacl_Curve25519_51_{scalarmult,
secret_to_public,ecdh}`, `Hacl_Ed25519_{secret_to_public,sign,verify}`,
`Hacl_HKDF_{extract,expand}_sha2_256`, `Hacl_HMAC_compute_{sha1,sha2_256,sha2_384,
sha2_512}`, `Hacl_HPKE_Curve51_CP32_SHA256_{sealBase,openBase}`, `Hacl_Hash_SHA1_hash`,
`Hacl_Hash_SHA2_{hash_256,hash_384,hash_512,sha256_init,sha256_update_nblocks,
sha256_update_last,sha256_finish}`, `Hacl_Hash_SHA3_{sha3_256,sha3_384,sha3_512,shake128,
shake256}`, `Hacl_P256_{ecdsa_sign_p256_sha2,ecdsa_sign_p256_without_hash,
ecdsa_verif_p256_sha2,ecdsa_verif_without_hash,validate_public_key,validate_private_key,
compressed_to_raw,dh_initiator,dh_responder}`, `Hacl_RSAPSS_{new_rsapss_load_pkey,
new_rsapss_load_skey,rsapss_sign,rsapss_verify}`, `Lib_Memzero0_memzero0`. So no shim and no
Lean precondition type changes. The number of `@[extern]`s does not change.

## 4. Build closure

- Include closure of the vendored units and the shims, computed over `include/` and
  `ffi/hacl_vale_config/`: every vendored header is reached. Nothing is missing except
  `libintvector_debug.h` and the platform `config.h`, both behind `__has_include`.
- Link closure: every cross-unit call resolves to a vendored `.c` file, a `static inline`
  in a vendored header, or a Vale `.S` symbol. The Simd calls of
  `EverCrypt_Chacha20Poly1305.c` are under `HACL_CAN_COMPILE_VEC128/256`, which we leave
  undefined.
- `Hacl_Hash_MD5.c` is added to every list that compiles `Hacl_HMAC.c`: the lakefile's
  `libl4hacl`, `Wasm/build-wasm.sh`, `labs/demos/foafnaut/build-web-render.sh`,
  `tests/crypto/run-kat.sh` and `deploy/units/l4factoidal.json`. The deploy manifest also
  gains `Hacl_Hash_SHA3.c`, now called by HMAC. The F\* tree's `build-ocaml.sh` compiles
  only Ed25519, Curve25519 and SHA-2, which need neither.
- Local syntax check (`cc -fsyntax-only -Wall`, no objects, no build), arm64 macOS: all 22
  vendored units and all 8 shims, 0 errors and 0 warnings. With `-target
  x86_64-apple-macos12` (so `HACL_CAN_COMPILE_VALE` is 1) the three EverCrypt units and
  `ffi/hacl_aesgcm.c` also pass.
- The configuration macros the vendored code reads are the same set as before;
  `ffi/hacl_vale_config/config.h` changes only in its comments.

## 5. AES

Upstream still has no portable AES and no arm64 AES-GCM: `dist/gcc-compatible` has Vale
`aesgcm` for x86-64 (Linux, macOS, MinGW, MSVC) and ppc64le only. The four vendored `.S`
files are byte-identical to the old pin. `EverCrypt_AEAD.c` tests the same five CPU features
before any Vale call and still refuses without `HACL_CAN_COMPILE_VALE`. No AES entry point
was added, and `tools/aes-gate-allow.txt` is unchanged.

## 6. Wasm

- The Lean Wasm module (`Wasm/build-wasm.sh`) and the web engine
  (`build-web-render.sh`) compile this same directory with Emscripten. They are re-pinned by
  this change (with `Hacl_Hash_MD5.c` added to both lists) and need nothing else.
- The prebuilt `hacl-wasm@1.4.0` modules in `third_party/hacl-wasm/` are used only by the F\*/OCaml
  npm path (`formal/fstar/ocaml-output/hacl_stubs.js`). They are a different artifact
  (binaries built by upstream in 2023 with its own toolchain pin) and a different curation, and
  are **not** re-pinned here. The npm `hacl-wasm` package is still at 1.4.0. hacl-star
  `f557259007` ships `dist/wasm/` (72 files: `.wasm` modules, loader and `api.json`). A
  separate step would replace `third_party/hacl-wasm/` with the needed modules of
  `dist/wasm` at the same commit, check that `hacl_stubs.js` matches the `api.json` entry
  names, record the sha256 of each module, and run the npm suite's VC vectors
  (`npm/factoidal/test`).

## 7. Evidence

Measured on the exact tree of `wip/hacl-repin` `12c9fe4e2` unless stated.

| Requirement | Check | Result |
|---|---|---|
| Engine builds with the new files; WebCryptoAPI with no losses | `branch-wpt.yml` run 43586156878 (Linux engine library from `12c9fe4e2`), names `/WebCryptoAPI/,sample:40`, 2,694 names | Built. Against the main 2b464c0a8 baseline: +3,425 subtests, 7 tests worse, none in WebCryptoAPI (css-mixins, legend-display, `createImageBitmap.p3`, CSP pages, two CSS typed-OM/values; all present in the check of the same base without the re-pin). **Isolated:** against run 43585629355, which built the same base commit `81aa14268` without the re-pin and used the same baseline, all 2,694 shared names give identical results subtest for subtest: WebCryptoAPI 336 tests, 51,438 passes in both, 0 differences; all names 103,638 passes in both, 0 subtest and 0 harness differences. |
| AES gate | `python3 tools/aes-gate.py` on the rebased tree; PR check `aes-gate` | 0 findings; the PR check passed. |
| Full Lean build | `verify-lean4.yml` on the PR head (run 43586268947) | Building the library, proofs and guards, plus the escape-hatch audit, passed. The job then failed at "Gate compiled recursion and compiler replacement reach" on four WebDriver rows missing from `tools/lean-tail-recursion-allow.txt`. The same gate fails on main (run 43581618519, WebDriver `Gate.mismatches`, `Protocol.matchPath`): not caused by this change. |
| Full Lean build, all gates | `verify-lean4.yml` dispatched on `wip/hacl-repin-ci` `1577ca2a9` (= `12c9fe4e2` + workflow steps only), run 43591028398 | **Success**, every step: build, escape-hatch audit, the recursion gate (passed in this run), all suites. |
| HACL\* known-answer and Wycheproof vectors | same run: `lake exe l4vc-probe` | TOTAL 258 pass, 0 fail: Ed25519 RFC 8032 22/22, did:key 8/8, VC DI eddsa-rdfc-2022 8/8, eddsa spec vectors 24/24, ecdsa spec vectors 18/18, sha256 differential (HACL\* vs pure Lean) 61/61, VC structural 117/117 |
| | same run: `lake exe l4crypto-probe` (GitHub x86-64 runner; "HACL\* Vale AES-GCM is available") | TOTAL 3,648 pass, 0 fail, 256 acceptable, 183 not run: RFC 8439 13/13, Wycheproof ChaCha20-Poly1305 837/837, HMAC/HKDF differential 25/25, Wycheproof HKDF-SHA-256 172/172, Wycheproof X25519 299 pass + 254 acceptable, RFC 9180 A.2 15/15, AES-GCM 319 pass (Vale; the 183 not run are AES-192 and non-96-bit IVs, which the binding does not offer, as before), LWS snapshot seal 11/11, P-256 RFC 6979 12/12, P-256 secret-to-public 357/357, P-256 compressed 341 + 1 acceptable, NIST RSA-OAEP 187/187, Wycheproof RSA-OAEP 2048-SHA1 70/70, 2048-SHA256 73/73, 3072 73/73, 4096 73/73, P-256 ECDH 771 + 1 acceptable |
| | same run: `lake exe l4jose-probe` | TOTAL 1,077 pass, 0 fail, 3 acceptable: JOSE RFC fixtures 17/17, Wycheproof ECDSA P-256 P1363 262/262, Wycheproof RSA PKCS#1 2048/3072/4096-SHA256 258+1, 258+1, 257+1, DPoP 11/11, Solid-OIDC 14/14 |
| | `tests/crypto/run-kat.sh` (C known-answer driver of `ffi/hacl_webcrypto.c`) | **Not run.** In CI (run 43594401705) every unit compiled, but the link failed: `run-kat.sh` names `libleanrt.a` before `libInit.a`, which macOS `ld64` accepts and GNU `ld` does not. All undefined references are Lean runtime symbols (`lean_system_platform_*`, `lean_get_githash`, ...), none a HACL\* symbol. Not run locally (no local builds). Its primitives are the same `ffi/hacl_webcrypto.c` entry points the WebCryptoAPI tests above exercise, with identical results. |
| | `tests/crypto/ecdh-diff.mjs`, `rsa-oaep-diff.mjs`, `aes-diff.mjs` | **Not run:** they need a locally built `l4crypto-probe` (`lake build`), and local builds are not allowed. The vectors they compare are also in `l4crypto-probe`, which passed. |

The merged commit has the same `third_party/hacl`, `formal/lean4/ffi`, `formal/lean4/L4Factoidal/Crypto`,
`Wasm/build-wasm.sh`, `tests/crypto` and deploy-manifest trees (git object ids) as the measured
`12c9fe4e2`. It is that commit rebased onto main `d10aed616`, whose own changes to `lakefile.lean` and
`build-web-render.sh` are in regions unrelated to HACL\*.

## 8. What this shows and what it does not

- Shown, by check: the vendored files equal upstream `f557259007` byte for byte (`SHA256SUMS`); the
  include and link closures are complete; the shims match the upstream prototypes; no AES code was added.
- Tested, not proved: the re-pinned C gives the same answers as before on every vector the repository
  holds (sections above) and on WebCryptoAPI and a regression sample of WPT.
- Trusted: HACL\*'s proofs (now including the 2026 group-law soundness fixes) and that the
  `dist/` at the commit is KaRaMeL's extraction of the verified code; the C compiler; the Lean FFI.
- Not related by theorem: the externs to the pure Lean specifications (unchanged:
  https://github.com/danbri/factoidal/issues/777).

## 9. Open

- The prebuilt `third_party/hacl-wasm/` (`hacl-wasm@1.4.0`) of the F\*/OCaml npm path: not re-pinned
  (section 6).
- `tests/crypto/run-kat.sh` links only on macOS. Putting `libInit.a` before `libleanrt.a` (plus the Linux
  C++ runtime) would let CI run it.
- In upstream `dist/gcc-compatible` and not adopted here (each would be its own change, and an extern
  needs the owner): HMAC-SHA3-* and HMAC-SHA-224 (already in the vendored `Hacl_HMAC.c`, no extern),
  `Hacl_Streaming_HMAC`, K-256 ECDSA (`Hacl_K256_ECDSA`), `Hacl_FFDHE`, the other HPKE ciphersuites
  (P-256 and Curve64, SHA-512), BLAKE2 keyed/tree hashing through its new API, and the Simd/Vec units
  (they need target intrinsics). Still absent upstream: a portable or arm64 AES.
