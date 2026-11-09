/* hacl_webcrypto.c — the web engine's boundary to HACL* (crypto.subtle of page scripts).
 *
 * Realises the `@[extern "l4_web_hacl_*"]` opaques of
 * formal/lean4/L4Factoidal/Crypto/WebHacl.lean over the vendored HACL* C
 * (third_party/hacl/, cryspen/hacl-packages 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2,
 * Apache-2.0; third_party/hacl/PROVENANCE.md). Design record:
 * docs/designissues/2026-11-09-hacl-web-crypto.md, section "The C boundary".
 *
 * This file is the only C between page scripts and HACL*. It holds NO cryptographic
 * logic: every primitive is one HACL* call. Every entry point has the same shape, which
 * tools/hacl-web-glue-audit.py checks:
 *
 *   1. Length checks on every argument, BEFORE any HACL* call. The Lean side has already
 *      checked the same lengths: each extern takes a proof of its precondition
 *      (WebHacl.lean), so a call that would fail here does not type-check there. These
 *      checks are the second line, for a caller outside Lean.
 *   2. The output is a FRESH Lean byte array of exactly the size the primitive writes,
 *      allocated here. It is therefore disjoint from every input (HACL*'s F*
 *      preconditions ask `disjoint output input`; inputs may alias each other, which
 *      HACL* allows for read-only buffers).
 *   3. One HACL* call, through `l4wc_*` (hacl_webcrypto_core.c: raw buffers; on the Hub
 *      the separately loaded hacl-web.wasm).
 *   4. On a HACL* refusal the output is zeroed (Lib_Memzero0, which the compiler may not
 *      remove) and freed, and an EMPTY array is answered. A failure never answers a
 *      partly written buffer.
 *   5. Secret temporaries on the stack are zeroed with Lib_Memzero0 before return.
 *
 * Inputs are BORROWED (`@&` on the Lean side). HACL* takes non-const `uint8_t *` for
 * inputs but does not write through them (its F* specifications `modifies` only the
 * output). No function here compares secret bytes with `==`, `memcmp` or a branch:
 * `l4_web_hacl_ct_eq` folds KaRaMeL's constant-time `FStar_UInt8_eq_mask`, the mask HACL*
 * itself uses (Hacl_Curve25519_51_ecdh). The only branches are on lengths and on HACL*'s
 * own success flags, which are public.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include <stdlib.h>
#include "krml/internal/target.h"
#include "FStar_UInt_8_16_32_64.h"
#include "lib_memzero0.h"
#include "hacl_webcrypto_core.h"

/* The hash family at the boundary: 1 SHA-1, 2 SHA-256, 3 SHA-384, 4 SHA-512
 * (WebHacl.HashAlg.code). */
static size_t l4w_hash_size(uint8_t alg) {
  switch (alg) { case 1: return 20; case 2: return 32; case 3: return 48; case 4: return 64; default: return 0; }
}
static size_t l4w_block_size(uint8_t alg) {
  switch (alg) { case 1: case 2: return 64; case 3: case 4: return 128; default: return 0; }
}

static lean_obj_res l4w_empty(void) { return lean_alloc_sarray(1, 0, 0); }
static lean_obj_res l4w_fresh(size_t n) { return lean_alloc_sarray(1, n, n); }
/* Step 4: zero and free a fresh output that HACL* refused to fill. */
static lean_obj_res l4w_refuse(lean_obj_res out) {
  size_t n = lean_sarray_size(out);
  if (n) Lib_Memzero0_memzero0(lean_sarray_cptr(out), (uint64_t)n);
  lean_dec_ref(out);
  return l4w_empty();
}
#define L4W_SIZE(x) lean_sarray_size(x)
#define L4W_PTR(x) lean_sarray_cptr(x)

/* ---- Hashes: Hacl_Hash_SHA1_hash, Hacl_Hash_SHA2_hash_{256,384,512} ----------------
 * Precondition (F*, Spec.Hash.Definitions): input_len <= max_input_length, and the C API
 * takes a uint32_t, so input_len < 2^32. Output: exactly the digest size. */
LEAN_EXPORT lean_obj_res l4_web_hacl_hash(uint8_t alg, b_lean_obj_arg msg) {
  size_t hn = l4w_hash_size(alg), n = L4W_SIZE(msg);
  if (hn == 0 || n > UINT32_MAX) return l4w_empty();
  lean_obj_res out = l4w_fresh(hn);
  if (!l4wc_hash(alg, L4W_PTR(msg), (uint32_t)n, L4W_PTR(out))) return l4w_refuse(out);
  return out;
}

/* ---- HMAC: Hacl_HMAC_compute_{sha1,sha2_256,sha2_384,sha2_512} -----------------------
 * Precondition (F*, Hacl.HMAC.compute_st): key_len < 2^32 (keysized), and
 * data_len + block_length < 2^32. Output: exactly the hash size. */
LEAN_EXPORT lean_obj_res l4_web_hacl_hmac(uint8_t alg, b_lean_obj_arg key, b_lean_obj_arg msg) {
  size_t hn = l4w_hash_size(alg), bn = l4w_block_size(alg);
  size_t kn = L4W_SIZE(key), mn = L4W_SIZE(msg);
  if (hn == 0 || kn > UINT32_MAX || mn > (size_t)UINT32_MAX - bn) return l4w_empty();
  lean_obj_res out = l4w_fresh(hn);
  if (!l4wc_hmac(alg, L4W_PTR(key), (uint32_t)kn, L4W_PTR(msg), (uint32_t)mn, L4W_PTR(out))) return l4w_refuse(out);
  return out;
}

/* ---- Constant-time equality of two byte strings of the same (public) length ---------
 * 1 when equal. Unequal lengths answer 0 at once: lengths are public. The fold has no
 * branch on the bytes: FStar_UInt8_eq_mask is KaRaMeL's verified constant-time mask. */
LEAN_EXPORT uint8_t l4_web_hacl_ct_eq(b_lean_obj_arg a, b_lean_obj_arg b) {
  size_t n = L4W_SIZE(a);
  if (n != L4W_SIZE(b)) return 0;
  const uint8_t *x = L4W_PTR(a), *y = L4W_PTR(b);
  uint8_t acc = 255U;
  for (size_t i = 0; i < n; i++) acc = (uint8_t)(FStar_UInt8_eq_mask(x[i], y[i]) & acc);
  return (uint8_t)(acc & 1U);
}

/* ---- Ed25519 (RFC 8032): Hacl_Ed25519_{secret_to_public,sign,verify} ----------------
 * Preconditions (F*, Hacl.Ed25519): private and public keys 32 bytes, signature 64,
 * msg_len + 64 <= max_size_t, so msg_len <= 2^32 - 65 for the uint32_t API. */
#define L4W_ED_MAX ((size_t)UINT32_MAX - 64U)
LEAN_EXPORT lean_obj_res l4_web_hacl_ed25519_public(b_lean_obj_arg sk) {
  if (L4W_SIZE(sk) != 32) return l4w_empty();
  lean_obj_res out = l4w_fresh(32);
  l4wc_ed25519_public(L4W_PTR(sk), L4W_PTR(out));
  return out;
}
LEAN_EXPORT lean_obj_res l4_web_hacl_ed25519_sign(b_lean_obj_arg sk, b_lean_obj_arg msg) {
  if (L4W_SIZE(sk) != 32 || L4W_SIZE(msg) > L4W_ED_MAX) return l4w_empty();
  lean_obj_res out = l4w_fresh(64);
  l4wc_ed25519_sign(L4W_PTR(sk), L4W_PTR(msg), (uint32_t)L4W_SIZE(msg), L4W_PTR(out));
  return out;
}
LEAN_EXPORT uint8_t l4_web_hacl_ed25519_verify(b_lean_obj_arg pk, b_lean_obj_arg msg, b_lean_obj_arg sig) {
  if (L4W_SIZE(pk) != 32 || L4W_SIZE(sig) != 64 || L4W_SIZE(msg) > L4W_ED_MAX) return 0;
  return l4wc_ed25519_verify(L4W_PTR(pk), L4W_PTR(msg), (uint32_t)L4W_SIZE(msg), L4W_PTR(sig)) ? 1 : 0;
}

/* ---- X25519 (RFC 7748): Hacl_Curve25519_51_{secret_to_public,ecdh} -------------------
 * 32-byte scalar and u-coordinate. HACL* clamps the scalar. Hacl_Curve25519_51_ecdh
 * refuses an all-zero shared secret (a small-order input point) with a constant-time
 * test; WebCrypto's X25519 deriveBits then rejects with OperationError. */
LEAN_EXPORT lean_obj_res l4_web_hacl_x25519_public(b_lean_obj_arg sk) {
  if (L4W_SIZE(sk) != 32) return l4w_empty();
  lean_obj_res out = l4w_fresh(32);
  l4wc_x25519_public(L4W_PTR(sk), L4W_PTR(out));
  return out;
}
LEAN_EXPORT lean_obj_res l4_web_hacl_x25519(b_lean_obj_arg sk, b_lean_obj_arg pk) {
  if (L4W_SIZE(sk) != 32 || L4W_SIZE(pk) != 32) return l4w_empty();
  lean_obj_res out = l4w_fresh(32);
  if (!l4wc_x25519(L4W_PTR(sk), L4W_PTR(pk), L4W_PTR(out))) return l4w_refuse(out);
  return out;
}

/* ---- P-256 (FIPS 186-4, SP 800-56A): Hacl_P256_* --------------------------------------
 * Keys: private 32 bytes (HACL* checks 0 < d < n), public x || y 64 bytes (HACL* checks
 * the point: not infinity, coordinates below p, on the curve). Message representative
 * `e`: exactly 32 bytes (HACL*: msg_len >= 32, and it reads the first 32), made in Lean
 * from the hash (WebHacl.p256MsgRep). Nonce: 32 bytes from the page's HMAC_DRBG. */
LEAN_EXPORT lean_obj_res l4_web_hacl_p256_public(b_lean_obj_arg sk) {
  if (L4W_SIZE(sk) != 32) return l4w_empty();
  lean_obj_res out = l4w_fresh(64);
  if (!l4wc_p256_public(L4W_PTR(sk), L4W_PTR(out))) return l4w_refuse(out);
  return out;
}
LEAN_EXPORT uint8_t l4_web_hacl_p256_valid_public(b_lean_obj_arg xy) {
  if (L4W_SIZE(xy) != 64) return 0;
  return l4wc_p256_valid_public(L4W_PTR(xy)) ? 1 : 0;
}
LEAN_EXPORT uint8_t l4_web_hacl_p256_valid_private(b_lean_obj_arg sk) {
  if (L4W_SIZE(sk) != 32) return 0;
  return l4wc_p256_valid_private(L4W_PTR(sk)) ? 1 : 0;
}
/* SEC 1 §2.3.4 compressed point (0x02 or 0x03, then x) to x || y; HACL* checks the point. */
LEAN_EXPORT lean_obj_res l4_web_hacl_p256_decompress(b_lean_obj_arg c) {
  if (L4W_SIZE(c) != 33) return l4w_empty();
  lean_obj_res out = l4w_fresh(64);
  if (!l4wc_p256_decompress(L4W_PTR(c), L4W_PTR(out))) return l4w_refuse(out);
  return out;
}
LEAN_EXPORT lean_obj_res l4_web_hacl_p256_sign(b_lean_obj_arg sk, b_lean_obj_arg e, b_lean_obj_arg nonce) {
  if (L4W_SIZE(sk) != 32 || L4W_SIZE(e) != 32 || L4W_SIZE(nonce) != 32) return l4w_empty();
  lean_obj_res out = l4w_fresh(64);
  if (!l4wc_p256_sign(L4W_PTR(sk), L4W_PTR(e), L4W_PTR(nonce), L4W_PTR(out))) return l4w_refuse(out);
  return out;
}
LEAN_EXPORT uint8_t l4_web_hacl_p256_verify(b_lean_obj_arg xy, b_lean_obj_arg e, b_lean_obj_arg rs) {
  if (L4W_SIZE(xy) != 64 || L4W_SIZE(e) != 32 || L4W_SIZE(rs) != 64) return 0;
  return l4wc_p256_verify(L4W_PTR(xy), L4W_PTR(e), L4W_PTR(rs)) ? 1 : 0;
}
/* ECDH: the x-coordinate of d·Q (SP 800-56A §5.7.1.2, the "Z" WebCrypto's deriveBits
 * returns). The whole point stays in the core, which zeroes it; only x leaves. HACL*
 * checks d and Q (Hacl_P256_dh_responder). */
LEAN_EXPORT lean_obj_res l4_web_hacl_p256_ecdh(b_lean_obj_arg xy, b_lean_obj_arg sk) {
  if (L4W_SIZE(xy) != 64 || L4W_SIZE(sk) != 32) return l4w_empty();
  lean_obj_res out = l4w_fresh(32);
  if (!l4wc_p256_ecdh(L4W_PTR(xy), L4W_PTR(sk), L4W_PTR(out))) return l4w_refuse(out);
  return out;
}

/* ---- ChaCha20-Poly1305 (RFC 8439): Hacl_AEAD_Chacha20Poly1305_{encrypt,decrypt} ------
 * Key 32 bytes, nonce 12, tag 16; input_len and data_len below 2^32 (and the sealed
 * length input_len + 16 too). Seal answers ciphertext || tag. Open answers 1 || plaintext,
 * or the single byte 0 when HACL*'s constant-time tag check fails (HACL* then leaves the
 * output unwritten; it is zeroed and freed all the same). */
LEAN_EXPORT lean_obj_res l4_web_hacl_chachapoly_seal(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                                    b_lean_obj_arg aad, b_lean_obj_arg plain) {
  size_t pn = L4W_SIZE(plain), an = L4W_SIZE(aad);
  if (L4W_SIZE(key) != 32 || L4W_SIZE(nonce) != 12 || pn > (size_t)UINT32_MAX - 16U || an > UINT32_MAX)
    return l4w_empty();
  lean_obj_res out = l4w_fresh(pn + 16);
  l4wc_chacha_seal(L4W_PTR(key), L4W_PTR(nonce), L4W_PTR(aad), (uint32_t)an, L4W_PTR(plain), (uint32_t)pn,
                   L4W_PTR(out));
  return out;
}
LEAN_EXPORT lean_obj_res l4_web_hacl_chachapoly_open(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                                    b_lean_obj_arg aad, b_lean_obj_arg sealed) {
  size_t cn = L4W_SIZE(sealed), an = L4W_SIZE(aad);
  if (L4W_SIZE(key) != 32 || L4W_SIZE(nonce) != 12 || cn < 16 || cn - 16 > UINT32_MAX || an > UINT32_MAX)
    return l4w_empty();
  size_t pn = cn - 16;
  lean_obj_res out = l4w_fresh(pn + 1);
  uint8_t *o = L4W_PTR(out);
  if (!l4wc_chacha_open(L4W_PTR(key), L4W_PTR(nonce), L4W_PTR(aad), (uint32_t)an, L4W_PTR(sealed), (uint32_t)pn,
                        o + 1)) {
    lean_dec_ref(l4w_refuse(out)); /* the empty array l4w_refuse answers is not used here */
    lean_obj_res fail = l4w_fresh(1);
    L4W_PTR(fail)[0] = 0;
    return fail;
  }
  o[0] = 1;
  return out;
}

/* ---- RSA (RFC 8017): Hacl_Bignum64_mod_exp_{vartime,consttime}, Hacl_RSAPSS ----------
 * Modulus `n`: big-endian, no leading zero octet, 128 to 512 octets in whole 64-bit limbs
 * (1024 to 4096 bits). Exponents `e`, `d`: big-endian, 1 to |n| octets. The operand of a
 * raw operation is exactly |n| octets. HACL* checks n odd and > 1 and the operand < n
 * (mod_exp returns false otherwise). The private exponent is used left-padded to |n|
 * octets with dBits = 8|n|, so the bit length of d does not leave Lean. Every buffer
 * holding d is zeroed (Lib_Memzero0) before it is freed. Padding (EMSA-PKCS1-v1_5,
 * EME-OAEP) is Lean's; PSS is HACL*'s Hacl_RSAPSS (SHA-256/384/512). */
static uint32_t l4w_bits(const uint8_t *p, size_t n) {
  size_t i = 0;
  while (i < n && p[i] == 0) i++;
  if (i == n) return 0;
  uint32_t b = (uint32_t)((n - i - 1) * 8);
  uint8_t top = p[i];
  while (top) { b++; top >>= 1; }
  return b;
}
static int l4w_rsa_mod_ok(b_lean_obj_arg n) {
  size_t k = L4W_SIZE(n);
  return k % 8 == 0 && k >= 128 && k <= 512 && L4W_PTR(n)[0] != 0;
}
/* RSAEP / RSAVP1: x^e mod n (public, variable time). */
LEAN_EXPORT lean_obj_res l4_web_hacl_rsa_public(b_lean_obj_arg n, b_lean_obj_arg e, b_lean_obj_arg x) {
  size_t k = L4W_SIZE(n);
  if (!l4w_rsa_mod_ok(n) || L4W_SIZE(e) == 0 || L4W_SIZE(e) > k || L4W_SIZE(x) != k) return l4w_empty();
  uint32_t ebits = l4w_bits(L4W_PTR(e), L4W_SIZE(e));
  if (ebits == 0) return l4w_empty();
  lean_obj_res out = l4w_fresh(k);
  if (!l4wc_modexp(L4W_PTR(n), (uint32_t)k, L4W_PTR(e), (uint32_t)L4W_SIZE(e), ebits, L4W_PTR(x), 0, L4W_PTR(out)))
    return l4w_refuse(out);
  return out;
}
/* RSADP / RSASP1: x^d mod n (constant time in d). */
LEAN_EXPORT lean_obj_res l4_web_hacl_rsa_private(b_lean_obj_arg n, b_lean_obj_arg d, b_lean_obj_arg x) {
  size_t k = L4W_SIZE(n);
  if (!l4w_rsa_mod_ok(n) || L4W_SIZE(d) == 0 || L4W_SIZE(d) > k || L4W_SIZE(x) != k) return l4w_empty();
  lean_obj_res out = l4w_fresh(k);
  if (!l4wc_modexp(L4W_PTR(n), (uint32_t)k, L4W_PTR(d), (uint32_t)L4W_SIZE(d), (uint32_t)(8 * k), L4W_PTR(x), 1,
                   L4W_PTR(out)))
    return l4w_refuse(out);
  return out;
}
static int l4w_pss_alg(uint8_t alg) { return alg == 2 ? 1 : alg == 3 ? 2 : alg == 4 ? 3 : -1; }
/* RSASSA-PSS sign (RFC 8017 §8.1.1) by Hacl_RSAPSS_rsapss_sign: hash code 2, 3 or 4
 * (SHA-256, 384, 512), the salt drawn by Lean from the page's HMAC_DRBG. d goes to the
 * core padded to |n| octets in a buffer zeroed and freed here; the core zeroes the
 * secret-key limbs HACL* made (Hacl_RSAPSS_new_rsapss_load_skey checks n, e and d). */
LEAN_EXPORT lean_obj_res l4_web_hacl_rsapss_sign(uint8_t alg, b_lean_obj_arg n, b_lean_obj_arg e, b_lean_obj_arg d,
                                                b_lean_obj_arg salt, b_lean_obj_arg msg) {
  int a = l4w_pss_alg(alg);
  size_t k = L4W_SIZE(n), dl = L4W_SIZE(d);
  if (a < 0 || !l4w_rsa_mod_ok(n) || L4W_SIZE(e) == 0 || L4W_SIZE(e) > k || dl == 0 || dl > k ||
      L4W_SIZE(salt) > k || L4W_SIZE(msg) > (size_t)UINT32_MAX - 128U) return l4w_empty();
  uint32_t modBits = l4w_bits(L4W_PTR(n), k), eBits = l4w_bits(L4W_PTR(e), L4W_SIZE(e));
  if (eBits == 0 || (L4W_SIZE(e) - 1) * 8 >= eBits) return l4w_empty();
  uint8_t *dk = (uint8_t *)calloc(k, 1);
  if (!dk) return l4w_empty();
  memcpy(dk + (k - dl), L4W_PTR(d), dl);
  lean_obj_res out = l4w_fresh(k);
  int ok = l4wc_rsapss_sign((uint32_t)a, L4W_PTR(n), (uint32_t)k, modBits, L4W_PTR(e), eBits, dk, L4W_PTR(salt),
                            (uint32_t)L4W_SIZE(salt), L4W_PTR(msg), (uint32_t)L4W_SIZE(msg), L4W_PTR(out));
  Lib_Memzero0_memzero0(dk, (uint64_t)k);
  free(dk);
  if (!ok) return l4w_refuse(out);
  return out;
}
/* RSASSA-PSS verify (RFC 8017 §8.1.2) by Hacl_RSAPSS_rsapss_verify. A signature that is
 * not |n| octets verifies false. */
LEAN_EXPORT uint8_t l4_web_hacl_rsapss_verify(uint8_t alg, b_lean_obj_arg n, b_lean_obj_arg e, size_t sl,
                                             b_lean_obj_arg sig, b_lean_obj_arg msg) {
  int a = l4w_pss_alg(alg);
  size_t k = L4W_SIZE(n);
  if (a < 0 || !l4w_rsa_mod_ok(n) || L4W_SIZE(e) == 0 || L4W_SIZE(e) > k || L4W_SIZE(sig) != k ||
      L4W_SIZE(msg) > (size_t)UINT32_MAX - 128U) return 0;
  if (sl > k) return 0;
  uint32_t modBits = l4w_bits(L4W_PTR(n), k), eBits = l4w_bits(L4W_PTR(e), L4W_SIZE(e));
  if (eBits == 0 || (L4W_SIZE(e) - 1) * 8 >= eBits) return 0;
  return l4wc_rsapss_verify((uint32_t)a, L4W_PTR(n), (uint32_t)k, modBits, L4W_PTR(e), eBits, (uint32_t)sl,
                            L4W_PTR(sig), L4W_PTR(msg), (uint32_t)L4W_SIZE(msg)) ? 1 : 0;
}

/* ---- Linked? --------------------------------------------------------------------------
 * 1 when the core is HACL* (hacl_webcrypto_core.c); 0 with hacl_webcrypto_nohacl.c (the
 * Hub's engine, where the browser does the primitives). */
LEAN_EXPORT uint8_t l4_web_hacl_linked(lean_obj_arg u) {
  (void)u;
  return (uint8_t)l4wc_linked();
}

/* ---- Erasure ----------------------------------------------------------------------
 * `WebHacl.wipe`: the argument is OWNED. When this is its only reference (the key store
 * dropped its copy first) its bytes are zeroed in place before it is freed; a shared
 * array cannot be zeroed without changing another holder's value, so it is only
 * released. The answer is the array's size in both cases (the Lean specification of
 * `wipe` is `b.size`); `l4_web_hacl_wiped` counts the bytes actually zeroed, for tests. */
static uint64_t l4w_wiped_total = 0;
LEAN_EXPORT lean_obj_res l4_web_hacl_wipe(lean_obj_arg b) {
  size_t n = L4W_SIZE(b);
  if (lean_is_exclusive(b) && n) {
    Lib_Memzero0_memzero0(L4W_PTR(b), (uint64_t)n);
    l4w_wiped_total += n;
  }
  lean_dec_ref(b);
  return lean_usize_to_nat(n);
}
/* `WebHacl.zeroNow`, for a session's key store as the session ends (WebApi.wipeAll): the
 * bytes are zeroed in place whatever the reference count, because every holder is being
 * dropped with the session (the store, a structuredClone copy in the same store, the
 * session's waiting answers). A persistent object (a compiled-in constant) is left alone.
 * Answers the size. Never used on a store that lives on: there the reference-counted
 * `wipe` is used (a dropped key, WebApi.dropKey). */
LEAN_EXPORT lean_obj_res l4_web_hacl_zero_now(b_lean_obj_arg b) {
  size_t n = L4W_SIZE(b);
  if (n && !lean_is_persistent(b)) {
    Lib_Memzero0_memzero0(L4W_PTR(b), (uint64_t)n);
    l4w_wiped_total += n;
  }
  return lean_usize_to_nat(n);
}

/* `wipedSoFar : BaseIO Nat`: Lean 4.33 passes an IO action's extern no world argument
 * (its emitted prototype is `l4_web_hacl_wiped()`), so this takes none; a parameter here
 * made wasm-ld's signatures disagree and every call trap (core Wasm build, 2026-11-09). */
LEAN_EXPORT lean_obj_res l4_web_hacl_wiped(void) {
  return lean_io_result_mk_ok(lean_uint64_to_nat(l4w_wiped_total));
}
