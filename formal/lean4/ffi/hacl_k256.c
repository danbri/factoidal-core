/* hacl_k256.c — Lean 4 <-> C binding for the vendored HACL* secp256k1
 * ECDSA primitive (third_party/hacl/, Apache-2.0 / MIT, hacl-star commit
 * f557259007db9933442dde10aa995c1b00bd3446 — see third_party/hacl/PROVENANCE.md).
 * Realises the `@[extern]` opaques of L4Factoidal/Crypto/K256Native.lean.
 *
 * Owner, 2026-11-27, verbatim: "HACL* is both approved and PREFERED over our
 * own (crazy yolo roll your own etc.) Lean hackery." and, on the secp256k1
 * signer for Ethereum, "Do it."
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md.  There is no field,
 * group or scalar arithmetic in this file.  Every operation on a secret is
 * one HACL* call:
 *   - the private-key check:            Hacl_K256_ECDSA_is_private_key_valid
 *   - the public key:                   Hacl_K256_ECDSA_secret_to_public
 *   - the RFC 6979 nonce (section 3.3: HMAC_DRBG with SHA-256, entropy input
 *     int2octets(x), nonce bits2octets(h1), no personalization string):
 *                                       Hacl_HMAC_DRBG_instantiate / _generate
 *   - the signature (r, s), not low-S:  Hacl_K256_ECDSA_ecdsa_sign_hashed_msg
 *   - R = k G, for the recovery id:     Hacl_EC_K256_point_mul / _point_store
 *   - low-S normalisation (EIP-2):      Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize
 * The logic here is length checks, the RFC 6979 retry loop, and two decisions
 * on values that are PUBLIC once the signature exists: whether x(R) equals r,
 * and the parity of y(R).  L4_DECLASSIFY marks the points where a value
 * derived from a secret becomes public.  It is empty in the library; the
 * Valgrind check (tests/ct/) defines it as VALGRIND_MAKE_MEM_DEFINED, so that
 * every other branch or address that depends on the key is reported.
 *
 * RFC 6979 retry (section 3.2 step h.3): K = HMAC_K(V || 0x00), V = HMAC_K(V),
 * then the next candidate is HMAC_K(V).  HMAC_DRBG generate with no additional
 * input ends with exactly that update (SP 800-90A section 10.1.2.2 and 10.1.2.5),
 * so each _generate call gives the next RFC 6979 candidate.
 *
 * The hash argument z must be h1 mod n, 32 bytes big-endian (the Lean caller
 * reduces it; the hash is public).  With qlen = hlen = 256, bits2octets(h1) is
 * exactly that value, and ECDSA signs the same integer.
 *
 * Boundary contract:
 *   l4_hacl_k256_private_key_valid(sk[32])            -> 0 / 1
 *   l4_hacl_k256_secret_to_public(sk[32])             -> x||y [64] or empty
 *   l4_hacl_k256_sign_recoverable(z[32], sk[32])      -> r||s||recid [65] or empty
 *   l4_hacl_k256_verify(z[32], pub[64], sig[64])      -> 0 / 1 (low-S only)
 * Every length refusal and every HACL* refusal is 0 or the empty array.  The
 * signer also refuses when x(R) >= n (probability about 2^-128), because an
 * Ethereum v cannot express that recovery id.
 *
 * Memory: every Lean argument is BORROWED (`@&`).  The nonce, R and the DRBG
 * state are erased with Lib_Memzero0_memzero0 before return.  Copies of the
 * private key in the Lean heap are not erased (Lean gives no such control).
 */
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_EC_K256.h"
#include "Hacl_HMAC_DRBG.h"
#include "Hacl_K256_ECDSA.h"
#include "lib_memzero0.h"

#ifndef L4_DECLASSIFY
#define L4_DECLASSIFY(p, n) ((void)(p), (void)(n))
#endif

#define L4_K256_MAX_CANDIDATES 16

bool l4_k256_sign_recoverable_core(uint8_t out[65], uint8_t z[32], uint8_t sk[32]) {
  uint8_t valid = (uint8_t)Hacl_K256_ECDSA_is_private_key_valid(sk);
  L4_DECLASSIFY(&valid, 1); /* a refused key is a public refusal */
  if (!valid) return false;

  uint8_t no_input[1] = {0};
  Hacl_HMAC_DRBG_state st = Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_SHA2_256);
  if (st.k == NULL || st.v == NULL || st.reseed_counter == NULL) return false;
  Hacl_HMAC_DRBG_instantiate(Spec_Hash_Definitions_SHA2_256, st, 32, sk, 32, z, 0, no_input);

  uint8_t k[32];
  uint8_t sig[64];
  uint8_t r_raw[64];
  uint64_t g[15];
  uint64_t r_pt[15];
  bool done = false;
  for (int i = 0; i < L4_K256_MAX_CANDIDATES && !done; i++) {
    uint8_t gen = (uint8_t)Hacl_HMAC_DRBG_generate(Spec_Hash_Definitions_SHA2_256, k, st, 32, 0, no_input);
    L4_DECLASSIFY(&gen, 1);
    if (!gen) break;
    uint8_t signed_ok = (uint8_t)Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(sig, z, sk, k);
    /* Whether a candidate is in [1, n-1] and gives r, s != 0 is the public
     * fact RFC 6979 retries on. */
    L4_DECLASSIFY(&signed_ok, 1);
    if (!signed_ok) continue;
    Hacl_EC_K256_mk_base_point(g);
    Hacl_EC_K256_point_mul(k, g, r_pt);
    Hacl_EC_K256_point_store(r_pt, r_raw);
    L4_DECLASSIFY(r_raw, 64); /* R is public: r is its x, v is its y parity */
    L4_DECLASSIFY(sig, 64);   /* the signature is the output */
    if (memcmp(r_raw, sig, 32) != 0) break; /* x(R) >= n: refuse */
    uint8_t recid = (uint8_t)(r_raw[63] & 1u);
    if (!Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(sig)) {
      if (!Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(sig)) break;
      recid ^= 1u; /* s -> n - s negates R */
    }
    memcpy(out, sig, 64);
    out[64] = recid;
    done = true;
  }

  Lib_Memzero0_memzero0(k, sizeof k);
  Lib_Memzero0_memzero0(r_pt, sizeof r_pt);
  Lib_Memzero0_memzero0(st.k, 32);
  Lib_Memzero0_memzero0(st.v, 32);
  Hacl_HMAC_DRBG_free(Spec_Hash_Definitions_SHA2_256, st);
  return done;
}

#ifndef L4_K256_NO_LEAN
#include <lean/lean.h>

static lean_obj_res l4_k256_empty_bytes(void) { return lean_alloc_sarray(1, 0, 0); }

static lean_obj_res l4_k256_bytes(const uint8_t *src, size_t n) {
  lean_obj_res out = lean_alloc_sarray(1, n, n);
  memcpy(lean_sarray_cptr(out), src, n);
  return out;
}

LEAN_EXPORT uint8_t l4_hacl_k256_private_key_valid(b_lean_obj_arg sk) {
  if (lean_sarray_size(sk) != 32) return 0;
  return Hacl_K256_ECDSA_is_private_key_valid(lean_sarray_cptr(sk)) ? 1 : 0;
}

LEAN_EXPORT lean_obj_res l4_hacl_k256_secret_to_public(b_lean_obj_arg sk) {
  if (lean_sarray_size(sk) != 32) return l4_k256_empty_bytes();
  uint8_t pub[64];
  if (!Hacl_K256_ECDSA_secret_to_public(pub, lean_sarray_cptr(sk))) return l4_k256_empty_bytes();
  return l4_k256_bytes(pub, 64);
}

LEAN_EXPORT lean_obj_res l4_hacl_k256_sign_recoverable(b_lean_obj_arg z, b_lean_obj_arg sk) {
  if (lean_sarray_size(z) != 32 || lean_sarray_size(sk) != 32) return l4_k256_empty_bytes();
  uint8_t out[65];
  if (!l4_k256_sign_recoverable_core(out, lean_sarray_cptr(z), lean_sarray_cptr(sk)))
    return l4_k256_empty_bytes();
  return l4_k256_bytes(out, 65);
}

LEAN_EXPORT uint8_t l4_hacl_k256_verify(b_lean_obj_arg z, b_lean_obj_arg pub, b_lean_obj_arg sig) {
  if (lean_sarray_size(z) != 32 || lean_sarray_size(pub) != 64 || lean_sarray_size(sig) != 64) return 0;
  return Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
             lean_sarray_cptr(z), lean_sarray_cptr(pub), lean_sarray_cptr(sig)) ? 1 : 0;
}
#endif
