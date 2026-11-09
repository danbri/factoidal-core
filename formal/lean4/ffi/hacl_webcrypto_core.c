/* hacl_webcrypto_core.c — the HACL* calls of the web engine's crypto boundary, over raw
 * buffers (no Lean objects). ffi/hacl_webcrypto.c makes every check and every allocation
 * and then calls these; each body here is one HACL* call, or for RSA the bignum
 * conversions around one.
 *
 * Natively this file is linked into the engine with the HACL* units. On the Hub it is
 * compiled with the HACL* units into a separate module, hacl-web.wasm, which the engine
 * loads the first time a page uses crypto.subtle (ffi/hacl_webcrypto_lazy.c and
 * labs/demos/foafnaut/hacl_web_lazy.js): pages without crypto load no HACL* code.
 * Record: docs/designissues/2026-11-09-hacl-web-crypto.md, "Lazy HACL* on the Hub".
 *
 * Every pointer argument is valid for the length the caller checked; outputs never
 * overlap inputs (the caller allocates them fresh). Answers: 1 success, 0 refusal.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Hash_SHA1.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_HMAC.h"
#include "Hacl_Ed25519.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_P256.h"
#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "Hacl_Bignum64.h"
#include "Hacl_RSAPSS.h"
#include "lib_memzero0.h"
#include "hacl_webcrypto_core.h"

int l4wc_linked(void) { return Hacl_Hash_SHA2_hash_256 != 0; }

int l4wc_hash(uint32_t alg, uint8_t *msg, uint32_t len, uint8_t *out) {
  switch (alg) {
    case 1: Hacl_Hash_SHA1_hash(out, msg, len); return 1;
    case 2: Hacl_Hash_SHA2_hash_256(out, msg, len); return 1;
    case 3: Hacl_Hash_SHA2_hash_384(out, msg, len); return 1;
    case 4: Hacl_Hash_SHA2_hash_512(out, msg, len); return 1;
    default: return 0;
  }
}

int l4wc_hmac(uint32_t alg, uint8_t *key, uint32_t klen, uint8_t *msg, uint32_t mlen, uint8_t *out) {
  switch (alg) {
    case 1: Hacl_HMAC_compute_sha1(out, key, klen, msg, mlen); return 1;
    case 2: Hacl_HMAC_compute_sha2_256(out, key, klen, msg, mlen); return 1;
    case 3: Hacl_HMAC_compute_sha2_384(out, key, klen, msg, mlen); return 1;
    case 4: Hacl_HMAC_compute_sha2_512(out, key, klen, msg, mlen); return 1;
    default: return 0;
  }
}

int l4wc_ed25519_public(uint8_t *sk, uint8_t *out) { Hacl_Ed25519_secret_to_public(out, sk); return 1; }
int l4wc_ed25519_sign(uint8_t *sk, uint8_t *msg, uint32_t mlen, uint8_t *out) {
  Hacl_Ed25519_sign(out, sk, mlen, msg); return 1;
}
int l4wc_ed25519_verify(uint8_t *pk, uint8_t *msg, uint32_t mlen, uint8_t *sig) {
  return Hacl_Ed25519_verify(pk, mlen, msg, sig) ? 1 : 0;
}
int l4wc_x25519_public(uint8_t *sk, uint8_t *out) { Hacl_Curve25519_51_secret_to_public(out, sk); return 1; }
int l4wc_x25519(uint8_t *sk, uint8_t *pk, uint8_t *out) { return Hacl_Curve25519_51_ecdh(out, sk, pk) ? 1 : 0; }

int l4wc_p256_public(uint8_t *sk, uint8_t *out) { return Hacl_P256_dh_initiator(out, sk) ? 1 : 0; }
int l4wc_p256_valid_public(uint8_t *xy) { return Hacl_P256_validate_public_key(xy) ? 1 : 0; }
int l4wc_p256_valid_private(uint8_t *sk) { return Hacl_P256_validate_private_key(sk) ? 1 : 0; }
int l4wc_p256_decompress(uint8_t *c, uint8_t *out) { return Hacl_P256_compressed_to_raw(c, out) ? 1 : 0; }
int l4wc_p256_sign(uint8_t *sk, uint8_t *e, uint8_t *nonce, uint8_t *out) {
  return Hacl_P256_ecdsa_sign_p256_without_hash(out, 32U, e, sk, nonce) ? 1 : 0;
}
int l4wc_p256_verify(uint8_t *xy, uint8_t *e, uint8_t *rs) {
  return Hacl_P256_ecdsa_verif_without_hash(32U, e, xy, rs, rs + 32) ? 1 : 0;
}
/* The x-coordinate of d·Q; the whole point stays on this stack and is zeroed. */
int l4wc_p256_ecdh(uint8_t *xy, uint8_t *sk, uint8_t *out) {
  uint8_t point[64];
  int ok = Hacl_P256_dh_responder(point, xy, sk) ? 1 : 0;
  if (ok) memcpy(out, point, 32);
  Lib_Memzero0_memzero0(point, sizeof point);
  return ok;
}

void l4wc_chacha_seal(uint8_t *key, uint8_t *nonce, uint8_t *aad, uint32_t alen, uint8_t *plain, uint32_t plen,
                      uint8_t *out) {
  Hacl_AEAD_Chacha20Poly1305_encrypt(out, out + plen, plain, plen, aad, alen, key, nonce);
}
/* `ct` holds plen octets of ciphertext and then the 16-octet tag. 1 when the tag holds. */
int l4wc_chacha_open(uint8_t *key, uint8_t *nonce, uint8_t *aad, uint32_t alen, uint8_t *ct, uint32_t plen,
                     uint8_t *out) {
  return Hacl_AEAD_Chacha20Poly1305_decrypt(out, ct, plen, aad, alen, key, nonce, ct + plen) == 0U ? 1 : 0;
}

/* ---- RSA ---------------------------------------------------------------------------- */
static uint64_t *l4wc_bn(const uint8_t *x, uint32_t xl, uint32_t len) {
  uint8_t *buf = (uint8_t *)calloc(len, 1);
  if (!buf) return NULL;
  memcpy(buf + (len - xl), x, xl);
  uint64_t *bn = Hacl_Bignum64_new_bn_from_bytes_be(len, buf);
  Lib_Memzero0_memzero0(buf, (uint64_t)len);
  free(buf);
  return bn;
}
static void l4wc_free_bn(uint64_t *bn, uint32_t limbs) {
  if (bn) { Lib_Memzero0_memzero0(bn, (uint64_t)limbs * 8U); free(bn); }
}
/* x^ex mod n into out (k octets each). `secret`: constant time, ex padded to k octets and
 * its bit length taken as 8k; else variable time over ebits bits. */
int l4wc_modexp(uint8_t *n, uint32_t k, uint8_t *ex, uint32_t exlen, uint32_t ebits, uint8_t *x, uint32_t secret,
                uint8_t *out) {
  uint32_t limbs = k / 8;
  uint32_t elen = secret ? k : ((exlen + 7) / 8) * 8;
  uint64_t *bn = l4wc_bn(n, k, k), *ba = l4wc_bn(x, k, k), *be = l4wc_bn(ex, exlen, elen);
  uint64_t *br = (uint64_t *)calloc(limbs, 8);
  int ok = 0;
  if (bn && ba && be && br) {
    ok = (secret ? Hacl_Bignum64_mod_exp_consttime(limbs, bn, ba, 8 * k, be, br)
                 : Hacl_Bignum64_mod_exp_vartime(limbs, bn, ba, ebits, be, br)) ? 1 : 0;
    if (ok) Hacl_Bignum64_bn_to_bytes_be(k, br, out);
  }
  l4wc_free_bn(bn, limbs); l4wc_free_bn(ba, limbs); l4wc_free_bn(be, elen / 8); l4wc_free_bn(br, limbs);
  return ok;
}
/* RSASSA-PSS sign: `a` is HACL*'s Spec_Hash_Definitions code; d is padded to k octets. */
int l4wc_rsapss_sign(uint32_t a, uint8_t *n, uint32_t k, uint32_t modBits, uint8_t *e, uint32_t eBits, uint8_t *dk,
                     uint8_t *salt, uint32_t slen, uint8_t *msg, uint32_t mlen, uint8_t *out) {
  uint64_t *skey = Hacl_RSAPSS_new_rsapss_load_skey(modBits, eBits, 8 * k, n, e, dk);
  if (!skey) return 0;
  uint32_t skeyLimbs = 2 * ((modBits - 1) / 64 + 1) + (eBits - 1) / 64 + 1 + k / 8;
  int ok = Hacl_RSAPSS_rsapss_sign((Spec_Hash_Definitions_hash_alg)a, modBits, eBits, 8 * k, skey, slen, salt, mlen, msg,
                                   out) ? 1 : 0;
  l4wc_free_bn(skey, skeyLimbs);
  return ok;
}
int l4wc_rsapss_verify(uint32_t a, uint8_t *n, uint32_t k, uint32_t modBits, uint8_t *e, uint32_t eBits, uint32_t slen,
                       uint8_t *sig, uint8_t *msg, uint32_t mlen) {
  uint64_t *pkey = Hacl_RSAPSS_new_rsapss_load_pkey(modBits, eBits, n, e);
  if (!pkey) return 0;
  int ok = Hacl_RSAPSS_rsapss_verify((Spec_Hash_Definitions_hash_alg)a, modBits, eBits, pkey, slen, k, sig, mlen, msg)
           ? 1 : 0;
  free(pkey);
  return ok;
}
