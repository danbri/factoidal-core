/* hacl_webcrypto_core.h — the raw HACL* calls of the web engine's crypto boundary
 * (hacl_webcrypto_core.c natively, hacl-web.wasm through hacl_webcrypto_lazy.c on the Hub). */
#ifndef L4_HACL_WEBCRYPTO_CORE_H
#define L4_HACL_WEBCRYPTO_CORE_H
#include <stdint.h>
int l4wc_hash(uint32_t alg, uint8_t *msg, uint32_t len, uint8_t *out);
int l4wc_hmac(uint32_t alg, uint8_t *key, uint32_t klen, uint8_t *msg, uint32_t mlen, uint8_t *out);
int l4wc_ed25519_public(uint8_t *sk, uint8_t *out);
int l4wc_ed25519_sign(uint8_t *sk, uint8_t *msg, uint32_t mlen, uint8_t *out);
int l4wc_ed25519_verify(uint8_t *pk, uint8_t *msg, uint32_t mlen, uint8_t *sig);
int l4wc_x25519_public(uint8_t *sk, uint8_t *out);
int l4wc_x25519(uint8_t *sk, uint8_t *pk, uint8_t *out);
int l4wc_p256_public(uint8_t *sk, uint8_t *out);
int l4wc_p256_valid_public(uint8_t *xy);
int l4wc_p256_valid_private(uint8_t *sk);
int l4wc_p256_decompress(uint8_t *c, uint8_t *out);
int l4wc_p256_sign(uint8_t *sk, uint8_t *e, uint8_t *nonce, uint8_t *out);
int l4wc_p256_verify(uint8_t *xy, uint8_t *e, uint8_t *rs);
int l4wc_p256_ecdh(uint8_t *xy, uint8_t *sk, uint8_t *out);
void l4wc_chacha_seal(uint8_t *key, uint8_t *nonce, uint8_t *aad, uint32_t alen, uint8_t *plain, uint32_t plen,
                      uint8_t *out);
int l4wc_chacha_open(uint8_t *key, uint8_t *nonce, uint8_t *aad, uint32_t alen, uint8_t *ct, uint32_t plen,
                     uint8_t *out);
int l4wc_modexp(uint8_t *n, uint32_t k, uint8_t *ex, uint32_t exlen, uint32_t ebits, uint8_t *x, uint32_t secret,
                uint8_t *out);
int l4wc_rsapss_sign(uint32_t a, uint8_t *n, uint32_t k, uint32_t modBits, uint8_t *e, uint32_t eBits, uint8_t *dk,
                     uint8_t *salt, uint32_t slen, uint8_t *msg, uint32_t mlen, uint8_t *out);
int l4wc_rsapss_verify(uint32_t a, uint8_t *n, uint32_t k, uint32_t modBits, uint8_t *e, uint32_t eBits, uint32_t slen,
                       uint8_t *sig, uint8_t *msg, uint32_t mlen);
#endif
