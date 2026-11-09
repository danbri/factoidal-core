/* hacl_webcrypto_nohacl.c — the `l4wc_*` core for an engine that links no HACL*: the Hub's
 * web-render.wasm, where crypto.subtle's primitives are the browser's own (WebApi host
 * mode, labs/demos/foafnaut/crypto_host.mjs). Every primitive refuses (0), so a call that
 * reached one would be refused by hacl_webcrypto.c like any HACL* refusal; Lean does not
 * reach them: `l4wc_linked` answers 0 and the engine then offers crypto.subtle only in host
 * mode. The hashes and HMAC behind getRandomValues fall back to Lean's own (WebHacl.hashFast).
 * Also the two RSA externs of Crypto/RsaNative and Crypto/RsaOaep, which the web engine's
 * Lean names but never calls: they refuse (an empty array).
 * Record: docs/designissues/2026-11-09-hacl-web-crypto.md, "The Hub". */
#include <lean/lean.h>
#include <stdint.h>
#include "hacl_webcrypto_core.h"

int l4wc_linked(void) { return 0; }
int l4wc_hash(uint32_t a, uint8_t *m, uint32_t l, uint8_t *o) { (void)a; (void)m; (void)l; (void)o; return 0; }
int l4wc_hmac(uint32_t a, uint8_t *k, uint32_t kl, uint8_t *m, uint32_t ml, uint8_t *o) {
  (void)a; (void)k; (void)kl; (void)m; (void)ml; (void)o; return 0;
}
int l4wc_ed25519_public(uint8_t *sk, uint8_t *o) { (void)sk; (void)o; return 0; }
int l4wc_ed25519_sign(uint8_t *sk, uint8_t *m, uint32_t ml, uint8_t *o) { (void)sk; (void)m; (void)ml; (void)o; return 0; }
int l4wc_ed25519_verify(uint8_t *pk, uint8_t *m, uint32_t ml, uint8_t *s) { (void)pk; (void)m; (void)ml; (void)s; return 0; }
int l4wc_x25519_public(uint8_t *sk, uint8_t *o) { (void)sk; (void)o; return 0; }
int l4wc_x25519(uint8_t *sk, uint8_t *pk, uint8_t *o) { (void)sk; (void)pk; (void)o; return 0; }
int l4wc_p256_public(uint8_t *sk, uint8_t *o) { (void)sk; (void)o; return 0; }
int l4wc_p256_valid_public(uint8_t *xy) { (void)xy; return 0; }
int l4wc_p256_valid_private(uint8_t *sk) { (void)sk; return 0; }
int l4wc_p256_decompress(uint8_t *c, uint8_t *o) { (void)c; (void)o; return 0; }
int l4wc_p256_sign(uint8_t *sk, uint8_t *e, uint8_t *n, uint8_t *o) { (void)sk; (void)e; (void)n; (void)o; return 0; }
int l4wc_p256_verify(uint8_t *xy, uint8_t *e, uint8_t *rs) { (void)xy; (void)e; (void)rs; return 0; }
int l4wc_p256_ecdh(uint8_t *xy, uint8_t *sk, uint8_t *o) { (void)xy; (void)sk; (void)o; return 0; }
void l4wc_chacha_seal(uint8_t *k, uint8_t *n, uint8_t *a, uint32_t al, uint8_t *p, uint32_t pl, uint8_t *o) {
  (void)k; (void)n; (void)a; (void)al; (void)p; (void)pl; (void)o;
}
int l4wc_chacha_open(uint8_t *k, uint8_t *n, uint8_t *a, uint32_t al, uint8_t *c, uint32_t pl, uint8_t *o) {
  (void)k; (void)n; (void)a; (void)al; (void)c; (void)pl; (void)o; return 0;
}
int l4wc_modexp(uint8_t *n, uint32_t k, uint8_t *e, uint32_t el, uint32_t eb, uint8_t *x, uint32_t s, uint8_t *o) {
  (void)n; (void)k; (void)e; (void)el; (void)eb; (void)x; (void)s; (void)o; return 0;
}
int l4wc_rsapss_sign(uint32_t a, uint8_t *n, uint32_t k, uint32_t mb, uint8_t *e, uint32_t eb, uint8_t *d, uint8_t *s,
                     uint32_t sl, uint8_t *m, uint32_t ml, uint8_t *o) {
  (void)a; (void)n; (void)k; (void)mb; (void)e; (void)eb; (void)d; (void)s; (void)sl; (void)m; (void)ml; (void)o; return 0;
}
int l4wc_rsapss_verify(uint32_t a, uint8_t *n, uint32_t k, uint32_t mb, uint8_t *e, uint32_t eb, uint32_t sl, uint8_t *s,
                       uint8_t *m, uint32_t ml) {
  (void)a; (void)n; (void)k; (void)mb; (void)e; (void)eb; (void)sl; (void)s; (void)m; (void)ml; return 0;
}
LEAN_EXPORT lean_obj_res l4_hacl_rsa_public_op(b_lean_obj_arg n, b_lean_obj_arg e, b_lean_obj_arg s) {
  (void)n; (void)e; (void)s; return lean_alloc_sarray(1, 0, 0);
}
LEAN_EXPORT lean_obj_res l4_hacl_rsa_private_op(b_lean_obj_arg n, b_lean_obj_arg d, b_lean_obj_arg c) {
  (void)n; (void)d; (void)c; return lean_alloc_sarray(1, 0, 0);
}
