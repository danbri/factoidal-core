/* hacl_webcrypto_fuzz.c: hostile lengths and contents through every entry point of the
 * web engine's HACL* boundary (formal/lean4/ffi/hacl_webcrypto.c, its core and HACL*),
 * built natively with AddressSanitizer and UndefinedBehaviorSanitizer
 * (tests/crypto/run-fuzz.sh). Record docs/designissues/2026-11-09-crypto-boundary-security.md,
 * "Fuzzing the shim".
 *
 * Lean's runtime is NOT linked: the few runtime functions lean.h calls are defined below
 * over malloc and free, so every Lean array the shim allocates (each output) is an ASan
 * allocation with redzones, and a write past an output, a read past an input, a leak or a
 * double free is reported. Each call's answer is checked to be a valid size (the size the
 * primitive writes, or the empty refusal), and the inputs unchanged (borrowed arrays are
 * read only).
 *
 *   tests/crypto/run-fuzz.sh [ITERATIONS] [SEED]
 */
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* ---- the runtime functions lean.h needs, over malloc ------------------------------- */
/* Live Lean objects: every one the shim allocates must be freed (or answered and freed
 * here), so a leaked object shows (macOS's ASan has no leak checker). */
static long live = 0;
void *mi_malloc_small(size_t n) { live++; return malloc(n); }
void *mi_malloc(size_t n) { live++; return malloc(n); }
void mi_free(void *p) { live--; free(p); }
lean_object *lean_alloc_object(size_t n) { live++; return (lean_object *)malloc(n); }
void lean_inc_heartbeat(void) {}
void lean_internal_panic_overflow(void) { fprintf(stderr, "overflow\n"); abort(); }
void lean_notify_assert(const char *f, int l, const char *c) { fprintf(stderr, "%s:%d: %s\n", f, l, c); abort(); }
void lean_internal_panic_out_of_memory(void) { fprintf(stderr, "out of memory\n"); abort(); }
void lean_dec_ref_cold(lean_object *o) { if (o->m_rc == 1) { live--; free(o); } else o->m_rc--; }
lean_obj_res lean_big_usize_to_nat(size_t n) { (void)n; abort(); }
lean_obj_res lean_big_uint64_to_nat(uint64_t n) { (void)n; abort(); }

lean_obj_res l4_web_hacl_hash(uint8_t, b_lean_obj_arg);
lean_obj_res l4_web_hacl_hmac(uint8_t, b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_ct_eq(b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_ed25519_public(b_lean_obj_arg);
lean_obj_res l4_web_hacl_ed25519_sign(b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_ed25519_verify(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_x25519_public(b_lean_obj_arg);
lean_obj_res l4_web_hacl_x25519(b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_public(b_lean_obj_arg);
uint8_t l4_web_hacl_p256_valid_public(b_lean_obj_arg);
uint8_t l4_web_hacl_p256_valid_private(b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_decompress(b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_sign(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_p256_verify(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_ecdh(b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_chachapoly_seal(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_chachapoly_open(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_rsa_public(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_rsa_private(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_rsapss_sign(uint8_t, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_rsapss_verify(uint8_t, b_lean_obj_arg, b_lean_obj_arg, size_t, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_wipe(lean_obj_arg);

/* ---- hostile inputs ------------------------------------------------------------------ */
static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* Lengths at and around every boundary the entry points check. */
static const size_t LENS[] = {0, 1, 2, 11, 12, 13, 15, 16, 17, 19, 20, 21, 31, 32, 33, 47, 48, 49, 63, 64, 65, 66,
  96, 127, 128, 129, 136, 255, 256, 257, 383, 384, 511, 512, 513, 520, 1000, 4096, 65536};
#define NLENS (sizeof LENS / sizeof LENS[0])
static size_t a_len(void) {
  uint64_t r = rnd() % 16;
  if (r < 12) return LENS[rnd() % NLENS];
  return rnd() % (r == 15 ? (1u << 20) : 2048);
}
static lean_object *arr(size_t n) {
  lean_object *o = lean_alloc_sarray(1, n, n);
  uint8_t *p = lean_sarray_cptr(o);
  switch (rnd() % 6) {
    case 0: memset(p, 0, n); break;
    case 1: memset(p, 0xff, n); break;
    case 2: for (size_t i = 0; i < n; i++) p[i] = (uint8_t)(i == 0 ? (rnd() % 2 ? 2 : 4) : rnd()); break;
    case 3: for (size_t i = 0; i < n; i++) p[i] = (uint8_t)(i == 0 ? 0 : rnd()); break;  /* leading zero */
    case 4: for (size_t i = 0; i < n; i++) p[i] = (uint8_t)(rnd() | (i + 1 == n ? 1 : 0)); break;  /* odd */
    default: for (size_t i = 0; i < n; i++) p[i] = (uint8_t)rnd(); break;
  }
  return o;
}
static lean_object *arr_len(void) { return arr(a_len()); }

static long calls = 0, bad = 0;
static uint32_t sum(lean_object *o) {
  uint32_t h = 2166136261u; size_t n = lean_sarray_size(o); const uint8_t *p = lean_sarray_cptr(o);
  for (size_t i = 0; i < n; i++) h = (h ^ p[i]) * 16777619u;
  return h ^ (uint32_t)n;
}
/* An answer must be empty (a refusal) or of one of the sizes the primitive writes. */
static void answer(const char *what, lean_object *r, size_t ok1, size_t ok2) {
  size_t n = lean_sarray_size(r);
  calls++;
  if (n != 0 && n != ok1 && n != ok2) { bad++; fprintf(stderr, "%s: answer of %zu bytes\n", what, n); }
  lean_dec_ref(r);
}
#define KEEP(x) uint32_t s_##x = sum(x)
#define SAME(x) do { if (sum(x) != s_##x) { bad++; fprintf(stderr, "input " #x " changed\n"); } } while (0)

/* An argument of the size the entry point takes most of the time, and a hostile one
 * otherwise, so that calls get past the length checks into HACL*. */
static lean_object *args[6];
static uint32_t sums[6];
static int nargs;
static lean_object *A(size_t want) {
  lean_object *o = arr(rnd() % 4 ? want : a_len());
  sums[nargs] = sum(o); args[nargs++] = o;
  return o;
}
static size_t rsa_len(void) { size_t ks[] = {128, 136, 256, 384, 512}; return ks[rnd() % 5]; }

int main(int argc, char **argv) {
  long iters = argc > 1 ? atol(argv[1]) : 20000;
  rs = argc > 2 ? strtoull(argv[2], 0, 10) : 0x9e3779b97f4a7c15ull;
  if (rs == 0) rs = 1;
  for (long it = 0; it < iters; it++) {
    nargs = 0;
    uint8_t alg = (uint8_t)(rnd() % 4 ? 1 + rnd() % 4 : rnd() % 8);
    size_t hs[] = {0, 20, 32, 48, 64, 0, 0, 0}, h = hs[alg];
    size_t k = rsa_len();
    switch (rnd() % 21) {
      case 0: answer("hash", l4_web_hacl_hash(alg, A(a_len())), h, h); break;
      case 1: answer("hmac", l4_web_hacl_hmac(alg, A(a_len()), A(a_len())), h, h); break;
      case 2: calls++; (void)l4_web_hacl_ct_eq(A(32), A(32)); break;
      case 3: answer("ed25519_public", l4_web_hacl_ed25519_public(A(32)), 32, 32); break;
      case 4: answer("ed25519_sign", l4_web_hacl_ed25519_sign(A(32), A(a_len())), 64, 64); break;
      case 5: calls++; (void)l4_web_hacl_ed25519_verify(A(32), A(a_len()), A(64)); break;
      case 6: answer("x25519_public", l4_web_hacl_x25519_public(A(32)), 32, 32); break;
      case 7: answer("x25519", l4_web_hacl_x25519(A(32), A(32)), 32, 32); break;
      case 8: answer("p256_public", l4_web_hacl_p256_public(A(32)), 64, 64); break;
      case 9: calls++; (void)l4_web_hacl_p256_valid_public(A(64)); (void)l4_web_hacl_p256_valid_private(A(32)); break;
      case 10: answer("p256_decompress", l4_web_hacl_p256_decompress(A(33)), 64, 64); break;
      case 11: answer("p256_sign", l4_web_hacl_p256_sign(A(32), A(32), A(32)), 64, 64); break;
      case 12: calls++; (void)l4_web_hacl_p256_verify(A(64), A(32), A(64)); break;
      case 13: answer("p256_ecdh", l4_web_hacl_p256_ecdh(A(64), A(32)), 32, 32); break;
      case 14: { lean_object *kk = A(32), *n = A(12), *ad = A(a_len()), *p = A(a_len());
        answer("chacha_seal", l4_web_hacl_chachapoly_seal(kk, n, ad, p), lean_sarray_size(p) + 16, 0); break; }
      case 15: { lean_object *kk = A(32), *n = A(12), *ad = A(a_len()), *c = A(16 + a_len()); size_t cn = lean_sarray_size(c);
        answer("chacha_open", l4_web_hacl_chachapoly_open(kk, n, ad, c), 1, cn >= 16 ? cn - 15 : 1); break; }
      case 16: { lean_object *n = A(k); answer("rsa_public", l4_web_hacl_rsa_public(n, A(rnd() % 2 ? 3 : 1 + rnd() % k), A(k)), lean_sarray_size(n), 0); break; }
      case 17: { lean_object *n = A(k); answer("rsa_private", l4_web_hacl_rsa_private(n, A(1 + rnd() % k), A(k)), lean_sarray_size(n), 0); break; }
      case 18: { lean_object *n = A(k); lean_object *e = A(3), *d = A(1 + rnd() % k), *sl = A(rnd() % 80), *m = A(a_len());
        answer("rsapss_sign", l4_web_hacl_rsapss_sign(alg, n, e, d, sl, m), lean_sarray_size(n), 0); break; }
      case 19: { lean_object *n = A(k); lean_object *e = A(3), *sg = A(k), *m = A(a_len());
        calls++; (void)l4_web_hacl_rsapss_verify(alg, n, e, (size_t)(rnd() % 600), sg, m); break; }
      default: { lean_object *w = arr_len(); calls++; (void)l4_web_hacl_wipe(w); break; }
    }
    for (int i = 0; i < nargs; i++) {
      if (sum(args[i]) != sums[i]) { bad++; fprintf(stderr, "an input changed (case args %d)\n", i); }
      lean_dec_ref(args[i]);
    }
  }
  printf("fuzz: %ld calls, %ld bad answers or changed inputs, %ld Lean objects not freed\n", calls, bad, live);
  return bad || live ? 1 : 0;
}
