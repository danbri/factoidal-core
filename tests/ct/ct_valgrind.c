/* ct_valgrind.c — a Valgrind memcheck test that the secret-key paths we call
 * have no branch and no memory address that depends on the secret.
 *
 * Method (Langley's ctgrind; the same idea as the "secret = undefined" mode of
 * ct-verif and TIMECOP): mark the secret bytes as UNDEFINED with
 * VALGRIND_MAKE_MEM_UNDEFINED.  Memcheck then reports every conditional jump
 * and every memory address computed from them.  Outputs that become public
 * (the signature, R) are marked DEFINED again at the declassification points
 * (L4_DECLASSIFY in formal/lean4/ffi/hacl_k256.c).
 *
 * Each case counts the errors that memcheck reports while it runs.  Two
 * cases are controls that MUST leak (HACL*'s variable-time exponentiation, and
 * a textbook square-and-multiply).  If a control reports no error, the check
 * cannot see a leak and the run fails.
 *
 * Without -DHAVE_VALGRIND the client requests are no-ops: the file is then a
 * correctness test only (the EIP-155 vector and an RFC 6979 vector).
 *
 * This is a test, not a proof.  It covers the compiled code on the machine and
 * compiler of the run, for the inputs of the run.  Design record:
 * docs/designissues/2026-11-27-bignum-timing-and-aes.md section 6, layer 3.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifdef HAVE_VALGRIND
#include <valgrind/memcheck.h>
#define L4_DECLASSIFY(p, n) VALGRIND_MAKE_MEM_DEFINED((p), (n))
#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED((p), (n))
#define ERRORS() ((long)VALGRIND_COUNT_ERRORS)
#else
#define L4_DECLASSIFY(p, n) ((void)(p), (void)(n))
#define SECRET(p, n) ((void)(p), (void)(n))
#define ERRORS() 0L
#endif

#define L4_K256_NO_LEAN
#include "../../formal/lean4/ffi/hacl_k256.c"
#include "Hacl_Bignum64.h"

static int failures = 0;

static void hex(const char *s, uint8_t *out, size_t n) {
  for (size_t i = 0; i < n; i++) sscanf(s + 2 * i, "%2hhx", &out[i]);
}

static void expect_bytes(const char *label, const uint8_t *got, const char *want_hex, size_t n) {
  uint8_t want[128];
  hex(want_hex, want, n);
  int ok = memcmp(got, want, n) == 0;
  printf("%s %s\n", ok ? "PASS" : "FAIL", label);
  if (!ok) failures++;
}

/* A case that must not leak: errors counted while it runs must be 0. */
static void expect_errors(const char *label, long before, int must_leak) {
  long n = ERRORS() - before;
#ifdef HAVE_VALGRIND
  int ok = must_leak ? (n > 0) : (n == 0);
  printf("%s %s: %ld memcheck errors (%s)\n", ok ? "PASS" : "FAIL", label, n,
         must_leak ? "control, must be more than 0" : "must be 0");
  if (!ok) failures++;
#else
  (void)n; (void)must_leak;
  printf("SKIP %s (no Valgrind)\n", label);
#endif
}

/* Control 2: a textbook square-and-multiply that branches on each exponent bit. */
static uint64_t naive_powmod(uint64_t b, uint64_t e, uint64_t m) {
  unsigned __int128 r = 1, x = b % m;
  while (e) {
    if (e & 1) r = (r * x) % m;
    x = (x * x) % m;
    e >>= 1;
  }
  return (uint64_t)r;
}

int main(void) {
  /* 1. EIP-155 example (https://eips.ethereum.org/EIPS/eip-155): private key
   *    0x46 repeated, signing hash daf5..8e53, v = 37 for chain id 1, so the
   *    recovery id is 0.  Its r and s are the RFC 6979 signature. */
  uint8_t sk[32], z[32], out[65];
  memset(sk, 0x46, 32);
  hex("daf5a779ae972f972197303d7b574746c7ef83eadac0f2791ad23db92e4c8e53", z, 32);
  SECRET(sk, 32);
  long before = ERRORS();
  int ok = l4_k256_sign_recoverable_core(out, z, sk);
  L4_DECLASSIFY(&ok, sizeof ok);
  expect_errors("secp256k1 sign (EIP-155 key secret)", before, 0);
  L4_DECLASSIFY(out, 65);
  if (!ok) { printf("FAIL EIP-155 sign refused\n"); failures++; }
  expect_bytes("EIP-155 r", out,
               "28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276", 32);
  expect_bytes("EIP-155 s", out + 32,
               "67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83", 32);
  printf("%s EIP-155 recovery id %u (want 0, v = 37)\n", out[64] == 0 ? "PASS" : "FAIL", out[64]);
  if (out[64] != 0) failures++;

  /* 2. The public key of that key, and verification (public data only). */
  uint8_t pub[64];
  before = ERRORS();
  int pk_ok = Hacl_K256_ECDSA_secret_to_public(pub, sk);
  L4_DECLASSIFY(&pk_ok, sizeof pk_ok);
  expect_errors("secp256k1 secret_to_public (key secret)", before, 0);
  L4_DECLASSIFY(pub, 64);
  L4_DECLASSIFY(sk, 32);
  int v_ok = pk_ok && Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(z, pub, out);
  printf("%s EIP-155 signature verifies\n", v_ok ? "PASS" : "FAIL");
  if (!v_ok) failures++;
  out[10] ^= 1;
  int bad = Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(z, pub, out);
  printf("%s EIP-155 signature with one changed bit is refused\n", bad ? "FAIL" : "PASS");
  if (bad) failures++;

  /* 3. Private key 1: the public key is the generator G (SEC 2 section 2.4.1). */
  uint8_t one[32] = {0};
  one[31] = 1;
  Hacl_K256_ECDSA_secret_to_public(pub, one);
  expect_bytes("public key of 1 is G", pub,
               "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
               "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 64);

  /* 4. HACL* constant-time modular exponentiation, secret exponent. */
  uint64_t n[4] = {0xfffffffefffffc2fULL, 0xffffffffffffffffULL, 0xffffffffffffffffULL, 0xffffffffffffffffULL};
  uint64_t a[4] = {3, 0, 0, 0};
  uint64_t e[4] = {0x0123456789abcdefULL, 0xfedcba9876543210ULL, 0x0f1e2d3c4b5a6978ULL, 0x1122334455667788ULL};
  uint64_t res_ct[4], res_vt[4];
  SECRET(e, sizeof e);
  before = ERRORS();
  Hacl_Bignum64_mod_exp_consttime(4, n, a, 256, e, res_ct);
#if defined(__clang__) && defined(__x86_64__)
  /* Expected failure: clang x86-64 compiles the mask select of
   * Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64 into a jump on
   * the reduction carry. https://github.com/danbri/factoidal-core/issues/1200
   * If this case stops leaking, it fails: remove this branch and close the issue. */
  expect_errors("expected failure (issue 1200): HACL* Bignum64 mod_exp_consttime, clang x86-64", before, 1);
#else
  expect_errors("HACL* Bignum64 mod_exp_consttime (exponent secret)", before, 0);
#endif

  /* 5. Control 1: HACL* variable-time exponentiation, same inputs. */
  before = ERRORS();
  Hacl_Bignum64_mod_exp_vartime(4, n, a, 256, e, res_vt);
  expect_errors("control: HACL* Bignum64 mod_exp_vartime (exponent secret)", before, 1);
  L4_DECLASSIFY(res_ct, sizeof res_ct);
  L4_DECLASSIFY(res_vt, sizeof res_vt);
  printf("%s constant-time and variable-time results agree\n",
         memcmp(res_ct, res_vt, sizeof res_ct) == 0 ? "PASS" : "FAIL");
  if (memcmp(res_ct, res_vt, sizeof res_ct) != 0) failures++;

  /* 6. Control 2: textbook square-and-multiply. */
  uint64_t se = 0xdeadbeefcafef00dULL;
  SECRET(&se, sizeof se);
  before = ERRORS();
  volatile uint64_t sink = naive_powmod(3, se, 0xffffffffffffffc5ULL);
  (void)sink;
  expect_errors("control: textbook square-and-multiply (exponent secret)", before, 1);

  printf("%s ct_valgrind: %d failures\n", failures ? "FAIL" : "PASS", failures);
  return failures ? 1 : 0;
}
