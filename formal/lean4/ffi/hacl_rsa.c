/* hacl_rsa.c — Lean 4 <-> C binding for the RSA PUBLIC and PRIVATE
 * operations over the vendored HACL* generic 64-bit bignum field
 * (third_party/hacl/, Apache-2.0, hacl-packages commit
 * 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see third_party/hacl/
 * PROVENANCE.md).  Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/RsaNative.lean (public) and
 * L4Factoidal/Crypto/RsaOaep.lean (private).
 *
 * WHAT IS EXPOSED.  Two primitives and nothing else:
 *   * RSAVP1 / RSAEP (RFC 8017 sections 5.2.2 and 5.1.1), s^e mod n, the
 *     PUBLIC operation, over Hacl_Bignum64_mod_exp_vartime;
 *   * RSADP (RFC 8017 section 5.1.2, first form (n, d)), c^d mod n, the
 *     PRIVATE operation, over Hacl_Bignum64_mod_exp_consttime.  Added
 *     2026-10-27 for RSA-OAEP decryption (XML Encryption
 *     rsa-oaep-mgf1p, JWE RSA-OAEP and RSA-OAEP-256,
 *     https://github.com/danbri/factoidal/issues/1082).
 * There is no key generation, no CRT form and no signing entry point.
 *
 * VARIABLE TIME FOR THE PUBLIC EXPONENT ONLY.  Hacl_Bignum64_mod_exp_vartime
 * is not constant time in the exponent.  In the public operation the
 * exponent is the RSA PUBLIC exponent e, a published value, so a timing
 * observer learns nothing new.  The private operation uses
 * Hacl_Bignum64_mod_exp_consttime, which is constant time over the
 * exponent d, and passes the PUBLIC bound 8*k as the bit count of d, so
 * the bit length of d does not reach the call either.
 *
 * NO PADDING LOGIC HERE.  EMSA-PKCS1-v1_5 (L4Factoidal/JOSE/Pkcs1.lean)
 * and EME-OAEP (L4Factoidal/Crypto/RsaOaep.lean) are pure Lean, where
 * they carry theorems.  This file returns the raw k-byte integer and makes
 * no decision about a signature or a padding.  For OAEP this keeps the
 * Manger 2001 oracle out of C: the file has one refusal (the empty result)
 * for every input it refuses, and it never reads the leading byte of the
 * decrypted block.
 *
 * Boundary contract, with k = n.size:
 *   l4_hacl_rsa_public_op(n, e, s)  -> res[k] | empty
 *   l4_hacl_rsa_private_op(n, d, c) -> res[k] | empty
 * The EMPTY ByteArray is a refusal, never a result:
 *   * k not 256, 384 or 512 bytes (2048, 3072 or 4096 bits);
 *   * s.size != k (c.size != k), or e (d) empty, or longer than k;
 *   * e with no set bit (public operation);
 *   * allocation failure;
 *   * HACL* rejecting its own preconditions (n even, n <= 1, or s >= n,
 *     c >= n — the last is RFC 8017's "representative out of range").
 * A successful result is always exactly k bytes, so a caller
 * distinguishes a refusal by size.
 *
 * Memory: arguments are BORROWED; every heap buffer is freed on every
 * exit path.  In the private operation the copies of d (the padded byte
 * buffer and the limb array) and the result limb array are cleared with
 * HACL*'s Lib_Memzero0_memzero0 (third_party/hacl/src/Lib_Memzero0.c:
 * explicit_bzero on Linux, memset_s on macOS, a volatile loop elsewhere;
 * already in the link closure of libl4hacl and of Wasm/build-wasm.sh)
 * before they are freed.  The Lean-owned argument d and the Lean-owned
 * result are not cleared here.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Bignum64.h"
#include "lib_memzero0.h"

static lean_obj_res l4_rsa_empty(void) { return lean_alloc_sarray(1, 0, 0); }

/* Number of significant bits of a big-endian byte string.  Byte counting,
 * not arithmetic on a secret: e is public. */
static uint32_t l4_be_bit_length(const uint8_t *b, size_t n) {
  size_t i = 0;
  while (i < n && b[i] == 0) i++;
  if (i == n) return 0;
  uint32_t bits = (uint32_t)((n - i - 1) * 8);
  uint8_t top = b[i];
  while (top != 0) { bits++; top >>= 1; }
  return bits;
}

LEAN_EXPORT lean_obj_res l4_hacl_rsa_public_op(b_lean_obj_arg n_ba,
                                               b_lean_obj_arg e_ba,
                                               b_lean_obj_arg s_ba) {
  size_t k = lean_sarray_size(n_ba);
  if (k != 256 && k != 384 && k != 512) return l4_rsa_empty();
  if (lean_sarray_size(s_ba) != k) return l4_rsa_empty();
  size_t elen = lean_sarray_size(e_ba);
  if (elen == 0 || elen > k) return l4_rsa_empty();

  uint32_t e_bits = l4_be_bit_length(lean_sarray_cptr(e_ba), elen);
  if (e_bits == 0) return l4_rsa_empty();

  uint32_t n_limbs = (uint32_t)(k / 8);
  uint32_t e_limbs = (e_bits + 63U) / 64U;

  /* Right-align e in a limb-multiple big-endian buffer so that
   * new_bn_from_bytes_be yields exactly e_limbs limbs. */
  size_t e_pad = (size_t)e_limbs * 8U;
  uint8_t *e_buf = (uint8_t *)calloc(e_pad, 1);
  if (e_buf == NULL) return l4_rsa_empty();
  memcpy(e_buf + (e_pad - elen), lean_sarray_cptr(e_ba), elen);

  uint64_t *bn_n = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, lean_sarray_cptr(n_ba));
  uint64_t *bn_s = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, lean_sarray_cptr(s_ba));
  uint64_t *bn_e = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)e_pad, e_buf);
  uint64_t *bn_r = (uint64_t *)calloc(n_limbs, sizeof(uint64_t));

  lean_obj_res out;
  if (bn_n == NULL || bn_s == NULL || bn_e == NULL || bn_r == NULL) {
    out = l4_rsa_empty();
  } else if (!Hacl_Bignum64_mod_exp_vartime(n_limbs, bn_n, bn_s, e_bits, bn_e, bn_r)) {
    out = l4_rsa_empty();
  } else {
    out = lean_alloc_sarray(1, k, k);
    Hacl_Bignum64_bn_to_bytes_be((uint32_t)k, bn_r, lean_sarray_cptr(out));
  }

  free(e_buf);
  free(bn_n);
  free(bn_s);
  free(bn_e);
  free(bn_r);
  return out;
}

/* RSADP, RFC 8017 section 5.1.2 step 2.a: m = c^d mod n.  Constant time
 * over d (Hacl_Bignum64_mod_exp_consttime).  d is right-aligned into a
 * k-byte buffer so that its limb count, and the bit bound passed to HACL*,
 * are functions of the public k alone. */
LEAN_EXPORT lean_obj_res l4_hacl_rsa_private_op(b_lean_obj_arg n_ba,
                                                b_lean_obj_arg d_ba,
                                                b_lean_obj_arg c_ba) {
  size_t k = lean_sarray_size(n_ba);
  if (k != 256 && k != 384 && k != 512) return l4_rsa_empty();
  if (lean_sarray_size(c_ba) != k) return l4_rsa_empty();
  size_t dlen = lean_sarray_size(d_ba);
  if (dlen == 0 || dlen > k) return l4_rsa_empty();

  uint32_t n_limbs = (uint32_t)(k / 8);
  uint32_t d_bits = (uint32_t)(k * 8U);

  uint8_t *d_buf = (uint8_t *)calloc(k, 1);
  if (d_buf == NULL) return l4_rsa_empty();
  memcpy(d_buf + (k - dlen), lean_sarray_cptr(d_ba), dlen);

  uint64_t *bn_n = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, lean_sarray_cptr(n_ba));
  uint64_t *bn_c = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, lean_sarray_cptr(c_ba));
  uint64_t *bn_d = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, d_buf);
  uint64_t *bn_m = (uint64_t *)calloc(n_limbs, sizeof(uint64_t));

  lean_obj_res out;
  if (bn_n == NULL || bn_c == NULL || bn_d == NULL || bn_m == NULL) {
    out = l4_rsa_empty();
  } else if (!Hacl_Bignum64_mod_exp_consttime(n_limbs, bn_n, bn_c, d_bits, bn_d, bn_m)) {
    out = l4_rsa_empty();
  } else {
    out = lean_alloc_sarray(1, k, k);
    Hacl_Bignum64_bn_to_bytes_be((uint32_t)k, bn_m, lean_sarray_cptr(out));
  }

  Lib_Memzero0_memzero0(d_buf, (uint64_t)k);
  free(d_buf);
  if (bn_d != NULL) Lib_Memzero0_memzero0(bn_d, (uint64_t)n_limbs * sizeof(uint64_t));
  free(bn_d);
  if (bn_m != NULL) Lib_Memzero0_memzero0(bn_m, (uint64_t)n_limbs * sizeof(uint64_t));
  free(bn_m);
  free(bn_n);
  free(bn_c);
  return out;
}
