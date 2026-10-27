/* hacl_p256.c — Lean 4 <-> C binding for the vendored HACL* NIST P-256
 * ECDSA verification primitive (third_party/hacl/, Apache-2.0,
 * hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see
 * third_party/hacl/PROVENANCE.md).  Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/P256Native.lean.
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md, "Lean 4 tree
 * amendment" — signature primitives come from HACL* via FFI ONLY.  There
 * is NO cryptographic logic in this file.  The only logic is length
 * checking around Lean's ByteArray (a `lean_sarray` of uint8) and the
 * split of a JWS 64-byte r||s signature into the two 32-byte halves
 * HACL* takes.
 *
 * Calling convention match (JWS ES256, RFC 7518 section 3.4):
 *   JWS ES256 signature = R || S, each the 32-byte big-endian
 *   fixed-length integer.  HACL* takes signature_r and signature_s as
 *   two separate 32-byte big-endian buffers.  So the conversion is one
 *   pointer offset, not a re-encoding: there is no DER here.
 *   The public key is x || y, 64 raw bytes, which is what a JWK
 *   `{"kty":"EC","crv":"P-256","x":...,"y":...}` gives after base64url
 *   decoding both members.  Hacl_P256_ecdsa_verif_p256_sha2 itself
 *   hashes the message with SHA-256 and validates the public key.
 *
 * Boundary contract:
 *   l4_hacl_p256_verify_sha256(pubXY[64], msg, sig[64]) -> 0 / 1
 *   l4_hacl_p256_sign_sha256(sk[32], msg, nonce[32]) -> sig[64] or empty
 *   l4_hacl_p256_secret_to_public(sk[32]) -> pubXY[64] or empty
 *   l4_hacl_p256_compressed_to_raw(pk[33]) -> pubXY[64] or empty
 *   l4_hacl_p256_ecdh(theirXY[64], sk[32]) -> x||y of sk*Q [64] or empty
 * Every length refusal is 0 or an empty ByteArray, and so is every
 * refusal HACL* reports (a private key or nonce outside [1, n-1], a
 * compressed point that is not on the curve).  There is no "unknown"
 * answer and no success-by-default path.  The three producing entries
 * were added for the authorization server
 * (https://github.com/danbri/factoidal/issues/916); each body is length
 * checks and exactly one HACL* call.
 *
 * Memory: every argument is BORROWED (`@&` on the Lean side), so nothing
 * is dec-ref'd here.  HACL* takes non-const `uint8_t *` for its inputs
 * but does not write through them.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_P256.h"

LEAN_EXPORT uint8_t l4_hacl_p256_verify_sha256(b_lean_obj_arg pub_xy,
                                               b_lean_obj_arg msg,
                                               b_lean_obj_arg sig) {
  if (lean_sarray_size(pub_xy) != 64) return 0;
  if (lean_sarray_size(sig) != 64) return 0;
  size_t n = lean_sarray_size(msg);
  if (n > UINT32_MAX) return 0;
  uint8_t *s = lean_sarray_cptr(sig);
  return Hacl_P256_ecdsa_verif_p256_sha2((uint32_t)n, lean_sarray_cptr(msg),
                                         lean_sarray_cptr(pub_xy),
                                         s, s + 32) ? 1 : 0;
}

/* Point validity of a raw x||y public key (HACL* checks the point is on
 * the curve and is not the point at infinity).  Exposed so the Lean JWK
 * layer can refuse a malformed EC key at parse time rather than at
 * verification time.  Not a cryptographic decision made here: the whole
 * body is one HACL* call. */
LEAN_EXPORT uint8_t l4_hacl_p256_validate_public_key(b_lean_obj_arg pub_xy) {
  if (lean_sarray_size(pub_xy) != 64) return 0;
  return Hacl_P256_validate_public_key(lean_sarray_cptr(pub_xy)) ? 1 : 0;
}

static lean_obj_res l4_p256_empty_bytes(void) {
  return lean_alloc_sarray(1, 0, 0);
}

/* ECDSA-P256-SHA256 signing: HACL* Hacl_P256_ecdsa_sign_p256_sha2.  The
 * nonce is 32 bytes the CALLER supplies (the host's random source); HACL*
 * refuses a private key or nonce outside [1, n-1], and then this returns
 * the empty array.  The signature is r || s, 64 bytes, as JWS ES256 wants. */
LEAN_EXPORT lean_obj_res l4_hacl_p256_sign_sha256(b_lean_obj_arg sk,
                                                  b_lean_obj_arg msg,
                                                  b_lean_obj_arg nonce) {
  if (lean_sarray_size(sk) != 32) return l4_p256_empty_bytes();
  if (lean_sarray_size(nonce) != 32) return l4_p256_empty_bytes();
  size_t n = lean_sarray_size(msg);
  if (n > UINT32_MAX) return l4_p256_empty_bytes();
  uint8_t sig[64];
  if (!Hacl_P256_ecdsa_sign_p256_sha2(sig, (uint32_t)n, lean_sarray_cptr(msg),
                                      lean_sarray_cptr(sk), lean_sarray_cptr(nonce)))
    return l4_p256_empty_bytes();
  lean_obj_res out = lean_alloc_sarray(1, 64, 64);
  memcpy(lean_sarray_cptr(out), sig, 64);
  return out;
}

/* The public key x || y of a private key: HACL* Hacl_P256_dh_initiator
 * (scalar multiplication of the base point), which refuses a private key
 * outside [1, n-1]. */
LEAN_EXPORT lean_obj_res l4_hacl_p256_secret_to_public(b_lean_obj_arg sk) {
  if (lean_sarray_size(sk) != 32) return l4_p256_empty_bytes();
  uint8_t pk[64];
  if (!Hacl_P256_dh_initiator(pk, lean_sarray_cptr(sk))) return l4_p256_empty_bytes();
  lean_obj_res out = lean_alloc_sarray(1, 64, 64);
  memcpy(lean_sarray_cptr(out), pk, 64);
  return out;
}

/* SEC 1 point decompression: HACL* Hacl_P256_compressed_to_raw, which
 * checks the prefix byte (0x02 or 0x03) and that the point is on the
 * curve. */
LEAN_EXPORT lean_obj_res l4_hacl_p256_compressed_to_raw(b_lean_obj_arg pk) {
  if (lean_sarray_size(pk) != 33) return l4_p256_empty_bytes();
  uint8_t raw[64];
  if (!Hacl_P256_compressed_to_raw(lean_sarray_cptr(pk), raw)) return l4_p256_empty_bytes();
  lean_obj_res out = lean_alloc_sarray(1, 64, 64);
  memcpy(lean_sarray_cptr(out), raw, 64);
  return out;
}

/* ECDH over P-256 (SP 800-56A section 5.7.1.2, the ECC CDH primitive):
 * HACL* Hacl_P256_dh_responder.  Its header comment: "The function also
 * checks whether `private_key` and `their_pubkey` are valid", that is, the
 * private key is in [1, n-1] and the public key is on the curve and is not
 * the point at infinity; on either refusal it returns false and this entry
 * returns the empty array.  HACL* writes the 64-byte point x || y of
 * private_key * their_pubkey.  The selection of the x coordinate (RFC 7518
 * section 4.6.2, SP 800-56A Z) is made in Lean, P256Native.p256Ecdh.
 * Added for https://github.com/danbri/factoidal/issues/1083. */
LEAN_EXPORT lean_obj_res l4_hacl_p256_ecdh(b_lean_obj_arg their_xy,
                                           b_lean_obj_arg sk) {
  if (lean_sarray_size(their_xy) != 64) return l4_p256_empty_bytes();
  if (lean_sarray_size(sk) != 32) return l4_p256_empty_bytes();
  uint8_t shared[64];
  if (!Hacl_P256_dh_responder(shared, lean_sarray_cptr(their_xy),
                              lean_sarray_cptr(sk))) {
    memset(shared, 0, sizeof shared);
    return l4_p256_empty_bytes();
  }
  lean_obj_res out = lean_alloc_sarray(1, 64, 64);
  memcpy(lean_sarray_cptr(out), shared, 64);
  memset(shared, 0, sizeof shared);
  return out;
}
