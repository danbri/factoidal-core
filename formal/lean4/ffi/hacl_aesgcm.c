/* hacl_aesgcm.c — Lean 4 <-> C binding for AES-128-GCM and AES-256-GCM
 * through HACL*'s EverCrypt_AEAD over the Vale verified x86-64 assembly
 * (third_party/hacl/src/EverCrypt_AEAD.c, third_party/hacl/vale/src/
 * aesgcm-x86_64-{linux,darwin}.S), cryspen/hacl-packages commit
 * 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2, Apache-2.0 — see
 * third_party/hacl/PROVENANCE.md. Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/AesGcmNative.lean.
 * Issue: https://github.com/danbri/factoidal/issues/677.
 *
 * Owner decision, 2026-10-27, verbatim: "Ok for now: “My proposal is HACL*
 * Vale on x86-64 and a refusal on other CPU”".
 *
 * There is NO AES or GCM arithmetic in this file. The only logic is length
 * checks around Lean's ByteArray, the choice of EverCrypt algorithm by key
 * length (16 bytes: Spec_Agile_AEAD_AES128_GCM; 32 bytes: AES256_GCM), the
 * one-time CPU feature detection (EverCrypt_AutoConfig2_init), and the split
 * of `ciphertext || tag` (a pointer offset). The tag comparison is
 * EverCrypt's (Vale's); this file must never compare tags itself.
 *
 * Two builds of this file:
 *   - x86-64 Linux or macOS (not Emscripten): the real binding. The lakefile
 *     links EverCrypt_AEAD.c, EverCrypt_AutoConfig2.c,
 *     EverCrypt_Chacha20Poly1305.c (link closure of EverCrypt_AEAD.c) and the
 *     Vale aesgcm and cpuid .S files.
 *   - every other target, wasm32 included: stubs that refuse. Nothing from
 *     EverCrypt is referenced, so nothing else is linked.
 *
 * Boundary contract (all arguments BORROWED; results are fresh objects):
 *   l4_hacl_aesgcm_available(unit) -> 1 when this is the x86-64 build AND
 *       the CPU has AES-NI, PCLMULQDQ, AVX, SSE and MOVBE (the five features
 *       EverCrypt_AEAD_create_in tests before it takes the Vale path); else 0.
 *   l4_hacl_aesgcm_encrypt(key[16|32], iv[12], aad, plain)
 *       -> ciphertext || tag (plain.size + 16 bytes), or EMPTY on a refusal
 *          (lengths, not available, EverCrypt error).
 *   l4_hacl_aesgcm_decrypt(key[16|32], iv[12], aad, ct || tag)
 *       -> plaintext || status, where status (the LAST byte) is 1 when the
 *          tag authenticates and 0 when it does not; or EMPTY on a refusal.
 *          The status byte is there because an empty plaintext is a valid
 *          decryption, so EMPTY alone cannot mean "refused" (the
 *          ffi/hacl_chachapoly.c convention).
 *
 * The IV is 12 bytes only: the only length XML Encryption 1.1 (section
 * 5.2.4) and JWE (RFC 7518 section 5.3) use.
 *
 * Not checked here: IV reuse under one key (the protocol layer owns the IV);
 * the expanded key schedule that EverCrypt_AEAD_free releases is not cleared
 * by EverCrypt, and this file does not clear it either (the state type is
 * opaque to callers).
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#if defined(__x86_64__) && !defined(__EMSCRIPTEN__) && \
    (defined(__linux__) || defined(__APPLE__))
#define L4_AESGCM_VALE 1
#include <pthread.h>
#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#endif

static lean_obj_res l4_ag_empty(void) { return lean_alloc_sarray(1, 0, 0); }

#ifdef L4_AESGCM_VALE

static pthread_once_t l4_ag_once = PTHREAD_ONCE_INIT;
static void l4_ag_init(void) { EverCrypt_AutoConfig2_init(); }

static int l4_ag_cpu_ok(void) {
  pthread_once(&l4_ag_once, l4_ag_init);
  return EverCrypt_AutoConfig2_has_aesni() && EverCrypt_AutoConfig2_has_pclmulqdq() &&
         EverCrypt_AutoConfig2_has_avx() && EverCrypt_AutoConfig2_has_sse() &&
         EverCrypt_AutoConfig2_has_movbe();
}

/* Key length -> EverCrypt algorithm; 0 when the length is refused. */
static int l4_ag_alg(size_t klen, Spec_Agile_AEAD_alg *a) {
  if (klen == 16) { *a = Spec_Agile_AEAD_AES128_GCM; return 1; }
  if (klen == 32) { *a = Spec_Agile_AEAD_AES256_GCM; return 1; }
  return 0;
}

LEAN_EXPORT uint8_t l4_hacl_aesgcm_available(lean_obj_arg unit) {
  (void)unit;
  return l4_ag_cpu_ok() ? 1 : 0;
}

LEAN_EXPORT lean_obj_res l4_hacl_aesgcm_encrypt(b_lean_obj_arg key, b_lean_obj_arg iv,
                                               b_lean_obj_arg aad, b_lean_obj_arg plain) {
  Spec_Agile_AEAD_alg alg;
  if (!l4_ag_alg(lean_sarray_size(key), &alg)) return l4_ag_empty();
  if (lean_sarray_size(iv) != 12) return l4_ag_empty();
  size_t pn = lean_sarray_size(plain);
  size_t an = lean_sarray_size(aad);
  if (pn > UINT32_MAX - 16u || an > UINT32_MAX) return l4_ag_empty();
  if (!l4_ag_cpu_ok()) return l4_ag_empty();
  EverCrypt_AEAD_state_s *s = NULL;
  if (EverCrypt_AEAD_create_in(alg, &s, lean_sarray_cptr(key)) != EverCrypt_Error_Success ||
      s == NULL)
    return l4_ag_empty();
  lean_obj_res out = lean_alloc_sarray(1, pn + 16, pn + 16);
  uint8_t *o = lean_sarray_cptr(out);
  EverCrypt_Error_error_code rc =
      EverCrypt_AEAD_encrypt(s, lean_sarray_cptr(iv), 12u, lean_sarray_cptr(aad),
                             (uint32_t)an, lean_sarray_cptr(plain), (uint32_t)pn, o, o + pn);
  EverCrypt_AEAD_free(s);
  if (rc != EverCrypt_Error_Success) {
    lean_dec_ref(out);
    return l4_ag_empty();
  }
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_aesgcm_decrypt(b_lean_obj_arg key, b_lean_obj_arg iv,
                                               b_lean_obj_arg aad, b_lean_obj_arg ct) {
  Spec_Agile_AEAD_alg alg;
  if (!l4_ag_alg(lean_sarray_size(key), &alg)) return l4_ag_empty();
  if (lean_sarray_size(iv) != 12) return l4_ag_empty();
  size_t cn = lean_sarray_size(ct);
  size_t an = lean_sarray_size(aad);
  if (cn < 16) return l4_ag_empty();
  size_t pn = cn - 16;
  if (pn > UINT32_MAX || an > UINT32_MAX) return l4_ag_empty();
  if (!l4_ag_cpu_ok()) return l4_ag_empty();
  EverCrypt_AEAD_state_s *s = NULL;
  if (EverCrypt_AEAD_create_in(alg, &s, lean_sarray_cptr(key)) != EverCrypt_Error_Success ||
      s == NULL)
    return l4_ag_empty();
  lean_obj_res out = lean_alloc_sarray(1, pn + 1, pn + 1);
  uint8_t *o = lean_sarray_cptr(out);
  uint8_t *c = lean_sarray_cptr(ct);
  EverCrypt_Error_error_code rc =
      EverCrypt_AEAD_decrypt(s, lean_sarray_cptr(iv), 12u, lean_sarray_cptr(aad),
                             (uint32_t)an, c, (uint32_t)pn, c + pn, o);
  EverCrypt_AEAD_free(s);
  if (rc == EverCrypt_Error_Success) {
    o[pn] = 1;
  } else if (rc == EverCrypt_Error_AuthenticationFailure) {
    /* Never hand back a partial or unauthenticated plaintext. */
    memset(o, 0, pn);
    o[pn] = 0;
  } else {
    lean_dec_ref(out);
    return l4_ag_empty();
  }
  return out;
}

#else /* not x86-64: refuse. https://github.com/danbri/factoidal/issues/677 */

LEAN_EXPORT uint8_t l4_hacl_aesgcm_available(lean_obj_arg unit) {
  (void)unit;
  return 0;
}

LEAN_EXPORT lean_obj_res l4_hacl_aesgcm_encrypt(b_lean_obj_arg key, b_lean_obj_arg iv,
                                               b_lean_obj_arg aad, b_lean_obj_arg plain) {
  (void)key; (void)iv; (void)aad; (void)plain;
  return l4_ag_empty();
}

LEAN_EXPORT lean_obj_res l4_hacl_aesgcm_decrypt(b_lean_obj_arg key, b_lean_obj_arg iv,
                                               b_lean_obj_arg aad, b_lean_obj_arg ct) {
  (void)key; (void)iv; (void)aad; (void)ct;
  return l4_ag_empty();
}

#endif
