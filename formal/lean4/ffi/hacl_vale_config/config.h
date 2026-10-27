/* config.h — the HACL* build configuration for the EverCrypt AES-GCM units
 * (third_party/hacl/src/EverCrypt_AEAD.c, EverCrypt_AutoConfig2.c,
 * EverCrypt_Chacha20Poly1305.c), https://github.com/danbri/factoidal/issues/677.
 *
 * Upstream (cryspen/hacl-packages 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2)
 * generates this file with CMake from config/Config.h.in. This file is that
 * template filled in by hand for the one configuration this tree builds, and
 * it is NOT an upstream file: it holds no code, only the feature switches.
 *
 * - HACL_CAN_COMPILE_VALE is 1 only on x86-64 (Linux or macOS, not
 *   Emscripten). The lakefile assembles the Vale .S files only there, and
 *   only there is this directory on the include path of the EverCrypt units.
 *   ffi/hacl_aesgcm.c makes the same test.
 * - HACL_CAN_COMPILE_VEC128 and VEC256 are NOT defined: the vectorised
 *   ChaCha20-Poly1305 units are not vendored, so EverCrypt_Chacha20Poly1305.c
 *   (link closure of EverCrypt_AEAD.c) compiles to the portable
 *   Hacl_AEAD_Chacha20Poly1305 calls only.
 * - The TARGET_ARCHITECTURE ids are the values of config/default_config.h. */
#ifndef L4_HACL_VALE_CONFIG_H
#define L4_HACL_VALE_CONFIG_H

#define TARGET_ARCHITECTURE_ID_UNKNOWN 0
#define TARGET_ARCHITECTURE_ID_X86 1
#define TARGET_ARCHITECTURE_ID_X64 2
#define TARGET_ARCHITECTURE_ID_ARM32 3
#define TARGET_ARCHITECTURE_ID_ARM64 4
#define TARGET_ARCHITECTURE_ID_SYSTEMZ 5
#define TARGET_ARCHITECTURE_ID_POWERPC64 6

#if defined(__x86_64__) && !defined(__EMSCRIPTEN__) && \
    (defined(__linux__) || defined(__APPLE__))
#define TARGET_ARCHITECTURE TARGET_ARCHITECTURE_ID_X64
#define HACL_CAN_COMPILE_VALE 1
#else
#define TARGET_ARCHITECTURE TARGET_ARCHITECTURE_ID_UNKNOWN
#endif

#ifndef HACL_CAN_COMPILE_VEC128
#define Lib_IntVector_Intrinsics_vec128 void *
#endif
#ifndef HACL_CAN_COMPILE_VEC256
#define Lib_IntVector_Intrinsics_vec256 void *
#endif

#endif
