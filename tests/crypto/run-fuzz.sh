#!/usr/bin/env bash
# Fuzz the web engine's HACL* boundary natively under AddressSanitizer and
# UndefinedBehaviorSanitizer: tests/crypto/hacl_webcrypto_fuzz.c (hostile lengths and
# contents through every entry point of formal/lean4/ffi/hacl_webcrypto.c), the core and
# the vendored HACL* units, with Lean's allocator replaced by malloc so every output array
# has redzones. Usage: tests/crypto/run-fuzz.sh [ITERATIONS] [SEED] [OUTDIR]
# Record docs/designissues/2026-11-09-crypto-boundary-security.md, "Fuzzing the shim".
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
H="$ROOT/third_party/hacl"
T=$(lean --print-prefix 2>/dev/null || echo "$HOME/.elan/toolchains/leanprover--lean4---v4.33.1")
OUT=${3:-$(mktemp -d)}
UNITS=(Hacl_Hash_SHA1 Hacl_Hash_SHA2 Hacl_HMAC Hacl_Hash_Blake2s Hacl_Hash_Blake2b Hacl_Ed25519 Hacl_Curve25519_51
  Hacl_P256 Hacl_AEAD_Chacha20Poly1305 Hacl_Chacha20 Hacl_MAC_Poly1305 Hacl_Bignum Hacl_Bignum64 Hacl_RSAPSS Lib_Memzero0)
SRCS=("$ROOT/tests/crypto/hacl_webcrypto_fuzz.c" "$ROOT/formal/lean4/ffi/hacl_webcrypto.c" "$ROOT/formal/lean4/ffi/hacl_webcrypto_core.c")
for u in "${UNITS[@]}"; do SRCS+=("$H/src/$u.c"); done
clang -O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fno-sanitize-recover=undefined \
  -I "$H/include" -I "$T/include" "${SRCS[@]}" -o "$OUT/fuzz"
ASAN_OPTIONS=abort_on_error=1 UBSAN_OPTIONS=print_stacktrace=1 "$OUT/fuzz" "${1:-20000}" "${2:-1}"
