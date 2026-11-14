#!/usr/bin/env bash
# Build and run tests/crypto/hacl_webcrypto_kat.c against formal/lean4/ffi/hacl_webcrypto.c
# and the vendored HACL* units the web engine links (native, host C compiler).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
H="$ROOT/third_party/hacl"
T=$(lean --print-prefix)
OUT=${1:-$(mktemp -d)}
UNITS=(Hacl_Hash_SHA1 Hacl_Hash_SHA2 Hacl_Hash_SHA3 Hacl_HMAC Hacl_Hash_Blake2s Hacl_Hash_Blake2b Hacl_Ed25519 Hacl_Curve25519_51
  Hacl_P256 Hacl_AEAD_Chacha20Poly1305 Hacl_Chacha20 Hacl_MAC_Poly1305 Hacl_Bignum Hacl_Bignum64 Hacl_RSAPSS Lib_Memzero0)
SRCS=("$ROOT/tests/crypto/hacl_webcrypto_kat.c" "$ROOT/formal/lean4/ffi/hacl_webcrypto.c")
for u in "${UNITS[@]}"; do SRCS+=("$H/src/$u.c"); done
cc -O2 -I "$H/include" -I "$T/include" "${SRCS[@]}" "$T/lib/lean/libleanrt.a" "$T/lib/lean/libInit.a" \
  -L"$T/lib" -lgmp -luv -lc++ -o "$OUT/kat" 2>&1 | { grep -v "was built for newer" >&2 || true; }
"$OUT/kat"
