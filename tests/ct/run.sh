#!/usr/bin/env bash
# Build and run tests/ct/ct_valgrind.c.
#   tests/ct/run.sh            correctness only (no Valgrind; any host)
#   tests/ct/run.sh valgrind   memcheck check of secret-dependent branches and
#                              addresses (Linux with valgrind installed)
# Output binary goes to a temporary directory, never into the tree.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
H="$ROOT/third_party/hacl"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
SRCS=(Hacl_K256_ECDSA Hacl_EC_K256 Hacl_HMAC_DRBG Hacl_HMAC Hacl_Hash_SHA2 Hacl_Hash_SHA1
      Hacl_Hash_SHA3 Hacl_Hash_Blake2s Hacl_Hash_Blake2b Hacl_Hash_MD5 Lib_Memzero0
      Hacl_Bignum64 Hacl_Bignum)
FLAGS=(-O2 -g -std=gnu11 -I "$H/include" -I "$H/include/krml/internal")
MODE="${1:-plain}"
if [ "$MODE" = valgrind ]; then FLAGS+=(-DHAVE_VALGRIND); fi
files=()
for s in "${SRCS[@]}"; do files+=("$H/src/$s.c"); done
"${CC:-cc}" "${FLAGS[@]}" "$ROOT/tests/ct/ct_valgrind.c" "${files[@]}" -o "$OUT/ct_valgrind"
if [ "$MODE" = valgrind ]; then
  RC=0
  valgrind --tool=memcheck --error-exitcode=0 --track-origins=yes --num-callers=30 \
    "$OUT/ct_valgrind" || RC=$?
  exit "$RC"
else
  "$OUT/ct_valgrind"
fi
