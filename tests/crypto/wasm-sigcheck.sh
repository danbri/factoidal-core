#!/bin/bash
# wasm-sigcheck.sh: link Lean's emitted C of Crypto/WebHacl.lean against ffi/hacl_webcrypto.c
# for wasm32 and print every wasm-ld "function signature mismatch" (a mismatched extern links
# and then traps at each call: the core Wasm build refuses it). The Lean runtime and the
# rest of the library are not linked; their undefined symbols are ignored.
#   cd formal/lean4 && lean -c /tmp/WebHacl.c L4Factoidal/Crypto/WebHacl.lean   (with LEAN_PATH)
#   tests/crypto/wasm-sigcheck.sh /tmp/WebHacl.c formal/lean4/ffi/hacl_webcrypto.c /tmp/sigcheck
# Needs emcc and the Wasm runtime headers (FACTOIDAL_WASM_RUNTIME_CACHE/wasm-include).
set -u
IR=$1; SHIM=$2; OUT=$3
R=${FACTOIDAL_WASM_RUNTIME_CACHE:-/Users/danbri/working/sandbox/october/tpac/depmap/cache/l4wasm-cache/l4wasm-work}
T=$(lean --print-prefix)
H=$(cd "$(dirname "$0")/../.." && pwd)/third_party/hacl/include
F=(-O1 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I "$R/wasm-include" -I "$T/include" -I "$H" -I "$(dirname "$SHIM")")
mkdir -p "$OUT"
emcc "${F[@]}" -c "$IR" -o "$OUT/ir.o" 2>/dev/null || { echo "IR compile failed"; exit 2; }
emcc "${F[@]}" -c "$SHIM" -o "$OUT/shim.o" 2>/dev/null || { echo "shim compile failed"; exit 2; }
emcc -O1 -fwasm-exceptions -sERROR_ON_UNDEFINED_SYMBOLS=0 -sWARN_ON_UNDEFINED_SYMBOLS=0 --no-entry -Wl,--export-all \
  "$OUT/ir.o" "$OUT/shim.o" -o "$OUT/t.wasm" > "$OUT/link.txt" 2>&1
if grep -o 'function signature mismatch: [A-Za-z0-9_]*' "$OUT/link.txt" | sort -u | grep .; then exit 1; fi
echo "no signature mismatch"
