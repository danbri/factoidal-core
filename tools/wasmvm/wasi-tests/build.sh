#!/bin/bash
# Rebuild the WASI test modules embedded in formal/lean4/L4Factoidal/WasmVM/Tests/Wasi.lean
# (issue https://github.com/danbri/factoidal/issues/1244). Prints each as a Lean
# ByteArray; paste the output over the definitions of the same name.
#   wasi_hand.wat, wasi_badtype.wat, wasi_badname.wat: wasm-tools parse (1.263.0)
#   wasi_all.c: emcc -Oz -sSTANDALONE_WASM --no-entry (Emscripten 6.0.8); its 45
#     imports are typed by the compiler from Emscripten's wasi/api.h, which is an
#     outside check of the witx lowering in Wasi.lean (`Fn.type`).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=$(mktemp -d)
for n in hand badtype badname; do wasm-tools parse "$HERE/wasi_$n.wat" -o "$OUT/$n.wasm"; done
${EMCC:-emcc} -Oz -sSTANDALONE_WASM --no-entry "$HERE/wasi_all.c" -o "$OUT/all.wasm"
for n in hand badtype badname all; do
  python3 -I - "$OUT/$n.wasm" "${n}Module" <<'PY'
import sys
b = open(sys.argv[1], 'rb').read()
rows = [', '.join('0x%02x' % x for x in b[i:i+15]) for i in range(0, len(b), 15)]
print('def %s : ByteArray := ⟨#[\n  %s]⟩\n' % (sys.argv[2], ',\n  '.join(rows)))
PY
done
rm -rf "$OUT"
