#!/usr/bin/env bash
# baseline-emcc/build.sh — the Emscripten baseline: lean/FxSubset.lean and the
# Lean runtime built with emcc and the flags of formal/lean4/Wasm/build-wasm.sh
# (-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions, no pthreads, mimalloc,
# 8 MB stack, memory growth). Reuses the work directory of ../build.sh
# (core C, runtime sources, libuv headers, FxSubset.c): run that first.
# Inputs: WORK (default /opt/wc), VARIANT (default emcc), OPT (default -O3),
# XFLAGS, JOBS. Needs emcc on PATH (source /opt/emsdk/emsdk_env.sh).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"
LEAN_DIR="$REPO/formal/lean4"
WORK="${WORK:-/opt/wc}"; VARIANT="${VARIANT:-emcc}"; OPT="${OPT:--O3}"; XFLAGS="${XFLAGS:-}"; JOBS="${JOBS:-4}"
KEY="$(printf 'emcc|%s|%s' "$OPT" "$XFLAGS" | sha256sum | cut -c1-12)"
OBJ="$WORK/obj-$KEY"; OUT="$WORK/out/$VARIANT"; RT_SRC="$WORK/lean4-src/src"; INC="$WORK/inc"
mkdir -p "$OBJ/core" "$OBJ/rt" "$OBJ/lib" "$OUT"
CFLAGS="$OPT -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions $XFLAGS -I $INC -I $RT_SRC/include
        -Wno-unused-parameter -Wno-unused-command-line-argument -Wno-parentheses-equality"
emcc --version | head -1
FXC="$(ls -t "$WORK"/obj-*/FxSubset.c | head -1)"; LIST="$(dirname "$FXC")/lib-c.list"
[ -s "$FXC" ] && [ -s "$LIST" ] || { echo "run ../build.sh first"; exit 1; }
cc_one() { local f="$1" d="$2" b; b="$(echo "${f#*/.lake/build/ir/}" | sed 's|.*/core-c/||; s|/|_|g; s|\.c$||')"
  [ -s "$OBJ/$d/$b.o" ] && return 0
  emcc $CFLAGS -c "$f" -o "$OBJ/$d/$b.o" 2>/dev/null || { echo "CC-FAIL $b" >&2; rm -f "$OBJ/$d/$b.o"; return 1; }; }
export -f cc_one; export CFLAGS OBJ
ls "$WORK"/core-c/*.c | xargs -P "$JOBS" -I{} bash -c 'cc_one "$@" core' _ {}
grep -v '/FxSubset.c$' "$LIST" | xargs -P "$JOBS" -I{} bash -c 'cc_one "$@" lib' _ {}
emcc $CFLAGS -c "$FXC" -o "$OBJ/lib/FxSubset.o"
emcc $CFLAGS -c "$LEAN_DIR/ffi/l4_ext.c" -o "$OBJ/lib/l4_ext.o"
emcc $CFLAGS -c "$HERE/fx_emcc.c" -o "$OBJ/lib/fx_emcc.o"
for s in debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io \
         hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex; do
  [ -s "$OBJ/rt/$s.o" ] || em++ -std=c++20 $CFLAGS -I "$RT_SRC" -I "$WORK/libuv/include" -c "$RT_SRC/runtime/$s.cpp" -o "$OBJ/rt/$s.o"
done
emcc $CFLAGS -c "$LEAN_DIR/Wasm/l4_stubs.c" -o "$OBJ/rt/l4_stubs.o"
[ -s "$OBJ/rt/mimalloc_static.o" ] || emcc $OPT $XFLAGS -DNDEBUG -DMI_SECURE=0 -Wno-unused-function \
   -I "$WORK/mimalloc/include" -c "$WORK/mimalloc/src/static.c" -o "$OBJ/rt/mimalloc_static.o"
em++ $OPT -DNDEBUG -fwasm-exceptions $XFLAGS "$OBJ"/lib/*.o "$OBJ"/core/*.o "$OBJ"/rt/*.o \
  -o "$OUT/fxsubset.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 \
  -sEXPORTED_FUNCTIONS=_fx_parse_c,_fx_query_c,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString \
  -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=8MB \
  -sENVIRONMENT=web,worker,node -sASSERTIONS=0 2> "$OUT/link.stderr" || { cat "$OUT/link.stderr"; exit 1; }
echo "  $OUT/fxsubset.wasm: $(wc -c < "$OUT/fxsubset.wasm") bytes; glue $(wc -c < "$OUT/fxsubset.mjs") bytes"
