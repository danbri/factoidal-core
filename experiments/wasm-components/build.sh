#!/usr/bin/env bash
# build.sh — build the experiment's Lean subset (lean/WcCore.lean: the Turtle
# reader and the queryDataset query op) to wasm in several ways
# (https://github.com/danbri/factoidal/issues/1167, milestone 1):
#
#   build.sh c          Lean -> C for WcCore and its import closure
#   build.sh p1         wasi-sdk, wasm32-wasip1 core module (reactor)
#                       + the WIT exports, made a component with the
#                       wasi_snapshot_preview1 reactor adapter
#   build.sh p2         wasi-sdk, wasm32-wasip2: a component directly
#   build.sh emcc       Emscripten, the flags of Wasm/build-wasm.sh (baseline)
#   build.sh static     the p1 objects + a Rust static library, one core module
#   build.sh compose X  wac plug the Rust client component into engine X
#   build.sh all        c, p1, p2, emcc
#
# Variants (environment): WC_OPT=-O3|-Oz, WC_LTO=1 (-flto), WC_SIMD=1
# (-msimd128), WC_TAIL=1 (-mtail-call), WC_EH=wasm|trap (see below),
# WC_WASMOPT=1 (Binaryen -O after the link). Outputs go to $WC_OUT
# (default /opt/wc/out); nothing here touches the shipped build.
# Tools: tools/install.sh. Runtime patches: tools/patch-runtime-wasi.py.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$REPO/formal/lean4"
WC="${WC_TOOLS:-/opt/wc}"
OUT="${WC_OUT:-$WC/out}"
WORK="${WC_WORK:-$WC/work}"
OPT="${WC_OPT:--O3}"
VARIANT="${WC_VARIANT:-$(echo "${WC_OPT:--O3}" | tr -d - | tr A-Z a-z)}"
EXTRA=""
[ "${WC_LTO:-0}" = 1 ] && { EXTRA="$EXTRA -flto"; VARIANT="$VARIANT-lto"; }
[ "${WC_SIMD:-0}" = 1 ] && { EXTRA="$EXTRA -msimd128"; VARIANT="$VARIANT-simd"; WC_FEATURES="${WC_FEATURES:-} --enable-simd"; }
[ "${WC_TAIL:-0}" = 1 ] && { EXTRA="$EXTRA -mtail-call"; VARIANT="$VARIANT-tail"; WC_FEATURES="${WC_FEATURES:-} --enable-tail-call"; }
JOBS="${WC_JOBS:-4}"
# WC_EH=wasm: -fwasm-exceptions (C++ throw/catch as wasm exception handling)
# WC_EH=trap: catch blocks dropped, a throw traps (wasi-port/cxa_trap.cpp)
EH_MODE="${WC_EH:-wasm}"
if [ "$EH_MODE" = trap ]; then EH_CC="-fexceptions"; VARIANT="$VARIANT-trap"; else EH_CC="-fwasm-exceptions"; fi
export PATH="$HOME/.elan/bin:$WC/bin:$PATH"
TOOLCHAIN="$(cd "$LEAN_DIR" && lean --print-prefix)"
LEAN_SRC="$TOOLCHAIN/src/lean"
RT="$WC/lean4-src/src"
mkdir -p "$OUT" "$WORK"
say() { printf '\n=== %s\n' "$*"; }

# ---------------------------------------------------------------------
lean_c() {
  say "Lean -> C (WcCore and its import closure)"
  ( cd "$LEAN_DIR" && lake build L4Factoidal.Syntax.Turtle Wasm.Ops.Query >/dev/null )
  mkdir -p "$WORK/c"
  ( cd "$LEAN_DIR" && LEAN_PATH="$LEAN_DIR/.lake/build/lib/lean:$TOOLCHAIN/lib/lean" \
      "$TOOLCHAIN/bin/lean" -R "$HERE/lean" -c "$WORK/c/WcCore.c" "$HERE/lean/WcCore.lean" )
  python3 "$HERE/tools/closure.py" "$HERE/lean/WcCore.lean" "$LEAN_DIR" "$LEAN_SRC" > "$WORK/closure.txt"
  : > "$WORK/c.list"
  echo "$WORK/c/WcCore.c" >> "$WORK/c.list"
  while read -r kind path; do
    case "$kind" in
      repo) rel="${path#$LEAN_DIR/}"; c="$LEAN_DIR/.lake/build/ir/${rel%.lean}.c"
            [ -s "$c" ] || { echo "missing ir: $c"; exit 1; }
            echo "$c" >> "$WORK/c.list" ;;
      core) rel="${path#$LEAN_SRC/}"; c="$WORK/c/core/$(echo "${rel%.lean}" | tr / _).c"
            echo "$path $c" >> "$WORK/core-gen.list"; echo "$c" >> "$WORK/c.list" ;;
    esac
  done < "$WORK/closure.txt"
  mkdir -p "$WORK/c/core"
  sort -u "$WORK/core-gen.list" | while read -r src c; do
    [ -s "$c" ] || echo "$src $c"
  done | xargs -P "$JOBS" -L 1 sh -c \
    'LEAN_PATH="'"$TOOLCHAIN/lib/lean"'" "'"$TOOLCHAIN/bin/lean"'" -R "'"$LEAN_SRC"'" -c "$1" "$0" >/dev/null 2>&1 || echo "GEN-FAIL $0"'
  rm -f "$WORK/core-gen.list"
  echo "  C files: $(wc -l < "$WORK/c.list") ($(grep -c '/c/core/' "$WORK/c.list") toolchain)"
}

# ---------------------------------------------------------------------
# Shared headers: lean/config.h (mimalloc on, GMP off, as build-wasm.sh),
# version.h, mimalloc.h, githash.h.
headers() {
  local inc="$WORK/inc"
  mkdir -p "$inc/lean"
  printf '#pragma once\n#include <lean/version.h>\n#define LEAN_MIMALLOC\n#define LEAN_IS_STAGE0 0\n' > "$inc/lean/config.h"
  cp "$TOOLCHAIN/include/lean/version.h" "$inc/lean/"
  cp "$WC/mimalloc/include/mimalloc.h" "$inc/lean/mimalloc.h"
  printf '#pragma once\n#define LEAN_GITHASH "%s"\n' "$("$TOOLCHAIN/bin/lean" --githash)" > "$inc/githash.h"
  python3 "$HERE/tools/patch-runtime-wasi.py" "$RT" >/dev/null
}

RT_SRCS="debug thread mpz utf8 object apply exception interrupt memory stackinfo
         compact init_module io hash byteslice platform alloc allocprof sharecommon
         stack_overflow object_ref mpn mutex"

# compile_set <tag> <cc> <cxx> <cflags...>: objects into $WORK/obj-<tag>.
compile_set() {
  local tag="$1" cc="$2" cxx="$3"; shift 3
  local flags="$*" od="$WORK/obj-$tag"
  mkdir -p "$od/lean" "$od/rt"
  export od cc flags
  xargs -P "$JOBS" -I{} sh -c 'f="{}"; b=$(echo "$f" | md5sum | cut -c1-8)_$(basename "${f%.c}");
     [ -s "$od/lean/$b.o" ] || $cc $flags -c "$f" -o "$od/lean/$b.o" 2>>"$od/cc.err" || echo "CC-FAIL $f"' < "$WORK/c.list"
  for s in $RT_SRCS; do
    [ -s "$od/rt/$s.o" ] || $cxx -std=c++20 $flags -I "$RT" -c "$RT/runtime/$s.cpp" -o "$od/rt/$s.o"
  done
  [ -s "$od/rt/mimalloc.o" ] || $cc $OPT -DNDEBUG -DMI_SECURE=0 $EXTRA_CC_MI -Wno-unused-function \
      -I "$WC/mimalloc/include" -c "$WC/mimalloc/src/static.c" -o "$od/rt/mimalloc.o"
  $cc $flags -c "$HERE/c/wc_shim.c" -o "$od/rt/wc_shim.o"
  echo "  objects ($tag): $(ls "$od/lean" | wc -l) Lean, $(ls "$od/rt" | wc -l) runtime"
}

WASI_DEFS="-DLEAN_EMSCRIPTEN -D_WASI_EMULATED_SIGNAL -D_WASI_EMULATED_PROCESS_CLOCKS -D_WASI_EMULATED_MMAN -D_WASI_EMULATED_GETPID"
LEAN_WARN="-Wno-unused-parameter -Wno-unused-command-line-argument -Wno-parentheses-equality -Wno-unused-label -Wno-unused-but-set-variable"

# post_link <core.wasm>: the exnref translation (B11) and, with WC_WASMOPT=1,
# Binaryen's optimiser at the level Emscripten runs it at -O3/-Oz, so that the
# sizes compare like with like (emcc runs wasm-opt after wasm-ld).
post_link() {
  local f="$1" passes=""
  [ "$EH_MODE" = trap ] || passes="--translate-to-exnref"
  [ "${WC_WASMOPT:-0}" = 1 ] && passes="$passes $OPT"
  [ -n "$passes" ] || return 0
  "$WC/emsdk/upstream/bin/wasm-opt" --enable-exception-handling --enable-bulk-memory \
    --enable-nontrapping-float-to-int --enable-sign-ext --enable-mutable-globals \
    --enable-reference-types --enable-multivalue ${WC_FEATURES:-} $passes "$f" -o "$f.tmp"
  mv "$f.tmp" "$f"
}

wasi_build() {
  local target="$1" otag="$1-$VARIANT" tag="$1-$VARIANT"
  [ "${WC_WASMOPT:-0}" = 1 ] && tag="$tag-wo"
  local SDK="$WC/wasi-sdk"
  local cc="$SDK/bin/clang --target=$target --sysroot=$SDK/share/wasi-sysroot"
  local cxx="$SDK/bin/clang++ --target=$target --sysroot=$SDK/share/wasi-sysroot"
  headers
  say "wasi-sdk $target ($VARIANT: $OPT$EXTRA)"
  EXTRA_CC_MI="" compile_set "$otag" "$cc" "$cxx" \
    "$OPT -DNDEBUG $EXTRA $WASI_DEFS $EH_CC -I $HERE/wasi-port -I $HERE/wasi-port/uvonly -I $WORK/inc -I $RT/include $LEAN_WARN"
  local od="$WORK/obj-$otag"
  # wit-bindgen C bindings for world `engine`
  mkdir -p "$WORK/gen"
  wit-bindgen c "$HERE/wit/factoidal.wit" --world engine --out-dir "$WORK/gen" >/dev/null
  $cc $OPT -I "$WORK/gen" -c "$WORK/gen/engine.c" -o "$od/rt/engine.o"
  $cc $OPT -I "$WORK/gen" -c "$HERE/c/wc_component.c" -o "$od/rt/wc_component.o"
  $cc $OPT -c "$HERE/wasi-port/uv_stubs.c" -o "$od/rt/uv_stubs.o"
  $cxx $OPT -c "$HERE/wasi-port/process_stubs.cpp" -o "$od/rt/process_stubs.o"
  $cc $OPT -I "$WORK/inc" -I "$RT/include" -c "$LEAN_DIR/ffi/l4_ext.c" -o "$od/rt/l4_ext.o"
  local LIBS="-lwasi-emulated-signal -lwasi-emulated-process-clocks -lwasi-emulated-mman -lwasi-emulated-getpid"
  local EH="-fwasm-exceptions -lunwind"
  if [ "$EH_MODE" = trap ]; then
    $cxx $OPT -c "$HERE/wasi-port/cxa_trap.cpp" -o "$od/rt/cxa_trap.o"
    EH=""
  else
    rm -f "$od/rt/cxa_trap.o"
  fi
  case "$target" in
    wasm32-wasip1)
      $cxx $OPT $EXTRA -mexec-model=reactor $EH "$od"/lean/*.o "$od"/rt/*.o "$WORK/gen/engine_component_type.o" \
        $LIBS -Wl,--export=wc_init -Wl,-z,stack-size=8388608 -Wl,--strip-debug -Wl,--Map="$OUT/$tag.map" \
        -o "$OUT/$tag.core.wasm"
      post_link "$OUT/$tag.core.wasm"
      local ADAPTER="$WC/wasi_snapshot_preview1.reactor.wasm"
      wasm-tools component new "$OUT/$tag.core.wasm" --adapt "wasi_snapshot_preview1=$ADAPTER" \
        -o "$OUT/$tag.component.wasm"
      ;;
    wasm32-wasip2)
      $cxx $OPT $EXTRA -mexec-model=reactor $EH "$od"/lean/*.o "$od"/rt/*.o "$WORK/gen/engine_component_type.o" \
        $LIBS -Wl,--export=wc_init -Wl,-z,stack-size=8388608 -Wl,--strip-debug -Wl,--skip-wit-component \
        -Wl,--Map="$OUT/$tag.map" -o "$OUT/$tag.core.wasm"
      post_link "$OUT/$tag.core.wasm"
      wasm-tools component new "$OUT/$tag.core.wasm" -o "$OUT/$tag.component.wasm"
      ;;
  esac
  ls -l "$OUT/$tag".*.wasm
}

# The static-link variant (issue 1167 strategy 3): the wasip1 objects of
# wasi_build, the Rust static library rust-static (the driver of bench.rs),
# one core module, one memory, direct calls. A wasip1 command module.
static_build() {
  local target=wasm32-wasip1 otag="wasm32-wasip1-$VARIANT"
  local SDK="$WC/wasi-sdk" od="$WORK/obj-$otag"
  local cxx="$SDK/bin/clang++ --target=$target --sysroot=$SDK/share/wasi-sysroot"
  [ -s "$od/rt/wc_shim.o" ] || { echo "build.sh p1 first (with the same variant)"; exit 1; }
  say "static link: Lean objects + Rust staticlib ($VARIANT)"
  ( cd "$HERE/rust-static" && cargo build -q --release --target wasm32-wasip1 )
  local rt=() o
  for o in "$od"/rt/*.o; do
    case "$(basename "$o")" in engine.o|wc_component.o) ;; *) rt+=("$o") ;; esac
  done
  ${cxx/clang++/clang} $OPT -c "$HERE/c/wc_static_main.c" -o "$od/wc_static_main.o"
  local EH="-fwasm-exceptions -lunwind"
  [ "$EH_MODE" = trap ] && EH=""
  $cxx $OPT $EXTRA $EH "$od"/lean/*.o "${rt[@]}" "$od/wc_static_main.o" \
    "$HERE/rust-static/target/wasm32-wasip1/release/libwc_static.a" \
    -lwasi-emulated-signal -lwasi-emulated-process-clocks -lwasi-emulated-mman -lwasi-emulated-getpid \
    -Wl,-z,stack-size=8388608 -Wl,--strip-debug -o "$OUT/$otag-static.wasm"
  post_link "$OUT/$otag-static.wasm"
  ls -l "$OUT/$otag-static.wasm"
}

# compose <engine component>: wac plug the Rust client (rust-client) into it.
compose() {
  local engine="$1" out="${1%.component.wasm}.composed.wasm"
  ( cd "$HERE/rust-client" && cargo build -q --release --target wasm32-wasip2 )
  wac plug "$HERE/rust-client/target/wasm32-wasip2/release/wc-client.wasm" --plug "$engine" -o "$out"
  ls -l "$out"
}

emcc_build() {
  local tag="emcc-$VARIANT"
  # shellcheck disable=SC1091
  source "$WC/emsdk/emsdk_env.sh" >/dev/null 2>&1
  headers
  say "Emscripten ($VARIANT: $OPT$EXTRA)"
  # build-wasm.sh compiles runtime/object.cpp with its own step-1b patch; the
  # same defect is patched here by patch-runtime-wasi.py (B1), not wasi-guarded.
  EXTRA_CC_MI="" compile_set "$tag" emcc em++ \
    "$OPT -DNDEBUG $EXTRA -DLEAN_EMSCRIPTEN -fwasm-exceptions -I $WORK/inc -I $RT/include -I $HERE/wasi-port/uvonly $LEAN_WARN"
  local od="$WORK/obj-$tag"
  emcc $OPT -c "$HERE/wasi-port/uv_stubs.c" -o "$od/rt/uv_stubs.o"
  em++ $OPT -c "$HERE/wasi-port/process_stubs.cpp" -o "$od/rt/process_stubs.o"
  emcc $OPT -I "$WORK/inc" -I "$RT/include" -c "$LEAN_DIR/ffi/l4_ext.c" -o "$od/rt/l4_ext.o"
  em++ $OPT $EXTRA -fwasm-exceptions "$od"/lean/*.o "$od"/rt/*.o \
    -o "$OUT/$tag.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 \
    -sEXPORTED_FUNCTIONS=_wc_init,_wc_turtle_to_nquads_c,_wc_query_turtle_c,_wc_free,_malloc,_free \
    -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString,stringToUTF8,lengthBytesUTF8 \
    -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=8MB \
    -sENVIRONMENT=web,worker,node -sASSERTIONS=0 -Wl,--Map="$OUT/$tag.map"
  ls -l "$OUT/$tag".*
}

case "${1:-all}" in
  c) lean_c ;;
  p1) wasi_build wasm32-wasip1 ;;
  p2) wasi_build wasm32-wasip2 ;;
  emcc) emcc_build ;;
  static) static_build ;;
  compose) compose "$2" ;;
  all) lean_c; wasi_build wasm32-wasip1; wasi_build wasm32-wasip2; emcc_build ;;
  *) echo "usage: build.sh c|p1|p2|emcc|static|compose <component>|all"; exit 2 ;;
esac
