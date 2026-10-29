#!/usr/bin/env bash
# build.sh — build the Factoidal subset (lean/FxSubset.lean: one RDF parse
# entry, one SPARQL query entry) plus the Lean v4.33.1 runtime with wasi-sdk,
# as a WebAssembly component that exports the WIT world in wit/.
#
# https://github.com/danbri/factoidal/issues/1167, milestone 1. An experiment:
# it changes nothing in the shipped build (formal/lean4/Wasm/build-wasm.sh),
# the npm package or any factoidal-builds workflow.
#
# Usage:
#   TARGET=wasip2 VARIANT=p2 experiments/wasm-components/build.sh
#   TARGET=wasip1 VARIANT=p1 experiments/wasm-components/build.sh
#   TARGET=wasip2 VARIANT=p2-tail XFLAGS="-mtail-call" experiments/wasm-components/build.sh
#
# Inputs (environment):
#   TARGET   wasip1 | wasip2                (default wasip2)
#   VARIANT  name of the output directory   (default $TARGET)
#   OPT      optimisation flag              (default -O3)
#   XFLAGS   extra code generation flags    (default none)
#   WASI_SDK wasi-sdk root                  (default /opt/tc/wasi-sdk-30.0-x86_64-linux)
#   TOOLS    directory with wasm-tools, wit-bindgen (default /opt/tc/bin)
#   WORK     work directory                 (default /opt/wc)
#   JOBS     parallel compile jobs          (default 4)
#   WASM_OPT wasm-opt level, e.g. -O3       (default: no wasm-opt pass)
# Prerequisites: setup-tools.sh; `lake build Wasm.Ops.Query Wasm.Ops.Parse`
# in formal/lean4 (it writes the library C into .lake/build/ir).
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$REPO/formal/lean4"
TARGET="${TARGET:-wasip2}"
VARIANT="${VARIANT:-$TARGET}"
OPT="${OPT:--O3}"
XFLAGS="${XFLAGS:-}"
WASI_SDK="${WASI_SDK:-/opt/tc/wasi-sdk-30.0-x86_64-linux}"
TOOLS="${TOOLS:-/opt/tc/bin}"
WORK="${WORK:-/opt/wc}"
JOBS="${JOBS:-4}"
export PATH="$HOME/.elan/bin:$PATH"
TC="$(cd "$LEAN_DIR" && lean --print-prefix)"
LEAN_TAG="$(sed 's|.*:||' "$LEAN_DIR/lean-toolchain" | tr -d ' \n')"
MIMALLOC_TAG=v2.2.7

case "$TARGET" in wasip1|wasip2) ;; *) echo "TARGET must be wasip1 or wasip2"; exit 1;; esac
say() { printf '\n=== %s\n' "$*"; }

# Object directories are keyed by everything that changes code generation.
KEY="$(printf '%s|%s|%s' "$TARGET" "$OPT" "$XFLAGS" | sha256sum | cut -c1-12)"
OBJ="$WORK/obj-$KEY"
OUT="$WORK/out/$VARIANT"
mkdir -p "$WORK" "$OBJ/core" "$OBJ/rt" "$OBJ/lib" "$OUT"
printf '%s\n' "target=$TARGET opt=$OPT xflags=$XFLAGS" > "$OBJ/KEY.txt"

CC="$WASI_SDK/bin/clang --target=wasm32-$TARGET --sysroot=$WASI_SDK/share/wasi-sysroot"
CXX="$WASI_SDK/bin/clang++ --target=wasm32-$TARGET --sysroot=$WASI_SDK/share/wasi-sysroot"
AR="$WASI_SDK/bin/llvm-ar"
RT_SRC="$WORK/lean4-src/src"
SHIM="$HERE/runtime-wasi/shim"
INC="$WORK/inc"
WASI_EMU="-D_WASI_EMULATED_SIGNAL -D_WASI_EMULATED_PROCESS_CLOCKS -D_WASI_EMULATED_MMAN -D_WASI_EMULATED_GETPID"
# LEAN_EMSCRIPTEN selects the runtime's single-threaded, no-libuv, no-getrandom
# paths; runtime-wasi/shim supplies the two Emscripten headers it then includes.
CFLAGS="$OPT -DNDEBUG -DLEAN_EMSCRIPTEN $WASI_EMU $XFLAGS -I $INC -I $RT_SRC/include
        -Wno-unused-parameter -Wno-unused-command-line-argument -Wno-parentheses-equality"

say "configuration"
echo "  target $TARGET, variant $VARIANT, opt $OPT, xflags '${XFLAGS}'"
echo "  wasi-sdk $(cat "$WASI_SDK/VERSION" 2>/dev/null | head -1), lean $LEAN_TAG"
echo "  objects $OBJ"

say "step 1 — Lean runtime sources at $LEAN_TAG, mimalloc $MIMALLOC_TAG, patches"
if [ ! -d "$RT_SRC/runtime" ]; then
  git clone -q --filter=blob:none --sparse --depth 1 --branch "$LEAN_TAG" \
      https://github.com/leanprover/lean4 "$WORK/lean4-src"
  (cd "$WORK/lean4-src" && git sparse-checkout set src/runtime src/include src/util)
fi
[ -d "$WORK/mimalloc" ] || git clone -q --depth 1 --branch "$MIMALLOC_TAG" \
    https://github.com/microsoft/mimalloc "$WORK/mimalloc"
# libuv headers only (io.cpp includes uv.h for declarations; no libuv code is
# linked). runtime-wasi/shim supplies netdb.h, termios.h and pwd.h for them.
[ -d "$WORK/libuv/include" ] || git clone -q --depth 1 --branch v1.48.0 \
    https://github.com/libuv/libuv "$WORK/libuv"
bash "$HERE/runtime-wasi/patch-runtime.sh" "$RT_SRC"

say "step 2 — configuration headers"
mkdir -p "$INC/lean"
printf '#pragma once\n#include <lean/version.h>\n#define LEAN_MIMALLOC\n#define LEAN_IS_STAGE0 0\n' > "$INC/lean/config.h"
cp "$TC/include/lean/version.h" "$INC/lean/version.h"
cp "$WORK/mimalloc/include/mimalloc.h" "$INC/lean/mimalloc.h"
printf '#pragma once\n#define LEAN_GITHASH "%s"\n' "$("$TC/bin/lean" --githash)" > "$INC/githash.h"

say "step 3 — regenerate the core library C (Init, Std.Data, Std.Time closure)"
CORE_C="$WORK/core-c"; mkdir -p "$CORE_C"
P="$JOBS" CORE_C="$CORE_C" TC="$TC" bash "$HERE/gen-core.sh"

say "step 4 — compile the core library C"
cc_core() {
  local f="$1" b; b="$(basename "${f%.c}")"
  [ -s "$OBJ/core/$b.o" ] && return 0
  $CC $CFLAGS -c "$f" -o "$OBJ/core/$b.o" 2>/dev/null || { echo "CC-FAIL $b" >&2; rm -f "$OBJ/core/$b.o"; return 1; }
}
export -f cc_core; export CC CFLAGS OBJ
ls "$CORE_C"/*.c | xargs -P "$JOBS" -I{} bash -c 'cc_core "$@"' _ {}
rm -f "$OBJ/libleaninit.a"; $AR rcs "$OBJ/libleaninit.a" "$OBJ"/core/*.o
echo "  core objects: $(ls "$OBJ"/core/*.o | wc -l)"

say "step 5 — compile the Lean runtime (24 files of the Emscripten build, minus 3) and mimalloc"
# Not compiled: stack_overflow.cpp (no signals; wasi_stubs.cpp), process.cpp
# (no processes), compact.cpp (no ELF program headers; .olean compaction).
RT_SRCS="debug thread mpz utf8 object apply exception interrupt memory stackinfo
         init_module io hash byteslice platform alloc allocprof sharecommon
         object_ref mpn mutex"
for s in $RT_SRCS; do
  [ -s "$OBJ/rt/$s.o" ] && continue
  $CXX -std=c++20 $CFLAGS -include "$SHIM/wasi_prelude.h" -I "$SHIM" -I "$WORK/libuv/include" -I "$RT_SRC" \
       -c "$RT_SRC/runtime/$s.cpp" -o "$OBJ/rt/$s.o"
done
$CXX -std=c++20 $CFLAGS -c "$HERE/runtime-wasi/wasi_stubs.cpp" -o "$OBJ/rt/wasi_stubs.o"
[ -s "$OBJ/rt/mimalloc_static.o" ] || $CC $OPT $XFLAGS -DNDEBUG -DMI_SECURE=0 -Wno-unused-function \
    -I "$WORK/mimalloc/include" -c "$WORK/mimalloc/src/static.c" -o "$OBJ/rt/mimalloc_static.o"
rm -f "$OBJ/libleanrt.a"; $AR rcs "$OBJ/libleanrt.a" "$OBJ"/rt/*.o
echo "  runtime objects: $(ls "$OBJ"/rt/*.o | wc -l)"

say "step 6 — the Factoidal subset: FxSubset.lean and its import closure"
(cd "$LEAN_DIR" && lake env lean -R "$HERE/lean" -c "$OBJ/FxSubset.c" "$HERE/lean/FxSubset.lean")
INIT_FN="$(grep -o '^LEAN_EXPORT lean_object\* initialize_[A-Za-z0-9_]*(uint8_t builtin)' "$OBJ/FxSubset.c" | head -1 | sed 's/.*lean_object\* //; s/(.*//')"
[ -n "$INIT_FN" ] || { echo "no module initialiser in FxSubset.c"; exit 1; }
echo "  module initialiser: $INIT_FN"
python3 "$HERE/closure.py" "$LEAN_DIR" "$HERE/lean/FxSubset.lean" > "$OBJ/lib-c.list"
echo "$OBJ/FxSubset.c" >> "$OBJ/lib-c.list"
cc_lib() {
  local f="$1" b h
  b="$(echo "${f#*/.lake/build/ir/}" | sed 's|/|_|g; s|\.c$||')"
  h="$(sha256sum "$f" | cut -c1-16)"
  [ -s "$OBJ/lib/$b.o" ] && [ "$(cat "$OBJ/lib/$b.o.sha" 2>/dev/null)" = "$h" ] && return 0
  $CC $CFLAGS -c "$f" -o "$OBJ/lib/$b.o" && echo "$h" > "$OBJ/lib/$b.o.sha" \
    || { echo "CC-FAIL $b" >&2; rm -f "$OBJ/lib/$b.o"; return 1; }
}
export -f cc_lib
xargs -P "$JOBS" -I{} bash -c 'cc_lib "$@"' _ {} < "$OBJ/lib-c.list"
# The SPARQL 1.1 section 17.6 extension-function call-out: off Emscripten
# ffi/l4_ext.c has no host and answers "no value". A component would import it.
$CC $CFLAGS -c "$LEAN_DIR/ffi/l4_ext.c" -o "$OBJ/lib/l4_ext.o"
rm -f "$OBJ/libfx.a"; $AR rcs "$OBJ/libfx.a" "$OBJ"/lib/*.o
echo "  library objects: $(wc -l < "$OBJ/lib-c.list")"

say "step 7 — WIT bindings (wit-bindgen C) and the glue"
GEN="$OBJ/gen"; rm -rf "$GEN"; mkdir -p "$GEN"
"$TOOLS/wit-bindgen" c "$HERE/wit" --world subset --out-dir "$GEN" >/dev/null
$CC $CFLAGS -I "$GEN" -c "$GEN/subset.c" -o "$OBJ/subset_bindings.o"
$CC $CFLAGS -I "$GEN" -DFX_INIT_MODULE="$INIT_FN" \
    -c "$HERE/component/fx_component.c" -o "$OBJ/fx_component.o"

say "step 8 — link"
LIBS="-lwasi-emulated-signal -lwasi-emulated-process-clocks -lwasi-emulated-mman -lwasi-emulated-getpid"
LINKFLAGS="$OPT $XFLAGS -mexec-model=reactor -Wl,--strip-debug -Wl,-z,stack-size=8388608 -Wl,--Map=$OUT/link.map"
OBJS="$OBJ/fx_component.o $OBJ/subset_bindings.o $GEN/subset_component_type.o"
# wasm-ld, like ELF lld, resolves references between archives in any order.
ARCHIVES="$OBJ/libfx.a $OBJ/libleaninit.a $OBJ/libleanrt.a"
# The core module first (for wasip2, wasm-component-ld with
# --skip-wit-component), then the optional wasm-opt pass that Emscripten runs
# at -O3, then `wasm-tools component new`, which reads the WIT type that
# subset_component_type.o embedded (and, for wasip1, adapts the Preview 1
# imports to Preview 2 with the reactor adapter).
SKIP=""; [ "$TARGET" = wasip2 ] && SKIP="-Wl,--skip-wit-component"
$CXX $LINKFLAGS $SKIP $OBJS $ARCHIVES $LIBS -o "$OUT/subset.core.wasm" 2> "$OUT/link.stderr" \
  || { cat "$OUT/link.stderr"; exit 1; }
cat "$OUT/link.stderr"
CORE="$OUT/subset.core.wasm"
if [ -n "${WASM_OPT:-}" ]; then
  # Same level as the Emscripten link (-O3 runs wasm-opt -O3); --strip-debug
  # also drops the name section, as Emscripten's release link does.
  wasm-opt $WASM_OPT --strip-debug --strip-producers --enable-bulk-memory --enable-nontrapping-float-to-int \
    --enable-sign-ext --enable-mutable-globals ${WASM_OPT_FEATURES:-} "$CORE" -o "$OUT/subset.opt.wasm"
  CORE="$OUT/subset.opt.wasm"
fi
echo "  core module: $(wc -c < "$CORE") bytes"
if [ "$TARGET" = wasip2 ]; then
  "$TOOLS/wasm-tools" component new "$CORE" -o "$OUT/subset.wasm"
else
  ADAPTER="$WORK/wasi_snapshot_preview1.reactor.wasm"
  [ -s "$ADAPTER" ] || { echo "missing $ADAPTER (setup-tools.sh)"; exit 1; }
  "$TOOLS/wasm-tools" component new "$CORE" \
      --adapt "wasi_snapshot_preview1=$ADAPTER" -o "$OUT/subset.wasm"
fi
"$TOOLS/wasm-tools" validate --features all "$OUT/subset.wasm"
"$TOOLS/wasm-tools" component wit "$OUT/subset.wasm" > "$OUT/subset.wit"
echo "  $OUT/subset.wasm: $(wc -c < "$OUT/subset.wasm") bytes"
