#!/bin/bash
# Build QuickJS-NG to a standalone WebAssembly module for the Lean WasmVM engine
# (https://github.com/danbri/factoidal/issues/1244; record:
# docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").
#
# Usage: tools/wasmvm/build-quickjs.sh [WORKDIR]
#   WORKDIR (default ~/working/qjs-wasm) gets the QuickJS-NG source tarball at the
#   pinned tag (checked by SHA-256) and the output qjs-wasmvm.wasm. Nothing is written
#   into the repository, and the output is not committed.
#
# QuickJS-NG v0.18.0 is the version the Foafnaut script engine already pins
# (labs/demos/foafnaut/web-render/script-engine/quickjs.mjs). It is MIT licensed; see
# tools/wasmvm/quickjs/README.md and LICENSE in the tarball.
#
# Sources: the four library files of QuickJS-NG (quickjs.c, libregexp.c, libunicode.c,
# dtoa.c) and tools/wasmvm/quickjs/qjs_wasmvm_entry.c. Not quickjs-libc.c: page
# scripts get no std or os module, no files, no processes.
#
# Flags, and why:
#   -sSTANDALONE_WASM --no-entry  WASI imports only (from the C library) plus the
#                                 module's own foafnaut_dom imports; no JavaScript glue;
#                                 _initialize runs the C constructors
#   -sERROR_ON_UNDEFINED_SYMBOLS=0 the foafnaut_dom functions are imports, not
#                                 undefined symbols; they carry import_module attributes
#   -fno-exceptions               QuickJS is C; no C++ exceptions anywhere
#   no -pthread                   QuickJS-NG builds without threads by default here
#                                 (no atomics in the output; checked below)
#   -mno-simd128                  the engine has no SIMD
#   -sALLOW_MEMORY_GROWTH         the JS heap grows with the page
#   -sSTACK_SIZE=1MB              QuickJS recurses on the C stack (parser, interpreter);
#                                 its own limit (JS_SetMaxStackSize) is 768 KB
#   -O2                           (-Oz output size is printed for comparison when
#                                 QJS_BOTH=1)
set -euo pipefail
QJS_TAG=v0.18.0
QJS_SHA256=28bcd89aa3683fd2a946537e5ce3f11cc46b5cbf3383c7561aaef3df5ff9f1dd
WORK=${1:-$HOME/working/qjs-wasm}
HERE=$(cd "$(dirname "$0")" && pwd)
EMCC=${EMCC:-/opt/homebrew/bin/emcc}
SRC=$WORK/src/quickjs-${QJS_TAG#v}

mkdir -p "$WORK/src"
TAR=$WORK/qjs-ng-${QJS_TAG#v}.tar.gz
if [ ! -f "$TAR" ]; then
  curl -sSfL -o "$TAR" "https://github.com/quickjs-ng/quickjs/archive/refs/tags/$QJS_TAG.tar.gz"
fi
got=$(shasum -a 256 "$TAR" | cut -d' ' -f1)
if [ "$got" != "$QJS_SHA256" ]; then
  echo "quickjs-ng $QJS_TAG tarball has sha256 $got, expected $QJS_SHA256" >&2; exit 1
fi
[ -d "$SRC" ] || tar xzf "$TAR" -C "$WORK/src"
# Our patches (quickjs/patches/*.patch, in name order) go on a fresh copy of the pinned
# source each build, so $SRC stays as released and a changed patch always takes effect.
# 0001-map-hash-mix: Map, Set, WeakMap and WeakSet hash numbers and pointers so that
# node numbers and objects spread over the buckets (each get and set was linear in the
# size of the map for small integer keys: quadratic over a page's nodes).
PSRC=$WORK/src/quickjs-${QJS_TAG#v}-foafnaut
rm -rf "$PSRC"; cp -R "$SRC" "$PSRC"
for p in "$HERE"/quickjs/patches/*.patch; do patch -s -p1 -d "$PSRC" < "$p"; done
SRC=$PSRC

# The JavaScript prelude (quickjs/prelude.js) goes into the module as QuickJS-NG bytecode:
# a native build of the same pinned sources compiles it (quickjs/prelude_bytecode.c), so
# the guest reads bytecode when it loads instead of parsing the source.
mkdir -p "$WORK/gen" "$WORK/prelude-tool"
"${HOST_CC:-cc}" -O2 -D_GNU_SOURCE -funsigned-char -I"$SRC" \
  "$SRC/quickjs.c" "$SRC/libregexp.c" "$SRC/libunicode.c" "$SRC/dtoa.c" "$HERE/quickjs/prelude_bytecode.c" \
  -lm -o "$WORK/prelude-tool/prelude_bytecode"
"$WORK/prelude-tool/prelude_bytecode" "$HERE/quickjs/prelude.js" "$WORK/gen/prelude.h"
# The WebAssembly API glue (quickjs/webassembly.js) the same way; the prelude runs it on the
# first read of `WebAssembly` (native wasmGlue), so a page without WebAssembly never loads it.
"$WORK/prelude-tool/prelude_bytecode" "$HERE/quickjs/webassembly.js" "$WORK/gen/wasm_glue.h" wasm_glue

build() {
  local opt=$1 out=$2
  local obj=$WORK/obj$opt
  mkdir -p "$obj"
  local objs=()
  for f in quickjs libregexp libunicode dtoa; do
    "$EMCC" "$opt" -fno-exceptions -mno-simd128 -D_GNU_SOURCE -funsigned-char \
      -I"$SRC" -c "$SRC/$f.c" -o "$obj/$f.o"
    objs+=("$obj/$f.o")
  done
  "$EMCC" "$opt" -mno-simd128 -I"$SRC" -I"$WORK/gen" -c "$HERE/quickjs/qjs_wasmvm_entry.c" -o "$obj/entry.o"
  "$EMCC" "$opt" -fno-exceptions -mno-simd128 "${objs[@]}" "$obj/entry.o" \
    -sSTANDALONE_WASM --no-entry -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=4MB -sSTACK_SIZE=1MB \
    -sERROR_ON_UNDEFINED_SYMBOLS=0 \
    -o "$out"
  echo "$out: $(wc -c < "$out" | tr -d ' ') bytes"
}

build -O2 "$WORK/qjs-wasmvm.wasm"
if [ "${QJS_BOTH:-0}" = 1 ]; then build -Oz "$WORK/qjs-wasmvm-Oz.wasm"; fi
if command -v wasm-tools >/dev/null; then
  echo "imports:"; wasm-tools print "$WORK/qjs-wasmvm.wasm" | grep '(import ' | sed 's/^ */  /'
  echo "exports:"; wasm-tools print "$WORK/qjs-wasmvm.wasm" | grep '(export ' | sed 's/^ */  /'
  # Instructions and types only: the data segments hold the prelude's text, which may
  # name the words (the WebAssembly API reads a `shared` memory descriptor field).
  if wasm-tools print "$WORK/qjs-wasmvm.wasm" | grep -v '^ *(data ' | grep -q 'atomic\|shared'; then
    echo "error: the module uses atomics or shared memory" >&2; exit 1
  fi
fi
