#!/bin/bash
# Build HarfBuzz to a standalone WebAssembly module for the Lean WasmVM engine
# (https://github.com/danbri/factoidal/issues/1244; record:
# docs/designissues/2026-11-07-wasmvm-engine.md, "HarfBuzz in the VM").
#
# Usage: tools/wasmvm/build-harfbuzz.sh [WORKDIR]
#   WORKDIR (default ~/working/hb-wasm) gets a shallow clone of HarfBuzz at the
#   pinned tag and the output harfbuzz-wasmvm.wasm. Nothing is written into the
#   repository. The output is not committed (owner decides later whether the binary
#   is vendored or built).
#
# HarfBuzz is MIT ("Old MIT", COPYING in the clone); https://github.com/harfbuzz/harfbuzz.
#
# Flags, and why:
#   -sSTANDALONE_WASM --no-entry  a module with WASI imports only and no JavaScript glue;
#                                 _initialize runs the C constructors
#   -fno-exceptions -fno-rtti     HarfBuzz needs neither
#   -DHB_NO_MT                    no threads, no atomics
#   -mno-simd128                  the engine has no SIMD yet (the default is already off;
#                                 stated so a later default change cannot add it)
#   -msign-ext -mbulk-memory -mnontrapping-fptoint -mmutable-globals -mmultivalue
#                                 not passed: these are the default features of this
#                                 emcc and the engine runs all of them
#   -sALLOW_MEMORY_GROWTH         fonts and buffers of any size
#   -Oz                           smallest code (-O2 build size is printed for comparison
#                                 when HB_BOTH=1)
# HarfBuzz's experimental Wasm shaper (HB_HAS_WASM) is not enabled: it is off unless
# the build defines it, and this build does not.
set -euo pipefail
HB_TAG=15.0.0
HB_COMMIT=35f656a1a2bab548ea7f54a6dd3fba2b09680d14
WORK=${1:-$HOME/working/hb-wasm}
HERE=$(cd "$(dirname "$0")" && pwd)
EMCC=${EMCC:-/opt/homebrew/bin/emcc}
SRC=$WORK/harfbuzz-$HB_TAG

mkdir -p "$WORK"
if [ ! -d "$SRC" ]; then
  git clone -q --depth 1 --branch "$HB_TAG" https://github.com/harfbuzz/harfbuzz.git "$SRC"
fi
got=$(git -C "$SRC" rev-parse HEAD)
if [ "$got" != "$HB_COMMIT" ]; then
  echo "harfbuzz $HB_TAG is at $got, expected $HB_COMMIT" >&2; exit 1
fi

build() {
  local opt=$1 out=$2
  local obj=$WORK/obj$opt
  mkdir -p "$obj"
  "$EMCC" "$opt" -std=c++17 -fno-exceptions -fno-rtti -DHB_NO_MT -mno-simd128 \
    -I"$SRC/src" -c "$SRC/src/harfbuzz.cc" -o "$obj/harfbuzz.o"
  "$EMCC" "$opt" -mno-simd128 -I"$SRC/src" -c "$HERE/harfbuzz/hb_wasmvm_entry.c" -o "$obj/entry.o"
  "$EMCC" "$opt" -fno-exceptions -mno-simd128 "$obj/harfbuzz.o" "$obj/entry.o" \
    -sSTANDALONE_WASM --no-entry -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=4MB \
    -o "$out"
  echo "$out: $(wc -c < "$out" | tr -d ' ') bytes"
}

build -Oz "$WORK/harfbuzz-wasmvm.wasm"
if [ "${HB_BOTH:-0}" = 1 ]; then build -O2 "$WORK/harfbuzz-wasmvm-O2.wasm"; fi
if command -v wasm-tools >/dev/null; then
  echo "imports:"; wasm-tools print "$WORK/harfbuzz-wasmvm.wasm" | grep '(import ' | sed 's/^ */  /'
  echo "exports:"; wasm-tools print "$WORK/harfbuzz-wasmvm.wasm" | grep '(export ' | sed 's/^ */  /'
fi
