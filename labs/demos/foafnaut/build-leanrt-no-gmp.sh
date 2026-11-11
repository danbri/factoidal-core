#!/usr/bin/env bash
# Build Lean's runtime library without GNU MP, for the native Foafnaut link.
# Usage: build-leanrt-no-gmp.sh TOOLCHAIN_PREFIX CACHE_DIR
# Prints the path of libleanrt-no-gmp.a on its last line.
#
# Lean's release builds define LEAN_USE_GMP (src/CMakeLists.txt, USE_GMP). Without it the
# runtime uses its own big numbers (runtime/mpn.cpp, runtime/mpz.cpp), which is what the
# Wasm build has always used (formal/lean4/Wasm/build-wasm.sh, step 2).
#
# Only the four runtime objects that depend on how a big number is stored are rebuilt, from
# the matching Lean release's sources; the rest of the toolchain's libleanrt.a is kept, so
# mimalloc and everything else stay exactly as Lean shipped them. libInit/libStd do not
# reference GMP; libleancpp's objects that mention mpz (name, name_generator, expr, num,
# print) are not linked into the render library (ld -why_load, 2026-11-10).
set -euo pipefail
TOOLCHAIN=$1
CACHE=$2
VERSION=$("$TOOLCHAIN/bin/lean" --version | sed -E 's/^Lean \(version ([^ ,]+).*/\1/')
[ -n "$VERSION" ] || { echo "cannot read Lean version from $TOOLCHAIN" >&2; exit 1; }
HERE="$CACHE/$VERSION"
SOURCE_DIR=${LEAN4_RUNTIME_SRC:-${FACTOIDAL_WASM_RUNTIME_CACHE:-}/lean4-src}
if [ ! -f "$SOURCE_DIR/src/runtime/mpz.cpp" ]; then
  SOURCE_DIR="$HERE/lean4-src"
  [ -f "$SOURCE_DIR/src/runtime/mpz.cpp" ] || {
    rm -rf "$SOURCE_DIR"; mkdir -p "$HERE"
    git clone --quiet --filter=blob:none --sparse --depth 1 --branch "v$VERSION" \
      https://github.com/leanprover/lean4 "$SOURCE_DIR"
    ( cd "$SOURCE_DIR" && git sparse-checkout set src/runtime src/include src/util )
  }
fi
SRC="$SOURCE_DIR/src"
RUNTIME="$TOOLCHAIN/lib/lean/libleanrt.a"
UNITS=(mpz object compact sharecommon)
# Lean's own C++ flags for libleanrt on this platform (src/CMakeLists.txt, runtime/CMakeLists.txt);
# LEAN_USE_GMP is the one difference. LEAN_MIMALLOC comes from the toolchain's lean/config.h,
# so allocation matches the rest of the toolchain's objects.
FLAGS=(-std=c++20 -O3 -DNDEBUG -DLEAN_MULTI_THREAD -DLEAN_EXPORTING '-DLEAN_BUILD_TYPE="Release"'
  -ffp-contract=off -fvisibility=hidden -fvisibility-inlines-hidden -ftls-model=local-exec)
[ "$(uname -s)" = Linux ] && FLAGS+=(-fPIC)
CXX=${CXX:-c++}
OUT="$HERE/libleanrt-no-gmp.a"
STAMP="$OUT.stamp"
want(){
  shasum -a 256 "$RUNTIME" | cut -d' ' -f1
  for unit in "${UNITS[@]}"; do shasum -a 256 "$SRC/runtime/$unit.cpp" | cut -d' ' -f1; done
  printf '%s\n' "$CXX" "${FLAGS[@]}"
  "$CXX" --version | head -1
}
if [ -s "$OUT" ] && [ -f "$STAMP" ] && [ "$(want)" = "$(cat "$STAMP")" ]; then
  echo "$OUT"; exit 0
fi
OBJ="$HERE/obj"
rm -rf "$OBJ"; mkdir -p "$OBJ"
pids=()
for unit in "${UNITS[@]}"; do
  ( cd "$OBJ" && "$CXX" "${FLAGS[@]}" -I "$TOOLCHAIN/include" -I "$SRC" -w \
      -c "$SRC/runtime/$unit.cpp" -o "$OBJ/$unit.cpp.o" ) &
  pids+=($!)
done
for pid in "${pids[@]}"; do wait "$pid"; done
cp "$RUNTIME" "$OUT.tmp"
chmod u+w "$OUT.tmp"
ar d "$OUT.tmp" mpz.cpp.o object.cpp.o compact.cpp.o sharecommon.cpp.o
( cd "$OBJ" && ar r "$OUT.tmp" mpz.cpp.o object.cpp.o compact.cpp.o sharecommon.cpp.o 2>/dev/null )
ranlib "$OUT.tmp" 2>/dev/null
if nm "$OUT.tmp" 2>/dev/null | grep -q '_gmp'; then echo "GMP reference left in $OUT.tmp" >&2; exit 1; fi
mv "$OUT.tmp" "$OUT"
want > "$STAMP"
echo "$OUT"
