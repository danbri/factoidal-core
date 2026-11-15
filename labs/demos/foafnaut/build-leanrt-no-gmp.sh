#!/usr/bin/env bash
# Build Lean's runtime library without GNU MP, for the native Foafnaut link.
# Usage: build-leanrt-no-gmp.sh TOOLCHAIN_PREFIX CACHE_DIR
# Prints the path of libleanrt-no-gmp.a on its last line.
#
# On Linux the result also goes into a shared library (libweb-render.so) that a host opens
# with dlopen, so that no Lean toolchain is needed at run time. The toolchain's libleanrt.a
# is built with -ftls-model=local-exec, which a shared object can not hold (the linker
# refuses R_X86_64_TPOFF32). So on Linux the units with thread-local variables are compiled
# again with -ftls-model=initial-exec, as Lean compiles its own libleanrt_initial-exec.a for
# libleanshared.so (src/runtime/CMakeLists.txt), and the archive is checked to hold no
# local-exec TLS relocation. Their thread-local data is about 200 bytes, well inside the
# static TLS that glibc keeps for libraries opened later. The toolchain's C++ objects use
# libc++, so these are compiled with clang++ -stdlib=libc++ (Debian/Ubuntu: libc++-dev
# libc++abi-dev); the libuv and mimalloc headers are those of the versions Lean pins.
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
OS=$(uname -s)
if [ "$OS" = Linux ]; then
  # The units of libleanrt.a with thread-local variables (objdump -r: R_X86_64_TPOFF32),
  # and mimalloc's static.c, which Lean compiles as C++ with MIMALLOC_FLAGS.
  UNITS+=(alloc interrupt io memory stackinfo thread)
  MIMALLOC_TAG=v2.2.7   # src/CMakeLists.txt, LEAN_MI_SECURE comment
  LIBUV_TAG=v1.48.0     # src/CMakeLists.txt, ExternalProject libuv
  for pin in "mimalloc $MIMALLOC_TAG https://github.com/microsoft/mimalloc" "libuv $LIBUV_TAG https://github.com/libuv/libuv"; do
    read -r name tag url <<< "$pin"
    [ -f "$HERE/$name-$tag/include/$([ "$name" = libuv ] && echo uv.h || echo mimalloc.h)" ] || {
      rm -rf "$HERE/$name-$tag"; mkdir -p "$HERE"
      git clone --quiet --depth 1 --branch "$tag" "$url" "$HERE/$name-$tag"
    }
  done
fi
# Lean's own C++ flags for libleanrt on this platform (src/CMakeLists.txt, runtime/CMakeLists.txt);
# LEAN_USE_GMP is the one difference. LEAN_MIMALLOC comes from the toolchain's lean/config.h,
# so allocation matches the rest of the toolchain's objects.
FLAGS=(-std=c++20 -O3 -DNDEBUG -DLEAN_MULTI_THREAD -DLEAN_EXPORTING '-DLEAN_BUILD_TYPE="Release"'
  -ffp-contract=off -fvisibility=hidden -fvisibility-inlines-hidden)
if [ "$OS" = Linux ]; then
  FLAGS+=(-fPIC -ftls-model=initial-exec -stdlib=libc++ -D__CLANG__ -I "$HERE/libuv-$LIBUV_TAG/include")
  CXX=${LEANRT_CXX:-clang++}
  echo '#include <vector>' | "$CXX" -stdlib=libc++ -x c++ -fsyntax-only - 2>/dev/null || {
    echo "$CXX can not compile against libc++: install libc++-dev and libc++abi-dev (Lean's C++ runtime uses libc++)" >&2; exit 1; }
else
  FLAGS+=(-ftls-model=local-exec)
  CXX=${CXX:-c++}
fi
OUT="$HERE/libleanrt-no-gmp.a"
STAMP="$OUT.stamp"
want(){
  shasum -a 256 "$RUNTIME" | cut -d' ' -f1
  for unit in "${UNITS[@]}"; do shasum -a 256 "$SRC/runtime/$unit.cpp" | cut -d' ' -f1; done
  if [ "$OS" = Linux ]; then echo "mimalloc $MIMALLOC_TAG libuv $LIBUV_TAG"; fi
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
MEMBERS=()
for unit in "${UNITS[@]}"; do MEMBERS+=("$unit.cpp.o"); done
if [ "$OS" = Linux ]; then
  # Lean's MIMALLOC_FLAGS (src/runtime/CMakeLists.txt), compiled as C++ like Lean does.
  ( cd "$OBJ" && "$CXX" "${FLAGS[@]}" -DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -DMI_WIN_NOREDIRECT -DMI_SECURE=0 \
      -I "$HERE/mimalloc-$MIMALLOC_TAG/include" -w -x c++ -c "$HERE/mimalloc-$MIMALLOC_TAG/src/static.c" -o "$OBJ/static.c.o" ) &
  pids+=($!)
  MEMBERS+=(static.c.o)
fi
for pid in "${pids[@]}"; do wait "$pid"; done
cp "$RUNTIME" "$OUT.tmp"
chmod u+w "$OUT.tmp"
ar d "$OUT.tmp" "${MEMBERS[@]}"
( cd "$OBJ" && ar r "$OUT.tmp" "${MEMBERS[@]}" 2>/dev/null )
ranlib "$OUT.tmp" 2>/dev/null
if nm "$OUT.tmp" 2>/dev/null | grep -q '_gmp'; then echo "GMP reference left in $OUT.tmp" >&2; exit 1; fi
if [ "$OS" = Linux ]; then
  # No local-exec TLS may be left: x86_64 R_X86_64_TPOFF32, aarch64 R_AARCH64_TLSLE_*.
  LE=$(readelf -rW "$OUT.tmp" | grep -c -E 'R_X86_64_TPOFF32|R_AARCH64_TLSLE' || true)
  [ "$LE" = 0 ] || { echo "$LE local-exec TLS relocations left in $OUT.tmp" >&2; readelf -rW "$OUT.tmp" | grep -E 'File:|TPOFF32|TLSLE' | head >&2; exit 1; }
fi
mv "$OUT.tmp" "$OUT"
want > "$STAMP"
echo "$OUT"
