#!/usr/bin/env bash
# The units of Lean's runtime that an allocation and a free pass through (runtime/object.cpp,
# runtime/alloc.cpp and mimalloc's static.c), compiled as ThinLTO bitcode into one archive, so
# that the link of `leanjs` (lakefile.lean, `leanjsLto`) can inline them into BubblePopJS's code.
# The toolchain's libleanrt.a holds the same units as machine code; this archive comes first on
# the link line, so the linker takes these and never pulls the toolchain's members of the same
# name. Record: docs/designissues/2026-11-16-lean-memory-overhead.md, section D, and the Linux
# measurement of issue 471 (docs/designissues/2026-11-25-leanjs-lto-linux.md).
#
# Usage: leanrt-lto.sh OUT_DIR [TOOLCHAIN_PREFIX]   (writes OUT_DIR/libleanrt-lto.a)
#
# Sources, at the versions the toolchain was built from, fetched once into OUT_DIR/src:
#   Lean's runtime at the toolchain's tag (src/runtime, src/include, src/util);
#   mimalloc v2.2.3 (the GIT_TAG of the Lean release's CMakeLists.txt);
#   libuv v1.48.0 headers (src/CMakeLists.txt, ExternalProject libuv).
# LEANRT_LTO_LEAN_SRC may name a Lean checkout instead (its src/runtime is used).
#
# Flags: Lean's own for libleanrt (src/CMakeLists.txt, src/runtime/CMakeLists.txt), with
# LEAN_USE_GMP as the release builds define it, so object.cpp agrees with the toolchain's
# mpz.cpp about how a big number is stored. Needs clang++ with libc++ headers (Debian/Ubuntu:
# libc++-dev libc++abi-dev) and gmp.h (libgmp-dev, GMP 6.x as the toolchain's libgmp.a).
# To build `leanjs` without this: `lake build -K leanjsLto=off leanjs`.
set -euo pipefail
OUT=${1:?usage: leanrt-lto.sh OUT_DIR [TOOLCHAIN_PREFIX]}
mkdir -p "$OUT"
PREFIX=${2:-$(lean --print-prefix)}
VERSION=$("$PREFIX/bin/lean" --version | sed -E 's/^Lean \(version ([^ ,]+).*/\1/')
[ -n "$VERSION" ] || { echo "leanrt-lto: cannot read the Lean version" >&2; exit 1; }
CXX=${LEANRT_CXX:-clang++}
CC=${LEANRT_CC:-clang}
fail(){ echo "leanrt-lto: $1" >&2; echo "leanrt-lto: to build leanjs without link-time optimisation: lake build -K leanjsLto=off leanjs" >&2; exit 1; }
command -v "$CXX" >/dev/null || fail "$CXX not found (set LEANRT_CXX)"
echo '#include <vector>' | "$CXX" -stdlib=libc++ -x c++ -fsyntax-only - 2>/dev/null \
  || fail "$CXX can not compile against libc++ (install libc++-dev libc++abi-dev)"
echo '#include <gmp.h>' | "$CXX" -x c++ -fsyntax-only - 2>/dev/null || fail "no gmp.h (install libgmp-dev)"

SRCROOT="$OUT/src"
LEAN_SRC=${LEANRT_LTO_LEAN_SRC:-$SRCROOT/lean4-v$VERSION}
MIMALLOC_TAG=v2.2.3
LIBUV_TAG=v1.48.0
fetch(){ # dir tag url [sparse paths...]
  local dir=$1 tag=$2 url=$3; shift 3
  [ -d "$dir/.git" ] && return 0
  rm -rf "$dir.tmp"
  if [ $# -gt 0 ]; then
    git clone --quiet --filter=blob:none --sparse --depth 1 --branch "$tag" "$url" "$dir.tmp" \
      || fail "could not fetch $url at $tag"
    git -C "$dir.tmp" sparse-checkout set "$@"
  else
    git clone --quiet --depth 1 --branch "$tag" "$url" "$dir.tmp" || fail "could not fetch $url at $tag"
  fi
  mv "$dir.tmp" "$dir"
}
[ -f "$LEAN_SRC/src/runtime/object.cpp" ] || \
  fetch "$LEAN_SRC" "v$VERSION" https://github.com/leanprover/lean4 src/runtime src/include src/util
fetch "$SRCROOT/mimalloc-$MIMALLOC_TAG" "$MIMALLOC_TAG" https://github.com/microsoft/mimalloc
fetch "$SRCROOT/libuv-$LIBUV_TAG" "$LIBUV_TAG" https://github.com/libuv/libuv include
SRC="$LEAN_SRC/src"
MI="$SRCROOT/mimalloc-$MIMALLOC_TAG"

FLAGS=(-std=c++20 -O3 -DNDEBUG -DLEAN_USE_GMP -DLEAN_MULTI_THREAD -DLEAN_EXPORTING '-DLEAN_BUILD_TYPE="Release"'
  -ffp-contract=off -fvisibility=hidden -fvisibility-inlines-hidden -fPIC -stdlib=libc++ -D__CLANG__
  -I "$SRCROOT/libuv-$LIBUV_TAG/include" -flto=thin
  # the triple of the toolchain's clang, which compiles the engine's C: bitcode of one target
  "--target=$("$PREFIX/bin/clang" -print-target-triple)")
OBJ="$OUT/obj"
rm -rf "$OBJ"; mkdir -p "$OBJ"
pids=()
for unit in object alloc; do
  "$CXX" "${FLAGS[@]}" -I "$PREFIX/include" -I "$SRC" -w -c "$SRC/runtime/$unit.cpp" -o "$OBJ/$unit.cpp.o" &
  pids+=($!)
done
# Lean's MIMALLOC_FLAGS (src/runtime/CMakeLists.txt); Lean compiles static.c as C++.
"$CXX" "${FLAGS[@]}" -DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -DMI_WIN_NOREDIRECT -DMI_SECURE=0 \
  -I "$MI/include" -w -x c++ -c "$MI/src/static.c" -o "$OBJ/static.c.o" &
pids+=($!)
# glibc 2.38 and later headers send strtol and the like to __isoc23_* names under _GNU_SOURCE
# (always on for C++); the toolchain's older glibc, which leanc links against, has none. Hidden
# forwarders to the old functions, as labs/demos/foafnaut/build-leanrt-no-gmp.sh has them.
cat > "$OBJ/isoc23_compat.c" <<'EOF'
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#define HIDDEN __attribute__((visibility("hidden")))
HIDDEN long __isoc23_strtol(const char *s, char **e, int b) { return strtol(s, e, b); }
HIDDEN unsigned long __isoc23_strtoul(const char *s, char **e, int b) { return strtoul(s, e, b); }
HIDDEN long long __isoc23_strtoll(const char *s, char **e, int b) { return strtoll(s, e, b); }
HIDDEN unsigned long long __isoc23_strtoull(const char *s, char **e, int b) { return strtoull(s, e, b); }
HIDDEN int __isoc23_fscanf(FILE *f, const char *fmt, ...) { va_list a; va_start(a, fmt); int r = vfscanf(f, fmt, a); va_end(a); return r; }
HIDDEN int __isoc23_sscanf(const char *s, const char *fmt, ...) { va_list a; va_start(a, fmt); int r = vsscanf(s, fmt, a); va_end(a); return r; }
EOF
"$CC" -std=c11 -O2 -fPIC -c "$OBJ/isoc23_compat.c" -o "$OBJ/isoc23_compat.o" &
pids+=($!)
for pid in "${pids[@]}"; do wait "$pid" || fail "a runtime unit did not compile"; done
rm -f "$OUT/libleanrt-lto.a.tmp"
"$PREFIX/bin/llvm-ar" rcs "$OUT/libleanrt-lto.a.tmp" "$OBJ/object.cpp.o" "$OBJ/alloc.cpp.o" "$OBJ/static.c.o" "$OBJ/isoc23_compat.o"
mv "$OUT/libleanrt-lto.a.tmp" "$OUT/libleanrt-lto.a"
echo "$OUT/libleanrt-lto.a"
