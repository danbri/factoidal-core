#!/usr/bin/env bash
#
# tools/lean-wasm-exe.sh ROOT_MODULE OUT_JS — build one Lean executable of
# formal/lean4 as a wasm32 program that node runs (`node OUT_JS ARGS...`).
# https://github.com/danbri/factoidal/issues/797
#
# It compiles the C that `lake build` wrote for ROOT_MODULE and for every
# module of this package it imports (transitively; the import lines of the
# .lean files), with the flags of Wasm/build-wasm.sh, and links them with the
# wasm32 objects of Lean's core library and runtime that build-wasm.sh left in
# its work directory (steps 1 to 5), plus Wasm/l4_stubs.c. So the program is
# compiled from the SAME generated C as the native executable, by emcc in place
# of clang. Files are read and written through node (-sNODERAWFS=1).
#
#   ROOT_MODULE  a module with a `main`, e.g. Harness.PrimBytesTest
#   OUT_JS       the program to write (OUT_JS and OUT_JS's .wasm)
#
# Needs: `lake build` of the executable first (formal/lean4/.lake/build/ir),
# emcc (on PATH, or /opt/emsdk), and L4_WASM_WORK (default /tmp/l4wasm-build)
# with core-obj/, rt-obj/, wasm-include/ and lean4-src/ from build-wasm.sh.
# Exit 2 when a prerequisite is missing, 1 when a compile or the link fails.
# Objects are cached in L4_WASM_EXE_OBJ (default $L4_WASM_WORK/exe-obj) and
# recompiled when their .c is newer.
set -uo pipefail
ROOT_MODULE="${1:?root module}"; OUT="${2:?output .js}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
LEAN_DIR="$REPO/formal/lean4"
WORK="${L4_WASM_WORK:-/tmp/l4wasm-build}"
OBJ="${L4_WASM_EXE_OBJ:-$WORK/exe-obj}"

if ! command -v emcc >/dev/null 2>&1 && [ -x /opt/emsdk/upstream/emscripten/emcc ]; then
  export PATH="/opt/emsdk:/opt/emsdk/upstream/emscripten:$PATH"
  export EMSDK=/opt/emsdk EM_CONFIG=/opt/emsdk/.emscripten
fi
command -v emcc >/dev/null 2>&1 || { echo "lean-wasm-exe: emcc not found"; exit 2; }
for d in core-obj rt-obj wasm-include lean4-src/src/include; do
  [ -d "$WORK/$d" ] || { echo "lean-wasm-exe: $WORK/$d missing (run formal/lean4/Wasm/build-wasm.sh first)"; exit 2; }
done
mkdir -p "$OBJ"

CFLAGS="-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I $WORK/wasm-include -I $WORK/lean4-src/src/include
        -Wno-unused-parameter -Wno-unused-command-line-argument -Wno-parentheses-equality"

# The import closure of ROOT_MODULE within this package.
MODS="$(python3 -I - "$LEAN_DIR" "$ROOT_MODULE" <<'EOF'
import os, re, sys
lean_dir, root = sys.argv[1], sys.argv[2]
seen, todo = [], [root]
while todo:
    m = todo.pop()
    if m in seen:
        continue
    path = os.path.join(lean_dir, *m.split('.')) + '.lean'
    if not os.path.exists(path):
        continue          # Init, Std, Lean: in the core objects
    seen.append(m)
    for line in open(path, encoding='utf-8'):
        r = re.match(r'\s*import\s+([\w.]+)', line)
        if r:
            todo.append(r.group(1))
print('\n'.join(seen))
EOF
)" || { echo "lean-wasm-exe: import closure failed"; exit 1; }
[ -n "$MODS" ] || { echo "lean-wasm-exe: $ROOT_MODULE not found under $LEAN_DIR"; exit 2; }

objs=()
while IFS= read -r m; do
  rel="${m//.//}"
  c="$LEAN_DIR/.lake/build/ir/$rel.c"
  [ -f "$c" ] || { echo "lean-wasm-exe: $c missing (lake build first)"; exit 2; }
  o="$OBJ/${rel//\//_}.o"
  if ! [ -s "$o" ] || [ "$c" -nt "$o" ]; then
    emcc $CFLAGS -c "$c" -o "$o.tmp" && mv "$o.tmp" "$o" \
      || { echo "lean-wasm-exe: CC-FAIL $m"; rm -f "$o.tmp"; exit 1; }
  fi
  objs+=("$o")
done <<< "$MODS"
emcc $CFLAGS -Wno-comment -c "$LEAN_DIR/Wasm/l4_stubs.c" -o "$OBJ/l4_stubs.o" || exit 1
# An executable's `main` calls lean_setup_args, which the runtime defines in
# runtime/libuv.cpp (not built for wasm32). This is the definition that file
# itself uses when it is built without libuv: the arguments unchanged.
printf '%s\n' 'char **lean_setup_args(int argc, char **argv) { (void)argc; return argv; }' > "$OBJ/l4_exe_stubs.c"
emcc $CFLAGS -c "$OBJ/l4_exe_stubs.c" -o "$OBJ/l4_exe_stubs.o" || exit 1

em++ -O3 -DNDEBUG -fwasm-exceptions \
  "${objs[@]}" "$OBJ/l4_stubs.o" "$OBJ/l4_exe_stubs.o" "$WORK"/core-obj/*.o "$WORK"/rt-obj/*.o \
  -o "$OUT" \
  -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=8MB \
  -sENVIRONMENT=node -sNODERAWFS=1 -sEXIT_RUNTIME=1 -sASSERTIONS=0 \
  || { echo "lean-wasm-exe: link failed"; exit 1; }
echo "lean-wasm-exe: $OUT ($(echo "$MODS" | wc -l | tr -d ' ') modules, emcc $(emcc --version | head -1 | sed 's/.*) //; s/ .*//'))"
