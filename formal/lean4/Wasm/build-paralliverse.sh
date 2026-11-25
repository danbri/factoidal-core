#!/usr/bin/env bash
# Build the separate Hub CPU module using build-wasm.sh's runtime cache.
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "$0")/.." && pwd)"
ROOT="$(cd "$LEAN_DIR/../.." && pwd)"
RUNTIME="$(cd "${1:?usage: build-paralliverse.sh RUNTIME_CACHE [ASSETS]}" && pwd)"
ASSETS="${2:-$ROOT/docs/web/hub/assets/l4/paralliverse}"
mkdir -p "$ASSETS"
ASSETS="$(cd "$ASSETS" && pwd)"
BUILD="$(mktemp -d "$RUNTIME/paralliverse.XXXXXX")"
trap 'rm -rf "$BUILD"' EXIT

python3 "$ROOT/tools/lean-module-closure.py" --lean-dir "$LEAN_DIR" Wasm.ParalliverseHub > "$BUILD/modules.txt"
MODULES=()
while IFS= read -r source; do MODULES+=("${source%.lean}"); done < "$BUILD/modules.txt"
SOURCES=(formal/lean4/lean-toolchain formal/lean4/Wasm/build-wasm.sh
         formal/lean4/Wasm/build-paralliverse.sh formal/lean4/Wasm/paralliverse_shim.c
         formal/lean4/Wasm/paralliverse-smoke.mjs tools/wasm32-nat-literals.py
         tools/lean-module-closure.py docs/web/hub/paralliverse/worker.mjs
         docs/web/hub/paralliverse/gpu.mjs docs/web/hub/paralliverse/word-gpu.mjs)
for module in "${MODULES[@]}"; do SOURCES+=("formal/lean4/$module.lean"); done

# Capture the exact inputs before compiling. An unrelated generated file can
# change during the normal web build without affecting this source claim.
SOURCE_COMMIT="$(git -C "$ROOT" rev-parse --verify HEAD)"
SOURCE_ROOT="$BUILD/source"
for path in "${SOURCES[@]}"; do
  mkdir -p "$SOURCE_ROOT/$(dirname "$path")"
  if ! git -C "$ROOT" show "$SOURCE_COMMIT:$path" > "$SOURCE_ROOT/$path" ||
     ! cmp -s "$ROOT/$path" "$SOURCE_ROOT/$path"; then
    printf 'Paralliverse source differs from %s: %s\n' "$SOURCE_COMMIT" "$path" >&2
    exit 1
  fi
done

cd "$SOURCE_ROOT/formal/lean4"
export LEAN_STACK_SIZE_KB=16384
TOOLCHAIN="$(lean --print-prefix)"

hash_file() {
  if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1
  else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

RT_SRC="$RUNTIME/lean4-src/src"
RT_OBJ="$RUNTIME/rt-obj"
CORE_OBJ="$RUNTIME/core-obj"
WITNESS="$BUILD/runtime-patch.witness"
cp "$RT_OBJ/object.wasm32-string-list.sha256" "$WITNESS"
if ! grep -q 'wasm32 patch (build-wasm.sh step 1b)' "$RT_SRC/runtime/object.cpp" ||
   ! cmp -s "$TOOLCHAIN/include/lean/version.h" "$RUNTIME/wasm-include/lean/version.h" ||
   [ "$(cat "$WITNESS")" != "$(printf 'wasm32-string-list-v1\n%s\n%s\n' \
      "$(hash_file "$RT_SRC/runtime/object.cpp")" "$(hash_file "$RT_OBJ/object.o")")" ] ||
   [ ! -s "$RT_OBJ/mimalloc_static.o" ] || [ ! -s "$CORE_OBJ/Init.o" ]; then
  echo 'Paralliverse requires the matching patched Lean Wasm runtime cache.' >&2
  exit 1
fi

NAMES=()
for module in "${MODULES[@]}"; do
  name="${module##*/}"
  mkdir -p "$BUILD/olean/$(dirname "$module")"
  LEAN_PATH="$BUILD/olean:$TOOLCHAIN/lib/lean" "$TOOLCHAIN/bin/lean" -j1 -s16384 -M2048 -R "$PWD" \
    -o "$BUILD/olean/$module.olean" -c "$BUILD/$name.c" "$module.lean"
  case "$module" in */ParalliverseHub) grep -q 'initialize_Wasm_ParalliverseHub(' "$BUILD/$name.c";; esac
  NAMES+=("$name=$BUILD/$name.c")
done
FLAGS=(-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I "$RUNTIME/wasm-include" -I "$RT_SRC/include")
REWRITE="$SOURCE_ROOT/tools/wasm32-nat-literals.py"

# Reuse the existing Init objects unless their generated C needs the wasm32
# big-Nat rewrite. Check the rewritten and reused inputs before the link.
for source in "$RUNTIME/core-c/Init.c" "$RUNTIME/core-c/Init_"*.c; do
  name="$(basename "$source" .c)"
  NAMES+=("$name=$source")
done
python3 "$REWRITE" --batch "$BUILD/wasm32-src" "${NAMES[@]}" > "$BUILD/compile.list"
COMPILE=()
while IFS= read -r source; do COMPILE+=("$source"); done < "$BUILD/compile.list"
[ "${#COMPILE[@]}" = "${#NAMES[@]}" ]
python3 "$REWRITE" --check "${COMPILE[@]}"

OBJECTS=()
for i in "${!COMPILE[@]}"; do
  source="${COMPILE[$i]}"
  name="${NAMES[$i]%%=*}"
  if [ "$source" = "$RUNTIME/core-c/$name.c" ]; then
    object="$CORE_OBJ/$name.o"
    [ -s "$object" ]
  else
    object="$BUILD/$name.o"
    emcc "${FLAGS[@]}" -c "$source" -o "$object"
  fi
  OBJECTS+=("$object")
done
emcc "${FLAGS[@]}" -c Wasm/paralliverse_shim.c -o "$BUILD/paralliverse_shim.o"

LINK_STATUS=0
em++ -O3 -DNDEBUG -fwasm-exceptions --no-entry \
  "${OBJECTS[@]}" "$BUILD/paralliverse_shim.o" "$RT_OBJ/"*.o \
  -o "$BUILD/paralliverse.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 \
  -sEXPORTED_FUNCTIONS=_paralliverse_call_v1,_paralliverse_input_limit_v1,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=HEAPU8 \
  -sINCOMING_MODULE_JS_API=wasmBinary,locateFile \
  -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1 \
  2> "$BUILD/link.stderr" || LINK_STATUS=$?
cat "$BUILD/link.stderr" >&2
[ "$LINK_STATUS" -eq 0 ] || exit "$LINK_STATUS"
MISMATCHES=$(grep -o 'function signature mismatch: [A-Za-z0-9_]*' "$BUILD/link.stderr" \
  | sed 's/.*: //' | sort -u | grep -v -x -e lean_io_create_tempfile -e lean_io_create_tempdir) || MISMATCHES=""
if [ -n "$MISMATCHES" ]; then
  printf 'Paralliverse Wasm signature mismatch: %s\n' "$MISMATCHES" >&2
  exit 1
fi
node Wasm/paralliverse-smoke.mjs "$BUILD"

python3 - "$SOURCE_ROOT" "$BUILD" "$SOURCE_COMMIT" "${SOURCES[@]}" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys

source_root, build = map(Path, sys.argv[1:3])
source_commit, *sources = sys.argv[3:]

def describe(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}

witness = build / "runtime-patch.witness"
scheme, source_sha, object_sha = witness.read_text().splitlines()
manifest = {
    "abiVersion": 1,
    "inputLayoutVersion": 1,
    "sourceCommit": source_commit,
    "leanToolchain": (source_root / "formal/lean4/lean-toolchain").read_text().strip(),
    "emscripten": subprocess.check_output(["emcc", "--version"], text=True).splitlines()[0],
    "sources": {path: describe(source_root / path) for path in sources},
    "runtimePatch": {
        "scheme": scheme,
        "sourceSha256": source_sha,
        "objectSha256": object_sha,
        "witness": describe(witness),
    },
    "files": {name: describe(build / name) for name in ("paralliverse.mjs", "paralliverse.wasm")},
}
(build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"Paralliverse CPU Wasm: {manifest['files']['paralliverse.wasm']['bytes']} bytes")
PY
for name in paralliverse.mjs paralliverse.wasm manifest.json; do
  cp "$BUILD/$name" "$ASSETS/$name.tmp"
  mv "$ASSETS/$name.tmp" "$ASSETS/$name"
done
