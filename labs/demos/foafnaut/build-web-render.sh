#!/usr/bin/env bash
# Build only the HTML/DOM/style/layout/common-scene and SVG rendering closure.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$LAB/../../.." && pwd)
PROJECT="$ROOT/formal/lean4"
BUILD="$LAB/.build/web-render"
MODE=${1:---native}
case "$MODE" in --native|--wasm|--source-only) ;; *) echo 'usage: build-web-render.sh [--native|--wasm|--source-only]' >&2; exit 2;; esac
AVAILABLE=$(df -Pk "$ROOT" | awk 'NR==2 {print $4}')
if [ "$AVAILABLE" -lt 3145728 ]; then echo 'Need at least 3 GiB free before building' >&2; exit 1; fi
mkdir -p "$BUILD/olean" "$BUILD/ir" "$BUILD/obj-native" "$BUILD/obj-wasm" "$BUILD/engines"
if ! mkdir "$BUILD/lock"; then echo 'Web renderer build already running' >&2; exit 1; fi
trap 'rmdir "$BUILD/lock"' EXIT
# Lake always runs from this explicit project directory; no second Lean package.
cd "$PROJECT"
export LEAN_NUM_THREADS=2
export EMCC_CORES=2
export BINARYEN_CORES=2
if [ "$MODE" = --wasm ]; then
export EM_CACHE="$BUILD/emscripten-cache"
if [ ! -s "$EM_CACHE/sysroot_install.stamp" ]; then
  TOOL_CACHE=$(python3 - "$(command -v emcc)" <<'PY'
from pathlib import Path
import sys
print(Path(sys.argv[1]).resolve().parent/"cache")
PY
)
  mkdir -p "$EM_CACHE"
  cp -R "$TOOL_CACHE/." "$EM_CACHE/"
fi
fi
CORE=(L4Factoidal.Rendering.Layout L4Factoidal.Rendering.Links L4Factoidal.XML.NamespaceView L4Factoidal.Tdb2.Format L4Factoidal.Rendering.FloatFormat L4Factoidal.Syntax.IriResolve L4Factoidal.Rendering.RdfView)
lake build "${CORE[@]}" L4Factoidal.Rendering.Tests L4Factoidal.Rendering.RdfViewTests
export LEAN_PATH="$BUILD/olean:$PROJECT/.lake/build/lib/lean"
LAB_MODULES=(Graphics GraphicsPrepared Font SVGPath SVGReferences SVGCSS SVGDash SVGDashUnits SVGStroke SVG WebRenderSVG WebRender WebRenderRDF RenderPlan)
for module in "${LAB_MODULES[@]}"; do
  printf 'LEAN %s %s\n' "$module" "$(date -u)"
  lean -R "$LAB" -o "$BUILD/olean/$module.olean" -c "$BUILD/ir/$module.c" "$LAB/$module.lean"
done
lean -R "$LAB" "$LAB/WebRenderTests.lean"
lean -R "$LAB" -c "$BUILD/ir/WebRenderCLI.c" "$LAB/WebRenderCLI.lean"
# Enumerate exactly the project import closure, excluding the unrelated library.
python3 - "$PROJECT" "$BUILD/core-c-files.txt" <<'PY'
from pathlib import Path
import re,sys
project=Path(sys.argv[1]); seen=set(); order=[]
def visit(module):
    if module in seen or not module.startswith('L4Factoidal.'): return
    seen.add(module); source=project/Path(*module.split('.')).with_suffix('.lean')
    for imported in re.findall(r'^import\s+(\S+)',source.read_text(),re.M): visit(imported)
    order.append(str(project/'.lake/build/ir'/Path(*module.split('.')).with_suffix('.c')))
for module in ['L4Factoidal.Rendering.Layout','L4Factoidal.Rendering.Links','L4Factoidal.XML.NamespaceView','L4Factoidal.Tdb2.Format','L4Factoidal.Rendering.FloatFormat','L4Factoidal.Syntax.IriResolve','L4Factoidal.Rendering.RdfView']: visit(module)
Path(sys.argv[2]).write_text('\n'.join(order)+'\n')
PY
SOURCES=()
while IFS= read -r file; do SOURCES+=("$file"); done < "$BUILD/core-c-files.txt"
for module in "${LAB_MODULES[@]}"; do SOURCES+=("$BUILD/ir/$module.c"); done
if [ "$MODE" = --source-only ]; then echo 'WEB_RENDER_SOURCE_RC=0'; exit 0; fi
TOOLCHAIN=$(lean --print-prefix)
if [ "$MODE" = --native ]; then
  OBJECTS=()
  for source in "${SOURCES[@]}" "$BUILD/ir/WebRenderCLI.c"; do
    name=$(basename "$source" .c)
    # Prefix project paths to avoid names colliding with lab modules.
    case "$source" in *'/.lake/'*) name="Core_$(echo "$source" | sed 's|.*/ir/||;s|/|_|g;s|\.c$||')";; esac
    object="$BUILD/obj-native/$name.o"
    printf 'NATIVE %s %s\n' "$name" "$(date -u)"
    leanc -O2 -c "$source" -o "$object"
    OBJECTS+=("$object")
  done
  leanc -O2 -o "$BUILD/web-render-native" "${OBJECTS[@]}"
  echo "WEB_RENDER_NATIVE=$BUILD/web-render-native"
else
  RUNTIME=${FACTOIDAL_WASM_RUNTIME_CACHE:?Set verified Lean 4.33.1 runtime cache path}
  hash_file(){ shasum -a 256 "$1" | cut -d' ' -f1; }
  source="$RUNTIME/lean4-src/src/runtime/object.cpp"
  object="$RUNTIME/rt-obj/object.o"
  witness="$RUNTIME/rt-obj/object.wasm32-string-list.sha256"
  [ -s "$witness" ] && [ -s "$RUNTIME/core-obj/Init.o" ] && [ -s "$RUNTIME/rt-obj/mimalloc_static.o" ]
  grep -q 'wasm32 patch (build-wasm.sh step 1b)' "$source"
  [ "$(cat "$witness")" = "$(printf 'wasm32-string-list-v1\n%s\n%s\n' "$(hash_file "$source")" "$(hash_file "$object")")" ]
  for pair in 'MAJOR 4' 'MINOR 33' 'PATCH 1'; do
    read -r part value <<< "$pair"
    grep -q "^#define LEAN_VERSION_$part $value$" "$RUNTIME/wasm-include/lean/version.h"
  done
  printf '%s\n' "$RUNTIME" > "$BUILD/runtime-path.txt"
  cp "$witness" "$BUILD/runtime-object-witness.txt"
  OBJECTS=()
  FLAGS=(-O2 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I "$RUNTIME/wasm-include" -I "$TOOLCHAIN/include")
  for source in "${SOURCES[@]}" "$LAB/web_render_shim.c"; do
    name=$(basename "$source" .c)
    case "$source" in *'/.lake/'*) name="Core_$(echo "$source" | sed 's|.*/ir/||;s|/|_|g;s|\.c$||')";; esac
    object="$BUILD/obj-wasm/$name.o"
    printf 'WASM %s %s\n' "$name" "$(date -u)"
    emcc "${FLAGS[@]}" -c "$source" -o "$object"
    OBJECTS+=("$object")
  done
  em++ -O2 -DNDEBUG -fwasm-exceptions --no-entry "${OBJECTS[@]}" "$RUNTIME/core-obj/"*.o "$RUNTIME/rt-obj/"*.o \
    -o "$BUILD/engines/web-render.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 \
    -sEXPORTED_FUNCTIONS=_web_render_call,_web_render_rdf_call,_web_render_hit,_web_render_free -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString \
    -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1
  emcc "${FLAGS[@]}" -c "$LAB/render_plan_shim.c" -o "$BUILD/obj-wasm/render_plan_shim.o"
  em++ -O2 -DNDEBUG -fwasm-exceptions --no-entry "$BUILD/obj-wasm/RenderPlan.o" "$BUILD/obj-wasm/render_plan_shim.o" "$RUNTIME/core-obj/"*.o "$RUNTIME/rt-obj/"*.o \
    -o "$BUILD/engines/render-plan.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 \
    -sEXPORTED_FUNCTIONS=_render_plan,_render_plan_free -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString \
    -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1
  echo "WEB_RENDER_WASM=$BUILD/engines/web-render.mjs"
fi
python3 "$LAB/web-render/write-witness.py"
printf 'WEB_RENDER_BUILD_RC=0 %s\n' "$(date -u)"
