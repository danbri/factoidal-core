#!/usr/bin/env bash
# Build small Lean WASM engines. No full Factoidal library build is needed.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$LAB/../../.." && pwd)
PROJECT="$REPO/formal/lean4"
. "$LAB/toolchain-versions.env"
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
emcc --version | sed -n '1p' | grep -q "$EMSCRIPTEN_VERSION" || { echo "Use Emscripten $EMSCRIPTEN_VERSION" >&2; exit 1; }
BUILD="$LAB/.build"
RUNTIME=${FACTOIDAL_WASM_RUNTIME_CACHE:-${L4_WASM_WORK:-$BUILD/runtime}}
while [ $# -gt 0 ]; do
  case "$1" in
    --runtime-cache) RUNTIME=${2:?missing runtime cache}; shift 2 ;;
    *) echo "usage: $0 [--runtime-cache DIR]" >&2; exit 2 ;;
  esac
done
mkdir -p "$BUILD/ir" "$BUILD/olean/L4Factoidal/XML" "$BUILD/obj" "$BUILD/engines"
RUNTIME=$(mkdir -p "$RUNTIME" && cd "$RUNTIME" && pwd)
LOCK=${FOAFNAUT_BUILD_LOCK:-$BUILD/lean.lock}
if ! mkdir "$LOCK"; then echo "Lean build lock is busy: $LOCK" >&2; exit 1; fi
trap 'rmdir "$LOCK"' EXIT
cd "$PROJECT"
TOOLCHAIN=$(lean --print-prefix)
EXPECTED=$(tr -d ' \n' < lean-toolchain)
case "$EXPECTED" in *:v4.33.1) ;; *) echo "Re-audit runtime ABI for toolchain $EXPECTED" >&2; exit 1;; esac
if [ ! -s "$RUNTIME/core-obj/Init.o" ] || [ ! -s "$RUNTIME/rt-obj/object.o" ] || [ ! -s "$RUNTIME/rt-obj/mimalloc_static.o" ]; then
  echo "Cold Lean runtime/Init/Std cache: $RUNTIME"
  L4_WASM_RUNTIME_ONLY=1 bash "$PROJECT/Wasm/build-wasm.sh" "$RUNTIME"
else
  echo "Reusing Lean runtime/Init/Std objects: $RUNTIME"
fi
for pair in 'MAJOR 4' 'MINOR 33' 'PATCH 1'; do
  read -r PART VALUE <<< "$pair"
  grep -q "^#define LEAN_VERSION_$PART $VALUE$" "$RUNTIME/wasm-include/lean/version.h" \
    || { echo 'Runtime version does not match pinned Lean 4.33.1' >&2; exit 1; }
done
export LEAN_PATH="$BUILD/olean:$PROJECT/.lake/build/lib/lean"
hash_file() { if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }
# Fresh source closure, independent of another checkout's XML .olean/C cache.
CLOSURE=lean-4.33.1
for name in Document Parser Wellformedness Namespaces NamespaceView; do
  SOURCE="$PROJECT/L4Factoidal/XML/$name.lean"
  CLOSURE="$CLOSURE $(hash_file "$SOURCE")"
  if [ "$(cat "$BUILD/ir/XML_$name.stamp" 2>/dev/null || true)" != "$CLOSURE" ]; then
    "$TOOLCHAIN/bin/lean" -R "$PROJECT" -o "$BUILD/olean/L4Factoidal/XML/$name.olean" \
      -c "$BUILD/ir/XML_$name.c" "$SOURCE"
    printf '%s' "$CLOSURE" > "$BUILD/ir/XML_$name.stamp"
  fi
done
# Fresh RDF/Turtle/JSON closure for the FOAF view. No JavaScript RDF parser.
CORE_MODULES=(RDF/XmlCanon RDF/Core RDF/Graph Encoding/Hex Syntax/Lexing
  Syntax/NTriples Syntax/IriResolve RDF/IriSyntax NatBounds Syntax/Turtle
  JSON/Value JSON/Parser JSON/Serialize UI/Geometry UI/LayoutPolicy UI/PolicyProtocol UI/Presentation)
CLOSURE=lean-4.33.1
for module in "${CORE_MODULES[@]}"; do
  SOURCE="$PROJECT/L4Factoidal/$module.lean"
  NAME="Core_${module//\//_}"
  CLOSURE="$CLOSURE $(hash_file "$SOURCE")"
  mkdir -p "$BUILD/olean/L4Factoidal/$(dirname "$module")"
  if [ "$(cat "$BUILD/ir/$NAME.stamp" 2>/dev/null || true)" != "$CLOSURE" ]; then
    "$TOOLCHAIN/bin/lean" -R "$PROJECT" -o "$BUILD/olean/L4Factoidal/$module.olean" \
      -c "$BUILD/ir/$NAME.c" "$SOURCE"
    printf '%s' "$CLOSURE" > "$BUILD/ir/$NAME.stamp"
  fi
done
"$TOOLCHAIN/bin/lean" -R "$LAB/foaf" -o "$BUILD/olean/FoafGraph.olean" \
  -c "$BUILD/ir/FoafGraph.c" "$LAB/foaf/FoafGraph.lean"
for name in Graphics Font Geometry UI Demos SVG SceneSVG FoafNaut RenderPlan PolicyBridge; do
  "$TOOLCHAIN/bin/lean" -R "$LAB" -o "$BUILD/olean/$name.olean" -c "$BUILD/ir/$name.c" "$LAB/$name.lean"
done
"$TOOLCHAIN/bin/lean" -R "$LAB/foaf" --run "$LAB/foaf/Tests.lean" "$LAB/foaf/fixtures/people.ttl"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/FoafNautTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/GeometryTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/FoafGeometryProofs.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SceneSVGTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGCapacityTests.lean"
for module in LayoutPolicyTests PolicyProtocolTests PresentationTests; do
  "$TOOLCHAIN/bin/lean" -R "$PROJECT" "$PROJECT/L4Factoidal/UI/$module.lean"
done
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/RenderPlanTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" --run "$LAB/Graphics.lean" > "$BUILD/native-artifact.json"
rmdir "$LOCK"
trap - EXIT
FLAGS=(-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I "$RUNTIME/wasm-include" -I "$TOOLCHAIN/include")
for source in "$BUILD/ir/"*.c "$LAB/graphics_shim.c" "$LAB/ui_shim.c" "$LAB/demos_shim.c" "$LAB/svg_shim.c" "$LAB/foafnaut_shim.c" "$LAB/render_plan_shim.c" "$LAB/policy_shim.c"; do
  name=$(basename "${source%.c}")
  HASH=$(hash_file "$source")
  if [ "$(cat "$BUILD/obj/$name.sha" 2>/dev/null || true)" != "$HASH" ]; then
    emcc "${FLAGS[@]}" -c "$source" -o "$BUILD/obj/$name.o"
    printf '%s' "$HASH" > "$BUILD/obj/$name.sha"
  fi
done
link_engine() {
  local name=$1 exports=$2; shift 2
  em++ -O3 -DNDEBUG -fwasm-exceptions --no-entry "$@" \
    "$RUNTIME/core-obj/"*.o "$RUNTIME/rt-obj/"*.o -o "$BUILD/engines/$name.mjs" \
    -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 "-sEXPORTED_FUNCTIONS=$exports" \
    -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString -sALLOW_MEMORY_GROWTH=1 \
    -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1 \
    2> "$BUILD/$name.link.stderr"
  cat "$BUILD/$name.link.stderr" >&2
  if sed -n 's/.*function signature mismatch: //p' "$BUILD/$name.link.stderr" | grep -Ev '^(lean_io_create_tempfile|lean_io_create_tempdir)$'; then
    echo "Unexpected ABI mismatch linking $name" >&2; return 1
  fi
}
link_engine graphics-generator _graphics_call,_graphics_free "$BUILD/obj/Graphics.o" "$BUILD/obj/graphics_shim.o"
link_engine ui-engine _ui_init,_ui_step,_ui_free "$BUILD/obj/Graphics.o" "$BUILD/obj/UI.o" "$BUILD/obj/ui_shim.o"
link_engine demos-engine _demos_init,_demos_step,_demos_free "$BUILD/obj/Graphics.o" "$BUILD/obj/Demos.o" "$BUILD/obj/demos_shim.o"
link_engine svg-engine _svg_call,_svg_pixel,_svg_free "$BUILD/obj/Graphics.o" "$BUILD/obj/SVG.o" "$BUILD/obj/svg_shim.o" "$BUILD/obj/"XML_*.o
link_engine render-plan _render_plan,_render_plan_free "$BUILD/obj/RenderPlan.o" "$BUILD/obj/render_plan_shim.o"
link_engine layout-policy-engine _layout_policy,_layout_policy_free "$BUILD/obj/PolicyBridge.o" "$BUILD/obj/policy_shim.o" "$BUILD/obj/"Core_*.o
link_engine foafnaut-engine _foafnaut_init,_foafnaut_init_policy,_foafnaut_step,_foafnaut_picture,_foafnaut_picture_checked,_foafnaut_export_svg,_foafnaut_text,_foafnaut_free \
  "$BUILD/obj/Graphics.o" "$BUILD/obj/Font.o" "$BUILD/obj/Geometry.o" "$BUILD/obj/SceneSVG.o" "$BUILD/obj/FoafGraph.o" "$BUILD/obj/FoafNaut.o" \
  "$BUILD/obj/foafnaut_shim.o" "$BUILD/obj/"Core_*.o
"$TOOLCHAIN/bin/lean" --version > "$BUILD/tool-versions.txt"
cd "$REPO"
if command -v sha256sum >/dev/null; then HASH_COMMAND=(sha256sum); else HASH_COMMAND=(shasum -a 256); fi
"${HASH_COMMAND[@]}" formal/lean4/L4Factoidal/XML/{Document,Parser,Wellformedness,Namespaces,NamespaceView}.lean \
  labs/demos/foafnaut/{Graphics,Font,Geometry,UI,Demos,SVG,SceneSVG,FoafNaut,RenderPlan,PolicyBridge}.lean \
  labs/demos/foafnaut/foaf/FoafGraph.lean > "$BUILD/source-SHA256SUMS"
for module in "${CORE_MODULES[@]}"; do
  "${HASH_COMMAND[@]}" "formal/lean4/L4Factoidal/$module.lean" >> "$BUILD/source-SHA256SUMS"
done
emcc --version >> "$BUILD/tool-versions.txt"
deno --version >> "$BUILD/tool-versions.txt"
echo "Foafnaut engines ready: $BUILD/engines"
