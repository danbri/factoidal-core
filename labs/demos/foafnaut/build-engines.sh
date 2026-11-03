#!/usr/bin/env bash
# Build small Lean WASM engines. No full Factoidal library build is needed.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$LAB/../../.." && pwd)
PROJECT="$REPO/formal/lean4"
. "$LAB/toolchain-versions.env"
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
BUILD="$LAB/.build"
hash_file() { if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }
RUNTIME=${FACTOIDAL_WASM_RUNTIME_CACHE:-${L4_WASM_WORK:-$BUILD/runtime}}
SOURCE_ONLY=false
while [ $# -gt 0 ]; do
  case "$1" in
    --runtime-cache) RUNTIME=${2:?missing runtime cache}; shift 2 ;;
    --source-only) SOURCE_ONLY=true; shift ;;
    *) echo "usage: $0 [--source-only] [--runtime-cache DIR]" >&2; exit 2 ;;
  esac
done
# Source-only preparation is also used by native packaging; no Emscripten
# executable or runtime cache is required when no WASM compilation is requested.
if [ "$SOURCE_ONLY" != true ]; then
  emcc --version | sed -n '1p' | grep -q "$EMSCRIPTEN_VERSION" || { echo "Use Emscripten $EMSCRIPTEN_VERSION" >&2; exit 1; }
fi
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
mkdir -p "$BUILD/ir" "$BUILD/olean/L4Factoidal/XML" "$BUILD/obj" "$BUILD/engines"
RUNTIME=$(mkdir -p "$RUNTIME" && cd "$RUNTIME" && pwd)
LOCK=${FOAFNAUT_BUILD_LOCK:-$BUILD/lean.lock}
if ! mkdir "$LOCK"; then echo "Lean build lock is busy: $LOCK" >&2; exit 1; fi
trap 'rmdir "$LOCK"' EXIT
cd "$PROJECT"
TOOLCHAIN=$(lean --print-prefix)
EXPECTED=$(tr -d ' \n' < lean-toolchain)
case "$EXPECTED" in *:v4.33.1) ;; *) echo "Re-audit runtime ABI for toolchain $EXPECTED" >&2; exit 1;; esac
if [ "$SOURCE_ONLY" != true ]; then
  runtime_patch_verified() {
    local source="$RUNTIME/lean4-src/src/runtime/object.cpp"
    local object="$RUNTIME/rt-obj/object.o"
    local witness="$RUNTIME/rt-obj/object.wasm32-string-list.sha256"
    [ -s "$source" ] && [ -s "$object" ] && [ -s "$witness" ] || return 1
    grep -q 'wasm32 patch (build-wasm.sh step 1b)' "$source" || return 1
    [ "$(cat "$witness")" = "$(printf 'wasm32-string-list-v1\n%s\n%s\n' "$(hash_file "$source")" "$(hash_file "$object")")" ]
  }
  if [ ! -s "$RUNTIME/core-obj/Init.o" ] || [ ! -s "$RUNTIME/rt-obj/mimalloc_static.o" ] || ! runtime_patch_verified; then
    echo "Cold or unverified Lean runtime/Init/Std cache: $RUNTIME"
    L4_WASM_RUNTIME_ONLY=1 bash "$PROJECT/Wasm/build-wasm.sh" "$RUNTIME"
  else
    echo "Reusing Lean runtime/Init/Std objects: $RUNTIME"
  fi
  runtime_patch_verified || { echo 'Runtime wasm32 string-list patch witness did not verify' >&2; exit 1; }
  cp "$RUNTIME/rt-obj/object.wasm32-string-list.sha256" "$BUILD/runtime-object-witness.txt"
  for pair in 'MAJOR 4' 'MINOR 33' 'PATCH 1'; do
    read -r PART VALUE <<< "$pair"
    grep -q "^#define LEAN_VERSION_$PART $VALUE$" "$RUNTIME/wasm-include/lean/version.h" \
      || { echo 'Runtime version does not match pinned Lean 4.33.1' >&2; exit 1; }
  done
else
  echo 'Source-only Lean compile: runtime fetch, C compilation and WASM linking are disabled'
fi
export LEAN_PATH="$BUILD/olean:$PROJECT/.lake/build/lib/lean"
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
  JSON/Value JSON/Parser JSON/Serialize UI/Geometry UI/LayoutPolicy UI/PolicyProtocol UI/Presentation Math/Affine Tdb2/Format Rendering/FloatFormat)
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
# Exact TOAN arithmetic/matrix modules are native test oracles, not GPU data.
for module in MathML/Rat Math/Matrix; do
  mkdir -p "$BUILD/olean/L4Factoidal/$(dirname "$module")"
  "$TOOLCHAIN/bin/lean" -R "$PROJECT" -o "$BUILD/olean/L4Factoidal/$module.olean" "$PROJECT/L4Factoidal/$module.lean"
done
"$TOOLCHAIN/bin/lean" -R "$PROJECT" --run "$PROJECT/L4Factoidal/Math/AffineTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB/foaf" -o "$BUILD/olean/FoafGraph.olean" \
  -c "$BUILD/ir/FoafGraph.c" "$LAB/foaf/FoafGraph.lean"
for name in Graphics GraphicsPrepared Font Geometry UI Demos SVGPath SVGReferences SVGCSS SVGDash SVGDashUnits SVGStroke SVG SceneSVG Solving SolvingPolicy SolvingSVG FoafNaut FoafPresentation FoafLiveBridge RenderPlan PolicyBridge; do
  "$TOOLCHAIN/bin/lean" -R "$LAB" -o "$BUILD/olean/$name.olean" -c "$BUILD/ir/$name.c" "$LAB/$name.lean"
done
"$TOOLCHAIN/bin/lean" -R "$LAB/foaf" --run "$LAB/foaf/Tests.lean" "$LAB/foaf/fixtures/people.ttl"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/FoafNautTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/GeometryTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" -o "$BUILD/olean/FoafGeometryProofs.olean" "$LAB/FoafGeometryProofs.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" -o "$BUILD/olean/FoafPresentationProofs.olean" "$LAB/FoafPresentationProofs.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/FoafPresentationTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SceneSVGTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGRootTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" -o "$BUILD/olean/SVGClipTests.olean" "$LAB/SVGClipTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" -o "$BUILD/olean/SVGUseTests.olean" "$LAB/SVGUseTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGPrerequisiteTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGTransformTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGPercentageTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGDashTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGLinearStrokeTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGStrokeProofs.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGPathLengthTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGDashUnitTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGDashUnitProofs.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGDashProofs.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGSamplingTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGCSSTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGCSSIntegrationTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGPathTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/SVGCapacityTests.lean"
for module in LayoutPolicyTests PolicyProtocolTests PresentationTests; do
  "$TOOLCHAIN/bin/lean" -R "$PROJECT" "$PROJECT/L4Factoidal/UI/$module.lean"
done
"$TOOLCHAIN/bin/lean" -R "$LAB" "$LAB/RenderPlanTests.lean"
"$TOOLCHAIN/bin/lean" -R "$LAB" --run "$LAB/GraphicsArtifact.lean" > "$BUILD/native-artifact.json"
rmdir "$LOCK"
trap - EXIT
if [ "$SOURCE_ONLY" = true ]; then
  echo 'Lean source modules, named SVG proofs and source regressions passed; no WASM engine was rebuilt.'
  exit 0
fi
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
  if ! em++ -O3 -DNDEBUG -fwasm-exceptions --no-entry "$@" \
    "$RUNTIME/core-obj/"*.o "$RUNTIME/rt-obj/"*.o -o "$BUILD/engines/$name.mjs" \
    -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 "-sEXPORTED_FUNCTIONS=$exports" \
    -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString -sALLOW_MEMORY_GROWTH=1 \
    -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1 \
    2> "$BUILD/$name.link.stderr"; then
    cat "$BUILD/$name.link.stderr" >&2
    return 1
  fi
  cat "$BUILD/$name.link.stderr" >&2
  if sed -n 's/.*function signature mismatch: //p' "$BUILD/$name.link.stderr" | grep -Ev '^(lean_io_create_tempfile|lean_io_create_tempdir)$'; then
    echo "Unexpected ABI mismatch linking $name" >&2; return 1
  fi
}
link_engine graphics-generator _graphics_call,_graphics_free "$BUILD/obj/Graphics.o" "$BUILD/obj/graphics_shim.o"
link_engine ui-engine _ui_init,_ui_step,_ui_free "$BUILD/obj/Graphics.o" "$BUILD/obj/UI.o" "$BUILD/obj/ui_shim.o"
link_engine demos-engine _demos_init,_demos_step,_demos_free "$BUILD/obj/Graphics.o" "$BUILD/obj/Demos.o" "$BUILD/obj/demos_shim.o"
link_engine svg-engine _svg_call,_svg_call_url,_svg_pixel,_svg_free "$BUILD/obj/Graphics.o" "$BUILD/obj/GraphicsPrepared.o" "$BUILD/obj/SVG.o" "$BUILD/obj/SVGCSS.o" "$BUILD/obj/SVGDash.o" "$BUILD/obj/SVGDashUnits.o" "$BUILD/obj/SVGStroke.o" "$BUILD/obj/SVGPath.o" "$BUILD/obj/SVGReferences.o" "$BUILD/obj/Core_Math_Affine.o" "$BUILD/obj/Core_Tdb2_Format.o" "$BUILD/obj/Core_Rendering_FloatFormat.o" "$BUILD/obj/Core_Syntax_IriResolve.o" "$BUILD/obj/svg_shim.o" "$BUILD/obj/"XML_*.o
link_engine render-plan _render_plan,_render_plan_free "$BUILD/obj/RenderPlan.o" "$BUILD/obj/render_plan_shim.o"
link_engine layout-policy-engine _layout_policy,_layout_policy_free "$BUILD/obj/PolicyBridge.o" "$BUILD/obj/policy_shim.o" "$BUILD/obj/"Core_*.o
link_engine foafnaut-engine _foafnaut_init,_foafnaut_init_policy,_foafnaut_step,_foafnaut_picture,_foafnaut_picture_checked,_foafnaut_export_svg,_foafnaut_text,_foafnaut_free,_foafnaut_live_start,_foafnaut_live_event,_foafnaut_live_text,_foafnaut_live_tick,_foafnaut_live_acknowledge,_foafnaut_live_export_svg,_foafnaut_live_dispose \
  "$BUILD/obj/Graphics.o" "$BUILD/obj/Font.o" "$BUILD/obj/Geometry.o" "$BUILD/obj/SceneSVG.o" "$BUILD/obj/FoafGraph.o" "$BUILD/obj/FoafNaut.o" \
  "$BUILD/obj/FoafPresentation.o" "$BUILD/obj/FoafLiveBridge.o" \
  "$BUILD/obj/foafnaut_shim.o" "$BUILD/obj/"Core_*.o
"$TOOLCHAIN/bin/lean" --version > "$BUILD/tool-versions.txt"
cd "$REPO"
if command -v sha256sum >/dev/null; then HASH_COMMAND=(sha256sum); else HASH_COMMAND=(shasum -a 256); fi
"${HASH_COMMAND[@]}" formal/lean4/L4Factoidal/XML/{Document,Parser,Wellformedness,Namespaces,NamespaceView}.lean \
  formal/lean4/Wasm/build-wasm.sh labs/demos/foafnaut/build-engines.sh \
  labs/demos/foafnaut/{Graphics,GraphicsPrepared,GraphicsArtifact,Font,Geometry,UI,Demos,SVGPath,SVGReferences,SVGCSS,SVGDash,SVGDashUnits,SVGStroke,SVG,SceneSVG,Solving,SolvingArtifact,SolvingPolicy,SolvingSVG,FoafNaut,FoafPresentation,FoafLiveBridge,RenderPlan,PolicyBridge}.lean \
  labs/demos/foafnaut/foaf/FoafGraph.lean > "$BUILD/source-SHA256SUMS"
for module in "${CORE_MODULES[@]}"; do
  "${HASH_COMMAND[@]}" "formal/lean4/L4Factoidal/$module.lean" >> "$BUILD/source-SHA256SUMS"
done
emcc --version >> "$BUILD/tool-versions.txt"
deno --version >> "$BUILD/tool-versions.txt"
echo "Foafnaut engines ready: $BUILD/engines"
