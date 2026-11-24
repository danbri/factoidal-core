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
# C compiles of the generated Lean IR and HACL* are independent, so they run COMPILE_JOBS
# at a time (default: the core count, at most 4; COMPILE_JOBS=1 is the old serial order).
# Objects are linked in the same order as before, whatever order they finish in.
# FOAFNAUT_CC_LAUNCHER (for example ccache) goes in front of the native C compiler; for
# Wasm, Emscripten's own EM_COMPILER_WRAPPER does the same.
CPUS=$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)
COMPILE_JOBS=${COMPILE_JOBS:-$(( CPUS < 4 ? CPUS : 4 ))}
LAUNCH=()
[ -n "${FOAFNAUT_CC_LAUNCHER:-}" ] && LAUNCH=("$FOAFNAUT_CC_LAUNCHER")
COMPILE_PIDS=()
COMPILE_FAILED=0
# Every compile command, one per line, shell-quoted: CI recompiles a sample without its cache
# and compares the objects (factoidal-builds scripts/cache-audit.sh).
COMPILE_LOG="$BUILD/compile-commands.txt"
: > "$COMPILE_LOG"
# compile_bg COMMAND...: start one compile, after waiting for the oldest when COMPILE_JOBS run.
compile_bg(){
  printf '%q ' "$@" >> "$COMPILE_LOG"; printf '\n' >> "$COMPILE_LOG"
  if [ "${#COMPILE_PIDS[@]}" -ge "$COMPILE_JOBS" ]; then
    wait "${COMPILE_PIDS[0]}" || COMPILE_FAILED=1
    COMPILE_PIDS=(${COMPILE_PIDS[@]+"${COMPILE_PIDS[@]:1}"})
  fi
  "$@" &
  COMPILE_PIDS+=($!)
}
# compile_wait: wait for every started compile; any failure stops the build.
compile_wait(){
  local pid
  for pid in ${COMPILE_PIDS[@]+"${COMPILE_PIDS[@]}"}; do wait "$pid" || COMPILE_FAILED=1; done
  COMPILE_PIDS=()
  [ "$COMPILE_FAILED" = 0 ] || { echo 'A C compile failed (its error is above); build refused' >&2; exit 1; }
}
if [ "$MODE" = --wasm ]; then
export EM_CACHE="$BUILD/emscripten-cache"
if [ ! -s "$EM_CACHE/sysroot_install.stamp" ]; then
  TOOL_CACHE=$(python3 - "$(command -v emcc)" <<'PY'
from pathlib import Path
import sys
emcc=Path(sys.argv[1]).resolve().parent
# Beside emcc in an emsdk install; ../libexec/cache in a Homebrew one.
print(next((c for c in (emcc/"cache",emcc.parent/"libexec"/"cache") if c.is_dir()),emcc/"cache"))
PY
)
  mkdir -p "$EM_CACHE"
  cp -R "$TOOL_CACHE/." "$EM_CACHE/"
fi
fi
# BubblePopJS's realm as data: the prelude runs once here, and LeanJSRealmData.lean (not in
# git) holds the heap it leaves, which the first page decodes (WasmVM/Hosts/LeanJSRealm.lean).
# LeanJS's include_str inputs (prelude.js, webassembly.js) are Lake input_files its library
# needs (lakefile.lean), so a newer prelude rebuilds LeanJS, and the realm, in this lake build.
PRELUDE="$ROOT/tools/wasmvm/quickjs/prelude.js"
lake build bubblepop-realm
# BubblePopJS is the default on the Hub too, so the Wasm build carries the realm as data
# (+598 KB, +140 KB gzipped, 2026-11-09 figures): the first page does not lex and run prelude.js.
REALM_SOURCE="$PRELUDE"
.lake/build/bin/bubblepop-realm L4Factoidal/WasmVM/Hosts/LeanJSRealmData.lean "$REALM_SOURCE"
CORE=(L4Factoidal.Epub L4Factoidal.Par.Chunked L4Factoidal.Codec.Inflate L4Factoidal.Codec.VP8Alpha L4Factoidal.DOM.OfXml L4Factoidal.Rendering.Layout L4Factoidal.Rendering.SfntProfile L4Factoidal.Rendering.Links L4Factoidal.XML.NamespaceView L4Factoidal.Tdb2.Format L4Factoidal.Rendering.FloatFormat L4Factoidal.Syntax.IriResolve L4Factoidal.Rendering.RdfView L4Factoidal.Rendering.FontRequests L4Factoidal.Unicode.BidiData L4Factoidal.Unicode.Bidi L4Factoidal.XSLT.Transform L4Factoidal.XSLT4.Transform L4Factoidal.UI.PolicyProtocol L4Factoidal.UI.Presentation L4Factoidal.UI.Geometry L4Factoidal.UI.LayoutPolicy L4Factoidal.Syntax.Turtle L4Factoidal.JSON.Parser L4Factoidal.JSON.Serialize L4Factoidal.WasmVM.Api L4Factoidal.WasmVM.Bench.Engine L4Factoidal.WasmVM.Tests.Proposals L4Factoidal.WasmVM.Wasi L4Factoidal.WasmVM.Hosts.Page L4Factoidal.WasmVM.Hosts.PageAot L4Factoidal.WHATWG.Encoding.Sniff L4Factoidal.WasmVM.Hosts.LeanJS L4Factoidal.WasmVM.Hosts.LeanJSRealm L4Factoidal.WasmVM.Hosts.LeanJSWorkers L4Factoidal.EventLoop.Model L4Factoidal.EventLoop.Dispatch L4Factoidal.SPARQL.Query L4Factoidal.SPARQL.Parser L4Factoidal.SPARQL.StorePlan L4Factoidal.Planner.Kinds.Memory L4Factoidal.Planner.FromQuery L4Factoidal.RDF.Pretty L4Factoidal.FrameCost.Band L4Factoidal.FrameCost.Lru L4Factoidal.Rendering.ComputedValues L4Factoidal.Rendering.FontFaceRule L4Factoidal.Rendering.Smil L4Factoidal.Rendering.ClipTheorems L4Factoidal.Rendering.InkBound L4Factoidal.HTML.CspSource L4Factoidal.Net.Subresource L4Factoidal.Rendering.GridResolved L4Factoidal.Rendering.ImportTree L4Factoidal.HostContract.Trace L4Factoidal.HTML.AccessibleTree)
lake build "${CORE[@]}" L4Factoidal.Rendering.Tests L4Factoidal.Rendering.CascadeTests L4Factoidal.Rendering.TableLayoutTests L4Factoidal.Rendering.FlexLayoutTests L4Factoidal.Rendering.PositionLayoutTests L4Factoidal.Rendering.GridLayoutTests L4Factoidal.Rendering.ReplacedTests L4Factoidal.Rendering.RdfViewTests L4Factoidal.Rendering.FontLayoutTests L4Factoidal.Rendering.FontFaceTests L4Factoidal.Rendering.FontProviderTests L4Factoidal.Rendering.FontDataTests L4Factoidal.Rendering.FontFaceRuleTests L4Factoidal.Rendering.SfntMarkTheorems L4Factoidal.Rendering.SmilTests L4Factoidal.Rendering.InkBoundTests L4Factoidal.WasmVM.Tests.LeanJSRealm L4Factoidal.WasmVM.Tests.LeanJSWorkers L4Factoidal.DOM.XPath.Theorems L4Factoidal.FrameCost.Cull
export LEAN_PATH="$BUILD/olean:$PROJECT/.lake/build/lib/lean"
LAB_MODULES=(Graphics GraphicsPrepared Font SVGPathData SVGCurves SVGPath SVGReferences SVGCSS SVGDash SVGDashUnits SVGStroke ImagePNG ImageJPEG ImageGIF ImageData SVG SVGRaster SVGText SVGForgiving SVGCssColour WebRenderSVG WebRender WebHit WebRenderRDF WebRenderFont WebRenderFontRequests WebRenderScript WebSelection WebHistory WebRoute WebGesture WebShell WebPrint Geometry SceneSVG FoafGraph FoafNaut WebGraph WebXslt WebWasmSample WebWasm WebEventLoop WebScripts WebState WebSparql WebRepaint WebAccept WebConsole WebPaint WebBuild WebAbout WebHostContract WebDocument RenderPlan)
# The engine's own build facts (WebBuild.lean reads this file with include_str when it
# compiles): the release number of npm/factoidal/package.json, the full commit, the build
# time, uncommitted changes, and whether the commit is the tagged release. Made here from
# git, never typed. After the hygiene ratchet below runs, its counts are added and the
# modules from WebBuild on are compiled again, so the engine states them too.
ENGINE_VERSION=$(sed -n 's/^  "version": "\([^"]*\)".*/\1/p' "$ROOT/npm/factoidal/package.json" | head -1)
ENGINE_COMMIT=$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || true)
ENGINE_DIRTY=false
[ -n "$(git -C "$ROOT" status --porcelain --untracked-files=no 2>/dev/null)" ] && ENGINE_DIRTY=true
ENGINE_RELEASE=false
if [ "$ENGINE_DIRTY" = false ] && [ -n "$ENGINE_VERSION" ] && git -C "$ROOT" tag --points-at HEAD 2>/dev/null | grep -qx "v$ENGINE_VERSION"; then ENGINE_RELEASE=true; fi
printf 'version=%s\ncommit=%s\nbuiltAt=%s\ndirty=%s\nrelease=%s\n' "$ENGINE_VERSION" "$ENGINE_COMMIT" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$ENGINE_DIRTY" "$ENGINE_RELEASE" > "$BUILD/engine-build.txt"
for module in "${LAB_MODULES[@]}"; do
  printf 'LEAN %s %s\n' "$module" "$(date -u)"
  lean -R "$LAB" -o "$BUILD/olean/$module.olean" -c "$BUILD/ir/$module.c" "$LAB/$module.lean"
done
# Lean hygiene ratchet (issue 390; docs/designissues/2026-11-11-lean-hygiene-ratchet.md).
# LabHygiene.lean counts the unsafe, implemented_by, partial def, extern and opaque
# declarations Lean recorded for these modules and the L4Factoidal modules they import;
# its theorem lab_ratchet fails to compile when a count is above its baseline. It must
# import every module above; its counts become the build record's hygiene field.
# Not linked: no runtime code.
rm -f "$BUILD/hygiene.json"
for module in "${LAB_MODULES[@]}"; do
  grep -qx "import $module" "$LAB/LabHygiene.lean" 2>/dev/null || { echo "LabHygiene.lean does not import $module: the hygiene ratchet would not see it; build refused" >&2; exit 1; }
done
printf 'LEAN LabHygiene %s\n' "$(date -u)"
lean -R "$LAB" "$LAB/LabHygiene.lean" | tee "$BUILD/hygiene.log"
sed -n 's/^HYGIENE_JSON //p' "$BUILD/hygiene.log" > "$BUILD/hygiene.json"
[ -s "$BUILD/hygiene.json" ] || { echo 'LabHygiene.lean printed no HYGIENE_JSON line; build refused' >&2; exit 1; }
# The ratchet's counts into the engine's build facts, then WebBuild and the modules after it again.
python3 - "$BUILD/hygiene.json" >> "$BUILD/engine-build.txt" <<'PY'
import json,sys
counts=json.load(open(sys.argv[1]))
for part,key in (("lab","hygieneLab"),("formal","hygieneFormal")):
    c=counts[part]
    print(f"{key}={c['modules']} modules: {c['unsafe']} unsafe, {c['implemented_by']} implemented_by, {c['partial_def']} partial def, {c['extern']} extern, {c['opaque']} opaque")
PY
AFTER=0
for module in "${LAB_MODULES[@]}"; do
  [ "$module" = WebBuild ] && AFTER=1
  [ "$AFTER" = 1 ] || continue
  printf 'LEAN %s %s (with hygiene counts)\n' "$module" "$(date -u)"
  lean -R "$LAB" -o "$BUILD/olean/$module.olean" -c "$BUILD/ir/$module.c" "$LAB/$module.lean"
done
for check in WebRenderTests WebRenderFontRequestsTests WebRenderScriptTests WebDocumentTests; do
  lean -R "$LAB" "$LAB/$check.lean"
done
lean -R "$LAB" "$LAB/WebRenderCurveTests.lean"
lean -R "$LAB" "$LAB/SVGForgivingTests.lean"
lean -R "$LAB" "$LAB/WebHitTests.lean"
lean -R "$LAB" "$LAB/SVGTextTests.lean"
# Incremental equals full (issue 513): theorems about the tile edge lists and the retained compile; no runtime code.
lean -R "$LAB" "$LAB/IncrementalProofs.lean"
lean -R "$LAB" "$LAB/SVGGradientTests.lean"
lean -R "$LAB" "$LAB/ImageTests.lean"
lean -R "$LAB" "$LAB/ImageGIFTests.lean"
lean -R "$LAB" "$LAB/SVGImageTests.lean"
lean -R "$LAB" "$LAB/WebSparqlTests.lean"
lean -R "$LAB" -c "$BUILD/ir/WebRenderCLI.c" "$LAB/WebRenderCLI.lean"
# Enumerate exactly the project import closure, excluding the unrelated library.
python3 - "$PROJECT" "$BUILD/core-c-files.txt" "${CORE[@]}" <<'PY'
from pathlib import Path
import re,sys
project=Path(sys.argv[1]); seen=set(); order=[]
STD_IN_WASM=('Std.Data.','Std.Classes.','Std.Do.','Std.Time.')
def visit(module):
    if module in seen or not module.startswith('L4Factoidal.'): return
    seen.add(module); source=project/Path(*module.split('.')).with_suffix('.lean')
    for imported in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
        # The Wasm runtime holds Init and only these parts of Std (formal/lean4/Wasm/build-wasm.sh):
        # any other Std module, or Std whole, is an undefined initialize_Std* at the Wasm link.
        if (imported=='Std' or imported.startswith('Std.')) and not imported.startswith(STD_IN_WASM):
            sys.exit(f'{source}: import {imported}: the Wasm engine links only Std.Data, Std.Classes, Std.Do and the Std.Time modules of build-wasm.sh; import the module you use')
        visit(imported)
    order.append(str(project/'.lake/build/ir'/Path(*module.split('.')).with_suffix('.c')))
for module in sys.argv[3:]: visit(module)
Path(sys.argv[2]).write_text('\n'.join(order)+'\n')
PY
SOURCES=()
while IFS= read -r file; do SOURCES+=("$file"); done < "$BUILD/core-c-files.txt"
# HACL* for crypto.subtle (L4Factoidal/Crypto/WebHacl.lean; record
# docs/designissues/2026-11-09-hacl-web-crypto.md): the vendored, unmodified units the
# boundary ffi/hacl_webcrypto.c calls, and their link closure (BLAKE2 and MD5 for Hacl_HMAC.c).
# Portable C only: no Vale assembly, no vector units, so native and Wasm are the same code.
HACL="$ROOT/third_party/hacl"
HACL_SOURCES=("$PROJECT/ffi/hacl_webcrypto.c")
for unit in Hacl_Hash_SHA1 Hacl_Hash_SHA2 Hacl_Hash_SHA3 Hacl_HMAC Hacl_Hash_Blake2s Hacl_Hash_Blake2b Hacl_Hash_MD5 Hacl_Ed25519 \
  Hacl_Curve25519_51 Hacl_P256 Hacl_AEAD_Chacha20Poly1305 Hacl_Chacha20 Hacl_MAC_Poly1305 Hacl_Bignum Hacl_Bignum64 Hacl_RSAPSS Lib_Memzero0; do
  HACL_SOURCES+=("$HACL/src/$unit.c")
done
for module in "${LAB_MODULES[@]}"; do SOURCES+=("$BUILD/ir/$module.c"); done
if [ "$MODE" = --source-only ]; then echo 'WEB_RENDER_SOURCE_RC=0'; exit 0; fi
TOOLCHAIN=$(lean --print-prefix)
# Public C entry points of web_render_shim.c, with the linker's leading underscores.
SHIM_EXPORTS=(
  _web_render_call _web_render_rdf_call _web_render_font_call _web_render_font_requests_call
  _web_document_call _web_document_call_bin _web_document_font_call_bin _web_document_image_call_bin
  _web_document_decode_call_bin _web_document_decode2_call_bin _web_render_hit _web_render_free
)
# Fails the build if GNU MP reached a linked binary (issue 393).
assert_no_gmp(){
  if nm "$1" 2>/dev/null | grep -q '__gmp'; then
    echo "GNU MP symbols in $1 ($(nm "$1" 2>/dev/null | grep -c '__gmp')), expected none" >&2
    exit 1
  fi
  echo "NO_GMP $(basename "$1"): nm shows no __gmp symbol"
}
if [ "$MODE" = --native ]; then
  # FOAFNAUT_NATIVE_LTO=1 (macOS; off by default): ThinLTO across the engine's C and the units of
  # Lean's runtime that an allocation and a free pass through (build-leanrt-no-gmp.sh, LEANRT_LTO).
  # The shipped build calls mi_malloc_small, lean_dec_ref_cold, lean_del_core and mi_free across
  # the library boundary for every cell; inlined, the library corpus runs in 0.85 of the time and
  # a held-out Test262 selection in 0.77 to 0.88 (docs/designissues/2026-11-16-lean-memory-overhead.md,
  # section D). The engine's C is then compiled by the system clang with leanc's own flags
  # (`leanc --print-cflags`: among them -ffp-contract=off and -fvisibility=hidden), because the
  # system linker reads only its own compiler's bitcode. The library grows by about 5%, so it is
  # checked under its own budget name until a budget for it is recorded.
  NATIVE_LTO=0
  [ "${FOAFNAUT_NATIVE_LTO:-0}" = 1 ] && [ "$(uname -s)" = Darwin ] && NATIVE_LTO=1
  LTO_LINK=()
  [ "$NATIVE_LTO" = 1 ] && LTO_LINK=(-flto=thin)
  echo "NATIVE_LTO=$NATIVE_LTO"
  OBJECTS=()
  for source in "${SOURCES[@]}" "$BUILD/ir/WebRenderCLI.c"; do
    name=$(basename "$source" .c)
    # Prefix project paths to avoid names colliding with lab modules.
    case "$source" in *'/.lake/'*) name="Core_$(echo "$source" | sed 's|.*/ir/||;s|/|_|g;s|\.c$||')";; esac
    object="$BUILD/obj-native/$name.o"
    printf 'NATIVE %s %s\n' "$name" "$(date -u)"
    # -O3 -DNDEBUG as Lake compiles Lean's C. Without NDEBUG every inline function of
    # lean.h that reads an object (lean_ctor_get, lean_array_get_core, ...) runs its
    # assert: the native library ran WasmVM at half the speed of the Wasm engine
    # (fib 58 against 119 million instructions a second; WasmVM record, "In the Foafnaut
    # engine").
    # No heartbeat count at each allocation (lean_no_heartbeat.h): the engine never reads it.
    if [ "$NATIVE_LTO" = 1 ]; then
      # shellcheck disable=SC2046  # leanc's flags are separate words
      compile_bg ${LAUNCH[@]+"${LAUNCH[@]}"} "${CC:-cc}" $(leanc --print-cflags) -Wno-unused-command-line-argument -O3 -DNDEBUG -flto=thin -include "$LAB/lean_no_heartbeat.h" -Dlean_inc_heartbeat=foafnaut_no_heartbeat -c "$source" -o "$object"
    else
    compile_bg ${LAUNCH[@]+"${LAUNCH[@]}"} leanc -O3 -DNDEBUG -include "$LAB/lean_no_heartbeat.h" -Dlean_inc_heartbeat=foafnaut_no_heartbeat -c "$source" -o "$object"
    fi
    OBJECTS+=("$object")
  done
  for source in "${HACL_SOURCES[@]}"; do
    object="$BUILD/obj-native/hacl_$(basename "$source" .c).o"
    printf 'NATIVE %s %s\n' "$(basename "$source" .c)" "$(date -u)"
    # -fPIC: these objects also go into the Linux shared library, and Hacl_RSAPSS.c and
    # Hacl_Hash_SHA3.c name `stderr` (KaRaMeL's error print), which a shared object must reach
    # through the GOT ("relocation R_X86_64_PC32 cannot be used against symbol 'stderr'").
    compile_bg ${LAUNCH[@]+"${LAUNCH[@]}"} "${CC:-cc}" -O3 -DNDEBUG -fPIC -I "$HACL/include" -I "$TOOLCHAIN/include" -c "$source" -o "$object"
    OBJECTS+=("$object")
  done
  compile_wait
  LEANLIB="$TOOLCHAIN/lib/lean"
  # Native macOS builds link Lean's runtime without GNU MP (issue 393): see
  # build-leanrt-no-gmp.sh. The Linux library does too (below); the Linux web-render-native
  # program still links through leanc with GMP (not yet changed).
  if [ "$(uname -s)" = Darwin ]; then
    LEANRT=$(LEANRT_LTO="$NATIVE_LTO" "$LAB/build-leanrt-no-gmp.sh" "$TOOLCHAIN" "$LAB/.build/leanrt-no-gmp" | tail -1)
    "${CC:-cc}" -O3 ${LTO_LINK[@]+"${LTO_LINK[@]}"} -o "$BUILD/web-render-native" "${OBJECTS[@]}" \
      "$LEANLIB/libInit.a" "$LEANLIB/libStd.a" "$LEANLIB/libleancpp.a" "$LEANRT" \
      -L"$TOOLCHAIN/lib" -luv -lc++ -Wl,-dead_strip 2>&1 | { grep -v "was built for newer .macOS. version" >&2 || true; }
    assert_no_gmp "$BUILD/web-render-native"
  else
    leanc -O3 -o "$BUILD/web-render-native" "${OBJECTS[@]}"
  fi
  echo "WEB_RENDER_NATIVE=$BUILD/web-render-native"
  # The same objects and the Wasm C shim, as a library the desktop app opens through FFI.
  # Native output is the same bytes as Wasm output (native_html_test.ts checks this).
  LIBRARY_OBJECTS=()
  for object in "${OBJECTS[@]}"; do [ "$(basename "$object")" = WebRenderCLI.o ] || LIBRARY_OBJECTS+=("$object"); done
  case "$(uname -s)" in
    Darwin)
      LIBRARY="$BUILD/engines/libweb-render.dylib"
      SHARED=(-dynamiclib -Wl,-dead_strip -lc++)
      # Exports are dead-strip roots. Keep the shim ABI and let ld discard unused engine internals.
      for symbol in "${SHIM_EXPORTS[@]}"; do SHARED+=("-Wl,-exported_symbol,$symbol"); done
      ;;
    Linux) LIBRARY="$BUILD/engines/libweb-render.so";;
    *) LIBRARY="";;
  esac
  # Linux makes the library for Textnaut and the WPT runner (tests/browser-wpt/testharness-run.ts
  # --native-engine). It is self-contained: Lean's runtime, Init, Std, libuv and libc++ are
  # linked in statically, so no Lean toolchain is needed at run time. The runtime is the
  # GMP-free one of build-leanrt-no-gmp.sh, with initial-exec thread-local storage (the
  # toolchain's libleanrt.a uses local-exec, which a shared object can not hold). leanc links
  # it, so it is linked against the toolchain's old glibc and runs on older systems too.
  # --exclude-libs keeps the archives' symbols out of the dynamic table: only the shim's
  # entry points are exported. The check below fails the build if the library would need
  # anything beyond the C library.
  if [ "$(uname -s)" = Linux ]; then
  mkdir -p "$BUILD/engines"
  LEANRT=$("$LAB/build-leanrt-no-gmp.sh" "$TOOLCHAIN" "$LAB/.build/leanrt-no-gmp" | tail -1)
  "${CC:-cc}" -O3 -DNDEBUG -fPIC -I "$TOOLCHAIN/include" -c "$LAB/web_render_shim.c" -o "$BUILD/obj-native/web_render_shim.o"
  leanc -shared -O3 -o "$LIBRARY" -Wl,--as-needed "${LIBRARY_OBJECTS[@]}" "$BUILD/obj-native/web_render_shim.o" \
    "$LEANLIB/libInit.a" "$LEANLIB/libStd.a" "$LEANLIB/libleancpp.a" "$LEANRT" \
    "$TOOLCHAIN/lib/libuv.a" "$TOOLCHAIN/lib/libc++.a" "$TOOLCHAIN/lib/libc++abi.a" "$TOOLCHAIN/lib/libunwind.a" \
    -Wl,--exclude-libs,ALL -Wl,-Bsymbolic -Wl,--gc-sections -Wl,--no-undefined -lpthread -ldl -lm
  assert_no_gmp "$LIBRARY"
  # Only C library dependencies, and no run path into a toolchain.
  NEEDED=$(readelf -dW "$LIBRARY" | sed -n 's/.*(NEEDED).*\[\(.*\)\]/\1/p' | sort | tr '\n' ' ')
  for lib in $NEEDED; do
    case "$lib" in libc.so.*|libm.so.*|libdl.so.*|libpthread.so.*|librt.so.*|ld-linux*) ;;
      *) echo "$LIBRARY needs $lib; it must need only the C library (NEEDED: $NEEDED)" >&2; exit 1;; esac
  done
  if readelf -dW "$LIBRARY" | grep -E 'R(UN)?PATH' | grep -q -v 'ORIGIN'; then
    echo "$LIBRARY has a run path outside its own directory: $(readelf -dW "$LIBRARY" | grep -E 'R(UN)?PATH')" >&2; exit 1
  fi
  echo "SELF_CONTAINED $(basename "$LIBRARY"): NEEDED $NEEDED"
  echo "WEB_RENDER_LIBRARY=$LIBRARY"
  LIBRARY=""
  fi
  # The desktop app is macOS only, so other hosts make no library.
  if [ -n "$LIBRARY" ]; then
  "${CC:-cc}" -O3 -DNDEBUG -I "$TOOLCHAIN/include" -c "$LAB/web_render_shim.c" -o "$BUILD/obj-native/web_render_shim.o"
  # Static Lean runtime from the same toolchain: the library needs no Lean at run time.
  "${CC:-cc}" -O2 ${LTO_LINK[@]+"${LTO_LINK[@]}"} -o "$LIBRARY" "${LIBRARY_OBJECTS[@]}" "$BUILD/obj-native/web_render_shim.o" \
    "$LEANLIB/libInit.a" "$LEANLIB/libStd.a" "$LEANLIB/libleancpp.a" "$LEANRT" \
    -L"$TOOLCHAIN/lib" -luv "${SHARED[@]}" 2>&1 | { grep -v "was built for newer .macOS. version" >&2 || true; }
  assert_no_gmp "$LIBRARY"
  echo "WEB_RENDER_LIBRARY=$LIBRARY"
  fi
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
  # Lean emits a Nat literal below 2^63 with no reference counting (a scalar on the 64-bit
  # machine that compiles it); on wasm32 one of 2^31 or more is a heap object that its
  # owners free twice. tools/wasm32-nat-literals.py makes each such literal persistent (record
  # 2026-11-08-lean-js-engine.md, section 17): our modules here, the toolchain's Init and Std
  # modules below.
  NAMES=()
  for source in "${SOURCES[@]}" "$LAB/web_render_shim.c"; do
    name=$(basename "$source" .c)
    case "$source" in *'/.lake/'*) name="Core_$(echo "$source" | sed 's|.*/ir/||;s|/|_|g;s|\.c$||')";; esac
    NAMES+=("$name=$source")
  done
  COMPILE=()
  while IFS= read -r file; do COMPILE+=("$file"); done < <(python3 "$ROOT/tools/wasm32-nat-literals.py" --batch "$BUILD/wasm32-src" "${NAMES[@]}")
  # The gate: no file that is compiled for wasm32 keeps such a literal.
  python3 "$ROOT/tools/wasm32-nat-literals.py" --check "${COMPILE[@]}"
  for i in "${!NAMES[@]}"; do
    name=${NAMES[$i]%%=*}
    object="$BUILD/obj-wasm/$name.o"
    printf 'WASM %s %s\n' "$name" "$(date -u)"
    compile_bg emcc "${FLAGS[@]}" -c "${COMPILE[$i]}" -o "$object"
    OBJECTS+=("$object")
  done
  # The runtime cache's Init and Std objects with such literals, compiled again from its C
  # with the flags of build-wasm.sh (step 4); CORE_OBJECTS is the cache's list with these in place.
  CORE_NAMES=()
  for source in "$RUNTIME/core-c/"*.c; do CORE_NAMES+=("$(basename "$source" .c)=$source"); done
  mkdir -p "$BUILD/obj-wasm/core"
  CORE_OBJECTS=()
  i=0
  while IFS= read -r file; do
    name=${CORE_NAMES[$i]%%=*}; i=$((i+1))
    if [ "$file" = "$RUNTIME/core-c/$name.c" ]; then CORE_OBJECTS+=("$RUNTIME/core-obj/$name.o"); continue; fi
    printf 'WASM core %s %s\n' "$name" "$(date -u)"
    emcc -O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I "$RUNTIME/wasm-include" -I "$TOOLCHAIN/include" -c "$file" -o "$BUILD/obj-wasm/core/$name.o"
    CORE_OBJECTS+=("$BUILD/obj-wasm/core/$name.o")
  done < <(python3 "$ROOT/tools/wasm32-nat-literals.py" --batch "$BUILD/wasm32-src/core" "${CORE_NAMES[@]}")
  python3 "$ROOT/tools/wasm32-nat-literals.py" --check "$BUILD/wasm32-src/core/"*.c
  [ "${#CORE_OBJECTS[@]}" = "$(ls "$RUNTIME/core-obj/"*.o | wc -l | tr -d ' ')" ] || { echo 'core objects and core C differ in the runtime cache' >&2; exit 1; }
  for source in "${HACL_SOURCES[@]}"; do
    object="$BUILD/obj-wasm/hacl_$(basename "$source" .c).o"
    printf 'WASM %s %s\n' "$(basename "$source" .c)" "$(date -u)"
    compile_bg emcc "${FLAGS[@]}" -I "$HACL/include" -c "$source" -o "$object"
    OBJECTS+=("$object")
  done
  compile_wait
  # Link at -O3 (wasm-opt -O3): 3.8 % less over gzip (6.20 -> 5.97 MB) for everyone who loads the Hub,
  # the same time to first frame and a few percent less stack per call (2026-11-09).
  em++ -O3 -DNDEBUG -fwasm-exceptions --no-entry "${OBJECTS[@]}" "${CORE_OBJECTS[@]}" "$RUNTIME/rt-obj/"*.o \
    -o "$BUILD/engines/web-render.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 \
    -sEXPORTED_FUNCTIONS="$(IFS=,; printf '%s' "${SHIM_EXPORTS[*]},_malloc,_free")" \
    -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString,HEAPU8,stackSave,stackRestore \
    -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1
  emcc "${FLAGS[@]}" -c "$LAB/render_plan_shim.c" -o "$BUILD/obj-wasm/render_plan_shim.o"
  em++ -O2 -DNDEBUG -fwasm-exceptions --no-entry "$BUILD/obj-wasm/RenderPlan.o" "$BUILD/obj-wasm/render_plan_shim.o" "${CORE_OBJECTS[@]}" "$RUNTIME/rt-obj/"*.o \
    -o "$BUILD/engines/render-plan.mjs" -sMODULARIZE=1 -sEXPORT_ES6=1 -sINVOKE_RUN=0 \
    -sEXPORTED_FUNCTIONS=_render_plan,_render_plan_free -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString \
    -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=4MB -sENVIRONMENT=node,web,worker -sASSERTIONS=1
  echo "WEB_RENDER_WASM=$BUILD/engines/web-render.mjs"
fi
[ "$MODE" = --native ] && node "$LAB/web-render/check-budget.mjs" "$BUILD/web-render-native"
# Size and link content of the engine (tools/binary-budget.py, issue 551): no Lean.Elab/Lean.Meta
# code, at most 2 % above the recorded size for this platform.
if [ "$MODE" = --native ] && [ -n "${LIBRARY:-}" ]; then
  BUDGET_NAME=$(basename "$LIBRARY")
  [ "${NATIVE_LTO:-0}" = 1 ] && BUDGET_NAME="libweb-render-lto.dylib"
  python3 "$ROOT/tools/binary-budget.py" check "$BUDGET_NAME=$LIBRARY"
elif [ "$MODE" = --wasm ]; then
  python3 "$ROOT/tools/binary-budget.py" check "web-render.wasm=$BUILD/engines/web-render.wasm"
fi
python3 "$LAB/web-render/write-witness.py"
printf 'WEB_RENDER_BUILD_RC=0 %s\n' "$(date -u)"
