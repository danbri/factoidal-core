#!/usr/bin/env bash
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
. "$LAB/toolchain-versions.env"
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
SKIP=0
BUILD_ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --skip-build) SKIP=1; shift ;;
    --runtime-cache) BUILD_ARGS+=(--runtime-cache "${2:?missing runtime cache}"); shift 2 ;;
    *) echo "usage: $0 [--skip-build] [--runtime-cache DIR]" >&2; exit 2 ;;
  esac
done
if [ "$SKIP" = 0 ]; then bash "$LAB/build-engines.sh" "${BUILD_ARGS[@]}"; fi
mkdir -p "$LAB/.build"
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror "$LAB/native_coordinates_test.c" \
  -lm -o "$LAB/.build/native-coordinates-test"
"$LAB/.build/native-coordinates-test"
# The status note is rendered by this engine; its HTML must match its Markdown.
python3 "$LAB/../../../tools/status-to-html.py" "$LAB/../../../docs/web/hub/foafnaut2525-status.md" \
  "$LAB/web-render/fixtures/status.html" --check
# The demo pages match their sources, and each one does what its manifest says.
python3 "$LAB/../../../tools/build-demo-pages.py" --check
# The verified FOAF overlap check: the bytes in the page and in FoafCheckBytes.lean are the
# assembler output of wasm/foaf-check.wat (docs/designissues/2026-11-09-verified-foaf-layout.md).
rc=0; bash "$LAB/wasm/build.sh" --check || rc=$?
if [ "$rc" = 2 ]; then echo 'NOT RUN: wasm/build.sh --check needs the pinned wabt wat2wasm'; elif [ "$rc" != 0 ]; then exit "$rc"; fi
# The Spinal Tap page's queries and inlined results match its Wikidata snapshot (no network).
python3 "$LAB/tools/spinal-tap-snapshot.py" --check
if [ -x "$LAB/.build/web-render/web-render-native" ]; then
  python3 "$LAB/../../../tools/check-demo-pages.py" "$LAB/.build/web-render/web-render-native"
else
  echo 'NOT RUN: check-demo-pages.py needs web-render-native, which this build does not have yet'
fi
# The native HTML tests need the web-render engine, which Builds makes after this
# step in its engines job and before it in its macOS job, and more permissions.
TESTS=()
for test in "$LAB/"*_test.ts; do case "$test" in "$LAB/native_html_test.ts"|"$LAB/native_html_bytes_test.ts"|"$LAB/native_html_fonts_test.ts"|"$LAB/native_html_wasm_test.ts"|"$LAB/native_html_sparql_test.ts"|"$LAB/native_window_queue_test.ts"|"$LAB/showcase_gaps_test.ts"|"$LAB/print_gaps_test.ts"|"$LAB/svg_text_test.ts"|"$LAB/browser_state_test.ts"|"$LAB/html_images_test.ts"|"$LAB/frame_work_test.ts"|"$LAB/link_route_test.ts"|"$LAB/native_html_scripts_test.ts"|"$LAB/gesture_test.ts"|"$LAB/frame_cost_test.ts"|"$LAB/scroll_prefetch_test.ts"|"$LAB/native_html_pointer_test.ts"|"$LAB/page_gpu_test.ts"|"$LAB/bubblepop_pages_test.ts"|"$LAB/dom_breadth_test.ts"|"$LAB/canvas2d_test.ts"|"$LAB/long_words_test.ts"|"$LAB/native_liberal_test.ts"|"$LAB/device_pixels_test.ts"|"$LAB/showoff_test.ts") ;; *) TESTS+=("$test");; esac; done
deno check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  "$LAB/run_ui.ts" "$LAB/run_lean.ts" "$LAB/run_svg.ts" "$LAB/run_foaf_svg.ts" "${TESTS[@]}"
deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --allow-read "${TESTS[@]}"
# Frame cost ratchet: frame_cost_test.ts (above) replays the cases of the Lean model
# (L4Factoidal/FrameCost); the fixture must be the model's output.
FRAME_COST_CASES="$LAB/../../../formal/lean4/.lake/build/bin/frame-cost-cases"
if [ -x "$FRAME_COST_CASES" ]; then
  "$FRAME_COST_CASES" --check "$LAB/fixtures/frame_cost_cases.json"
else
  echo 'NOT RUN: frame-cost-cases --check needs `lake build frame-cost-cases` in formal/lean4'
fi
# Browser state (WebState.lean): local LWS servers in temporary folders, through the
# `factoidal` command, and Lean through web-state (build-web-state.sh).
if [ -x "$LAB/.build/web-state/web-state" ] && command -v factoidal >/dev/null; then
  deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-write --allow-run --allow-net --allow-env "$LAB/browser_state_test.ts"
else
  echo 'NOT RUN: browser_state_test.ts needs web-state (build-web-state.sh) and the factoidal command'
fi
# The input queue test needs the macOS window library from build-executables.sh.
if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
    --allow-read --allow-ffi --allow-run "$LAB/native_window_queue_test.ts"
  # Print with no panel to a PDF: three pages of the paper size (issue 1268).
  PRINT_PDF=$(mktemp -t foafnaut-print).pdf
  deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-ffi --allow-read --allow-write \
    "$LAB/native_print_check.ts" "$LAB/.build/native/libnative-window.dylib" "$PRINT_PDF"
  rm -f "$PRINT_PDF"
else
  echo 'NOT RUN: native_window_queue_test.ts needs the macOS window library'
fi
if [ -f "$LAB/.build/web-render/engines/web-render.wasm" ]; then
  mkdir -p "$LAB/.build/native-html/runtime"
  cp "$LAB/.build/web-render/engines/web-render."{mjs,wasm} "$LAB/.build/native-html/runtime/"
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-write --allow-net "$LAB/native_html_test.ts"
  # Bytes answers against the Base64 reference on every demo page (issue 1268), Wasm and
  # the native library when it is built.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_bytes_test.ts"
  # Device pixels (dprfix): a 2x and a 3x frame are the 1x layout scaled, Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/device_pixels_test.ts"
  # Fallback fonts: Armenian through Noto Sans Armenian after Noto Sans, Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_fonts_test.ts"
  # WebAssembly run by WasmVM, Lean's engine, in this engine (issue 1244), Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_wasm_test.ts"
  # HTML img drawn by Lean: sizes, alt text, same-origin fetch; Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/html_images_test.ts"
  # Frame cost ratchet, counted by the hosts: a colour-only hover lays out 0 times and a
  # geometry hover once; render request bytes do not grow with image size. Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/frame_work_test.ts"
  # Long words (issue 1268): script and style text is not shaped; a 10,000-character word
  # shapes in linear time. Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/long_words_test.ts"
  # Web fonts (@font-face), marks across fonts, paint-only SVG transforms and animation
  # (FrameCost.paint_never_layouts, counted by the engine), hostile text. Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-run=hb-shape "$LAB/showoff_test.ts"
  # The Hub's fallback fonts: files, sizes, SHA-256, and which fonts each demo page fetches.
  deno test --no-check --no-config --allow-read "$LAB/fallback_fonts_test.ts"
  # SVG text, tspan and textPath drawn with the held font (issue 1270), Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/svg_text_test.ts"
  # The link rules (WebRoute.lean): a few thousand links through Lean's op shellRoute and through
  # link-route.mjs, the routing of the Hub worker and run_html.ts for an older engine; every
  # link must get the same route. Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/link_route_test.ts"
  # Back and forward swipes (WebGesture.lean): Lean's op gesture on generated touches and
  # trackpad swipes, against the conventions and the theorems. Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/gesture_test.ts"
  # These import the engine module too, so they run here, once it is built: the frame cost
  # cases and scroll prefetch (Wasm and native).
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/frame_cost_test.ts" "$LAB/scroll_prefetch_test.ts"
  # Liberal mode and the console (WebAccept.lean, WebConsole.lean): each skip on the original
  # fixtures (fixtures/liberal), strict refusals, the note, the console page, media queries
  # against the viewport, and the same frame with no entries on pages strict accepts. Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-env "$LAB/native_liberal_test.ts"
  # The SPARQL planner page (WebSparql.lean): plans, rows and the drawn page, Wasm and native.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_sparql_test.ts"
  # Page scripts on BubblePopJS (the JavaScript engine written in Lean) (WasmVM/Hosts/LeanJS.lean): the same turns as on
  # QuickJS-NG, with no guest module; the demo pages, compared with QuickJS-NG when the guest exists.
  SCRIPT_ENGINE=bubblepop deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-env "$LAB/native_html_scripts_test.ts" "$LAB/native_html_pointer_test.ts"
  if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then
    SCRIPT_ENGINE=bubblepop deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/page_gpu_test.ts"
    deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/bubblepop_pages_test.ts"
    # DOM breadth (Range, Selection, traversal, markup, reflection, computed style) on both engines.
    deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/dom_breadth_test.ts"
  fi
  # Page scripts run by Lean (WebScripts.lean): QuickJS-NG in WasmVM on the Lean DOM, clicks and
  # timers through the Lean event loop, Wasm and native. Only when the guest module exists
  # (tools/wasmvm/build-quickjs.sh, or fetch-builds --set foafnaut-web): it is not committed.
  QJS_GUEST=${QUICKJS_WASM:-$HOME/working/qjs-wasm/qjs-wasmvm.wasm}
  [ -f "$QJS_GUEST" ] || QJS_GUEST="$LAB/../../../docs/web/hub/wasm-guests/qjs-wasmvm.wasm"
  if [ -f "$QJS_GUEST" ]; then
    QUICKJS_WASM="$QJS_GUEST" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/native_html_scripts_test.ts"
    # Pointer events, layout reads and the page GPU subset run in page scripts too.
    QUICKJS_WASM="$QJS_GUEST" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/native_html_pointer_test.ts" "$LAB/page_gpu_test.ts"
    # Canvas 2D drawn by Lean: Chrome's pixels for small scenes, host commands, answers, frame cost (both engines).
    QUICKJS_WASM="$QJS_GUEST" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/canvas2d_test.ts"
    # The window replays the page GPU commands (2026-11-08: the start turn's commands, which make
    # the canvas and buffers, were dropped, so every later turn failed and the canvas stayed
    # blank). Each triangle page runs off screen for 8 s (25 s on Wasm); any page GPU or page error fails.
    if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
      GPU_ENGINE=() GPU_SECONDS=25
      if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then GPU_ENGINE=(--native-engine "$LAB/.build/web-render/engines/libweb-render.dylib"); GPU_SECONDS=8; fi
      for gpu_page in webgpu-triangle webgl-triangle canvas-chart shader-gallery; do
        GPU_LOG=$(mktemp -t foafnaut-page-gpu)
        GPU_RC=0
        QUICKJS_WASM="$QJS_GUEST" perl -e 'alarm shift; exec @ARGV' "$GPU_SECONDS" deno run --no-check --no-config --no-npm --node-modules-dir=none \
          --unstable-webgpu --unstable-ffi -A "$LAB/run_html.ts" --offscreen --no-state --strict --html "$LAB/pages/$gpu_page.html" ${GPU_ENGINE[@]+"${GPU_ENGINE[@]}"} >"$GPU_LOG" 2>&1 || GPU_RC=$?
        # 142: the alarm ended the run, as planned. Any other non-zero code is a failure.
        if { [ "$GPU_RC" != 0 ] && [ "$GPU_RC" != 142 ]; } || grep -qE 'page GPU|page error' "$GPU_LOG" || ! grep -q '"native-html-presented"' "$GPU_LOG"; then
          echo "page GPU in the window: $gpu_page failed:" >&2; grep -m5 -E 'page GPU|page error|rror' "$GPU_LOG" >&2; rm -f "$GPU_LOG"; exit 1
        fi
        echo "page GPU in the window: $gpu_page replayed with no error"; rm -f "$GPU_LOG"
      done
    fi
  else
    echo 'NOT RUN: native_html_scripts_test.ts needs the QuickJS guest module (tools/wasmvm/build-quickjs.sh)'
  fi
  # The showcase gaps (issue 1268): each test passes while its gap is open, and fails when
  # an engine change closes it, so the test and its issue change together.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read "$LAB/showcase_gaps_test.ts"
  # The print gaps of issue 1279, in the same way.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --allow-read "$LAB/print_gaps_test.ts"
  # Print page breaks of the print showcase (issue 1268): chapters start pages, print rules apply.
  deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-ffi --allow-env "$LAB/print_layout_check.ts"
  # The whole print path to a PDF with no window or panel: Lean pages, GPU images, NSPrintOperation.
  if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
    PRINT_PDF=$(mktemp -t foafnaut-showcase).pdf
    deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/print_document_check.ts" print-showcase.html "$PRINT_PDF"
    rm -f "$PRINT_PDF"
  else
    echo 'NOT RUN: print_document_check.ts needs the macOS window library'
  fi
  # Two-layer scroll (issue 1268): the composite of the layers has the bytes of one Lean
  # frame at each scroll tried, on this machine's GPU. With no GPU adapter it says NOT RUN.
  deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/scroll_layers_check.ts"
  # Chrome pixels (issue 1268): a selected address changes only the address box, in the selection colour.
  deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/chrome_pixels_check.ts"
  # Every run_html.ts sweep with --offscreen, native and Wasm engines (issue 1268): no window is
  # shown, so it runs with the screen locked and on CI. About 65 s on an M1.
  if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
    bash "$LAB/sweeps.sh"
  else
    echo 'NOT RUN: sweeps.sh needs macOS and the window library'
  fi
  # The CPU backend (SVGRaster.lean) against WebGPU: each demo page and each SVG shapes test,
  # per pixel, within the tolerance of docs/designissues/2026-11-08-cpu-render-backend.md.
  # NOT RUN with no Chrome.
  node "$LAB/cpu_render_diff_check.mjs"
else
  echo 'NOT RUN: native_html_test.ts needs the web-render engine, which this build does not have yet'
fi
