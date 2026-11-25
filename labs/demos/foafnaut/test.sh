#!/usr/bin/env bash
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
. "$LAB/toolchain-versions.env"
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
SKIP=0
BUILD_ARGS=()
# Every check runs and the failures are listed together at the end (exit 1 if any failed),
# so one CI run shows every broken test, not only the first. --fail-fast (or
# FOAFNAUT_FAIL_FAST=1) stops at the first failing check instead, for local use.
FAIL_FAST=${FOAFNAUT_FAIL_FAST:-0}
while [ $# -gt 0 ]; do
  case "$1" in
    --skip-build) SKIP=1; shift ;;
    --runtime-cache) BUILD_ARGS+=(--runtime-cache "${2:?missing runtime cache}"); shift 2 ;;
    --fail-fast) FAIL_FAST=1; shift ;;
    *) echo "usage: $0 [--skip-build] [--runtime-cache DIR] [--fail-fast]" >&2; exit 2 ;;
  esac
done
FAILED=() RESULTS=()
# check LABEL COMMAND...: run one check, record its result and time, go on unless --fail-fast.
check() {
  local label=$1 start=$SECONDS rc=0; shift
  "$@" || rc=$?
  RESULTS+=("$([ "$rc" = 0 ] && echo ok || echo "FAILED (exit $rc)") $((SECONDS - start)) s  $label")
  if [ "$rc" != 0 ]; then
    FAILED+=("$label (exit $rc)")
    echo "test.sh: FAILED $label (exit $rc)" >&2
    if [ "$FAIL_FAST" = 1 ]; then exit "$rc"; fi
  fi
}
summary() {
  local rc=$?
  [ ${#RESULTS[@]} -gt 0 ] || return 0
  echo
  echo "test.sh summary: ${#RESULTS[@]} checks, ${#FAILED[@]} failed, ${SECONDS} s"
  printf '  %s\n' "${RESULTS[@]}"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    { echo "### Foafnaut test.sh: ${#RESULTS[@]} checks, ${#FAILED[@]} failed, ${SECONDS} s"
      [ ${#FAILED[@]} = 0 ] || printf -- '- FAILED %s\n' "${FAILED[@]}"
      [ "$rc" = 0 ] || [ ${#FAILED[@]} != 0 ] || echo "- stopped by an error outside the checks (exit $rc)"
    } >> "$GITHUB_STEP_SUMMARY"
  fi
  if [ ${#FAILED[@]} != 0 ]; then
    echo "test.sh: ${#FAILED[@]} failed:"; printf '  %s\n' "${FAILED[@]}"
  fi
}
trap summary EXIT
if [ "$SKIP" = 0 ]; then bash "$LAB/build-engines.sh" "${BUILD_ARGS[@]}"; fi
mkdir -p "$LAB/.build"
native_coordinates() {
  "${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror "$LAB/native_coordinates_test.c" \
    -lm -o "$LAB/.build/native-coordinates-test" && "$LAB/.build/native-coordinates-test"
}
check native_coordinates_test.c native_coordinates
# The status note is rendered by this engine; its HTML must match its Markdown.
check "status-to-html.py" python3 "$LAB/../../../tools/status-to-html.py" "$LAB/../../../docs/web/hub/foafnaut2525-status.md" \
  "$LAB/web-render/fixtures/status.html" --check
# The demo pages match their sources, and each one does what its manifest says.
check "build-demo-pages.py" python3 "$LAB/../../../tools/build-demo-pages.py" --check
# The verified FOAF overlap check: the bytes in the page and in FoafCheckBytes.lean are the
# assembler output of wasm/foaf-check.wat (docs/designissues/2026-11-09-verified-foaf-layout.md).
foaf_wasm_check() {
  local rc=0; bash "$LAB/wasm/build.sh" --check || rc=$?
  if [ "$rc" = 2 ]; then echo 'NOT RUN: wasm/build.sh --check needs the pinned wabt wat2wasm'; return 0; fi
  return "$rc"
}
check "wasm/build.sh --check" foaf_wasm_check
# The Spinal Tap page's queries and inlined results match its Wikidata snapshot (no network).
check "spinal-tap-snapshot.py" python3 "$LAB/tools/spinal-tap-snapshot.py" --check
if [ -x "$LAB/.build/web-render/web-render-native" ]; then
  check "check-demo-pages.py" python3 "$LAB/../../../tools/check-demo-pages.py" "$LAB/.build/web-render/web-render-native"
else
  echo 'NOT RUN: check-demo-pages.py needs web-render-native, which this build does not have yet'
fi
# Colour emoji drawn by Lean (ColrRaster) against an independent COLR renderer's pixels
# (fixtures/emoji-reference, emoji_reference.py), through web-render-native --colour-glyph.
if [ -x "$LAB/.build/web-render/web-render-native" ]; then
  check "emoji_pixels_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-run --allow-write "$LAB/emoji_pixels_test.ts"
else
  echo 'NOT RUN: emoji_pixels_test.ts needs web-render-native'
fi
# The native HTML tests need the web-render engine, which Builds makes after this
# step in its engines job and before it in its macOS job, and more permissions.
TESTS=()
for test in "$LAB/"*_test.ts; do case "$test" in "$LAB/native_html_test.ts"|"$LAB/about_page_test.ts"|"$LAB/native_html_bytes_test.ts"|"$LAB/native_html_fonts_test.ts"|"$LAB/serif_face_test.ts"|"$LAB/mono_face_test.ts"|"$LAB/background_image_test.ts"|"$LAB/native_html_wasm_test.ts"|"$LAB/native_html_sparql_test.ts"|"$LAB/native_window_queue_test.ts"|"$LAB/showcase_gaps_test.ts"|"$LAB/print_gaps_test.ts"|"$LAB/svg_text_test.ts"|"$LAB/browser_state_test.ts"|"$LAB/html_images_test.ts"|"$LAB/frame_work_test.ts"|"$LAB/link_route_test.ts"|"$LAB/native_html_scripts_test.ts"|"$LAB/gesture_test.ts"|"$LAB/frame_cost_test.ts"|"$LAB/scroll_prefetch_test.ts"|"$LAB/native_html_pointer_test.ts"|"$LAB/native_html_key_test.ts"|"$LAB/network_gaps_test.ts"|"$LAB/page_gpu_test.ts"|"$LAB/bubblepop_pages_test.ts"|"$LAB/dom_breadth_test.ts"|"$LAB/canvas2d_test.ts"|"$LAB/long_words_test.ts"|"$LAB/native_liberal_test.ts"|"$LAB/device_pixels_test.ts"|"$LAB/showoff_test.ts"|"$LAB/emoji_pixels_test.ts"|"$LAB/bubblepop_cost_test.ts"|"$LAB/shader_gallery_test.ts"|"$LAB/partial_frame_test.ts"|"$LAB/workers_test.ts"|"$LAB/many_images_test.ts"|"$LAB/script_reads_holds_test.ts"|"$LAB/script_turn_cost_test.ts"|"$LAB/cssom_insert_cost_test.ts"|"$LAB/live_list_cost_test.ts"|"$LAB/turn_slice_test.ts"|"$LAB/start_slice_test.ts"|"$LAB/start_resume_test.ts"|"$LAB/undo_snapshot_test.ts"|"$LAB/svg_depth_test.ts"|"$LAB/host_parity_test.ts"|"$LAB/native_net_test.ts"|"$LAB/native_net_pool_test.ts"|"$LAB/native_net_dns_test.ts"|"$LAB/origin_isolation_test.ts"|"$LAB/native_window_ax_test.ts"|"$LAB/accessibility_tree_test.ts") ;; *) TESTS+=("$test");; esac; done
check "deno check (hosts and pure tests)" deno check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  "$LAB/run_ui.ts" "$LAB/run_lean.ts" "$LAB/run_svg.ts" "$LAB/run_foaf_svg.ts" "${TESTS[@]}"
check "deno test (pure tests)" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --allow-read "${TESTS[@]}"
# Page requests of the desktop host (native_net.ts): local servers on the loopback interface (the
# net permission is for the test names, which never resolve); a pinned request goes to its address
# and to no other; https makes a throwaway
# certificate with openssl.
check "native_net tests (pool, DNS cache)" deno test --no-config --no-npm --node-modules-dir=none --allow-net --allow-run=openssl --allow-read --allow-write "$LAB/native_net_test.ts" "$LAB/native_net_pool_test.ts" "$LAB/native_net_dns_test.ts"
# Frame cost ratchet: frame_cost_test.ts (above) replays the cases of the Lean model
# (L4Factoidal/FrameCost); the fixture must be the model's output.
FRAME_COST_CASES="$LAB/../../../formal/lean4/.lake/build/bin/frame-cost-cases"
if [ -x "$FRAME_COST_CASES" ]; then
  check "frame-cost-cases --check" "$FRAME_COST_CASES" --check "$LAB/fixtures/frame_cost_cases.json"
else
  echo 'NOT RUN: frame-cost-cases --check needs `lake build frame-cost-cases` in formal/lean4'
fi
# Compute kernels generated by Lean (L4Factoidal/GpuKernel, issue 398): the GPU's output words
# against the Lean reference, synthetic boxes and, with the native engine, boxes of real scenes.
# Prints NOT RUN itself with no lean/leanc or no WebGPU adapter. About 15 s.
# Its real scenes load the engine through native_html_engine.ts, which needs the runtime copy.
if [ -f "$LAB/.build/web-render/engines/web-render.wasm" ]; then
  mkdir -p "$LAB/.build/native-html/runtime"
  cp "$LAB/.build/web-render/engines/web-render."{mjs,wasm} "$LAB/.build/native-html/runtime/"
fi
GPU_KERNEL_ENGINE=()
if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then GPU_KERNEL_ENGINE=(--engine "$LAB/.build/web-render/engines/libweb-render.dylib"); fi
check "gpu_kernel_diff.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  --allow-read --allow-write --allow-run --allow-env --allow-ffi "$LAB/gpu_kernel_diff.ts" ${GPU_KERNEL_ENGINE[@]+"${GPU_KERNEL_ENGINE[@]}"}
# The host's frame pipeline against its Lean model (L4Factoidal/HostPipeline/Model.lean,
# issue 398): traces of two pages off screen, replayed by the Lean checker, plus two controls.
# Prints NOT RUN itself with no lean, window library or WebGPU adapter. About 40 s.
PIPE_ENGINE=()
if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then PIPE_ENGINE=(--native-engine "$LAB/.build/web-render/engines/libweb-render.dylib"); fi
check "pipeline_trace_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  -A "$LAB/pipeline_trace_check.ts" ${PIPE_ENGINE[@]+"${PIPE_ENGINE[@]}"}
# Browser state (WebState.lean): local LWS servers in temporary folders, through the
# `factoidal` command, and Lean through web-state (build-web-state.sh).
if [ -x "$LAB/.build/web-state/web-state" ] && command -v factoidal >/dev/null; then
  check "browser_state_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-write --allow-run --allow-net --allow-env "$LAB/browser_state_test.ts"
else
  echo 'NOT RUN: browser_state_test.ts needs web-state (build-web-state.sh) and the factoidal command'
fi
# The input queue test needs the macOS window library from build-executables.sh.
if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
  check "native_window_queue_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
    --allow-read --allow-ffi --allow-run "$LAB/native_window_queue_test.ts"
  # The accessibility elements of the window library, from a tree in the engine's format.
  check "native_window_ax_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
    --allow-read --allow-ffi --allow-run "$LAB/native_window_ax_test.ts"
  # Print with no panel to a PDF: three pages of the paper size (issue 1268).
  PRINT_PDF=$(mktemp -t foafnaut-print).pdf
  check "native_print_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-ffi --allow-read --allow-write \
    "$LAB/native_print_check.ts" "$LAB/.build/native/libnative-window.dylib" "$PRINT_PDF"
  rm -f "$PRINT_PDF"
else
  echo 'NOT RUN: native_window_queue_test.ts needs the macOS window library'
fi
if [ -f "$LAB/.build/web-render/engines/web-render.wasm" ]; then
  mkdir -p "$LAB/.build/native-html/runtime"
  cp "$LAB/.build/web-render/engines/web-render."{mjs,wasm} "$LAB/.build/native-html/runtime/"
  check "native_html_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-write --allow-net "$LAB/native_html_test.ts"
  # about:foafnaut and --version as the engine writes them (WebAbout.lean).
  check "about_page_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --allow-read "$LAB/about_page_test.ts"
  # Bytes answers against the Base64 reference on every demo page (issue 1268), Wasm and
  # the native library when it is built.
  check "native_html_bytes_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_bytes_test.ts"
  # Device pixels (dprfix): a 2x and a 3x frame are the 1x layout scaled, Wasm and native.
  check "device_pixels_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/device_pixels_test.ts"
  # Fallback fonts: Armenian through Noto Sans Armenian after Noto Sans, Wasm and native.
  check "native_html_fonts_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_fonts_test.ts"
  # The serif face given before the first page: one layout for serif pages, the same frames
  # for pages with no serif text, Wasm and native.
  check "serif_face_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/serif_face_test.ts"
  # The monospace face: pre and code in Liberation Mono, the same frames for pages with no
  # monospace text, one layout once the face is held, 0.6 em advances; Wasm and native.
  check "mono_face_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/mono_face_test.ts"
  # Background images: url() tiled from the padding box, clipped to the border box (native).
  check "background_image_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/background_image_test.ts"
  # WebAssembly run by WasmVM, Lean's engine, in this engine (issue 1244), Wasm and native.
  check "native_html_wasm_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_wasm_test.ts"
  # HTML img drawn by Lean: sizes, alt text, same-origin fetch; Wasm and native.
  check "html_images_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/html_images_test.ts"
  # Many images, call after call on one engine: no image of an earlier call, none missing,
  # a key's new bytes drawn; native and Wasm boxes the same (issue 390). And a script
  # session's layout reads see the images held at the read, not at start.
  check "many_images_test.ts script_reads_holds_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env --allow-write "$LAB/many_images_test.ts" "$LAB/script_reads_holds_test.ts"
  # A script turn that writes and reads styles costs in proportion to the page (no n² read of
  # the element keys, WebDocument.RuleMatcher).
  check "script_turn_cost_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/script_turn_cost_test.ts"
  # Rules inserted into a style sheet one at a time: Lean reads the new rule, not the sheet
  # again (CssSheet.insertAt, insertRule_eq_insertAt), and the result is as before.
  check "cssom_insert_cost_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/cssom_insert_cost_test.ts"
  # A loop over a live collection costs in proportion to its nodes, and the collection follows
  # the tree (the prelude keeps a list's nodes while Dom.stamp stays; addCommand_changes).
  check "live_list_cost_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/live_list_cost_test.ts"
  # Sliced timer turns give the result of one turn (EventLoop.Driver.advanceGoStop_resume), and
  # the script clock runs at BubblePopJS's own rate (LeanJS.stepsPerMs).
  check "turn_slice_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/turn_slice_test.ts"
  # A start in slices gives the logs and the DOM of a whole start (LeanJS.startSome_resume,
  # startFinish_eq_startSome), and an action without a budget finishes it.
  check "start_slice_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/start_slice_test.ts"
  # A start that waits for sync answers goes on from the script that waited (LeanJS.start_eq_from).
  check "start_resume_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/start_resume_test.ts"
  # the undo of a sync request costs what the action writes, not the heap (WebScripts.undoShell, JS.UndoLog):
  # a timer turn of a large page costs what it does, and its sync request is answered
  check "undo_snapshot_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env "$LAB/undo_snapshot_test.ts"
  # Inline SVG deep in the HTML is drawn or dropped, never a refusal of the page
  # (SVGReferences.maxIndexDepth, WebDocument.liberalSvg).
  check "svg_depth_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
    --allow-read --allow-ffi --allow-env --allow-write "$LAB/svg_depth_test.ts"
  # Frame cost ratchet, counted by the hosts: a colour-only hover lays out 0 times and a
  # geometry hover once; render request bytes do not grow with image size. Wasm and native.
  check "frame_work_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/frame_work_test.ts"
  # The accessibility tree through the engine's op: what the styles hide is not in it, boxes
  # from the layout, `unchanged` for the same layout, the hosts' forms, the chrome's controls,
  # and its cost grows with the page, not its square. Wasm and native.
  check "accessibility_tree_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/accessibility_tree_test.ts"
  # Long words (issue 1268): script and style text is not shaped; a 10,000-character word
  # shapes in linear time. Wasm and native.
  check "long_words_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/long_words_test.ts"
  # Web fonts (@font-face), marks across fonts, paint-only SVG transforms and animation
  # (FrameCost.paint_never_layouts, counted by the engine), hostile text. Wasm and native.
  check "showoff_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-run=hb-shape "$LAB/showoff_test.ts"
  # Partial compile (NativeSVG.compileRetained): one moved shape recompiles one primitive,
  # no change compiles nothing, and the bytes equal the plain compile. Native engine.
  check "partial_frame_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-env "$LAB/partial_frame_test.ts"
  # The Hub's fallback fonts: files, sizes, SHA-256, and which fonts each demo page fetches.
  check "fallback_fonts_test.ts" deno test --no-check --no-config --allow-read "$LAB/fallback_fonts_test.ts"
  # SVG text, tspan and textPath drawn with the held font (issue 1270), Wasm and native.
  check "svg_text_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/svg_text_test.ts"
  # The link rules (WebRoute.lean): a few thousand links through Lean's op shellRoute and through
  # link-route.mjs, the routing of the Hub worker and run_html.ts for an older engine; every
  # link must get the same route. Wasm and native.
  check "link_route_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/link_route_test.ts"
  # Back and forward swipes (WebGesture.lean): Lean's op gesture on generated touches and
  # trackpad swipes, against the conventions and the theorems. Wasm and native.
  check "gesture_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/gesture_test.ts"
  # These import the engine module too, so they run here, once it is built: the frame cost
  # cases and scroll prefetch (Wasm and native).
  check "frame_cost_test.ts scroll_prefetch_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/frame_cost_test.ts" "$LAB/scroll_prefetch_test.ts"
  # Liberal mode and the console (WebAccept.lean, WebConsole.lean): each skip on the original
  # fixtures (fixtures/liberal), strict refusals, the note, the console page, media queries
  # against the viewport, and the same frame with no entries on pages strict accepts. Wasm and native.
  check "native_liberal_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-env "$LAB/native_liberal_test.ts"
  # The SPARQL planner page (WebSparql.lean): plans, rows and the drawn page, Wasm and native.
  check "native_html_sparql_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/native_html_sparql_test.ts"
  # Page scripts on BubblePopJS (the JavaScript engine written in Lean) (WasmVM/Hosts/LeanJS.lean): the same turns as on
  # QuickJS-NG, with no guest module; the demo pages, compared with QuickJS-NG when the guest exists.
  check "native_html_scripts_test.ts native_html_pointer_test.ts native_html_key_test.ts network_gaps_test.ts (bubblepop)" env SCRIPT_ENGINE=bubblepop deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-env "$LAB/native_html_scripts_test.ts" "$LAB/native_html_pointer_test.ts" \
    "$LAB/native_html_key_test.ts" "$LAB/network_gaps_test.ts"
  # The cost ratchet: element-by-element work (push, a[i] = v, charCodeAt) is linear.
  check "bubblepop_cost_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
    --allow-read --allow-ffi --allow-env "$LAB/bubblepop_cost_test.ts"
  # The Spinal Tap page as a budgeted run (issue 450): load, layouts and 600 animation ticks on
  # the native engine against fixtures/spinal-perf/budgets.json (known failures printed). About 15 s.
  check "spinal_perf_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi --allow-read --allow-ffi --allow-env \
    --allow-net=127.0.0.1 --allow-write="$LAB/.build" --allow-run=git "$LAB/spinal_perf_check.ts"
  # Which features of the Spinal Tap page cost what (issue 450): variants made from the page at
  # test time (DOM with no scripts, no SVG, text only, plain text, empty), each on the native
  # engine in a process of its own, against fixtures/spinal-bisect/budgets.json. About 20 s.
  # The full mode, with the desktop browser, is spinal_bisect_full.sh (not here).
  check "spinal_bisect_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi --allow-read --allow-ffi --allow-env \
    --allow-net=127.0.0.1 --allow-write="$LAB/.build,/tmp/foafnaut-timing.lock" --allow-run "$LAB/spinal_bisect_check.ts"
  # The idle loop (issue 450): an idle off-screen window waits for events, not an 8 ms poll;
  # wakeups per second against the window section of the same budgets. About 10 s.
  check "idle_loop_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-run --allow-env \
    --allow-write "$LAB/idle_loop_check.ts"
  # The real-page survey's host options (--shot-at-end, --liberal-report json) on a local fixture,
  # and survey.ts on one lab page (no network, no Chrome). About 15 s.
  check "realpages_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-run --allow-env \
    --allow-write "$LAB/realpages_check.ts"
  if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then
    check "page_gpu_test.ts (bubblepop)" env SCRIPT_ENGINE=bubblepop deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/page_gpu_test.ts"
    check "bubblepop_pages_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/bubblepop_pages_test.ts"
    # DOM breadth (Range, Selection, traversal, markup, reflection, computed style) on both engines.
    check "dom_breadth_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/dom_breadth_test.ts"
    # Dedicated workers on BubblePopJS: messages, clone, importScripts, scope, timers, errors,
    # each worker's own Math.random seed, and start and round-trip times.
    check "workers_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/workers_test.ts"
    # Origin isolation checks C1 to C5 (issue 518): each fails when its leak exists; known open
    # ones are listed in the test and fail once they pass.
    check "origin_isolation_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/origin_isolation_test.ts"
    # Host parity (docs/designissues/2026-11-14-engine-integration.md): the fixtures of
    # tests/browser-integration through the WPT runner's page path, the window's and Textnaut's
    # page loading, the window itself (with what it drew, when the window library and a GPU are
    # there) and Textnaut must give the results of tests/browser-integration/expected.json, the
    # render must show the tree and the boxes the page's scripts see, and the hosts must take
    # their page steps from page-load.mjs.
    check "host_parity_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none \
      --allow-read --allow-write --allow-net --allow-run --allow-env --allow-ffi "$LAB/host_parity_test.ts"
  fi
  # Host contract (formal/lean4/L4Factoidal/HostContract): Textnaut on the native library and on the
  # Wasm build, and the Hub's Textnaut host in Node, record their boundary traces; the engine's op
  # hostContract checks each against its target and the traces against each other. NOT RUN with no
  # Wasm runtime or with an engine older than the op.
  check "host_contract_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none -A --unstable-ffi \
    "$LAB/host_contract_check.ts"
  # Page scripts run by Lean (WebScripts.lean): QuickJS-NG in WasmVM on the Lean DOM, clicks and
  # timers through the Lean event loop, Wasm and native. Only when the guest module exists
  # (tools/wasmvm/build-quickjs.sh, or fetch-builds --set foafnaut-web): it is not committed.
  QJS_GUEST=${QUICKJS_WASM:-$HOME/working/qjs-wasm/qjs-wasmvm.wasm}
  [ -f "$QJS_GUEST" ] || QJS_GUEST="$LAB/../../../docs/web/hub/wasm-guests/qjs-wasmvm.wasm"
  if [ -f "$QJS_GUEST" ]; then
    check "native_html_scripts_test.ts (quickjs)" env QUICKJS_WASM="$QJS_GUEST" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/native_html_scripts_test.ts"
    # Pointer events, layout reads and the page GPU subset run in page scripts too.
    check "native_html_pointer_test.ts page_gpu_test.ts (quickjs)" env QUICKJS_WASM="$QJS_GUEST" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/native_html_pointer_test.ts" "$LAB/page_gpu_test.ts"
    # Canvas 2D drawn by Lean: Chrome's pixels for small scenes, host commands, answers, frame cost (both engines).
    check "canvas2d_test.ts (quickjs)" env QUICKJS_WASM="$QJS_GUEST" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/canvas2d_test.ts"
    # The shader gallery on both script engines: every shader draws each frame with no layout,
    # Lean's reasons reach the page, and the QuickJS-NG instructions of a frame stay under the ratchet.
    for engine in quickjs bubblepop; do
      check "shader_gallery_test.ts ($engine)" env QUICKJS_WASM="$QJS_GUEST" SCRIPT_ENGINE=$engine deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi \
        --allow-read --allow-ffi --allow-env "$LAB/shader_gallery_test.ts"
    done
    # The window replays the page GPU commands (2026-11-08: the start turn's commands, which make
    # the canvas and buffers, were dropped, so every later turn failed and the canvas stayed
    # blank). Each triangle page runs off screen for 8 s (25 s on Wasm); any page GPU or page error fails.
    if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
      GPU_ENGINE=() GPU_SECONDS=25
      if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then GPU_ENGINE=(--native-engine "$LAB/.build/web-render/engines/libweb-render.dylib"); GPU_SECONDS=8; fi
      page_gpu_window() {
        local gpu_page=$1 GPU_LOG GPU_RC=0
        GPU_LOG=$(mktemp -t foafnaut-page-gpu)
        QUICKJS_WASM="$QJS_GUEST" perl -e 'alarm shift; exec @ARGV' "$GPU_SECONDS" deno run --no-check --no-config --no-npm --node-modules-dir=none \
          --unstable-webgpu --unstable-ffi -A "$LAB/run_html.ts" --offscreen --no-state --strict --html "$LAB/pages/$gpu_page.html" ${GPU_ENGINE[@]+"${GPU_ENGINE[@]}"} >"$GPU_LOG" 2>&1 || GPU_RC=$?
        # 142: the alarm ended the run, as planned. Any other non-zero code is a failure.
        if { [ "$GPU_RC" != 0 ] && [ "$GPU_RC" != 142 ]; } || grep -qE 'page GPU|page error|"native-html-log-flood"' "$GPU_LOG" || ! grep -q '"native-html-presented"' "$GPU_LOG"; then
          echo "page GPU in the window: $gpu_page failed:" >&2; grep -m5 -E 'page GPU|page error|rror|native-html-log-flood' "$GPU_LOG" >&2; rm -f "$GPU_LOG"; return 1
        fi
        echo "page GPU in the window: $gpu_page replayed with no error"; rm -f "$GPU_LOG"
      }
      for gpu_page in webgpu-triangle webgl-triangle canvas-chart shader-gallery; do
        check "page GPU in the window: $gpu_page" page_gpu_window "$gpu_page"
      done
      # Page requests in the window (issue 374): a page from a local server, async and sync
      # XMLHttpRequest, fetch, a data: URL and a CORS refusal (native_net_window_check.ts).
      check "native_net_window_check.ts (quickjs)" env QUICKJS_WASM="$QJS_GUEST" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi -A \
        "$LAB/native_net_window_check.ts" ${GPU_ENGINE[@]+"${GPU_ENGINE[@]}"}
      # Everyday use in the window against a local site (docs/foafnaut-daily-use.md): links,
      # back, reload, a 404 page, a start address that does not answer, typing in a search box
      # and Enter, a form's button, a POST; the open gaps (cookies, new-tab links, downloads)
      # must still fail (XFAIL) until they are closed.
      check "daily_use_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi -A \
        "$LAB/daily_use_check.ts" ${GPU_ENGINE[@]+"${GPU_ENGINE[@]}"}
    fi
  else
    echo 'NOT RUN: native_html_scripts_test.ts needs the QuickJS guest module (tools/wasmvm/build-quickjs.sh)'
  fi
  # The showcase gaps (issue 1268): each test passes while its gap is open, and fails when
  # an engine change closes it, so the test and its issue change together.
  check "showcase_gaps_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read "$LAB/showcase_gaps_test.ts"
  # The print gaps of issue 1279, in the same way.
  check "print_gaps_test.ts" deno test --no-check --no-config --no-npm --node-modules-dir=none --allow-read "$LAB/print_gaps_test.ts"
  # Print page breaks of the print showcase (issue 1268): chapters start pages, print rules apply.
  check "print_layout_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-ffi --allow-env "$LAB/print_layout_check.ts"
  # The whole print path to a PDF with no window or panel: Lean pages, GPU images, NSPrintOperation.
  if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
    PRINT_PDF=$(mktemp -t foafnaut-showcase).pdf
    check "print_document_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
      --allow-read --allow-ffi --allow-env "$LAB/print_document_check.ts" print-showcase.html "$PRINT_PDF"
    rm -f "$PRINT_PDF"
  else
    echo 'NOT RUN: print_document_check.ts needs the macOS window library'
  fi
  # Two-layer scroll (issue 1268): the composite of the layers has the bytes of one Lean
  # frame at each scroll tried, on this machine's GPU. With no GPU adapter it says NOT RUN.
  check "scroll_layers_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/scroll_layers_check.ts"
  # A heavy frame in bands of about 16 ms (issue 450) gives the bytes of one draw. NOT RUN with no GPU.
  check "banded_draw_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi --allow-env --allow-net=127.0.0.1 "$LAB/banded_draw_check.ts"
  # Chrome pixels (issue 1268): a selected address changes only the address box, in the selection colour.
  check "chrome_pixels_check.ts" deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-ffi "$LAB/chrome_pixels_check.ts"
  # Every run_html.ts sweep with --offscreen, native and Wasm engines (issue 1268): no window is
  # shown, so it runs with the screen locked and on CI. About 65 s on an M1.
  if [ "$(uname -s)" = Darwin ] && [ -f "$LAB/.build/native/libnative-window.dylib" ]; then
    check "sweeps.sh" bash "$LAB/sweeps.sh"
  else
    echo 'NOT RUN: sweeps.sh needs macOS and the window library'
  fi
  # The CPU backend (SVGRaster.lean) against WebGPU: each demo page and each SVG shapes test,
  # per pixel, within the tolerance of docs/designissues/2026-11-08-cpu-render-backend.md.
  # NOT RUN with no Chrome.
  check "cpu_render_diff_check.mjs" node "$LAB/cpu_render_diff_check.mjs"
else
  echo 'NOT RUN: native_html_test.ts needs the web-render engine, which this build does not have yet'
fi
# Every check ran: exit 1 when any failed (the summary above lists them).
if [ ${#FAILED[@]} != 0 ]; then exit 1; fi
