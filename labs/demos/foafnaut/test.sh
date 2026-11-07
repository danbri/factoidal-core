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
if [ -x "$LAB/.build/web-render/web-render-native" ]; then
  python3 "$LAB/../../../tools/check-demo-pages.py" "$LAB/.build/web-render/web-render-native"
else
  echo 'NOT RUN: check-demo-pages.py needs web-render-native, which this build does not have yet'
fi
# The native HTML tests need the web-render engine, which Builds makes after this
# step in its engines job and before it in its macOS job, and more permissions.
TESTS=()
for test in "$LAB/"*_test.ts; do case "$test" in "$LAB/native_html_test.ts"|"$LAB/native_html_bytes_test.ts"|"$LAB/native_window_queue_test.ts"|"$LAB/showcase_gaps_test.ts"|"$LAB/page_scripts_test.ts") ;; *) TESTS+=("$test");; esac; done
deno check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  "$LAB/run_ui.ts" "$LAB/run_lean.ts" "$LAB/run_svg.ts" "$LAB/run_foaf_svg.ts" "$LAB/run_html.ts" "$LAB/page_scripts_test.ts" "${TESTS[@]}"
# Page scripts (issue 1271): the QuickJS-NG session, the Lean DOM and the guest API.
if [ -f "$LAB/.build/script-engine/qjs-wasi-reactor.wasm" ]; then
  node --test "$LAB/web-render/script-engine/session.test.mjs"
  if [ -f "$LAB/.build/web-render/engines/web-render.mjs" ]; then node --test "$LAB/web-render/script-engine/lean-dom.test.mjs"; fi
else
  echo 'NOT RUN: session.test.mjs needs the QuickJS-NG reactor (web-render/script-engine/fetch-reactor.mjs)'
fi
deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --allow-read "${TESTS[@]}"
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
  # The showcase gaps (issue 1268): each test passes while its gap is open, and fails when
  # an engine change closes it, so the test and its issue change together.
  deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read "$LAB/showcase_gaps_test.ts"
  # Page scripts in the desktop host (issue 1271), and VerifiedJS refusing visibly (issue 1252).
  deno test --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-write --allow-run \
    "$LAB/page_scripts_test.ts"
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
else
  echo 'NOT RUN: native_html_test.ts needs the web-render engine, which this build does not have yet'
fi
