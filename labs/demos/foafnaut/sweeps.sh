#!/usr/bin/env bash
# Every run_html.ts sweep with --offscreen (issue 1268): no window is shown, frames are drawn
# into a GPU texture, events go through the window library's queue. It runs with the screen
# locked, with the display asleep, and on a machine with no display (CI).
# One line for each sweep and engine: rc, seconds, and the offscreen latency summary.
# The latency here includes the pixel check of every frame (a sweep checks each frame). For
# input latency without it, run the sweep with --idle-checks-only: on 2026-11-08 the graph
# click was 195 ms here and 27.6 ms with --idle-checks-only (native engine).
# Exit 0 only when every run exits 0, or 4 (not run: the engine lacks an op the sweep needs). Usage: sweeps.sh [--only NAME]... [--wasm-only]
set -uo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
[ "$(uname -s)" = Darwin ] || { echo 'NOT RUN: sweeps.sh needs macOS (the window library)'; exit 0; }
for need in .build/native/libnative-window.dylib .build/native-html/runtime/web-render.wasm .build/engines/render-plan.wasm; do
  [ -f "$LAB/$need" ] || { echo "sweeps.sh: missing $need (build-engines.sh, build-executables.sh)" >&2; exit 2; }
done
ONLY=() WASM_ONLY=0
while [ $# -gt 0 ]; do
  case "$1" in
    --only) ONLY+=("${2:?--only needs a sweep name}"); shift 2 ;;
    --wasm-only) WASM_ONLY=1; shift ;;
    *) echo "usage: $0 [--only NAME]... [--wasm-only]" >&2; exit 2 ;;
  esac
done
NATIVE_LIB="$LAB/.build/web-render/engines/libweb-render.dylib"
ENGINES=(wasm)
[ "$WASM_ONLY" = 0 ] && [ -f "$NATIVE_LIB" ] && ENGINES=(native wasm)
[ "${#ENGINES[@]}" = 1 ] && [ "$WASM_ONLY" = 0 ] && echo "sweeps.sh: no libweb-render.dylib, so the Wasm engine only"
WORK=$(mktemp -d -t foafnaut-sweeps)
trap 'rm -rf "$WORK"' EXIT
INDEX="file://$LAB/pages/index.html"
# name and the run_html.ts arguments of each sweep. Every sweep supported by this run_html.ts.
SWEEPS=(
  "scroll|--scroll-sweep"
  "resize|--resize-sweep"
  "command|--command-sweep"
  "history|--history-sweep"
  "back|--back-sweep"
  "graph|--graph-sweep"
  "edit|--edit-sweep"
  "press|--press-sweep"
  "swipe|--swipe-sweep"
  "paste|--paste-sweep $INDEX"
  "print-pdf|--print-pdf $WORK/print.pdf"
  "shortcut|--shortcut-sweep --html $LAB/pages/showcase.html"
  "link-scroll|--link-scroll-sweep --follow-links --html $LAB/pages/showcase.html"
  "scroll-end|--scroll-end-sweep --html $LAB/pages/showcase-dataviz.html"
  "find|--find-sweep --html $LAB/fixtures/find/find.html"
)
SOURCE=$(cat "$LAB/run_html.ts")
FAILED=0 NOTRUN=0 START=$(date +%s)
for entry in "${SWEEPS[@]}"; do
  name=${entry%%|*} args=${entry#*|} flag=${args%% *}
  if [ "${#ONLY[@]}" -gt 0 ] && [[ " ${ONLY[*]} " != *" $name "* ]]; then continue; fi
  # A sweep of an open branch, not in this run_html.ts: said, not counted.
  [[ "$SOURCE" == *"\"$flag\""* ]] || { echo "$name: NOT RUN (no $flag in run_html.ts)"; continue; }
  for engine in "${ENGINES[@]}"; do
    log="$WORK/$name-$engine.log"
    if [ "$engine" = native ]; then choice=(--native-engine "$NATIVE_LIB"); else choice=(--wasm-engine); fi
    t0=$(date +%s)
    # shellcheck disable=SC2086 # the sweep arguments split on spaces, as written above
    timeout 600 deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi -A \
      "$LAB/run_html.ts" --offscreen --perf-summary --no-state --strict $args "${choice[@]}" >"$log" 2>&1
    rc=$?
    secs=$(( $(date +%s) - t0 ))
    summary=$(python3 -I - "$log" <<'EOF'
import json,sys
line=None
for raw in open(sys.argv[1],errors="replace"):
    if raw.startswith('{"type":"native-html-perf-summary"'):
        try: line=json.loads(raw)
        except ValueError: pass
if not line: print("no perf summary"); sys.exit()
l,f,s=line["inputLatency"],line["frames"],line["scrollPresents"]
print(f'{line.get("present","window")}: input latency (with a pixel check of every frame) {l["count"]} events p50 {l["p50Ms"]} p95 {l["p95Ms"]} max {l["maxMs"]} ms; '
      f'frames {f["presented"]} presented, {f["checked"]} checked, p50 {f["totalMsP50"]} ms; scroll presents {s["count"]}, p50 {s["totalMsP50"]} ms')
EOF
)
    # Exit code 4: the engine is older than the sweep (run_html.ts says which op is missing).
    if [ "$rc" = 4 ]; then
      NOTRUN=$((NOTRUN+1))
      echo "$name $engine: NOT RUN; $(grep -m1 'NOT RUN' "$log")"
      continue
    fi
    echo "$name $engine: rc=$rc ${secs}s; $summary"
    if [ "$rc" != 0 ]; then
      FAILED=$((FAILED+1))
      echo "--- $name $engine: its log, without the JSON trace lines" >&2
      grep -v "^{" "$log" >&2
    fi
  done
done
echo "sweeps.sh: $FAILED failed, $NOTRUN not run (engine older than the sweep); $(( $(date +%s) - START )) s"
[ "$FAILED" = 0 ]
