#!/usr/bin/env bash
# Run a probe page in Foafnaut on the Linux rig (tools/foafnaut-linux-rig/setup.sh first), served
# over local HTTP from .build/. Usage: run.sh [tor-probe.html|tor-split.html]. Prints the page
# lines and, for each page task that did work, the host's instruction count and real time.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../../../.." && pwd)
PAGE=${1:-tor-probe.html}; PORT=${PORT:-8765}; LOG=$(mktemp)
python3 -m http.server "$PORT" --bind 127.0.0.1 --directory "$HERE/.build" >/dev/null 2>&1 & SRV=$!
trap 'kill $SRV 2>/dev/null; pkill -f "watch-sweep 300" 2>/dev/null || true; rm -f "$LOG"' EXIT
bash "$ROOT/tools/foafnaut-linux-rig/run.sh" --url "http://127.0.0.1:$PORT/$PAGE" --offscreen \
  --watch-sweep 300 >"$LOG" 2>&1 & RUN=$!
for _ in $(seq 600); do grep -qE '^page: tor (end|error)' "$LOG" && break; kill -0 $RUN 2>/dev/null || break; sleep 1; done
sleep 2
grep -E '^page: tor ' "$LOG"
grep -E '"native-html-script"' "$LOG" | python3 -c '
import json,sys
for l in sys.stdin:
    r=json.loads(l)
    if r.get("instructions",0)>1000000: print("task cause=%s instructions=%d leanMs=%s" % (r["cause"], r["instructions"], r["leanMs"]))'
