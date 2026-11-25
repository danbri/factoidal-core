#!/usr/bin/env bash
# Run tor-bootstrap.html in Foafnaut on the Linux rig (tools/foafnaut-linux-rig/setup.sh first),
# served over local HTTP from .build/. Prints the page and Arti lines, and the host's instruction
# count and real engine time (leanMs) of each page task that did work.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../../../.." && pwd)
PORT=${PORT:-8766}; LOG=${LOG:-$(mktemp)}; WAIT=${WAIT:-900}
python3 -m http.server "$PORT" --bind 127.0.0.1 --directory "$HERE/.build" >/dev/null 2>&1 & SRV=$!
trap 'kill $SRV 2>/dev/null; pkill -f "watch-sweep 1500" 2>/dev/null || true' EXIT
bash "$ROOT/tools/foafnaut-linux-rig/run.sh" --url "http://127.0.0.1:$PORT/tor-bootstrap.html" --offscreen \
  --watch-sweep 1500 >"$LOG" 2>&1 & RUN=$!
for _ in $(seq "$WAIT"); do grep -qE '^page: page (end|error)' "$LOG" && break; kill -0 $RUN 2>/dev/null || break; sleep 1; done
sleep 2
grep -E '^page: (page|tor|arti)' "$LOG" | cut -c1-300
grep -E '"native-html-script"' "$LOG" | python3 -c '
import json,sys
for l in sys.stdin:
    r=json.loads(l)
    if r.get("instructions",0)>1000000: print("task cause=%s instructions=%d leanMs=%s" % (r["cause"], r["instructions"], r["leanMs"]))'
# Expected failure (https://github.com/danbri/factoidal-core/issues/1061): the raw page clock is
# virtual and reads earlier than 2024. An unexpected pass fails the run.
raw=$(grep -oE '^page: page clock-raw [0-9]+' "$LOG" | grep -oE '[0-9]+$' || true)
if [[ -z "$raw" ]]; then echo "clock: no reading"; exit 1
elif (( raw < 1704067200000 )); then echo "XFAIL page clock is not real ($raw ms): https://github.com/danbri/factoidal-core/issues/1061"
else echo "UNEXPECTED PASS page clock is real ($raw ms): remove the Date.now shim in pages.py and close https://github.com/danbri/factoidal-core/issues/1061"; exit 1; fi
echo "log: $LOG"
