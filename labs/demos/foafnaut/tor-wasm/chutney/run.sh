#!/usr/bin/env bash
# End-to-end test of the Arti wasm transport on a private Tor network (chutney, C tor for every
# node). Starts the network and two local web servers, runs deno/tor-host.ts with the opt-in,
# and checks: bootstrap 100%, one request through an exit, one request to an onion service, and
# the same guards after a second worker starts from the first one's saved state (kept in memory).
# Exits 0 only when all three pass. No public Tor traffic.
# Needs: tor (apt), chutney (pip install git+https://gitlab.torproject.org/tpo/core/chutney.git),
# deno, and build.sh run first.
#
# EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
# WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
# chutney's nodes use fixed local ports; a network left running makes the new one fail late.
# (Probe by connecting: `ss` is not installed everywhere.)
for p in 5100 7100 4747 4748; do
  if (exec 3<>"/dev/tcp/127.0.0.1/$p") 2>/dev/null; then
    echo "run.sh: port $p is in use (an earlier network still running?)" >&2; exit 2
  fi
done
WORK=${WORK:-$(mktemp -d)}
NET="$WORK/net"; mkdir -p "$NET" "$WORK/www47" "$WORK/www48"
echo "onion service target" > "$WORK/www47/index.html"
echo "exit target" > "$WORK/www48/index.html"
pids=()
cleanup() { chutney --data-dir "$NET" stop >/dev/null 2>&1 || true; kill "${pids[@]}" 2>/dev/null || true; }
trap cleanup EXIT
python3 -m http.server 4747 --bind 127.0.0.1 --directory "$WORK/www47" >/dev/null 2>&1 & pids+=($!)
python3 -m http.server 4748 --bind 127.0.0.1 --directory "$WORK/www48" >/dev/null 2>&1 & pids+=($!)
chutney --data-dir "$NET" init --net-from-script-path "$HERE/network" --disable-ipv6 true >"$WORK/chutney.log" 2>&1
chutney --data-dir "$NET" bootstrap >>"$WORK/chutney.log" 2>&1
ONION=$(find "$NET/nodes/" -path '*h/hidden_service/hostname' -exec cat {} \; | head -1)
OUT="$WORK/arti.log"
deno run --unstable-worker-options --allow-net --allow-read "$HERE/../deno/tor-host.ts" \
  --dangerously-use-unreviewed-tor-transport --config "$NET/nodes/arti.toml" --timeout 120000 \
  --request 127.0.0.1:4748 --request "$ONION:5858" --restart-check --hold 70000 >"$OUT" 2>&1
grep -E '^\{' "$OUT"
ok=0
grep -q '"step":"bootstrap","ok":true' "$OUT" && echo "PASS bootstrap" || { echo "FAIL bootstrap"; ok=1; }
grep -q 'exit target' "$OUT" && echo "PASS exit request" || { echo "FAIL exit request"; ok=1; }
grep -q 'onion service target' "$OUT" && echo "PASS onion service request" || { echo "FAIL onion service request"; ok=1; }
grep -q '"sameGuards":true' "$OUT" && echo "PASS same guards after restart" || { echo "FAIL same guards after restart"; ok=1; }
echo "logs: $WORK"
exit $ok
