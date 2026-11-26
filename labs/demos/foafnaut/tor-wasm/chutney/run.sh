#!/usr/bin/env bash
# End-to-end test of the Arti wasm transport on a private Tor network (chutney, C tor for every
# node). Starts the network and two local web servers, runs deno/tor-host.ts with the opt-in,
# and checks: bootstrap 100%, one request through an exit, one request to an onion service, and
# the same guards after a second worker starts from the state the first one saved in a sealed
# local LWS storage (deno/tor-state.ts), and no guard identity in clear text in that storage;
# and stream isolation: one circuit per partition, and new ones after a new identity.
# Needs the @factoidal/core engine bundle (tools/fetch-builds.sh --set web).
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
# A fresh storage key for this test's sealed state store (never written to disk by the test).
FOAFNAUT_TOR_STATE_KEY=$(node "$HERE/../../../../../npm/factoidal/bin/factoidal.mjs" lws-keygen 2>/dev/null | tail -1)
export FOAFNAUT_TOR_STATE_KEY
deno run --unstable-worker-options --allow-net --allow-read --allow-write --allow-run --allow-env "$HERE/../deno/tor-host.ts" \
  --dangerously-use-unreviewed-tor-transport --config "$NET/nodes/arti.toml" --timeout 120000 \
  --request siteA@127.0.0.1:4748 --request siteA@127.0.0.1:4748 --request siteB@127.0.0.1:4748 \
  --request NEWID --request siteA@127.0.0.1:4748 --request siteC@"$ONION:5858" \
  --request PAR --request p1@127.0.0.1:4748 --request p2@127.0.0.1:4748 --request p3@"$ONION:5858" \
  --request p4@127.0.0.1:4748 --request p5@"$ONION:5858" --request p6@127.0.0.1:4748 --request END \
  --fetch a.example@http://127.0.0.1:4748/ --fetch b.example@http://127.0.0.1:4748/ \
  --fetch c.example@http://"$ONION":5858/ --fetch d.example@http://"$ONION":5858/ --fetch a.example@http://"$ONION":5858/ \
  --restart-check --hold 70000 --state-dir "$WORK/tor-state" --debug --trace-conns >"$OUT" 2>&1
grep -E '^\{' "$OUT"
ok=0
grep -q '"step":"bootstrap","ok":true' "$OUT" && echo "PASS bootstrap" || { echo "FAIL bootstrap"; ok=1; }
grep -q 'exit target' "$OUT" && echo "PASS exit request" || { echo "FAIL exit request"; ok=1; }
# Isolation, from Arti's debug lines (this run only; debug is off by default): the circuits of the
# four exit streams of run 1, in order: siteA, siteA, siteB, then siteA after a new identity.
mapfile -t circs < <(grep -oE 'Got a circuit for .* tunnel_id=Circ [0-9.]+' "$OUT" | head -4 | grep -oE 'Circ [0-9.]+$')
echo "circuits: ${circs[*]}"
if [[ ${#circs[@]} -eq 4 && "${circs[0]}" == "${circs[1]}" && "${circs[2]}" != "${circs[0]}" \
      && "${circs[3]}" != "${circs[0]}" && "${circs[3]}" != "${circs[2]}" ]]; then
  echo "PASS isolation (same partition shares, other partition and new identity do not)"
else echo "FAIL isolation"; ok=1; fi
grep -q 'onion service target' "$OUT" && echo "PASS onion service request" || { echo "FAIL onion service request"; ok=1; }
grep -q '"step":"parallel","run":"1","streams":6,"ok":6' "$OUT" && echo "PASS 6 streams at once (4 exit, 2 onion; new partitions, so new circuits)" || { echo "FAIL parallel streams"; ok=1; }
grep -q '"step":"proxy-check","run":"1","ok":true' "$OUT" && echo "PASS start-up check: loopback, private and reserved names all reach the proxy (NO_PROXY cleared)" || { echo "FAIL proxy check"; ok=1; }
grep -qE '"step":"socks","run":"1","fetches":5,"ok":5,"ms":[0-9]+,"streamsOpenAfter":0,"events":5' "$OUT" && echo "PASS 5 fetches at once through the SOCKS5 server, all 5 seen by it (Deno fetch, socks5h; 2 exit, 3 onion)" || { echo "FAIL SOCKS5 fetches"; ok=1; }
grep -E '"step":"(socks|socks-fetch)","run":"1"' "$OUT" | cut -c1-200
n=$(grep -E '^arti ' "$OUT" | grep -cE '127\.0\.0\.1|\[::1\]' || true)
[ "$n" = 0 ] && [ "$(grep -cE '^arti .*DEBUG' "$OUT")" -gt 0 ] && echo "PASS no relay address in Arti's debug lines (--debug on)" || { echo "FAIL relay addresses in $n Arti lines"; ok=1; }
grep '"step":"loop"' "$OUT" | head -3
grep -q '"via":"sealed LWS storage".*"sameGuards":true' "$OUT" && echo "PASS same guards after restart, through the sealed store" || { echo "FAIL same guards after restart"; ok=1; }
grep -q '"filesWithGuardIdsInClearText":0' "$OUT" && echo "PASS no guard identity in clear text on disk" || { echo "FAIL state at rest"; ok=1; }
echo "logs: $WORK"
exit $ok
