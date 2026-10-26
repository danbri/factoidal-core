#!/usr/bin/env bash
#
# tests/qlvr/bench.sh — time every oracle query in `l4qlvr query` and in the
# QLever server on the same machine. https://github.com/danbri/factoidal/issues/778
#
# Warm: one run of each first (file cache), then RUNS (default 3) measured
# runs; the table gives the median.
#
#   Lean wall     wall clock of the `l4qlvr query` process (start, loading the
#                 vocabulary and six permutation trailers, side-index lookups,
#                 execution, SPARQL JSON to a file)
#   Lean exec     l4qlvr's own "execution" time (constant lookup, scans,
#                 joins, modifiers, rendering)
#   Lean RSS      peak RSS of the process (VmHWM), kB
#   QLever HTTP   curl time_total for the same query, Accept
#                 application/sparql-results+json, result cache cleared before
#                 each run
#   QLever total  the server's own "time.total" (application/qlever-results+json,
#                 send=0 so no rows are exported; cache cleared before each run)
#
# Needs the server on port QLVR_PORT (default 7019; tools/qlvr/build-instance.sh)
# and the access token of tools/qlvr/Qleverfile for clearing the cache.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4qlvr"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
INST="$WORK/instance"
PORT="${QLVR_PORT:-7019}"
TOKEN="${QLVR_TOKEN:-olympics_qlvr}"
RUNS="${RUNS:-3}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/qlvr-bench.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

if ! curl -sf "localhost:$PORT" --data-urlencode 'query=ASK {}' >/dev/null; then
  echo "no QLever server on port $PORT" >&2; exit 2
fi
median() { sort -n | awk '{a[NR]=$1} END {print (NR ? a[int((NR+1)/2)] : "")}'; }
clear_cache() {
  curl -sf "localhost:$PORT" --data-urlencode cmd=clear-cache --data-urlencode "access-token=$TOKEN" >/dev/null
}

echo "| Query | Rows | Lean wall ms | Lean exec ms | Lean peak RSS kB | QLever HTTP ms | QLever total ms |"
echo "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"
for rq in "$HERE"/queries/q*.rq; do
  name="$(basename "$rq" .rq)"
  q="$(cat "$rq")"
  "$BIN" query "$INST" --file "$rq" >/dev/null 2>&1
  : >"$TMP/lw"; : >"$TMP/le"; : >"$TMP/lr"; : >"$TMP/qh"; : >"$TMP/qt"
  for _ in $(seq "$RUNS"); do
    t0=$(date +%s%N)
    "$BIN" query "$INST" --file "$rq" >"$TMP/out.json" 2>"$TMP/err"
    t1=$(date +%s%N)
    echo $(( (t1 - t0) / 1000000 )) >>"$TMP/lw"
    grep -o 'execution [0-9]* ms' "$TMP/err" | grep -o '[0-9]*' >>"$TMP/le"
    grep -o 'VmHWM): [0-9]* kB' "$TMP/err" | grep -o '[0-9]*' >>"$TMP/lr"
    rows="$(grep -o 'query: [0-9]* rows' "$TMP/err" | grep -o '[0-9]*')"
    clear_cache
    curl -s -o /dev/null -w '%{time_total}\n' "localhost:$PORT" -H 'Accept: application/sparql-results+json' \
      --data-urlencode "query=$q" | awk '{printf "%d\n", $1 * 1000}' >>"$TMP/qh"
    clear_cache
    curl -s "localhost:$PORT" -H 'Accept: application/qlever-results+json' --data-urlencode "query=$q" \
      --data-urlencode send=0 | python3 -I -c 'import json,sys; print(json.load(sys.stdin)["time"]["total"].rstrip("ms"))' >>"$TMP/qt"
  done
  echo "| $name | $rows | $(median <"$TMP/lw") | $(median <"$TMP/le") | $(sort -n "$TMP/lr" | tail -1) | $(median <"$TMP/qh") | $(median <"$TMP/qt") |"
done
