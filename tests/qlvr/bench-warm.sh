#!/usr/bin/env bash
#
# tests/qlvr/bench-warm.sh — `l4qlvr` against the QLever server with the
# start-up cost separated (https://github.com/danbri/factoidal/issues/778).
# Record: docs/designissues/2026-10-11-qlvr-performance.md.
#
# Per oracle query:
#   QLever compute  the server's own time.computeResult (qlever-results+json,
#                   send=0, result cache cleared before each run), median
#   QLever HTTP     curl time_total for application/sparql-results+json (rows
#                   serialised and sent), cache cleared, median
#   Lean process    wall clock of one `l4qlvr query` process (start, vocabulary
#                   load, trailers, side index, execution, output), median
#   Lean warm       `l4qlvr query --repeat REPEAT`: the session (vocabulary,
#                   trailers, side index) is loaded once; median execution of
#                   the REPEAT runs in the same process (constant lookup,
#                   column reads and decode, joins, modifiers, SPARQL JSON
#                   text; only the last run writes it)
#   Lean warm libzstd   the same with the column frames decoded by libzstd
#                   (ffi/qlvr_zstd.c) in place of the Lean decoder
#   decode          Lean decoder time inside one warm run (last run), ms
#
# RUNS (default 3) process and HTTP runs; REPEAT (default 10) warm runs.
# Needs the server on port QLVR_PORT (default 7019; tools/qlvr/build-instance.sh).
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4QLVR:-$ROOT/formal/lean4/.lake/build/bin/l4qlvr}"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
INST="$WORK/instance"
PORT="${QLVR_PORT:-7019}"
TOKEN="${QLVR_TOKEN:-olympics_qlvr}"
RUNS="${RUNS:-3}"
REPEAT="${REPEAT:-10}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/qlvr-bench.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

if ! curl -sf "localhost:$PORT" --data-urlencode 'query=ASK {}' >/dev/null; then
  echo "no QLever server on port $PORT" >&2; exit 2
fi
median() { sort -n | awk '{a[NR]=$1} END {print (NR ? a[int((NR+1)/2)] : "")}'; }
clear_cache() {
  curl -sf "localhost:$PORT" --data-urlencode cmd=clear-cache --data-urlencode "access-token=$TOKEN" >/dev/null
}
zstd_ok=1
"$BIN" query "$INST" 'SELECT * WHERE { ?s ?p ?o } LIMIT 1' --libzstd >/dev/null 2>&1 || zstd_ok=0

echo "| Query | Rows | QLever compute ms | QLever HTTP ms | Lean process ms | Lean warm ms | Lean warm libzstd ms | decode ms (Lean / libzstd) |"
echo "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
for rq in "$HERE"/queries/q*.rq; do
  name="$(basename "$rq" .rq)"
  q="$(cat "$rq")"
  "$BIN" query "$INST" --file "$rq" >/dev/null 2>&1
  : >"$TMP/qc"; : >"$TMP/qh"; : >"$TMP/lp"
  for _ in $(seq "$RUNS"); do
    clear_cache
    curl -s "localhost:$PORT" -H 'Accept: application/qlever-results+json' --data-urlencode "query=$q" \
      --data-urlencode send=0 | python3 -I -c 'import json,sys; print(json.load(sys.stdin)["time"]["computeResult"].rstrip("ms"))' >>"$TMP/qc"
    clear_cache
    curl -s -o /dev/null -w '%{time_total}\n' "localhost:$PORT" -H 'Accept: application/sparql-results+json' \
      --data-urlencode "query=$q" | awk '{printf "%d\n", $1 * 1000}' >>"$TMP/qh"
    t0=$(date +%s%N)
    "$BIN" query "$INST" --file "$rq" >/dev/null 2>"$TMP/err"
    t1=$(date +%s%N)
    echo $(( (t1 - t0) / 1000000 )) >>"$TMP/lp"
  done
  rows="$(grep -o 'query: [0-9]* rows' "$TMP/err" | grep -o '[0-9]*')"
  "$BIN" query "$INST" --file "$rq" --repeat "$REPEAT" >/dev/null 2>"$TMP/w"
  warm="$(grep -o 'median [0-9]*' "$TMP/w" | grep -o '[0-9]*' | awk '{printf "%.1f", $1 / 1000}')"
  dl="$(grep -o 'decode [0-9]* us' "$TMP/w" | head -1 | grep -o '[0-9]*' | awk '{printf "%.1f", $1 / 1000}')"
  warmz="n/a"; dz="n/a"
  if [ "$zstd_ok" = 1 ]; then
    "$BIN" query "$INST" --file "$rq" --repeat "$REPEAT" --libzstd >/dev/null 2>"$TMP/z"
    warmz="$(grep -o 'median [0-9]*' "$TMP/z" | grep -o '[0-9]*' | awk '{printf "%.1f", $1 / 1000}')"
    dz="$(grep -o 'decode [0-9]* us' "$TMP/z" | head -1 | grep -o '[0-9]*' | awk '{printf "%.1f", $1 / 1000}')"
  fi
  echo "| $name | $rows | $(median <"$TMP/qc") | $(median <"$TMP/qh") | $(median <"$TMP/lp") | $warm | $warmz | $dl / $dz |"
done
