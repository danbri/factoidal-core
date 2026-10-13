#!/usr/bin/env bash
#
# tests/sbm11/process-start.sh — process time of one selective lookup on the
# DBpedia slice (https://github.com/danbri/factoidal/issues/805). Record:
# docs/designissues/2026-10-12-sbm11-stage4.md section 13.
#
# Until issue 805 every `l4sbm11 query` process read each PRM1 file it used
# whole, also under --verify none: d01 (all triples of one subject, an SPO
# prefix scan) took 484 ms per process on the DBpedia slice against 0.24 ms
# warm (three-engine record, section 8 item 3), because the SPO PRM1 file is
# 8,185,170 bytes. The acceptance of the issue is a d01 process time under
# 50 ms.
#
# The check: RUNS (default 7) new processes of
#   l4sbm11 query GEN --file d01-subject-lookup.rq --verify none
# their median wall time must be under LIMIT_MS (default 50). Printed with the
# load average before and after, the bytes the process read from the
# generation's files, and its peak RSS.
#
# Usage: tests/sbm11/process-start.sh [GEN]
#   GEN       default /home/user/bench-data/sbm11/dbpedia (the slice of the
#             three-engine benchmark, tools/bench/three-engines/run.sh)
#   SBM11_BIN the l4sbm11 to time (default: the one this tree builds)
#   QUERY     the query file (default the d01 query of that benchmark)
#   VERIFY    none (default) or merkle
# Exit 0: median under the limit; 1: not; 2: an input is missing.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${SBM11_BIN:-$ROOT/formal/lean4/.lake/build/bin/l4sbm11}"
GEN="${1:-/home/user/bench-data/sbm11/dbpedia}"
QUERY="${QUERY:-$ROOT/tools/bench/three-engines/queries/dbpedia/d01-subject-lookup.rq}"
RUNS="${RUNS:-7}"
LIMIT_MS="${LIMIT_MS:-50}"
VERIFY="${VERIFY:-none}"
for need in "$BIN" "$GEN/manifest.sbm11" "$QUERY"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-start.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
load() { cut -d' ' -f1-3 /proc/loadavg; }
echo "load average before: $(load)"
: >"$TMP/t"
for _ in $(seq "$RUNS"); do
  a=$(date +%s%N)
  rc=0
  "$BIN" query "$GEN" --file "$QUERY" --verify "$VERIFY" >"$TMP/out" 2>"$TMP/err" || rc=$?
  b=$(date +%s%N)
  if [ "$rc" -ne 0 ]; then echo "FAIL: exit $rc: $(tail -1 "$TMP/err")"; exit 1; fi
  echo $(( (b - a) / 1000 )) >>"$TMP/t"
done
echo "load average after:  $(load)"
med=$(sort -n "$TMP/t" | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}')
ms=$(awk -v u="$med" 'BEGIN { printf "%.1f", u / 1000 }')
all=$(sort -n "$TMP/t" | awk '{printf "%s%.1f", (NR > 1 ? " " : ""), $1 / 1000}')
fbytes=$(grep -o 'file bytes read [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
obytes=$(grep -o 'open file bytes [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
rss=$(grep -o 'VmHWM): [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
rows=$(grep -o 'rows [0-9]*' "$TMP/err" | head -1 | grep -o '[0-9]*$')
echo "$(basename "$QUERY" .rq) --verify $VERIFY: process ms median $ms (runs: $all); rows $rows; file bytes read ${fbytes:-?} (at open ${obytes:-not reported}); peak RSS ${rss:-?} kB"
if awk -v u="$med" -v l="$LIMIT_MS" 'BEGIN { exit !(u < l * 1000) }'; then
  echo "ok: median $ms ms is under $LIMIT_MS ms"
  exit 0
fi
echo "FAIL: median $ms ms is not under $LIMIT_MS ms (https://github.com/danbri/factoidal/issues/805)"
exit 1
