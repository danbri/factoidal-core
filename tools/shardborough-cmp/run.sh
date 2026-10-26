#!/usr/bin/env bash
# Run the 21 QLever oracle queries through the Shardborough disk query paths
# and compare each answer with QLever's.
#
# Usage: tools/shardborough-cmp/run.sh [WORK-DIR] [LAYOUT...]
#   WORK-DIR default /home/user/qlvr-work/shardborough-cmp (made by pack.sh)
#   LAYOUT   ibk3 (l4block-id-v3-query) and/or ibk5 (l4block-quad-query);
#            default both.
# Env: RUNS (measured runs per query, default 3; one unmeasured run first),
#      ORACLE (default /home/user/qlvr-work/oracle), QUERY_TIMEOUT (s, 600).
#
# Per query and layout it records: equal to the oracle (tests/qlvr/
# compare_query.py: multisets of solutions, numbers by value, ORDER BY keys
# in order), median wall ms, median peak RSS kB (VmHWM of the process), the
# tool's logical-read-bytes and fetched-bytes, the blocks read (shards=), the
# open mode, and zone-excluded (IBK5). Output: WORK/measure/queries-LAYOUT.tsv
# and one line per query on stdout.
#
# The in-memory snapshot mode (l4block-snapshot-session) is not run: it is
# not a Shardborough disk result (CLAUDE.md, 2026-10-11).
# Design record: docs/designissues/2026-10-11-shardborough-vs-qlever.md
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
B="$ROOT/formal/lean4/.lake/build/bin"
WORK="${1:-/home/user/qlvr-work/shardborough-cmp}"
shift || true
LAYOUTS="${*:-ibk3 ibk5}"
ORACLE="${ORACLE:-/home/user/qlvr-work/oracle}"
RUNS="${RUNS:-3}"
QT="${QUERY_TIMEOUT:-600}"
RU="$ROOT/tools/shardborough-cmp/rusage.py"
CMP="$ROOT/tests/qlvr/compare_query.py"
OUT="$WORK/measure"
mkdir -p "$OUT/answers"
echo "# a query file with no ORDER BY: compare_query.py checks multisets only" > "$OUT/no-order.rq"

for layout in $LAYOUTS; do
  case "$layout" in
    ibk3) TOOL="$B/l4block-id-v3-query" ;;
    ibk5) TOOL="$B/l4block-quad-query" ;;
    *) echo "run.sh: unknown layout $layout"; exit 2 ;;
  esac
  COL="$WORK/col-$layout"
  [ -e "$COL/CURRENT" ] || { echo "run.sh: $COL has no CURRENT; run pack.sh"; exit 2; }
  TSV="$OUT/queries-$layout.tsv"
  printf 'query\tequal\tmultiset_equal\toracle_rows\trows\twall_ms_median\tmaxrss_kb_median\tlogical_read_bytes\tfetched_bytes\tblocks\tzone_excluded\topen_mode\trc\n' > "$TSV"
  for q in "$ROOT"/tests/qlvr/queries/q*.rq; do
    name="$(basename "$q" .rq)"
    ans="$OUT/answers/$layout-$name.json"
    err="$OUT/answers/$layout-$name.err"
    QTEXT="$(cat "$q")"
    # One unmeasured run (warms the page cache), then RUNS measured runs.
    WARM_RC=0
    timeout "$QT" "$TOOL" "$COL" --json --query "$QTEXT" > "$ans" 2> "$err" || WARM_RC=$?
    for i in $(seq 1 "$RUNS"); do
      RC=0
      timeout "$QT" python3 "$RU" "$OUT/answers/$layout-$name.ru$i.json" -- \
        "$TOOL" "$COL" --json --query "$QTEXT" > "$ans" 2> "$err" || RC=$?
    done
    EQ=no
    CMP_RC=0
    python3 "$CMP" "$ORACLE/$name.srj" "$ans" "$q" > "$OUT/answers/$layout-$name.cmp" 2>&1 || CMP_RC=$?
    [ "$CMP_RC" -eq 0 ] && EQ=yes
    # The same comparison without the ORDER BY key check: QLever orders
    # strings by ICU collation, SPARQL 1.1 section 15.1 by code point.
    MS=no
    MS_RC=0
    python3 "$CMP" "$ORACLE/$name.srj" "$ans" "$OUT/no-order.rq" > "$OUT/answers/$layout-$name.cmp-multiset" 2>&1 || MS_RC=$?
    [ "$MS_RC" -eq 0 ] && MS=yes
    python3 - "$name" "$EQ" "$MS" "$ORACLE/$name.srj" "$ans" "$err" "$RC" "$WARM_RC" "$RUNS" \
      "$OUT/answers/$layout-$name" >> "$TSV" <<'PY'
import json, re, statistics, sys
name, eq, ms, oracle, ans, err, rc, warm_rc, runs, stem = sys.argv[1:11]
def rows(p):
    try:
        return str(len(json.load(open(p))["results"]["bindings"]))
    except Exception:
        return "-"
recs = []
for i in range(1, int(runs) + 1):
    try:
        recs.append(json.load(open(f"{stem}.ru{i}.json")))
    except Exception:
        pass
wall = statistics.median(r["wall_ms"] for r in recs) if recs else "-"
rss = statistics.median(r["maxrss_kb"] for r in recs) if recs else "-"
diag = open(err, errors="replace").read()
def field(k):
    m = re.search(k + r"=([^\s]+)", diag)
    return m.group(1) if m else "-"
mode = field("open-mode")
print("\t".join([name, eq, ms, rows(oracle), rows(ans), str(wall), str(rss),
                 field("logical-read-bytes"), field("fetched-bytes"),
                 field("shards"), field("zone-excluded"), mode, rc]))
PY
    tail -n 1 "$TSV" | sed "s/^/$layout\t/"
  done
done
