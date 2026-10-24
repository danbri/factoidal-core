#!/usr/bin/env bash
#
# tests/sbm11/threads.sh — answers of the parallel block scan (stages 1 and
# 1b of https://github.com/danbri/factoidal/issues/799) at 1, 2, 4 and 8
# threads. Record: docs/designissues/2026-10-12-parallel-block-scans.md.
#
# Each query runs as `l4sbm11 query --threads N` for N in 1 2 4 8. The SPARQL
# JSON output (byte for byte) and the answer fields of the stderr line (path,
# row count, verify mode, constants looked up, block bytes read, range bytes
# fetched, file bytes read) must equal the N = 1 run. Inputs:
#   gate      tests/sbm11/gate/gate.nq, packed and activated here, with every
#             tests/sbm11/gate/*.rq and tests/sbm11/threads/*.rq
#   gate2     the same packed with 2 rows per block (several block ranges per
#             scan), the same queries; and a coverage check: at 4 threads the
#             divided streamed, counted and ORDER BY ... LIMIT paths of stage
#             1b each run for at least one query
#   olympics  an activated olympics generation (default
#             /home/user/qlvr-work/sbm11/s3/wfull, or $SBM11_OLYMPICS), with
#             tests/qlvr/queries/q*.rq
#   olympics, default page limit: q19 and q21 with SBM11_PAGES unset (default
#             8192), and again with SBM11_PAGES=2048 (the former default, fewer
#             pages than the two queries use: the eviction of a full cache
#             runs here); the SPARQL JSON and
#             the block bytes must be equal (the dictionary bytes are not
#             compared, see below)
#   dbpedia   the DBpedia slice generation of issue 798 (default
#             /home/user/bench-data/sbm11/dbpedia, or $SBM11_DBPEDIA; skipped
#             with a line when absent), tools/bench/three-engines/queries/
#             dbpedia d*.rq, `--verify none`; and at every thread count the
#             answer equal (as a multiset, the normalisation of
#             tools/bench/three-engines/bench.py) to the recorded Virtuoso
#             answer of the three-engine record ($BENCH_DATA/answers/dbpedia),
#             or, for d18 and d19 (added after that run, issue 823), to the
#             recorded answer of `l4factoidal query` over the source triples
#             the query reads (NAME.l4factoidal.json)
#
# Rendering beside the ORDER BY sort (stage 1o): the gate sections set
# SBM11_SORTED_RENDER_ROWS=1, so that every ORDER BY result without DISTINCT,
# OFFSET or LIMIT is rendered by pool workers while the calling thread sorts.
#
# Block ranges: the gate sections set SBM11_MIN_RANGE_ROWS=0, so that a scan
# of a few rows is divided into one range per thread (the default divides a
# scan only into ranges of at least 8,192 estimated rows,
# IdQuery.rangeCount); olympics and dbpedia run with the default.
#
# Dictionary page cache: the runs set SBM11_PAGES=1000000 (unless set), so
# that no page cache is emptied during a query. A page is then read once in
# every thread count and the dictionary byte counts are compared exactly.
# With the default limit (2,048 pages) a query that touches more pages
# empties the cache and reads pages again, and how many depends on the order
# in which the scan tasks touch them; that case is the olympics default-limit
# section above.
#
# Last, tests/sbm11/pool-stress.sh (POOL_STRESS_RUNS, default 500 query
# processes, each with a 10-second limit) looks for a hang of the worker pool
# (issue https://github.com/danbri/factoidal/issues/981).
#
# The W3C census at several thread counts is tests/sbm11/census.sh with
# SBM11_THREADS set; this script does not run it.
#
# Prints one labelled line per input; exits 1 when any answer differs.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
OLY="${SBM11_OLYMPICS:-/home/user/qlvr-work/sbm11/s3/wfull}"
DBP="${SBM11_DBPEDIA:-/home/user/bench-data/sbm11/dbpedia}"
BENCH_DATA="${BENCH_DATA:-/home/user/bench-data}"
export SBM11_PAGES="${SBM11_PAGES:-1000000}"
EXTRA=()
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-threads.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
THREADS="1 2 4 8"
fail=0

# answer_of FILE: the fields of the stderr answer line that do not depend on
# timing or on the delta log's replay time; with BLOCKS_ONLY=1 only the path,
# rows, verify mode and block bytes read
answer_of() {
  if [ "${BLOCKS_ONLY:-0}" = 1 ]; then
    grep -o 'sbm11-query: .*' "$1" | sed -e 's/; open .*//' -e 's/; constants looked up.*block bytes read/; block bytes read/' -e 's/; range bytes fetched.*//'
  else
    grep -o 'sbm11-query: .*' "$1" | sed -e 's/; open .*//'
  fi
}

# compare_inputs LABEL GEN QUERY...: each query at every thread count
compare_inputs() {
  local label="$1" gen="$2"
  shift 2
  local n=0 same=0 differ=0 errs=0 q t name ok base_out base_ans ans rc
  for q in "$@"; do
    n=$((n + 1))
    name="$(basename "$q" .rq)"
    ok=1
    for t in $THREADS; do
      rc=0
      timeout 600 "$BIN/l4sbm11" query "$gen" --file "$q" --threads "$t" "${EXTRA[@]}" \
        >"$TMP/$label-$name-t$t.out" 2>"$TMP/$label-$name-t$t.err" || rc=$?
      if [ "$rc" -ne 0 ]; then
        errs=$((errs + 1)); ok=0
        echo "  $label $name threads=$t: exit $rc: $(tail -1 "$TMP/$label-$name-t$t.err" | head -c 160)"
        break
      fi
      ans="$(answer_of "$TMP/$label-$name-t$t.err")"
      if [ "$t" = 1 ]; then
        base_out="$TMP/$label-$name-t1.out"
        base_ans="$ans"
        continue
      fi
      if cmp -s "$base_out" "$TMP/$label-$name-t$t.out" && [ "$ans" = "$base_ans" ]; then
        :
      else
        ok=0
        echo "  $label $name threads=$t: differs from threads=1"
      fi
    done
    if [ "$ok" = 1 ]; then same=$((same + 1)); else differ=$((differ + 1)); fail=1; fi
  done
  echo "$label: $n queries x 4 thread counts (1 2 4 8): identical $same, differ $differ, nonzero exit $errs (out of $n)"
}

MINR_SAVED="${SBM11_MIN_RANGE_ROWS-unset}"
export SBM11_MIN_RANGE_ROWS=0
# stage 1o: an ORDER BY result of 1 row or more is rendered on pool workers
# while the calling thread sorts (default: 64 rows or more)
SORTR_SAVED="${SBM11_SORTED_RENDER_ROWS-unset}"
export SBM11_SORTED_RENDER_ROWS=1
echo "=== gate fixture"
G="$TMP/gate"
rc=0
"$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$G/gen" --workers 1 >"$TMP/gpack.log" 2>&1 || rc=$?
if [ "$rc" -eq 0 ]; then
  "$BIN/l4sbm11" activate "$G" gen >"$TMP/gact.log" 2>&1 || rc=$?
fi
if [ "$rc" -ne 0 ]; then
  echo "gate: pack or activate failed (exit $rc)"
  fail=1
else
  compare_inputs gate "$G" "$HERE"/gate/*.rq "$HERE"/threads/*.rq
fi

echo "=== gate fixture, 2 rows per block (several chunks per scan)"
G2="$TMP/gate2"
rc=0
"$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$G2/gen" --workers 1 --block-rows 2 >"$TMP/g2pack.log" 2>&1 || rc=$?
if [ "$rc" -eq 0 ]; then
  "$BIN/l4sbm11" activate "$G2" gen >"$TMP/g2act.log" 2>&1 || rc=$?
fi
if [ "$rc" -ne 0 ]; then
  echo "gate2: pack or activate failed (exit $rc)"
  fail=1
else
  compare_inputs gate2 "$G2" "$HERE"/gate/*.rq "$HERE"/threads/*.rq
  # coverage: the divided paths of stage 1b ran
  streamed=0; counted=0; top=0
  for q in "$HERE"/gate/*.rq "$HERE"/threads/*.rq; do
    rc=0
    "$BIN/l4sbm11" query "$G2" --file "$q" --threads 4 --explain >/dev/null 2>"$TMP/cov.err" || rc=$?
    [ "$rc" -eq 0 ] || continue
    grep -q 'streamed in [0-9]* block ranges' "$TMP/cov.err" && streamed=$((streamed + 1))
    grep -q 'counted while streaming in [0-9]* block ranges' "$TMP/cov.err" && counted=$((counted + 1))
    grep -q 'rows of the order kept in each of' "$TMP/cov.err" && top=$((top + 1))
  done
  echo "gate2 coverage at 4 threads: divided streamed $streamed, counted $counted, ORDER BY ... LIMIT $top queries"
  if [ "$streamed" -eq 0 ] || [ "$counted" -eq 0 ] || [ "$top" -eq 0 ]; then
    echo "gate2 coverage: a divided path did not run"; fail=1
  fi
fi

if [ "$MINR_SAVED" = unset ]; then unset SBM11_MIN_RANGE_ROWS; else export SBM11_MIN_RANGE_ROWS="$MINR_SAVED"; fi
if [ "$SORTR_SAVED" = unset ]; then unset SBM11_SORTED_RENDER_ROWS; else export SBM11_SORTED_RENDER_ROWS="$SORTR_SAVED"; fi
echo "=== olympics"
if [ ! -d "$OLY" ]; then
  echo "olympics: no generation at $OLY (set SBM11_OLYMPICS); not compared"
  fail=1
else
  compare_inputs olympics "$OLY" "$ROOT"/tests/qlvr/queries/q*.rq
  echo "=== olympics, default page limit (SPARQL JSON and block bytes)"
  SBM11_PAGES= BLOCKS_ONLY=1 compare_inputs olympics-default-pages "$OLY" \
    "$ROOT"/tests/qlvr/queries/q19-*.rq "$ROOT"/tests/qlvr/queries/q21-*.rq
  echo "=== olympics, page limit 2048 (a cache that fills; SPARQL JSON and block bytes)"
  SBM11_PAGES=2048 BLOCKS_ONLY=1 compare_inputs olympics-small-pages "$OLY" \
    "$ROOT"/tests/qlvr/queries/q19-*.rq "$ROOT"/tests/qlvr/queries/q21-*.rq
fi

echo "=== dbpedia"
if [ ! -d "$DBP" ]; then
  echo "dbpedia: no generation at $DBP (set SBM11_DBPEDIA); not compared"
else
  EXTRA=(--verify none)
  compare_inputs dbpedia "$DBP" "$ROOT"/tools/bench/three-engines/queries/dbpedia/d*.rq
  # each thread count against the recorded Virtuoso answer
  rec_equal=0; rec_diff=0; rec_missing=0
  for q in "$ROOT"/tools/bench/three-engines/queries/dbpedia/d*.rq; do
    name="$(basename "$q" .rq)"
    want="$BENCH_DATA/answers/dbpedia/$name.virtuoso.json"
    # a query added after the three-engine run (d18, d19: issue 823) has the
    # answer of `l4factoidal query` over the source triples it reads
    [ -f "$want" ] || want="$BENCH_DATA/answers/dbpedia/$name.l4factoidal.json"
    if [ ! -f "$want" ]; then rec_missing=$((rec_missing + 1)); continue; fi
    for t in $THREADS; do
      got="$TMP/dbpedia-$name-t$t.out"
      if [ ! -f "$got" ]; then rec_diff=$((rec_diff + 1)); continue; fi
      v="$(python3 -I - "$ROOT/tools/bench/three-engines" "$got" "$want" <<'PY'
import sys
sys.path.insert(0, sys.argv[1])
import bench
a = bench.solutions(open(sys.argv[2], "rb").read())
b = bench.solutions(open(sys.argv[3], "rb").read())
print("equal" if bench.compare(a, b)["equal"] else "different %d %d" % (a[1], b[1]))
PY
)"
      if [ "$v" = equal ]; then rec_equal=$((rec_equal + 1))
      else rec_diff=$((rec_diff + 1)); echo "  dbpedia $name threads=$t: $v from the Virtuoso record"; fi
    done
  done
  echo "dbpedia against the three-engine record (Virtuoso answers; l4factoidal answers for d18, d19): equal $rec_equal, different $rec_diff (query x thread count), queries without a record $rec_missing"
  [ "$rec_diff" -eq 0 ] && [ "$rec_missing" -eq 0 ] || fail=1
  EXTRA=()
fi

echo "=== worker pool stress (tests/sbm11/pool-stress.sh, issue 981)"
rc=0
RUNS="${POOL_STRESS_RUNS:-500}" "$HERE/pool-stress.sh" || rc=$?
[ "$rc" -eq 0 ] || fail=1

if [ "$fail" = 0 ]; then echo "threads.sh: all answers identical"; else echo "threads.sh: FAILED"; fi
exit "$fail"
