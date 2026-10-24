#!/usr/bin/env bash
#
# tests/sbm11/pool-stress.sh — many short `l4sbm11 query` processes at 2, 4
# and 8 threads, each with a time limit, to find a rare hang or a wrong
# answer of the worker pool (Harness/WorkerPool.lean; issue
# https://github.com/danbri/factoidal/issues/981, record
# docs/designissues/2026-10-12-parallel-block-scans.md stage 1n).
#
# First `l4pool-bench stress` starts and stops the pool POOL_CYCLES times in
# one process (limit 120 s). Then each process opens the gate fixture (tests/sbm11/gate/gate.nq), so it
# starts the pool, runs one query and stops the pool: the start and the stop
# of the pool run once per process. The queries are the property-path queries
# of tests/sbm11/gate (ids-path-*.rq; ids-path-star-nested hung once at 4
# threads, issue 981) and tests/sbm11/threads/*.rq (the divided paths).
#
# A process that runs longer than LIMIT seconds is a hang: its thread stacks
# are written with gdb (`thread apply all bt`) to $LOG/hang-N.stacks, then it
# is killed. A process that exits nonzero, or whose SPARQL JSON differs from
# the 1-thread answer, is a failure.
#
# Environment (defaults give the bounded test, about 1 to 2 minutes):
#   RUNS=500         processes in all
#   THREADS="2 4 8"  thread counts, used in turn
#   LIMIT=10         seconds per process
#   LOAD=0           1: run one CPU-bound process per vCPU beside the runs
#   LOG=.claude-runs/pool-stress  where the hang stacks and the summary go
#   BIN=formal/lean4/.lake/build/bin/l4sbm11
#   QUERIES="a.rq b.rq"  in place of the default query list
#
# Prints one labelled summary line; exits 1 on any hang or failure.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BINDIR="$ROOT/formal/lean4/.lake/build/bin"
BIN="${BIN:-$BINDIR/l4sbm11}"
RUNS="${RUNS:-500}"
THREADS="${THREADS:-2 4 8}"
LIMIT="${LIMIT:-10}"
LOAD="${LOAD:-0}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-pool-stress.XXXXXX")"
LOG="${LOG:-$ROOT/.claude-runs/pool-stress}"
mkdir -p "$LOG"
HOGS=()
cleanup() {
  for h in "${HOGS[@]}"; do kill "$h" 2>/dev/null; done
  rm -rf "$TMP"
}
trap cleanup EXIT
export SBM11_MIN_RANGE_ROWS=0
export SBM11_PAGES="${SBM11_PAGES:-1000000}"

G="$TMP/gate"
rc=0
"$BINDIR/l4sbm11-pack" "$HERE/gate/gate.nq" "$G/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN" activate "$G" gen >"$TMP/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  echo "pool-stress: pack or activate failed (exit $rc)"; exit 1
fi

# 1. the pool alone: start, wake, work 0 to 200 us, stop, POOL_CYCLES times
#    in one process (`l4pool-bench stress`). Before the repair of issue 981
#    this hung within 20,000 cycles.
POOL_CYCLES="${POOL_CYCLES:-20000}"
pool_hang=0
"$BINDIR/l4pool-bench" stress "$POOL_CYCLES" 200 3 >"$TMP/pool.log" 2>&1 &
ppid=$!
for _ in $(seq 1 1200); do kill -0 "$ppid" 2>/dev/null || break; sleep 0.1; done
if kill -0 "$ppid" 2>/dev/null; then
  gdb -p "$ppid" -batch -ex 'thread apply all bt' >"$LOG/pool-bench-hang.stacks" 2>&1
  kill -9 "$ppid" 2>/dev/null
  pool_hang=1
  echo "  HANG l4pool-bench stress: stacks $LOG/pool-bench-hang.stacks"
fi
prc=0; wait "$ppid" 2>/dev/null || prc=$?
if [ "$pool_hang" = 0 ] && [ "$prc" -ne 0 ]; then
  pool_hang=1; echo "  FAIL l4pool-bench stress: exit $prc: $(tail -1 "$TMP/pool.log")"
fi
echo "pool-stress: l4pool-bench stress $POOL_CYCLES start-stop cycles (limit 120 s): $([ "$pool_hang" = 0 ] && echo "ended" || echo "HUNG or failed")"

# 2. query processes
if [ -n "${QUERIES:-}" ]; then read -r -a QS <<<"$QUERIES"
else QS=("$HERE"/gate/ids-path-*.rq "$HERE"/threads/*.rq); fi
read -r -a TS <<<"$THREADS"
# the 1-thread answer of each query (no pool)
for i in "${!QS[@]}"; do
  rc=0
  timeout 600 "$BIN" query "$G" --file "${QS[$i]}" --threads 1 >"$TMP/want-$i.out" 2>/dev/null || rc=$?
  if [ "$rc" -ne 0 ]; then echo "pool-stress: ${QS[$i]} at 1 thread: exit $rc"; exit 1; fi
done

if [ "$LOAD" = 1 ]; then
  for _ in $(seq 1 "$(nproc)"); do
    ( while :; do :; done ) &
    HOGS+=("$!")
  done
fi

hangs=0; fails=0; done_runs=0
t0=$(date +%s)
for ((n = 0; n < RUNS; n++)); do
  t=${TS[$(( n % ${#TS[@]} ))]}
  i=$(( (n / ${#TS[@]}) % ${#QS[@]} ))
  "$BIN" query "$G" --file "${QS[$i]}" --threads "$t" >"$TMP/got.out" 2>"$TMP/got.err" &
  pid=$!
  ( sleep "$LIMIT"
    if kill -0 "$pid" 2>/dev/null; then
      gdb -p "$pid" -batch -ex 'thread apply all bt' >"$LOG/hang-$n.stacks" 2>&1
      echo "query ${QS[$i]} threads $t" >>"$LOG/hang-$n.stacks"
      kill -9 "$pid" 2>/dev/null
    fi ) 2>/dev/null &
  wd=$!
  rc=0
  wait "$pid" || rc=$?
  pkill -P "$wd" sleep 2>/dev/null
  wait "$wd" 2>/dev/null
  done_runs=$((done_runs + 1))
  if [ -f "$LOG/hang-$n.stacks" ]; then
    hangs=$((hangs + 1))
    echo "  HANG run $n: $(basename "${QS[$i]}") threads=$t; stacks $LOG/hang-$n.stacks"
  elif [ "$rc" -ne 0 ]; then
    fails=$((fails + 1))
    cp "$TMP/got.err" "$LOG/fail-$n.err"
    echo "  FAIL run $n: $(basename "${QS[$i]}") threads=$t exit $rc: $(tail -1 "$TMP/got.err" | head -c 160)"
  elif ! cmp -s "$TMP/got.out" "$TMP/want-$i.out"; then
    fails=$((fails + 1))
    echo "  FAIL run $n: $(basename "${QS[$i]}") threads=$t: answer differs from threads=1"
  fi
done
t1=$(date +%s)
line="pool-stress: $done_runs processes ($(( ${#QS[@]} )) queries, threads $THREADS, load $LOAD, limit ${LIMIT} s, $((t1 - t0)) s): hangs $hangs, failures $fails"
echo "$line"
echo "$line" >>"$LOG/summary.txt"
[ "$hangs" -eq 0 ] && [ "$fails" -eq 0 ] && [ "$pool_hang" -eq 0 ]
