#!/usr/bin/env bash
#
# tests/sbm11/bench-threads.sh — warm latency of `l4sbm11 query --threads N`
# for N in THREADS (default 1 2 4 8), interleaved over ROUNDS (default 7)
# rounds, with the 1-minute load average before each process.
# Record: docs/designissues/2026-10-12-parallel-block-scans.md section 5.
#
# Usage: tests/sbm11/bench-threads.sh GEN [query.rq ...]
#   default queries: q01 q07 q10 q19 q21 of tests/qlvr/queries
#
# Each process opens GEN once and runs the query REPEAT times (default 10,
# `--repeat`); the warm figure of a process is the median of its runs. The
# CSV (stdout) has one row per process: round, query, threads, warm median
# ms, warm min ms, peak RSS kB (VmHWM), load1 before, load1 after. A summary
# table with the medians over rounds and the ratio to threads = 1 follows.
# Nothing is compared with a target here: the ratio is reported as measured.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4sbm11"
GEN="${1:?usage: bench-threads.sh GEN [query.rq ...]}"; shift
ROUNDS="${ROUNDS:-7}"
REPEAT="${REPEAT:-10}"
THREADS="${THREADS:-1 2 4 8}"
if [ $# -eq 0 ]; then
  set -- "$ROOT"/tests/qlvr/queries/q01-count-all.rq "$ROOT"/tests/qlvr/queries/q07-join-three.rq \
    "$ROOT"/tests/qlvr/queries/q10-orderby-limit-double.rq "$ROOT"/tests/qlvr/queries/q19-scan-bound-predicate-iri.rq \
    "$ROOT"/tests/qlvr/queries/q21-scan-bound-predicate-lang.rq
fi
OUT="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-bench-threads.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT
load1() { cut -d' ' -f1 /proc/loadavg; }

echo "round,query,threads,warm_median_ms,warm_min_ms,peak_rss_kb,load1_before,load1_after"
for r in $(seq 1 "$ROUNDS"); do
  for q in "$@"; do
    name="$(basename "$q" .rq)"
    for t in $THREADS; do
      lb="$(load1)"
      "$BIN" query "$GEN" --file "$q" --threads "$t" --repeat "$REPEAT" >"$OUT/out" 2>"$OUT/err" || {
        echo "bench: $name threads=$t exit $?" >&2; exit 1; }
      la="$(load1)"
      med="$(grep -o 'execution ms median [0-9.]*' "$OUT/err" | awk '{print $4}')"
      min="$(grep -o 'min [0-9.]*' "$OUT/err" | head -1 | awk '{print $2}')"
      rss="$(grep -o 'peak RSS (VmHWM): [0-9]* kB' "$OUT/err" | awk '{print $4}')"
      echo "$r,$name,$t,$med,$min,$rss,$lb,$la"
    done
  done
done
