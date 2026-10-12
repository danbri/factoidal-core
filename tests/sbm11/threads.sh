#!/usr/bin/env bash
#
# tests/sbm11/threads.sh — answers of the parallel block scan (stage 1 of
# https://github.com/danbri/factoidal/issues/799) at 1, 2, 4 and 8 threads.
# Record: docs/designissues/2026-10-12-parallel-block-scans.md.
#
# Each query runs as `l4sbm11 query --threads N` for N in 1 2 4 8. The SPARQL
# JSON output (byte for byte) and the answer fields of the stderr line (path,
# row count, verify mode, constants looked up, block bytes read) must equal
# the N = 1 run. Two inputs:
#   gate      tests/sbm11/gate/gate.nq, packed and activated here, with every
#             tests/sbm11/gate/*.rq
#   olympics  an activated olympics generation (default
#             /home/user/qlvr-work/sbm11/s3/wfull, or $SBM11_OLYMPICS), with
#             tests/qlvr/queries/q*.rq
# The W3C census at several thread counts is tests/sbm11/census.sh with
# SBM11_THREADS set; this script does not run it.
#
# Prints one labelled line per input; exits 1 when any answer differs.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
OLY="${SBM11_OLYMPICS:-/home/user/qlvr-work/sbm11/s3/wfull}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-threads.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
THREADS="1 2 4 8"
fail=0

# answer_of FILE: the fields of the stderr answer line that do not depend on
# timing or on the delta log's replay time
answer_of() {
  grep -o 'sbm11-query: .*' "$1" | sed -e 's/; open .*//'
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
      timeout 600 "$BIN/l4sbm11" query "$gen" --file "$q" --threads "$t" \
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
  compare_inputs gate "$G" "$HERE"/gate/*.rq
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
  compare_inputs gate2 "$G2" "$HERE"/gate/*.rq
fi

echo "=== olympics"
if [ ! -d "$OLY" ]; then
  echo "olympics: no generation at $OLY (set SBM11_OLYMPICS); not compared"
  fail=1
else
  compare_inputs olympics "$OLY" "$ROOT"/tests/qlvr/queries/q*.rq
fi

if [ "$fail" = 0 ]; then echo "threads.sh: all answers identical"; else echo "threads.sh: FAILED"; fi
exit "$fail"
