#!/usr/bin/env bash
#
# tests/sbm11/bench.sh — SBM11 stage 4 query timings
# (https://github.com/danbri/factoidal/issues/790). Record:
# docs/designissues/2026-10-12-sbm11-stage4.md section 6.
#
# Per oracle query (tests/qlvr/queries/q*.rq):
#   process ms   wall clock of one `l4sbm11 query` process (start, manifest,
#                the permutations the plan opens, dictionary lookups, scans,
#                joins, modifiers, SPARQL JSON), median of RUNS (default 5)
#   warm ms      `l4sbm11 query --repeat REPEAT` (default 10): the generation
#                is opened once; median execution of the runs in that process
#                (the opened permutations, the verified chunk caches and the
#                dictionary page cache persist between runs)
#   RSS kB       peak resident set (VmHWM) of the last process run
#   block bytes  PRB1 frame bytes the plan reads (positioned reads)
#   chunk bytes  bytes of the 65,536-byte chunks read and verified by their
#                Merkle proofs in a process run (the read unit of `pread`)
#   l4qlvr ms    with QLVR=1: the same for `l4qlvr query` on the QLever index
#                (process median of RUNS; warm with --repeat REPEAT)
#
# Usage: tests/sbm11/bench.sh GEN [q01 q02 ...]
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4sbm11"
QBIN="$ROOT/formal/lean4/.lake/build/bin/l4qlvr"
INST="${QLVR_INST:-/home/user/qlvr-work/instance}"
GEN="${1:?usage: bench.sh GEN [queries]}"; shift
RUNS="${RUNS:-5}"
REPEAT="${REPEAT:-10}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-bench.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
median() { sort -n | awk '{a[NR]=$1} END {print (NR ? a[int((NR+1)/2)] : "")}'; }
now_ms() { date +%s%N; }

sel=("$@")
echo "| Query | path | process ms | warm ms | RSS kB | block bytes | chunk bytes | l4qlvr process ms | l4qlvr warm ms |"
echo "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  name="$(basename "$rq" .rq)"
  if [ ${#sel[@]} -gt 0 ]; then
    hit=0; for s in "${sel[@]}"; do case $name in $s*) hit=1 ;; esac; done
    [ $hit = 1 ] || continue
  fi
  : >"$TMP/p"
  for _ in $(seq "$RUNS"); do
    a=$(now_ms); "$BIN" query "$GEN" --file "$rq" >/dev/null 2>"$TMP/err"; b=$(now_ms)
    echo $(( (b - a) / 1000 )) >>"$TMP/p"
  done
  p=$(median <"$TMP/p")
  rss=$(grep -o 'VmHWM): [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  path=$(grep -o 'path=[a-z]*' "$TMP/err")
  bb=$(grep -o 'block bytes read [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  cb=$(grep -o 'chunk bytes fetched and verified [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  w=$("$BIN" query "$GEN" --file "$rq" --repeat "$REPEAT" 2>&1 >/dev/null | grep -o 'median [0-9.]*' | grep -o '[0-9.]*$')
  qp=""; qw=""
  if [ "${QLVR:-0}" = 1 ]; then
    : >"$TMP/q"
    for _ in $(seq "$RUNS"); do
      a=$(now_ms); "$QBIN" query "$INST" --file "$rq" >/dev/null 2>&1; b=$(now_ms)
      echo $(( (b - a) / 1000 )) >>"$TMP/q"
    done
    qp=$(median <"$TMP/q")
    qp=$(awk -v u="$qp" 'BEGIN { printf "%.1f", u / 1000 }')
    qw=$("$QBIN" query "$INST" --file "$rq" --repeat "$REPEAT" 2>&1 >/dev/null | grep -o 'median [0-9]*' | head -1 | grep -o '[0-9]*$')
    qw=$(awk -v u="$qw" 'BEGIN { printf "%.1f", u / 1000 }')
  fi
  pm=$(awk -v u="$p" 'BEGIN { printf "%.1f", u / 1000 }')
  echo "| $name | $path | $pm | $w | $rss | $bb | $cb | $qp | $qw |"
done
