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
#   range bytes  bytes fetched by positioned reads in a process run: under
#                --verify merkle the 65,536-byte chunks read and checked by
#                their Merkle proofs, under --verify none the exact ranges
#   file bytes   every byte the process read from the generation's files
#                (manifest, .merkle sidecars, PRM1 and GDX1 read whole under
#                merkle, the fetched ranges)
#   open ms      manifest, sidecars, GDX1 header (the permutations open on
#                first use, inside the execution time)
#   VERIFY       merkle or none: passed as --verify (unset: the CLI default,
#                none for a generation a CURRENT pointer names)
#   l4qlvr ms    with QLVR=1: the same for `l4qlvr query` on the QLever index
#                (process median of RUNS; warm with --repeat REPEAT)
#
# Usage: tests/sbm11/bench.sh GEN [q01 q02 ...]
# SBM11_BIN: the `l4sbm11` to time (default: the one this tree builds).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${SBM11_BIN:-$ROOT/formal/lean4/.lake/build/bin/l4sbm11}"
QBIN="$ROOT/formal/lean4/.lake/build/bin/l4qlvr"
INST="${QLVR_INST:-/home/user/qlvr-work/instance}"
GEN="${1:?usage: bench.sh GEN [queries]}"; shift
RUNS="${RUNS:-5}"
REPEAT="${REPEAT:-10}"
VFLAG=(); [ -n "${VERIFY:-}" ] && VFLAG=(--verify "$VERIFY")
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-bench.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
median() { sort -n | awk '{a[NR]=$1} END {print (NR ? a[int((NR+1)/2)] : "")}'; }
now_ms() { date +%s%N; }

sel=("$@")
echo "| Query | path | verify | process ms | open ms | warm ms | RSS kB | block bytes | range bytes | file bytes | l4qlvr process ms | l4qlvr warm ms |"
echo "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  name="$(basename "$rq" .rq)"
  if [ ${#sel[@]} -gt 0 ]; then
    hit=0; for s in "${sel[@]}"; do case $name in $s*) hit=1 ;; esac; done
    [ $hit = 1 ] || continue
  fi
  : >"$TMP/p"; : >"$TMP/o"
  for _ in $(seq "$RUNS"); do
    a=$(now_ms); "$BIN" query "$GEN" --file "$rq" "${VFLAG[@]}" >/dev/null 2>"$TMP/err"; b=$(now_ms)
    echo $(( (b - a) / 1000 )) >>"$TMP/p"
    grep -o 'open [0-9.]* ms' "$TMP/err" | grep -o '[0-9.]*' >>"$TMP/o"
  done
  p=$(median <"$TMP/p")
  om=$(sort -g "$TMP/o" | awk '{a[NR]=$1} END {print (NR ? a[int((NR+1)/2)] : "")}')
  vv=$(grep -o 'verify=[a-z]*' "$TMP/err" | head -1)
  fbytes=$(grep -o 'file bytes read [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  rss=$(grep -o 'VmHWM): [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  path=$(grep -o 'path=[a-z]*' "$TMP/err")
  bb=$(grep -o 'block bytes read [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  cb=$(grep -o 'range bytes fetched [0-9]*' "$TMP/err" | grep -o '[0-9]*$')
  w=$("$BIN" query "$GEN" --file "$rq" "${VFLAG[@]}" --repeat "$REPEAT" 2>&1 >/dev/null | grep -o 'median [0-9.]*' | grep -o '[0-9.]*$')
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
  echo "| $name | $path | $vv | $pm | $om | $w | $rss | $bb | $cb | $fbytes | $qp | $qw |"
done
