#!/usr/bin/env bash
#
# tests/sbm11/dict_scaling.sh -- the n, 2n, 4n scaling assertion for SBM11
# packer phases 1 and 2 and for the dictionary lookup
# (https://github.com/danbri/factoidal/issues/788; skill
# danbri-function-precrime-checkers, section 3).
#
# Sources: the first quarter, the first half and all of SOURCE (default the
# olympics N-Triples of the QLever instance, 1,781,625 triples). For each:
# `l4sbm11-dict-pack SOURCE OUT` (it prints its phase times and its peak RSS,
# VmHWM) and `l4sbm11-dict-pack --lookup-bench OUT 1000 100` (positioned
# reads). Fails when
#   pack time(4n)      > 9.0 x max(pack time(n), 1000 ms)
#   peak RSS(4n)       > 1.25 x peak RSS(n) + 65536 kB
#   lookup mean(4n)    > 2.0 x lookup mean(n) + 100 us
# With --doubled it also builds SOURCE followed by a copy of SOURCE whose
# IRIs carry a suffix (datatype IRIs unchanged), packs it, and fails when its
# peak RSS differs from the peak RSS of SOURCE by more than 10 % (stage 2
# acceptance: "peak RSS unchanged within 10 % when the source doubles").
#
# Usage: tests/sbm11/dict_scaling.sh [--doubled]
# Env:   SBM11_SOURCE (default /home/user/qlvr-work/instance/olympics.nt)
#        SBM11_WORK   (default /home/user/qlvr-work/sbm11/scaling; removed at the end)
#        L4_SBM11_BIN (default formal/lean4/.lake/build/bin/l4sbm11-dict-pack)
# Exit: 0 all assertions hold, 1 an assertion fails, 2 setup error.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_SBM11_BIN:-$ROOT/formal/lean4/.lake/build/bin/l4sbm11-dict-pack}"
SRC="${SBM11_SOURCE:-/home/user/qlvr-work/instance/olympics.nt}"
WORK="${SBM11_WORK:-/home/user/qlvr-work/sbm11/scaling}"
DOUBLED=0
[ "${1:-}" = "--doubled" ] && DOUBLED=1
[ -x "$BIN" ] || { echo "missing $BIN (lake build l4sbm11-dict-pack)"; exit 2; }
[ -f "$SRC" ] || { echo "missing $SRC"; exit 2; }
mkdir -p "$WORK" || exit 2
FAIL=0

lines="$(wc -l < "$SRC")"
q=$((lines / 4))
head -n "$q" "$SRC" > "$WORK/n1.nt"
head -n $((2 * q)) "$SRC" > "$WORK/n2.nt"

field() { # field NAME TEXT
  printf '%s\n' "$2" | grep -o "$1=[0-9.]*" | head -1 | cut -d= -f2
}

declare -A TIME RSS LOOK
run_one() { # run_one LABEL SOURCE
  local label="$1" src="$2" out="$WORK/out-$1" log rc
  rm -rf "$out"
  log="$(timeout 900 "$BIN" "$src" "$out" 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then echo "FAIL $label: pack exit $rc: $log"; FAIL=1; return; fi
  printf '%s\n' "$log"
  TIME[$label]="$(field total-ms "$log" | cut -d. -f1)"
  RSS[$label]="$(field peak-rss "$log")"
  log="$(timeout 900 "$BIN" --lookup-bench "$out" 1000 100 2>&1)"; rc=$?
  printf '%s\n' "$log"
  if [ "$rc" -ne 0 ]; then echo "FAIL $label: lookup exit $rc"; FAIL=1; fi
  LOOK[$label]="$(field mean-us "$log" | cut -d. -f1)"
  rm -rf "$out"
}

run_one n "$WORK/n1.nt"
run_one 2n "$WORK/n2.nt"
run_one 4n "$SRC"
rm -f "$WORK/n1.nt" "$WORK/n2.nt"

check() { # check DESCRIPTION CONDITION
  if [ "$2" = 1 ]; then echo "ok   $1"; else echo "FAIL $1"; FAIL=1; fi
}
if [ -n "${TIME[n]:-}" ] && [ -n "${TIME[4n]:-}" ]; then
  base=$(( TIME[n] > 1000 ? TIME[n] : 1000 ))
  check "pack time 4n ${TIME[4n]} ms <= 9.0 x max(n ${TIME[n]} ms, 1000 ms) (2n ${TIME[2n]} ms)" \
    "$(( TIME[4n] * 10 <= 90 * base ? 1 : 0 ))"
  check "peak RSS 4n ${RSS[4n]} kB <= 1.25 x n ${RSS[n]} kB + 65536 kB (2n ${RSS[2n]} kB)" \
    "$(( RSS[4n] * 100 <= 125 * RSS[n] + 6553600 ? 1 : 0 ))"
  check "lookup mean 4n ${LOOK[4n]} us <= 2.0 x n ${LOOK[n]} us + 100 us (2n ${LOOK[2n]} us)" \
    "$(( LOOK[4n] <= 2 * LOOK[n] + 100 ? 1 : 0 ))"
fi

if [ "$DOUBLED" = 1 ]; then
  python3 - "$SRC" "$WORK/doubled.nt" <<'PY'
import re, sys
src, dst = sys.argv[1], sys.argv[2]
iri = re.compile(r'(?<!\^\^)<([^>]*)>')
with open(dst, "w", encoding="utf-8") as out:
    with open(src, encoding="utf-8") as fh:
        for line in fh:
            out.write(line)
    with open(src, encoding="utf-8") as fh:
        for line in fh:
            out.write(iri.sub(lambda m: "<" + m.group(1) + "/copy2>", line))
PY
  run_one doubled "$WORK/doubled.nt"
  rm -f "$WORK/doubled.nt"
  if [ -n "${RSS[doubled]:-}" ] && [ -n "${RSS[4n]:-}" ]; then
    check "peak RSS doubled ${RSS[doubled]} kB within 10 % of source ${RSS[4n]} kB (time ${TIME[doubled]} ms against ${TIME[4n]} ms)" \
      "$(( RSS[doubled] * 100 <= 110 * RSS[4n] && RSS[doubled] * 100 >= 90 * RSS[4n] ? 1 : 0 ))"
  fi
fi
rmdir "$WORK" 2>/dev/null
exit "$FAIL"
