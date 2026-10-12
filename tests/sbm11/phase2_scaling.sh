#!/usr/bin/env bash
#
# tests/sbm11/phase2_scaling.sh -- the n, 2n, 4n scaling assertion for SBM11
# packer phase 2, the k-way merge of the term runs that writes GDV1, GDX1 and
# the remap files (https://github.com/danbri/factoidal/issues/804; skill
# danbri-function-precrime-checkers, section 3; record
# docs/designissues/2026-10-12-sbm11-stage3.md section 4.1).
#
# Sources: synthetic N-Triples (tests/sbm11/gen_distinct_terms.py) of N, 2N
# and 4N lines (N default 1,000,000: 1,333,371, 2,666,704 and 5,333,371
# distinct terms; 32, 62 and 121 term runs). Each is packed with
# `l4sbm11-pack SOURCE OUT --phase2-only`, which runs phase 1 and phase 2 and
# prints phase2-ms. Fails when, for each doubling,
#   phase2-ms(2m) > 2.2 x max(phase2-ms(m), FLOOR ms)      (FLOOR default 500)
# The number of term runs grows with the source (a run holds at most
# run-terms / workers terms), so a merge that scans every run head per record
# is quadratic in the terms; before the fix this failed (2026-10-12: 5,345 ms,
# 16,988 ms at 2N, 61,654 ms at 4N: 3.2 and 3.6 times per doubling).
#
# With SBM11_REF_PACK=BIN (an l4sbm11-pack that has --phase2-only) every rung
# is also packed by BIN, and dict.gdv1, dict.gdx1 and every remap file must be
# byte-identical between the two.
#
# Usage: tests/sbm11/phase2_scaling.sh
# Env:   SBM11_P2_LINES (default 1000000), SBM11_P2_FLOOR_MS (default 500),
#        SBM11_WORK (default /home/user/qlvr-work/sbm11/phase2-scaling; removed
#        at the end), L4_SBM11_PACK (default formal/lean4/.lake/build/bin/l4sbm11-pack),
#        SBM11_REF_PACK (optional).
# Exit:  0 all assertions hold, 1 an assertion fails, 2 setup error.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_SBM11_PACK:-$ROOT/formal/lean4/.lake/build/bin/l4sbm11-pack}"
REF="${SBM11_REF_PACK:-}"
N="${SBM11_P2_LINES:-1000000}"
FLOOR="${SBM11_P2_FLOOR_MS:-500}"
WORK="${SBM11_WORK:-/home/user/qlvr-work/sbm11/phase2-scaling}"
[ -x "$BIN" ] || { echo "missing $BIN (lake build l4sbm11-pack)"; exit 2; }
if [ -n "$REF" ] && [ ! -x "$REF" ]; then echo "missing $REF"; exit 2; fi
mkdir -p "$WORK" || exit 2
FAIL=0
check() { if [ "$2" = 1 ]; then echo "ok   $1"; else echo "FAIL $1"; FAIL=1; fi; }
field() { printf '%s\n' "$2" | grep -o "$1=[0-9.]*" | head -1 | cut -d= -f2; }

declare -A P2
for rung in 1 2 4; do
  src="$WORK/s$rung.nt"
  if ! python3 -I "$HERE/gen_distinct_terms.py" $((rung * N)) "$src"; then echo "generator failed"; exit 2; fi
  rm -rf "$WORK/out"
  rc=0
  log="$(timeout 900 "$BIN" "$src" "$WORK/out" --phase2-only 2>&1)" || rc=$?
  if [ "$rc" -ne 0 ]; then echo "FAIL ${rung}n: pack exit $rc: $log"; FAIL=1; rm -f "$src"; continue; fi
  printf '%s (load %s)\n' "$log" "$(cut -d' ' -f1-3 /proc/loadavg)"
  P2[$rung]="$(field phase2-ms "$log" | cut -d. -f1)"
  if [ -n "$REF" ]; then
    rm -rf "$WORK/ref"
    rc=0
    rlog="$(timeout 900 "$REF" "$src" "$WORK/ref" --phase2-only 2>&1)" || rc=$?
    if [ "$rc" -ne 0 ]; then echo "FAIL ${rung}n: reference pack exit $rc: $rlog"; FAIL=1
    else
      printf 'reference: %s\n' "$rlog"
      same=1; files=0
      for f in "$WORK/ref"/dict.gdv1 "$WORK/ref"/dict.gdx1 "$WORK/ref"/*.remap; do
        files=$((files + 1))
        cmp -s "$f" "$WORK/out/$(basename "$f")" || { same=0; echo "differs: $(basename "$f")"; }
      done
      [ "$(ls "$WORK/out" | wc -l)" = "$(ls "$WORK/ref" | wc -l)" ] || same=0
      check "${rung}n: $files files (GDV1, GDX1, remaps) byte-identical to the reference packer" "$same"
    fi
    rm -rf "$WORK/ref"
  fi
  rm -rf "$WORK/out" "$src"
done

if [ -n "${P2[1]:-}" ] && [ -n "${P2[2]:-}" ] && [ -n "${P2[4]:-}" ]; then
  b1=$(( P2[1] > FLOOR ? P2[1] : FLOOR ))
  b2=$(( P2[2] > FLOOR ? P2[2] : FLOOR ))
  check "phase 2 at 2n ${P2[2]} ms <= 2.2 x max(n ${P2[1]} ms, $FLOOR ms)" "$(( P2[2] * 10 <= 22 * b1 ? 1 : 0 ))"
  check "phase 2 at 4n ${P2[4]} ms <= 2.2 x max(2n ${P2[2]} ms, $FLOOR ms)" "$(( P2[4] * 10 <= 22 * b2 ? 1 : 0 ))"
else
  FAIL=1
fi
rmdir "$WORK" 2>/dev/null
exit "$FAIL"
