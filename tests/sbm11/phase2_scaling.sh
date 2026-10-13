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
# distinct terms). Each is packed with `l4sbm11-pack SOURCE OUT --phase2-only
# --run-terms 32768` (8,192 terms per run and worker: 244, 417 and 836 term
# runs, the order of the DBpedia slice's runs at the default run size), which
# runs phase 1 and phase 2 and prints phase2-ms (wall) and, on Linux,
# phase2-cpu-ms (CPU time of the one thread that runs phase 2, from
# /proc/thread-self/schedstat). The test uses phase2-cpu-ms where it is
# printed, else phase2-ms. Each source is packed REPS times (default 3), in
# rounds of n, 2n, 4n, and the median is used. Fails when
#   phase2(4n) > 4.84 x max(phase2(n), FLOOR ms)   (2.2 per doubling; FLOOR 500)
# The run count k grows with the source (a run holds at most run-terms /
# workers terms). A merge that scans every run head per record is quadratic.
# A merge through a tree costs about log2 k comparisons per record, one more
# per doubling, so its ratio per doubling is a little above 2 (2.05 to 2.15
# measured); one run at load 1 to 2.5 on 4 vCPUs varied by up to 18 %, in CPU
# time too (other processes share the machine), and single doublings
# measured 1.86 to 2.38, so the test bounds the two doublings together and
# prints each. With N = 500,000 the n run took under 1 s and varied most.
# Before the fix (2026-10-12, N = 1,000,000, default run size): 5,345, 16,988
# and 61,654 ms (3.2 and 3.6 per doubling); record:
# docs/designissues/2026-10-12-sbm11-stage3.md section 4.1.
#
# With SBM11_REF_PACK=BIN (an l4sbm11-pack that has --phase2-only) every rung
# is also packed by BIN, and dict.gdv1, dict.gdx1 and every remap file must be
# byte-identical between the two.
#
# Usage: tests/sbm11/phase2_scaling.sh
# Env:   SBM11_P2_LINES (default 1000000), SBM11_P2_RUN_TERMS (default 32768),
#        SBM11_P2_FLOOR_MS (default 500), SBM11_P2_REPS (default 3),
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
RUNTERMS="${SBM11_P2_RUN_TERMS:-32768}"
FLOOR="${SBM11_P2_FLOOR_MS:-500}"
REPS="${SBM11_P2_REPS:-3}"
WORK="${SBM11_WORK:-/home/user/qlvr-work/sbm11/phase2-scaling}"
[ -x "$BIN" ] || { echo "missing $BIN (lake build l4sbm11-pack)"; exit 2; }
if [ -n "$REF" ] && [ ! -x "$REF" ]; then echo "missing $REF"; exit 2; fi
mkdir -p "$WORK" || exit 2
FAIL=0
check() { if [ "$2" = 1 ]; then echo "ok   $1"; else echo "FAIL $1"; FAIL=1; fi; }
field() { printf '%s\n' "$2" | grep -o "$1=[0-9.]*" | head -1 | cut -d= -f2; }

declare -A P2 TIMES
KIND="phase2-ms"
for rung in 1 2 4; do
  if ! python3 -I "$HERE/gen_distinct_terms.py" $((rung * N)) "$WORK/s$rung.nt"; then echo "generator failed"; exit 2; fi
done
# rounds of n, 2n, 4n: a change of machine load during the test falls on
# every size alike
for rep in $(seq 1 "$REPS"); do
  for rung in 1 2 4; do
    rm -rf "$WORK/out"
    rc=0
    log="$(timeout 900 "$BIN" "$WORK/s$rung.nt" "$WORK/out" --phase2-only --run-terms "$RUNTERMS" 2>&1)" || rc=$?
    if [ "$rc" -ne 0 ]; then echo "FAIL ${rung}n: pack exit $rc: $log"; FAIL=1; continue; fi
    printf '%s (load %s)\n' "$log" "$(cut -d' ' -f1-3 /proc/loadavg)"
    cpu="$(field phase2-cpu-ms "$log" | cut -d. -f1)"
    if [ -n "$cpu" ]; then t="$cpu"; KIND="phase2-cpu-ms"; else t="$(field phase2-ms "$log" | cut -d. -f1)"; fi
    TIMES[$rung]="${TIMES[$rung]:-} $t"
  done
done
rm -rf "$WORK/out"
for rung in 1 2 4; do
  read -r -a times <<<"${TIMES[$rung]:-}"
  if [ "${#times[@]}" -eq "$REPS" ]; then
    P2[$rung]="$(printf '%s\n' "${times[@]}" | sort -n | sed -n "$(( (REPS + 1) / 2 ))p")"
    echo "${rung}n: $KIND median ${P2[$rung]} of ${times[*]}"
  fi
done

if [ -n "$REF" ]; then
  for rung in 1 2 4; do
    rm -rf "$WORK/out" "$WORK/ref"
    rc=0
    timeout 900 "$BIN" "$WORK/s$rung.nt" "$WORK/out" --phase2-only --run-terms "$RUNTERMS" >/dev/null 2>&1 || rc=$?
    rlog="$(timeout 900 "$REF" "$WORK/s$rung.nt" "$WORK/ref" --phase2-only --run-terms "$RUNTERMS" 2>&1)" || rc=$?
    if [ "$rc" -ne 0 ]; then echo "FAIL ${rung}n: pack or reference pack exit $rc: $rlog"; FAIL=1
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
    rm -rf "$WORK/out" "$WORK/ref"
  done
fi
rm -f "$WORK/s1.nt" "$WORK/s2.nt" "$WORK/s4.nt"

if [ -n "${P2[1]:-}" ] && [ -n "${P2[2]:-}" ] && [ -n "${P2[4]:-}" ]; then
  b1=$(( P2[1] > FLOOR ? P2[1] : FLOOR ))
  r2="$(python3 -c "print(f'{${P2[2]} / $b1:.2f}')")"
  r4="$(python3 -c "print(f'{${P2[4]} / max(${P2[2]}, $FLOOR):.2f}')")"
  echo "doublings: 2n/n $r2, 4n/2n $r4"
  check "phase 2 ($KIND) at 4n ${P2[4]} ms <= 4.84 x max(n ${P2[1]} ms, $FLOOR ms): 2.2 per doubling (2n ${P2[2]} ms)" \
    "$(( P2[4] * 100 <= 484 * b1 ? 1 : 0 ))"
else
  FAIL=1
fi
rmdir "$WORK" 2>/dev/null
exit "$FAIL"
