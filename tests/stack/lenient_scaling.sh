#!/usr/bin/env bash
#
# tests/stack/lenient_scaling.sh -- the lenient (recovery) parse through the
# streaming path takes time linear in the input and peak memory flat in the
# input (https://github.com/danbri/factoidal/issues/716,
# skills/danbri-function-precrime-checkers, "the scaling assertion").
#
# For each format, tools/lenient-ladder-gen.py writes inputs of n, 2n, 4n and
# 8n statements with one malformed statement every K statements (errors
# spread through the whole input). `l4factoidal parse --lenient FILE` streams
# each file in 65,536-byte chunks under `/usr/bin/time -v`. The run fails when
#
#   * the diagnostic count is not the number of malformed statements, or the
#     printed quad count is not the number of statements kept;
#   * time(2x) > 2.6 * max(time(x), 1 s) for a consecutive pair (user + system
#     seconds; linear time predicts 2.0, quadratic 4.0);
#   * peak resident set (largest input) > 1.25 * peak (smallest) + 64 MiB
#     (flat memory predicts 1.0; memory linear in the input predicts 8.0).
#
# Prints one line per point and "N pass, M fail (out of T)" over the checks.
#
# Usage:  tests/stack/lenient_scaling.sh [base-statements [error-every [formats]]]
#         defaults: 250000 statements (N-Quads: about 25, 50, 100 and 200 MB),
#                   one error every 1000, formats "nquads turtle".
# Env:    LENIENT_SCALING_DIR      work directory (default: a mktemp dir, removed)
#         LENIENT_SCALING_TIMEOUT  seconds per parse (default 900)
#
# Needs /usr/bin/time (GNU time) and python3. Timing on a shared host is
# noisy; a failure of the time check alone should be re-run before it is
# read as a regression.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4factoidal"
GEN="$ROOT/tools/lenient-ladder-gen.py"

if [ ! -x "$BIN" ]; then
  echo "tests/stack/lenient_scaling.sh: $BIN not built (cd formal/lean4 && lake build l4factoidal)" >&2
  exit 2
fi
if [ ! -x /usr/bin/time ]; then
  echo "tests/stack/lenient_scaling.sh: /usr/bin/time (GNU time) not installed" >&2
  exit 2
fi

BASE="${1:-250000}"
EVERY="${2:-1000}"
FORMATS="${3:-nquads turtle}"
CAP="${LENIENT_SCALING_TIMEOUT:-900}"
if [ -n "${LENIENT_SCALING_DIR:-}" ]; then
  WORK="$LENIENT_SCALING_DIR"; mkdir -p "$WORK"; KEEP=1
else
  WORK="$(mktemp -d)"; KEEP=0
fi
cleanup() { if [ "$KEEP" = 0 ]; then rm -rf "$WORK"; fi; }
trap cleanup EXIT

PASS=0
FAIL=0
ok()   { echo "ok   $1"; PASS=$((PASS + 1)); }
bad()  { echo "FAIL $1"; FAIL=$((FAIL + 1)); }

ext_of() { case "$1" in nquads) echo nq ;; ntriples) echo nt ;; turtle) echo ttl ;; esac; }

for fmt in $FORMATS; do
  ext="$(ext_of "$fmt")"
  echo "=== $fmt: one malformed statement every $EVERY"
  printf '%-10s %12s %9s %9s %9s %9s %12s %10s\n' \
    statements bytes user_s sys_s cpu_s wall_s peak_rss_kb diags
  times=(); rss=()
  for mult in 1 2 4 8; do
    n=$((BASE * mult))
    f="$WORK/ladder-$n.$ext"
    meta="$(python3 "$GEN" --format "$fmt" --statements "$n" --error-every "$EVERY" --output "$f")"
    bytes="$(printf '%s' "$meta" | python3 -c 'import json,sys; print(json.load(sys.stdin)["bytes"])')"
    malformed="$(printf '%s' "$meta" | python3 -c 'import json,sys; print(json.load(sys.stdin)["malformed"])')"
    kept="$(printf '%s' "$meta" | python3 -c 'import json,sys; print(json.load(sys.stdin)["kept"])')"
    RC=0
    /usr/bin/time -v -o "$WORK/time.txt" timeout "$CAP" "$BIN" parse --lenient "$f" --format "$fmt" \
      > "$WORK/out.txt" 2> "$WORK/diags.jsonl" || RC=$?
    user="$(awk -F': ' '/User time/ {print $2}' "$WORK/time.txt")"
    sys="$(awk -F': ' '/System time/ {print $2}' "$WORK/time.txt")"
    wall="$(awk '/Elapsed \(wall clock\)/ {print $NF}' "$WORK/time.txt")"
    peak="$(awk -F': ' '/Maximum resident set size/ {print $2}' "$WORK/time.txt")"
    cpu="$(python3 -c "print(round($user + $sys, 2))")"
    ndiag="$(wc -l < "$WORK/diags.jsonl" | tr -d ' ')"
    count="$(tr -d ' \n' < "$WORK/out.txt")"
    printf '%-10s %12s %9s %9s %9s %9s %12s %10s\n' "$n" "$bytes" "$user" "$sys" "$cpu" "$wall" "$peak" "$ndiag"
    # Exit 1 is "diagnostics were written", which this input must produce.
    if [ "$RC" != 1 ] && ! { [ "$malformed" = 0 ] && [ "$RC" = 0 ]; }; then
      bad "$fmt n=$n: exit status $RC"
    fi
    if [ "$ndiag" = "$malformed" ] && [ "$count" = "$kept" ]; then
      ok "$fmt n=$n: $ndiag diagnostics, $count quads kept"
    else
      bad "$fmt n=$n: $ndiag diagnostics (expected $malformed), $count quads kept (expected $kept)"
    fi
    times+=("$cpu"); rss+=("$peak")
    rm -f "$f"
  done
  for i in 1 2 3; do
    prev="${times[$((i - 1))]}"; cur="${times[$i]}"
    if python3 -c "import sys; sys.exit(0 if $cur <= 2.6 * max($prev, 1.0) else 1)"; then
      ok "$fmt time x$((2 ** i)) / x$((2 ** (i - 1))): $cur s / $prev s"
    else
      bad "$fmt time x$((2 ** i)) / x$((2 ** (i - 1))): $cur s / $prev s (over 2.6)"
    fi
  done
  if python3 -c "import sys; sys.exit(0 if ${rss[3]} <= 1.25 * ${rss[0]} + 65536 else 1)"; then
    ok "$fmt peak memory flat: ${rss[0]} KiB at n, ${rss[3]} KiB at 8n"
  else
    bad "$fmt peak memory not flat: ${rss[0]} KiB at n, ${rss[3]} KiB at 8n"
  fi
done

echo "=== lenient_scaling: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" = 0 ]
