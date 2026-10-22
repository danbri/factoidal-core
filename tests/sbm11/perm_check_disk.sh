#!/usr/bin/env bash
#
# tests/sbm11/perm_check_disk.sh -- the temporary disk of the exact
# permutation check of activation (lemma L3b; `Harness/Sbm11PermCheck.lean`;
# https://github.com/danbri/factoidal/issues/810, OKR batch 3 KR 1.4,
# https://github.com/danbri/factoidal/issues/875).
#
# A generated dataset (tests/sbm11/gen_distinct_terms.py, 120,000 lines, 37
# predicates) is packed and verified (`l4sbm11 verify`). The check prints the
# bytes it wrote to its temporary directory and the peak size of that
# directory (`temp-written-bytes`, `temp-peak-bytes`).
#
#   admitted              the generation is admitted.
#   temp-at-most-half     the peak temporary bytes are at most half the bytes
#                         of the generation directory. Until 2026-10-22 the
#                         check wrote 32 bytes per row of POS, SPO and OSP
#                         (about 5 times the generation on olympics) and this
#                         row was an expected failure naming issue 810.
#   spill-temp-at-most-half
#                         the same with SBM11_VERIFY_GROUP_ROWS=4096, which
#                         makes the check write sorted runs of SPO and OSP
#                         and of the larger POS predicates to disk.
#   spill-many-runs       the run with SBM11_VERIFY_GROUP_ROWS=64 (more than
#                         a thousand runs, the merge heap) is admitted.
#
# Usage: tests/sbm11/perm_check_disk.sh. Environment: L4_BIN_DIR (the built
# binaries). Prints "perm check disk: N pass, M fail, K expected-fail (out of
# T)"; exit 1 when any case fails, 2 when a binary is missing.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
ISSUE="https://github.com/danbri/factoidal/issues/810"
# rows that are expected failures today (each names ISSUE); empty when none
XFAIL_ROWS=""
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-permdisk.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <group> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-8s %-30s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-8s %-30s %s\n' "$1" "$2" "$4"; fi
}
xfail() { # xfail <group> <name> <issue-url> <expected-failure-holds:0|1> <detail>
  if [ "$4" = 0 ]; then XFAIL=$((XFAIL + 1)); printf 'XFAIL  %-8s %-30s (%s) %s\n' "$1" "$2" "$3" "$5"
  else FAIL=$((FAIL + 1)); printf 'XPASS  %-8s %-30s (%s) %s -- change this case to an assertion and close the issue\n' "$1" "$2" "$3" "$5"; fi
}
row() { # row <group> <name> <ok:0|1> <detail>: an assertion, or an expected failure when listed in XFAIL_ROWS
  case " $XFAIL_ROWS " in
    *" $2 "*) if [ "$3" = 0 ]; then xfail "$1" "$2" "$ISSUE" 1 "$4"; else xfail "$1" "$2" "$ISSUE" 0 "$4"; fi ;;
    *) record "$1" "$2" "$3" "$4" ;;
  esac
}
summary() { echo "perm check disk: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"; }

python3 -I "$HERE/gen_distinct_terms.py" 120000 "$TMP/d.nt"
rc=0
"$BIN/l4sbm11-pack" "$TMP/d.nt" "$TMP/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
if [ "$rc" -ne 0 ]; then
  record setup pack 1 "exit $rc: $(tail -1 "$TMP/pack.log")"; summary; exit 1
fi
rm -f "$TMP/d.nt"
genb="$(du -sb "$TMP/gen" | cut -f1)"

# verify_case <name-prefix> <group rows or empty>
verify_case() {
  local pre="$1" gr="$2" vrc=0 peak written
  if [ -n "$gr" ]; then
    SBM11_VERIFY_GROUP_ROWS="$gr" "$BIN/l4sbm11" verify "$TMP/gen" >"$TMP/v$pre.out" 2>"$TMP/v$pre.err" || vrc=$?
  else
    "$BIN/l4sbm11" verify "$TMP/gen" >"$TMP/v$pre.out" 2>"$TMP/v$pre.err" || vrc=$?
  fi
  peak="$(grep -o 'temp-peak-bytes=[0-9]*' "$TMP/v$pre.err" | cut -d= -f2)"
  written="$(grep -o 'temp-written-bytes=[0-9]*' "$TMP/v$pre.err" | cut -d= -f2)"
  if [ "$vrc" -eq 0 ] && grep -q 'admitted failures=0' "$TMP/v$pre.out"; then
    record verify "${pre}admitted" 0 "$(grep 'exact permutation check' "$TMP/v$pre.err" | sed 's/.*check: //; s/ digest.*//')"
  else
    record verify "${pre}admitted" 1 "exit $vrc: $(grep 'FAIL' "$TMP/v$pre.err" | head -2 | tr '\n' ' ')"
  fi
  if [ -z "$peak" ]; then
    row disk "${pre}temp-at-most-half" 1 "no temp-peak-bytes in the output"
  elif [ $((2 * peak)) -le "$genb" ]; then
    row disk "${pre}temp-at-most-half" 0 "temp peak $peak bytes (written $written), generation $genb bytes"
  else
    row disk "${pre}temp-at-most-half" 1 "temp peak $peak bytes (written $written), generation $genb bytes"
  fi
}
verify_case "" ""
verify_case "spill-" 4096
rc=0
SBM11_VERIFY_GROUP_ROWS=64 "$BIN/l4sbm11" verify "$TMP/gen" >"$TMP/v64.out" 2>"$TMP/v64.err" || rc=$?
if [ "$rc" -eq 0 ] && grep -q 'admitted failures=0' "$TMP/v64.out"; then
  record verify spill-many-runs 0 "$(grep 'exact permutation check' "$TMP/v64.err" | sed 's/.*check: //; s/ digest.*//')"
else
  record verify spill-many-runs 1 "exit $rc: $(grep 'FAIL' "$TMP/v64.err" | head -2 | tr '\n' ' ')"
fi
left="$(ls -d "$TMP"/gen.verify-* 2>/dev/null | wc -l)"
if [ "$left" = 0 ]; then record verify temp-removed 0 "no temporary directory left"
else record verify temp-removed 1 "$left left"; fi
summary
[ "$FAIL" -eq 0 ]
