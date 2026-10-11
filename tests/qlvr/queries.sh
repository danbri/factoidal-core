#!/usr/bin/env bash
#
# tests/qlvr/queries.sh — every oracle query through `l4qlvr query` against
# QLever's answers. https://github.com/danbri/factoidal/issues/778
#
# For each tests/qlvr/queries/qNN-*.rq: run `l4qlvr query INDEXDIR --file`,
# compare the SPARQL JSON with the oracle answer QLVR_WORK/oracle/qNN-*.srj
# as multisets of solutions (numbers by value; the ORDER BY keys in order
# when the query has ORDER BY; tests/qlvr/compare_query.py).
#
# Outcomes per query:
#   pass     equal to the oracle
#   fail     different, or an error (exit 1)
#   refused  `l4qlvr` says the query is outside its fragment (exit 3).
#            A refusal listed in tests/qlvr/expected-refusals.tsv (with the
#            issue that tracks it) is an expected failure (XFAIL) and does not
#            fail the run; an unlisted refusal fails the run; a listed query
#            that is answered (pass or fail) is XPASS/STALE and fails the run,
#            so the list and the issue are updated when the gap closes.
#
# Prints one line per query (with Lean time and peak RSS from l4qlvr's
# stderr), then "qlvr queries: N pass, M fail, R refused (out of T)".
# Exit 0 only when every query passes or is an expected refusal; 2 when an
# input is missing.
set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4qlvr"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
INST="$WORK/instance"
ORACLE="$WORK/oracle"
XFAIL="$HERE/expected-refusals.tsv"

for need in "$BIN" "$INST/olympics.index.spo" "$ORACLE" "$XFAIL"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/qlvr-queries.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

PASS=0; FAIL=0; REF=0; BAD=0
for rq in "$HERE"/queries/q*.rq; do
  name="$(basename "$rq" .rq)"
  srj="$ORACLE/$name.srj"
  issue="$(awk -F'\t' -v q="$name" '$1 == q { print $2 }' "$XFAIL")"
  "$BIN" query "$INST" --file "$rq" >"$TMP/$name.json" 2>"$TMP/$name.err"; rc=$?
  info="$(grep -o 'total [0-9]* ms; peak RSS (VmHWM): [0-9]* kB' "$TMP/$name.err" | head -1)"
  if [ "$rc" -eq 3 ]; then
    REF=$((REF + 1))
    why="$(grep -o 'refused: .*' "$TMP/$name.err" | head -1)"
    if [ -n "$issue" ]; then
      printf 'XFAIL   %-36s %s (%s)\n' "$name" "$why" "$issue"
    else
      BAD=$((BAD + 1)); printf 'REFUSED %-36s %s (not in expected-refusals.tsv)\n' "$name" "$why"
    fi
    continue
  fi
  if [ -n "$issue" ]; then
    BAD=$((BAD + 1)); printf 'STALE   %-36s listed in expected-refusals.tsv (%s) but answered (exit %s)\n' "$name" "$issue" "$rc"
  fi
  if [ "$rc" -ne 0 ]; then
    FAIL=$((FAIL + 1)); printf 'FAIL    %-36s exit %s: %s\n' "$name" "$rc" "$(tail -1 "$TMP/$name.err")"
    continue
  fi
  if [ ! -f "$srj" ]; then
    FAIL=$((FAIL + 1)); printf 'FAIL    %-36s no oracle answer %s\n' "$name" "$srj"; continue
  fi
  if res="$(python3 -I "$HERE/compare_query.py" "$srj" "$TMP/$name.json" "$rq")"; then
    PASS=$((PASS + 1)); printf 'ok      %-36s %s; %s\n' "$name" "$res" "$info"
  else
    FAIL=$((FAIL + 1)); printf 'FAIL    %-36s %s\n' "$name" "$(echo "$res" | head -6 | tr '\n' ' ')"
  fi
done
echo "qlvr queries: $PASS pass, $FAIL fail, $REF refused (out of $((PASS + FAIL + REF)))"
[ "$FAIL" -eq 0 ] && [ "$BAD" -eq 0 ]
