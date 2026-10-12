#!/usr/bin/env bash
#
# tests/sbm11/run.sh — SBM11 stage 4, SPARQL over a generation
# (https://github.com/danbri/factoidal/issues/790; tracking
# https://github.com/danbri/factoidal/issues/787). Record:
# docs/designissues/2026-10-12-sbm11-stage4.md.
#
#   (a) oracle   q01 to q21 (tests/qlvr/queries) through `l4sbm11 query` on
#                the olympics generation against the QLever oracle
#                (QLVR_WORK/oracle/*.srj), as multisets by value, with the
#                differences of the comparison record section 3.3 handled as
#                that section says (tests/sbm11/compare_oracle.py). Prints
#                "N pass, M fail (out of 21)".
#   (b) render   every oracle query answered twice, by the key printer (the
#                default) and with --reference-render (every term through
#                jsonOfTerm); the outputs must be byte-identical.
#   (c) ids vs reference   oracle queries q03 to q18 answered on ids and with
#                --reference (the reference evaluator over the quads the
#                planner guard selects); equal as multisets
#                (tests/sbm11/compare_answers.py).
#   (d) gate     tests/sbm11/gate/gate.nq (default and named graphs, integer
#                types, a non-canonical integer, language tags, blank nodes)
#                packed and activated; each tests/sbm11/gate/*.rq answered by
#                `l4sbm11 query` and by the in-memory reference engine
#                (`l4factoidal query gate.nq`), equal as multisets. A query
#                named ids-* must run on ids (path=ids); one named ref-* must
#                take the reference fallback (path=reference): EXISTS, NOT
#                EXISTS, MINUS, OPTIONAL with FILTER, sub-SELECT and the other
#                forms only the reference semantics decide (CLAUDE.md
#                anti-pattern 34).
#   (e) checks   `l4sbm11 prm-check` (the byte-array PRM1 decoder against the
#                list decoder of the round-trip theorem) and `l4sbm11
#                frame-check` (the word decoder against decodeColumnAt) on
#                every PRM1 file and every frame of the generation.
#
# Usage: tests/sbm11/run.sh [GEN]   (default /home/user/qlvr-work/sbm11/s3/wfull,
# an activated olympics generation; tests/sbm11/stage3_check.sh makes one).
# Exit 0 only when every check passes; 2 when an input is missing.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
GEN="${1:-$WORK/sbm11/s3/wfull}"
ORACLE="$WORK/oracle"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4factoidal" "$GEN" "$ORACLE"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-run.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0
record() { # record <part> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok   %-8s %-34s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL %-8s %-34s %s\n' "$1" "$2" "$4"; fi
}

echo "=== (a) oracle queries"
OP=0; OF=0
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  rc=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" >"$TMP/$n.srj" 2>"$TMP/$n.err" || rc=$?
  if [ "$rc" -ne 0 ]; then
    record oracle "$n" 1 "exit $rc: $(tail -1 "$TMP/$n.err")"; OF=$((OF + 1)); continue
  fi
  v="$(python3 -I "$HERE/compare_oracle.py" "$ORACLE/$n.srj" "$TMP/$n.srj" "$rq" "$n" 2>&1)"; c=$?
  p="$(grep -o 'path=[a-z]*' "$TMP/$n.err")"
  record oracle "$n" "$c" "$p; $(printf '%s' "$v" | head -1)"
  if [ "$c" = 0 ]; then OP=$((OP + 1)); else OF=$((OF + 1)); fi
done
echo "oracle: $OP pass, $OF fail (out of $((OP + OF)))"

echo "=== (b) key printer against jsonOfTerm"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --reference-render >"$TMP/$n.ref" 2>/dev/null
  if cmp -s "$TMP/$n.srj" "$TMP/$n.ref"; then record render "$n" 0 "byte-identical ($(wc -c <"$TMP/$n.srj") bytes)"
  else record render "$n" 1 "outputs differ"; fi
done

echo "=== (c) the id path against the reference fallback"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  case $n in q0[3-9]*|q1[0-8]*) ;; *) continue ;; esac
  rc=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --reference >"$TMP/$n.fb" 2>"$TMP/$n.fberr" || rc=$?
  if [ "$rc" -ne 0 ]; then record ids-ref "$n" 1 "fallback exit $rc"; continue; fi
  v="$(python3 -I "$HERE/compare_answers.py" "$TMP/$n.srj" "$TMP/$n.fb" 0)"
  case "$v" in equal*) record ids-ref "$n" 0 "$v; $(grep -o 'quads=[0-9]*' "$TMP/$n.fberr")" ;; *) record ids-ref "$n" 1 "$v" ;; esac
done

echo "=== (d) gate fixture: id path and reference fallback against l4factoidal"
G="$TMP/gate"
rc=0
"$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$G/gen" --workers 1 >"$TMP/gpack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G" gen >"$TMP/gact.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  record gate pack-activate 1 "exit $rc: $(tail -1 "$TMP/gpack.log" "$TMP/gact.log" 2>/dev/null | tr '\n' ' ')"
else
  for rq in "$HERE"/gate/*.rq; do
    n="$(basename "$rq" .rq)"
    qb="file://$(realpath "$rq")"
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$G" --file "$rq" --base "$qb" >"$TMP/g-$n.got" 2>"$TMP/g-$n.err" || rc=$?
    if [ "$rc" -ne 0 ]; then record gate "$n" 1 "exit $rc: $(tail -1 "$TMP/g-$n.err")"; continue; fi
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$HERE/gate/gate.nq" --format nquads --query "$rq" \
      >"$TMP/g-$n.want" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$TMP/g-$n.got" "$TMP/g-$n.want" "$rrc")"
    p="$(grep -o 'path=[a-z]*' "$TMP/g-$n.err")"
    want_path=path=ids; case $n in ref-*) want_path=path=reference ;; esac
    if [ "$p" != "$want_path" ]; then record gate "$n" 1 "$p, expected $want_path"
    else case "$v" in equal*) record gate "$n" 0 "$p; $v" ;; *) record gate "$n" 1 "$p; $v" ;; esac
    fi
  done
fi

echo "=== (e) decoder checks on every PRM1 file and frame"
if out="$("$BIN/l4sbm11" prm-check "$GEN" 2>&1)"; then record checks prm-check 0 "$(printf '%s' "$out" | tr '\n' ' ' | head -c 150)"
else record checks prm-check 1 "$out"; fi
if out="$("$BIN/l4sbm11" frame-check "$GEN" 2>&1)"; then record checks frame-check 0 "$out"
else record checks frame-check 1 "$out"; fi

echo
echo "sbm11 stage 4: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
