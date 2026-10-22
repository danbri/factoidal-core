#!/usr/bin/env bash
#
# tests/sbm11/filter_keys.sh — how the SBM11 id path decides a FILTER conjunct
# (https://github.com/danbri/factoidal/issues/948).
#
# `l4sbm11 query --explain` prints one line "FILTER conjuncts on ids: ..." that
# names, for each compiled conjunct, how it is evaluated (`FKind.explainName`
# in formal/lean4/L4Factoidal/Storage/Sbm11/IdQuery.lean): on ids, on key
# bytes, or by the reference evaluator on decoded terms.
#
#   control   a STRSTARTS conjunct (a query of this script) is decided on the
#             key ranks of the dictionary: the explain line is there and names
#             that path. This case shows that the check below can see a
#             conjunct that does not go to the reference evaluator.
#   typed     the shape of DBpedia d14 (tests/sbm11/gate/ids-sip-date-filter.rq,
#             `FILTER(?d < "2021-01-01"^^xsd:date)`) is an expected failure:
#             on main the conjunct goes to the reference evaluator, because the
#             key-byte comparison of typed literals was left out (it compared
#             lexical forms; `<`, `<=`, `>`, `>=` compare in the XSD value
#             space, Fn.Comparison.termCompare). The case "the typed-date FILTER
#             is decided on key bytes" fails today and names issue 948. The run
#             fails when it passes, so that the case is changed to an assertion
#             and the issue is closed. The answer is also compared with
#             `--reference` (a real assertion, compare_answers.py: the same solutions).
#
# Usage: tests/sbm11/filter_keys.sh. Environment: L4_BIN_DIR (the built binaries).
# Prints "filter keys: N pass, M fail, K expected-fail (out of T)"; exit 1 when
# any case fails.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
GATE="$HERE/gate/gate.nq"
ISSUE="${FILTER_KEYS_ISSUE:-https://github.com/danbri/factoidal/issues/948}"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$GATE" "$HERE/gate/ids-sip-date-filter.rq"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-fkeys.XXXXXX")"
trap '[ -n "${FILTER_KEYS_KEEP:-}" ] || rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <group> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-8s %-40s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-8s %-40s %s\n' "$1" "$2" "$4"; fi
}
xfail() { # xfail <group> <name> <issue-url> <expected-failure-holds:0|1> <detail>
  if [ "$4" = 0 ]; then XFAIL=$((XFAIL + 1)); printf 'XFAIL  %-8s %-40s (%s) %s\n' "$1" "$2" "$3" "$5"
  else FAIL=$((FAIL + 1)); printf 'XPASS  %-8s %-40s (%s) %s -- change this case to an assertion and close the issue\n' "$1" "$2" "$3" "$5"; fi
}
finish() {
  echo
  echo "filter keys: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
  [ "$FAIL" -eq 0 ]
  exit $?
}

G="$TMP/gate"
rc=0
"$BIN/l4sbm11-pack" "$GATE" "$G/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G" gen >"$TMP/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then record setup pack-activate 1 "exit $rc"; finish; fi

# explain <query file> <tag>: the id run with --explain; its FILTER line in $TMP/<tag>.kinds
explain() {
  local rq="$1" tag="$2" r=0
  timeout 120 "$BIN/l4sbm11" query "$G" --file "$rq" --base "file://$(realpath "$rq")" --explain \
    >"$TMP/$tag.out" 2>"$TMP/$tag.err" || r=$?
  grep 'plan: FILTER conjuncts on ids:' "$TMP/$tag.err" >"$TMP/$tag.kinds" || : >"$TMP/$tag.kinds"
  return "$r"
}

# control: STRSTARTS of a simple literal is decided on key bytes
cat >"$TMP/control.rq" <<'EOF'
PREFIX ex: <http://ex.org/>
SELECT ?s ?o WHERE { ?s ?p ?o FILTER(STRSTARTS(?o, "a")) }
EOF
if ! explain "$TMP/control.rq" control; then record control strstarts-on-key-bytes 1 "exit: $(tail -1 "$TMP/control.err" | cut -c1-100)"
elif [ ! -s "$TMP/control.kinds" ]; then record control strstarts-on-key-bytes 1 "no 'FILTER conjuncts on ids' line in --explain"
elif grep -q 'key bytes\|key ranks' "$TMP/control.kinds" && ! grep -q 'reference' "$TMP/control.kinds"; then
  record control strstarts-on-key-bytes 0 "$(sed 's/^plan: //' "$TMP/control.kinds" | cut -c1-100)"
else record control strstarts-on-key-bytes 1 "$(sed 's/^plan: //' "$TMP/control.kinds" | cut -c1-100)"; fi

# typed: the d14 shape (issue 948)
rq="$HERE/gate/ids-sip-date-filter.rq"
r2=0
timeout 120 "$BIN/l4sbm11" query "$G" --file "$rq" --base "file://$(realpath "$rq")" --reference \
  >"$TMP/typed.ref.out" 2>"$TMP/typed.ref.err" || r2=$?
if ! explain "$rq" typed || [ "$r2" -ne 0 ]; then record typed d14-shape-answer 1 "exit (ids or --reference $r2)"
else
  cmpl="$(python3 "$HERE/compare_answers.py" "$TMP/typed.out" "$TMP/typed.ref.out" 0 2>&1 | head -1)"
  case "$cmpl" in
    equal*) record typed d14-shape-answer 0 "same solutions as --reference: $cmpl" ;;
    *) record typed d14-shape-answer 1 "against --reference: $cmpl" ;;
  esac
  if [ ! -s "$TMP/typed.kinds" ]; then record typed typed-date-filter-on-key-bytes 1 "no 'FILTER conjuncts on ids' line in --explain"
  elif grep -q 'key bytes' "$TMP/typed.kinds" && ! grep -q 'reference' "$TMP/typed.kinds"; then
    xfail typed xfail-typed-date-filter-on-key-bytes "$ISSUE" 1 "$(sed 's/^plan: //' "$TMP/typed.kinds" | cut -c1-90)"
  else
    xfail typed xfail-typed-date-filter-on-key-bytes "$ISSUE" 0 "$(sed 's/^plan: //' "$TMP/typed.kinds" | cut -c1-90)"
  fi
fi
finish
