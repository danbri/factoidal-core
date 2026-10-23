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
#             `FILTER(?d < "2021-01-01"^^xsd:date)`) is decided on the key bytes
#             (`FKind.dateCmp`, DateKey.dateCmpKey?, issue 948: the XSD
#             value-space order for keys `YYYY-MM-DD`, theorem
#             DateKeyTheorems.dateCmpKey_termCompare), and its answer equals
#             `--reference` (compare_answers.py: the same solutions).
#   admit     a fixture of this script with dates inside and outside the
#             admitted set (timezones, a negative year, a five-digit year,
#             year 0000, a day that does not exist, an ill-typed form, a
#             dateTime, another datatype). For admitted constants the conjunct
#             runs on key bytes; for a constant outside the set (a timezone, a
#             negative or five-digit year) and for `=` it goes to the reference
#             evaluator. Every answer equals `--reference`.
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
    record typed typed-date-filter-on-key-bytes 0 "$(sed 's/^plan: //' "$TMP/typed.kinds" | cut -c1-90)"
  else
    record typed typed-date-filter-on-key-bytes 1 "$(sed 's/^plan: //' "$TMP/typed.kinds" | cut -c1-90)"
  fi
fi

# admit: dates inside and outside the admitted set of DateKey.dateParts?
D="$TMP/dates"
XD='<http://www.w3.org/2001/XMLSchema#date>'
{
  i=0
  for lex in 2020-01-01 1800-01-01 1799-12-31 2000-02-29 0001-01-01 1800-01-01Z 1799-12-31+14:00 \
      1800-01-01-14:00 -0044-03-15 12020-01-01 0000-01-01 2001-02-29 abc 1800-1-1; do
    i=$((i + 1))
    printf '<http://ex.org/d%s> <http://ex.org/when> "%s"^^%s .\n' "$i" "$lex" "$XD"
  done
  printf '<http://ex.org/t1> <http://ex.org/when> "1799-01-01T00:00:00"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n'
  printf '<http://ex.org/t2> <http://ex.org/when> "1799-06-01"^^<http://ex.org/dt> .\n'
  printf '<http://ex.org/t3> <http://ex.org/when> "1799-06-01" .\n'
} >"$TMP/dates.nq"
rc=0
"$BIN/l4sbm11-pack" "$TMP/dates.nq" "$D/gen" --workers 1 >"$TMP/dpack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$D" gen >"$TMP/dact.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then record admit pack-activate 1 "exit $rc"; finish; fi

# admit_case <name> <filter> <expected path: keys|reference>
admit_case() {
  local name="$1" filt="$2" want="$3" rq="$TMP/a-$1.rq" r1=0 r2=0
  printf 'PREFIX ex: <http://ex.org/>\nPREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\nSELECT ?s ?d WHERE { ?s ex:when ?d FILTER(%s) }\n' "$filt" >"$rq"
  timeout 120 "$BIN/l4sbm11" query "$D" --file "$rq" --explain >"$TMP/a-$name.out" 2>"$TMP/a-$name.err" || r1=$?
  timeout 120 "$BIN/l4sbm11" query "$D" --file "$rq" --reference >"$TMP/a-$name.ref" 2>"$TMP/a-$name.referr" || r2=$?
  if [ "$r1" -ne 0 ] || [ "$r2" -ne 0 ]; then record admit "$name" 1 "exit (ids $r1, --reference $r2)"; return; fi
  local kinds cmpl
  kinds="$(grep 'plan: FILTER conjuncts on ids:' "$TMP/a-$name.err" | sed 's/^plan: //')"
  cmpl="$(python3 "$HERE/compare_answers.py" "$TMP/a-$name.out" "$TMP/a-$name.ref" 0 2>&1 | head -1)"
  case "$cmpl" in equal*) ;; *) record admit "$name" 1 "against --reference: $cmpl"; return ;; esac
  case "$want" in
    keys) if printf '%s' "$kinds" | grep -q 'key bytes' && ! printf '%s' "$kinds" | grep -q 'reference'; then
            record admit "$name" 0 "$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$TMP/a-$name.out") rows; key bytes; $cmpl"
          else record admit "$name" 1 "expected key bytes: $kinds"; fi ;;
    reference) if printf '%s' "$kinds" | grep -q 'reference'; then
            record admit "$name" 0 "$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$TMP/a-$name.out") rows; reference; $cmpl"
          else record admit "$name" 1 "expected the reference evaluator: $kinds"; fi ;;
  esac
}
admit_case lt-admitted '?d < "1800-01-01"^^xsd:date' keys
admit_case gt-admitted '?d > "1800-01-01"^^xsd:date' keys
admit_case le-leapday '?d <= "2000-02-29"^^xsd:date' keys
admit_case ge-swap '"1800-01-01"^^xsd:date >= ?d' keys
admit_case lt-swap-first-year '"0001-01-01"^^xsd:date < ?d' keys
admit_case const-timezone '?d < "1800-01-01Z"^^xsd:date' reference
admit_case const-timezone-plus '?d >= "1799-12-31+14:00"^^xsd:date' reference
admit_case const-negative-year '?d > "-0044-03-15"^^xsd:date' reference
admit_case const-five-digit-year '?d < "12020-01-01"^^xsd:date' reference
admit_case const-invalid-day '?d < "2001-02-29"^^xsd:date' reference
admit_case const-datetime '?d < "1800-01-01T00:00:00"^^xsd:dateTime' reference
admit_case eq-not-relational '?d = "1800-01-01"^^xsd:date' reference
finish
