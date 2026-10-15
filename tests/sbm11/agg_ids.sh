#!/usr/bin/env bash
#
# tests/sbm11/agg_ids.sh — grouped aggregates on term ids
# (https://github.com/danbri/factoidal/issues/825; record
# docs/designissues/2026-10-12-sbm11-stage4.md section 16).
#
# The gate queries (tests/sbm11/run.sh part (d)) compare each answer with the
# reference engine and check `path=ids`; both the aggregation on ids and the
# decoded rows report `path=ids`, so the gate cannot tell which one ran. This
# script checks that.
#
#   fast      every gate query whose SELECT clause is in the plan of
#             `AggStream.aggPlan?` (GROUP BY variables or none; variables and
#             non-DISTINCT COUNT, SUM, MIN, MAX and AVG of a variable) says
#             "aggregated on ids" in `--explain`, and its answer is
#             byte-identical to the answer of `--no-agg-ids`, which decodes the
#             rows and runs `selectPost` (the two outputs come from the same
#             tail, so equal bytes mean equal rows in equal order);
#   decoded   a table the plan does not admit (a group column that holds a
#             dictionary literal or an unbound value) falls back to the decoded
#             rows and still answers as `--no-agg-ids` does;
#   gaps      the grouped SELECTs that still run on the decoded rows because the
#             plan does not take them (HAVING, DISTINCT aggregates,
#             GROUP_CONCAT, an expression in GROUP BY, a dictionary literal or
#             an unbound variable as the key) are expected failures: the case
#             "takes the aggregation on ids" fails today and names the open
#             issue https://github.com/danbri/factoidal/issues/861;
#             so is the representative row of a group, which holds every
#             variable of the WHERE clause where the query reads one: the case
#             "the representative rows hold no more values than groups" fails
#             today for a query that reads the group variable only; and MIN and
#             MAX over IRIs, which decode every distinct IRI where the order of
#             the ids (the byte order of the dictionary keys) would find the
#             first and the last: the case "at most four ids decoded for each
#             group" fails today on 40 IRIs in two groups.
#             The run fails when one of them passes, so that the case is
#             changed to an assertion and the issue is closed.
#   dbpedia   when the DBpedia slice generation exists (SBM11_DBPEDIA, default
#             /home/user/bench-data/sbm11/dbpedia): d19 and the queries of
#             tests/sbm11/agg-dbpedia (630,000 date literals, 730 to 180,000
#             groups, MIN and MAX of IRIs, two group keys) on ids and with
#             `--no-agg-ids`, byte-identical; and one expected failure,
#             "d19 warm time at most 300 ms" (about 500 ms today), which names
#             https://github.com/danbri/factoidal/issues/862.
#
# Usage: tests/sbm11/agg_ids.sh. Environment: L4_BIN_DIR (the built binaries).
# Prints "agg ids: N pass, M fail, K expected-fail (out of T)"; exit 1 when any
# case fails.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
GATE="$HERE/gate/gate.nq"
DBP="${SBM11_DBPEDIA:-/home/user/bench-data/sbm11/dbpedia}"
ISSUE="${AGG_IDS_ISSUE:-https://github.com/danbri/factoidal/issues/861}"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$GATE"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-agg.XXXXXX")"
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

G="$TMP/gate"
rc=0
"$BIN/l4sbm11-pack" "$GATE" "$G/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G" gen >"$TMP/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  record setup pack-activate 1 "exit $rc: $(tail -1 "$TMP/pack.log" "$TMP/act.log" 2>/dev/null | tr '\n' ' ')"
  echo "agg ids: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
  exit 1
fi

# run_both <gen> <query file> <tag>: the default run and the --no-agg-ids run;
# the post line of each in $TMP/<tag>.{a,b}.post, the outputs in $TMP/<tag>.{a,b}.out
run_both() {
  local gen="$1" rq="$2" tag="$3" qb="file://$(realpath "$2")" r1=0 r2=0
  timeout 600 "$BIN/l4sbm11" query "$gen" --file "$rq" --base "$qb" --explain >"$TMP/$tag.a.out" 2>"$TMP/$tag.a.err" || r1=$?
  timeout 600 "$BIN/l4sbm11" query "$gen" --file "$rq" --base "$qb" --explain --no-agg-ids >"$TMP/$tag.b.out" 2>"$TMP/$tag.b.err" || r2=$?
  grep 'plan: post' "$TMP/$tag.a.err" >"$TMP/$tag.a.post" || : >"$TMP/$tag.a.post"
  grep 'plan: post' "$TMP/$tag.b.err" >"$TMP/$tag.b.post" || : >"$TMP/$tag.b.post"
  RUN_RC="$r1/$r2"
  [ "$r1" -eq 0 ] && [ "$r2" -eq 0 ]
}

FAST="ids-agg-absent ids-agg-dates ids-agg-distinct ids-agg-empty-group ids-agg-graph ids-agg-group-bool \
ids-agg-group-int ids-agg-group-iri ids-agg-group-iri-nosort ids-agg-kinds ids-agg-labels ids-agg-mixed \
ids-agg-no-rows ids-agg-optional ids-agg-order-extra ids-agg-order-limit ids-agg-promotion ids-agg-same-twice \
ids-agg-two-keys"
for n in $FAST; do
  if ! run_both "$G" "$HERE/gate/$n.rq" "$n"; then record fast "$n" 1 "exit $RUN_RC: $(tail -1 "$TMP/$n.a.err" | cut -c1-100)"; continue; fi
  if ! grep -q 'aggregated on ids' "$TMP/$n.a.post"; then record fast "$n" 1 "did not aggregate on ids: $(cut -c1-120 "$TMP/$n.a.post")"
  elif grep -q 'aggregated on ids' "$TMP/$n.b.post"; then record fast "$n" 1 "--no-agg-ids still aggregated on ids"
  elif ! cmp -s "$TMP/$n.a.out" "$TMP/$n.b.out"; then record fast "$n" 1 "the answers differ in bytes"
  else record fast "$n" 0 "$(sed 's/^plan: post: //' "$TMP/$n.a.post" | cut -c1-110)"; fi
done

# a table the plan does not admit: a dictionary literal or an unbound value in a group column
DECODED="ids-agg-literal-key ids-agg-unbound-key"
for n in $DECODED; do
  if ! run_both "$G" "$HERE/gate/$n.rq" "$n"; then record decoded "$n" 1 "exit $RUN_RC"; continue; fi
  if grep -q 'aggregated on ids' "$TMP/$n.a.post"; then record decoded "$n" 1 "aggregated on ids over a column it does not admit"
  elif ! cmp -s "$TMP/$n.a.out" "$TMP/$n.b.out"; then record decoded "$n" 1 "the answers differ in bytes"
  else record decoded "$n" 0 "decoded rows: $(sed 's/^plan: post: //' "$TMP/$n.a.post" | cut -c1-90)"; fi
done

# the grouped SELECTs the plan does not take (the shortfalls of the issue)
GAPS="ids-agg-avg-having:HAVING ids-agg-count-distinct:COUNT(DISTINCT) ids-agg-group-concat:GROUP_CONCAT \
ids-agg-group-expr:GROUP-BY-expression ids-agg-literal-key:literal-key ids-agg-unbound-key:unbound-key"
for g in $GAPS; do
  n="${g%%:*}"; what="${g##*:}"
  if ! run_both "$G" "$HERE/gate/$n.rq" "gap-$n"; then record gaps "$n" 1 "exit $RUN_RC"; continue; fi
  if grep -q 'aggregated on ids' "$TMP/gap-$n.a.post"; then
    xfail gaps "xfail-$what" "$ISSUE" 1 "the query aggregates on ids: $(sed 's/^plan: post: //' "$TMP/gap-$n.a.post" | cut -c1-80)"
  else
    xfail gaps "xfail-$what" "$ISSUE" 0 "runs on the decoded rows: $(sed 's/^plan: post: //' "$TMP/gap-$n.a.post" | cut -c1-70)"
  fi
done

# the representative row of a group holds every variable of the WHERE clause (three
# here: ?x, ?g, ?v); the query reads one of them (?g)
n=ids-agg-group-iri-nosort
if run_both "$G" "$HERE/gate/$n.rq" "rep-$n"; then
  groups="$(sed -n 's/.* into \([0-9]*\) groups.*/\1/p' "$TMP/rep-$n.a.post")"
  repv="$(sed -n 's/.*, \([0-9]*\) values in the representative rows.*/\1/p' "$TMP/rep-$n.a.post")"
  if [ -z "$groups" ] || [ -z "$repv" ]; then record gaps "rep-$n" 1 "no counts in: $(cut -c1-120 "$TMP/rep-$n.a.post")"
  elif [ "$repv" -le "$groups" ]; then
    xfail gaps xfail-representative-values "$ISSUE" 1 "$repv values in the representative rows of $groups groups"
  else
    xfail gaps xfail-representative-values "$ISSUE" 0 "$repv values in the representative rows of $groups groups; the query reads one value per group"
  fi
else record gaps "rep-$n" 1 "exit $RUN_RC"; fi

# MIN and MAX over IRIs: 40 IRIs in two groups. The order of IRI ids is the byte order of the
# dictionary keys, which is the order SPARQL gives IRIs, so the first and the last of a group
# could be found on ids and decoded alone; today every distinct IRI is decoded.
MM="$TMP/minmax"; mkdir -p "$MM"
for i in $(seq 1 40); do echo "<http://ex.org/m$i> <http://ex.org/in> <http://ex.org/K$((i % 2))> ."; done >"$MM/minmax.nq"
echo 'PREFIX ex: <http://ex.org/> SELECT ?k (MIN(?x) AS ?lo) (MAX(?x) AS ?hi) WHERE { ?x ex:in ?k } GROUP BY ?k' >"$MM/q.rq"
rc=0
"$BIN/l4sbm11-pack" "$MM/minmax.nq" "$MM/col/gen" --workers 1 >"$TMP/mm-pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$MM/col" gen >"$TMP/mm-act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then record gaps minmax-iri 1 "pack or activate failed (exit $rc)"
elif ! run_both "$MM/col" "$MM/q.rq" "mm"; then record gaps minmax-iri 1 "exit $RUN_RC"
elif ! cmp -s "$TMP/mm.a.out" "$TMP/mm.b.out"; then record gaps minmax-iri 1 "the answers differ in bytes"
else
  groups="$(sed -n 's/.* into \([0-9]*\) groups.*/\1/p' "$TMP/mm.a.post")"
  dec="$(sed -n 's/.*(\([0-9]*\) distinct ids decoded.*/\1/p' "$TMP/mm.a.post")"
  if [ -z "$groups" ] || [ -z "$dec" ]; then record gaps minmax-iri 1 "no counts in: $(cut -c1-120 "$TMP/mm.a.post")"
  elif [ "$dec" -le $((4 * groups)) ]; then
    xfail gaps xfail-minmax-iri-decode "$ISSUE" 1 "$dec ids decoded for $groups groups"
  else
    xfail gaps xfail-minmax-iri-decode "$ISSUE" 0 "$dec ids decoded for $groups groups (40 IRIs); the first and the last of each group would do"
  fi
fi

# DBpedia d19 (issue 825): when the slice generation is there
if [ -d "$DBP" ] && [ -f "$ROOT/tools/bench/three-engines/queries/dbpedia/d19-group-aggregates.rq" ]; then
  q="$ROOT/tools/bench/three-engines/queries/dbpedia/d19-group-aggregates.rq"
  r1=0; r2=0
  timeout 600 "$BIN/l4sbm11" query "$DBP" --file "$q" --verify none --explain >"$TMP/d19.a.out" 2>"$TMP/d19.a.err" || r1=$?
  timeout 600 "$BIN/l4sbm11" query "$DBP" --file "$q" --verify none --explain --no-agg-ids >"$TMP/d19.b.out" 2>"$TMP/d19.b.err" || r2=$?
  if [ "$r1" -ne 0 ] || [ "$r2" -ne 0 ]; then record dbpedia d19 1 "exit $r1/$r2"
  elif ! grep -q 'aggregated on ids' "$TMP/d19.a.err"; then record dbpedia d19 1 "did not aggregate on ids"
  elif ! cmp -s "$TMP/d19.a.out" "$TMP/d19.b.out"; then record dbpedia d19 1 "the answers differ in bytes"
  else record dbpedia d19 0 "$(grep -o 'aggregated on ids into [0-9]* groups' "$TMP/d19.a.err"); byte-identical to --no-agg-ids ($(wc -c <"$TMP/d19.a.out") bytes)"; fi
  # https://github.com/danbri/factoidal/issues/862: d19 warm time (the execution median of 5
  # runs in one process) at most 300 ms; about 500 ms today, so the case fails as expected
  ISSUE862="${AGG_IDS_ISSUE_862:-https://github.com/danbri/factoidal/issues/862}"
  warm="$(timeout 600 "$BIN/l4sbm11" query "$DBP" --file "$ROOT/tools/bench/three-engines/queries/dbpedia/d19-group-aggregates.rq" --verify none --repeat 5 2>&1 >/dev/null | sed -n 's/.*execution ms median \([0-9]*\)\..*/\1/p')"
  if [ -z "$warm" ]; then record dbpedia d19-warm 1 "no warm time in the output"
  elif [ "$warm" -le 300 ]; then xfail dbpedia xfail-d19-warm-300ms "$ISSUE862" 1 "warm $warm ms"
  else xfail dbpedia xfail-d19-warm-300ms "$ISSUE862" 0 "warm $warm ms against 300 ms"; fi
  for q in "$HERE"/agg-dbpedia/*.rq; do
    n="$(basename "$q" .rq)"
    r1=0; r2=0
    timeout 600 "$BIN/l4sbm11" query "$DBP" --file "$q" --verify none --explain >"$TMP/db-$n.a.out" 2>"$TMP/db-$n.a.err" || r1=$?
    timeout 600 "$BIN/l4sbm11" query "$DBP" --file "$q" --verify none --no-agg-ids >"$TMP/db-$n.b.out" 2>"$TMP/db-$n.b.err" || r2=$?
    if [ "$r1" -ne 0 ] || [ "$r2" -ne 0 ]; then record dbpedia "$n" 1 "exit $r1/$r2"
    elif ! grep -q 'aggregated on ids' "$TMP/db-$n.a.err"; then record dbpedia "$n" 1 "did not aggregate on ids"
    elif ! cmp -s "$TMP/db-$n.a.out" "$TMP/db-$n.b.out"; then record dbpedia "$n" 1 "the answers differ in bytes"
    else record dbpedia "$n" 0 "$(grep -o 'aggregated on ids into [0-9]* groups' "$TMP/db-$n.a.err"); byte-identical to --no-agg-ids ($(wc -c <"$TMP/db-$n.a.out") bytes)"; fi
  done
else
  echo "skip   dbpedia  d19 and agg-dbpedia            (no generation at $DBP)"
fi

echo
echo "agg ids: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
