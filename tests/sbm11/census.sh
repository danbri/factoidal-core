#!/usr/bin/env bash
#
# tests/sbm11/census.sh — the W3C persisted census on SBM11 (stage 4,
# https://github.com/danbri/factoidal/issues/790; the IBK3/IBK4 form is
# tools/w3c-persisted-census.sh). Record:
# docs/designissues/2026-10-12-sbm11-stage4.md section 5.
#
# NOT a W3C conformance result: each answer is compared with the REFERENCE
# Lean engine's answer over the SAME input file (`l4factoidal query`), not
# with the suite's expected result.
#
# For every mf:QueryEvaluationTest of the SPARQL 1.0 and 1.1 suites with
# qt:query and qt:data and/or qt:graphData:
#   1. the data file and every graph-data file become one N-Quads input
#      (`l4factoidal parse --out nquads`; a graph-data file's statements get
#      the file's IRI as graph name, the rule of Harness/Manifest.lean);
#   2. `l4sbm11-pack` packs it, `l4sbm11 activate` activates it;
#   3. `l4sbm11 query` answers the query (the id path or the reference
#      fallback; stderr names which), with the query file's IRI as base;
#   4. `l4factoidal query` answers it over the N-Quads input.
# SELECT answers are compared as multisets of solutions
# (tests/sbm11/compare_answers.py: blank-node labels ignored, language tags
# compared in lower case, since the packer folds them, RDF 1.1 Concepts 3.3);
# ASK by the boolean; CONSTRUCT and DESCRIBE as multisets of N-Triples lines,
# blank node labels and language-tag case masked (until issue 823 by the number
# of triples only).
#
# Prints executed / matched / differed / not comparable, per path, and the
# refusals at pack and at query. Usage: tests/sbm11/census.sh [SUITE_DIR...]
# SBM11_BIN: the `l4sbm11` to run (default: the one this tree builds), to
# compare the census of two builds. SBM11_SIP: when set, the `--sip` mode
# (auto, the CLI default; always: candidates into every join scan the shape
# allows; off; issue 809), with `--explain`, and the summary counts the
# tests in which a scan with candidates ran; unset, no `--sip` is passed (a
# build before issue 809 has no such option). `--explain` is always passed: the
# summary counts the tests whose grouped aggregates ran on ids (issue 825). SBM11_THREADS: the
# `--threads` count (1).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
S11="${SBM11_BIN:-$BIN/l4sbm11}"
# FACTOIDAL_TESTING_ROOT: the directory that holds the W3C fixtures (default
# third_party/testing of this tree). A checkout that has no submodules (a git
# worktree) points it at the checkout that has them.
TESTING="${FACTOIDAL_TESTING_ROOT:-$ROOT/third_party/testing}"
suites=("$@")
if [ ${#suites[@]} -eq 0 ]; then
  suites=("$TESTING/w3c/sparql/sparql10" "$TESTING/w3c/sparql/sparql11")
fi
mkdir -p "$ROOT/tmp"
RUN="$(mktemp -d "$ROOT/tmp/sbm11-census.XXXXXX")"
trap 'rm -rf "$RUN"' EXIT
TSV="$RUN/census.tsv"; : >"$TSV"

extract='PREFIX mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#>
PREFIX qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#>
SELECT ?t ?query ?data ?g WHERE {
  ?t a mf:QueryEvaluationTest ; mf:action ?a .
  ?a qt:query ?query .
  OPTIONAL { ?a qt:data ?data }
  OPTIONAL { ?a qt:graphData ?g }
  FILTER (BOUND(?data) || BOUND(?g))
}'

format_of() {
  case $1 in
    *.nt) echo ntriples ;;
    *.nq) echo nquads ;;
    *.trig) echo trig ;;
    *.rdf) echo rdfxml ;;
    *) echo turtle ;;
  esac
}

rows="$RUN/rows.tsv"; : >"$rows"
for suite in "${suites[@]}"; do
  while IFS= read -r manifest; do
    dir=$(dirname "$manifest")
    "$BIN/l4factoidal" query "$manifest" --base "file://$dir/" --table \
      --query-string "$extract" 2>/dev/null | tail -n +2 >>"$rows" || true
  done < <(find "$suite" -name manifest.ttl | sort)
done

declare -A tq td tg
order=()
while IFS=$'\t' read -r t q d g; do
  [ -z "$t" ] && continue
  if [ -z "${tq[$t]:-}" ]; then order+=("$t"); fi
  tq[$t]=$q
  [ -n "$d" ] && td[$t]=$d
  [ -n "$g" ] && case "${tg[$t]:-}" in *"$g"*) ;; *) tg[$t]="${tg[$t]:-}${g}"$'\n' ;; esac
done <"$rows"

eligible=0; missing=0; rpack=0; rquery=0; executed=0; matched=0; differed=0; uncompared=0
ids_exec=0; ids_match=0; ref_exec=0; ref_match=0; sip_tests=0; agg_tests=0
mg_q=0; mg_eq=0; mg_diff=0; mg_ref=0; mg_fail=0
MIS="$RUN/mismatches.txt"; : >"$MIS"
n=0
for t in "${order[@]}"; do
  qfile=${tq[$t]#file://}
  dfile=${td[$t]:-}; dfile=${dfile#file://}
  ok=1
  [ -f "$qfile" ] || ok=0
  [ -n "$dfile" ] && [ ! -f "$dfile" ] && ok=0
  while IFS= read -r g; do [ -z "$g" ] && continue; [ -f "${g#file://}" ] || ok=0; done <<<"${tg[$t]:-}"
  if [ "$ok" -ne 1 ]; then missing=$((missing + 1)); continue; fi
  eligible=$((eligible + 1)); n=$((n + 1))
  st="$RUN/s$n"; mkdir -p "$st"
  input="$st/input.nq"; : >"$input"
  conv=1
  if [ -n "$dfile" ]; then
    "$BIN/l4factoidal" parse "$dfile" --format "$(format_of "$dfile")" --out nquads \
      --base "file://$dfile" >>"$input" 2>/dev/null || conv=0
  fi
  while IFS= read -r g; do
    [ -z "$g" ] && continue
    gf=${g#file://}
    "$BIN/l4factoidal" parse "$gf" --format "$(format_of "$gf")" --out nquads --base "file://$gf" 2>/dev/null \
      | sed -e '/^[[:space:]]*$/d' -e "s| \.\$| <$g> .|" >>"$input" || conv=0
  done <<<"${tg[$t]:-}"
  if [ "$conv" -ne 1 ]; then
    rpack=$((rpack + 1)); printf '%s\trefused-convert\n' "$t" >>"$TSV"; rm -rf "$st"; continue
  fi
  rc=0
  timeout 120 "$BIN/l4sbm11-pack" "$input" "$st/gen" --workers 1 >"$st/pack.log" 2>&1 || rc=$?
  if [ "$rc" -eq 0 ]; then
    timeout 120 "$S11" activate "$st" gen >"$st/act.log" 2>&1 || rc=$?
  fi
  if [ "$rc" -ne 0 ]; then
    rpack=$((rpack + 1)); printf '%s\trefused-pack\t%s\n' "$t" "$(tail -1 "$st/pack.log" "$st/act.log" 2>/dev/null | tr '\n' ' ' | head -c 200)" >>"$TSV"
    rm -rf "$st"; continue
  fi
  qbase="file://$(realpath "$qfile")"
  rc=0
  timeout 120 "$S11" query "$st" --file "$qfile" --base "$qbase" --threads "${SBM11_THREADS:-1}" --explain ${SBM11_SIP:+--sip "$SBM11_SIP"} >"$st/got" 2>"$st/got.err" || rc=$?
  if [ "$rc" -ne 0 ]; then
    rquery=$((rquery + 1)); printf '%s\trefused-query\t%s\n' "$t" "$(tail -1 "$st/got.err" | head -c 200)" >>"$TSV"
    rm -rf "$st"; continue
  fi
  executed=$((executed + 1))
  path=ids; grep -q 'path=reference' "$st/got.err" && path=reference
  # the fallback's reason (`path=reference reason="..."`), for the histogram
  # of shapes the id path does not run (issue 775)
  reason=""; [ $path = reference ] && reason="$(grep -o 'reason="[^"]*"' "$st/got.err" | head -1 | sed 's/^reason="//; s/"$//')"
  if [ $path = ids ]; then ids_exec=$((ids_exec + 1)); else ref_exec=$((ref_exec + 1)); fi
  grep -q 'sideways' "$st/got.err" && sip_tests=$((sip_tests + 1))
  # a grouped SELECT whose aggregates ran on ids (issue 825)
  grep -q 'aggregated on ids' "$st/got.err" && agg_tests=$((agg_tests + 1))
  if [ -n "${SBM11_MEMGEN:-}" ]; then
    mrc=0
    timeout 120 "$S11" memgen-check "$st" --base "$qbase" "$qfile" >"$st/mg" 2>&1 || mrc=$?
    ml="$(grep '^memgen-check: [0-9]* queries' "$st/mg" | tail -1)"
    case "$ml" in
      *"1 queries, 1 equal, 0 differ"*"check = true)") mg_q=$((mg_q + 1)); mg_eq=$((mg_eq + 1)) ;;
      *"0 queries, 0 equal, 0 differ (1 on the reference path"*"check = true)") mg_ref=$((mg_ref + 1)) ;;
      *"1 queries, 0 equal, 1 differ"*) mg_q=$((mg_q + 1)); mg_diff=$((mg_diff + 1))
        printf '%s (memgen-check): %s\n' "${t##*/}" "$(grep '^DIFFER' "$st/mg" | head -1)" >>"$MIS" ;;
      *) mg_fail=$((mg_fail + 1))
        printf '%s (memgen-check): exit %s: %s\n' "${t##*/}" "$mrc" "$(tail -1 "$st/mg")" >>"$MIS" ;;
    esac
  fi
  rrc=0
  timeout 120 "$BIN/l4factoidal" query "$input" --format nquads --base "file://$input" --query "$qfile" \
    >"$st/want" 2>/dev/null || rrc=$?
  verdict=$(python3 -I "$HERE/compare_answers.py" "$st/got" "$st/want" "$rrc" 2>&1 | head -1)
  case "$verdict" in
    equal*) matched=$((matched + 1))
            if [ $path = ids ]; then ids_match=$((ids_match + 1)); else ref_match=$((ref_match + 1)); fi
            printf '%s\tmatched\t%s\t%s\n' "$t" "$path" "$reason" >>"$TSV" ;;
    uncompared*) uncompared=$((uncompared + 1)); printf '%s\tuncompared\t%s\t%s\n' "$t" "$path" "$verdict" >>"$TSV" ;;
    *) differed=$((differed + 1)); printf '%s\tdiffered\t%s\t%s\n' "$t" "$path" "$verdict" >>"$TSV"
       printf '%s (%s): %s\n' "${t##*/}" "$path" "$verdict" >>"$MIS" ;;
  esac
  rm -rf "$st"
done

echo "sbm11 census (row agreement with the reference engine over the same input, NOT conformance):"
echo "  $executed executed, $rpack refused at convert/pack/activate, $rquery refused at query (out of $eligible eligible QueryEvaluationTest entries; $missing skipped for missing files)"
echo "  of the $executed executed: $matched matched the reference engine, $differed differed, $uncompared not comparable"
echo "  id path: $ids_exec executed, $ids_match matched; reference fallback: $ref_exec executed, $ref_match matched"
echo "  grouped aggregates on ids (issue 825): $agg_tests of the $ids_exec id-path tests"
if [ -n "${SBM11_MEMGEN:-}" ]; then
  echo "  memgen-check (issue 776): $mg_q queries, $mg_eq equal, $mg_diff differ ($mg_ref on the reference path, not compared; $mg_fail failed or check = false)"
fi
if [ -n "${SBM11_SIP:-}" ]; then
  echo "  --sip $SBM11_SIP: a scan with candidates ran in $sip_tests of the $ids_exec id-path tests (issue 809)"
fi
if [ -s "$MIS" ]; then echo "  mismatches:"; sed 's/^/    /' "$MIS"; fi
cut -f2 "$TSV" | sort | uniq -c
echo "  reference fallback reasons (executed tests):"
awk -F'\t' '$3 == "reference" { r = $4; if (r == "") r = "(no reason printed)"; c[r]++ } END { for (k in c) printf "    %4d  %s\n", c[k], k }' "$TSV" | sort -rn
cp "$TSV" "$ROOT/tmp/sbm11-census-latest.tsv"
echo "  per-test outcomes: tmp/sbm11-census-latest.tsv"
