#!/usr/bin/env bash
#
# cli-smoke.sh — exercise every VERB of `l4factoidal` (Wasm/Cli.lean),
# the real command-line interface built on the dispatch ABI
# (Wasm/Dispatch.lean). Modelled on native-smoke.sh, which exercises
# the ABI itself through `l4wasm-cli`; this script exercises the
# person/script-facing layer on top of it — flags, stdin, exit codes,
# error text — so an ABI bug and a CLI-argument-parsing bug can never
# be confused for one another.
#
#   formal/lean4/Wasm/cli-smoke.sh
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$LEAN_DIR"
command -v lake >/dev/null || { echo "lake not on PATH (export PATH=\$HOME/.elan/bin:\$PATH)"; exit 1; }

echo "=== build l4factoidal"
lake build l4factoidal >/dev/null
CLI="$LEAN_DIR/.lake/build/bin/l4factoidal"
[ -x "$CLI" ] || { echo "FAIL: $CLI not built"; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

PASS=0
FAIL=0
XFAIL=0

pass() { echo "ok   $1"; PASS=$((PASS + 1)); }
fail() {
  local label="$1"; shift
  echo "FAIL $label"
  for l in "$@"; do printf '     %s\n' "$l"; done
  FAIL=$((FAIL + 1))
}

# verdict LABEL ISSUE OK [DETAIL...]
# OK is 1 when the check held. ISSUE empty: a plain assertion. ISSUE set: an
# expected failure for that open issue (CLAUDE.md, "A stated shortfall is a
# failing test plus an open issue"): a failed check counts as xfail and keeps
# the run green; a check that holds is an XPASS and FAILS the run, so the
# case is changed to a plain assertion and the issue closed in the same commit.
verdict() {
  local label="$1" issue="$2" ok="$3"; shift 3
  if [ -z "$issue" ]; then
    if [ "$ok" = 1 ]; then pass "$label"; else fail "$label" "$@"; fi
  elif [ "$ok" = 1 ]; then
    fail "$label" "XPASS: expected to fail until https://github.com/danbri/factoidal/issues/$issue is fixed, and it passes" \
      "make it a plain assertion (ISSUE empty) and close the issue"
  else
    echo "xfail $label (https://github.com/danbri/factoidal/issues/$issue)"
    XFAIL=$((XFAIL + 1))
  fi
}

# json_holds PY_EXPR: 1 when $OUT is JSON and PY_EXPR (over `r`) holds, else 0.
json_holds() {
  if printf '%s' "$OUT" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($1), r
" 2>/dev/null; then echo 1; else echo 0; fi
}

# assert_exit LABEL WANT_EXIT -- CMD...
# Runs CMD, checks only its exit code. Leaves $OUT / $ERR / $RC set for
# a caller that wants to check content too.
run_cmd() {
  OUT="$("$@" 2>"$TMP/stderr")" && RC=0 || RC=$?
  ERR="$(cat "$TMP/stderr")"
}

assert_exit() {
  local label="$1" want="$2"; shift 2
  run_cmd "$@"
  if [ "$RC" -eq "$want" ]; then
    pass "$label"
  else
    fail "$label" "exit=$RC want=$want" "stdout=$OUT" "stderr=$ERR"
  fi
}

# assert_text LABEL WANT_EXIT out|err NEEDLE -- CMD...
assert_text() {
  local label="$1" want="$2" stream="$3" needle="$4"; shift 4
  run_cmd "$@"
  local hay
  [ "$stream" = "out" ] && hay="$OUT" || hay="$ERR"
  # A here-string, not a pipe: with pipefail, `grep -q` closing the pipe early
  # makes the writer die of SIGPIPE on a long text (the help text), and the
  # pipeline then fails although the needle was found.
  if [ "$RC" -eq "$want" ] && grep -qF -- "$needle" <<< "$hay"; then
    pass "$label"
  else
    fail "$label" "exit=$RC want=$want" "stdout=$OUT" "stderr=$ERR"
  fi
}

# assert_json LABEL WANT_EXIT PY_EXPR -- CMD...
# PY_EXPR sees the parsed stdout JSON as `r`.
assert_json() {
  local label="$1" want="$2" expr="$3"; shift 3
  run_cmd "$@"
  if [ "$RC" -ne "$want" ]; then
    fail "$label" "exit=$RC want=$want" "stdout=$OUT" "stderr=$ERR"
    return
  fi
  if printf '%s' "$OUT" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
" 2>/dev/null; then
    pass "$label"
  else
    fail "$label" "stdout=$OUT"
  fi
}

echo "=== cli smoke ($TMP)"

# --- version / help / ops --------------------------------------------
assert_text "version"          0 out "l4factoidal-wasm"     "$CLI" version
assert_text "version abi line" 0 out "dispatch ABI:"        "$CLI" version
assert_text "help"             0 out "Usage: l4factoidal"   "$CLI" help
assert_text "no verb -> usage error" 2 err "missing verb"   "$CLI"
assert_text "unknown verb -> usage error" 2 err "unknown verb" "$CLI" definitelyNotAVerb
assert_json "ops reflection"   0 \
  'r["ok"] is True and set(["parseToDatasetJson","queryDataset","owlClosure","clParse","datasetOpen"]) <= set(r["ops"])' \
  "$CLI" ops

# --- parse -------------------------------------------------------------
echo '@prefix ex: <http://example.org/> . ex:a ex:p ex:b, ex:c .' > "$TMP/data.ttl"

assert_text "parse file, default -> count" 0 out "2" \
  "$CLI" parse "$TMP/data.ttl" --format turtle
assert_text "parse --out nquads" 0 out "<http://example.org/a> <http://example.org/p> <http://example.org/b> ." \
  "$CLI" parse "$TMP/data.ttl" --format turtle --out nquads
assert_text "parse --out turtle" 0 out "@prefix" \
  "$CLI" parse "$TMP/data.ttl" --format turtle --out turtle
assert_text "parse bad turtle -> error" 1 err "offset" \
  bash -c "printf 'not turtle @@@' | '$CLI' parse --format turtle"
assert_text "parse unknown --out -> usage error" 2 err "unknown --out" \
  "$CLI" parse "$TMP/data.ttl" --out bogus
assert_text "parse missing --format value -> usage error" 2 err "missing value" \
  "$CLI" parse --format
assert_text "parse missing file -> error" 1 err "no such file" \
  "$CLI" parse /no/such/file.ttl

# stdin: no positional file argument at all.
STDIN_COUNT="$(printf '@prefix ex: <http://e/> . ex:a ex:p ex:b .' | "$CLI" parse --format turtle)"
if [ "$STDIN_COUNT" = "1" ]; then pass "parse stdin (no file arg)"; else
  fail "parse stdin (no file arg)" "got '$STDIN_COUNT'"
fi

# Issue 724: `parse` counts the graph as a set (RDF 1.1 Concepts §3) and a
# COUNT(*) query over the same file agrees with it (before: 3 and 2).
printf '@prefix e: <http://e/> .\ne:a e:p e:b .\ne:a e:p e:b .\ne:a e:q "x"@EN .\n' > "$TMP/repeat.ttl"
REP_PARSE="$("$CLI" parse "$TMP/repeat.ttl" --format turtle)"
REP_QUERY="$("$CLI" query "$TMP/repeat.ttl" --format turtle \
  --query-string 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }' --table | sed -n 2p)"
if [ "$REP_PARSE" = "2" ] && [ "$REP_QUERY" = "2" ]; then
  pass "parse and query COUNT(*) agree on a repeated triple (issue 724)"
else
  fail "parse and query COUNT(*) agree on a repeated triple (issue 724)" \
    "parse='$REP_PARSE' query='$REP_QUERY'"
fi

# --- query ---------------------------------------------------------------
printf '<http://e/a> <http://e/p> <http://e/b> .\n' > "$TMP/d.nt"

assert_json "query select" 0 \
  'r["head"]["vars"] == ["s"] and r["results"]["bindings"][0]["s"]["value"] == "http://e/a"' \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
assert_text "query select --table" 0 out "http://e/a" \
  "$CLI" query "$TMP/d.nt" --format ntriples --table \
    --query-string 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
assert_text "query ask true -> exit 0" 0 out "true" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'ASK { <http://e/a> <http://e/p> <http://e/b> }'
assert_text "query ask false -> exit 1" 1 out "false" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'ASK { <http://e/a> <http://e/p> <http://e/zzz> }'
assert_text "query construct" 0 out "<http://e/q>" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'CONSTRUCT { ?s <http://e/q> ?o } WHERE { ?s <http://e/p> ?o }'

# SPARQL 1.1 §17.1: the types derived from xsd:integer are numeric. An
# xsd:int literal compares and adds by value; an out-of-range xsd:unsignedByte
# is ill-typed, so the comparison is a type error and FILTER drops the row
# (https://github.com/danbri/factoidal/issues/782).
cat > "$TMP/int.nt" <<'INTEOF'
<http://ex/a> <http://ex/age> "72"^^<http://www.w3.org/2001/XMLSchema#int> .
<http://ex/b> <http://ex/age> "72"^^<http://www.w3.org/2001/XMLSchema#integer> .
<http://ex/c> <http://ex/age> "73"^^<http://www.w3.org/2001/XMLSchema#int> .
<http://ex/e> <http://ex/age> "300"^^<http://www.w3.org/2001/XMLSchema#unsignedByte> .
INTEOF
assert_json "query FILTER(?a >= 72) on xsd:int (issue 782)" 0 \
  '[b["s"]["value"] for b in r["results"]["bindings"]] == ["http://ex/a", "http://ex/b", "http://ex/c"]' \
  "$CLI" query "$TMP/int.nt" --format ntriples \
    --query-string 'SELECT ?s WHERE { ?s <http://ex/age> ?a FILTER(?a >= 72) } ORDER BY ?s'
assert_json "query FILTER(?a = 72) on xsd:int (issue 782)" 0 \
  '[b["s"]["value"] for b in r["results"]["bindings"]] == ["http://ex/a", "http://ex/b"]' \
  "$CLI" query "$TMP/int.nt" --format ntriples \
    --query-string 'SELECT ?s WHERE { ?s <http://ex/age> ?a FILTER(?a = 72) } ORDER BY ?s'
assert_json "query (?a + 1) on xsd:int is xsd:integer (issue 782)" 0 \
  '[(b.get("b") or {}).get("value") for b in r["results"]["bindings"]] == ["73", "73", "74", None] and r["results"]["bindings"][0]["b"]["datatype"] == "http://www.w3.org/2001/XMLSchema#integer"' \
  "$CLI" query "$TMP/int.nt" --format ntriples \
    --query-string 'SELECT ?s ?b WHERE { ?s <http://ex/age> ?a BIND(?a + 1 AS ?b) } ORDER BY ?s'

# DESCRIBE (SPARQL 1.1 §16.4) prints the Concise Bounded Description of the
# resources it names: Alice's blank-node address is followed to its street,
# Carol is unrelated, and an IRI with no statements has an empty description.
cat > "$TMP/desc.nt" <<'DESCEOF'
<http://e/a> <http://e/name> "Alice" .
<http://e/a> <http://e/addr> _:b1 .
_:b1 <http://e/street> "1 High St" .
<http://e/c> <http://e/name> "Carol" .
DESCEOF
assert_text "query DESCRIBE <iri> follows the blank-node chain" 0 out "1 High St" \
  "$CLI" query "$TMP/desc.nt" --format ntriples --query-string 'DESCRIBE <http://e/a>'
run_cmd "$CLI" query "$TMP/desc.nt" --format ntriples --query-string 'DESCRIBE <http://e/a>'
if [ "$RC" -eq 0 ] && printf '%s' "$OUT" | grep -q 'Alice' && ! printf '%s' "$OUT" | grep -q 'Carol'; then
  pass "query DESCRIBE <iri> leaves out an unrelated resource"
else
  fail "query DESCRIBE <iri> leaves out an unrelated resource" "exit=$RC" "stdout=$OUT" "stderr=$ERR"
fi
run_cmd "$CLI" query "$TMP/desc.nt" --format ntriples \
  --query-string 'DESCRIBE ?x WHERE { ?x <http://e/name> ?n } ORDER BY DESC(?n) LIMIT 1'
if [ "$RC" -eq 0 ] && printf '%s' "$OUT" | grep -q 'Carol' && ! printf '%s' "$OUT" | grep -q 'Alice'; then
  pass "query DESCRIBE ?x ORDER BY DESC LIMIT 1 describes one resource"
else
  fail "query DESCRIBE ?x ORDER BY DESC LIMIT 1 describes one resource" "exit=$RC" "stdout=$OUT" "stderr=$ERR"
fi
run_cmd "$CLI" query "$TMP/desc.nt" --format ntriples --query-string 'DESCRIBE <http://e/nobody>'
if [ "$RC" -eq 0 ] && [ -z "$OUT" ]; then
  pass "query DESCRIBE of an IRI with no statements -> empty graph"
else
  fail "query DESCRIBE of an IRI with no statements -> empty graph" "exit=$RC" "stdout=$OUT" "stderr=$ERR"
fi
assert_text "query bad SPARQL (DESCRIBE with no target) -> error" 1 err "SPARQL parse error" \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'DESCRIBE WHERE { ?s ?p ?o }'

# SPARQL 1.1 Federated Query 2.3: a SERVICE call without SILENT that
# fails stops the query (exit 1, the error on stderr); with SILENT it is
# one solution with no bindings (https://github.com/danbri/factoidal/issues/717).
assert_text "query SERVICE without SILENT, no endpoint -> error" 1 err "SERVICE <http://u.example/sparql> failed" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'SELECT * WHERE { SERVICE <http://u.example/sparql> { ?s ?p ?o } }'
assert_json "query SERVICE SILENT, no endpoint -> one empty solution" 0 \
  'r["results"]["bindings"] == [{}]' \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'SELECT * WHERE { SERVICE SILENT <http://u.example/sparql> { ?s ?p ?o } }'
assert_text "query missing --query/--query-string -> usage error" 2 err "need --query" \
  "$CLI" query "$TMP/d.nt" --format ntriples
assert_text "query both --query and --query-string -> usage error" 2 err "pass only one" \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'ASK{}' --query "$TMP/d.nt"

# --- update ----------------------------------------------------------
assert_text "update" 0 out "<http://e/x> <http://e/p> <http://e/y> ." \
  "$CLI" update "$TMP/d.nt" --format ntriples \
    --update-string 'INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }'
assert_text "update missing --update/--update-string -> usage error" 2 err "need --update" \
  "$CLI" update "$TMP/d.nt" --format ntriples

# --- query and update base IRI (https://github.com/danbri/factoidal/issues/741)
# SPARQL 1.1 §4.1.1.2 resolves a relative IRI in a query against the base IRI
# (RFC 3986 §5.1). The base of a text read from a file is the file's IRI
# (RFC 3986 §5.1.3, the retrieval URI); a BASE in the text comes first
# (§5.1.1); a text given on the command line takes --base.
TMPIRI="file://$(realpath "$TMP")"
printf 'SELECT ?x WHERE { BIND(<rel> AS ?x) }\n' > "$TMP/rel.rq"
run_cmd "$CLI" query "$TMP/d.nt" --format ntriples --query "$TMP/rel.rq"
verdict "query --query FILE: a relative IRI resolves against the file's IRI" "" \
  "$( [ "$RC" -eq 0 ] && json_holds "r['results']['bindings'][0]['x']['value'] == '$TMPIRI/rel'" || echo 0 )" \
  "exit=$RC" "stdout=$OUT" "stderr=$ERR"
run_cmd "$CLI" query "$TMP/d.nt" --format ntriples --base http://example.org/b/ \
  --query-string 'SELECT ?x WHERE { BIND(<rel> AS ?x) }'
verdict "query --query-string --base IRI: a relative IRI resolves against IRI" "" \
  "$( [ "$RC" -eq 0 ] && json_holds "r['results']['bindings'][0]['x']['value'] == 'http://example.org/b/rel'" || echo 0 )" \
  "exit=$RC" "stdout=$OUT" "stderr=$ERR"
assert_text "query --query-string with no base: a relative IRI is an error" 1 err "invalid IRI" \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'SELECT ?x WHERE { BIND(<rel> AS ?x) }'
printf 'BASE <http://example.org/q/>\nSELECT ?x WHERE { BIND(<rel> AS ?x) }\n' > "$TMP/base.rq"
assert_json "query --query FILE: BASE in the text comes before the file's IRI" 0 \
  'r["results"]["bindings"][0]["x"]["value"] == "http://example.org/q/rel"' \
  "$CLI" query "$TMP/d.nt" --format ntriples --query "$TMP/base.rq"
printf 'INSERT DATA { <s> <p> <o> }\n' > "$TMP/rel.ru"
run_cmd "$CLI" update "$TMP/d.nt" --format ntriples --update "$TMP/rel.ru"
verdict "update --update FILE: a relative IRI resolves against the file's IRI" "" \
  "$( [ "$RC" -eq 0 ] && grep -qF "<$TMPIRI/s> <$TMPIRI/p> <$TMPIRI/o> ." <<< "$OUT" && echo 1 || echo 0 )" \
  "exit=$RC" "stdout=$OUT" "stderr=$ERR"
run_cmd "$CLI" update "$TMP/d.nt" --format ntriples --base http://example.org/b/ \
  --update-string 'INSERT DATA { <s> <p> <o> }'
verdict "update --update-string --base IRI: a relative IRI resolves against IRI" "" \
  "$( [ "$RC" -eq 0 ] && grep -qF '<http://example.org/b/s> <http://example.org/b/p> <http://example.org/b/o> .' <<< "$OUT" && echo 1 || echo 0 )" \
  "exit=$RC" "stdout=$OUT" "stderr=$ERR"

# The five W3C queries of issue 741, with their data. The CLI reads one
# dataset, so the test's qt:data and qt:graphData files are written as one
# N-Quads file; a qt:graphData graph is named by its file's IRI, as the
# manifest names it.
W3C_SPARQL="$LEAN_DIR/../../third_party/testing/w3c/sparql/sparql11"
ROWS_PY="$LEAN_DIR/../../tests/known-defects/sparql_rows.py"
fileiri() { printf 'file://%s' "$(realpath "$1")"; }
# nq_of FILE [GRAPH]: FILE (Turtle, base = its IRI) as N-Quads lines, in the
# default graph or in the named graph GRAPH.
nq_of() {
  "$CLI" parse "$1" --format turtle --base "$(fileiri "$1")" --out nquads |
    if [ -n "${2:-}" ]; then sed -e '/^$/d' -e "s| \.\$| <$2> .|"; else sed '/^$/d'; fi
}
# w3c_dataset OUT DEFAULT_FILE... -- NAMED_FILE...
w3c_dataset() {
  local out="$1" named=0; shift
  : > "$out"
  for f in "$@"; do
    if [ "$f" = "--" ]; then named=1; continue; fi
    if [ "$named" = 1 ]; then nq_of "$f" "$(fileiri "$f")" >> "$out"; else nq_of "$f" >> "$out"; fi
  done
}
if [ ! -r "$W3C_SPARQL/manifest-all.ttl" ] || [ ! -r "$ROWS_PY" ]; then
  fail "W3C SPARQL 1.1 test files" "missing under third_party/testing/w3c (run tools/ensure-test-env.sh)"
else
  # select_vs_srx LABEL ISSUE DATASET QUERY SRX: the rows equal the W3C rows.
  select_vs_srx() {
    local label="$1" issue="$2" ds="$3" q="$4" srx="$5" ok=0
    run_cmd "$CLI" query "$ds" --format nquads --query "$q"
    if [ "$RC" -eq 0 ] && printf '%s' "$OUT" | python3 -I "$ROWS_PY" > "$TMP/got.rows" 2>/dev/null \
       && python3 -I "$ROWS_PY" < "$srx" > "$TMP/want.rows" 2>/dev/null \
       && cmp -s "$TMP/got.rows" "$TMP/want.rows"; then ok=1; fi
    verdict "$label" "$issue" "$ok" "exit=$RC" "stdout=$OUT" "stderr=$ERR"
  }
  B="$W3C_SPARQL/bindings"
  w3c_dataset "$TMP/w3c-graph.nq" "$B/empty.ttl" -- "$B/data01.ttl" "$B/data02.ttl"
  run_cmd "$CLI" query "$TMP/w3c-graph.nq" --format nquads --query "$B/graph.rq"
  D1="$(fileiri "$B/data01.ttl")"; D2="$(fileiri "$B/data02.ttl")"
  verdict "W3C bindings/graph.rq (VALUES <data01.ttl> inside GRAPH)" "" \
    "$( [ "$RC" -eq 0 ] && json_holds "sorted((b['g']['value'], b['t']['value']) for b in r['results']['bindings']) == sorted([('$D1','foo'),('$D1','bar'),('$D2','foo')])" || echo 0 )" \
    "exit=$RC" "stdout=$OUT" "stderr=$ERR"
  C="$W3C_SPARQL/construct"
  w3c_dataset "$TMP/w3c-cw04.nq" -- "$C/data.ttl"
  run_cmd "$CLI" query "$TMP/w3c-cw04.nq" --format nquads --query "$C/constructwhere04.rq"
  WANT_CW04="$("$CLI" parse "$C/constructwhere04result.ttl" --format turtle --out nquads | sed '/^$/d' | sort)"
  verdict "W3C construct/constructwhere04.rq (FROM <data.ttl>)" "" \
    "$( [ "$RC" -eq 0 ] && [ -n "$WANT_CW04" ] && [ "$(printf '%s\n' "$OUT" | sed '/^$/d' | sort)" = "$WANT_CW04" ] && echo 1 || echo 0 )" \
    "exit=$RC" "stdout=$OUT" "stderr=$ERR"
  E="$W3C_SPARQL/exists"
  w3c_dataset "$TMP/w3c-ex03.nq" "$E/exists01.ttl" -- "$E/exists02.ttl"
  select_vs_srx "W3C exists/exists03.rq (GRAPH <exists02.ttl>)" "" \
    "$TMP/w3c-ex03.nq" "$E/exists03.rq" "$E/exists03.srx"
  P="$W3C_SPARQL/property-path"
  w3c_dataset "$TMP/w3c-ng.nq" -- "$P/ng-01.ttl" "$P/ng-02.ttl" "$P/ng-03.ttl"
  select_vs_srx "W3C property-path/path-ng-01.rq (GRAPH <ng-01.ttl>)" "" \
    "$TMP/w3c-ng.nq" "$P/path-ng-01.rq" "$P/path-ng-01.srx"
  select_vs_srx "W3C property-path/path-ng-02.rq (GRAPH <ng-01.ttl> with a path)" "" \
    "$TMP/w3c-ng.nq" "$P/path-ng-02.rq" "$P/path-ng-01.srx"

  # --- CONSTRUCT blank node labels (https://github.com/danbri/factoidal/issues/742)
  # RDF 1.1 N-Triples [141s] BLANK_NODE_LABEL has no ':'. The output of W3C
  # construct/constructlist.rq (a collection in the template) must parse back
  # as N-Triples, with every triple kept: 4 solutions of 5 template triples,
  # 20 triples, so the labels are distinct per solution and per template
  # position (SPARQL 1.1 §16.2.1).
  run_cmd "$CLI" query "$C/data.ttl" --format turtle --query "$C/constructlist.rq"
  CL_OUT="$OUT"; CL_RC="$RC"
  WANT_CL="$("$CLI" parse "$C/constructlistresult.ttl" --format turtle)"
  run_cmd bash -c "printf '%s\n' \"\$1\" | '$CLI' parse --format ntriples" _ "$CL_OUT"
  verdict "W3C construct/constructlist.rq output parses as N-Triples ($WANT_CL triples)" "" \
    "$( [ "$CL_RC" -eq 0 ] && [ "$RC" -eq 0 ] && [ "$OUT" = "$WANT_CL" ] && [ "$OUT" = 20 ] && echo 1 || echo 0 )" \
    "query exit=$CL_RC parse exit=$RC parse stdout=$OUT parse stderr=$ERR" "query stdout=$(printf '%s' "$CL_OUT" | head -n 2)"

  # --- NOW() (https://github.com/danbri/factoidal/issues/743): SPARQL 1.1
  # §17.4.5.1 gives an xsd:dateTime for the query execution. Until 2026-10-10
  # the ops path had no clock in its EvalEnv, so W3C functions/now01.rq answered
  # false (found by `l4diff --lean-cli`); the command line now reads the clock
  # once per query or update and passes it as `now`. The W3C expected result
  # now01.srx is true.
  F="$W3C_SPARQL/functions"
  run_cmd "$CLI" query "$F/data.ttl" --format turtle --query "$F/now01.rq"
  verdict "W3C functions/now01.rq (NOW() is an xsd:dateTime) -> true" "" \
    "$( [ "$RC" -eq 0 ] && [ "$OUT" = true ] && grep -q '<boolean>true</boolean>' "$F/now01.srx" && echo 1 || echo 0 )" \
    "exit=$RC" "stdout=$OUT" "stderr=$ERR"
fi

# --- NOW(): the value is the system clock, once per execution ----------------
# The value is read between two readings of `date`, so a constant or a fixed
# test clock fails. The seconds are compared as text: yyyy-mm-ddThh:mm:ss.
printf '<http://e/a> <http://e/p> <http://e/b> .\n<http://e/a> <http://e/p> <http://e/c> .\n<http://e/a> <http://e/p> <http://e/d> .\n' > "$TMP/now3.nt"
T_BEFORE="$(date -u +%Y-%m-%dT%H:%M:%S)"
run_cmd "$CLI" query "$TMP/now3.nt" --format ntriples \
  --query-string 'SELECT ?o ?n WHERE { ?s ?p ?o BIND(NOW() AS ?n) }'
T_AFTER="$(date -u +%Y-%m-%dT%H:%M:%S)"
NOW_ROWS="$OUT"
verdict "query: NOW() is the system clock, an xsd:dateTime in UTC" "" \
  "$(printf '%s' "$NOW_ROWS" | python3 -c "
import json, sys, re
r = json.load(sys.stdin)
b = r['results']['bindings']
v = b[0]['n']
assert v['datatype'] == 'http://www.w3.org/2001/XMLSchema#dateTime', v
assert re.fullmatch(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(\.\d+)?Z', v['value']), v
assert '$T_BEFORE' <= v['value'][:19] <= '$T_AFTER', (v, '$T_BEFORE', '$T_AFTER')
" 2>/dev/null && echo 1 || echo 0)" \
  "before=$T_BEFORE after=$T_AFTER" "stdout=$NOW_ROWS" "stderr=$ERR"
verdict "query: every NOW() of one execution is the same value (3 rows, 1 distinct)" "" \
  "$(printf '%s' "$NOW_ROWS" | python3 -c "
import json, sys
r = json.load(sys.stdin)
b = r['results']['bindings']
assert len(b) == 3, b
assert len(set(x['n']['value'] for x in b)) == 1, b
" 2>/dev/null && echo 1 || echo 0)" \
  "stdout=$NOW_ROWS"
run_cmd "$CLI" query "$TMP/now3.nt" --format ntriples \
  --query-string 'ASK { BIND(NOW() AS ?a) BIND(NOW() AS ?b) FILTER(?a = ?b) }'
verdict "query: two NOW() calls in one query are equal" "" \
  "$( [ "$RC" -eq 0 ] && [ "$OUT" = true ] && echo 1 || echo 0 )" "exit=$RC" "stdout=$OUT" "stderr=$ERR"
# Update: INSERT ... WHERE with NOW() in a BIND inserts the clock reading.
T_BEFORE="$(date -u +%Y-%m-%dT%H:%M:%S)"
run_cmd "$CLI" update "$TMP/now3.nt" --format ntriples \
  --update-string 'INSERT { <http://e/a> <http://e/at> ?n } WHERE { BIND(NOW() AS ?n) }'
T_AFTER="$(date -u +%Y-%m-%dT%H:%M:%S)"
NOW_UPD="$OUT"; NOW_UPD_RC="$RC"
NOW_AT="$(printf '%s\n' "$NOW_UPD" | sed -n 's|^<http://e/a> <http://e/at> "\([^"]*\)"^^<http://www.w3.org/2001/XMLSchema#dateTime> \.$|\1|p')"
verdict "update: INSERT ... WHERE BIND(NOW()) inserts an xsd:dateTime from the system clock" "" \
  "$( [ "$NOW_UPD_RC" -eq 0 ] && python3 -c "
import sys
b, a, v = sys.argv[1:4]
assert v != '' and b <= v[:19] <= a, (b, v, a)
" "$T_BEFORE" "$T_AFTER" "$NOW_AT" 2>/dev/null && echo 1 || echo 0 )" \
  "before=$T_BEFORE after=$T_AFTER" "inserted=$NOW_AT" "stdout=$NOW_UPD"

# --- canonicalize ------------------------------------------------------
assert_text "canonicalize" 0 out "_:c14n0" \
  bash -c "printf '_:b0 <http://e/p> \"v\" .' | '$CLI' canonicalize --format nquads"

# --- closure -----------------------------------------------------------
SUBCLASS='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .
<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .
'
printf '%s' "$SUBCLASS" > "$TMP/subclass.nq"

assert_text "closure --regime rdfs" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime rdfs
assert_text "closure --regime owl-rl" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime owl-rl
assert_text "closure --regime rho-df" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime rho-df
assert_text "closure --regime rdfs-plus" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime rdfs-plus
assert_text "closure missing --regime -> usage error" 2 err "need --regime" \
  "$CLI" closure "$TMP/subclass.nq" --format nquads
assert_text "closure unknown --regime -> usage error" 2 err "unknown --regime" \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime bogus

# --- owl-consistent / owl-entails --------------------------------------
assert_text "owl-consistent true -> exit 0" 0 out "true" \
  "$CLI" owl-consistent "$TMP/subclass.nq" --format nquads

NOTHING='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Nothing> .
'
printf '%s' "$NOTHING" > "$TMP/nothing.nq"
assert_text "owl-consistent false -> exit 1, stdout false" 1 out "false" \
  "$CLI" owl-consistent "$TMP/nothing.nq" --format nquads
assert_text "owl-consistent false -> reason on stderr" 1 err "contradiction" \
  "$CLI" owl-consistent "$TMP/nothing.nq" --format nquads

CYCLIC='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/A> .
<http://e/A> <http://www.w3.org/2000/01/rdf-schema#subClassOf> _:r .
_:r <http://www.w3.org/2002/07/owl#onProperty> <http://e/p> .
_:r <http://www.w3.org/2002/07/owl#someValuesFrom> <http://e/A> .
'
printf '%s' "$CYCLIC" > "$TMP/cyclic.nq"
assert_text "owl-consistent budget-out -> unknown, exit 1" 1 out "unknown" \
  "$CLI" owl-consistent "$TMP/cyclic.nq" --format nquads --fuel 1

CONCL='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> .
'
UNRELATED='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Zebra> .
'
printf '%s' "$CONCL" > "$TMP/concl.nq"
printf '%s' "$UNRELATED" > "$TMP/unrelated.nq"
assert_text "owl-entails true (closure) -> exit 0" 0 out "true" \
  "$CLI" owl-entails "$TMP/subclass.nq" "$TMP/concl.nq" --format nquads
assert_text "owl-entails false (refutation) -> exit 1" 1 out "false" \
  "$CLI" owl-entails "$TMP/subclass.nq" "$TMP/unrelated.nq" --format nquads
assert_text "owl-entails missing conclusion file -> usage error" 2 err "need PREMISE_FILE" \
  "$CLI" owl-entails "$TMP/subclass.nq"

# --- cl ------------------------------------------------------------------
IKL='(ist c (that (Dead OBL)))'
printf '%s' "$IKL" > "$TMP/prop.clif"

assert_json "cl parse" 0 \
  'r["ok"] is True and r["sentences"] == 1 and r["pureCL"] is False' \
  "$CLI" cl parse "$TMP/prop.clif"
assert_text "cl parse unclosed paren -> error" 1 err "unclosed" \
  bash -c "printf '(P a' | '$CLI' cl parse"

# The four ops of danbri/factoidal#623, through the CLI verbs.
printf '%s' '(forall (zz) (if (Boy zz) (Person zz)))' > "$TMP/alpha.clif"
printf '%s' '(P (that (Q a)))' > "$TMP/ikl.clif"
printf '%s' '(Boy Bill)' > "$TMP/sat-yes.clif"
printf '%s' '(Boy Sue)' > "$TMP/sat-no.clif"
printf '%s' '(forall (...m) (P ...m))' > "$TMP/seqmark.clif"
cat > "$TMP/interp.json" <<'INTERP'
{"domain":["bill","boy"],"default":"bill",
 "names":{"Bill":"bill","Boy":"boy","Sue":"boy"},
 "relations":[{"op":"boy","args":["bill"]}]}
INTERP

assert_json "cl serialize" 0 \
  'r["ok"] is True and r["clif"] == "(forall (zz) (if (Boy zz) (Person zz)))"
   and r["roundTripProved"] is False' \
  "$CLI" cl serialize "$TMP/alpha.clif"

assert_json "cl alpha-norm canonicalises bound names" 0 \
  'r["ok"] is True and r["clif"] == "(forall (v1) (if (Boy v1) (Person v1)))"' \
  "$CLI" cl alpha-norm "$TMP/alpha.clif"

assert_json "cl normalize -> head + tail" 0 \
  'r["ok"] is True and r["head"] == ["(P prop1)"]
   and r["tail"] == ["(iff (prop1) (Q a))"] and r["noIntrusion"] is True
   and r["preserves"] == "satisfiability"' \
  "$CLI" cl normalize "$TMP/ikl.clif"

assert_json "cl finite-sat satisfied" 0 \
  'r["ok"] is True and r["satisfied"] is True
   and r["preconditions"]["domainComplete"]["holds"] is True' \
  "$CLI" cl finite-sat "$TMP/interp.json" "$TMP/sat-yes.clif"

# The refutation, so a checker answering `true` to everything fails here.
assert_json "cl finite-sat refutes where the tables have no row" 0 \
  'r["ok"] is True and r["satisfied"] is False' \
  "$CLI" cl finite-sat "$TMP/interp.json" "$TMP/sat-no.clif"

# The hypothesis is checked, and a text outside it is refused by name.
assert_text "cl finite-sat refuses a sequence-marker quantifier" 1 err "noSeqQuant" \
  "$CLI" cl finite-sat "$TMP/interp.json" "$TMP/seqmark.clif"

assert_text "cl finite-sat missing INTERP.json -> usage error" 2 err "need INTERP.json" \
  "$CLI" cl finite-sat

assert_text "cl missing subcommand -> usage error" 2 err "need a subcommand" \
  "$CLI" cl
assert_text "cl unknown subcommand -> usage error" 2 err "unknown subcommand" \
  "$CLI" cl bogus

echo "=== cli-smoke: $PASS pass, $FAIL fail, $XFAIL xfail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
