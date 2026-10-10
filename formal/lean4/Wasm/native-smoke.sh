#!/usr/bin/env bash
#
# native-smoke.sh — exercise EVERY op of the dispatch ABI
# (Wasm/Dispatch.lean) once through the native CLI, so an ABI bug and a
# wasm-toolchain bug can never be confused for one another.
#
#   formal/lean4/Wasm/native-smoke.sh
#
# Builds l4wasm-cli, then drives `l4wasm-cli call <op> <argsJsonFile>`
# (and, for the dataset-handle ops whose state must survive across
# calls, `l4wasm-cli callseq <seqJsonFile>` — several ops in one
# process) with tiny inline fixtures and asserts the envelope keys the
# F* npm entry (bin/npm-entry/entry_jsoo.ml) pins. Includes one error
# path per family: bad Turtle (parse), bad SPARQL (query), unknown handle
# (handles), unknown op (dispatch). Exits non-zero on any mismatch.
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$LEAN_DIR"
command -v lake >/dev/null || { echo "lake not on PATH (export PATH=\$HOME/.elan/bin:\$PATH)"; exit 1; }

echo "=== build l4wasm-cli + IBK3 fixture publisher"
lake build l4wasm-cli l4block-shard-pack >/dev/null
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"
PACK="$LEAN_DIR/.lake/build/bin/l4block-shard-pack"
[ -x "$CLI" ] || { echo "FAIL: $CLI not built"; exit 1; }
[ -x "$PACK" ] || { echo "FAIL: $PACK not built"; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

PASS=0
FAIL=0
XFAIL=0

# args <file> <arg>... — write a JSON array-of-strings args file.
args() {
  local out="$1"; shift
  python3 - "$out" "$@" <<'EOF'
import json, sys
with open(sys.argv[1], "w") as f:
    json.dump(sys.argv[2:], f)
EOF
}

# checkseq <label> <seqfile> <python-assert-expr>
# Runs `l4wasm-cli callseq <seqfile>` — several op/args pairs in ONE
# process, which is what dataset-handle state needs — and hands the
# expression the parsed envelopes as the list `rs`, in call order.
checkseq() {
  local label="$1" seqfile="$2" expr="$3"
  local out
  out="$("$CLI" callseq "$seqfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
rs = [json.loads(line) for line in sys.stdin if line.strip()]
assert ($expr), rs
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

# checkblob <label> <op> <argsfile> <blobfile> <python-assert-expr>
# Runs `l4wasm-cli callblob <op> <argsfile> <blobfile>` — the native form of
# the wasm module's `l4_call_blob_c`, which carries ONE contiguous byte region
# beside the string arguments. The expression sees the envelope as `r`.
checkblob() {
  local label="$1" op="$2" argsfile="$3" blobfile="$4" expr="$5"
  local out
  out="$("$CLI" callblob "$op" "$argsfile" "$blobfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

# check <label> <op> <argsfile> <python-assert-expr>
# The expression sees the parsed envelope as `r`.
check() {
  local label="$1" op="$2" argsfile="$3" expr="$4"
  local out
  out="$("$CLI" call "$op" "$argsfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

echo "=== dispatch smoke ($TMP)"

# --- Parse family -----------------------------------------------------
TTL='@prefix ex: <http://example.org/> . ex:alice ex:knows ex:bob .'
args "$TMP/parse.json" "$TTL" "turtle" ""
check "parseToDatasetJson turtle" parseToDatasetJson "$TMP/parse.json" \
  'r["ok"] is True and r["count"] == 1 and "example.org/alice" in r["nquads"]'

args "$TMP/parse-nt.json" '<http://e/a> <http://e/p> <http://e/b> .' "ntriples" ""
check "parseToDatasetJson ntriples" parseToDatasetJson "$TMP/parse-nt.json" \
  'r["ok"] is True and r["count"] == 1'

args "$TMP/parse-bad.json" 'this is not turtle @@@' "turtle" ""
check "parseToDatasetJson bad turtle -> error" parseToDatasetJson "$TMP/parse-bad.json" \
  'r["ok"] is False and isinstance(r["error"], str) and len(r["error"]) > 0'

args "$TMP/parse-jsonld.json" '{"@context":{"name":"http://xmlns.com/foaf/0.1/name"},"@id":"http://example.org/alice","name":"Alice"}' "jsonld" ""
check "parseToDatasetJson jsonld" parseToDatasetJson "$TMP/parse-jsonld.json" \
  'r["ok"] is True and r["count"] == 1 and "foaf/0.1/name" in r["nquads"] and "Alice" in r["nquads"]'

args "$TMP/parse-jsonld-bad.json" '{' "jsonld" ""
check "parseToDatasetJson jsonld, not JSON -> error" parseToDatasetJson "$TMP/parse-jsonld-bad.json" \
  'r["ok"] is False and "JSON-LD" in r["error"]'

# --- parseDocument: lenient (recovery) parse, issue 716 ------------------
# Wasm/Ops/Lenient.lean. One bad statement among good ones: the good ones
# are kept, the bad one is one diagnostic with its line, column, offset and
# class; without {"lenient":true} the op answers as parseToDatasetJson.
LTTL='<http://x/a> <http://x/p> "1" .
<http://x/b> <http://x/p> .
<http://x/c> <http://x/p> "3" .
'
args "$TMP/pd-ttl.json" "$LTTL" "turtle" "" '{"lenient":true}'
check "parseDocument lenient turtle keeps 2, reports line 2" parseDocument "$TMP/pd-ttl.json" \
  'r["ok"] is True and r["count"] == 2 and len(r["diagnostics"]) == 1
   and r["diagnostics"][0]["line"] == 2 and r["diagnostics"][0]["column"] == 27
   and r["diagnostics"][0]["offset"] == 58
   and r["diagnostics"][0]["class"] == "unexpected-token"
   and r["prefixes"] == {}'
args "$TMP/pd-strict.json" "$LTTL" "turtle" "" ""
check "parseDocument without lenient -> the strict error envelope" parseDocument "$TMP/pd-strict.json" \
  'r["ok"] is False and r["line"] == 2 and r["column"] == 27 and r["format"] == "turtle"'
LNQ='<http://x/a> <http://x/p> <http://x/o> <http://x/g> .
<http://x/a> <http://x/p> "x" "g" .
<http://x/a> <http://x/p> "bad \q" .
<http://x/b> <http://x/p> <http://x/o> .
'
args "$TMP/pd-nq.json" "$LNQ" "nquads" "" '{"lenient":true}'
check "parseDocument lenient nquads: two classes, two kept" parseDocument "$TMP/pd-nq.json" \
  'r["ok"] is True and r["count"] == 2
   and [(d["line"], d["class"]) for d in r["diagnostics"]] == [(2, "bad-graph-name"), (3, "bad-escape")]'
args "$TMP/pd-nq-max.json" "$LNQ" "nquads" "" '{"lenient":true,"maxErrors":1}'
check "parseDocument maxErrors 1 stops with too-many-errors" parseDocument "$TMP/pd-nq-max.json" \
  'r["ok"] is True and [d["class"] for d in r["diagnostics"]] == ["bad-graph-name", "too-many-errors"]'
args "$TMP/pd-trig.json" '<http://x/g> { <http://x/a> <http://x/p> . <http://x/b> <http://x/p> <http://x/o> }' "trig" "" '{"lenient":true}'
check "parseDocument lenient trig recovers inside the graph block" parseDocument "$TMP/pd-trig.json" \
  'r["ok"] is True and r["count"] == 1 and "<http://x/g>" in r["nquads"] and len(r["diagnostics"]) == 1'
args "$TMP/pd-arity.json" "$LTTL" "turtle"
check "parseDocument with three arguments -> arity error" parseDocument "$TMP/pd-arity.json" \
  'r["ok"] is False and "expects 4 arguments" in r["error"]'

NQ='<http://e/a> <http://e/p> <http://e/b> .
<http://e/a> <http://e/p> <http://e/c> <http://e/g> .
'
args "$TMP/ser-nq.json" "$NQ"
check "serializeNQuads" serializeNQuads "$TMP/ser-nq.json" \
  'r["ok"] is True and "<http://e/g>" in r["nquads"] and r["nquads"].count(" .") == 2'

args "$TMP/ser-ttl.json" "$NQ"
check "serializeTurtle" serializeTurtle "$TMP/ser-ttl.json" \
  'r["ok"] is True and "@prefix" in r["turtle"] and "<http://e/>" in r["turtle"]'

# --- Query family -----------------------------------------------------
DATA='<http://e/a> <http://e/p> <http://e/b> .
'
args "$TMP/q-select.json" "$DATA" 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
check "queryDataset select" queryDataset "$TMP/q-select.json" \
  'r["ok"] is True and r["kind"] == "select" and isinstance(r["srj"], dict)
   and r["srj"]["head"]["vars"] == ["s"]
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'

args "$TMP/q-ask.json" "$DATA" 'ASK { <http://e/a> <http://e/p> <http://e/b> }'
check "queryDataset ask" queryDataset "$TMP/q-ask.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'

# ASK applies its SolutionModifier (grammar rule [12]; issue 699). The data
# holds one triple: one solution, one group of one row.
args "$TMP/q-ask-limit0.json" "$DATA" 'ASK { ?s ?p ?o } LIMIT 0'
check "queryDataset ask LIMIT 0 -> false" queryDataset "$TMP/q-ask-limit0.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is False'
args "$TMP/q-ask-offset.json" "$DATA" 'ASK { ?s ?p ?o } OFFSET 1'
check "queryDataset ask OFFSET past the end -> false" queryDataset "$TMP/q-ask-offset.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is False'
args "$TMP/q-ask-having-no.json" "$DATA" 'ASK { ?s ?p ?o } GROUP BY ?s HAVING (COUNT(*) > 1)'
check "queryDataset ask GROUP BY HAVING fails -> false" queryDataset "$TMP/q-ask-having-no.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is False'
args "$TMP/q-ask-having-yes.json" "$DATA" 'ASK { ?s ?p ?o } GROUP BY ?s HAVING (COUNT(*) > 0)'
check "queryDataset ask GROUP BY HAVING holds -> true" queryDataset "$TMP/q-ask-having-yes.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'

# §18.6 EXISTS / NOT EXISTS through the backend path: the data holds a p b
# only, so NOT EXISTS of the reversed pattern keeps the row and EXISTS drops
# it. Regression pin (2026-09-02): the backend environment carried no
# dataset and FILTER NOT EXISTS answered zero rows.
args "$TMP/q-not-exists.json" "$DATA" \
  'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER NOT EXISTS { ?o <http://e/p> ?s } }'
check "queryDataset FILTER NOT EXISTS keeps the row" queryDataset "$TMP/q-not-exists.json" \
  'r["ok"] is True and r["kind"] == "select"
   and len(r["srj"]["results"]["bindings"]) == 1
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'

args "$TMP/q-exists.json" "$DATA" \
  'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER EXISTS { ?o <http://e/p> ?s } }'
check "queryDataset FILTER EXISTS drops the row" queryDataset "$TMP/q-exists.json" \
  'r["ok"] is True and r["kind"] == "select" and len(r["srj"]["results"]["bindings"]) == 0'

args "$TMP/q-construct.json" "$DATA" \
  'CONSTRUCT { ?s <http://e/q> ?o } WHERE { ?s <http://e/p> ?o }'
check "queryDataset construct" queryDataset "$TMP/q-construct.json" \
  'r["ok"] is True and r["kind"] == "construct" and "<http://e/q>" in r["nquads"]'

# DESCRIBE (§16.4): the Concise Bounded Description of each resource the
# clause names. Alice has a blank-node address that is followed to its
# street; Carol is an unrelated subject; the literal "Alice" names nothing.
DESC_DATA='<http://e/a> <http://e/name> "Alice" .
<http://e/a> <http://e/addr> _:b1 .
_:b1 <http://e/street> "1 High St" .
<http://e/c> <http://e/name> "Carol" .
'
args "$TMP/q-describe.json" "$DESC_DATA" 'DESCRIBE <http://e/a>'
check "queryDataset DESCRIBE follows the blank-node chain" queryDataset "$TMP/q-describe.json" \
  'r["ok"] is True and r["kind"] == "describe" and r["nquads"].count(" .") == 3
   and "1 High St" in r["nquads"] and "Carol" not in r["nquads"]'

args "$TMP/q-describe-var.json" "$DESC_DATA" \
  'DESCRIBE ?x WHERE { ?x <http://e/name> ?n } ORDER BY ?n LIMIT 1'
check "queryDataset DESCRIBE ?x ORDER BY LIMIT 1 describes one resource" queryDataset "$TMP/q-describe-var.json" \
  'r["ok"] is True and r["kind"] == "describe" and r["nquads"].count(" .") == 3
   and "Alice" in r["nquads"] and "Carol" not in r["nquads"]'

args "$TMP/q-describe-two.json" "$DESC_DATA" \
  'DESCRIBE ?x WHERE { ?x <http://e/name> ?n }'
check "queryDataset DESCRIBE ?x with two bindings describes both" queryDataset "$TMP/q-describe-two.json" \
  'r["ok"] is True and r["kind"] == "describe" and r["nquads"].count(" .") == 4
   and "Alice" in r["nquads"] and "Carol" in r["nquads"]'

args "$TMP/q-describe-none.json" "$DESC_DATA" 'DESCRIBE <http://e/nobody>'
check "queryDataset DESCRIBE of an IRI with no triples -> empty graph" queryDataset "$TMP/q-describe-none.json" \
  'r["ok"] is True and r["kind"] == "describe" and r["nquads"] == ""'

args "$TMP/q-describe-lit.json" "$DESC_DATA" \
  'DESCRIBE ?n WHERE { <http://e/a> <http://e/name> ?n }'
check "queryDataset DESCRIBE of a literal binding -> empty graph" queryDataset "$TMP/q-describe-lit.json" \
  'r["ok"] is True and r["kind"] == "describe" and r["nquads"] == ""'

args "$TMP/q-bad.json" "$DATA" 'DESCRIBE WHERE { ?s ?p ?o }'
check "queryDataset bad SPARQL (DESCRIBE with no target) -> error" queryDataset "$TMP/q-bad.json" \
  'r["ok"] is False and "SPARQL parse error" in r["error"]'

args "$TMP/update.json" "$DATA" \
  'INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }'
check "updateDataset" updateDataset "$TMP/update.json" \
  'r["ok"] is True and "<http://e/x>" in r["nquads"] and "<http://e/a>" in r["nquads"]'

# --- NOW() (https://github.com/danbri/factoidal/issues/743) ------------
# SPARQL 1.1 section 17.4.5.1: NOW() is one xsd:dateTime for the whole query
# execution. The pure ops take it as an argument; every IO op reads the system
# clock once and passes it. `l4wasm-cli call` serves the IO table, as the wasm
# shim does. NOWOK holds a Python predicate: the lexical form is a UTC
# xsd:dateTime within 300 seconds of the system clock, so a constant, a fixed
# test clock, or an unbound NOW() all fail.
NOWOK='(lambda v: v.endswith("Z") and abs((__import__("datetime").datetime.now(__import__("datetime").timezone.utc) - __import__("datetime").datetime.strptime(v[:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=__import__("datetime").timezone.utc)).total_seconds()) < 300)'
XSDDT='http://www.w3.org/2001/XMLSchema#dateTime'
DATA3='<http://e/a> <http://e/p> <http://e/b> .
<http://e/a> <http://e/p> <http://e/c> .
<http://e/a> <http://e/p> <http://e/d> .
'
# W3C functions/now01.rq
args "$TMP/now-ask.json" "$DATA" \
  'ASK { BIND(NOW() AS ?n) FILTER(DATATYPE(?n) = <http://www.w3.org/2001/XMLSchema#dateTime>) }'
check "queryDataset NOW() is an xsd:dateTime (W3C functions/now01.rq) -> true" queryDataset "$TMP/now-ask.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'
args "$TMP/now-select.json" "$DATA3" 'SELECT ?o ?n WHERE { ?s ?p ?o BIND(NOW() AS ?n) }'
check "queryDataset NOW() is the system clock, one value for every row" queryDataset "$TMP/now-select.json" \
  'r["ok"] is True and len(r["srj"]["results"]["bindings"]) == 3
   and len({b["n"]["value"] for b in r["srj"]["results"]["bindings"]}) == 1
   and r["srj"]["results"]["bindings"][0]["n"]["datatype"] == "'"$XSDDT"'"
   and '"$NOWOK"'(r["srj"]["results"]["bindings"][0]["n"]["value"])'
args "$TMP/now-select12.json" "$DATA3" 'SELECT ?n WHERE { BIND(NOW() AS ?n) }'
check "queryDataset12 NOW() is the system clock" queryDataset12 "$TMP/now-select12.json" \
  'r["ok"] is True and '"$NOWOK"'(r["srj"]["results"]["bindings"][0]["n"]["value"])'
args "$TMP/now-update.json" "$DATA" \
  'INSERT { <http://e/a> <http://e/at> ?n } WHERE { BIND(NOW() AS ?n) }'
check "updateDataset INSERT ... WHERE BIND(NOW()) inserts the system clock" updateDataset "$TMP/now-update.json" \
  'r["ok"] is True and '"$NOWOK"'(__import__("re").search(r"<http://e/at> \"([^\"]*)\"\^\^<'"$XSDDT"'>", r["nquads"]).group(1))'
args "$TMP/now-raw.json" "$DATA3" 'SELECT ?n WHERE { BIND(NOW() AS ?n) }' \
  '{"dataFormat":"ntriples","output":"csv"}'
check "queryRaw NOW() is the system clock" queryRaw "$TMP/now-raw.json" \
  'r["ok"] is True and '"$NOWOK"'(r["text"].split("\r\n")[1])'
python3 - "$TMP/now-handles.json" <<'EOF'
import json, sys
TTL = '@prefix ex: <http://e/> . ex:a ex:p ex:b .'
NOWQ = "SELECT ?n WHERE { BIND(NOW() AS ?n) }"
seq = [
  ["datasetOpen",    [TTL, "turtle", ""]],
  ["datasetQuery",   ["h1", NOWQ]],
  ["datasetQuery12", ["h1", NOWQ]],
  ["datasetUpdate",  ["h1", "INSERT { <http://e/a> <http://e/at> ?n } WHERE { BIND(NOW() AS ?n) }"]],
  ["datasetQuery",   ["h1", "SELECT ?v WHERE { <http://e/a> <http://e/at> ?v }"]],
  ["datasetClose",   ["h1"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "dataset handle NOW(): datasetQuery, datasetQuery12 and datasetUpdate read the clock" "$TMP/now-handles.json" \
  'rs[1]["ok"] is True and '"$NOWOK"'(rs[1]["srj"]["results"]["bindings"][0]["n"]["value"])
   and rs[2]["ok"] is True and '"$NOWOK"'(rs[2]["srj"]["results"]["bindings"][0]["n"]["value"])
   and rs[3]["ok"] is True and rs[3]["count"] == 2
   and rs[4]["ok"] is True and rs[4]["srj"]["results"]["bindings"][0]["v"]["datatype"] == "'"$XSDDT"'"
   and '"$NOWOK"'(rs[4]["srj"]["results"]["bindings"][0]["v"]["value"])'
# Negative: a different call is a different instant, not a stored one. Two
# queries in two executions need not agree; the one-execution rule is checked
# above (three rows, one value). Here the unknown handle still answers its error.
args "$TMP/now-unknown.json" "h999" 'SELECT ?n WHERE { BIND(NOW() AS ?n) }'
check "datasetQuery NOW() on an unknown handle -> error, no clock value" datasetQuery "$TMP/now-unknown.json" \
  'r["ok"] is False and "srj" not in r'

# --- NOW() on the PURE entries (https://github.com/danbri/factoidal/issues/748)
# `l4wasm-cli call` serves the IO table. `callpure` serves `L4Wasm.call`, the
# pure `l4_call` entry, which reads no clock; `callblob` serves `L4Wasm.callBlob`,
# the pure `l4_call_blob` entry. A host that meets one of these has no clock, so
# the op takes the instant as an optional last argument `now`.
#
# xverdict LABEL ISSUE OK [OUTPUT]
# OK is 1 when the check held. ISSUE empty: a plain assertion. ISSUE set: an
# expected failure for that open issue (CLAUDE.md, "A stated shortfall is a
# failing test plus an open issue"): a failed check counts as xfail and keeps
# the run green; a check that holds is an XPASS and FAILS the run, so the case
# is changed to a plain assertion and the issue closed in the same commit.
xverdict() {
  local label="$1" issue="$2" ok="$3" out="${4:-}"
  if [ -z "$issue" ]; then
    if [ "$ok" = 1 ]; then
      echo "ok   $label"
      PASS=$((PASS + 1))
    else
      echo "FAIL $label"
      printf '     output: %s\n' "$out"
      FAIL=$((FAIL + 1))
    fi
  elif [ "$ok" = 1 ]; then
    echo "FAIL $label"
    echo "     XPASS: expected to fail until https://github.com/danbri/factoidal/issues/$issue is fixed, and it passes"
    echo "     make it a plain assertion (ISSUE empty) and close the issue"
    FAIL=$((FAIL + 1))
  else
    echo "xfail $label (https://github.com/danbri/factoidal/issues/$issue)"
    printf '     output: %s\n' "$out"
    XFAIL=$((XFAIL + 1))
  fi
}

# checkpure <label> <issue> <op> <argsfile> <python-assert-expr>
# Like `check`, through the PURE entry `L4Wasm.call`.
checkpure() {
  local label="$1" issue="$2" op="$3" argsfile="$4" expr="$5"
  local out ok=0
  out="$("$CLI" callpure "$op" "$argsfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
" 2>/dev/null; then ok=1; fi
  xverdict "$label" "$issue" "$ok" "$out"
}

# W3C functions/now01.rq on W3C functions/data.ttl, through the pure entry.
# The data is Turtle; the op reads N-Quads, so the parse op converts it. The
# arguments are the data, the query, an empty base IRI and the instant `now`.
W3C_FUNCTIONS="$LEAN_DIR/../../third_party/testing/w3c/sparql/sparql11/functions"
if [ -r "$W3C_FUNCTIONS/now01.rq" ] && [ -r "$W3C_FUNCTIONS/data.ttl" ]; then
  python3 - "$TMP/w3c-fn-parse.json" "$W3C_FUNCTIONS/data.ttl" <<'PYEOF'
import json, sys
with open(sys.argv[2], encoding="utf-8") as f:
    ttl = f.read()
with open(sys.argv[1], "w") as f:
    json.dump([ttl, "turtle", ""], f)
PYEOF
  "$CLI" call parseToDatasetJson "$TMP/w3c-fn-parse.json" >"$TMP/w3c-fn-nq.json"
  python3 - "$TMP/w3c-fn-nq.json" "$W3C_FUNCTIONS/now01.rq" "$TMP/w3c-now01.json" <<'PYEOF'
import json, sys
nq = json.load(open(sys.argv[1]))
assert nq["ok"] is True, nq
with open(sys.argv[2], encoding="utf-8") as f:
    rq = f.read()
with open(sys.argv[3], "w") as f:
    json.dump([nq["nquads"], rq, "", "2026-10-10T12:34:56.789Z"], f)
PYEOF
  checkpure "pure call queryDataset, W3C functions/now01.rq with the now argument -> true" "" \
    queryDataset "$TMP/w3c-now01.json" \
    'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'
else
  echo "FAIL W3C functions/now01.rq and data.ttl are missing under third_party/testing/w3c (run tools/ensure-test-env.sh)"
  FAIL=$((FAIL + 1))
fi

# The `l4block-*` query tools read the clock once per query through
# `L4Wasm.Ops.emptyEnvNow`. Method: a regular-expression scan of the Harness
# sources for `emptyEnv`, the environment with no clock (a tool that evaluates a
# user query with it answers NOW() as an error). The scan cannot see an
# environment built another way, such as `{}`; tools/blockengine-ibk4-quad-smoke.sh
# runs W3C functions/now01.rq through one tool for that reason.
# grep exits 1 when nothing matches (the expected result) and 2 on an error.
EMPTYENV_RC=0
EMPTYENV_USES="$(grep -n '\bemptyEnv\b' "$LEAN_DIR"/Harness/*.lean)" || EMPTYENV_RC=$?
xverdict "no Harness query tool builds emptyEnv (every one reads the clock through emptyEnvNow)" "" \
  "$( [ "$EMPTYENV_RC" -eq 1 ] && [ -z "$EMPTYENV_USES" ] && echo 1 || echo 0 )" "grep exit=$EMPTYENV_RC $EMPTYENV_USES"

# argsappend <argsfile> <value> — append one string to a JSON args file.
argsappend() {
  python3 - "$1" "$2" <<'PYEOF'
import json, sys
a = json.load(open(sys.argv[1]))
a.append(sys.argv[2])
json.dump(a, open(sys.argv[1], "w"))
PYEOF
}

# The instant is a plain argument of the pure entry, so the answers are exact.
# Positive: NOW() is the instant given, an xsd:dateTime. Negative: no instant, or
# an empty one, leaves NOW() an error; another instant gives another answer; an
# instant that is not an xsd:dateTime lexical form is an error, never "none".
NOWFIXED='2026-10-10T12:34:56.789Z'
NOWASK='ASK { BIND(NOW() AS ?n) FILTER(DATATYPE(?n) = <http://www.w3.org/2001/XMLSchema#dateTime>) }'
NOWSEL='SELECT ?n WHERE { BIND(NOW() AS ?n) }'
args "$TMP/pure-now-sel.json" "$DATA" "$NOWSEL" "" "$NOWFIXED"
checkpure "pure call queryDataset binds NOW() to the instant it is given" "" queryDataset "$TMP/pure-now-sel.json" \
  'r["ok"] is True and r["srj"]["results"]["bindings"][0]["n"]["value"] == "'"$NOWFIXED"'"
   and r["srj"]["results"]["bindings"][0]["n"]["datatype"] == "'"$XSDDT"'"'
args "$TMP/pure-now-other.json" "$DATA" "$NOWSEL" "" "2000-01-01T00:00:00Z"
checkpure "pure call queryDataset: another instant gives another answer" "" queryDataset "$TMP/pure-now-other.json" \
  'r["ok"] is True and r["srj"]["results"]["bindings"][0]["n"]["value"] == "2000-01-01T00:00:00Z"'
args "$TMP/pure-now-base.json" "$DATA" 'SELECT ?x ?n WHERE { BIND(<rel> AS ?x) BIND(NOW() AS ?n) }' "http://e/b/" "$NOWFIXED"
checkpure "pure call queryDataset takes the base IRI and the instant together" "" queryDataset "$TMP/pure-now-base.json" \
  'r["ok"] is True and r["srj"]["results"]["bindings"][0]["x"]["value"] == "http://e/b/rel"
   and r["srj"]["results"]["bindings"][0]["n"]["value"] == "'"$NOWFIXED"'"'
args "$TMP/pure-now-none.json" "$DATA" "$NOWASK"
checkpure "pure call queryDataset with no instant: NOW() is an error, ASK is false" "" queryDataset "$TMP/pure-now-none.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is False'
args "$TMP/pure-now-empty.json" "$DATA" "$NOWASK" "" ""
checkpure "pure call queryDataset with an empty instant means none: ASK is false" "" queryDataset "$TMP/pure-now-empty.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is False'
for BADNOW in yesterday 2026-10-10 2026-02-30T00:00:00Z ' 2026-10-10T12:34:56Z'; do
  args "$TMP/pure-now-bad.json" "$DATA" "$NOWASK" "" "$BADNOW"
  checkpure "pure call queryDataset with the instant '$BADNOW' -> error, no answer" "" queryDataset "$TMP/pure-now-bad.json" \
    'r["ok"] is False and "not an xsd:dateTime lexical form" in r["error"] and "boolean" not in r'
done
args "$TMP/pure-now-arity.json" "$DATA" "$NOWASK" "" "$NOWFIXED" "extra"
checkpure "pure call queryDataset with five arguments -> arity error" "" queryDataset "$TMP/pure-now-arity.json" \
  'r["ok"] is False and "expects 2, 3 or 4 arguments" in r["error"]'
args "$TMP/pure-now-upd.json" "$DATA" \
  'INSERT { <http://e/a> <http://e/at> ?n } WHERE { BIND(NOW() AS ?n) }' "" "$NOWFIXED"
checkpure "pure call updateDataset inserts the instant it is given" "" updateDataset "$TMP/pure-now-upd.json" \
  'r["ok"] is True and "<http://e/a> <http://e/at> \"'"$NOWFIXED"'\"^^<'"$XSDDT"'> ." in r["nquads"]'
args "$TMP/pure-now-upd-none.json" "$DATA" \
  'INSERT { <http://e/a> <http://e/at> ?n } WHERE { BIND(NOW() AS ?n) }'
checkpure "pure call updateDataset with no instant inserts nothing" "" updateDataset "$TMP/pure-now-upd-none.json" \
  'r["ok"] is True and "<http://e/at>" not in r["nquads"]'
args "$TMP/pure-now-upd-bad.json" "$DATA" \
  'INSERT { <http://e/a> <http://e/at> ?n } WHERE { BIND(NOW() AS ?n) }' "" "soon"
checkpure "pure call updateDataset with a bad instant -> error, no dataset" "" updateDataset "$TMP/pure-now-upd-bad.json" \
  'r["ok"] is False and "not an xsd:dateTime lexical form" in r["error"] and "nquads" not in r'
args "$TMP/pure-now-raw.json" "$DATA3" "$NOWSEL" '{"dataFormat":"ntriples","output":"csv"}' "$NOWFIXED"
checkpure "pure call queryRaw binds NOW() to the instant it is given" "" queryRaw "$TMP/pure-now-raw.json" \
  'r["ok"] is True and r["text"].split("\r\n")[1] == "'"$NOWFIXED"'"'
args "$TMP/pure-now-raw-none.json" "$DATA3" "$NOWSEL" '{"dataFormat":"ntriples","output":"csv"}'
checkpure "pure call queryRaw with no instant leaves the NOW() column empty" "" queryRaw "$TMP/pure-now-raw-none.json" \
  'r["ok"] is True and r["text"].split("\r\n")[1] == ""'
args "$TMP/pure-now-raw-bad.json" "$DATA3" "$NOWSEL" '{"dataFormat":"ntriples","output":"csv"}' "soon"
checkpure "pure call queryRaw with a bad instant -> error" "" queryRaw "$TMP/pure-now-raw-bad.json" \
  'r["ok"] is False and "not an xsd:dateTime lexical form" in r["error"]'
# The pure byte-region entry delegates the other ops to the pure call.
: > "$TMP/empty.blob"
checkblob "pure callBlob queryDataset binds NOW() to the instant it is given" queryDataset \
  "$TMP/pure-now-sel.json" "$TMP/empty.blob" \
  'r["ok"] is True and r["srj"]["results"]["bindings"][0]["n"]["value"] == "'"$NOWFIXED"'"'

# --- Stateless block-worker family ----------------------------------
# Generate the fixture with the same Lean publisher used by native stores;
# the test therefore crosses the dispatch boundary with a real current-format
# artifact rather than a hand-authored byte string.
printf '%s\n' '<http://e/a> <http://e/p> <http://e/b> .' >"$TMP/block.ttl"
"$PACK" "$TMP/block.ttl" "$TMP/block-store" ibk3 >/dev/null
python3 - "$TMP/block-store/predicate-0.ibk3" "$TMP/block-ibk3.json" <<'EOF'
import json, pathlib, sys
block = pathlib.Path(sys.argv[1]).read_bytes().hex()
pathlib.Path(sys.argv[2]).write_text(json.dumps([block, "http://e/p", "source:native-smoke"]))
EOF
check "scanIBK3Predicate current artifact" scanIBK3Predicate "$TMP/block-ibk3.json" \
  'r["ok"] is True and r["format"] == "IBK3"
   and r["blankNodeScope"] == "source:native-smoke" and r["rows"] == 1
   and "<http://e/a> <http://e/p> <http://e/b> ." in r["ntriples"]'

args "$TMP/block-ibk3-bad.json" "00" "http://e/p" "source:native-smoke"
check "scanIBK3Predicate corrupt artifact -> error" scanIBK3Predicate "$TMP/block-ibk3-bad.json" \
  'r["ok"] is False and "invalid or corrupt canonical IBK3" in r["error"]'

args "$TMP/block-ibk3-noscope.json" "00" "http://e/p" ""
check "scanIBK3Predicate requires blank-node scope" scanIBK3Predicate "$TMP/block-ibk3-noscope.json" \
  'r["ok"] is False and "blankNodeScope must be non-empty" in r["error"]'

# Bounded block-set preview: blocks stay inside Lean, no N-Triples round trip.
python3 - "$TMP/block-store/predicate-0.ibk3" "$TMP/block-set.json" "$TMP/block-set-nolimit.json" <<'EOF'
import json, pathlib, sys
block = pathlib.Path(sys.argv[1]).read_bytes().hex()
blocks = json.dumps([["http://e/p", block]])
pathlib.Path(sys.argv[2]).write_text(json.dumps([blocks, "source:native-smoke",
  "SELECT ?s ?o WHERE { ?s <http://e/p> ?o } LIMIT 5"]))
pathlib.Path(sys.argv[3]).write_text(json.dumps([blocks, "source:native-smoke",
  "SELECT ?s ?o WHERE { ?s <http://e/p> ?o }"]))
EOF
check "queryIBK3BlockSetPreview bounded select" queryIBK3BlockSetPreview "$TMP/block-set.json" \
  'r["ok"] is True and r["kind"] == "select"
   and len(r["srj"]["results"]["bindings"]) == 1
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'
check "queryIBK3BlockSetPreview requires LIMIT" queryIBK3BlockSetPreview "$TMP/block-set-nolimit.json" \
  'r["ok"] is False and "require LIMIT" in r["error"]'

# DESCRIBE over the block set: a subgraph of the decoded set, so no LIMIT.
python3 - "$TMP/block-store/predicate-0.ibk3" "$TMP/block-set-describe.json" "$TMP/block-set-describe-bgp.json" <<'EOF'
import json, pathlib, sys
block = pathlib.Path(sys.argv[1]).read_bytes().hex()
blocks = json.dumps([["http://e/p", block]])
pathlib.Path(sys.argv[2]).write_text(json.dumps([blocks, "source:native-smoke",
  "DESCRIBE <http://e/a>"]))
pathlib.Path(sys.argv[3]).write_text(json.dumps([blocks, "source:native-smoke",
  "DESCRIBE ?s WHERE { ?s <http://e/p> ?o }"]))
EOF
check "queryIBK3BlockSetPreview DESCRIBE by IRI" queryIBK3BlockSetPreview "$TMP/block-set-describe.json" \
  'r["ok"] is True and r["kind"] == "describe"
   and "<http://e/a> <http://e/p> <http://e/b> ." in r["nquads"]'
check "queryIBK3BlockSetPreview DESCRIBE of a bound variable" queryIBK3BlockSetPreview "$TMP/block-set-describe-bgp.json" \
  'r["ok"] is True and r["kind"] == "describe" and r["nquads"].count(" .") == 1'

# --- Shardborough store family (manifest inspect / plan / query) ------
# The WASM module has no file system, so a JavaScript host reads the files.
# These three ops are what keep the host from having to understand any of
# them: it carries bytes by name, and every decision stays in Lean.
#
# Fixtures come from the same Lean publisher a native store uses, so the
# manifest bytes, the digests and the block bytes are the real ones.
REPO_ROOT="$(cd "$LEAN_DIR/../.." && pwd)"

printf '%s\n' \
  '<http://e/a> <http://e/p> <http://e/b> .' \
  '<http://e/a> <http://e/q> "one" .' \
  '<http://e/c> <http://e/p> <http://e/d> .' >"$TMP/store.ttl"
"$PACK" "$TMP/store.ttl" "$TMP/store-ibk3" ibk3 >/dev/null

# One predicate per line, 65 of them: enough entries that a full-manifest
# plan trips the 64-artifact cap without any large file.
python3 - "$TMP/wide.ttl" <<'EOF'
import sys
with open(sys.argv[1], "w") as f:
    for i in range(65):
        f.write(f"<http://e/s> <http://e/p{i}> <http://e/o{i}> .\n")
EOF
"$PACK" "$TMP/wide.ttl" "$TMP/store-wide" ibk3 >/dev/null

"$PACK" "$REPO_ROOT/tests/local/data/quad_sample.trig" "$TMP/store-ibk4" ibk4 >/dev/null

# The IBK4 N-Quads pack streams (PackStream.quadIngestFeed) on BOTH surfaces:
# the native CLI reads the file in chunks, the pack ops take the chunks from
# the host. Neither buffers the source. A routing change that made only one of
# them stream would still pass every other check here, so the gate is a byte
# comparison of the two generations, not a count.
#
# Both routes now also PUBLISH during the ingest pass
# (docs/designissues/2026-09-05-pack-publication-every-batch.md), so the block
# SET depends on the publication batch as well as on the source. The two
# defaults differ -- 268,435,456 source bytes on the native CLI, 67,108,864 in
# the module, which has a 32-bit address space -- so a byte comparison is only
# meaningful below the smaller of them. This fixture is five lines, so neither
# route reaches a batch end and both publish under rules 2 and 5 alone. A
# fixture above 64 MiB would need --batch-bytes on the CLI and the fourth
# packBegin argument in the module, set to the same number.
#
# The block set of this fixture is unchanged by that landing, and by the
# 2026-09-05 change to (predicate, graph) buckets: <http://e/p> has rows in
# the default graph and in g1, which is two blocks under either rule, and the
# first-seen key order is the order the old predicate-major route used here.
printf '%s\n' \
  '<http://e/a> <http://e/p> "x" .' \
  '<http://e/a> <http://e/p> "y" <http://e/g1> .' \
  '<http://e/b> <http://e/q> "z"@en <http://e/g2> .' \
  '<http://e/c> <http://e/p> "w" <http://e/g1> .' \
  '_:b1 <http://e/q> <http://e/d> <http://e/g2> .' > "$TMP/quads.nq"
"$PACK" "$TMP/quads.nq" "$TMP/store-nq-cli" ibk4 >/dev/null
"$CLI" pack "$TMP/quads.nq" "$TMP/store-nq-ops" nquads ibk4 >/dev/null
if diff -r "$TMP/store-nq-cli" "$TMP/store-nq-ops" >/dev/null; then
  echo "ok   pack ops and the CLI commit the same IBK4 N-Quads generation"
  PASS=$((PASS + 1))
else
  echo "FAIL pack ops and the CLI commit the same IBK4 N-Quads generation"
  DIFF_RC=0; diff -r "$TMP/store-nq-cli" "$TMP/store-nq-ops" || DIFF_RC=$?
  printf '     diff exit %s\n' "$DIFF_RC"
  FAIL=$((FAIL + 1))
fi

# storeargs <out> <manifest-file> [extra json string]... — the manifest is
# hex, so only the host's file read crosses the boundary.
storeargs() {
  local out="$1" manifest="$2"; shift 2
  python3 - "$out" "$manifest" "$@" <<'EOF'
import json, pathlib, sys
out, manifest = sys.argv[1], sys.argv[2]
argv = [pathlib.Path(manifest).read_bytes().hex()] + sys.argv[3:]
pathlib.Path(out).write_text(json.dumps(argv))
EOF
}

# blobargs <argsout> <blobout> <manifest> <sparql> <generation-dir> <key>...
# The host path: the artifacts go into ONE contiguous region with no encoding,
# and the args document describes {"key","offset","len"} windows into it.
# `--tamper` as the last key flips one byte of the region.
blobargs() {
  local argsout="$1" blobout="$2" manifest="$3" sparql="$4" dir="$5"; shift 5
  python3 - "$argsout" "$blobout" "$manifest" "$sparql" "$dir" "$@" <<'EOF'
import json, pathlib, sys
argsout, blobout, manifest, sparql, directory = sys.argv[1:6]
keys = list(sys.argv[6:])
tamper = "--tamper" in keys
if tamper:
    keys.remove("--tamper")
blob = bytearray()
descriptors = []
for key in keys:
    data = (pathlib.Path(directory) / key).read_bytes()
    descriptors.append({"key": key, "offset": len(blob), "len": len(data)})
    blob += data
if tamper and blob:
    blob[len(blob) // 2] ^= 0xFF
pathlib.Path(blobout).write_bytes(bytes(blob))
pathlib.Path(argsout).write_text(json.dumps(
    [pathlib.Path(manifest).read_bytes().hex(), sparql, json.dumps(descriptors)]))
EOF
}

# hexargs <argsout> <manifest> <sparql> <generation-dir> <key>... — the
# diagnostic {"key","bytes":"<hex>"} form, reachable through the plain `call`
# entry that carries no region. A host must not use it: it doubles the bytes
# over the boundary and walks every character on the way in.
hexargs() {
  local argsout="$1" manifest="$2" sparql="$3" dir="$4"; shift 4
  python3 - "$argsout" "$manifest" "$sparql" "$dir" "$@" <<'EOF'
import json, pathlib, sys
argsout, manifest, sparql, directory = sys.argv[1:5]
payload = [{"key": key,
            "bytes": (pathlib.Path(directory) / key).read_bytes().hex()}
           for key in sys.argv[5:]]
pathlib.Path(argsout).write_text(json.dumps(
    [pathlib.Path(manifest).read_bytes().hex(), sparql, json.dumps(payload)]))
EOF
}

storeargs "$TMP/store-inspect.json" "$TMP/store-ibk3/manifest.sbm2"
check "storeManifestInspect reports an IBK3 generation" storeManifestInspect "$TMP/store-inspect.json" \
  'r["ok"] is True and r["wireVersion"] >= 1 and r["rangeCommitted"] is True
   and "ibk3" in r["layout"] and len(r["entries"]) == 2
   and r["entries"][0]["key"].endswith(".ibk3")
   and r["entries"][0]["blockKind"] == "IBK3"
   and len(r["entries"][0]["sha256"]) == 64
   and r["entries"][0]["rows"] >= 1
   and r["entries"][0]["chunkBytes"] > 0
   and len(r["entries"][0]["merkleRoot"]) == 64
   and r["totalBytes"] > 0 and r["totalRows"] == 3'

args "$TMP/store-inspect-bad.json" "00"
check "storeManifestInspect refuses bytes that do not decode" storeManifestInspect "$TMP/store-inspect-bad.json" \
  'r["ok"] is False and "do not decode" in r["error"]'

storeargs "$TMP/store-plan-bound.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s WHERE { ?s <http://e/p> ?o }'
check "storeQueryPlan selects one shard for a constant predicate" storeQueryPlan "$TMP/store-plan-bound.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle(1)"
   and r["shards"] == 1 and len(r["keys"]) == 1 and r["bytes"] > 0 and r["rows"] == 2'

storeargs "$TMP/store-plan-open.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s WHERE { ?s ?p ?o }'
check "storeQueryPlan opens the whole manifest for an unbound predicate" storeQueryPlan "$TMP/store-plan-open.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle-full-manifest(2)"
   and r["shards"] == 2 and len(r["keys"]) == 2'

# An EXISTS outside the pattern is evaluated against the active graph
# (section 18.6), so the plan must select every entry.
storeargs "$TMP/store-plan-exists.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s (EXISTS { ?s <http://e/q> ?v } AS ?e) WHERE { ?s <http://e/p> ?o }'
check "storeQueryPlan refuses predicate selection under EXISTS" storeQueryPlan "$TMP/store-plan-exists.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle-full-manifest(2)" and r["shards"] == 2'

# DESCRIBE reads every statement about the resources it names, so no pattern
# may prune the shards. `DESCRIBE <http://e/a>` has an empty pattern, which the
# predicate collector alone would plan as zero shards, and the pattern
# `?s <http://e/p> ?o` would plan one shard and lose the `q` statement of a.
storeargs "$TMP/store-plan-describe.json" "$TMP/store-ibk3/manifest.sbm2" \
  'DESCRIBE <http://e/a>'
check "storeQueryPlan opens the whole manifest for DESCRIBE <iri>" storeQueryPlan "$TMP/store-plan-describe.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle-full-manifest(2)" and r["shards"] == 2'
storeargs "$TMP/store-plan-describe-var.json" "$TMP/store-ibk3/manifest.sbm2" \
  'DESCRIBE ?s WHERE { ?s <http://e/p> ?o }'
check "storeQueryPlan opens the whole manifest for DESCRIBE ?s WHERE" storeQueryPlan "$TMP/store-plan-describe-var.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle-full-manifest(2)" and r["shards"] == 2'

# The HOST path: one contiguous region, no encoding, offset/len windows.
blobargs "$TMP/store-query.json" "$TMP/store-query.blob" \
  "$TMP/store-ibk3/manifest.sbm2" 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' \
  "$TMP/store-ibk3" predicate-0.ibk3
checkblob "storeQuery answers over a supplied IBK3 block region" storeQuery \
  "$TMP/store-query.json" "$TMP/store-query.blob" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and r["mode"] == "ibk3-paged-merkle(1)"
   and len(r["srj"]["results"]["bindings"]) == 2'

# DESCRIBE over the same generation. The plan opens both shards, so both
# artifacts must be supplied, and the description of a holds the q statement
# that the pattern predicate alone would have left unread. Supplying only the
# p artifact is a refusal, not a partial description.
blobargs "$TMP/store-describe.json" "$TMP/store-describe.blob" \
  "$TMP/store-ibk3/manifest.sbm2" 'DESCRIBE ?s WHERE { ?s <http://e/p> <http://e/b> }' \
  "$TMP/store-ibk3" predicate-0.ibk3 predicate-1.ibk3
checkblob "storeQuery DESCRIBE reads every shard, not the pattern predicate's" storeQuery \
  "$TMP/store-describe.json" "$TMP/store-describe.blob" \
  'r["ok"] is True and r["kind"] == "describe" and r["shards"] == 2
   and r["mode"] == "ibk3-paged-merkle-full-manifest(2)"
   and r["nquads"].count(" .") == 2
   and "<http://e/a> <http://e/p> <http://e/b> ." in r["nquads"]
   and "<http://e/a> <http://e/q> \"one\" ." in r["nquads"]
   and "<http://e/c>" not in r["nquads"]'
blobargs "$TMP/store-describe-short.json" "$TMP/store-describe-short.blob" \
  "$TMP/store-ibk3/manifest.sbm2" 'DESCRIBE <http://e/a>' \
  "$TMP/store-ibk3" predicate-0.ibk3
checkblob "storeQuery DESCRIBE refuses a region that lacks a shard of the full manifest" storeQuery \
  "$TMP/store-describe-short.json" "$TMP/store-describe-short.blob" \
  'r["ok"] is False'

# The diagnostic hexadecimal form must answer exactly the same envelope, so a
# fixture written either way pins the same behaviour.
hexargs "$TMP/store-query-hex.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' "$TMP/store-ibk3" predicate-0.ibk3
check "storeQuery hexadecimal diagnostic path answers the same rows" storeQuery "$TMP/store-query-hex.json" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and len(r["srj"]["results"]["bindings"]) == 2'

# NOW() through the IO store entries (https://github.com/danbri/factoidal/issues/743):
# `storeQuery` (served by `storeQueryIO` on the IO table, the one `call` reaches)
# and `storeHandleQuery` read the clock once per query.
hexargs "$TMP/store-query-now.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s ?o ?n WHERE { ?s <http://e/p> ?o BIND(NOW() AS ?n) }' "$TMP/store-ibk3" predicate-0.ibk3
check "storeQuery NOW() is the system clock, one value for every row" storeQuery "$TMP/store-query-now.json" \
  'r["ok"] is True and len(r["srj"]["results"]["bindings"]) == 2
   and len({b["n"]["value"] for b in r["srj"]["results"]["bindings"]}) == 1
   and '"$NOWOK"'(r["srj"]["results"]["bindings"][0]["n"]["value"])'
# The pure byte-region entry (`callblob`) has no clock; `storeQuery` takes the
# instant as a fourth argument (https://github.com/danbri/factoidal/issues/748).
blobargs "$TMP/store-query-now-pure.json" "$TMP/store-query-now-pure.blob" \
  "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s ?o ?n WHERE { ?s <http://e/p> ?o BIND(NOW() AS ?n) }' "$TMP/store-ibk3" predicate-0.ibk3
cp "$TMP/store-query-now-pure.json" "$TMP/store-query-now-pure-none.json"
argsappend "$TMP/store-query-now-pure.json" "$NOWFIXED"
checkblob "storeQuery through the pure callBlob binds NOW() to the instant it is given" storeQuery \
  "$TMP/store-query-now-pure.json" "$TMP/store-query-now-pure.blob" \
  'r["ok"] is True and len(r["srj"]["results"]["bindings"]) == 2
   and all(b["n"]["value"] == "'"$NOWFIXED"'" and b["n"]["datatype"] == "'"$XSDDT"'"
           for b in r["srj"]["results"]["bindings"])'
checkblob "storeQuery through the pure callBlob with no instant leaves NOW() unbound" storeQuery \
  "$TMP/store-query-now-pure-none.json" "$TMP/store-query-now-pure.blob" \
  'r["ok"] is True and len(r["srj"]["results"]["bindings"]) == 2
   and all("n" not in b for b in r["srj"]["results"]["bindings"])'
cp "$TMP/store-query-now-pure-none.json" "$TMP/store-query-now-pure-bad.json"
argsappend "$TMP/store-query-now-pure-bad.json" "tomorrow"
checkblob "storeQuery through the pure callBlob with a bad instant -> error, no rows" storeQuery \
  "$TMP/store-query-now-pure-bad.json" "$TMP/store-query-now-pure.blob" \
  'r["ok"] is False and "not an xsd:dateTime lexical form" in r["error"] and "srj" not in r'
python3 - "$TMP/store-handle-now.json" "$TMP/store-ibk3/manifest.sbm2" "$TMP/store-ibk3" <<'EOF'
import json, pathlib, sys
out, manifest, directory = sys.argv[1:4]
manifest_hex = pathlib.Path(manifest).read_bytes().hex()
payload = json.dumps([{"key": key,
                       "bytes": (pathlib.Path(directory) / key).read_bytes().hex()}
                      for key in ["predicate-0.ibk3"]])
seq = [
  ["storeOpen",        [manifest_hex, payload]],
  ["storeHandleQuery", ["s1", "SELECT ?s ?o ?n WHERE { ?s <http://e/p> ?o BIND(NOW() AS ?n) }"]],
  ["storeHandleClose", ["s1"]],
]
json.dump(seq, open(out, "w"))
EOF
checkseq "storeHandleQuery NOW() is the system clock, one value for every row" "$TMP/store-handle-now.json" \
  'rs[1]["ok"] is True and len(rs[1]["srj"]["results"]["bindings"]) == 2
   and len({b["n"]["value"] for b in rs[1]["srj"]["results"]["bindings"]}) == 1
   and '"$NOWOK"'(rs[1]["srj"]["results"]["bindings"][0]["n"]["value"])'

# A window that runs past the end of the region the call carried is an
# ordinary refusal, not a memory fault: Lean never receives a host pointer.
python3 - "$TMP/store-query.json" "$TMP/store-query-overrun.json" <<'EOF'
import json, pathlib, sys
argv = json.loads(pathlib.Path(sys.argv[1]).read_text())
artifacts = json.loads(argv[2])
artifacts[0]["offset"] += 1
argv[2] = json.dumps(artifacts)
pathlib.Path(sys.argv[2]).write_text(json.dumps(argv))
EOF
checkblob "storeQuery refuses a window past the end of the region" storeQuery \
  "$TMP/store-query-overrun.json" "$TMP/store-query.blob" \
  'r["ok"] is False and "names blob bytes" in r["error"]'

# A digest that does not match its manifest entry refuses the whole query
# and names the key; no partially trusted generation is answered from.
blobargs "$TMP/store-query-tampered.json" "$TMP/store-query-tampered.blob" \
  "$TMP/store-ibk3/manifest.sbm2" 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' \
  "$TMP/store-ibk3" predicate-0.ibk3 --tamper
checkblob "storeQuery refuses an artifact whose SHA-256 differs" storeQuery \
  "$TMP/store-query-tampered.json" "$TMP/store-query-tampered.blob" \
  'r["ok"] is False and "predicate-0.ibk3" in r["error"] and "SHA-256" in r["error"]'

storeargs "$TMP/store-query-missing.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' '[]'
check "storeQuery refuses a plan whose bytes were not supplied" storeQuery "$TMP/store-query-missing.json" \
  'r["ok"] is False and "no bytes were supplied for artifact" in r["error"]'

# Cap trip: 65 predicates, so the full-manifest plan needs 65 artifacts and
# the cap is 64. The refusal names the cap and the value that exceeded it.
storeargs "$TMP/store-query-cap.json" "$TMP/store-wide/manifest.sbm2" \
  'SELECT ?s WHERE { ?s ?p ?o }' '[]'
check "storeQuery refuses a plan over the artifact cap" storeQuery "$TMP/store-query-cap.json" \
  'r["ok"] is False and "selects 65 artifacts" in r["error"] and "cap is 64" in r["error"]'

# The same manifest still PLANS: the caps belong to storeQuery, so a host can
# see what a query would cost before it fetches anything.
storeargs "$TMP/store-plan-cap.json" "$TMP/store-wide/manifest.sbm2" \
  'SELECT ?s WHERE { ?s ?p ?o }'
check "storeQueryPlan reports a plan the query cap would refuse" storeQueryPlan "$TMP/store-plan-cap.json" \
  'r["ok"] is True and r["shards"] == 65'

# --- The same three ops over an SBM8 generation of IBK4 quad blocks ---
#
# SBM8 is SBM7 plus the LGI3 literal search index in a fourth sidecar role,
# which is what `l4block-shard-pack ... ibk4` now writes. SBM7 generations
# still decode and still answer; `tests/store-host/conformance.mjs` and
# `l4block-literal-gate` cover an SBM7 store that declares no sidecar.
# The g1 block is entry 2, not entry 1: since 2026-09-05 the packer buckets by
# the pair (predicate, graph) and publishes in first-seen KEY order, so the
# default-graph `knows` bucket takes ordinal 1 and the g1 `name` bucket takes
# ordinal 2. The four blocks and their rows are unchanged — this fixture's
# graphs are not interleaved — only the order.
storeargs "$TMP/store-inspect-ibk4.json" "$TMP/store-ibk4/manifest.sbm2"
check "storeManifestInspect reports an IBK4 generation and its graph set" storeManifestInspect "$TMP/store-inspect-ibk4.json" \
  'r["ok"] is True and r["wireVersion"] == 9
   and r["layout"] == "quad-ibk4-ptd1-lgi3-gbi1-merkle-v0"
   and r["blankNodeProfile"] == "content-digest-shared"
   and len(r["entries"]) == 4
   and r["entries"][0]["blockKind"] == "IBK4"
   and r["entries"][0]["sidecars"]["literalIndex"] == "predicate-0.ibk4.lgi3"
   and len(r["entries"][0]["blankNodeScope"]) > 0
   and all(len(e["graphs"]) == 1 for e in r["entries"])
   and all(e["sidecars"]["literalIndex"] == e["key"] + ".lgi3" for e in r["entries"])
   and all(e["sidecars"]["geoIndex"] == e["key"] + ".gbi1" for e in r["entries"])
   and [g["kind"] for g in r["entries"][0]["graphs"]][0] == "default"
   and [g["value"] for g in r["entries"][2]["graphs"]] == ["http://example.org/g1"]'

storeargs "$TMP/store-plan-ibk4.json" "$TMP/store-ibk4/manifest.sbm2" \
  'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }'
check "storeQueryPlan selects IBK4 entries by graph set" storeQueryPlan "$TMP/store-plan-ibk4.json" \
  'r["ok"] is True and r["mode"] == "ibk4-full-manifest(1)" and r["shards"] == 1
   and r["keys"] == ["predicate-2.ibk4"]
   and r["sidecarKeys"] == ["predicate-2.ibk4.lgi3", "predicate-2.ibk4.gbi1"]'

blobargs "$TMP/store-query-ibk4.json" "$TMP/store-query-ibk4.blob" \
  "$TMP/store-ibk4/manifest.sbm2" \
  'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }' \
  "$TMP/store-ibk4" predicate-2.ibk4
checkblob "storeQuery answers a GRAPH clause over a supplied IBK4 block region" storeQuery \
  "$TMP/store-query-ibk4.json" "$TMP/store-query-ibk4.blob" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and r["mode"] == "ibk4-full-manifest(1)"
   and len(r["srj"]["results"]["bindings"]) == 2'

# --- The same operations over an SBM10 generation of IBK5 quad blocks ---
#
# Wire version 10 (docs/designissues/2026-09-05-wire-version-10-scale.md).
# The fixture holds the four term shapes version 9 cannot store: an RDF 1.2
# triple term, a directional literal, a 70,000-byte literal and a
# 68,226-byte geometry. The last two are above maxInlineLexicalBytes, so they
# are OUT OF LINE: one `blob-<sha256 hex>.lit` artifact each, named in the
# manifest blob table, and the block holds only their extent and digest.
"$PACK" "$REPO_ROOT/tests/local/data/rdf12_sample.trig" "$TMP/store-ibk5" ibk5 >/dev/null

# The blob file names are content addresses, so they are read from the
# generation rather than written here.
IBK5_BLOBS=$(cd "$TMP/store-ibk5" && ls blob-*.lit)
# The block that holds ex:big, looked up by predicate in the TSV rather than
# assumed by ordinal: the packer publishes buckets in first-occurrence order
# of (predicate, graph), and a fixture edit or a policy change moves ordinals
# without moving the answer this gate is about.
IBK5_BIG=$(awk -F'\t' '$2=="http://example.org/big" {print $3; exit}' "$TMP/store-ibk5/manifest.tsv")
test -n "$IBK5_BIG"
# shellcheck disable=SC2086
set -- $IBK5_BLOBS
BLOB_GEO="$1"
BLOB_BIG="$2"

storeargs "$TMP/store-inspect-ibk5.json" "$TMP/store-ibk5/manifest.sbm2"
check "storeManifestInspect reports an IBK5 generation, its zone maps and its blob table" \
  storeManifestInspect "$TMP/store-inspect-ibk5.json" \
  'r["ok"] is True and r["wireVersion"] == 10
   and r["layout"] == "quad-ibk5-ptd2-lgi4-gbi1-merkle-v0"
   and len(r["entries"]) == 5
   and all(e["blockKind"] == "IBK5" for e in r["entries"])
   and all(e["sidecars"]["literalIndex"] == e["key"] + ".lgi4" for e in r["entries"])
   and all(len(e["subjectZone"]["min"]) % 2 == 0 for e in r["entries"])
   and all(e["subjectZone"]["min"] <= e["subjectZone"]["max"] for e in r["entries"])
   and all(e["objectZone"]["min"] <= e["objectZone"]["max"] for e in r["entries"])
   and len(r["blobs"]) == 2
   and all(b["key"].startswith("blob-") and b["key"].endswith(".lit") for b in r["blobs"])
   and all(b["key"] == "blob-" + b["sha256"] + ".lit" for b in r["blobs"])
   and sorted(b["bytes"] for b in r["blobs"]) == [68226, 70000]
   and [e["blobRefs"] for e in r["entries"] if "blobRefs" in e]
       == [[r["blobs"][1]["key"]], [r["blobs"][0]["key"]]]'

# The plan names the blob artifacts the selected entries refer to, AFTER the
# block keys and the sidecar keys, so a host fetches everything one query can
# touch without decoding a block.
storeargs "$TMP/store-plan-ibk5.json" "$TMP/store-ibk5/manifest.sbm2" \
  'SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } BIND(STRLEN(?o) AS ?n) }'
check "storeQueryPlan lists the blob keys an IBK5 plan reaches" storeQueryPlan \
  "$TMP/store-plan-ibk5.json" \
  'r["ok"] is True and r["mode"] == "ibk5-full-manifest(1)" and r["shards"] == 1
   and r["keys"] == ["'"$IBK5_BIG"'"]
   and r["sidecarKeys"] == ["'"$IBK5_BIG"'.lgi4", "'"$IBK5_BIG"'.gbi1"]
   and len(r["blobKeys"]) == 1
   and r["blobKeys"][0].startswith("blob-") and r["blobKeys"][0].endswith(".lit")
   and r["bytes"] > 70000
   and r["zoneExcluded"] == 0'

# The zone maps. A constant subject outside every block's subject range is
# dropped by the manifest alone, with no block read at all.
storeargs "$TMP/store-plan-ibk5-zone.json" "$TMP/store-ibk5/manifest.sbm2" \
  'SELECT ?o WHERE { GRAPH ?g { <http://example.org/zzzz> <http://example.org/label> ?o } }'
check "storeQueryPlan drops IBK5 entries by their zone maps" storeQueryPlan \
  "$TMP/store-plan-ibk5-zone.json" \
  'r["ok"] is True and r["shards"] == 0 and r["keys"] == []
   and r["zoneExcluded"] == 2'

# A subject the corpus HAS is kept, and the zone maps drop the other entry of
# the same predicate.
storeargs "$TMP/store-plan-ibk5-hit.json" "$TMP/store-ibk5/manifest.sbm2" \
  'SELECT ?o WHERE { GRAPH ?g { <http://example.org/s5> <http://example.org/label> ?o } }'
check "storeQueryPlan keeps the IBK5 entry whose zone map holds the subject" storeQueryPlan \
  "$TMP/store-plan-ibk5-hit.json" \
  'r["ok"] is True and r["shards"] == 1 and r["zoneExcluded"] == 1'

# The 70,000-byte literal, read through its blob artifact. STRLEN is over the
# RESOLVED lexical form, so a wrong or absent blob cannot answer it.
blobargs "$TMP/store-query-ibk5.json" "$TMP/store-query-ibk5.blob" \
  "$TMP/store-ibk5/manifest.sbm2" \
  'SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } BIND(STRLEN(?o) AS ?n) }' \
  "$TMP/store-ibk5" "$IBK5_BIG" "$BLOB_BIG"
checkblob "storeQuery resolves an out-of-line literal the host supplied" storeQuery \
  "$TMP/store-query-ibk5.json" "$TMP/store-query-ibk5.blob" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and r["mode"] == "ibk5-full-manifest(1)"
   and r["srj"]["results"]["bindings"][0]["n"]["value"] == "70000"'

# Without the blob the query is REFUSED by name; it is never answered with a
# fabricated or truncated literal.
blobargs "$TMP/store-query-ibk5-noblob.json" "$TMP/store-query-ibk5-noblob.blob" \
  "$TMP/store-ibk5/manifest.sbm2" \
  'SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } BIND(STRLEN(?o) AS ?n) }' \
  "$TMP/store-ibk5" "$IBK5_BIG"
checkblob "storeQuery refuses an IBK5 block whose blob was not supplied" storeQuery \
  "$TMP/store-query-ibk5-noblob.json" "$TMP/store-query-ibk5-noblob.blob" \
  'r["ok"] is False and "no bytes were supplied for artifact" in r["error"]
   and ".lit" in r["error"]'

# The RDF 1.2 triple term survives the round trip through the block.
blobargs "$TMP/store-query-ibk5-tt.json" "$TMP/store-query-ibk5-tt.blob" \
  "$TMP/store-ibk5/manifest.sbm2" \
  'SELECT ?o WHERE { <http://example.org/s1> <http://example.org/says> ?o }' \
  "$TMP/store-ibk5" predicate-0.ibk5
checkblob "storeQuery answers a triple term from an IBK5 block" storeQuery \
  "$TMP/store-query-ibk5-tt.json" "$TMP/store-query-ibk5-tt.blob" \
  'r["ok"] is True and r["srj"]["results"]["bindings"][0]["o"]["type"] == "triple"
   and r["srj"]["results"]["bindings"][0]["o"]["value"]["object"]["value"]
       == "http://example.org/b"'

# activateVerify over the whole SBM10 generation: the blob table as well as
# the blocks and their two sidecars, through the same GenerationVerify path
# l4block-shard-activate takes.
python3 - "$TMP/store-ibk5" "$TMP/activate-ibk5.json" "$TMP/activate-ibk5.blob" <<'EOF'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
# Every child except the manifest itself: activation checks the `.merkle`
# leaf sidecars beside the artifacts they commit.
names = sorted(p.name for p in directory.iterdir()
               if not p.name.startswith('manifest.'))
blob = bytearray()
descriptors = []
for name in names:
    data = (directory / name).read_bytes()
    descriptors.append({"key": name, "offset": len(blob), "len": len(data)})
    blob += data
pathlib.Path(sys.argv[3]).write_bytes(bytes(blob))
pathlib.Path(sys.argv[2]).write_text(json.dumps(
    [(directory / 'manifest.sbm2').read_bytes().hex(), json.dumps(descriptors)]))
EOF
checkblob "activateVerify admits an SBM10 generation with its blob table" activateVerify \
  "$TMP/activate-ibk5.json" "$TMP/activate-ibk5.blob" \
  'r["ok"] is True and r["artifacts"] == 34 and r["bytes"] > 138000'

# The same region without the blob artifacts is refused: a generation whose
# out-of-line literals are absent is not activated.
python3 - "$TMP/activate-ibk5.json" "$TMP/activate-ibk5-noblob.json" <<'EOF'
import json, pathlib, sys
argv = json.loads(pathlib.Path(sys.argv[1]).read_text())
kept = [d for d in json.loads(argv[1]) if not d["key"].startswith("blob-")]
argv[1] = json.dumps(kept)
pathlib.Path(sys.argv[2]).write_text(json.dumps(argv))
EOF
checkblob "activateVerify refuses an SBM10 generation whose blobs are absent" activateVerify \
  "$TMP/activate-ibk5-noblob.json" "$TMP/activate-ibk5.blob" \
  'r["ok"] is False and "blob artifact" in r["error"]'

# A handle over the whole SBM10 generation: the blobs are resolved ONCE at
# storeOpen, and both candidate-filter paths must keep an out-of-line literal
# in their candidate set. A CONTAINS needle inside the 70,000-byte literal has
# no gram in the block, and the 68,226-byte polygon has no bounding box in
# GBI1; without BlockV5Plan's opaque union each of these answers zero rows.
python3 - "$TMP/store-ibk5" "$TMP/store-ibk5-seq.json" <<'EOF'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
names = sorted(p.name for p in directory.iterdir()
               if not p.name.startswith('manifest.') and not p.name.endswith('.merkle'))
payload = json.dumps([{"key": name, "bytes": (directory / name).read_bytes().hex()}
                      for name in names])
manifest = (directory / 'manifest.sbm2').read_bytes().hex()
needle = ('SELECT ?s WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } '
          'FILTER(CONTAINS(?o, "needle")) }')
geo = ('SELECT ?s WHERE { GRAPH ?g { ?s '
       '<http://www.opengis.net/ont/geosparql#asWKT> ?o } FILTER('
       '<http://www.opengis.net/def/function/geosparql/sfIntersects>(?o, '
       '"POINT(5 5)"^^<http://www.opengis.net/ont/geosparql#wktLiteral>)) }')
length = ('SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } '
          'BIND(STRLEN(?o) AS ?n) }')
pathlib.Path(sys.argv[2]).write_text(json.dumps([
    ["storeOpen", [manifest, payload]],
    ["storeHandleQuery", ["s1", needle]],
    ["storeHandleQuery", ["s1", geo]],
    ["storeHandleQuery", ["s1", length]],
    ["storeHandleClose", ["s1"]]]))
EOF
checkseq "store handle: an IBK5 generation, its blobs resolved once at open" \
  "$TMP/store-ibk5-seq.json" \
  'rs[0]["ok"] is True and rs[0]["wireVersion"] == 10 and rs[0]["blobs"] == 2
   and rs[0]["artifacts"] == 5
   and rs[1]["ok"] is True
   and [b["s"]["value"] for b in rs[1]["srj"]["results"]["bindings"]]
       == ["http://example.org/s3"]
   and rs[2]["ok"] is True
   and [b["s"]["value"] for b in rs[2]["srj"]["results"]["bindings"]]
       == ["http://example.org/s4"]
   and rs[3]["srj"]["results"]["bindings"][0]["n"]["value"] == "70000"
   and rs[4]["ok"] is True'

# An open that leaves a blob out is refused, by name, before any query.
python3 - "$TMP/store-ibk5" "$TMP/store-ibk5-noblob-seq.json" <<'EOF'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
names = sorted(p.name for p in directory.iterdir()
               if not p.name.startswith('manifest.') and not p.name.endswith('.merkle')
               and not p.name.startswith('blob-'))
payload = json.dumps([{"key": name, "bytes": (directory / name).read_bytes().hex()}
                      for name in names])
pathlib.Path(sys.argv[2]).write_text(json.dumps([
    ["storeOpen", [(directory / 'manifest.sbm2').read_bytes().hex(), payload]]]))
EOF
checkseq "storeOpen refuses an IBK5 generation whose blobs were not supplied" \
  "$TMP/store-ibk5-noblob-seq.json" \
  'rs[0]["ok"] is False and "no bytes were supplied for artifact" in rs[0]["error"]
   and ".lit" in rs[0]["error"]'

# --- The literal index under the Unicode fold (LGI3 and LGI4, 2026-10-10) ---
#
# `CONTAINS(LCASE(STR(?o)), "école")` keeps `École Normale`, because LCASE is
# the Unicode case mapping. The index must list that row as a candidate, so it
# folds with `Text.CaseMap.searchFold` and not with the ASCII-only
# `String.toLower`. Each case opens ONE handle with the literal and geometry
# sidecars and ONE without them, asks the same query of both, and compares the
# whole answer envelopes. The assertion also reads `literalIndexes` from the two
# open envelopes: a sidecar that failed to decode would fall back to the scan,
# and two scans always agree. The expected rows are written out, so an index
# that is wrong in the same way as the scan fails too.
for UNI_FORMAT in ibk4 ibk5; do
  "$PACK" "$REPO_ROOT/tests/local/data/unicode_label_sample.trig" "$TMP/store-uni-$UNI_FORMAT" "$UNI_FORMAT" >/dev/null
  python3 - "$TMP/store-uni-$UNI_FORMAT" "$TMP/store-uni-$UNI_FORMAT-seq.json" "$UNI_FORMAT" <<'EOF'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
fmt = sys.argv[3]
block = "predicate-0." + fmt
names = sorted(p.name for p in directory.iterdir()
               if not p.name.startswith('manifest.') and not p.name.endswith('.merkle'))
def payload(keys):
    return json.dumps([{"key": key, "bytes": (directory / key).read_bytes().hex()}
                       for key in keys])
manifest = (directory / 'manifest.sbm2').read_bytes().hex()
needles = ["école", "ecole", "kelvin", "stanbul", "οδυσσευς",
           "straße", "plain", "unmatched"]
def query(needle):
    return ('SELECT ?s ?o WHERE { GRAPH ?g { ?s <http://www.w3.org/2000/01/rdf-schema#label> ?o '
            'FILTER(CONTAINS(LCASE(STR(?o)), "' + needle + '")) } } ORDER BY ?s ?o')
seq = [["storeOpen", [manifest, payload(names)]],
       ["storeOpen", [manifest, payload([block])]]]
for needle in needles:
    seq.append(["storeHandleQuery", ["s1", query(needle)]])
    seq.append(["storeHandleQuery", ["s2", query(needle)]])
json.dump(seq, open(sys.argv[2], "w"))
EOF
  checkseq "literal index under the Unicode fold: $UNI_FORMAT, index handle answers as the scan handle" \
    "$TMP/store-uni-$UNI_FORMAT-seq.json" \
    'rs[0]["ok"] is True and rs[0]["literalIndexes"] == 1
     and rs[1]["ok"] is True and rs[1]["literalIndexes"] == 0
     and all(rs[2 + 2 * i]["ok"] is True and rs[2 + 2 * i] == rs[3 + 2 * i] for i in range(8))
     and [[b["s"]["value"] for b in rs[2 + 2 * i]["srj"]["results"]["bindings"]]
          for i in range(8)]
       == [["http://example.org/s1"], ["http://example.org/s7"], ["http://example.org/s2"],
           ["http://example.org/s3"], ["http://example.org/s4"], ["http://example.org/s5"],
           ["http://example.org/s6"], []]'
done

# The sidecars carry the new names. Their first four bytes are the magic.
LGI3_MAGIC=$(head -c 4 "$TMP/store-uni-ibk4/predicate-0.ibk4.lgi3")
LGI4_MAGIC=$(head -c 4 "$TMP/store-uni-ibk5/predicate-0.ibk5.lgi4")
if [ "$LGI3_MAGIC" = "LGI3" ] && [ "$LGI4_MAGIC" = "LGI4" ]; then
  echo "ok   the packer writes LGI3 for wire version 9 and LGI4 for wire version 10"
  PASS=$((PASS + 1))
else
  echo "FAIL the packer writes LGI3 for wire version 9 and LGI4 for wire version 10"
  printf '     magic %s and %s\n' "$LGI3_MAGIC" "$LGI4_MAGIC"
  FAIL=$((FAIL + 1))
fi

# A manifest packed under the ASCII-only fold names LGI1 or LGI2 in its layout
# label. The label is the only byte of the manifest this test changes (the new
# and the retired spellings have the same length), so every length and
# digest in the manifest still agrees and the label is the only cause. Each
# operation that reads a manifest must refuse it with the cause and the remedy.
python3 - "$TMP" <<'EOF'
import json, pathlib, sys
tmp = pathlib.Path(sys.argv[1])
cases = [("ibk4", "quad-ibk4-ptd1-lgi3-gbi1-merkle-v0", "quad-ibk4-ptd1-lgi1-gbi1-merkle-v0"),
         ("ibk5", "quad-ibk5-ptd2-lgi4-gbi1-merkle-v0", "quad-ibk5-ptd2-lgi2-gbi1-merkle-v0")]
for fmt, new, old in cases:
    manifest = (tmp / ("store-uni-" + fmt) / "manifest.sbm2").read_bytes()
    assert manifest.count(new.encode()) == 1, (fmt, manifest.count(new.encode()))
    assert len(new) == len(old)
    retired = manifest.replace(new.encode(), old.encode())
    assert retired != manifest and len(retired) == len(manifest)
    hexed = retired.hex()
    q = "SELECT * WHERE { ?s ?p ?o }"
    (tmp / ("retired-" + fmt + "-inspect.json")).write_text(json.dumps([hexed]))
    (tmp / ("retired-" + fmt + "-plan.json")).write_text(json.dumps([hexed, q]))
    (tmp / ("retired-" + fmt + "-open.json")).write_text(json.dumps([["storeOpen", [hexed, "[]"]]]))
EOF
for RETIRED_FORMAT in ibk4 ibk5; do
  check "storeManifestInspect refuses a $RETIRED_FORMAT manifest whose layout names a retired literal index" \
    storeManifestInspect "$TMP/retired-$RETIRED_FORMAT-inspect.json" \
    'r["ok"] is False and "ASCII-only fold" in r["error"] and "Re-pack" in r["error"]
     and "do not decode" not in r["error"]'
  check "storeQueryPlan refuses a $RETIRED_FORMAT manifest whose layout names a retired literal index" \
    storeQueryPlan "$TMP/retired-$RETIRED_FORMAT-plan.json" \
    'r["ok"] is False and "ASCII-only fold" in r["error"] and "Re-pack" in r["error"]'
  checkseq "storeOpen refuses a $RETIRED_FORMAT manifest whose layout names a retired literal index" \
    "$TMP/retired-$RETIRED_FORMAT-open.json" \
    'rs[0]["ok"] is False and "ASCII-only fold" in rs[0]["error"] and "Re-pack" in rs[0]["error"]'
done

args "$TMP/store-arity.json" "00"
check "storeQuery wrong arity -> error" storeQuery "$TMP/store-arity.json" \
  'r["ok"] is False and "expects 3 arguments" in r["error"]'

# --- Store handles (issue 641, the stateful half) ---------------------
# Handle state lives in the process, so the dependent sequence runs through
# `callseq`. It uses the diagnostic hexadecimal descriptor form, which is what
# `callseq` can carry; the blob form is the same admission and is exercised
# above and by tools/wasm-store-query-smoke.sh.
#
# WHAT THIS GATES: the handle and the stateless path must answer the SAME
# ROWS, not the same row count (anti-pattern 34). The sequence asks one query
# both ways and the assertion compares the binding lists themselves.
python3 - "$TMP/store-handle-seq.json" "$TMP/store-ibk3/manifest.sbm2" \
    "$TMP/store-ibk3" <<'EOF'
import json, pathlib, sys
out, manifest, directory = sys.argv[1:4]
manifest_hex = pathlib.Path(manifest).read_bytes().hex()
def payload(names):
    return json.dumps([{"key": key,
                        "bytes": (pathlib.Path(directory) / key).read_bytes().hex()}
                       for key in names])
Q = "SELECT ?s ?o WHERE { ?s <http://e/p> ?o } ORDER BY ?s ?o"
seq = [
  # Open on BOTH artifacts, so the handle retains more than one query needs.
  ["storeOpen",         [manifest_hex, payload(["predicate-0.ibk3", "predicate-1.ibk3"])]],
  ["storeHandleQuery",  ["s1", Q]],
  # The same query through the stateless op, for the row comparison.
  ["storeQuery",        [manifest_hex, Q, payload(["predicate-0.ibk3"])]],
  # A query that needs every retained block: the cached-index path.
  ["storeHandleQuery",  ["s1", "SELECT ?s WHERE { ?s ?p ?o }"]],
  # FILTER NOT EXISTS is decided by the reference evaluator (anti-pattern 34).
  ["storeHandleQuery",  ["s1",
      "ASK { ?s <http://e/p> ?o FILTER NOT EXISTS { ?s <http://e/q> ?v } }"]],
  ["storeHandleList",   []],
  ["storeHandleClose",  ["s1"]],
  ["storeHandleQuery",  ["s1", "ASK { ?s ?p ?o }"]],
  # A handle opened with ONE block refuses a query whose plan needs both.
  ["storeOpen",         [manifest_hex, payload(["predicate-0.ibk3"])]],
  ["storeHandleQuery",  ["s2", "SELECT ?s WHERE { ?s ?p ?o }"]],
  ["storeHandleClose",  ["s2"]],
]
json.dump(seq, open(out, "w"))
EOF
checkseq "store handle: open once, answer many, same rows as storeQuery" \
  "$TMP/store-handle-seq.json" \
  'rs[0]["ok"] is True and rs[0]["handle"] == "s1" and rs[0]["artifacts"] == 2
   and rs[0]["bytes"] > 0 and rs[0]["rows"] == 3
   and rs[1]["ok"] is True and rs[1]["kind"] == "select"
   and rs[1]["shards"] == 1 and rs[1]["mode"] == "ibk3-paged-merkle(1)"
   and rs[2]["ok"] is True
   and rs[1]["srj"]["results"]["bindings"] == rs[2]["srj"]["results"]["bindings"]
   and rs[1]["shards"] == rs[2]["shards"] and rs[1]["mode"] == rs[2]["mode"]
   and rs[3]["ok"] is True and rs[3]["shards"] == 2
   and rs[3]["mode"] == "ibk3-paged-merkle-full-manifest(2)"
   and len(rs[3]["srj"]["results"]["bindings"]) == 3
   and rs[4]["ok"] is True and rs[4]["kind"] == "ask"
   and rs[5]["ok"] is True and len(rs[5]["handles"]) == 1
   and rs[5]["handles"][0]["handle"] == "s1" and rs[5]["bytes"] == rs[0]["bytes"]
   and rs[5]["handleCap"] == 8 and rs[5]["bytesCap"] == 134217728
   and rs[6] == {"ok": True}
   and rs[7]["ok"] is False and rs[7]["error"] == "unknown store handle: s1"
   and rs[8]["ok"] is True and rs[8]["handle"] == "s2" and rs[8]["artifacts"] == 1
   and rs[9]["ok"] is False and "does not retain" in rs[9]["error"]
   and rs[10] == {"ok": True}'

# Two stores open at once, each answering from its own generation: the shape a
# long-lived server holds. The second store is the IBK4 generation.
python3 - "$TMP/store-handle-two.json" "$TMP/store-ibk3/manifest.sbm2" \
    "$TMP/store-ibk3" "$TMP/store-ibk4/manifest.sbm2" "$TMP/store-ibk4" <<'EOF'
import json, pathlib, sys
out, m3, d3, m4, d4 = sys.argv[1:6]
def hexof(path):
    return pathlib.Path(path).read_bytes().hex()
def payload(directory, names):
    return json.dumps([{"key": key,
                        "bytes": (pathlib.Path(directory) / key).read_bytes().hex()}
                       for key in names])
ibk4_keys = sorted(entry.name for entry in pathlib.Path(d4).iterdir()
                   if entry.name.endswith(".ibk4"))
seq = [
  ["storeOpen",        [hexof(m3), payload(d3, ["predicate-0.ibk3"])]],
  ["storeOpen",        [hexof(m4), payload(d4, ibk4_keys)]],
  ["storeHandleList",  []],
  ["storeHandleQuery", ["s1", "SELECT ?s WHERE { ?s <http://e/p> ?o }"]],
  ["storeHandleQuery", ["s2",
      "SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }"]],
  ["storeHandleClose", ["s1"]],
  ["storeHandleClose", ["s2"]],
  ["storeOpen",        [hexof(m3), "[]"]],
  ["storeOpen",        [hexof(m3), json.dumps([{"key": "no-such.ibk3", "bytes": "00"}])]],
]
json.dump(seq, open(out, "w"))
EOF
checkseq "two store handles are independent; each open refusal names its reason" \
  "$TMP/store-handle-two.json" \
  'rs[0]["handle"] == "s1" and rs[1]["handle"] == "s2"
   and rs[2]["ok"] is True and len(rs[2]["handles"]) == 2
   and rs[2]["bytes"] == rs[0]["bytes"] + rs[1]["bytes"]
   and rs[3]["ok"] is True and rs[3]["kind"] == "select"
   and len(rs[3]["srj"]["results"]["bindings"]) == 2
   and rs[4]["ok"] is True and rs[4]["kind"] == "select"
   and len(rs[4]["srj"]["results"]["bindings"]) == 2
   and rs[5] == {"ok": True} and rs[6] == {"ok": True}
   and rs[7]["ok"] is False and "no artifact bytes were supplied" in rs[7]["error"]
   and rs[8]["ok"] is False and "is not declared by this manifest" in rs[8]["error"]'

# A tampered artifact is refused at OPEN, so no handle can answer from bytes
# it did not verify. The trust argument moves; it does not weaken.
python3 - "$TMP/store-handle-tamper.json" "$TMP/store-ibk3/manifest.sbm2" \
    "$TMP/store-ibk3" <<'EOF'
import json, pathlib, sys
out, manifest, directory = sys.argv[1:4]
raw = bytearray((pathlib.Path(directory) / "predicate-0.ibk3").read_bytes())
raw[-1] ^= 0xFF
seq = [
  ["storeOpen", [pathlib.Path(manifest).read_bytes().hex(),
                 json.dumps([{"key": "predicate-0.ibk3", "bytes": bytes(raw).hex()}])]],
  ["storeHandleList", []],
]
json.dump(seq, open(out, "w"))
EOF
checkseq "storeOpen refuses an artifact whose SHA-256 differs; no handle is issued" \
  "$TMP/store-handle-tamper.json" \
  'rs[0]["ok"] is False and "predicate-0.ibk3" in rs[0]["error"]
   and "SHA-256" in rs[0]["error"]
   and rs[1]["ok"] is True and rs[1]["handles"] == []'

args "$TMP/store-open-arity.json" "00"
check "storeOpen wrong arity -> error" storeOpen "$TMP/store-open-arity.json" \
  'r["ok"] is False and "expects 2 arguments" in r["error"]'

args "$TMP/store-handle-unknown.json" "s999" 'ASK { ?s ?p ?o }'
check "storeHandleQuery unknown handle -> error" storeHandleQuery \
  "$TMP/store-handle-unknown.json" \
  'r["ok"] is False and r["error"] == "unknown store handle: s999"'

# --- Canon family -----------------------------------------------------
args "$TMP/canon.json" '_:b0 <http://e/p> "v" .
'
check "canonicalizeToNQuads" canonicalizeToNQuads "$TMP/canon.json" \
  'r["ok"] is True and "_:c14n0" in r["nquads"]'

# --- Reason family ----------------------------------------------------
SUBCLASS='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .
<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .
'
args "$TMP/owl-rdfs.json" "$SUBCLASS" "RDFS"
check "owlClosure RDFS" owlClosure "$TMP/owl-rdfs.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["nquads"]'

args "$TMP/owl-rl.json" "$SUBCLASS" "OWL-RL"
check "owlClosure OWL-RL" owlClosure "$TMP/owl-rl.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["nquads"]'

args "$TMP/owl-badmode.json" "$SUBCLASS" "nonsense"
check "owlClosure unknown mode -> error" owlClosure "$TMP/owl-badmode.json" \
  'r["ok"] is False and "unknown mode" in r["error"]'

args "$TMP/rhodf.json" "$SUBCLASS"
check "rhoDfClosure" rhoDfClosure "$TMP/rhodf.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["ntriples"]
   and isinstance(r["rounds"], int) and r["rounds"] >= 1'

args "$TMP/frag-yes.json" "$SUBCLASS"
check "rhoDfFragmentCheck true" rhoDfFragmentCheck "$TMP/frag-yes.json" \
  'r["ok"] is True and r["fragment"] is True'

args "$TMP/frag-no.json" '<http://e/a> <http://e/p> "a literal" .
'
check "rhoDfFragmentCheck false (literal object)" rhoDfFragmentCheck "$TMP/frag-no.json" \
  'r["ok"] is True and r["fragment"] is False'

SAMEAS='<http://e/a> <http://www.w3.org/2002/07/owl#sameAs> <http://e/b> .
<http://e/a> <http://e/p> <http://e/v> .
'
args "$TMP/rdfsplus.json" "$SAMEAS"
check "rdfsPlusClosure" rdfsPlusClosure "$TMP/rdfsplus.json" \
  'r["ok"] is True and "<http://e/b> <http://e/p> <http://e/v> ." in r["ntriples"]
   and isinstance(r["rounds"], int) and r["rounds"] >= 1'

# --- OWL DL consistency / entailment (issue 586) ----------------------
# Envelopes pinned against bin/npm-entry/entry_jsoo.ml's
# owl_is_consistent_json / owl_entails_json: three-valued, budget-out
# reported as null with a reason, never a silent false.
args "$TMP/owl-cons-yes.json" "$SUBCLASS" ""
check "owlIsConsistent consistent -> true, no reason" owlIsConsistent "$TMP/owl-cons-yes.json" \
  'r["ok"] is True and r["consistent"] is True and "reason" not in r'

NOTHING='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Nothing> .
'
args "$TMP/owl-cons-no.json" "$NOTHING" ""
check "owlIsConsistent owl:Nothing member -> false + reason" owlIsConsistent "$TMP/owl-cons-no.json" \
  'r["ok"] is True and r["consistent"] is False and "contradiction" in r["reason"]'

# A cyclic TBox (A subClassOf someValuesFrom(p, A)) keeps the expansion
# changing, so fuel 1 runs out mid-search: the verdict is null.
CYCLIC='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/A> .
<http://e/A> <http://www.w3.org/2000/01/rdf-schema#subClassOf> _:r .
_:r <http://www.w3.org/2002/07/owl#onProperty> <http://e/p> .
_:r <http://www.w3.org/2002/07/owl#someValuesFrom> <http://e/A> .
'
args "$TMP/owl-cons-unk.json" "$CYCLIC" '{"fuel":"1"}'
check "owlIsConsistent fuel 1 -> null (budget-out, fuel named)" owlIsConsistent "$TMP/owl-cons-unk.json" \
  'r["ok"] is True and r["consistent"] is None and "budget-out" in r["reason"]
   and "fuel 1 " in r["reason"]'

# The same cyclic TBox at the default budget saturates under the
# witness-depth cap: consistent.
args "$TMP/owl-cons-cyc.json" "$CYCLIC" ""
check "owlIsConsistent cyclic TBox, default fuel -> true" owlIsConsistent "$TMP/owl-cons-cyc.json" \
  'r["ok"] is True and r["consistent"] is True'

# Entailment via the closure path: a type D . follows from
# a type C, C subClassOf D by cax-sco.
CONCL='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> .
'
args "$TMP/owl-ent-yes.json" "$SUBCLASS" "$CONCL" ""
check "owlEntails subclass typing -> true via closure" owlEntails "$TMP/owl-ent-yes.json" \
  'r["ok"] is True and r["entailed"] is True and r["via"] == "closure"'

# Not entailed: the negated conclusion is satisfiable beside the
# premise (a countermodel), reported via the refutation path.
UNRELATED='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Zebra> .
'
args "$TMP/owl-ent-no.json" "$SUBCLASS" "$UNRELATED" ""
check "owlEntails unrelated class -> false via refutation" owlEntails "$TMP/owl-ent-no.json" \
  'r["ok"] is True and r["entailed"] is False and r["via"] == "refutation"
   and "model" in r["reason"]'

# Budget-out on a refutation goal: null, never a silent false.
args "$TMP/owl-ent-unk.json" "$CYCLIC" "$UNRELATED" '{"fuel":"1"}'
check "owlEntails fuel 1 -> null (budget-out)" owlEntails "$TMP/owl-ent-unk.json" \
  'r["ok"] is True and r["entailed"] is None and r["via"] == "refutation"
   and "budget-out" in r["reason"]'

args "$TMP/owl-ent-badnq.json" 'not nquads @@@' "$CONCL" ""
check "owlEntails bad premise -> error" owlEntails "$TMP/owl-ent-badnq.json" \
  'r["ok"] is False and len(r["error"]) > 0'

# --- Common Logic / IKL family ----------------------------------------
IKL='(ist c (that (Dead OBL)))'
args "$TMP/cl-parse.json" "$IKL"
check "clParse ikl sentence" clParse "$TMP/cl-parse.json" \
  'r["ok"] is True and r["sentences"] == 1 and r["pureCL"] is False
   and r["normalized"] == "(ist c (that (Dead OBL)))"'

args "$TMP/cl-parse-pure.json" '(married Jack Jill) (forall (x) (if (Boy x) (Human x)))'
check "clParse pure CL text" clParse "$TMP/cl-parse-pure.json" \
  'r["ok"] is True and r["sentences"] == 2 and r["pureCL"] is True'

args "$TMP/cl-parse-bad.json" '(P a'
check "clParse unclosed paren -> error" clParse "$TMP/cl-parse-bad.json" \
  'r["ok"] is False and "unclosed" in r["error"]'

# clSerialize — the canonical writer, with the OPEN round-trip lemma
# reported rather than assumed (`clif_roundTrip`, CL/ClifAdequacy.lean).
args "$TMP/cl-ser.json" '(forall (x) (if (Boy x) (Person x)))'
check "clSerialize canonical text" clSerialize "$TMP/cl-ser.json" \
  'r["ok"] is True and r["sentences"] == 1
   and r["clif"] == "(forall (x) (if (Boy x) (Person x)))"
   and r["roundTripProved"] is False'

args "$TMP/cl-ser-bad.json" '(P a'
check "clSerialize unclosed paren -> error" clSerialize "$TMP/cl-ser-bad.json" \
  'r["ok"] is False and "unclosed" in r["error"]'

# clAlphaNorm — two alpha-variants must serialise byte-identically.
args "$TMP/cl-alpha-x.json" '(forall (x) (if (Boy x) (Person x)))'
check "clAlphaNorm canonical names" clAlphaNorm "$TMP/cl-alpha-x.json" \
  'r["ok"] is True and r["sentences"] == 1
   and r["clif"] == "(forall (v1) (if (Boy v1) (Person v1)))"'

args "$TMP/cl-alpha-z.json" '(forall (zz) (if (Boy zz) (Person zz)))'
check "clAlphaNorm collapses an alpha-variant" clAlphaNorm "$TMP/cl-alpha-z.json" \
  'r["ok"] is True
   and r["clif"] == "(forall (v1) (if (Boy v1) (Person v1)))"'

# clNormalize — Hayes's satisfiability-preserving IKL-to-CL reduction.
# `noIntrusion` is the PROOF HYPOTHESIS decided, so both verdicts are
# pinned: the head/tail pair, and the intrusion case the theorems do
# not cover.
args "$TMP/cl-norm.json" '(P (that (Q a)))'
check "clNormalize that-term -> head + tail" clNormalize "$TMP/cl-norm.json" \
  'r["ok"] is True and r["thatCount"] == 1 and r["noIntrusion"] is True
   and r["head"] == ["(P prop1)"] and r["tail"] == ["(iff (prop1) (Q a))"]
   and r["preserves"] == "satisfiability"'

args "$TMP/cl-norm-intr.json" '(forall (x) (P (that (Q x))))'
check "clNormalize intrusion -> noIntrusion false" clNormalize "$TMP/cl-norm-intr.json" \
  'r["ok"] is True and r["noIntrusion"] is False and r["thatCount"] == 1'

args "$TMP/cl-norm-bad.json" '(P a'
check "clNormalize unclosed paren -> error" clNormalize "$TMP/cl-norm-bad.json" \
  'r["ok"] is False and "unclosed" in r["error"]'

# clFiniteSat — CL.Examples' `tiny` as a wire interpretation: Boy holds
# of Bill alone. The refutations are pinned alongside the satisfactions,
# so a checker answering `true` to everything cannot pass.
CLI_FS='{"domain":["bill","boy"],"default":"bill","names":{"Bill":"bill","Boy":"boy","Sue":"boy"},"relations":[{"op":"boy","args":["bill"]}]}'

args "$TMP/cl-fs-yes.json" "$CLI_FS" '(Boy Bill)
(exists (x) (Boy x))'
check "clFiniteSat satisfied" clFiniteSat "$TMP/cl-fs-yes.json" \
  'r["ok"] is True and r["satisfied"] is True and r["domainSize"] == 2
   and [s["satisfied"] for s in r["sentences"]] == [True, True]
   and r["preconditions"]["domainComplete"]["holds"] is True
   and r["preconditions"]["noSeqQuant"]["holds"] is True'

args "$TMP/cl-fs-no.json" "$CLI_FS" '(Boy Sue)
(forall (x) (Boy x))'
check "clFiniteSat refutes where the tables have no row" clFiniteSat "$TMP/cl-fs-no.json" \
  'r["ok"] is True and r["satisfied"] is False
   and [s["satisfied"] for s in r["sentences"]] == [False, False]'

# The hypothesis `noSeqQuant` of `satisfiesFin_eq` is CHECKED, and a
# text outside it is refused by name rather than answered.
args "$TMP/cl-fs-seq.json" "$CLI_FS" '(forall (...m) (P ...m))'
check "clFiniteSat refuses a sequence-marker quantifier" clFiniteSat "$TMP/cl-fs-seq.json" \
  'r["ok"] is False and r["precondition"] == "noSeqQuant"
   and "noSeqQuant" in r["error"]'

args "$TMP/cl-fs-label.json" '{"domain":["bill"],"names":{"Boy":"nope"}}' '(Boy Bill)'
check "clFiniteSat unknown domain label -> error" clFiniteSat "$TMP/cl-fs-label.json" \
  'r["ok"] is False and "nope" in r["error"]'

args "$TMP/cl-fs-empty.json" '{"domain":[]}' '(Boy Bill)'
check "clFiniteSat empty domain -> error" clFiniteSat "$TMP/cl-fs-empty.json" \
  'r["ok"] is False and "at least one element" in r["error"]'

args "$TMP/cl-fs-nodom.json" '{}' '(Boy Bill)'
check "clFiniteSat missing domain -> error" clFiniteSat "$TMP/cl-fs-nodom.json" \
  "r['ok'] is False and 'domain' in r['error']"

args "$TMP/cl-fs-arity.json" "$CLI_FS"
check "clFiniteSat wrong arity -> error" clFiniteSat "$TMP/cl-fs-arity.json" \
  'r["ok"] is False and "expects 2 arguments" in r["error"]'

# --- Dataset handles (issue 585) --------------------------------------
# Handle state lives in the process, so the dependent sequence runs
# through `callseq`: open -> query -> update -> query -> serialize
# (both formats) -> close -> use-after-close error.
python3 - "$TMP/handles-seq.json" <<'EOF'
import json, sys
TTL = '@prefix ex: <http://e/> . ex:a ex:p ex:b .'
seq = [
  ["datasetOpen",      [TTL, "turtle", ""]],
  ["datasetQuery",     ["h1", "SELECT ?s WHERE { ?s <http://e/p> ?o }"]],
  ["datasetUpdate",    ["h1", "INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }"]],
  ["datasetQuery",     ["h1", "ASK { <http://e/x> <http://e/p> <http://e/y> }"]],
  ["datasetSerialize", ["h1", "nquads"]],
  ["datasetSerialize", ["h1", "turtle"]],
  ["datasetClose",     ["h1"]],
  ["datasetQuery",     ["h1", "ASK { ?s ?p ?o }"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "dataset handle lifecycle (open/query/update/serialize/close)" "$TMP/handles-seq.json" \
  'rs[0]["ok"] is True and rs[0]["handle"] == "h1" and rs[0]["count"] == 1
   and rs[1]["ok"] is True and rs[1]["kind"] == "select"
   and rs[1]["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"
   and rs[2]["ok"] is True and rs[2]["count"] == 2
   and rs[3]["ok"] is True and rs[3]["kind"] == "ask" and rs[3]["boolean"] is True
   and rs[4]["ok"] is True and "<http://e/x>" in rs[4]["nquads"] and "<http://e/a>" in rs[4]["nquads"]
   and rs[5]["ok"] is True and "@prefix" in rs[5]["turtle"]
   and rs[6] == {"ok": True}
   and rs[7]["ok"] is False and rs[7]["error"] == "unknown dataset handle: h1"'

# Two handles are independent: an update through h2 must not leak into
# h1, and closing h2 must leave h1 open. Also the per-family errors:
# an unknown serialize format, and closing an unknown handle.
python3 - "$TMP/handles-two.json" <<'EOF'
import json, sys
seq = [
  ["datasetOpen",      ["<http://e/a> <http://e/p> <http://e/b> .", "ntriples", ""]],
  ["datasetOpen",      ["<http://f/c> <http://f/q> <http://f/d> .", "ntriples", ""]],
  ["datasetUpdate",    ["h2", "INSERT DATA { <http://f/x> <http://f/q> <http://f/y> }"]],
  ["datasetSerialize", ["h1", "nquads"]],
  ["datasetSerialize", ["h1", "trig"]],
  ["datasetClose",     ["h2"]],
  ["datasetClose",     ["h2"]],
  ["datasetQuery",     ["h1", "ASK { <http://e/a> <http://e/p> <http://e/b> }"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "dataset handles are independent + per-family errors" "$TMP/handles-two.json" \
  'rs[0]["handle"] == "h1" and rs[1]["handle"] == "h2"
   and rs[2]["ok"] is True and rs[2]["count"] == 2
   and rs[3]["ok"] is True and "<http://f/" not in rs[3]["nquads"]
   and rs[4]["ok"] is False and "unknown format tag" in rs[4]["error"]
   and rs[5] == {"ok": True}
   and rs[6]["ok"] is False and rs[6]["error"] == "unknown dataset handle: h2"
   and rs[7]["ok"] is True and rs[7]["boolean"] is True'

# One-shot error paths reachable without process state.
args "$TMP/h-open-bad.json" 'this is not turtle @@@' "turtle" ""
check "datasetOpen bad turtle -> error, no handle" datasetOpen "$TMP/h-open-bad.json" \
  'r["ok"] is False and "handle" not in r and len(r["error"]) > 0'

args "$TMP/h-query-unknown.json" "h999" 'ASK { ?s ?p ?o }'
check "datasetQuery unknown handle -> error" datasetQuery "$TMP/h-query-unknown.json" \
  'r["ok"] is False and r["error"] == "unknown dataset handle: h999"'

args "$TMP/h-open-arity.json" "just-one-arg"
check "datasetOpen wrong arity -> error" datasetOpen "$TMP/h-open-arity.json" \
  'r["ok"] is False and "expects 3 arguments" in r["error"]'

# --- FPP0 proof checker (issue 623 / M1) ------------------------------
# The degenerate bundle of the adoption doc's section 8a: the conclusion
# is itself a declared assumption. It is VALID and it proves nothing,
# and the three fields that say so travel with the verdict. No digests
# are needed for this shape, so the fixture is writable by hand.
PROOF_DEGEN='{"profile":"fpp0/1","artifacts":[],"assumptions":[{"id":"a1","subject":{"kind":"clif","proposition":"(P jim)"},"level":"attestation"}],"steps":[],"conclusion":{"kind":"clif","proposition":"(P jim)"}}'

args "$TMP/proof-degen.json" "$PROOF_DEGEN"
check "proofCheck reports the degenerate bundle, never as a proof" proofCheck "$TMP/proof-degen.json" \
  'r["ok"] is True and r["valid"] is True
   and r["conclusionIsAssumption"] is True
   and r["foundationalOnly"] is False
   and r["counts"]["foundational"] == 0
   and len(r["assumptions"]) == 1'

# An UNKNOWN level string is refused by name — never read as the weakest
# member, never dropped (theorem L4Wasm.Ops.decodeLevelName_inj).
args "$TMP/proof-badlevel.json" "${PROOF_DEGEN/\"level\":\"attestation\"/\"level\":\"A\"}"
check "proofCheck refuses an unknown evidence level" proofCheck "$TMP/proof-badlevel.json" \
  'r["ok"] is False and "unknown evidence level" in r["error"]'

# A decode failure is NOT an invalid bundle: the level below is a level
# the decoder knows, and the KERNEL is what refuses the bundle.
args "$TMP/proof-fnd-asm.json" "${PROOF_DEGEN/\"level\":\"attestation\"/\"level\":\"foundational\"}"
check "proofCheck: a foundational assumption is ok:true, valid:false" proofCheck "$TMP/proof-fnd-asm.json" \
  'r["ok"] is True and r["valid"] is False'

args "$TMP/proof-inspect.json" "$PROOF_DEGEN"
check "proofInspect reports shape and NO verdict" proofInspect "$TMP/proof-inspect.json" \
  'r["ok"] is True and "valid" not in r and r["steps"] == 0
   and r["conclusionDeclaredAsAssumption"] is True'

args "$TMP/proof-arity.json"
check "proofCheck wrong arity -> error" proofCheck "$TMP/proof-arity.json" \
  'r["ok"] is False and "expects 1 argument" in r["error"]'

# --- Linked Web Storage 1.0 + Solid Protocol --------------------------
# https://github.com/danbri/factoidal/issues/659. The server ops hold a
# storage in a handle table, so a CRUD sequence must run in ONE process:
# `callseq`, like the dataset-handle ops above. The request and response
# documents are docs/lws-solid-conformance.md, section "wasm ABI".

python3 - "$TMP/lws-crud.json" <<'EOF'
import json, sys
req = lambda **kw: json.dumps(kw)
seq = [
  ["lwsOpen",  [json.dumps({"baseIri": "http://example.org/", "now": 1000000000})]],
  ["lwsStep",  ["lws1", req(method="PUT", target="/alice/card",
                            headers=[["content-type", "text/turtle"]],
                            body="<http://example.org/a> <http://example.org/b> \"v\" .")]],
  ["lwsStep",  ["lws1", req(method="GET", target="/alice/card")]],
  ["lwsStep",  ["lws1", req(method="HEAD", target="/alice/card")]],
  ["lwsStep",  ["lws1", req(method="PUT", target="/alice/card",
                            headers=[["content-type", "text/turtle"]],
                            body="<http://example.org/a> <http://example.org/b> \"w\" .")]],
  ["lwsStep",  ["lws1", req(method="DELETE", target="/alice/card")]],
  ["lwsStep",  ["lws1", req(method="GET", target="/alice/card")]],
  ["lwsClose", ["lws1"]],
  ["lwsStep",  ["lws1", req(method="GET", target="/")]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF

checkseq "lwsStep drives create, read, update and delete" "$TMP/lws-crud.json" \
  'rs[0]["ok"] is True and rs[0]["handle"] == "lws1" and rs[0]["root"] == "/"
   and [r["response"]["status"] for r in rs[1:7]] == [201, 200, 200, 204, 204, 404]
   and dict(rs[2]["response"]["headers"])["last-modified"]
       == "Sun, 09 Sep 2001 01:46:42 GMT"
   and dict(rs[3]["response"]["headers"])["last-modified"]
       == "Sun, 09 Sep 2001 01:46:42 GMT"
   and rs[3]["response"]["body"] == ""
   and rs[2]["response"]["body"].endswith("\"v\" .")
   and rs[7]["ok"] is True
   and rs[8]["ok"] is False and "unknown LWS handle" in rs[8]["error"]'

# The Solid server refines the LWS one: the storage root advertises
# pim:Storage, a container answers containment triples, and an N3 Patch
# applies. Same handle discipline.
python3 - "$TMP/solid-crud.json" <<'EOF'
import json, sys
req = lambda **kw: json.dumps(kw)
patch = """@prefix solid: <http://www.w3.org/ns/solid/terms#>.
@prefix ex: <http://www.example.org/terms#>.
_:rename a solid:InsertDeletePatch;
  solid:where   { ?person ex:familyName "Garcia". };
  solid:inserts { ?person ex:givenName "Alex". };
  solid:deletes { ?person ex:givenName "Claudia". }."""
seq = [
  ["solidOpen", [json.dumps({"baseIri": "http://example.org/", "now": 0})]],
  ["solidStep", ["solid1", req(method="GET", target="/")]],
  ["solidStep", ["solid1", req(method="PUT", target="/p/claudia",
                               headers=[["content-type", "text/turtle"]],
                               body='@prefix ex: <http://www.example.org/terms#>.\n'
                                    '<http://example.org/p/claudia> ex:familyName "Garcia"; '
                                    'ex:givenName "Claudia".')]],
  ["solidStep", ["solid1", req(method="GET", target="/p/")]],
  ["solidStep", ["solid1", req(method="PATCH", target="/p/claudia",
                               headers=[["content-type", "text/n3"]], body=patch)]],
  ["solidStep", ["solid1", req(method="GET", target="/p/claudia")]],
  ["solidStep", ["solid1", req(method="DELETE", target="/")]],
  # A patch whose formulae use relative references: RFC 3986 5.1.3 makes
  # the request target the base, so <> and <#it> resolve against it.
  ["solidStep", ["solid1", req(method="PUT", target="/notes/three",
                               headers=[["content-type", "text/turtle"]],
                               body='<#it> <http://www.w3.org/2000/01/rdf-schema#label> "one" .')]],
  ["solidStep", ["solid1", req(method="PATCH", target="/notes/three",
                               headers=[["content-type", "text/n3"]],
                               body='@prefix solid: <http://www.w3.org/ns/solid/terms#> .\n'
                                    '<> a solid:InsertDeletePatch ;\n'
                                    '   solid:inserts { <#it> '
                                    '<http://www.w3.org/2000/01/rdf-schema#comment> "added" . } .')]],
  ["solidStep", ["solid1", req(method="GET", target="/notes/three")]],
  # A PUT whose body edits a containment triple, written with the empty
  # relative reference as a client writes it (Solid Protocol 5.3).
  ["solidStep", ["solid1", req(method="PUT", target="/notes/",
                               headers=[["content-type", "text/turtle"]],
                               body='<> <http://www.w3.org/ns/ldp#contains> </notes/three> .')]],
  # The storage advertises an LDN inbox, so it holds one and a Receiver
  # answers a notification POST with 201 (LDN 3.1 and 3.3.1).
  ["solidStep", ["solid1", req(method="POST", target="/inbox/",
                               headers=[["content-type", "application/ld+json"]],
                               body='{"@id":"","https://www.w3.org/ns/activitystreams#actor":'
                                    '{"@id":"https://example.org/alice"}}')]],
  ["solidClose", ["solid1"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF

checkseq "solidStep serves a storage, a container and an N3 Patch" "$TMP/solid-crud.json" \
  'rs[0]["ok"] is True and rs[0]["storage"] == "http://example.org/"
   and "<http://www.w3.org/ns/pim/space#Storage>; rel=\"type\""
       in dict(rs[1]["response"]["headers"])["link"]
   and rs[2]["response"]["status"] == 201
   and "contains" in rs[3]["response"]["body"]
   and rs[4]["response"]["status"] == 204
   and "Alex" in rs[5]["response"]["body"]
   and "Claudia" not in rs[5]["response"]["body"]
   and rs[6]["response"]["status"] == 405
   and "DELETE" not in dict(rs[6]["response"]["headers"])["allow"]
   and rs[8]["response"]["status"] == 204
   and "added" in rs[9]["response"]["body"]
   and rs[10]["response"]["status"] == 409
   and "ldp#inbox" in dict(rs[1]["response"]["headers"])["link"]
   and rs[11]["response"]["status"] == 201
   and dict(rs[11]["response"]["headers"])["location"].startswith("/inbox/")'

# WAC-Allow is reported whether or not the decision is enforced, so a
# client always learns its privileges (Web Access Control §5.3.4).
python3 - "$TMP/solid-wac.json" <<'EOF'
import json, sys
req = lambda **kw: json.dumps(kw)
acl = """@prefix acl: <http://www.w3.org/ns/auth/acl#>.
<http://example.org/acl#owner> a acl:Authorization;
  acl:agent <http://example.org/alice/card#me>;
  acl:accessTo <http://example.org/alice/card>;
  acl:mode acl:Read, acl:Write, acl:Control."""
seq = [
  ["solidOpen", [json.dumps({"baseIri": "http://example.org/", "now": 0})]],
  ["solidStep", ["solid1", req(method="PUT", target="/alice/card",
                               headers=[["content-type", "text/turtle"]],
                               body="<http://example.org/a> <http://example.org/b> \"v\" .")]],
  ["solidStep", ["solid1", req(method="PUT", target="/alice/card.acl",
                               headers=[["content-type", "text/turtle"]], body=acl)]],
  ["solidStep", ["solid1", req(method="GET", target="/alice/card")]],
  ["solidStep", ["solid1", req(method="GET", target="/alice/card",
                               agent="http://example.org/alice/card#me")]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF

checkseq "solidStep reports WAC-Allow per agent" "$TMP/solid-wac.json" \
  'dict(rs[3]["response"]["headers"])["wac-allow"] == "user=\"\",public=\"\""
   and dict(rs[4]["response"]["headers"])["wac-allow"]
       == "user=\"read write append control\",public=\"\""'

# Web Access Control, enforced. The root ACL is a PROVISIONING input
# (`rootAcl` in the open configuration): under enforcement the request that
# would write it is the first request it would authorize, so a storage
# cannot bootstrap it. Each `callseq` runs in its own process, so the handle
# counter starts at one again and every sequence names "solid1".
python3 - "$TMP/solid-deny.json" <<'EOF'
import json, sys
req = lambda **kw: json.dumps(kw)
acl = """@prefix acl: <http://www.w3.org/ns/auth/acl#>.
<http://example.org/acl#owner> a acl:Authorization;
  acl:agent <http://example.org/alice/card#me>;
  acl:accessTo <http://example.org/>;
  acl:default <http://example.org/>;
  acl:mode acl:Read, acl:Write, acl:Control."""
seq = [
  ["solidOpen", [json.dumps({"baseIri": "http://example.org/", "now": 0,
                             "enforceWac": True, "rootAcl": acl})]],
  ["solidStep", ["solid1", req(method="PUT", target="/alice/card",
                               headers=[["content-type", "text/turtle"]],
                               body="<http://example.org/a> <http://example.org/b> \"v\" .",
                               agent="http://example.org/alice/card#me")]],
  ["solidStep", ["solid1", req(method="GET", target="/alice/card")]],
  ["solidStep", ["solid1", req(method="GET", target="/alice/card",
                               agent="http://example.org/bob/card#me")]],
  ["solidStep", ["solid1", req(method="GET", target="/alice/card",
                               agent="http://example.org/alice/card#me")]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF

checkseq "solidStep denies an unauthorized agent when WAC is enforced" "$TMP/solid-deny.json" \
  'rs[1]["response"]["status"] == 201
   and rs[2]["response"]["status"] == 401
   and rs[3]["response"]["status"] == 403
   and rs[4]["response"]["status"] == 200'


# The client ops are stateless: one builds a request, the other reads a
# response. They answer through `call` like any other op.
args "$TMP/solid-client-req.json" "create" '{"target":"/alice/","body":"<a> <b> <c> .","contentType":"text/turtle","slug":"note"}'
check "solidClientRequest builds a POST with Slug and Content-Type" solidClientRequest \
  "$TMP/solid-client-req.json" \
  'r["ok"] is True and r["request"]["method"] == "POST"
   and r["request"]["target"] == "/alice/"
   and dict([tuple(h) for h in r["request"]["headers"]])["slug"] == "note"
   and dict([tuple(h) for h in r["request"]["headers"]])["content-type"] == "text/turtle"'

args "$TMP/solid-client-resp.json" "wacAllow" '{"status":200,"headers":[["wac-allow","user=\"read write frobnicate\",public=\"read\""]],"body":""}'
check "solidClientResponse drops an unrecognised access mode" solidClientResponse \
  "$TMP/solid-client-resp.json" \
  'r["ok"] is True and r["interpretation"] == {"user": ["read", "write"], "public": ["read"]}'

# The storage walk of Solid Protocol §4.1 is a multi-step operation: the
# reply names the next resource to ask for, and the host sends the state
# back. Two responses drive it here — a 404 that continues, and the root
# reply that ends it.
args "$TMP/solid-walk-req.json" "discoverStorage" '{"target":"/notes/one","state":"/notes/"}'
check "solidClientRequest discoverStorage asks about the walk state" solidClientRequest \
  "$TMP/solid-walk-req.json" \
  'r["ok"] is True and r["request"]["method"] == "HEAD"
   and r["request"]["target"] == "/notes/"'

args "$TMP/solid-walk-1.json" "storage" '{"status":404,"headers":[],"body":"","target":"/notes/one"}'
check "solidClientResponse storage walk continues past a 404" solidClientResponse \
  "$TMP/solid-walk-1.json" \
  'r["ok"] is True and r["interpretation"]["isStorage"] is False
   and r["interpretation"]["storage"] is None
   and r["interpretation"]["continue"] is True
   and r["interpretation"]["state"] == "/notes/"'

args "$TMP/solid-walk-2.json" "storage" '{"status":200,"headers":[["link","<http://www.w3.org/ns/pim/space#Storage>; rel=\"type\""]],"body":"","target":"/"}'
check "solidClientResponse storage walk ends at the storage root" solidClientResponse \
  "$TMP/solid-walk-2.json" \
  'r["ok"] is True and r["interpretation"]["isStorage"] is True
   and r["interpretation"]["storage"] == "/"
   and r["interpretation"]["continue"] is False
   and r["interpretation"]["state"] is None'

args "$TMP/solid-walk-3.json" "storage" '{"status":404,"headers":[],"body":"","target":"/"}'
check "solidClientResponse storage walk stops at the root path" solidClientResponse \
  "$TMP/solid-walk-3.json" \
  'r["ok"] is True and r["interpretation"]["storage"] is None
   and r["interpretation"]["continue"] is False'

args "$TMP/solid-client-bad.json" "notAKind" '{"status":200}'
check "solidClientResponse unknown kind -> error" solidClientResponse \
  "$TMP/solid-client-bad.json" \
  'r["ok"] is False and "unknown kind" in r["error"]'

args "$TMP/lws-unknown.json" "lws999" '{"method":"GET","target":"/"}'
check "lwsStep on an unknown handle -> error" lwsStep "$TMP/lws-unknown.json" \
  'r["ok"] is False and "unknown LWS handle" in r["error"]'

# --- TOAN: the computer-algebra ops -----------------------------------
# Envelopes match bin/npm-entry/entry_jsoo.ml op for op. The `mathml`
# member is CONTENT MathML (to_content_mathml, line 2159), so each
# assertion below names a content element -- <apply>, <plus/>, <cn>.
# Asserting only that the string starts with "<math" would score a
# Presentation answer as correct.

TOAN_BODY='{"app":"plus","args":[{"sym":"x"},{"app":"times","args":[{"sym":"i"},{"sym":"y"}]}]}'

args "$TMP/toan-sum.json" "$TOAN_BODY" i 1 4
check "toanSummation sum_{i=1}^{4} (x + i*y) = 4x + 10y" \
  toanSummation "$TMP/toan-sum.json" \
  'r["ok"] is True and "<plus/>" in r["mathml"]
   and "<cn type=\"integer\">4</cn>" in r["mathml"]
   and "<cn type=\"integer\">10</cn>" in r["mathml"]
   and "<ci>x</ci>" in r["mathml"] and "<ci>y</ci>" in r["mathml"]
   and "<mi>" not in r["mathml"]'

args "$TMP/toan-prod.json" '{"sym":"i"}' i 1 3
check "toanProduct prod_{i=1}^{3} i = 6" toanProduct "$TMP/toan-prod.json" \
  'r["ok"] is True and "<cn type=\"integer\">6</cn>" in r["mathml"]'

args "$TMP/toan-empty.json" "$TOAN_BODY" i 5 1
check "toanSummation over an empty range is the additive identity" \
  toanSummation "$TMP/toan-empty.json" \
  'r["ok"] is True and "<cn type=\"integer\">0</cn>" in r["mathml"]'

args "$TMP/toan-simp.json" '{"app":"plus","args":[{"int":2},{"int":3}]}'
check "toanSimplify 2 + 3 folds to 5" toanSimplify "$TMP/toan-simp.json" \
  'r["ok"] is True and "<cn type=\"integer\">5</cn>" in r["mathml"]
   and "<plus/>" not in r["mathml"]'

args "$TMP/toan-rat.json" '{"app":"plus","args":[{"rat":[1,3]},{"rat":[1,3]},{"rat":[1,3]}]}'
check "toanSimplify 1/3 + 1/3 + 1/3 is exactly 1, not a float" \
  toanSimplify "$TMP/toan-rat.json" \
  'r["ok"] is True and "<cn type=\"integer\">1</cn>" in r["mathml"]
   and "0.9" not in r["mathml"] and "<rational" not in r["mathml"]'

args "$TMP/toan-diff.json" '{"app":"times","args":[{"sym":"x"},{"sym":"x"}]}' x
check "toanDiff d/dx (x*x) mentions x" toanDiff "$TMP/toan-diff.json" \
  'r["ok"] is True and "<ci>x</ci>" in r["mathml"] and "<apply>" in r["mathml"]'

args "$TMP/toan-diff-none.json" '{"app":"coth","args":[{"sym":"x"}]}' x
check "toanDiff with no rule emits the diff_unsupported marker" \
  toanDiff "$TMP/toan-diff-none.json" \
  'r["ok"] is True and "diff_unsupported" in r["mathml"]'

args "$TMP/toan-subst.json" '{"app":"plus","args":[{"sym":"x"},{"int":1}]}' x '{"int":4}'
check "toanSubst (x + 1)[x := 4] mentions 4" toanSubst "$TMP/toan-subst.json" \
  'r["ok"] is True and "<cn type=\"integer\">4</cn>" in r["mathml"]
   and "<ci>x</ci>" not in r["mathml"]'

args "$TMP/toan-mat.json" '{"mat":[[{"int":1},{"int":2}],[{"int":3},{"int":4}]]}'
check "toanSimplify carries a matrix literal through to <matrix>" \
  toanSimplify "$TMP/toan-mat.json" \
  'r["ok"] is True and "<matrix>" in r["mathml"]
   and r["mathml"].count("<matrixrow>") == 2'

args "$TMP/toan-bad.json" '{"nope":1}'
check "toanSimplify on an expr object with no known member -> error" \
  toanSimplify "$TMP/toan-bad.json" \
  'r["ok"] is False and "int / rat / bool / sym / app" in r["error"]'

args "$TMP/toan-badbound.json" "$TOAN_BODY" i one 4
check "toanSummation with a non-numeral bound -> error, not zero" \
  toanSummation "$TMP/toan-badbound.json" \
  'r["ok"] is False and "decimal integer" in r["error"]'

args "$TMP/toan-arity.json" '{"int":1}' x
check "toanSimplify arity is checked" toanSimplify "$TMP/toan-arity.json" \
  'r["ok"] is False and "expects 1 argument" in r["error"]'

# --- Crypto: the AEAD and HPKE ops ------------------------------------
# Round trips through the dispatch ABI with PUBLISHED bytes on both sides,
# not self-consistency: seal must reproduce the RFC's own ciphertext, and
# open must recover the RFC's own plaintext from it. A round trip that only
# fed seal's output back into open would pass against a pair of functions
# that agreed with each other and with nothing else.
#
# Vectors: RFC 8439 section 2.8.2 for the AEAD; RFC 9180 Appendix A.2.1,
# sequence number 0, for HPKE (DHKEM(X25519, HKDF-SHA256) / HKDF-SHA256 /
# ChaCha20Poly1305, base mode). The full corpora are lake exe l4crypto-probe.

AEAD_KEY="808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
AEAD_NONCE="070000004041424344454647"
AEAD_AAD="50515253c0c1c2c3c4c5c6c7"
AEAD_PT="4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e"
AEAD_CT="d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691"

args "$TMP/aead-seal.json" \
  "{\"alg\":\"chacha20-poly1305\",\"key\":\"$AEAD_KEY\",\"nonce\":\"$AEAD_NONCE\",\"aad\":\"$AEAD_AAD\",\"plaintext\":\"$AEAD_PT\"}"
check "aeadSeal reproduces the RFC 8439 2.8.2 ciphertext and tag" \
  aeadSeal "$TMP/aead-seal.json" \
  'r["ok"] is True and r["ciphertext"] == "'"$AEAD_CT"'"'

args "$TMP/aead-open.json" \
  "{\"alg\":\"chacha20-poly1305\",\"key\":\"$AEAD_KEY\",\"nonce\":\"$AEAD_NONCE\",\"aad\":\"$AEAD_AAD\",\"ciphertext\":\"$AEAD_CT\"}"
check "aeadOpen recovers the RFC 8439 2.8.2 plaintext" \
  aeadOpen "$TMP/aead-open.json" \
  'r["ok"] is True and r["plaintext"] == "'"$AEAD_PT"'"'

# One flipped ciphertext bit must NOT open. Without this the round trip
# above would pass against an "AEAD" that ignored the tag entirely.
AEAD_CT_BAD="d21a8d34${AEAD_CT:8}"
args "$TMP/aead-bad.json" \
  "{\"alg\":\"chacha20-poly1305\",\"key\":\"$AEAD_KEY\",\"nonce\":\"$AEAD_NONCE\",\"aad\":\"$AEAD_AAD\",\"ciphertext\":\"$AEAD_CT_BAD\"}"
check "aeadOpen refuses a flipped ciphertext bit" \
  aeadOpen "$TMP/aead-bad.json" \
  'r["ok"] is False and "authenticate" in r["error"]'

# AES-GCM is named in the ABI and refused with its issue, so a caller
# learns it is missing rather than getting a wrong answer or a bare
# "unknown alg". See https://github.com/danbri/factoidal/issues/677 .
args "$TMP/aead-aes.json" \
  "{\"alg\":\"aes-128-gcm\",\"key\":\"$AEAD_KEY\",\"nonce\":\"$AEAD_NONCE\",\"plaintext\":\"\"}"
check "aeadSeal names the AES-GCM gap and its issue" \
  aeadSeal "$TMP/aead-aes.json" \
  'r["ok"] is False and "677" in r["error"]'

HPKE_SKE="f4ec9b33b792c372c1d2c2063507b684ef925b8c75a42dbcbf57d63ccd381600"
HPKE_PKR="4310ee97d88cc1f088a5576c77ab0cf5c3ac797f3d95139c6c84b5429c59662a"
HPKE_SKR="8057991eef8f1f1af18f4a9491d16a1ce333f695d4db8e38da75975c4478e0fb"
HPKE_INFO="4f6465206f6e2061204772656369616e2055726e"
HPKE_AAD="436f756e742d30"
HPKE_PT="4265617574792069732074727574682c20747275746820626561757479"
HPKE_ENC="1afa08d3dec047a643885163f1180476fa7ddb54c6a8029ea33f95796bf2ac4a"
HPKE_CT="1c5250d8034ec2b784ba2cfd69dbdb8af406cfe3ff938e131f0def8c8b60b4db21993c62ce81883d2dd1b51a28"

args "$TMP/hpke-seal.json" \
  "{\"skE\":\"$HPKE_SKE\",\"pkR\":\"$HPKE_PKR\",\"info\":\"$HPKE_INFO\",\"aad\":\"$HPKE_AAD\",\"plaintext\":\"$HPKE_PT\"}"
check "hpkeSeal reproduces RFC 9180 A.2.1 enc and ct (sequence number 0)" \
  hpkeSeal "$TMP/hpke-seal.json" \
  'r["ok"] is True and r["enc"] == "'"$HPKE_ENC"'" and r["ciphertext"] == "'"$HPKE_CT"'"
   and r["message"] == r["enc"] + r["ciphertext"]'

args "$TMP/hpke-open.json" \
  "{\"skR\":\"$HPKE_SKR\",\"info\":\"$HPKE_INFO\",\"aad\":\"$HPKE_AAD\",\"message\":\"$HPKE_ENC$HPKE_CT\"}"
check "hpkeOpen recovers the RFC 9180 A.2.1 plaintext" \
  hpkeOpen "$TMP/hpke-open.json" \
  'r["ok"] is True and r["plaintext"] == "'"$HPKE_PT"'"'

args "$TMP/hpke-badinfo.json" \
  "{\"skR\":\"$HPKE_SKR\",\"info\":\"00\",\"aad\":\"$HPKE_AAD\",\"message\":\"$HPKE_ENC$HPKE_CT\"}"
check "hpkeOpen refuses a changed info" \
  hpkeOpen "$TMP/hpke-badinfo.json" \
  'r["ok"] is False and "authenticate" in r["error"]'

args "$TMP/hpke-shortkey.json" \
  "{\"skE\":\"00\",\"pkR\":\"$HPKE_PKR\",\"plaintext\":\"\"}"
check "hpkeSeal refuses a 1-byte ephemeral key" \
  hpkeSeal "$TMP/hpke-shortkey.json" \
  'r["ok"] is False and "32 bytes" in r["error"]'

# --- Formats, transforms, reasoning (issue 713, stage 1) ---------------
# One positive and one negative case per op. The envelope members are the
# ones bin/npm-entry/entry_extras.ml pins and lib/api.js reads.

# JSON-LD
args "$TMP/jl-to.json" \
  '{"@context":{"foaf":"http://xmlns.com/foaf/0.1/","name":"foaf:name"},"@id":"alice","name":"Alice"}' \
  '{"base":"http://example.org/"}'
check "jsonldToRdf resolves @id against the base option" jsonldToRdf "$TMP/jl-to.json" \
  'r["ok"] is True and r["nquads"] == "<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> \"Alice\" .\n"'
args "$TMP/jl-to-remote.json" '{"@context":"http://example.org/ctx","@id":"http://e/a"}' ''
check "jsonldToRdf remote @context, no loader -> error" jsonldToRdf "$TMP/jl-to-remote.json" \
  'r["ok"] is False and "remote context" in r["error"]'
args "$TMP/jl-from.json" '<http://ex/s> <http://ex/p> "5"^^<http://www.w3.org/2001/XMLSchema#integer> .' '{"useNativeTypes":true}'
check "jsonldFromRdf useNativeTypes -> JSON number" jsonldFromRdf "$TMP/jl-from.json" \
  'r["ok"] is True and r["jsonld"] == "[{\"@id\":\"http://ex/s\",\"http://ex/p\":[{\"@value\":5}]}]"'
args "$TMP/jl-from-bad.json" 'this is not n-quads' ''
check "jsonldFromRdf bad N-Quads -> error" jsonldFromRdf "$TMP/jl-from-bad.json" \
  'r["ok"] is False and "jsonldFromRdf" in r["error"]'

# RML (one logical source; the data text is the second argument)
RML_TTL='@prefix rml: <http://w3id.org/rml/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex: <http://example.org/> .
ex:TM a rml:TriplesMap ;
  rml:logicalSource [ a rml:LogicalSource ; rml:iterator "$.people[*]" ;
    rml:referenceFormulation rml:JSONPath ;
    rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "x" ] ] ;
  rml:subjectMap [ rml:template "http://example.org/person/{$.id}" ] ;
  rml:predicateObjectMap [ rml:predicate foaf:name ; rml:objectMap [ rml:reference "$.name" ] ] .'
args "$TMP/rml-parse.json" "$RML_TTL" turtle ""
RML_NQ="$("$CLI" call parseToDatasetJson "$TMP/rml-parse.json" | python3 -c 'import json,sys; print(json.load(sys.stdin)["nquads"], end="")')"
args "$TMP/rml.json" "$RML_NQ" '{"people":[{"id":"1","name":"Alice"},{"id":"2","name":"Bob"}]}' json
check "rmlMap JSON source" rmlMap "$TMP/rml.json" \
  'r["ok"] is True and r["nquads"].count(" .") == 2 and "person/1> <http://xmlns.com/foaf/0.1/name> \"Alice\"" in r["nquads"]'
args "$TMP/rml-badkind.json" "$RML_NQ" '{}' xml
check "rmlMap unknown sourceKind -> error" rmlMap "$TMP/rml-badkind.json" \
  'r["ok"] is False and "sourceKind" in r["error"]'
args "$TMP/rml-baddata.json" "$RML_NQ" 'not json' json
check "rmlMap source that is not JSON -> error" rmlMap "$TMP/rml-baddata.json" \
  'r["ok"] is False and "rmlMap" in r["error"]'

# CSVW
CSV='GID,on_street
1,ADDISON AV
2,ELM ST
'
args "$TMP/csvw.json" "$CSV" "" '{"base":"http://example.org/","url":"t.csv"}'
check "csvwToRdf standard mode, header-inferred table" csvwToRdf "$TMP/csvw.json" \
  'r["ok"] is True and "csvw#TableGroup" in r["nquads"] and r["nquads"].count("csvw#rownum") == 2 and "ADDISON AV" in r["nquads"]'
args "$TMP/csvw-min.json" "$CSV" "" '{"mode":"minimal","base":"http://example.org/","url":"t.csv"}'
check "csvwToRdf minimal mode has no table-group wrapper" csvwToRdf "$TMP/csvw-min.json" \
  'r["ok"] is True and "TableGroup" not in r["nquads"] and r["nquads"].count(" .") == 4'
args "$TMP/csvw-badmeta.json" "$CSV" "not json" ""
check "csvwToRdf undecodable metadata -> error" csvwToRdf "$TMP/csvw-badmeta.json" \
  'r["ok"] is False and "metadata" in r["error"]'
args "$TMP/csvw-badmode.json" "$CSV" "" '{"mode":"weird"}'
check "csvwToRdf unknown mode -> error" csvwToRdf "$TMP/csvw-badmode.json" \
  'r["ok"] is False and "mode" in r["error"]'

# XML, XPath, XSLT
args "$TMP/xml-ok.json" '<a><b/></a>'
check "xmlWellformed accepts" xmlWellformed "$TMP/xml-ok.json" \
  'r["ok"] is True and r["wellformed"] is True'
args "$TMP/xml-bad.json" '<a><b></a>'
check "xmlWellformed rejects" xmlWellformed "$TMP/xml-bad.json" \
  'r["ok"] is True and r["wellformed"] is False'
args "$TMP/xp-num.json" '<r><a>1</a><a>2</a></r>' 'count(/r/a)'
check "xpathEval number" xpathEval "$TMP/xp-num.json" \
  'r["ok"] is True and r["resultType"] == "number" and float(r["value"]) == 2'
args "$TMP/xp-nodes.json" '<r><a>1</a><a>2</a></r>' '/r/a'
check "xpathEval node-set" xpathEval "$TMP/xp-nodes.json" \
  'r["ok"] is True and r["resultType"] == "nodeset" and r["count"] == 2 and r["nodes"][1] == {"kind":"element","name":"a","value":"2"}'
args "$TMP/xp-bad.json" '<r/>' 'count('
check "xpathEval unparsable expression -> error" xpathEval "$TMP/xp-bad.json" \
  'r["ok"] is False and "XPath" in r["error"]'
args "$TMP/xp-badxml.json" '<r>' '/r'
check "xpathEval XML that is not well-formed -> error" xpathEval "$TMP/xp-badxml.json" \
  'r["ok"] is False and "well-formed" in r["error"]'
XSL='<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/"><greeting><xsl:value-of select="/doc/name"/></greeting></xsl:template></xsl:stylesheet>'
args "$TMP/xslt.json" "$XSL" '<doc><name>World</name></doc>'
check "xsltTransform value-of" xsltTransform "$TMP/xslt.json" \
  'r["ok"] is True and r["output"] == "<greeting>World</greeting>"'
args "$TMP/xslt-bad.json" '<not well formed' '<doc/>'
check "xsltTransform malformed stylesheet -> error" xsltTransform "$TMP/xslt-bad.json" \
  'r["ok"] is False and "stylesheet" in r["error"]'

# Schematron, JSON Schema
SCH='<schema xmlns="http://purl.oclc.org/dsdl/schematron"><pattern><rule context="doc"><assert test="@ok">doc must carry an ok attribute</assert></rule></pattern></schema>'
args "$TMP/sch-fail.json" "$SCH" '<doc/>'
check "schematronValidate failing assert" schematronValidate "$TMP/sch-fail.json" \
  'r["ok"] is True and len(r["findings"]) == 1 and r["findings"][0]["type"] == "assert-fail" and "ok attribute" in r["findings"][0]["message"]'
args "$TMP/sch-pass.json" "$SCH" '<doc ok="yes"/>'
check "schematronValidate satisfied assert -> no finding" schematronValidate "$TMP/sch-pass.json" \
  'r["ok"] is True and r["findings"] == []'
args "$TMP/sch-bad.json" '<notschematron/>' '<doc/>'
check "schematronValidate not a schema -> error" schematronValidate "$TMP/sch-bad.json" \
  'r["ok"] is False and "schema" in r["error"]'
args "$TMP/js-pass.json" '{"type":"integer"}' '5'
check "jsonSchemaValidate pass" jsonSchemaValidate "$TMP/js-pass.json" \
  'r["ok"] is True and r["valid"] is True and r["result"] == "pass" and r["errors"] == []'
args "$TMP/js-fail.json" '{"type":"integer"}' '"hello"'
check "jsonSchemaValidate fail" jsonSchemaValidate "$TMP/js-fail.json" \
  'r["ok"] is True and r["valid"] is False and r["result"] == "fail" and len(r["errors"]) == 1'
args "$TMP/js-bad.json" '{"type":' '5'
check "jsonSchemaValidate invalid schema JSON -> error" jsonSchemaValidate "$TMP/js-bad.json" \
  'r["ok"] is False and "invalid JSON" in r["error"]'

# MathML, XForms
MML='<math xmlns="http://www.w3.org/1998/Math/MathML"><apply><plus/><cn>2</cn><cn>3</cn></apply></math>'
args "$TMP/mml.json" "$MML" '{}'
check "mathmlEval 2+3 = 5/1" mathmlEval "$TMP/mml.json" \
  'r["ok"] is True and r["value"] == {"kind":"rat","num":5,"den":1}'
args "$TMP/mml-div0.json" '<math xmlns="http://www.w3.org/1998/Math/MathML"><apply><divide/><cn>1</cn><cn>0</cn></apply></math>' '{}'
check "mathmlEval division by zero is undef" mathmlEval "$TMP/mml-div0.json" \
  'r["ok"] is True and r["value"]["kind"] == "undef" and isinstance(r["value"]["reason"], str)'
args "$TMP/mml-env.json" '<math xmlns="http://www.w3.org/1998/Math/MathML"><apply><times/><ci>x</ci><cn>2</cn></apply></math>' '{"x":"3"}'
check "mathmlEval ci binding" mathmlEval "$TMP/mml-env.json" \
  'r["ok"] is True and r["value"] == {"kind":"rat","num":6,"den":1}'
args "$TMP/mml-bad.json" "$MML" '[1]'
check "mathmlEval bindings that are not an object -> error" mathmlEval "$TMP/mml-bad.json" \
  'r["ok"] is False and "bindings" in r["error"]'
args "$TMP/xf.json" '<data><x>5</x><y>0</y></data>' '[{"target":"y","calculate":"7"}]'
check "xformsRecalc calculate writes the leaf" xformsRecalc "$TMP/xf.json" \
  'r["ok"] is True and "<y>7</y>" in r["instance"] and r["validity"][0]["target"] == "y" and r["validity"][0]["value"] == "7"'
args "$TMP/xf-bad.json" '<data><y>0</y></data>' '[{"calculate":"7"}]'
check "xformsRecalc bind without a target -> error" xformsRecalc "$TMP/xf-bad.json" \
  'r["ok"] is False and "target" in r["error"]'

# RIF Core
RIF_SYM='<?xml version="1.0" encoding="UTF-8"?>
<Document xmlns="http://www.w3.org/2007/rif#"><payload><Group><sentence><Forall>
<declare><Var>x</Var></declare><declare><Var>y</Var></declare>
<formula><Implies>
<if><Frame><object><Var>x</Var></object><slot ordered="yes"><Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const><Var>y</Var></slot></Frame></if>
<then><Frame><object><Var>y</Var></object><slot ordered="yes"><Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const><Var>x</Var></slot></Frame></then>
</Implies></formula></Forall></sentence></Group></payload></Document>'
args "$TMP/rif.json" "$RIF_SYM" '<http://example.org/alice> <http://xmlns.com/foaf/0.1/knows> <http://example.org/bob> .'
check "rifEval symmetric rule derives the inverse triple" rifEval "$TMP/rif.json" \
  'r["ok"] is True and r["inputCount"] == 1 and r["derivedCount"] == 1 and "<http://example.org/bob> <http://xmlns.com/foaf/0.1/knows> <http://example.org/alice>" in r["saturatedNquads"]'
args "$TMP/rif-bad.json" '<not rif' '<http://e/a> <http://e/p> <http://e/b> .'
check "rifEval rules that do not parse -> error" rifEval "$TMP/rif-bad.json" \
  'r["ok"] is False and "RIF-XML" in r["error"]'

# OWL tableau
OWL_NS='http://www.w3.org/2002/07/owl#'
RDF_TYPE='http://www.w3.org/1999/02/22-rdf-syntax-ns#type'
TAB_HV="<http://e/c> <${OWL_NS}equivalentClass> _:r .
_:r <${RDF_TYPE}> <${OWL_NS}Restriction> .
_:r <${OWL_NS}onProperty> <http://e/p> .
_:r <${OWL_NS}hasValue> <http://e/v> .
<http://e/i> <http://e/p> <http://e/v> .
"
args "$TMP/tab-mat.json" "$TAB_HV"
check "tableauMaterialise adds the restriction membership" tableauMaterialise "$TMP/tab-mat.json" \
  'r["ok"] is True and r["addedCount"] == 1 and r["budgetHit"] is False and "<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> _:" in r["nquads"]'
args "$TMP/tab-mat-none.json" "<http://e/a> <${RDF_TYPE}> <http://e/C> .
"
check "tableauMaterialise with nothing to add -> addedCount 0" tableauMaterialise "$TMP/tab-mat-none.json" \
  'r["ok"] is True and r["addedCount"] == 0'
args "$TMP/tab-mat-bad.json" 'garbage'
check "tableauMaterialise bad N-Quads -> error" tableauMaterialise "$TMP/tab-mat-bad.json" \
  'r["ok"] is False'
TAB_DL="<http://e/K> <${OWL_NS}equivalentClass> _:r .
_:r <${RDF_TYPE}> <${OWL_NS}Restriction> .
_:r <${OWL_NS}onProperty> <http://e/p> .
_:r <${OWL_NS}minCardinality> \"1\"^^<http://www.w3.org/2001/XMLSchema#nonNegativeInteger> .
<http://e/K> <${OWL_NS}disjointWith> <http://e/D> .
<http://e/i> <http://e/p> <http://e/v> .
<http://e/i> <${RDF_TYPE}> <http://e/D> .
"
args "$TMP/tab-dl.json" "$TAB_DL"
check "tableauDlInconsistent: clash only after materialisation (rlAlone false)" tableauDlInconsistent "$TMP/tab-dl.json" \
  'r["ok"] is True and r["inconsistent"] is True and r["rlAlone"] is False'
args "$TMP/tab-dl-rl.json" "<http://e/C> <${OWL_NS}disjointWith> <http://e/D> .
<http://e/a> <${RDF_TYPE}> <http://e/C> .
<http://e/a> <${RDF_TYPE}> <http://e/D> .
"
check "tableauDlInconsistent: RL clash is a DL clash" tableauDlInconsistent "$TMP/tab-dl-rl.json" \
  'r["ok"] is True and r["inconsistent"] is True and r["rlAlone"] is True'
args "$TMP/tab-dl-ok.json" "<http://e/a> <${RDF_TYPE}> <http://e/C> .
"
check "tableauDlInconsistent: consistent graph" tableauDlInconsistent "$TMP/tab-dl-ok.json" \
  'r["ok"] is True and r["inconsistent"] is False and r["rlAlone"] is False'

# queryRaw: every output format, ASK, CONSTRUCT, entailment, errors
RAW_DATA='@prefix ex: <http://example.org/> . ex:alice ex:name "Alice" . ex:bob ex:name "Bob" .'
RAW_Q='PREFIX ex: <http://example.org/> SELECT ?n WHERE { ?p ex:name ?n } ORDER BY ?n'
args "$TMP/raw-json.json" "$RAW_DATA" "$RAW_Q" ''
check "queryRaw default output is SPARQL results JSON" queryRaw "$TMP/raw-json.json" \
  'r["ok"] is True and json.loads(r["text"])["results"]["bindings"][1]["n"]["value"] == "Bob"'
args "$TMP/raw-csv.json" "$RAW_DATA" "$RAW_Q" '{"output":"csv"}'
check "queryRaw csv" queryRaw "$TMP/raw-csv.json" \
  'r["ok"] is True and r["text"] == "n\r\nAlice\r\nBob\r\n"'
args "$TMP/raw-tsv.json" "$RAW_DATA" "$RAW_Q" '{"output":"tsv"}'
check "queryRaw tsv" queryRaw "$TMP/raw-tsv.json" \
  'r["ok"] is True and r["text"] == "?n\n\"Alice\"\n\"Bob\"\n"'
args "$TMP/raw-xml.json" "$RAW_DATA" "$RAW_Q" '{"output":"xml"}'
check "queryRaw xml" queryRaw "$TMP/raw-xml.json" \
  'r["ok"] is True and "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">" in r["text"] and "<literal>Alice</literal>" in r["text"]'
args "$TMP/raw-table.json" "$RAW_DATA" "$RAW_Q" '{"output":"table"}'
check "queryRaw table" queryRaw "$TMP/raw-table.json" \
  'r["ok"] is True and "| ?n" in r["text"] and "2 result(s)" in r["text"]'
args "$TMP/raw-ask.json" "$RAW_DATA" 'PREFIX ex: <http://example.org/> ASK { ex:alice ex:name "Alice" }' ''
check "queryRaw ASK in JSON" queryRaw "$TMP/raw-ask.json" \
  'r["ok"] is True and json.loads(r["text"])["boolean"] is True'
args "$TMP/raw-ask-csv.json" "$RAW_DATA" 'PREFIX ex: <http://example.org/> ASK { ex:alice ex:name "Alice" }' '{"output":"csv"}'
check "queryRaw ASK has no CSV encoding -> error" queryRaw "$TMP/raw-ask-csv.json" \
  'r["ok"] is False and "ASK" in r["error"]'
args "$TMP/raw-con.json" "$RAW_DATA" 'PREFIX ex: <http://example.org/> CONSTRUCT { ?p ex:label ?n } WHERE { ?p ex:name ?n }' '{"output":"ntriples"}'
check "queryRaw CONSTRUCT as N-Triples" queryRaw "$TMP/raw-con.json" \
  'r["ok"] is True and r["text"].count(" .") == 2 and "<http://example.org/label> \"Alice\"" in r["text"]'
args "$TMP/raw-con-json.json" "$RAW_DATA" 'PREFIX ex: <http://example.org/> CONSTRUCT { ?p ex:label ?n } WHERE { ?p ex:name ?n }' '{"output":"json"}'
check "queryRaw CONSTRUCT has no JSON results format -> error" queryRaw "$TMP/raw-con-json.json" \
  'r["ok"] is False and "CONSTRUCT" in r["error"]'
RAW_RDFS='@prefix schema: <http://schema.org/> . @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . @prefix ex: <http://example.org/> . schema:Hotel rdfs:subClassOf schema:Place . ex:motel6 a schema:Hotel .'
RAW_PLACE='PREFIX schema: <http://schema.org/> SELECT ?s WHERE { ?s a schema:Place }'
args "$TMP/raw-rdfs.json" "$RAW_RDFS" "$RAW_PLACE" '{"entail":"RDFS"}'
check "queryRaw entail RDFS sees the subclass instance" queryRaw "$TMP/raw-rdfs.json" \
  'r["ok"] is True and len(json.loads(r["text"])["results"]["bindings"]) == 1'
args "$TMP/raw-norfds.json" "$RAW_RDFS" "$RAW_PLACE" ''
check "queryRaw without entailment sees none" queryRaw "$TMP/raw-norfds.json" \
  'r["ok"] is True and len(json.loads(r["text"])["results"]["bindings"]) == 0'
args "$TMP/raw-badq.json" "$RAW_DATA" 'SELECT WITHOUT' ''
check "queryRaw bad SPARQL -> error" queryRaw "$TMP/raw-badq.json" \
  'r["ok"] is False and "SPARQL" in r["error"]'
args "$TMP/raw-badout.json" "$RAW_DATA" "$RAW_Q" '{"output":"yaml"}'
check "queryRaw unknown output -> error" queryRaw "$TMP/raw-badout.json" \
  'r["ok"] is False and "output" in r["error"]'

# queryHdt: the vendored hdt-cpp 1.3.3 fixture is the blob region
HDT_FIXTURE="$LEAN_DIR/../../third_party/testing/hdt/rdf-mt-test002.hdt"
if [ -f "$HDT_FIXTURE" ]; then
  args "$TMP/hdt-sel.json" 'SELECT ?s ?o WHERE { ?s <http://example.org/bar> ?o }'
  checkblob "queryHdt SELECT over an HDT file" queryHdt "$TMP/hdt-sel.json" "$HDT_FIXTURE" \
    'r["ok"] is True and r["kind"] == "select" and r["srj"]["results"]["bindings"][0]["o"]["value"] == "flargh"'
  args "$TMP/hdt-ask.json" 'ASK { <http://example.org/foo> <http://example.org/bar> ?o }'
  checkblob "queryHdt ASK over an HDT file" queryHdt "$TMP/hdt-ask.json" "$HDT_FIXTURE" \
    'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'
  args "$TMP/hdt-ask-no.json" 'ASK { <http://example.org/foo> <http://example.org/nothere> ?o }'
  checkblob "queryHdt ASK for an absent triple is false" queryHdt "$TMP/hdt-ask-no.json" "$HDT_FIXTURE" \
    'r["ok"] is True and r["boolean"] is False'

  # The pure byte-region entry takes the instant as a second argument (issue 748).
  args "$TMP/hdt-now.json" "$NOWASK" "$NOWFIXED"
  checkblob "queryHdt through the pure callBlob binds NOW() to the instant it is given" queryHdt "$TMP/hdt-now.json" "$HDT_FIXTURE" \
    'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'
  args "$TMP/hdt-now-none.json" "$NOWASK"
  checkblob "queryHdt through the pure callBlob with no instant: NOW() is an error, ASK is false" queryHdt "$TMP/hdt-now-none.json" "$HDT_FIXTURE" \
    'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is False'
  args "$TMP/hdt-now-bad.json" "$NOWASK" "tomorrow"
  checkblob "queryHdt through the pure callBlob with a bad instant -> error" queryHdt "$TMP/hdt-now-bad.json" "$HDT_FIXTURE" \
    'r["ok"] is False and "not an xsd:dateTime lexical form" in r["error"]'
else
  echo "SKIP queryHdt: $HDT_FIXTURE is absent (run tools/ensure-test-env.sh)"
fi
printf 'this is not an HDT file' > "$TMP/not-hdt.bin"
args "$TMP/hdt-junk.json" 'ASK { ?s ?p ?o }'
checkblob "queryHdt bytes that are not HDT -> error" queryHdt "$TMP/hdt-junk.json" "$TMP/not-hdt.bin" \
  'r["ok"] is False and "HDT" in r["error"]'
check "queryHdt through the plain call has no bytes -> error" queryHdt "$TMP/hdt-junk.json" \
  'r["ok"] is False and "blob" in r["error"]'

# SERVICE endpoint registry (callIO only; the registry lives in the process).
# With no endpoint registered, SERVICE without SILENT is an error envelope
# and SERVICE SILENT is one solution with no bindings (SPARQL 1.1
# Federated Query 2.3; https://github.com/danbri/factoidal/issues/717).
python3 - "$TMP/svc-seq.json" <<'EOF'
import json, sys
SVC = "SELECT ?s ?o WHERE { SERVICE <http://example.org/sparql> { ?s <http://e/p> ?o } }"
SVC_SILENT = "SELECT ?s ?o WHERE { SERVICE SILENT <http://example.org/sparql> { ?s <http://e/p> ?o } }"
DATA = "<http://e/x> <http://e/q> <http://e/y> ."
seq = [
  ["queryDataset", [DATA, SVC]],
  ["registerServiceEndpoint", ["http://example.org/sparql", "<http://e/a> <http://e/p> \"v\" ."]],
  ["queryDataset", [DATA, SVC]],
  ["datasetOpen", [DATA, "nquads", ""]],
  ["datasetQuery", ["h1", SVC]],
  ["registerServiceEndpoint", ["http://example.org/sparql", "<http://e/a> <http://e/p> \"w\" ."]],
  ["queryDataset", [DATA, SVC]],
  ["registerServiceEndpoint", ["", "<http://e/a> <http://e/p> \"v\" ."]],
  ["registerServiceEndpoint", ["http://example.org/sparql", "garbage"]],
  ["clearServiceEndpoints", []],
  ["queryDataset", [DATA, SVC]],
  ["queryDataset", [DATA, SVC_SILENT]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "SERVICE endpoint registry: register, replace, clear, errors" "$TMP/svc-seq.json" \
  'len(rs) == 12
   and rs[0]["ok"] is False and "SERVICE <http://example.org/sparql> failed" in rs[0]["error"]
   and rs[1] == {"ok": True, "count": 1}
   and [b["o"]["value"] for b in rs[2]["srj"]["results"]["bindings"]] == ["v"]
   and [b["o"]["value"] for b in rs[4]["srj"]["results"]["bindings"]] == ["v"]
   and [b["o"]["value"] for b in rs[6]["srj"]["results"]["bindings"]] == ["w"]
   and rs[7]["ok"] is False and "empty" in rs[7]["error"]
   and rs[8]["ok"] is False and "registerServiceEndpoint" in rs[8]["error"]
   and rs[9] == {"ok": True}
   and rs[10]["ok"] is False and "SERVICE <http://example.org/sparql> failed" in rs[10]["error"]
   and rs[11]["srj"]["results"]["bindings"] == [{}]'

# --- Envelope parity, https://github.com/danbri/factoidal/issues/685 ----
# Positioned parse errors, prefixes, per-document blank-node scope,
# serializeTurtleWith / datasetSerializeWith and bare literals.
args "$TMP/pe-ttl.json" 'this is not turtle' turtle ""
check "parse error carries offset, line, column and format (Turtle)" parseToDatasetJson "$TMP/pe-ttl.json" \
  'r["ok"] is False and r["line"] == 1 and r["column"] == 5 and r["offset"] == 4
   and r["format"] == "turtle" and r["error"].endswith("at line 1, column 5")'
python3 - "$TMP/pe-dot.json" <<'EOF'
import json, sys
text = "@prefix ex: <http://example.org/> .\nex:a ex:p ex:o\nex:b ex:p ex:o2 .\n"
json.dump([text, "turtle", ""], open(sys.argv[1], "w"))
EOF
check "a Turtle statement missing its dot is reported on the FOLLOWING line (line 3)" \
  parseToDatasetJson "$TMP/pe-dot.json" \
  'r["ok"] is False and r["line"] == 3 and r["column"] == 1 and "line 3, column 1" in r["error"]'
python3 - "$TMP/pe-utf8.json" <<'EOF'
import json, sys
# The failure is on line 2; the column counts scalar values, not bytes.
json.dump(["# ééé\n<http://x/s> <http://x/p> .", "ttl", ""], open(sys.argv[1], "w"))
EOF
check "the column of a parse error counts Unicode scalar values" parseToDatasetJson "$TMP/pe-utf8.json" \
  'r["ok"] is False and r["line"] == 2 and r["column"] == 27'
args "$TMP/pe-nt.json" '<http://x/s> <http://x/p> .' ntriples ""
check "parse error carries a position (N-Triples)" parseToDatasetJson "$TMP/pe-nt.json" \
  'r["ok"] is False and r["line"] == 1 and r["offset"] == r["column"] - 1 and r["format"] == "ntriples"'
args "$TMP/pe-nq.json" '<http://x/s> <http://x/p> .' nquads ""
check "parse error carries a position (N-Quads)" parseToDatasetJson "$TMP/pe-nq.json" \
  'r["ok"] is False and r["line"] == 1 and "offset" in r and r["format"] == "nquads"'
args "$TMP/pe-trig.json" '@prefix ex: <http://x/> . GRAPH ex:g { ex:s ex:p' trig ""
check "parse error carries a position (TriG)" parseToDatasetJson "$TMP/pe-trig.json" \
  'r["ok"] is False and r["line"] == 1 and "column" in r and r["format"] == "trig"'
args "$TMP/pe-xml.json" '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"><rdf:Description rdf:nodeID="333-555-666" /></rdf:RDF>' rdfxml ""
check "an RDF/XML failure carries a message and a format, no position" parseToDatasetJson "$TMP/pe-xml.json" \
  'r["ok"] is False and "line" not in r and "offset" not in r and r["format"] == "rdfxml"'
args "$TMP/pe-rel.json" '<a> <b> <c> .' turtle ""
check "a relative IRI with no base is a positioned error naming the IRI" parseToDatasetJson "$TMP/pe-rel.json" \
  'r["ok"] is False and "IRI" in r["error"] and r["line"] == 1'
args "$TMP/pe-tag.json" 'x' "Bogus" ""
check "an unknown format tag answers the message and the tag, lower-cased" parseToDatasetJson "$TMP/pe-tag.json" \
  'r["ok"] is False and "line" not in r and r["format"] == "bogus"'

python3 - "$TMP/pfx.json" <<'EOF'
import json, sys
text = ("@prefix ex: <http://example.org/> .\n@prefix a: <http://a.org/> .\n"
        "@prefix ex: <http://other.org/> .\nex:s a:p 1 .\n")
json.dump([text, "turtle", ""], open(sys.argv[1], "w"))
EOF
check "prefixes: each label once, its latest binding, in declaration order" parseToDatasetJson "$TMP/pfx.json" \
  'r["ok"] is True and list(r["prefixes"].items()) == [("a", "http://a.org/"), ("ex", "http://other.org/")]'
args "$TMP/pfx-trig2.json" '@prefix ex: <http://x/> . <http://x/g> { ex:s ex:p ex:o }' trig ""
check "prefixes are recorded for TriG" parseToDatasetJson "$TMP/pfx-trig2.json" \
  'r["ok"] is True and r["prefixes"] == {"ex": "http://x/"}'
args "$TMP/pfx-nq.json" '<http://x/s> <http://x/p> <http://x/o> .' nquads ""
check "N-Quads has no prefixes: an empty object" parseToDatasetJson "$TMP/pfx-nq.json" \
  'r["ok"] is True and r["prefixes"] == {}'

# Blank-node scope: two documents that both write _:b0 stay two nodes. This
# needs one process (a counter), so it is a callseq.
python3 - "$TMP/scope-seq.json" <<'EOF'
import json, sys
json.dump([["parseToDatasetJson", ['_:b0 <http://x/p> "one" .', "nquads", ""]],
           ["parseToDatasetJson", ['_:b0 <http://x/p> "two" .', "nquads", ""]],
           ["parseToDatasetJson", ['@prefix x: <http://x/> . [] x:p "three" .', "turtle", ""]],
           ["parseToDatasetJson", ['_:b0 <http://x/p> "one" .', "nquads", ""]]],
          open(sys.argv[1], "w"))
EOF
checkseq "each parse gets its own blank-node scope (d0_, d1_, d2_, d3_)" "$TMP/scope-seq.json" \
  'len(rs) == 4 and all(r["ok"] is True for r in rs)
   and rs[0]["nquads"].startswith("_:d0_b0 ") and rs[1]["nquads"].startswith("_:d1_b0 ")
   and rs[2]["nquads"].startswith("_:d2_") and rs[3]["nquads"].startswith("_:d3_b0 ")
   and len({line.split(" ")[0] for r in rs for line in r["nquads"].splitlines()}) == 4'

# Dataset handle: prefixes recorded at open, positioned error, serialization.
python3 - "$TMP/h685-seq.json" <<'EOF'
import json, sys
ttl = "@prefix ex: <http://example.org/> .\nex:s ex:p 1, true, 1.5, \"x\", 5. .\n".replace("5. .", "\"5.\"^^<http://www.w3.org/2001/XMLSchema#decimal> .")
seq = [["datasetOpen", [ttl, "turtle", ""]],
       ["datasetSerialize", ["h1", "turtle"]],
       ["datasetSerializeWith", ["h1", "turtle", json.dumps({"literalShorthand": False})]],
       ["datasetSerializeWith", ["h1", "turtle", json.dumps({"prefixes": {"e": "http://example.org/"}})]],
       ["datasetSerializeWith", ["h1", "turtle", json.dumps({"prefixes": {}})]],
       ["datasetSerializeWith", ["h1", "turtle", "{"]],
       ["datasetSerializeWith", ["h1", "nquads", ""]],
       ["datasetSerializeWith", ["h1", "n3", ""]],
       ["datasetSerializeWith", ["h9", "turtle", ""]],
       ["datasetOpen", ["this is not turtle", "turtle", ""]],
       ["datasetClose", ["h1"]]]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "dataset handle: prefixes at open, handle prefixes in output, serializeWith options, bare literals" \
  "$TMP/h685-seq.json" \
  'len(rs) == 11
   and rs[0]["ok"] is True and rs[0]["handle"] == "h1" and rs[0]["count"] == 5
   and rs[0]["prefixes"] == {"ex": "http://example.org/"}
   and "@prefix ex: <http://example.org/> ." in rs[1]["turtle"]
   and "ex:s ex:p 1 , 1.5 , " in rs[1]["turtle"] and ", true , " in rs[1]["turtle"]
   and rs[1]["turtle"].count("^^") == 1
   and rs[2]["turtle"].count("^^") == 4 and "ex:s ex:p" in rs[2]["turtle"]
   and "@prefix e: <http://example.org/> ." in rs[3]["turtle"] and "e:s e:p" in rs[3]["turtle"]
   and "ex:" not in rs[3]["turtle"]
   and "@prefix ex:" not in rs[4]["turtle"] and "@prefix ns1: <http://example.org/> ." in rs[4]["turtle"]
   and rs[5]["ok"] is False and "optionsJson" in rs[5]["error"]
   and rs[6]["ok"] is True and "nquads" in rs[6]
   and rs[7]["ok"] is False and "unknown format tag" in rs[7]["error"]
   and rs[8]["ok"] is False and "unknown dataset handle" in rs[8]["error"]
   and rs[9]["ok"] is False and rs[9]["line"] == 1 and rs[9]["format"] == "turtle"
   and rs[10]["ok"] is True'

# serializeTurtleWith (stateless): the options, the default, and a bad optionsJson.
python3 - "$TMP/stw.json" <<'EOF'
import json, sys
nq = '<http://x/s> <http://x/p> "1"^^<http://www.w3.org/2001/XMLSchema#integer> .\n'
json.dump([nq, json.dumps({"prefixes": {"ex": "http://x/"}, "literalShorthand": False})], open(sys.argv[1], "w"))
EOF
check "serializeTurtleWith: caller prefix wins, shorthand off keeps the quoted form" serializeTurtleWith "$TMP/stw.json" \
  'r["ok"] is True and "@prefix ex: <http://x/> ." in r["turtle"] and "ex:s ex:p \"1\"^^xsd:integer ." in r["turtle"]'
python3 - "$TMP/stw2.json" <<'EOF'
import json, sys
nq = '<http://x/s> <http://x/p> "1"^^<http://www.w3.org/2001/XMLSchema#integer> .\n'
json.dump([nq, ""], open(sys.argv[1], "w"))
EOF
check "serializeTurtleWith with no options prints the integer bare" serializeTurtleWith "$TMP/stw2.json" \
  'r["ok"] is True and "^^" not in r["turtle"] and " 1 ." in r["turtle"]'
python3 - "$TMP/stw3.json" <<'EOF'
import json, sys
json.dump(['<http://x/s> <http://x/p> <http://x/o> .\n', "not json"], open(sys.argv[1], "w"))
EOF
check "serializeTurtleWith refuses an optionsJson that is not JSON" serializeTurtleWith "$TMP/stw3.json" \
  'r["ok"] is False and "optionsJson" in r["error"]'
python3 - "$TMP/stw4.json" <<'EOF'
import json, sys
nq = ('<http://x/s> <http://x/p> "5."^^<http://www.w3.org/2001/XMLSchema#decimal> .\n'
      '<http://x/s> <http://x/p> "1e3"^^<http://www.w3.org/2001/XMLSchema#double> .\n'
      '<http://x/s> <http://x/p> "false"^^<http://www.w3.org/2001/XMLSchema#boolean> .\n'
      '<http://x/s> <http://x/p> " 7"^^<http://www.w3.org/2001/XMLSchema#integer> .\n')
json.dump([nq, ""], open(sys.argv[1], "w"))
EOF
check "bare literals only when the lexical form is the terminal: 1e3 and false bare, 5. and ' 7' quoted" \
  serializeTurtleWith "$TMP/stw4.json" \
  'r["ok"] is True and " 1e3" in r["turtle"] and " false" in r["turtle"]
   and "\"5.\"^^xsd:decimal" in r["turtle"] and "\" 7\"^^xsd:integer" in r["turtle"]'

# --- Stage 2 of https://github.com/danbri/factoidal/issues/713 ---------
# Matrix and sigmoid (Wasm/Ops/Maths.lean). Envelope shapes follow
# bin/npm-entry/entry_extras.ml.
args "$TMP/m-det.json" '[[1,2],[3,4]]'
check "matrixDeterminant 2x2 is exact" matrixDeterminant "$TMP/m-det.json" \
  'r["ok"] is True and r["result"] == "-2" and r["reason"] == ""'
args "$TMP/m-det-ns.json" '[[1,2,3],[4,5,6]]'
check "matrixDeterminant of a non-square matrix is undef with a reason" \
  matrixDeterminant "$TMP/m-det-ns.json" \
  'r["ok"] is True and r["result"] == "undef" and "square" in r["reason"]'
args "$TMP/m-det-rat.json" '[[[1,2],0],[0,[1,2]]]'
check "matrixDeterminant keeps exact rational entries" matrixDeterminant "$TMP/m-det-rat.json" \
  'r["ok"] is True and r["result"] == "1/4"'
args "$TMP/m-det-zero-den.json" '[[1,[1,0]],[3,4]]'
check "matrixDeterminant with a zero denominator is undef, division-by-zero" \
  matrixDeterminant "$TMP/m-det-zero-den.json" \
  'r["ok"] is True and r["result"] == "undef" and r["reason"] == "division-by-zero"'
args "$TMP/m-det-badjson.json" 'not json'
check "matrixDeterminant on invalid JSON -> error" matrixDeterminant "$TMP/m-det-badjson.json" \
  'r["ok"] is False and "invalid JSON" in r["error"]'
args "$TMP/m-det-badcell.json" '[[1.5,2],[3,4]]'
check "matrixDeterminant refuses a non-integer cell" matrixDeterminant "$TMP/m-det-badcell.json" \
  'r["ok"] is False and "each cell" in r["error"]'
args "$TMP/m-dot.json" '[1,2,3]' '[4,5,6]'
check "matrixScalarProduct" matrixScalarProduct "$TMP/m-dot.json" \
  'r["ok"] is True and r["result"] == "32"'
args "$TMP/m-dot-bad.json" '[1,2,3]' '[4,5]'
check "matrixScalarProduct of unequal lengths is undef" matrixScalarProduct "$TMP/m-dot-bad.json" \
  'r["ok"] is True and r["result"] == "undef" and "length" in r["reason"]'
args "$TMP/m-cross.json" '[1,0,0]' '[0,1,0]'
check "matrixVectorProduct e_x x e_y = e_z" matrixVectorProduct "$TMP/m-cross.json" \
  'r["ok"] is True and r["result"] == "[0,0,1]"'
args "$TMP/m-cross-bad.json" '[1,0]' '[0,1]'
check "matrixVectorProduct of 2-vectors is undef" matrixVectorProduct "$TMP/m-cross-bad.json" \
  'r["ok"] is True and r["result"] == "undef"'
args "$TMP/m-outer.json" '[1,2]' '[3,4]'
check "matrixOuterProduct" matrixOuterProduct "$TMP/m-outer.json" \
  'r["ok"] is True and r["result"] == "[[3,4],[6,8]]"'
args "$TMP/m-one-arg.json" '[1,2]'
check "matrixOuterProduct with one argument -> arity error" matrixOuterProduct "$TMP/m-one-arg.json" \
  'r["ok"] is False and "expects 2 arguments" in r["error"]'

args "$TMP/sig.json" '{"k":"1","x0":"0","l":"1","xmin":"-6","xmax":"6","n":"24"}'
check "sigmoidPoints: 25 points, exact midpoint, nine decimals" sigmoidPoints "$TMP/sig.json" \
  'r["ok"] is True and len(r["points"]) == 25
   and r["points"][12]["x"]["decimal"] == "0.000000000"
   and r["points"][12]["y"]["decimal"] == "0.500000000"
   and r["points"][12]["y"]["mantissa"] == "500000000" and r["points"][12]["y"]["scale"] == "9"
   and all(float(r["points"][i]["y"]["decimal"]) < float(r["points"][i + 1]["y"]["decimal"])
           for i in range(24))
   and abs(float(r["points"][0]["y"]["decimal"]) - 1 / (1 + 2.718281828459045 ** 6)) < 2e-9'
args "$TMP/sig-neg.json" '{"k":"1","x0":"0","l":"1","xmin":"-6","xmax":"6","n":"-1"}'
check "sigmoidPoints refuses a negative count" sigmoidPoints "$TMP/sig-neg.json" \
  'r["ok"] is False and "negative" in r["error"]'
args "$TMP/sig-missing.json" '{"k":"1"}'
check "sigmoidPoints names a missing field" sigmoidPoints "$TMP/sig-missing.json" \
  'r["ok"] is False and "x0" in r["error"]'
args "$TMP/sig-nodec.json" '{"k":"one","x0":"0","l":"1","xmin":"-6","xmax":"6","n":"2"}'
check "sigmoidPoints refuses a non-decimal parameter" sigmoidPoints "$TMP/sig-nodec.json" \
  'r["ok"] is False and "not a decimal" in r["error"]'
args "$TMP/empty0.json"
check "sigmoidFormulaMathml" sigmoidFormulaMathml "$TMP/empty0.json" \
  'r["ok"] is True and r["mathml"].startswith("<math ") and "<mfrac>" in r["mathml"]
   and "<msup><mi>e</mi>" in r["mathml"]'

# Ed25519 and SHA-256 (Wasm/Ops/Vc.lean), over the RFC 8032 section 7.1 vectors.
V1_SK=9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60
V1_PK=d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a
V1_SIG=e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b
V2_PK=3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c
V1_SIG_BAD="${V1_SIG:0:126}00"
args "$TMP/sha.json" abc
check "vcSha256Hex FIPS 180-4 abc" vcSha256Hex "$TMP/sha.json" \
  'r["ok"] is True and r["sha256"] == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"'
args "$TMP/ed-pk.json" "$V1_SK"
check "vcEd25519SecretToPublic RFC 8032 TEST 1" vcEd25519SecretToPublic "$TMP/ed-pk.json" \
  'r["ok"] is True and r["publicKeyHex"] == "'"$V1_PK"'"'
args "$TMP/ed-pk-bad.json" "ab"
check "vcEd25519SecretToPublic refuses a 1-byte key" vcEd25519SecretToPublic "$TMP/ed-pk-bad.json" \
  'r["ok"] is False and "malformed secret key" in r["error"]'
args "$TMP/ed-sign.json" "$V1_SK" ""
check "vcEd25519Sign RFC 8032 TEST 1 (empty message)" vcEd25519Sign "$TMP/ed-sign.json" \
  'r["ok"] is True and r["signatureHex"] == "'"$V1_SIG"'"'
args "$TMP/ed-sign-bad.json" "$V1_SK" "zz"
check "vcEd25519Sign refuses a non-hex message" vcEd25519Sign "$TMP/ed-sign-bad.json" \
  'r["ok"] is False and "malformed input" in r["error"]'
args "$TMP/ed-v-ok.json" "$V1_PK" "" "$V1_SIG"
check "vcEd25519Verify accepts the published triple" vcEd25519Verify "$TMP/ed-v-ok.json" \
  'r["ok"] is True and r["valid"] is True'
args "$TMP/ed-v-key.json" "$V2_PK" "" "$V1_SIG"
check "vcEd25519Verify REJECTS a wrong public key" vcEd25519Verify "$TMP/ed-v-key.json" \
  'r["ok"] is True and r["valid"] is False'
args "$TMP/ed-v-sig.json" "$V1_PK" "" "$V1_SIG_BAD"
check "vcEd25519Verify REJECTS a tampered signature" vcEd25519Verify "$TMP/ed-v-sig.json" \
  'r["ok"] is True and r["valid"] is False'
args "$TMP/ed-v-msg.json" "$V1_PK" "73" "$V1_SIG"
check "vcEd25519Verify REJECTS a different message" vcEd25519Verify "$TMP/ed-v-msg.json" \
  'r["ok"] is True and r["valid"] is False'
args "$TMP/ed-v-short.json" "ab" "" "$V1_SIG"
check "vcEd25519Verify REJECTS a 1-byte public key" vcEd25519Verify "$TMP/ed-v-short.json" \
  'r["ok"] is True and r["valid"] is False'
args "$TMP/ed-v-nonhex.json" "zz" "" "$V1_SIG"
check "vcEd25519Verify REJECTS a non-hex public key" vcEd25519Verify "$TMP/ed-v-nonhex.json" \
  'r["ok"] is True and r["valid"] is False'

# eddsa-rdfc-2022 over the canonical forms of the W3C vc-di-eddsa section 3.4
# test vectors (the same strings as VC/Tests.lean).
SPEC_SK=c96ef9ea10c5e414c471723aff9de72c35fa5b70fae97e8832ecac7d2e2b8ed6
SPEC_PK=b00d8d938e7f773d51565aad36a623f5344f7f5d1960f9cf3e8e12620ea2810f
SPEC_PV=z2YwC8z3ap7yx1nZYCg4L3j3ApHsF8kgPdSb5xoS1VR7vPG3F561B52hYnQF9iseabecm3ijx4K1FBTQsCZahKZme
SPEC_VM=did:key:z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2#z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2
cat > "$TMP/spec-doc.nq" <<'EOF'
<did:example:abcdefgh> <https://www.w3.org/ns/credentials/examples#alumniOf> "The School of Examples" .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/2018/credentials#VerifiableCredential> .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/ns/credentials/examples#AlumniCredential> .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/description> "A minimum viable example of an Alumni Credential." .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/name> "Alumni Credential" .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#credentialSubject> <did:example:abcdefgh> .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#issuer> <https://vc.example/issuers/5678> .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#validFrom> "2023-01-01T00:00:00Z"^^<http://www.w3.org/2001/XMLSchema#dateTime> .
EOF
{
  cat <<'EOF'
_:c14n0 <http://purl.org/dc/terms/created> "2023-02-24T23:36:38Z"^^<http://www.w3.org/2001/XMLSchema#dateTime> .
_:c14n0 <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://w3id.org/security#DataIntegrityProof> .
_:c14n0 <https://w3id.org/security#cryptosuite> "eddsa-rdfc-2022"^^<https://w3id.org/security#cryptosuiteString> .
_:c14n0 <https://w3id.org/security#proofPurpose> <https://w3id.org/security#assertionMethod> .
EOF
  printf '_:c14n0 <https://w3id.org/security#verificationMethod> <%s> .\n' "$SPEC_VM"
} > "$TMP/spec-cfg.nq"
# stage2args <out> <file-or-literal>... — an argument that names an existing
# file is replaced by that file's exact contents (a canonical form ends in a
# newline, which command substitution would strip).
stage2args() {
  local out="$1"; shift
  python3 - "$out" "$@" <<'EOF'
import json, os, sys
out, rest = sys.argv[1], sys.argv[2:]
json.dump([open(a).read() if os.path.isfile(a) else a for a in rest], open(out, "w"))
EOF
}
stage2args "$TMP/dix-create.json" "$SPEC_SK" "$TMP/spec-doc.nq" "$TMP/spec-cfg.nq"
check "vcEddsaCreateFromCanonical reproduces the W3C section 3.4 proofValue" \
  vcEddsaCreateFromCanonical "$TMP/dix-create.json" \
  'r["ok"] is True and r["proofValue"] == "'"$SPEC_PV"'"'
stage2args "$TMP/dix-create-bad.json" "ab" "$TMP/spec-doc.nq" "$TMP/spec-cfg.nq"
check "vcEddsaCreateFromCanonical refuses a 1-byte key" \
  vcEddsaCreateFromCanonical "$TMP/dix-create-bad.json" \
  'r["ok"] is False and "malformed key" in r["error"]'
stage2args "$TMP/dix-verify.json" "$SPEC_PK" "$TMP/spec-doc.nq" "$TMP/spec-cfg.nq" "$SPEC_PV"
check "vcEddsaVerifyFromCanonical accepts the W3C section 3.4 proof" \
  vcEddsaVerifyFromCanonical "$TMP/dix-verify.json" \
  'r["ok"] is True and r["verified"] is True'
stage2args "$TMP/dix-verify-key.json" "$V1_PK" "$TMP/spec-doc.nq" "$TMP/spec-cfg.nq" "$SPEC_PV"
check "vcEddsaVerifyFromCanonical REJECTS a wrong key" \
  vcEddsaVerifyFromCanonical "$TMP/dix-verify-key.json" \
  'r["ok"] is True and r["verified"] is False'
sed 's/Alumni Credential/Alumni CredentiaL/' "$TMP/spec-doc.nq" > "$TMP/spec-doc-bad.nq"
stage2args "$TMP/dix-verify-doc.json" "$SPEC_PK" "$TMP/spec-doc-bad.nq" "$TMP/spec-cfg.nq" "$SPEC_PV"
check "vcEddsaVerifyFromCanonical REJECTS a tampered document" \
  vcEddsaVerifyFromCanonical "$TMP/dix-verify-doc.json" \
  'r["ok"] is True and r["verified"] is False'
SPEC_PV_BAD="${SPEC_PV:0:5}${SPEC_PV:6:1}${SPEC_PV:5:1}${SPEC_PV:7}"
stage2args "$TMP/dix-verify-pv.json" "$SPEC_PK" "$TMP/spec-doc.nq" "$TMP/spec-cfg.nq" "$SPEC_PV_BAD"
check "vcEddsaVerifyFromCanonical REJECTS a tampered proofValue" \
  vcEddsaVerifyFromCanonical "$TMP/dix-verify-pv.json" \
  'r["ok"] is True and r["verified"] is False'
stage2args "$TMP/dix-verify-nomb.json" "$SPEC_PK" "$TMP/spec-doc.nq" "$TMP/spec-cfg.nq" "2YwC8z3a"
check "vcEddsaVerifyFromCanonical REJECTS a proofValue with no multibase prefix" \
  vcEddsaVerifyFromCanonical "$TMP/dix-verify-nomb.json" \
  'r["ok"] is True and r["verified"] is False'

# did:key
args "$TMP/did.json" "did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"
check "didKeyResolve returns the DID document as N-Triples" didKeyResolve "$TMP/did.json" \
  'r["ok"] is True and r["did"].startswith("did:key:z6Mk")
   and r["nquads"].count(" .\n") == 8 and "Ed25519VerificationKey2020" in r["nquads"]'
args "$TMP/did-secp.json" "did:key:zQ3shokFTS3brHcDQrn82RUDfCZESWL1ZdCEJwekUDPQiYBme"
check "didKeyResolve refuses a secp256k1 did:key" didKeyResolve "$TMP/did-secp.json" \
  'r["ok"] is False and "not a resolvable did:key" in r["error"]'
args "$TMP/did-web.json" "did:web:example.com"
check "didKeyResolve refuses another DID method" didKeyResolve "$TMP/did-web.json" \
  'r["ok"] is False'

# VCDM 2.0 checks (VC/Credential.lean, Doc).
V2CTX='{"@context":{"@protected":true}}'
VC_OK='{"@context":["https://www.w3.org/ns/credentials/v2"],"type":["VerifiableCredential"],"credentialSubject":{"id":"did:example:s"}}'
VC_NOSUBJ='{"@context":["https://www.w3.org/ns/credentials/v2"],"type":["VerifiableCredential"]}'
args "$TMP/vcc-ok.json" "$V2CTX" "$VC_OK"
check "vcCheckCredential accepts a minimal credential" vcCheckCredential "$TMP/vcc-ok.json" \
  'r["ok"] is True and r["valid"] is True and "reason" not in r'
args "$TMP/vcc-bad.json" "$V2CTX" "$VC_NOSUBJ"
check "vcCheckCredential REJECTS a credential with no subject, naming why" \
  vcCheckCredential "$TMP/vcc-bad.json" \
  'r["ok"] is True and r["valid"] is False and r["reason"] == "missing credentialSubject"'
args "$TMP/vcc-ctx.json" "$V2CTX" '{"@context":["https://ex.org/c","https://www.w3.org/ns/credentials/v2"],"type":["VerifiableCredential"],"credentialSubject":{"a":1}}'
check "vcCheckCredential REJECTS a base context that is not first" vcCheckCredential "$TMP/vcc-ctx.json" \
  'r["ok"] is True and r["valid"] is False and "FIRST" in r["reason"]'
args "$TMP/vcc-nojson.json" "$V2CTX" '{'
check "vcCheckCredential REJECTS malformed JSON" vcCheckCredential "$TMP/vcc-nojson.json" \
  'r["ok"] is True and r["valid"] is False and "not well-formed" in r["reason"]'
args "$TMP/vcc-badctx.json" 'nope' "$VC_OK"
check "vcCheckCredential with an unparseable v2 context -> error" vcCheckCredential "$TMP/vcc-badctx.json" \
  'r["ok"] is False and "v2ctx" in r["error"]'
args "$TMP/vcs-ok.json" '{"type":["VerifiableCredential"],"credentialSubject":{"a":1}}'
check "vcCheckCredentialSubject accepts a subject with no @context" vcCheckCredentialSubject "$TMP/vcs-ok.json" \
  'r["ok"] is True and r["valid"] is True'
args "$TMP/vcs-bad.json" '{"type":["VerifiableCredential"],"credentialSubject":{}}'
check "vcCheckCredentialSubject REJECTS an empty subject" vcCheckCredentialSubject "$TMP/vcs-bad.json" \
  'r["ok"] is True and r["valid"] is False and "no claims" in r["reason"]'
args "$TMP/vcl-ok.json" '{"@context":{"Known":"https://ex.org/Known","name":"https://schema.org/name"},"type":["Known"],"credentialSubject":{"name":"x"}}'
check "vcCheckNoDataLoss accepts defined terms" vcCheckNoDataLoss "$TMP/vcl-ok.json" \
  'r["ok"] is True and r["valid"] is True'
args "$TMP/vcl-type.json" '{"@context":{"Known":"https://ex.org/Known"},"type":["Unknown"],"credentialSubject":{"a":1}}'
check "vcCheckNoDataLoss REJECTS an undefined type term" vcCheckNoDataLoss "$TMP/vcl-type.json" \
  'r["ok"] is True and r["valid"] is False and "DATA_LOSS_DETECTION_ERROR" in r["reason"]'
args "$TMP/vcl-key.json" '{"@context":{"name":"https://schema.org/name","Known":"https://ex.org/Known"},"type":["Known"],"credentialSubject":{"nick":"x"}}'
check "vcCheckNoDataLoss REJECTS an undefined credentialSubject key" vcCheckNoDataLoss "$TMP/vcl-key.json" \
  'r["ok"] is True and r["valid"] is False and "credentialSubject" in r["reason"]'
args "$TMP/vcl-remote.json" '{"@context":"https://www.w3.org/ns/credentials/v2","type":["VerifiableCredential"],"credentialSubject":{"a":1}}'
check "vcCheckNoDataLoss REJECTS a remote context it cannot fetch" vcCheckNoDataLoss "$TMP/vcl-remote.json" \
  'r["ok"] is True and r["valid"] is False and "could not process @context" in r["reason"]'
RR_REG='[{"id":"https://www.w3.org/ns/credentials/v2","digestsHex":["24a18c90e9856d526111f29376e302d970b2bd10182e33959995b0207d7043b9"]}]'
RR_OK='{"@context":["https://www.w3.org/ns/credentials/v2"],"type":["VerifiableCredential"],"credentialSubject":{"a":1},"relatedResource":[{"id":"https://www.w3.org/ns/credentials/v2","digestMultibase":"uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k"}]}'
RR_BAD='{"@context":["https://www.w3.org/ns/credentials/v2"],"type":["VerifiableCredential"],"credentialSubject":{"a":1},"relatedResource":[{"id":"https://www.w3.org/ns/credentials/v2","digestMultibase":"uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7j"}]}'
args "$TMP/rr-ok.json" "$RR_REG" "$RR_OK"
check "vcCheckRelatedResourceDigests accepts a matching digestMultibase" \
  vcCheckRelatedResourceDigests "$TMP/rr-ok.json" \
  'r["ok"] is True and r["valid"] is True'
args "$TMP/rr-bad.json" "$RR_REG" "$RR_BAD"
check "vcCheckRelatedResourceDigests REJECTS a digest that matches no revision" \
  vcCheckRelatedResourceDigests "$TMP/rr-bad.json" \
  'r["ok"] is True and r["valid"] is False and "does not match" in r["reason"]'
args "$TMP/rr-one.json" "$RR_REG"
check "vcCheckRelatedResourceDigests with one argument -> arity error" \
  vcCheckRelatedResourceDigests "$TMP/rr-one.json" \
  'r["ok"] is False and "expects 2 arguments" in r["error"]'

args "$TMP/empty-stage2.json"
check "ops reflection lists the stage 2 ops" ops "$TMP/empty-stage2.json" \
  'set(["matrixDeterminant","matrixScalarProduct","matrixVectorProduct",
        "matrixOuterProduct","sigmoidPoints","sigmoidFormulaMathml",
        "vcSha256Hex","vcEd25519SecretToPublic","vcEd25519Sign","vcEd25519Verify",
        "vcEddsaCreateFromCanonical","vcEddsaVerifyFromCanonical",
        "vcCheckCredential","vcCheckCredentialSubject","vcCheckNoDataLoss",
        "vcCheckRelatedResourceDigests","didKeyResolve","parseDocument"]) <= set(r["ops"])'

# --- Stage 3 of issue 713: SPARQL 1.2 query ops, validation, regimes ---
TT12='<http://e/a> <http://e/says> <<( <http://e/s> <http://e/p> <http://e/o> )>> .
<http://e/b> <http://e/says> "plain" .
'
Q12='SELECT ?s WHERE { ?who <http://e/says> <<( ?s <http://e/p> <http://e/o> )>> }'
args "$TMP/q12.json" "$TT12" "$Q12"
check "queryDataset12 triple-term pattern" queryDataset12 "$TMP/q12.json" \
  'r["ok"] is True and r["kind"] == "select"
   and [b["s"]["value"] for b in r["srj"]["results"]["bindings"]] == ["http://e/s"]'
check "queryDataset (1.1 grammar) refuses the triple-term pattern" queryDataset "$TMP/q12.json" \
  'r["ok"] is False and "SPARQL parse error" in r["error"]'
python3 - "$TMP/handles-12.json" "$TT12" "$Q12" <<'EOF'
import json, sys
seq = [
  ["datasetOpen",    [sys.argv[2], "nquads12", ""]],
  ["datasetQuery12", ["h1", sys.argv[3]]],
  ["datasetQuery12", ["h1", "SELECT ?w WHERE { ?w <http://e/says> ?x FILTER(isTRIPLE(?x)) }"]],
  ["datasetQuery",   ["h1", sys.argv[3]]],
  ["datasetQuery12", ["h9", "ASK { ?s ?p ?o }"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "datasetQuery12 on a handle (triple term, isTRIPLE; 1.1 refuses; unknown handle)" "$TMP/handles-12.json" \
  'rs[0]["ok"] is True and rs[0]["count"] == 2
   and [b["s"]["value"] for b in rs[1]["srj"]["results"]["bindings"]] == ["http://e/s"]
   and [b["w"]["value"] for b in rs[2]["srj"]["results"]["bindings"]] == ["http://e/a"]
   and rs[3]["ok"] is False and "SPARQL parse error" in rs[3]["error"]
   and rs[4]["ok"] is False and rs[4]["error"] == "unknown dataset handle: h9"'

SHDATA='<http://e/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Person> .
<http://e/alice> <http://e/name> "Alice" .
<http://e/dave> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Person> .
'
SHAPES='<http://e/PS> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/ns/shacl#NodeShape> .
<http://e/PS> <http://www.w3.org/ns/shacl#targetClass> <http://e/Person> .
<http://e/PS> <http://www.w3.org/ns/shacl#property> _:p .
_:p <http://www.w3.org/ns/shacl#path> <http://e/name> .
_:p <http://www.w3.org/ns/shacl#minCount> "1"^^<http://www.w3.org/2001/XMLSchema#integer> .
'
args "$TMP/shacl.json" "$SHDATA" "$SHAPES"
check "shaclValidate: dave has no name -> conforms false, report names dave" shaclValidate "$TMP/shacl.json" \
  'r["ok"] is True and r["conforms"] is False and "http://e/dave" in r["reportNquads"]
   and "http://www.w3.org/ns/shacl#ValidationReport" in r["reportNquads"]'
args "$TMP/shacl-ok.json" "$(printf '%s' "$SHDATA" | head -2)
" "$SHAPES"
check "shaclValidate: alice alone conforms" shaclValidate "$TMP/shacl-ok.json" \
  'r["ok"] is True and r["conforms"] is True'
args "$TMP/shacl-bad.json" "not n-quads" "$SHAPES"
check "shaclValidate: bad data -> error" shaclValidate "$TMP/shacl-bad.json" 'r["ok"] is False'

SHEXC='PREFIX e: <http://e/>
e:S { e:name LITERAL }
'
args "$TMP/shex-yes.json" "$SHDATA" "$SHEXC" "http://e/alice" "http://e/S"
check "shexValidate ShExC: alice conforms" shexValidate "$TMP/shex-yes.json" \
  'r == {"ok": True, "verdict": True}'
args "$TMP/shex-no.json" "$SHDATA" "$SHEXC" "http://e/dave" "http://e/S"
check "shexValidate ShExC: dave does not" shexValidate "$TMP/shex-no.json" \
  'r == {"ok": True, "verdict": False}'
SHEXJ='{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://e/S","shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://e/name","valueExpr":{"type":"NodeConstraint","nodeKind":"literal"}}}}]}'
args "$TMP/shexj.json" "$SHDATA" "$SHEXJ" "http://e/alice" "http://e/S"
check "shexValidate ShExJ: alice conforms" shexValidate "$TMP/shexj.json" \
  'r == {"ok": True, "verdict": True}'
args "$TMP/shex-arity.json" "$SHDATA" "$SHEXC"
check "shexValidate wrong arity -> error" shexValidate "$TMP/shex-arity.json" \
  'r["ok"] is False and "expects 4 arguments" in r["error"]'

ENT='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .
<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .
<http://e/p> <http://www.w3.org/2002/07/owl#inverseOf> <http://e/q> .
<http://e/a> <http://e/p> <http://e/b> .
'
for regime in x-rdfscore x-rdfsplus; do
  args "$TMP/ent-$regime.json" "$ENT" 'ASK { <http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> }' "{\"dataFormat\":\"ntriples\",\"entail\":\"$regime\"}"
  check "queryRaw entail $regime: subclass membership entailed" queryRaw "$TMP/ent-$regime.json" \
    'r["ok"] is True and json.loads(r["text"])["boolean"] is True'
done
args "$TMP/ent-inv.json" "$ENT" 'ASK { <http://e/b> <http://e/q> <http://e/a> }' '{"dataFormat":"ntriples","entail":"x-rdfscore"}'
check "queryRaw entail x-rdfscore: owl:inverseOf not applied" queryRaw "$TMP/ent-inv.json" \
  'r["ok"] is True and json.loads(r["text"])["boolean"] is False'
args "$TMP/ent-bad.json" "$ENT" 'ASK { ?s ?p ?o }' '{"dataFormat":"ntriples","entail":"x-none-such"}'
check "queryRaw unknown entail regime -> error" queryRaw "$TMP/ent-bad.json" \
  'r["ok"] is False and "x-rdfsplus" in r["error"]'

args "$TMP/empty-stage3.json"
check "ops reflection lists the stage 3 ops" ops "$TMP/empty-stage3.json" \
  'set(["queryDataset12","datasetQuery12","shaclValidate","shexValidate"]) <= set(r["ops"])'

# --- Dispatch reflection + unknown op ---------------------------------
args "$TMP/empty.json"
check "ops reflection (incl. handle ops via callIO)" ops "$TMP/empty.json" \
  'r["ok"] is True and isinstance(r["abiVersion"], str)
   and set(["parseToDatasetJson","queryDataset","updateDataset",
            "serializeNQuads","serializeTurtle","canonicalizeToNQuads",
            "scanIBK2Predicate","scanIBK3Predicate","queryIBK3BlockSetPreview",
            "storeManifestInspect","storeQueryPlan","storeQuery",
            "owlClosure","owlIsConsistent","owlEntails",
            "rhoDfClosure","rhoDfFragmentCheck",
            "rdfsPlusClosure","clParse","clSerialize",
            "clAlphaNorm","clNormalize","clFiniteSat",
            "proofCheck","proofInspect",
            "toanSummation","toanProduct","toanSimplify",
            "toanDiff","toanSubst","ops",
            "datasetOpen","datasetQuery","datasetUpdate",
            "datasetSerialize","datasetClose",
            "activateVerify",
            "packBegin","packFeed","packEndPass",
            "packNext","packFinish","packClose",
            "lwsOpen","lwsStep","lwsClose",
            "solidOpen","solidStep","solidClose",
            "solidClientRequest","solidClientResponse",
            "aeadSeal","aeadOpen","hpkeSeal","hpkeOpen",
            "jsonldToRdf","jsonldFromRdf","rmlMap","csvwToRdf",
            "xmlWellformed","xpathEval","xsltTransform",
            "schematronValidate","jsonSchemaValidate","mathmlEval",
            "xformsRecalc","rifEval","tableauMaterialise",
            "tableauDlInconsistent","queryRaw","queryHdt",
            "registerServiceEndpoint","clearServiceEndpoints",
            "extRegister","extUnregister","extClear","extList"]) <= set(r["ops"])
   and r["blobOps"] == ["storeQuery","activateVerify","queryHdt"]
   and r["blobIoOps"] == ["blobEcho","packFeed","packNext"]'

check "unknown op -> error" definitelyNotAnOp "$TMP/empty.json" \
  'r["ok"] is False and "unknown op" in r["error"]'

# --- The core dispatch (l4factoidal-core.wasm, issue 713 stage 4) ------
# `l4wasm-cli corecall` drives Wasm/CoreDispatch.lean's `L4Wasm.Core.callIO`,
# the table the core wasm links.
corecheck() {
  local label="$1" op="$2" argsfile="$3" expr="$4"
  local out
  out="$("$CLI" corecall "$op" "$argsfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}
corecheck "core: ops reflection names the engine and the full-only ops" ops "$TMP/empty.json" \
  'r["ok"] is True and r["engine"] == "core" and "datasetOpen" in r["ops"]
   and "shaclValidate" in r["ops"] and "xpathEval" not in r["ops"]
   and "xpathEval" in r["fullOnlyOps"] and r["blobOps"] == [] and r["blobIoOps"] == []
   and r["fullOnlyFormats"] == ["jsonld", "json-ld", "application/ld+json"]'
corecheck "core: parseToDatasetJson turtle" parseToDatasetJson "$TMP/parse.json" \
  'r["ok"] is True and r["count"] == 1 and "example.org/alice" in r["nquads"]'
args "$TMP/core-q.json" "<http://e/a> <http://e/p> \"v\" ." "SELECT ?o WHERE { ?s ?p ?o }"
corecheck "core: queryDataset SELECT" queryDataset "$TMP/core-q.json" \
  'r["ok"] is True and "\"v\"" in json.dumps(r)'
# NOW() in the core table (https://github.com/danbri/factoidal/issues/743): the
# IO forms of queryDataset, updateDataset and queryRaw read the clock.
corecheck "core: queryDataset NOW() is the system clock" queryDataset "$TMP/now-select12.json" \
  'r["ok"] is True and '"$NOWOK"'(r["srj"]["results"]["bindings"][0]["n"]["value"])'
corecheck "core: updateDataset INSERT ... WHERE BIND(NOW()) inserts the system clock" updateDataset "$TMP/now-update.json" \
  'r["ok"] is True and '"$NOWOK"'(__import__("re").search(r"<http://e/at> \"([^\"]*)\"\^\^<'"$XSDDT"'>", r["nquads"]).group(1))'
corecheck "core: queryRaw NOW() is the system clock" queryRaw "$TMP/now-raw.json" \
  'r["ok"] is True and '"$NOWOK"'(r["text"].split("\r\n")[1])'
args "$TMP/core-x.json" "<a/>" "/a"
corecheck "core: a full-only op is refused naming the full engine" xpathEval "$TMP/core-x.json" \
  'r["ok"] is False and r["servedBy"] == "full" and "l4factoidal.wasm" in r["error"]'
args "$TMP/core-jl.json" '{"@id":"http://e/a","http://e/p":"v"}' "jsonld" ""
corecheck "core: JSON-LD is refused by name" parseToDatasetJson "$TMP/core-jl.json" \
  'r["ok"] is False and "not in the core engine" in r["error"]'
corecheck "core: unknown op -> error" definitelyNotAnOp "$TMP/empty.json" \
  'r["ok"] is False and "unknown op" in r["error"] and "servedBy" not in r'
check "full: ops reflection names the full engine" ops "$TMP/empty.json" \
  'r["ok"] is True and r["engine"] == "full"'

echo "=== native-smoke: $PASS pass, $FAIL fail, $XFAIL xfail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
