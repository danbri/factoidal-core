#!/usr/bin/env bash
#
# tests/sbm11/named_graphs.sh -- every named graph of an SBM11 store, also a graph
# with no triple and a graph named by a blank node, on the query path and the export
# (https://github.com/danbri/factoidal/issues/855 and
# https://github.com/danbri/factoidal/issues/856; record:
# docs/designissues/2026-10-12-sbm11-stage5.md section 12.7).
#
# RDF 1.1 Concepts section 4: a named graph is a graph name (an IRI or a blank node)
# and an RDF graph, and the RDF graph can be empty. SPARQL 1.1 Query section 18.6:
# `GRAPH ?g { }` gives one solution for each named graph of the dataset, and FROM
# NAMED selects a graph with no triple as it selects any other.
#
# The fixture is tests/sbm11/syntax/d5.trig: six named graphs, three IRIs and three
# blank nodes, two of each with no triple. The reference is the in-memory evaluator
# over the dataset that the source layer reads (`l4sbm11-w3c query-source` and
# `update-source`, which keep a graph with no triple); `l4factoidal query` reads its
# data through N-Quads, which cannot state one. The states:
#
#   base       the pack of d5.trig, no log
#   r1         a log: DROP GRAPH ex:g0, CREATE GRAPH ex:g9, CLEAR GRAPH ex:g1,
#              INSERT DATA into the new graph ex:g7 (DLOG version 1)
#   r1-gen2    r1 compacted and activated (the graph list of the new generation)
#   r2         a log: CLEAR NAMED, which names the three graphs named by a blank node
#              (DLOG version 3)
#   r2-gen2    r2 compacted and activated
#
# For each state, every query of tests/sbm11/graphs/ through `l4sbm11 query`, compared
# with the reference by tests/sbm11/compare_answers.py; a query named ids-* must run on
# ids (path=ids), one named ref-* on the reference fallback (path=reference: the id
# path refuses a GRAPH group with no triple pattern, FROM NAMED and MINUS). And
# `l4sbm11 graphs` of each generation; `l4sbm11 export` of each generation in TriG and
# JSON-LD, compared with the reference with the graphs with no triple kept
# (`l4sbm11-w3c compare --empty keep`); the N-Quads export, which writes the quads and
# names on standard error the graphs it cannot state; and the refusal of N-Triples
# without --graph.
#
# And expected failures that name open issues; the run fails when one passes:
# `l4factoidal query`, the in-memory query ops, gives neither a graph with no triple nor a
# graph named by a blank node (https://github.com/danbri/factoidal/issues/876); the IBK4
# and IBK5 stores refuse a graph with no triple, in the pack and in CREATE GRAPH and CLEAR
# GRAPH (https://github.com/danbri/factoidal/issues/880), and every update on them is refused
# (https://github.com/danbri/factoidal/issues/935).
#
# Prints "named graphs: N pass, M fail, K expected-fail (out of T)". Exit 0 when no case
# failed and no expected failure passed; 2 when a binary is missing.
#
# Env: L4_BIN_DIR   directory of the binaries (default formal/lean4/.lake/build/bin)
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
FX="$HERE/syntax/d5.trig"
QDIR="$HERE/graphs"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4sbm11-w3c" "$FX" "$QDIR"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-graphs.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <name> <ok:0|1> <detail>
  if [ "$2" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-44s %s\n' "$1" "$3"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-44s %s\n' "$1" "$3"; fi
}
xfail() { # xfail <name> <issue-url> <expected-failure-holds:0|1> <detail>
  if [ "$3" = 0 ]; then XFAIL=$((XFAIL + 1)); printf 'XFAIL  %-44s (%s) %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'XPASS  %-44s (%s) %s -- flip this case to a real assertion and close the issue\n' "$1" "$2" "$4"; fi
}
W3C() { "$BIN/l4sbm11-w3c" "$@"; }

# store <name>: pack d5.trig into $TMP/<name>/gen and activate it
store() {
  local d="$TMP/$1" rc=0
  timeout 120 "$BIN/l4sbm11-pack" "$FX" "$d/gen" --workers 1 >"$d.pack.log" 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { timeout 120 "$BIN/l4sbm11" activate "$d" gen >"$d.act.log" 2>&1 || rc=$?; }
  return $rc
}

# queries <state> <store root> <reference TriG>: every gate query, store against reference
queries() {
  local st="$1" root="$2" ref="$3" rq n rc rrc v p want
  for rq in "$QDIR"/*.rq; do
    n="$(basename "$rq" .rq)"
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$root" --file "$rq" --base "file://$(realpath "$rq")" \
      >"$TMP/$st-$n.got" 2>"$TMP/$st-$n.err" || rc=$?
    if [ "$rc" -ne 0 ]; then record "$st/$n" 1 "exit $rc: $(tail -1 "$TMP/$st-$n.err")"; continue; fi
    rrc=0
    timeout 120 "$BIN/l4sbm11-w3c" query-source "$ref" "$rq" --format trig --base - --mode rdf11 \
      >"$TMP/$st-$n.want" 2>"$TMP/$st-$n.werr" || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$TMP/$st-$n.got" "$TMP/$st-$n.want" "$rrc")"
    p="$(grep -o 'path=[a-z]*' "$TMP/$st-$n.err" | head -1)"
    want=path=ids; case $n in ref-*) want=path=reference ;; esac
    if [ "$p" != "$want" ]; then record "$st/$n" 1 "$p, expected $want"
    else case "$v" in equal*) record "$st/$n" 0 "$p; $v" ;; *) record "$st/$n" 1 "$p; $v" ;; esac
    fi
  done
}

# graphs <state> <generation> <want>: `l4sbm11 graphs` (IRIs sorted, then bnodes=N)
graphs() {
  local got
  got="$(timeout 60 "$BIN/l4sbm11" graphs "$2" 2>/dev/null | { grep '^<' || true; } | sort | tr '\n' ' ') bnodes=$(timeout 60 "$BIN/l4sbm11" graphs "$2" 2>/dev/null | grep -c '^_:')"
  if [ "$got" = "$3" ]; then record "$1/graphs" 0 "$got"; else record "$1/graphs" 1 "'$got', want '$3'"; fi
}

# exports <state> <generation> <reference TriG>: TriG and JSON-LD with the graphs with no
# triple kept; N-Quads with its notice; N-Triples refused
exports() {
  local st="$1" gen="$2" ref="$3" f rc out empties
  W3C query-source "$ref" "$QDIR/ref-graph-minus.rq" --format trig --base - --mode rdf11 >"$TMP/$st.empties.srj" 2>/dev/null
  empties="$(python3 -I -c 'import json, sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$TMP/$st.empties.srj" 2>/dev/null || echo unknown)"
  for f in trig jsonld; do
    rc=0
    timeout 120 "$BIN/l4sbm11" export "$gen" --format "$f" --out "$TMP/$st.$f" 2>"$TMP/$st.$f.err" || rc=$?
    if [ "$rc" -ne 0 ]; then record "$st/export-$f" 1 "exit $rc: $(tail -1 "$TMP/$st.$f.err")"; continue; fi
    out="$(W3C compare "$ref" "$TMP/$st.$f" --expected trig --actual "$f" --empty keep --mode rdf11 2>&1)"
    case "$out" in
      "pass empty-named-graphs=$empties"|"pass via-canonical empty-named-graphs=$empties")
        record "$st/export-$f" 0 "$out; $(grep -o 'graphs-with-no-triple=[0-9]*' "$TMP/$st.$f.err")" ;;
      *) record "$st/export-$f" 1 "$out (want $empties named graphs with no triple)" ;;
    esac
  done
  rc=0
  timeout 120 "$BIN/l4sbm11" export "$gen" --format nquads --out "$TMP/$st.nq" 2>"$TMP/$st.nq.err" || rc=$?
  out="$(W3C compare "$ref" "$TMP/$st.nq" --expected trig --mode rdf11 2>&1)"
  if [ "$empties" -eq 0 ]; then
    if [ "$rc" -eq 0 ] && ! grep -q 'no statement for a named graph' "$TMP/$st.nq.err" && [ "${out%% *}" = pass ]; then
      record "$st/export-nquads" 0 "no graph with no triple, no notice; $out"
    else record "$st/export-nquads" 1 "exit $rc; $out; $(grep 'no statement' "$TMP/$st.nq.err")"; fi
  elif [ "$rc" -eq 0 ] && grep -q "has no statement for a named graph with no triple; $empties such graphs" "$TMP/$st.nq.err" \
      && [ "${out%% *}" = pass ]; then
    record "$st/export-nquads" 0 "the quads ($out, graphs with no triple dropped on both sides); notice: $(grep -o "$empties such graphs[^;]*" "$TMP/$st.nq.err")"
  else record "$st/export-nquads" 1 "exit $rc; $out; stderr: $(tail -2 "$TMP/$st.nq.err" | tr '\n' ' ')"; fi
  rc=0
  timeout 120 "$BIN/l4sbm11" export "$gen" --format ntriples >"$TMP/$st.nt" 2>"$TMP/$st.nt.err" || rc=$?
  if [ "$rc" -ne 0 ] && [ ! -s "$TMP/$st.nt" ] && grep -q 'has named graphs' "$TMP/$st.nt.err"; then
    record "$st/export-ntriples-refused" 0 "exit $rc, no output: $(grep -o 'has named graphs[^,]*' "$TMP/$st.nt.err")"
  else record "$st/export-ntriples-refused" 1 "exit $rc, $(wc -c <"$TMP/$st.nt") bytes; $(tail -1 "$TMP/$st.nt.err")"; fi
}

# update <state> <store root> <request text> <want log version>: the store and the reference
update() {
  local st="$1" root="$2" req="$TMP/$1.ru" rc=0 out
  printf '%s\n' "$3" >"$req"
  timeout 120 "$BIN/l4sbm11" update "$root/gen" --file "$req" --base "file://$req" >"$TMP/$st.upd" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] || ! grep -q "log-version=$4" "$TMP/$st.upd"; then
    record "$st/update" 1 "exit $rc: $(grep -v ' op ' "$TMP/$st.upd" | tail -1)"; return 1
  fi
  out="$(W3C update-source "$FX" "$req" "$TMP/$st.ref.trig" --format trig --base - --mode rdf11 2>&1)"
  case "$out" in
    ok*) record "$st/update" 0 "store: $(grep -o 'log-version=[0-9]*' "$TMP/$st.upd"); reference: $out" ;;
    *) record "$st/update" 1 "reference: $out"; return 1 ;;
  esac
}

# compact <state> <store root>: fold the log into gen2 and activate it
compact() {
  local rc=0
  timeout 120 "$BIN/l4sbm11" compact "$2/gen" "$2/gen2" >"$TMP/$1.cmp" 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { timeout 60 "$BIN/l4sbm11" activate "$2" gen2 >>"$TMP/$1.cmp" 2>&1 || rc=$?; }
  if [ "$rc" -eq 0 ]; then record "$1/compact" 0 "compacted and activated"; else record "$1/compact" 1 "exit $rc: $(tail -1 "$TMP/$1.cmp")"; fi
  return $rc
}

EX='PREFIX ex: <http://example.org/>'
echo "=== base: the pack of d5.trig"
if store base; then
  record base/pack 0 "$(grep -o 'quads=[0-9]*' "$TMP/base.pack.log" | head -1)"
  graphs base "$TMP/base/gen" "<http://example.org/g0> <http://example.org/g1> <http://example.org/g2>  bnodes=3"
  queries base "$TMP/base" "$FX"
  exports base "$TMP/base/gen" "$FX"
else record base/pack 1 "$(tail -1 "$TMP/base.pack.log" "$TMP/base.act.log" 2>/dev/null | tr '\n' ' ')"; fi

echo "=== round trips: the Dataset route and the JSON-LD document of D5, exported as TriG"
# `l4sbm11-pack --via-dataset` reads the whole document into an RDF Dataset and packs it
# through `QuadSource.ofDataset`, which declares every named graph; d5.jsonld is the same
# dataset in JSON-LD (empty `@graph` arrays). Each export equals d5.trig with the graphs
# with no triple compared.
for v in via-dataset jsonld; do
  rc=0
  case $v in
    via-dataset) timeout 120 "$BIN/l4sbm11-pack" "$FX" "$TMP/rt-$v" --workers 1 --via-dataset >"$TMP/rt-$v.log" 2>&1 || rc=$? ;;
    jsonld) timeout 120 "$BIN/l4sbm11-pack" "$HERE/syntax/d5.jsonld" "$TMP/rt-$v" --workers 1 >"$TMP/rt-$v.log" 2>&1 || rc=$? ;;
  esac
  [ "$rc" -eq 0 ] && { timeout 120 "$BIN/l4sbm11" export "$TMP/rt-$v" --format trig --out "$TMP/rt-$v.trig" 2>"$TMP/rt-$v.err" || rc=$?; }
  if [ "$rc" -ne 0 ]; then record "round-trip/$v" 1 "exit $rc: $(tail -1 "$TMP/rt-$v.log" "$TMP/rt-$v.err" 2>/dev/null | tr '\n' ' ')"; continue; fi
  out="$(W3C compare "$FX" "$TMP/rt-$v.trig" --expected trig --actual trig --empty keep --mode rdf11 2>&1)"
  case "$out" in pass*) record "round-trip/$v" 0 "$out" ;; *) record "round-trip/$v" 1 "$out" ;; esac
done

echo "=== r1: DROP, CREATE, CLEAR and an INSERT into a new graph, in the log"
if store r1 && update r1 "$TMP/r1" "$EX DROP GRAPH ex:g0 ; CREATE GRAPH ex:g9 ; CLEAR GRAPH ex:g1 ; INSERT DATA { GRAPH ex:g7 { ex:n ex:p ex:m } }" 1; then
  queries r1 "$TMP/r1" "$TMP/r1.ref.trig"
  if compact r1 "$TMP/r1"; then
    graphs r1-gen2 "$TMP/r1/gen2" "<http://example.org/g1> <http://example.org/g2> <http://example.org/g7> <http://example.org/g9>  bnodes=3"
    queries r1-gen2 "$TMP/r1" "$TMP/r1.ref.trig"
    exports r1-gen2 "$TMP/r1/gen2" "$TMP/r1.ref.trig"
  fi
fi

echo "=== r2: CLEAR NAMED, which names the graphs named by a blank node, in the log"
if store r2 && update r2 "$TMP/r2" "CLEAR NAMED" 3; then
  queries r2 "$TMP/r2" "$TMP/r2.ref.trig"
  if compact r2 "$TMP/r2"; then
    graphs r2-gen2 "$TMP/r2/gen2" "<http://example.org/g0> <http://example.org/g1> <http://example.org/g2>  bnodes=3"
    queries r2-gen2 "$TMP/r2" "$TMP/r2.ref.trig"
    exports r2-gen2 "$TMP/r2/gen2" "$TMP/r2.ref.trig"
  fi
fi

echo "=== shortfall: the in-memory query ops"
# `l4factoidal query` gives its dataset to the query ops through the canonical N-Quads round
# trip (`withOpsDataset`), which cannot state a graph with no triple, and the ops evaluate
# on the indexed backend, which leaves out a graph named by a blank node: https://github.com/danbri/factoidal/issues/876
rows=-
if [ -x "$BIN/l4factoidal" ]; then
  timeout 120 "$BIN/l4factoidal" query "$FX" --format trig --query "$QDIR/ref-graph-names.rq" >"$TMP/l4f.srj" 2>"$TMP/l4f.err"
  rows="$(python3 -I -c 'import json, sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$TMP/l4f.srj" 2>/dev/null || echo error)"
fi
if [ "$rows" = 6 ]; then xfail xfail-l4factoidal-graph-names https://github.com/danbri/factoidal/issues/876 1 "l4factoidal query gives the 6 named graphs of d5.trig"
else xfail xfail-l4factoidal-graph-names https://github.com/danbri/factoidal/issues/876 0 "GRAPH ?g { } on d5.trig: l4factoidal query gives $rows rows, the reference evaluator 6"; fi

echo "=== refusal: the IBK4 and IBK5 stores"
# The IBK stores have no graph list and their log (DLOG version 1) has no graph slot. Owner
# decision of 2026-10-22 (https://github.com/danbri/factoidal/issues/880): they refuse a source
# that declares a named graph with no triple, and CREATE GRAPH and CLEAR of a named graph,
# with a message that names the rule. SBM11 stores such a graph.
# A missing binary is a failure.
ibk_rows() { # ibk_rows <collection root>: the rows of GRAPH ?g { }, "error" on a failure
  timeout 120 "$BIN/l4block-quad-query" "$1" --json --query "$(cat "$QDIR/ref-graph-names.rq")" 2>"$1.q.err" \
    | tail -1 >"$1.srj"
  python3 -I -c 'import json, sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$1.srj" 2>/dev/null \
    || echo error
}
RULE="IBK4 and IBK5 store no named graph without a triple (https://github.com/danbri/factoidal/issues/880)"
ibk_ok=0
for need in l4block-shard-pack l4block-shard-activate l4block-quad-query l4block-delta-log; do
  [ -x "$BIN/$need" ] || { record ibk-binaries 1 "missing: $BIN/$need"; ibk_ok=1; }
done
if [ "$ibk_ok" = 0 ]; then
  for fmt in ibk4 ibk5; do
    c="$TMP/$fmt-refused"; mkdir -p "$c"
    rc=0; timeout 120 "$BIN/l4block-shard-pack" "$FX" "$c/gen-1" "$fmt" >"$c.pack.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ] && grep -qF "refused: $RULE" "$c.pack.log" && [ ! -e "$c/gen-1/manifest.sbm2" ]; then
      record "$fmt-pack-refuses-empty-graph" 0 "d5.trig: exit $rc, message names the rule, no manifest written"
    else record "$fmt-pack-refuses-empty-graph" 1 "exit $rc: $(tail -1 "$c.pack.log" | cut -c1-200)"; fi
  done
  # a TriG whose named graphs all hold a triple still packs and answers
  printf '%s\n' '@prefix ex: <http://example.org/> .' 'ex:s ex:p ex:o .' \
    'ex:g1 { ex:a ex:p ex:b . }' 'ex:g2 { ex:c ex:p ex:d . }' >"$TMP/full.trig"
  for fmt in ibk4 ibk5; do
    c="$TMP/$fmt"; mkdir -p "$c"
    if timeout 120 "$BIN/l4block-shard-pack" "$TMP/full.trig" "$c/gen-1" "$fmt" >"$c.pack.log" 2>&1 \
        && timeout 120 "$BIN/l4block-shard-activate" "$c" gen-1 >"$c.act.log" 2>&1; then
      rows="$(ibk_rows "$c")"
      if [ "$rows" = 2 ]; then record "$fmt-pack-nonempty-graphs" 0 "2 named graphs, each with a triple, packed and answered"
      else record "$fmt-pack-nonempty-graphs" 1 "GRAPH ?g { } gives $rows rows, expected 2"; fi
    else record "$fmt-pack-nonempty-graphs" 1 "pack or activation failed: $(tail -1 "$c.pack.log" "$c.act.log" 2>/dev/null | tr '\n' ' ' | cut -c1-160)"; fi
  done
  # Every update on an IBK4 or IBK5 collection is refused: l4block-quad-query does not replay the
  # delta log, so a committed update would be invisible (https://github.com/danbri/factoidal/issues/935).
  # This covers CREATE GRAPH, CLEAR GRAPH, INSERT DATA and the DELETE DATA of the last triple of a
  # named graph (https://github.com/danbri/factoidal/issues/934). Refused: exit non-zero, a message
  # that names the rule, and no file of the collection changed.
  snapshot() { find "$1" -type f -exec cksum {} + 2>/dev/null | sort; }
  ISSUE935="https://github.com/danbri/factoidal/issues/935"
  printf '%s\n' '@prefix ex: <http://example.org/> .' 'ex:s ex:p ex:o .' 'ex:g1 { ex:a ex:p ex:b . }' >"$TMP/one.trig"
  for fmt in ibk4 ibk5; do
    c="$TMP/$fmt-upd"; mkdir -p "$c"
    if timeout 120 "$BIN/l4block-shard-pack" "$TMP/one.trig" "$c/gen-1" "$fmt" >"$c.pack.log" 2>&1 \
        && timeout 120 "$BIN/l4block-shard-activate" "$c" gen-1 >"$c.act.log" 2>&1; then
      before="$(snapshot "$c")"
      for upd in 'CREATE GRAPH <http://example.org/g9>' 'CLEAR GRAPH <http://example.org/g1>' \
          'INSERT DATA { GRAPH <http://example.org/g1> { <http://example.org/z> <http://example.org/p> <http://example.org/y> } }' \
          'DELETE DATA { GRAPH <http://example.org/g1> { <http://example.org/a> <http://example.org/p> <http://example.org/b> } }'; do
        rc=0; timeout 120 "$BIN/l4block-delta-log" "$c" --update "$upd" >"$c.upd.log" 2>&1 || rc=$?
        if [ "$rc" -ne 0 ] && grep -qF "$ISSUE935" "$c.upd.log" && [ "$before" = "$(snapshot "$c")" ]; then
          record "$fmt-update-refused: ${upd:0:30}" 0 "exit $rc, message names the rule, no file changed"
        else record "$fmt-update-refused: ${upd:0:30}" 1 "exit $rc: $(tail -n 1 "$c.upd.log" | cut -c1-160)"; fi
      done
    else record "$fmt-update-setup" 1 "pack or activation failed: $(tail -n 1 "$c.pack.log" | cut -c1-160)"; fi
  done
  # IBK3 keeps taking updates, and its query path replays them
  if [ -x "$BIN/l4block-id-v3-query" ]; then
    c="$TMP/ibk3-upd"; mkdir -p "$c"
    printf '%s\n' '@prefix ex: <http://example.org/> .' 'ex:s ex:p ex:o .' >"$TMP/one.ttl"
    rc=0
    timeout 120 "$BIN/l4block-shard-pack" "$TMP/one.ttl" "$c/gen-1" ibk3 >"$c.pack.log" 2>&1 \
      && timeout 120 "$BIN/l4block-shard-activate" "$c" gen-1 >"$c.act.log" 2>&1 \
      && timeout 120 "$BIN/l4block-delta-log" "$c" --update 'INSERT DATA { <http://example.org/new> <http://example.org/p> <http://example.org/o2> }' >"$c.upd.log" 2>&1 || rc=$?
    seen="$(timeout 120 "$BIN/l4block-id-v3-query" "$c" --json --query 'SELECT ?s WHERE { ?s ?p ?o }' 2>/dev/null | tail -n 1 | grep -c 'http://example.org/new')"
    if [ "$rc" -eq 0 ] && [ "$seen" -ge 1 ]; then record ibk3-update-commits-and-is-visible 0 "committed, exit 0; the query returns ex:new"
    else record ibk3-update-commits-and-is-visible 1 "exit $rc, rows with ex:new: $seen: $(tail -n 1 "$c.upd.log" | cut -c1-160)"; fi
  else record ibk3-update 1 "missing: $BIN/l4block-id-v3-query"; fi
fi

echo "named graphs: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
