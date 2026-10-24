#!/usr/bin/env bash
#
# tests/sbm11/frommerge/check.sh — FROM with two or more graphs is an RDF
# merge (https://github.com/danbri/factoidal/issues/979).
#
# SPARQL 1.1 Query section 13.2.1: "If a query provides more than one FROM
# clause, providing more than one IRI to indicate the default graph, then the
# default graph is the RDF merge of the graphs obtained from representations
# of the resources identified by the given IRIs." RDF 1.1 Semantics section
# 5.2: the merge renames the graphs' blank nodes apart. data.nq has `_:b0` in
# the named graphs g1 and g2 (one blank node of the store) and `_:b1` twice in
# g3.
#
# Until 2026-10-24 the reference evaluator built the default graph with
# `Graph.union` and the id path with the union over ids: ref-fm-join-across
# gave 1 row and ref-fm-count gave 1.
#
# Part (d) of tests/sbm11/run.sh runs this script.
#
# Checks (query: path, rows, value of ?n):
#   ref-fm-join-across  reference (the id path refuses a merged row with a
#                       blank node), 0 rows
#   ref-fm-count        reference, ?n = 2
#   ids-fm-join-one     ids, 1 row (control: one FROM graph)
#   ids-fm-ground       ids, 2 rows (a merge with no blank node in its rows)
#   ids-fm-named-one    ids, 1 row (one FROM graph keeps the store's nodes)
# The reference evaluator (`l4factoidal query`) gives the same answer. Exit 0
# only when the checks pass.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-fm.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
rc=0
"$BIN/l4sbm11-pack" "$HERE/data.nq" "$TMP/st/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$TMP/st" gen >"$TMP/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then echo "FAIL pack-activate exit $rc"; exit 1; fi
# answer <file>: the number of rows, or the value of ?n when the head has it
answer() {
  python3 -I -c '
import json,sys
d=json.load(open(sys.argv[1])); b=d["results"]["bindings"]
print(b[0]["n"]["value"] if d["head"]["vars"]==["n"] and len(b)==1 else len(b))' "$1"
}
fail=0
for q in ref-fm-join-across:reference:0 ref-fm-count:reference:2 ids-fm-join-one:ids:1 \
         ids-fm-ground:ids:2 ids-fm-named-one:ids:1; do
  n="${q%%:*}"; rest="${q#*:}"; want_path="path=${rest%%:*}"; want="${rest##*:}"
  qrc=0
  timeout 120 "$BIN/l4sbm11" query "$TMP/st" --file "$HERE/$n.rq" >"$TMP/$n.got" 2>"$TMP/$n.err" || qrc=$?
  rrc=0
  timeout 120 "$BIN/l4factoidal" query "$HERE/data.nq" --format nquads --query "$HERE/$n.rq" >"$TMP/$n.ref" 2>/dev/null || rrc=$?
  p="$(grep -o 'path=[a-z]*' "$TMP/$n.err" | head -1)"
  got="$( [ "$qrc" -eq 0 ] && answer "$TMP/$n.got" || echo "exit $qrc")"
  ref="$( [ "$rrc" -eq 0 ] && answer "$TMP/$n.ref" || echo "exit $rrc")"
  if [ "$p" = "$want_path" ] && [ "$got" = "$want" ] && [ "$ref" = "$want" ]; then
    echo "ok   $n: $p, answer $got, reference $ref"
  else
    echo "FAIL $n: $p, answer $got, reference $ref; expected $want_path and $want on both"; fail=1
  fi
done
exit "$fail"
