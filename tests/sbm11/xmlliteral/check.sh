#!/usr/bin/env bash
#
# tests/sbm11/xmlliteral/check.sh — two rdf:XMLLiteral literals with
# different lexical forms and the same canonical XML ("<x></x>" and "<x/>";
# https://github.com/danbri/factoidal/issues/776).
#
# RDF 1.1 Concepts section 3.3: two literals are the same term only when
# their lexical forms are the same character by character. SPARQL 1.1
# sections 18.3 and 18.4 join and match by RDF term equality. Both paths
# follow that: the id path gives the two literals two ids, and the reference
# evaluator compares them with `Term.eqb`, which compares lexical forms.
# Until 2026-10-23 `Term.eqb` compared rdf:XMLLiteral literals by canonical
# XML and the reference gave 4 and 2 rows
# (https://github.com/danbri/factoidal/issues/963).
#
# `ids-ne` (FILTER(?o != ?q) over the two literals): SPARQL 1.1 section
# 17.4.1.7, RDFterm-equal: two literals that are not the same term, of a
# datatype with no value comparison (rdf:XMLLiteral), are a type error under
# `=` and `!=`, so the FILTER removes every row (0 rows; a pair of the same
# term gives `false`). Until 2026-10-23 the reference evaluator compared the
# lexical forms and kept 2 rows.
#
# Part (d) of tests/sbm11/run.sh runs this script.
#
# Checks: each query runs on the id path and gives the RDF 1.1 answer
# (ids-join 2 rows, ids-const 1 row, ids-ne 0 rows), and the reference evaluator gives the
# same number of rows. Exit 0 only when the checks pass.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-xml.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
rc=0
"$BIN/l4sbm11-pack" "$HERE/data.nq" "$TMP/st/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$TMP/st" gen >"$TMP/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then echo "FAIL pack-activate exit $rc"; exit 1; fi
rows() { python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$1"; }
fail=0
for q in ids-join:2 ids-const:1 ids-ne:0; do
  n="${q%%:*}"; want="${q##*:}"
  qrc=0
  timeout 120 "$BIN/l4sbm11" query "$TMP/st" --file "$HERE/$n.rq" >"$TMP/$n.got" 2>"$TMP/$n.err" || qrc=$?
  rrc=0
  timeout 120 "$BIN/l4factoidal" query "$HERE/data.nq" --format nquads --query "$HERE/$n.rq" >"$TMP/$n.ref" 2>/dev/null || rrc=$?
  p="$(grep -o 'path=[a-z]*' "$TMP/$n.err" | head -1)"
  got="$( [ "$qrc" -eq 0 ] && rows "$TMP/$n.got" || echo "exit $qrc")"
  ref="$( [ "$rrc" -eq 0 ] && rows "$TMP/$n.ref" || echo "exit $rrc")"
  if [ "$p" = path=ids ] && [ "$got" = "$want" ] && [ "$ref" = "$want" ]; then
    echo "ok   $n: $p, $got rows, reference $ref rows (RDF 1.1 term equality)"
  else
    echo "FAIL $n: $p, $got rows, reference $ref rows; expected path=ids and $want rows on both"; fail=1
  fi
done
exit "$fail"
