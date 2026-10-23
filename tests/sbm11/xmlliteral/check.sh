#!/usr/bin/env bash
#
# tests/sbm11/xmlliteral/check.sh — two rdf:XMLLiteral literals with
# different lexical forms and the same canonical XML ("<x></x>" and "<x/>";
# https://github.com/danbri/factoidal/issues/776).
#
# RDF 1.1 Concepts section 3.3: two literals are the same term only when
# their lexical forms are the same character by character. The id path gives
# the two literals two ids and follows that rule. The reference evaluator
# compares two rdf:XMLLiteral literals with `Term.eqb`, which compares their
# canonical XML (`XmlCanon.xmlCanonEq`), so it joins them.
#
# This dataset makes the dictionary hypotheses `hdec` and `hcid` of
# `HarnessWhereTheorems.harness_where_allowed` false;
# `MemGenDictTheorems` proves them only for a dictionary with no
# rdf:XMLLiteral literal (`MemGen.keysOk`). Not in the gate parts of
# tests/sbm11/run.sh, because there the id path must equal the reference.
#
# Checks: each query runs on the id path and gives the RDF 1.1 answer
# (ids-join 2 rows, ids-const 1 row). The reference row counts are printed
# (4 and 2 on 2026-10-23). Exit 0 only when the checks pass.
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
for q in ids-join:2 ids-const:1; do
  n="${q%%:*}"; want="${q##*:}"
  qrc=0
  timeout 120 "$BIN/l4sbm11" query "$TMP/st" --file "$HERE/$n.rq" >"$TMP/$n.got" 2>"$TMP/$n.err" || qrc=$?
  rrc=0
  timeout 120 "$BIN/l4factoidal" query "$HERE/data.nq" --format nquads --query "$HERE/$n.rq" >"$TMP/$n.ref" 2>/dev/null || rrc=$?
  p="$(grep -o 'path=[a-z]*' "$TMP/$n.err" | head -1)"
  got="$( [ "$qrc" -eq 0 ] && rows "$TMP/$n.got" || echo "exit $qrc")"
  ref="$( [ "$rrc" -eq 0 ] && rows "$TMP/$n.ref" || echo "exit $rrc")"
  if [ "$p" = path=ids ] && [ "$got" = "$want" ]; then
    echo "ok   $n: $p, $got rows (RDF 1.1 term equality); reference $ref rows"
  else
    echo "FAIL $n: $p, $got rows, expected path=ids and $want rows; reference $ref rows"; fail=1
  fi
done
exit "$fail"
