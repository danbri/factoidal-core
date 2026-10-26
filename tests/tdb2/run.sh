#!/usr/bin/env bash
# Jena TDB2 read compatibility (https://github.com/danbri/factoidal/issues/834).
#
# Builds two TDB2 databases with Apache Jena's own bulk loader
# (tdb2.tdbloader), dumps each with Jena (tdb2.tdbdump), and requires the
# Lean decoder (`l4factoidal tdb2-dump`) and the Python format probe
# (tools/tdb2/probe_tdb2.py) to print the same N-Quads lines (compared as
# sorted line sets; blank node labels are Jena's stored labels, so no
# relabelling is needed). Then one SPARQL query over each database is answered
# by `l4factoidal query DIR --format tdb2` and by tdb2.tdbquery, and the
# counts must agree.
#
#   w3c: the data files of the W3C SPARQL 1.1 `functions` suite, two
#        `aggregates` data files and two RDF 1.1 TriG test files (integers,
#        decimals, doubles, dateTimes, language tags, named graphs).
#   big: examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl
#        (6,455 triples).
#
# Environment: SOTA_DL (Jena 6.2.0 install, as tools/sota-bench.py --install),
# TDB2_WORK (scratch, default a new temp dir, deleted), BIN, W3C_ROOT
# (default third_party/testing/w3c). Exit 0 all equal, 1 a difference, 2 setup.
set -uo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
bin=${BIN:-$root/formal/lean4/.lake/build/bin}
jena=${SOTA_DL:-/tmp/sota-dl-$(basename "$root")}/apache-jena-6.2.0/bin
w3c=${W3C_ROOT:-$root/third_party/testing/w3c}
[ -x "$jena/tdb2.tdbloader" ] || { echo "tdb2/run.sh: no Jena at $jena" >&2; exit 2; }
[ -d "$w3c/sparql/sparql11/functions" ] || { echo "tdb2/run.sh: no W3C fixtures at $w3c" >&2; exit 2; }
work=${TDB2_WORK:-$(mktemp -d)}
mkdir -p "$work"
fail=0

load() { # name files...
  local name=$1; shift
  rm -rf "${work:?}/$name"
  "$jena/tdb2.tdbloader" --loc "$work/$name" "$@" >"$work/$name.load.log" 2>&1 || { echo "tdbloader failed: $name"; exit 2; }
  "$jena/tdb2.tdbdump" --loc "$work/$name" 2>/dev/null | sort >"$work/$name.jena.nq"
}

check() { # name query
  local name=$1 q=$2 rc
  rc=0; timeout 600 "$bin/l4factoidal" tdb2-dump "$work/$name" | sort >"$work/$name.lean.nq" || rc=$?
  if [ "$rc" -ne 0 ] || ! cmp -s "$work/$name.jena.nq" "$work/$name.lean.nq"; then
    echo "FAIL $name: Lean dump differs from tdb2.tdbdump (rc $rc)"; diff "$work/$name.jena.nq" "$work/$name.lean.nq" | head -5; fail=1
  else
    echo "ok   $name: Lean dump = tdb2.tdbdump ($(wc -l <"$work/$name.jena.nq") quads)"
  fi
  rc=0; python3 "$root/tools/tdb2/probe_tdb2.py" dump "$work/$name" | sort >"$work/$name.probe.nq" || rc=$?
  if [ "$rc" -ne 0 ] || ! cmp -s "$work/$name.jena.nq" "$work/$name.probe.nq"; then
    echo "FAIL $name: probe dump differs from tdb2.tdbdump"; fail=1
  else
    echo "ok   $name: probe dump = tdb2.tdbdump"
  fi
  local nl nj
  nl=$("$bin/l4factoidal" query "$work/$name" --format tdb2 --query-string "$q" \
    | python3 -c 'import json,sys; print(json.load(sys.stdin)["results"]["bindings"][0]["n"]["value"])')
  nj=$("$jena/tdb2.tdbquery" --loc "$work/$name" --results=json "$q" 2>/dev/null \
    | python3 -c 'import json,sys; print(json.load(sys.stdin)["results"]["bindings"][0]["n"]["value"])')
  if [ "$nl" = "$nj" ] && [ -n "$nl" ]; then echo "ok   $name: query count $nl = Jena"
  else echo "FAIL $name: query count Lean '$nl', Jena '$nj'"; fail=1; fi
}

f=$w3c/sparql/sparql11
load w3c "$f"/functions/data*.ttl "$f"/aggregates/agg-numeric*.ttl "$f"/aggregates/agg-groupconcat-*.ttl \
  "$w3c"/rdf/rdf11/rdf-trig/trig-subm-26.trig "$w3c"/rdf/rdf11/rdf-trig/trig-kw-graph-*.trig
check w3c 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o FILTER(isLiteral(?o)) }'
load big "$root/examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl"
check big 'SELECT (COUNT(DISTINCT ?s) AS ?n) WHERE { ?s ?p ?o }'

[ -z "${TDB2_WORK:-}" ] && rm -rf "$work"
exit $fail
