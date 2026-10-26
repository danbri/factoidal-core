#!/usr/bin/env python3
"""Per-query cost of SPARQL over an open dataset handle, Lean engine, native.

`l4wasm-cli callseq` runs [datasetOpen(TTL)] followed by K x datasetQuery(h1, Q)
in ONE process (the npm handle path: the backend runner first, the reference
evaluator for a text:query query, then SPARQL JSON results). Per-query cost =
(CPU(K) - CPU(0)) / K, CPU = user+sys of the child (getrusage), median of R
runs of each. Prints rows from the first answer.

Usage (from the repository root, after `lake build l4wasm-cli` in formal/lean4):
  python3 tests/parity/geo-fulltext/cost/gen-literals.py 10000 > /tmp/ft10k.ttl
  python3 -I tests/parity/geo-fulltext/cost/measure-text-query.py \
      formal/lean4/.lake/build/bin/l4wasm-cli /tmp/ft10k.ttl 200 5

Record: docs/designissues/2026-10-10-lean-geo-distance-fulltext.md, section 4.
"""
import json, os, resource, shutil, statistics, subprocess, sys, tempfile

cli, data, K, R = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
ttl = open(data).read()
PRE = ('PREFIX text: <http://jena.apache.org/text#> '
       'PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> ')
QUERIES = [
    ("?s rdfs:label ?o (no text search)", 'SELECT ?s WHERE { ?s rdfs:label ?o }'),
    ('text:query "panel"', 'SELECT ?s WHERE { ?s text:query "panel" }'),
    ('text:query "panel solar"', 'SELECT ?s WHERE { ?s text:query "panel solar" }'),
    ('text:query (rdfs:label "panel")', 'SELECT ?s WHERE { ?s text:query (rdfs:label "panel") }'),
    ('text:query (rdfs:label "panel" 10)', 'SELECT ?s WHERE { ?s text:query (rdfs:label "panel" 10) }'),
    ('text:query "zzzz" (no match)', 'SELECT ?s WHERE { ?s text:query "zzzz" }'),
    ('FILTER(CONTAINS(LCASE(?o), "panel"))',
     'SELECT ?s WHERE { ?s rdfs:label ?o FILTER(CONTAINS(LCASE(?o), "panel")) }'),
]
tmp = tempfile.mkdtemp(prefix="geo-ft-seq-")

def run(seq):
    path = os.path.join(tmp, "seq.json")
    json.dump(seq, open(path, "w"))
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run([cli, "callseq", path], capture_output=True, text=True, timeout=600)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    assert p.returncode == 0, p.stderr[:300]
    return (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime), p.stdout

open_only = [["datasetOpen", [ttl, "turtle", ""]]]
t0 = statistics.median(run(open_only)[0] for _ in range(R))
print(f"fixture={os.path.basename(data)} K={K} R={R}; open (parse + index) = {t0*1000:.1f} ms CPU")
for label, body in QUERIES:
    q = PRE + body
    seq = open_only + [["datasetQuery", ["h1", q]]] * K
    times, out = [], None
    for _ in range(R):
        t, o = run(seq)
        times.append(t); out = out or o
    lines = [json.loads(l) for l in out.splitlines() if l.strip()]
    assert all(r.get("ok") for r in lines), lines[1]
    rows = len(lines[1]["srj"]["results"]["bindings"])
    per = (statistics.median(times) - t0) / K
    print(f"{label:38s} rows={rows:5d}  per query = {per*1000:6.2f} ms CPU")
shutil.rmtree(tmp)
