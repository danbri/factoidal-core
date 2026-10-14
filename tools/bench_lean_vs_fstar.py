#!/usr/bin/env python3
"""Lean engine vs F* engine: same input, same machine, ratio and growth.

Written 2026-10-10 for docs/designissues/2026-10-10-lean-vs-fstar-performance.md.

What it does
------------
For each row (a workload family) it generates inputs of size n, 2n, 4n, 8n,
runs the Lean command line and the F* command line on the same file, and
records for each (row, engine, n):

  * the minimum wall time of up to `--runs` runs (default 3; a case whose
    first run exceeds `--single-over` seconds is run once and the row says so),
  * the CPU time (user + system) and peak resident set size of the minimum run,
  * the 1-minute load average before the first run of the case,
  * a short fingerprint of standard output (first line, line count), so that
    a reader can see that both engines answered the same question.

A run that exceeds `--cap` seconds is killed and recorded as a cap trip; it is
a result, not an error (anti-pattern 17). Everything is written to
`--out` (JSON lines) as it is measured, so a container restart loses at most
one case. `--report` turns a JSON-lines file into the markdown table.

The machine has 4 CPUs shared with other agents. The load average is recorded
beside every number and the RATIO between the engines is the result, not the
absolute time. Wall time is used for the ratio and for growth; CPU time is
kept in the file for audit.

Usage
-----
  tools/bench_lean_vs_fstar.py --list
  tools/bench_lean_vs_fstar.py --rows parse-nt,parse-ttl --out /tmp/x.jsonl
  tools/bench_lean_vs_fstar.py --report /tmp/x.jsonl > table.md

Binaries (built in the working tree, not committed):
  Lean: formal/lean4/.lake/build/bin/{l4factoidal,l4shacl,l4jsonld-api}
  F*:   bin/linux-x86_64/factoidal
"""

from __future__ import annotations

import argparse
import json
import math
import os
import shutil
import sys
import threading
import time
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

# BENCH_LEAN_BIN_DIR points at a directory holding copies of the Lean binaries
# (l4factoidal, l4shacl, l4jsonld-api). A survey that spans a rebuild of the
# library must use a frozen copy, or the later rows measure a different binary.
LEAN_BIN = Path(os.environ.get("BENCH_LEAN_BIN_DIR",
                               str(ROOT / "formal/lean4/.lake/build/bin")))
LEAN = LEAN_BIN / "l4factoidal"
LEAN_SHACL = LEAN_BIN / "l4shacl"
LEAN_JSONLD = LEAN_BIN / "l4jsonld-api"
FSTAR = ROOT / "bin/linux-x86_64/factoidal"

FIX = Path(os.environ.get("BENCH_FIXTURE_DIR",
                          "/tmp/factoidal-bench-lean-vs-fstar"))

EX = "http://example.org/"
GENE = ROOT / "examples/wikidata/subsets/lifesci-kgx/data/gene.ttl"


# --------------------------------------------------------------------------
# measurement
# --------------------------------------------------------------------------
def run_once(cmd, cap, cwd=None):
    """Run cmd; return dict(status, wall, cpu, user, rss_kb, out_lines, out_bytes,
    first_line, stderr, stderr_full). `cpu` is user plus system time, `user` is user
    time only; `stderr` is the last 300 characters, `stderr_full` the first 512 KiB.
    stdout is drained by a thread and not stored."""
    cnt = {"lines": 0, "bytes": 0, "first": b""}
    err_chunks = []
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True, cwd=cwd)

    def drain_out():
        while True:
            chunk = proc.stdout.read(1 << 20)
            if not chunk:
                break
            if not cnt["first"]:
                cnt["first"] = chunk[:300].split(b"\n")[0]
            cnt["lines"] += chunk.count(b"\n")
            cnt["bytes"] += len(chunk)
        proc.stdout.close()

    def drain_err():
        while True:
            chunk = proc.stderr.read(1 << 16)
            if not chunk:
                break
            if len(err_chunks) < 8:
                err_chunks.append(chunk)
        proc.stderr.close()

    to = threading.Thread(target=drain_out, daemon=True)
    te = threading.Thread(target=drain_err, daemon=True)
    to.start()
    te.start()
    hit = {"v": False}

    def kill():
        hit["v"] = True
        try:
            os.killpg(os.getpgid(proc.pid), 9)
        except (ProcessLookupError, PermissionError):
            pass

    timer = threading.Timer(cap, kill)
    timer.start()
    t0 = time.perf_counter()
    _pid, status, ru = os.wait4(proc.pid, 0)
    wall = time.perf_counter() - t0
    timer.cancel()
    proc.returncode = 0
    to.join(timeout=10)
    te.join(timeout=10)
    rc = os.waitstatus_to_exitcode(status)
    st = "cap" if hit["v"] else ("ok" if rc == 0 else f"rc{rc}")
    return {
        "status": st, "wall": wall, "cpu": ru.ru_utime + ru.ru_stime,
        "user": ru.ru_utime, "rss_kb": ru.ru_maxrss, "out_lines": cnt["lines"],
        "out_bytes": cnt["bytes"],
        "first_line": cnt["first"].decode("utf-8", "replace"),
        "stderr": b"".join(err_chunks).decode("utf-8", "replace")[-300:],
        # the first 512 KiB of stderr, for a caller that reads a long summary line
        "stderr_full": b"".join(err_chunks).decode("utf-8", "replace"),
    }


def measure(cmd, runs, cap, single_over, cwd=None):
    load0 = os.getloadavg()[0]
    results = []
    for i in range(runs):
        r = run_once(cmd, cap, cwd)
        results.append(r)
        if r["status"] != "ok":
            break
        if i == 0 and r["wall"] > single_over:
            break
    ok = [r for r in results if r["status"] == "ok"]
    if not ok:
        bad = results[-1]
        return {"status": bad["status"], "wall": bad["wall"], "cpu": bad["cpu"],
                "rss_kb": bad["rss_kb"], "runs": len(results), "load1": load0,
                "first_line": bad["first_line"], "out_lines": bad["out_lines"],
                "out_bytes": bad["out_bytes"], "stderr": bad["stderr"]}
    best = min(ok, key=lambda r: r["wall"])
    return {"status": "ok", "wall": best["wall"], "cpu": best["cpu"],
            "rss_kb": max(r["rss_kb"] for r in ok), "runs": len(ok),
            "load1": load0, "first_line": best["first_line"],
            "out_lines": best["out_lines"], "out_bytes": best["out_bytes"],
            "wall_all": [round(r["wall"], 4) for r in ok]}


# --------------------------------------------------------------------------
# fixtures
# --------------------------------------------------------------------------
def fx(name):
    FIX.mkdir(parents=True, exist_ok=True)
    return FIX / name


def write_once(path: Path, producer):
    if path.exists() and path.stat().st_size > 0:
        return path
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        producer(f)
    tmp.rename(path)
    return path


def gen_nt(n):
    def p(f):
        for i in range(n):
            f.write(f"<{EX}s{i}> <{EX}p> <{EX}o{i}> .\n")
    return write_once(fx(f"nt-{n}.nt"), p)


def gen_mixed_nt(n, quads=False):
    """IRIs, plain, language-tagged, typed literals and blank nodes."""
    def p(f):
        for i in range(n):
            g = f" <{EX}g{i % 8}>" if quads else ""
            k = i % 5
            if k == 0:
                o = f"<{EX}o{i}>"
            elif k == 1:
                o = f'"value {i} with \\"escape\\""'
            elif k == 2:
                o = f'"valeur {i}"@fr'
            elif k == 3:
                o = f'"{i}"^^<http://www.w3.org/2001/XMLSchema#integer>'
            else:
                o = f"_:b{i % 997}"
            f.write(f"<{EX}s{i // 3}> <{EX}p{i % 7}> {o}{g} .\n")
    return write_once(fx(f"mixed-{'nq' if quads else 'nt'}-{n}.{'nq' if quads else 'nt'}"), p)


def gen_ttl(n):
    def p(f):
        f.write(f"@prefix ex: <{EX}> .\n")
        for i in range(n):
            f.write(f"ex:s{i} ex:p ex:o{i} .\n")
    return write_once(fx(f"ttl-{n}.ttl"), p)


def gen_ttl_rich(n):
    """About n triples: subjects with predicate lists, object lists, lists of
    literals, nested blank node property lists."""
    subjects = max(1, n // 7)

    def p(f):
        f.write(f"@prefix ex: <{EX}> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n")
        for i in range(subjects):
            f.write(f'ex:s{i} a ex:Thing ; ex:name "Name {i}"@en ; '
                    f'ex:age {i % 90} ; ex:score "{i % 100}.5"^^xsd:decimal ;\n'
                    f'  ex:knows ex:s{(i + 1) % subjects}, ex:s{(i + 2) % subjects} ;\n'
                    f'  ex:addr [ ex:city "City {i % 50}" ] .\n')
    return write_once(fx(f"ttlrich-{n}.ttl"), p)


def gen_trig(n):
    per = 50

    def p(f):
        f.write(f"@prefix ex: <{EX}> .\n")
        for j in range((n + per - 1) // per):
            f.write(f"ex:g{j} {{\n")
            for i in range(per):
                k = j * per + i
                if k >= n:
                    break
                f.write(f"  ex:s{k} ex:p ex:o{k} .\n")
            f.write("}\n")
    return write_once(fx(f"trig-{n}.trig"), p)


def gen_rdfxml(n):
    def p(f):
        f.write('<?xml version="1.0"?>\n<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" '
                f'xmlns:ex="{EX}">\n')
        for i in range(n):
            f.write(f'  <rdf:Description rdf:about="{EX}s{i}">\n'
                    f'    <ex:p rdf:resource="{EX}o{i}"/>\n  </rdf:Description>\n')
        f.write("</rdf:RDF>\n")
    return write_once(fx(f"rdfxml-{n}.rdf"), p)


_GENE_PARAS = None


def gene_slice(k):
    """Header plus k paragraphs of gene.ttl taken at a regular stride, so the
    slice has the composition of the whole file."""
    global _GENE_PARAS
    path = fx(f"gene-{k}.ttl")
    if path.exists() and path.stat().st_size > 0:
        return path
    if _GENE_PARAS is None:
        text = GENE.read_text(encoding="utf-8")
        cut = text.index("\n\n")
        _GENE_PARAS = (text[:cut + 2], text[cut + 2:].split("\n\n"))
    head, paras = _GENE_PARAS
    if k >= len(paras):
        picked = paras
    else:
        step = len(paras) / k
        picked = [paras[int(i * step)] for i in range(k)]
    tmp = path.with_suffix(".tmp")
    tmp.write_text(head + "\n\n".join(picked) + "\n", encoding="utf-8")
    tmp.rename(path)
    return path


def conv_nt(src: Path, name: str):
    """Convert a file to N-Quads with the F* engine (used only to build
    fixtures; the output is the same for both engines' input)."""
    out = fx(name)
    if out.exists() and out.stat().st_size > 0:
        return out
    tmp = out.with_suffix(".tmp")
    with tmp.open("wb") as f:
        subprocess.run([str(FSTAR), "dump-nq", str(src)], stdout=f, check=True)
    tmp.rename(out)
    return out


# closure shapes (reused from tools/bench_closure.py)
def gen_closure_shape(shape, n):
    import bench_closure as bc
    path = fx(f"clo-{shape}-{n}.ttl")
    if not path.exists():
        path.write_text(bc.GENERATORS[shape](n), encoding="utf-8")
    return path


# canonicalisation shapes
def gen_canon(shape, n):
    p_ = f"<{EX}p>"

    def prod(f):
        if shape == "iri":
            for i in range(n):
                f.write(f"<{EX}s{i}> {p_} <{EX}o{i}> .\n")
        elif shape == "uniq":
            # every blank node has its own literal: distinct first-degree hashes
            for i in range(n):
                f.write(f'_:b{i} <{EX}name> "node {i}" .\n')
                f.write(f"_:b{i} {p_} _:b{(i + 1) % n} .\n")
        elif shape == "person":
            # person -> address blank node with shared literal values
            for i in range(n):
                f.write(f"<{EX}s{i}> <{EX}addr> _:a{i} .\n")
                f.write(f'_:a{i} <{EX}city> "city {i % 20}" .\n')
                f.write(f'_:a{i} <{EX}zip> "z{i % 50}" .\n')
        elif shape == "chain":
            # indistinguishable first-degree hashes: forces N-degree hashing
            for i in range(n):
                f.write(f"_:b{i} {p_} _:b{i + 1} .\n")
        else:
            raise ValueError(shape)
    return write_once(fx(f"canon-{shape}-{n}.nq"), prod)


# SHACL fixtures
SHACL_SHAPES = """@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix ex: <http://example.org/> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
ex:PersonShape a sh:NodeShape ;
  sh:targetClass ex:Person ;
  sh:property [ sh:path ex:name ; sh:minCount 1 ; sh:maxCount 1 ; sh:datatype xsd:string ; sh:minLength 3 ] ;
  sh:property [ sh:path ex:age ; sh:datatype xsd:integer ; sh:minInclusive 0 ; sh:maxInclusive 150 ] ;
  sh:property [ sh:path ex:email ; sh:pattern "^[a-z0-9.]+@example[.]org$" ] ;
  sh:property [ sh:path ex:knows ; sh:class ex:Person ; sh:nodeKind sh:IRI ] .
"""


def gen_shacl(n):
    shapes = fx("shacl-shapes.ttl")
    if not shapes.exists():
        shapes.write_text(SHACL_SHAPES, encoding="utf-8")

    def prod(f):
        f.write(f"@prefix ex: <{EX}> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n")
        for i in range(n):
            f.write(f'ex:p{i} a ex:Person ; ex:name "Person {i}" ; ex:age {i % 90} ; '
                    f'ex:email "user{i}@example.org" ; ex:knows ex:p{(i + 1) % n} .\n')
    data = write_once(fx(f"shacl-data-{n}.ttl"), prod)
    return data, shapes


def shacl_manifest(data: Path, shapes: Path):
    """A one-entry sht:Validate manifest so that the Lean SHACL runner can be
    pointed at an arbitrary data graph and shapes graph. Both are loaded from
    sibling files. The expected report says sh:conforms true; the runner is
    invoked with --conforms-only, so a wrong answer is a FAIL line, which this
    harness checks for."""
    m = fx(f"shacl-manifest-{data.stem}.ttl")
    if not m.exists():
        m.write_text(f"""@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix sht: <http://www.w3.org/ns/shacl-test#> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
<> a mf:Manifest ; mf:entries ( <bench-1> ) .
<bench-1> a sht:Validate ; rdfs:label "bench" ;
  mf:action [ sht:dataGraph <{data.name}> ; sht:shapesGraph <{shapes.name}> ] ;
  mf:result [ a sh:ValidationReport ; sh:conforms true ] ;
  mf:status sht:approved .
""", encoding="utf-8")
    return m


# JSON-LD fixtures (same five shapes as Harness/JsonLdScale.lean)
def jq(s):
    return '"' + s + '"'


def gen_jsonld(shape, n):
    ex = lambda s: EX + s

    def prod(f):
        if shape == "hub":
            nodes = [f'{{"@id": {jq(ex(f"n{i}"))}, "@type": {jq(ex("T"))}, {jq(ex("p"))}: {jq(f"value {i}")}, '
                     f'{jq(ex("link"))}: {{"@id": {jq(ex("hub"))}}}}}' for i in range(n)]
            nodes.append(f'{{"@id": {jq(ex("hub"))}, {jq(ex("p"))}: "hub"}}')
            f.write("[" + ", ".join(nodes) + "]")
        elif shape == "fanout":
            refs = [f'{{"@id": {jq(ex(f"o{i}"))}}}' for i in range(n)]
            f.write(f'{{"@id": {jq(ex("s"))}, {jq(ex("link"))}: [' + ", ".join(refs) + "]}")
        elif shape == "bnode":
            nodes = [f'{{"@id": {jq(f"_:x{i}")}, {jq(ex("p"))}: {jq(str(i))}, '
                     f'{jq(ex("link"))}: {{"@id": {jq(f"_:x{i + 1}")}}}}}' for i in range(n)]
            f.write("[" + ", ".join(nodes) + "]")
        elif shape == "graphs":
            gs = [f'{{"@id": {jq(ex(f"g{i}"))}, "@graph": [{{"@id": {jq(ex(f"n{i}"))}, {jq(ex("p"))}: "v"}}]}}'
                  for i in range(n)]
            f.write("[" + ", ".join(gs) + "]")
        elif shape == "wide":
            props = [f'{jq(ex(f"p{i}"))}: {jq(f"v{i}")}' for i in range(n)]
            f.write(f'{{"@id": {jq(ex("s"))}, ' + ", ".join(props) + "}")
        else:
            raise ValueError(shape)
    return write_once(fx(f"jsonld-{shape}-{n}.jsonld"), prod)


# --------------------------------------------------------------------------
# rows
# --------------------------------------------------------------------------
GENE_QUERIES = None


def gene_queries():
    global GENE_QUERIES
    if GENE_QUERIES is None:
        import bench_competitive_queries as q
        GENE_QUERIES = {k: v["sparql"] for k, v in q.QUERIES.items()}
    return GENE_QUERIES


class Row:
    def __init__(self, rid, group, desc, sizes, make, lean, fstar, unit="triples",
                 note=""):
        self.rid, self.group, self.desc = rid, group, desc
        self.sizes, self.make, self.lean, self.fstar = sizes, make, lean, fstar
        self.unit, self.note = unit, note


ROWS: dict[str, Row] = {}


def add(row):
    ROWS[row.rid] = row


def S(p):
    return str(p)


# a) parse
add(Row("parse-nt", "parse", "N-Triples, full IRIs, 1 triple per line",
        [10000, 20000, 40000, 80000, 160000], gen_nt,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "ntriples"],
        lambda p, n: [S(FSTAR), "count", S(p)]))
add(Row("parse-nt-mixed", "parse", "N-Triples, mixed term kinds (IRI, plain, lang, typed, bnode)",
        [10000, 20000, 40000, 80000], lambda n: gen_mixed_nt(n, False),
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "ntriples"],
        lambda p, n: [S(FSTAR), "count", S(p)]))
add(Row("parse-nq", "parse", "N-Quads, mixed term kinds, 8 graphs",
        [10000, 20000, 40000, 80000], lambda n: gen_mixed_nt(n, True),
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "nquads"],
        lambda p, n: [S(FSTAR), "count", S(p)]))
add(Row("parse-ttl", "parse", "Turtle, prefixed names, 1 triple per line",
        [10000, 20000, 40000, 80000], gen_ttl,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "turtle"],
        lambda p, n: [S(FSTAR), "count", S(p)]))
add(Row("parse-ttl-rich", "parse", "Turtle, predicate lists, object lists, typed literals, bnode property lists",
        [10000, 20000, 40000, 80000], gen_ttl_rich,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "turtle"],
        lambda p, n: [S(FSTAR), "count", S(p)]))
add(Row("parse-ttl-gene", "parse", "Turtle, real data: slices of gene.ttl (Wikidata life sciences)",
        [5000, 10000, 20000, 40000, 80000], gene_slice,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "turtle"],
        lambda p, n: [S(FSTAR), "count", S(p)], unit="paragraphs"))
add(Row("parse-trig", "parse", "TriG, 50 triples per named graph",
        [10000, 20000, 40000, 80000], gen_trig,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "trig"],
        lambda p, n: [S(FSTAR), "count", S(p)]))
add(Row("parse-rdfxml", "parse", "RDF/XML, one rdf:Description per triple",
        [2500, 5000, 10000, 20000, 40000], gen_rdfxml,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "rdfxml"],
        lambda p, n: [S(FSTAR), "count", S(p)]))

# a2) parse + serialize
add(Row("ser-nq-nt", "serialize", "N-Triples parse then N-Quads out",
        [10000, 20000, 40000, 80000], gen_nt,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "ntriples", "--out", "nquads"],
        lambda p, n: [S(FSTAR), "dump-nq", S(p)]))
add(Row("ser-nq-ttl-gene", "serialize", "gene.ttl slice parse then N-Quads out",
        [5000, 10000, 20000, 40000], gene_slice,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "turtle", "--out", "nquads"],
        lambda p, n: [S(FSTAR), "dump-nq", S(p)], unit="paragraphs"))
add(Row("ser-ttl-gene", "serialize", "gene.ttl slice parse then Turtle out",
        [5000, 10000, 20000, 40000], gene_slice,
        lambda p, n: [S(LEAN), "parse", S(p), "--format", "turtle", "--out", "turtle"],
        lambda p, n: [S(FSTAR), "dump-turtle", S(p)], unit="paragraphs"))

# b) SPARQL on the real corpus
for qid in ("q1_count_star", "q2_bound_predicate_count", "q3_subject_point_lookup",
            "q4_two_pattern_join", "q5_group_by", "q6_optional_filter"):
    add(Row(f"query-{qid.split('_')[0]}", "sparql",
            f"SPARQL {qid} over gene.ttl slices (total = read + parse + query + print)",
            [5000, 10000, 20000, 40000, 80000], gene_slice,
            (lambda qid: lambda p, n: [S(LEAN), "query", S(p), "--format", "turtle",
                                       "--query-string", gene_queries()[qid]])(qid),
            (lambda qid: lambda p, n: [S(FSTAR), "query", "--data", S(p), "-e",
                                       gene_queries()[qid]])(qid),
            unit="paragraphs"))

add(Row("query-groupby-subject", "sparql",
        "SPARQL GROUP BY ?s (one group per subject) over gene.ttl slices",
        [1250, 2500, 5000, 10000, 20000], gene_slice,
        lambda p, n: [S(LEAN), "query", S(p), "--format", "turtle", "--query-string",
                      "SELECT ?s (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?s"],
        lambda p, n: [S(FSTAR), "query", "--data", S(p), "-e",
                      "SELECT ?s (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?s"],
        unit="paragraphs"))

# b2) SPARQL shapes outside the six corpus queries: DISTINCT, aggregate DISTINCT,
# ORDER BY. The UK Parliament endpoint is not in the checkout, so these run on
# gene.ttl slices; they exist to look for further quadratic evaluator costs.
for rid, desc, sparql in (
        ("query-distinct", "SPARQL SELECT DISTINCT ?s ?p over gene.ttl slices",
         "SELECT DISTINCT ?s ?p WHERE { ?s ?p ?o }"),
        ("query-count-distinct", "SPARQL COUNT(DISTINCT ?s) over gene.ttl slices",
         "SELECT (COUNT(DISTINCT ?s) AS ?c) WHERE { ?s ?p ?o }"),
        ("query-orderby", "SPARQL ORDER BY ?s ?p with LIMIT 20 over gene.ttl slices",
         "SELECT ?s ?p ?o WHERE { ?s ?p ?o } ORDER BY ?s ?p LIMIT 20")):
    add(Row(rid, "sparql", desc, [1250, 2500, 5000, 10000, 20000], gene_slice,
            (lambda sparql: lambda p, n: [S(LEAN), "query", S(p), "--format", "turtle",
                                          "--query-string", sparql])(sparql),
            (lambda sparql: lambda p, n: [S(FSTAR), "query", "--data", S(p), "-e", sparql])(sparql),
            unit="paragraphs"))

# c) closure
CLOSURE_SIZES = {
    "chain": [10, 20, 40, 80],
    "tree": [64, 128, 256, 512],
    "diamond": [16, 32, 64, 128],
    "wideflat": [250, 500, 1000, 2000],
    "dense": [125, 250, 500, 1000],
}
for shape, sizes in CLOSURE_SIZES.items():
    add(Row(f"rdfs-{shape}", "closure", f"RDFS closure, synthetic shape {shape}",
            sizes, (lambda shape: lambda n: gen_closure_shape(shape, n))(shape),
            lambda p, n: [S(LEAN), "closure", S(p), "--regime", "rdfs", "--format", "turtle"],
            lambda p, n: [S(FSTAR), "entail", "--data", S(p), "--regime", "RDFS"],
            unit="n"))
OWL_SIZES = {
    "chain": [10, 20, 40, 80],
    "wideflat": [125, 250, 500, 1000],
    "dense": [62, 125, 250, 500],
}
for shape, sizes in OWL_SIZES.items():
    add(Row(f"owlrl-{shape}", "closure", f"OWL 2 RL closure, synthetic shape {shape}",
            sizes, (lambda shape: lambda n: gen_closure_shape(shape, n))(shape),
            lambda p, n: [S(LEAN), "closure", S(p), "--regime", "owl-rl", "--format", "turtle"],
            lambda p, n: [S(FSTAR), "entail", "--data", S(p), "--regime", "OWL-RL"],
            unit="n"))

VOCABS = [
    ("skos", "third_party/vocabularies/skos.rdf", "rdfxml"),
    ("foaf", "third_party/vocabularies/foaf.rdf", "rdfxml"),
    ("dcterms", "third_party/vocabularies/dublin_core_terms.ttl", "turtle"),
    ("schemaorg", "third_party/vocabularies/schemaorg-30.0-current-https.ttl", "turtle"),
    ("qudt", "third_party/qudt/QUDT-all-in-one-OWL.ttl", "turtle"),
]
for name, rel, fmt in VOCABS:
    for regime, lname, fname in (("rdfs", "rdfs", "RDFS"), ("owlrl", "owl-rl", "OWL-RL")):
        add(Row(f"{regime}-vocab-{name}", "closure", f"{fname} closure of the real vocabulary {name}",
                [0], (lambda rel: lambda n: ROOT / rel)(rel),
                (lambda lname, fmt: lambda p, n: [S(LEAN), "closure", S(p), "--regime", lname,
                                                  "--format", fmt])(lname, fmt),
                (lambda fname: lambda p, n: [S(FSTAR), "entail", "--data", S(p),
                                             "--regime", fname])(fname),
                unit="file"))

# d) canonicalisation and SHACL
CANON_SIZES = {"iri": [500, 1000, 2000, 4000], "uniq": [125, 250, 500, 1000],
               "person": [125, 250, 500, 1000], "chain": [25, 50, 100, 200]}
for shape, sizes in CANON_SIZES.items():
    add(Row(f"rdfc-{shape}", "rdfc", f"RDFC-1.0 canonicalisation, shape {shape}",
            sizes, (lambda shape: lambda n: gen_canon(shape, n))(shape),
            lambda p, n: [S(LEAN), "canonicalize", S(p), "--format", "nquads"],
            lambda p, n: [S(FSTAR), "canonicalize", S(p)], unit="n"))

add(Row("shacl-person", "shacl", "SHACL Core: 4 property shapes over n Person nodes",
        [500, 1000, 2000, 4000], gen_shacl,
        lambda dp, n: [S(LEAN_SHACL), "--conforms-only", S(shacl_manifest(*dp))],
        lambda dp, n: [S(FSTAR), "shacl", "--data", S(dp[0]), "--shapes", S(dp[1])],
        unit="n", note="Lean time includes manifest parse and report comparison"))

for shape, sizes in {"hub": [250, 500, 1000, 2000], "fanout": [250, 500, 1000, 2000],
                     "bnode": [250, 500, 1000, 2000], "graphs": [250, 500, 1000, 2000],
                     "wide": [250, 500, 1000, 2000]}.items():
    add(Row(f"jsonld-torf-{shape}", "jsonld", f"JSON-LD to RDF, shape {shape}",
            sizes, (lambda shape: lambda n: gen_jsonld(shape, n))(shape),
            (lambda shape: lambda p, n: [S(LEAN_JSONLD), "--scale", "--once", shape, "toRdf", str(n)])(shape),
            lambda p, n: [S(FSTAR), "jsonld", "--in", S(p)], unit="n",
            note="Lean builds the document text in-process; F* reads it from a file"))


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------
def run_rows(args):
    out = open(args.out, "a", encoding="utf-8")
    sel = [r for r in args.rows.split(",") if r] if args.rows else list(ROWS)
    for rid in sel:
        row = ROWS[rid]
        sizes = row.sizes
        if args.max_size:
            sizes = [s for s in sizes if s <= args.max_size or s == 0]
        if args.first_only:
            sizes = sizes[:1]
        lean_dead = False
        fstar_dead = False
        for n in sizes:
            inp = row.make(n)
            for engine, fn in (("lean", row.lean), ("fstar", row.fstar)):
                if engine == "lean" and lean_dead:
                    rec = {"status": "skipped-after-cap"}
                elif engine == "fstar" and fstar_dead:
                    rec = {"status": "skipped-after-cap"}
                else:
                    cmd = fn(inp, n)
                    rec = measure(cmd, args.runs, args.cap, args.single_over)
                    rec["cmd"] = " ".join(cmd)
                    if rec["status"] in ("cap",):
                        if engine == "lean":
                            lean_dead = True
                        else:
                            fstar_dead = True
                rec.update({"row": rid, "group": row.group, "engine": engine, "n": n,
                            "unit": row.unit, "time": time.strftime("%H:%M:%S")})
                out.write(json.dumps(rec) + "\n")
                out.flush()
                print(f"{rid:24s} n={n:<8d} {engine:5s} {rec['status']:6s} "
                      f"wall={rec.get('wall', float('nan')):8.3f}s cpu={rec.get('cpu', float('nan')):8.3f}s "
                      f"load={rec.get('load1', float('nan')):.2f} out={rec.get('first_line', '')[:40]!r}",
                      flush=True)
    out.close()


def fmt_t(r):
    if r is None:
        return "-"
    if r["status"] == "cap":
        return f">{r['wall']:.0f}s cap"
    if r["status"] == "skipped-after-cap":
        return "skip"
    if r["status"] != "ok":
        return r["status"]
    t = r["wall"]
    return f"{t:.3f}s" if t < 100 else f"{t:.0f}s"


def report(path):
    recs = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    by = {}
    for r in recs:
        by.setdefault(r["row"], {}).setdefault(r["n"], {})[r["engine"]] = r
    # The memory columns carry the survey's memory rule
    # (docs/designissues/2026-10-10-lean-vs-fstar-performance.md, section 2):
    # a row ranks when the Lean peak resident set at its largest size is more
    # than 3 times the F* one (https://github.com/danbri/factoidal/issues/729).
    print("| row | n | unit | Lean | F* | Lean / F* | load | Lean x per doubling "
          "| Lean MB | F* MB | Lean MB / F* MB |")
    print("|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for rid, ns in by.items():
        sizes = sorted(ns)
        prev = None
        growths = []
        for n in sizes:
            le, fs = ns[n].get("lean"), ns[n].get("fstar")
            ratio = "-"
            if le and fs and le["status"] == "ok" and fs["status"] == "ok" and fs["wall"] > 0:
                ratio = f"{le['wall'] / fs['wall']:.1f}"
            g = ""
            if prev is not None and prev[0] > 0 and n == 2 * prev[0]:
                pl = prev[1]
                if le and le["status"] == "ok" and pl and pl["status"] == "ok" and pl["wall"] >= 0.05:
                    gv = le["wall"] / pl["wall"]
                    growths.append(gv)
                    g = f"{gv:.2f}"
            load = max((x.get("load1", 0) for x in (le, fs) if x and "load1" in x), default=0)
            lmb = le["rss_kb"] / 1024 if le and le["status"] == "ok" and le.get("rss_kb") else None
            fmb = fs["rss_kb"] / 1024 if fs and fs["status"] == "ok" and fs.get("rss_kb") else None
            mratio = f"{lmb / fmb:.1f}" if lmb and fmb else "-"
            print(f"| {rid} | {n} | {(le or fs or {}).get('unit', '')} | {fmt_t(le)} | {fmt_t(fs)} | {ratio} | {load:.1f} | {g} "
                  f"| {f'{lmb:.0f}' if lmb else '-'} | {f'{fmb:.0f}' if fmb else '-'} | {mratio} |")
            prev = (n, le)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--rows", default="")
    ap.add_argument("--out", default="/tmp/bench-lean-vs-fstar.jsonl")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--cap", type=float, default=120.0)
    ap.add_argument("--single-over", type=float, default=15.0,
                    help="run once when the first run exceeds this many seconds")
    ap.add_argument("--max-size", type=int, default=0)
    ap.add_argument("--first-only", action="store_true",
                    help="measure only the smallest size of each row (smoke test)")
    ap.add_argument("--report", default="")
    args = ap.parse_args()
    if args.report:
        return report(args.report)
    if args.list:
        for r in ROWS.values():
            print(f"{r.rid:24s} {r.group:10s} {r.sizes}  {r.desc}")
        return 0
    for b in (LEAN, FSTAR):
        if not b.exists():
            print(f"missing binary {b}", file=sys.stderr)
            return 2
    run_rows(args)
    return 0


if __name__ == "__main__":
    sys.exit(main())
