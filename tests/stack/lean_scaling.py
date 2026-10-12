#!/usr/bin/env python3
"""Scaling assertions for the Lean command line (l4factoidal).

For each row below the script generates an input of size x and one of size
4x, runs the Lean command on both (the minimum wall time of RUNS runs each),
and checks

    time(4x)  <=  BOUND * max(time(x), FLOOR)

with BOUND = 9.0 and FLOOR = 0.05 s. A linear or n log n command gives a
ratio of about 4 to 6; a quadratic command gives about 16. The floor keeps the
fixed cost of starting the process from turning timer noise into a failure.
This is the n, 2n, 4n assertion of skills/danbri-function-precrime-checkers,
for the paths that the survey of 2026-10-10 found quadratic and that were
repaired (docs/designissues/2026-10-10-lean-vs-fstar-performance.md):

  rdfs-closure-*   RDFS closure of a wide, a dense and a tree-shaped schema
  owlrl-closure-chain  OWL RL closure of a chain of subclass axioms. The closure
                   of n axioms has n(n-1)/2 triples, so 4x input is 16x output
                   and the row uses the bound 20.0 (ROW_BOUND)
  trig-parse       TriG parse, many small graph blocks
  trig-big-graph   TriG parse, one graph block with all the triples
  turtle-serialize Turtle pretty-printer over slices of a real life-sciences file
  turtle-object-list  Turtle parse of one statement whose object list has n
                   objects (`ex:s ex:p 0, 1, ... .`), 25,000 against 100,000
                   (https://github.com/danbri/factoidal/issues/754; the object
                   list was built with `acc ++ ...`: 10.33 s at 25,000 and no
                   result in 120 s at 100,000 before the repair, 0.058 s and
                   0.403 s after, measured 2026-10-12)
  rdfc-iri         RDFC-1.0 canonicalisation of a graph with no blank nodes
  rdfc-person      RDFC-1.0 canonicalisation of a graph with one blank node per person
  rdfc-bnode-unique  RDFC-1.0 canonicalisation of n persons, each a blank node with an
                   rdf:type, a name and an age (3n quads, every first-degree hash
                   unique): the input of the npm speed gate's canonicalize row
                   (https://github.com/danbri/factoidal/issues/745; 0.54 s to 9.49 s
                   for 4x input before the blank node to quads map, 0.18 s to 1.19 s
                   after)
  rdfc-bnode-collide  RDFC-1.0 canonicalisation of n blank nodes that share one
                   first-degree hash, so Hash N-Degree Quads runs for each.
                   Expected failure naming issue 751: 0.16 s to 2.37 s CPU for 4x
                   input (each Hash N-Degree Quads call filters every quad)
  group-by-few     SPARQL GROUP BY with 6 groups over many rows
  group-by-many    SPARQL GROUP BY with one group per subject
  count-distinct   SPARQL COUNT(DISTINCT ?s): the aggregate's DISTINCT
                   (https://github.com/danbri/factoidal/issues/722; 1.4 s to
                   22.8 s for 4x input before the repair, 0.12 s to 0.65 s after)
  count-distinct-star  SPARQL COUNT(DISTINCT *): DISTINCT rows inside an
                   aggregate (issue 722; 0.43 s to 11.7 s before, 0.11 s to 0.60 s after)
  query-vs-parse   `query` COUNT(*) against `parse` of the same 5,000 paragraphs of
                   gene.ttl: at most 2.0 times the CPU time and the peak memory
                   (https://github.com/danbri/factoidal/issues/724; 5.7 and 3.7
                   times before the command line stopped re-parsing N-Quads
                   text, 1.6 and 1.0 after)
  query-memory     peak resident memory of `query` COUNT(*) per input byte, from
                   x to 4x paragraphs of gene.ttl: at most 32 bytes
                   (https://github.com/danbri/factoidal/issues/729; 36.6 before
                   the Turtle reader stopped building the whole document as a
                   character list, 27 after)
  query-memory-fstar  the same slope against 3 times the F* engine's (2.0 bytes
                   per input byte on the same files): at most 6 bytes. Expected
                   failure naming issue 729 until the index and the solution
                   sequence stop growing with the data
  select-star      `query` SELECT * over 1,250 and 5,000 paragraphs of gene.ttl:
                   every row is printed. Expected failure naming issue 729:
                   0.34 s to 5.78 s CPU and 66 MB to 220 MB (F*: 1.43 s and
                   26 MB at 5,000). The command line parses the JSON envelope
                   the op returns (`JSON.parseItems` appends each item with
                   `acc ++ [v]`, in a mutual block) and pretty-prints it
  shacl-person     SHACL Core validation (l4shacl, a one-entry manifest) of n
                   ex:Person nodes against 4 property shapes
                   (https://github.com/danbri/factoidal/issues/723; 0.31 s to
                   3.82 s for 4x input before the data index, 0.043 s to 0.139 s after)
  termwire-page-decode  decode of one PTD2 page of n IRI terms (term codec v2,
                   the IBK5 dictionary page), 100 times, through
                   `l4termwire-page-decode`. Bound 6.0 (ROW_BOUND). Before the
                   repair of https://github.com/danbri/factoidal/issues/783
                   `TermWireV2.parseInline` took `List.length` of the rest of the
                   page for each term: 1,000 to 4,000 terms, 5 decodes, went from
                   0.20 s to 5.30 s (ratio 26); after, 0.015 s to 0.049 s
  startup          process start: `l4factoidal version` must take at most
                   STARTUP_BUDGET (20 ms) of CPU time, minimum of 15 runs
                   (305 million instructions and 43 ms before the fixtures were
                   moved out of the executable's modules; 25 million and 7 ms
                   after)

Expected failures (CLAUDE.md, "A stated shortfall is a failing test plus an
open issue"; skills/test-suites/SKILL.md, "Expected failures"): a row listed in
XFAIL is a cost that is known and not yet repaired. It still runs. When it
fails the bound it prints "XFAIL" with its issue URL and counts as
expected-fail, not as a pass; when it PASSES it prints "UNEXPECTED PASS" and
counts as a failure, so the run is red until the row is removed from XFAIL
(the repair turns the row into a real assertion) and the issue is closed.

The script measures; it does not compare with the F* engine. Exit status 0
when every pair passes or fails as expected, 1 when a pair fails or an
expected failure passes, 2 when the binary is missing. Scores print as
"N pass, M fail, K expected-fail (out of T)".

Usage:  tests/stack/lean_scaling.py [--runs N] [--only ROW[,ROW...]]
Env:    L4_BIN     path of l4factoidal (default formal/lean4/.lake/build/bin/l4factoidal)
        L4_SHACL_BIN   path of l4shacl (default: beside L4_BIN)
        L4_TERMWIRE_BIN  path of l4termwire-page-decode (default: beside L4_BIN)
        L4_SCALING_CAP   seconds per run before it counts as a failure (default 120)
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import bench_closure as bc  # noqa: E402  (closure shape generators)
import bench_lean_vs_fstar as bl  # noqa: E402  (real-data slices)

BOUND = 9.0
FLOOR = 0.05
BIN = Path(os.environ.get("L4_BIN", ROOT / "formal/lean4/.lake/build/bin/l4factoidal"))
SHACL_BIN = Path(os.environ.get("L4_SHACL_BIN", BIN.parent / "l4shacl"))
TERMWIRE_BIN = Path(os.environ.get("L4_TERMWIRE_BIN", BIN.parent / "l4termwire-page-decode"))
CAP = float(os.environ.get("L4_SCALING_CAP", "120"))
FIX = Path(os.environ.get("L4_SCALING_FIXTURES", "/tmp/factoidal-lean-scaling"))
EX = "http://example.org/"
# Rows whose OUTPUT grows faster than their input use a larger bound.
ROW_BOUND = {"owlrl-closure-chain": 20.0, "termwire-page-decode": 6.0}
# Rows that fail today, each with the open issue that tracks the cost. A row
# leaves this table in the commit that repairs it.
XFAIL: dict[str, str] = {
    "rdfc-bnode-collide": "https://github.com/danbri/factoidal/issues/751",
    "query-memory-fstar": "https://github.com/danbri/factoidal/issues/729",
    "select-star": "https://github.com/danbri/factoidal/issues/729",
}
# A run longer than this is not repeated: the minimum of several runs only
# removes timer and load noise, which is small against a run this long.
REPEAT_LIMIT = 5.0


def fixture(name: str, text_fn) -> Path:
    FIX.mkdir(parents=True, exist_ok=True)
    p = FIX / name
    if not p.exists():
        p.write_text(text_fn(), encoding="utf-8")
    return p


def rdfc_persons(n: int) -> str:
    """n blank-node persons, as tests/perf/l4_vs_fstar_wasm_bench.mjs writes
    them for its canonicalize row: every first-degree hash is unique."""
    rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
    xsd_int = "http://www.w3.org/2001/XMLSchema#integer"
    out = []
    for i in range(n):
        out.append(f"_:p{i} <{rdf_type}> <{EX}Person> .")
        out.append(f'_:p{i} <{EX}name> "Person {i}" .')
        out.append(f'_:p{i} <{EX}age> "{18 + i % 60}"^^<{xsd_int}> .')
    return "\n".join(out) + "\n"


def rdfc_collide(n: int) -> str:
    """n blank nodes with one quad each and the same first-degree hash."""
    rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
    return "".join(f"_:p{i} <{rdf_type}> <{EX}Person> .\n" for i in range(n))


def trig_blocks(n: int) -> str:
    per = 50
    out = [f"@prefix ex: <{EX}> ."]
    for j in range((n + per - 1) // per):
        out.append(f"ex:g{j} {{")
        for i in range(per):
            k = j * per + i
            if k < n:
                out.append(f"  ex:s{k} ex:p ex:o{k} .")
        out.append("}")
    return "\n".join(out) + "\n"


def trig_one_graph(n: int) -> str:
    body = "\n".join(f"  ex:s{i} ex:p ex:o{i} ." for i in range(n))
    return f"@prefix ex: <{EX}> .\nex:g {{\n{body}\n}}\n"


def turtle_object_list(n: int) -> str:
    """One statement, one subject, one predicate, n objects."""
    objs = ", ".join(str(i) for i in range(n))
    return f"@prefix ex: <{EX}> .\nex:s ex:p {objs} .\n"


# row id -> (small size, make input path, command builder)
ROWS = {
    "rdfs-closure-wideflat": (
        1000,
        lambda n: fixture(f"clo-wideflat-{n}.ttl", lambda: bc.GENERATORS["wideflat"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "rdfs", "--format", "turtle"]),
    "rdfs-closure-dense": (
        250,
        lambda n: fixture(f"clo-dense-{n}.ttl", lambda: bc.GENERATORS["dense"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "rdfs", "--format", "turtle"]),
    "rdfs-closure-tree": (
        256,
        lambda n: fixture(f"clo-tree-{n}.ttl", lambda: bc.GENERATORS["tree"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "rdfs", "--format", "turtle"]),
    "owlrl-closure-chain": (
        20,
        lambda n: fixture(f"clo-chain-{n}.ttl", lambda: bc.GENERATORS["chain"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "owl-rl", "--format", "turtle"]),
    "trig-parse": (
        2500,
        lambda n: fixture(f"trig-blocks-{n}.trig", lambda: trig_blocks(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "trig"]),
    "trig-big-graph": (
        2500,
        lambda n: fixture(f"trig-one-{n}.trig", lambda: trig_one_graph(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "trig"]),
    "turtle-object-list": (
        25000,
        lambda n: fixture(f"turtle-object-list-{n}.ttl", lambda: turtle_object_list(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "turtle"]),
    "turtle-serialize": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "parse", str(p), "--format", "turtle", "--out", "turtle"]),
    "rdfc-iri": (
        1000,
        lambda n: bl.gen_canon("iri", n),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "rdfc-person": (
        125,
        lambda n: bl.gen_canon("person", n),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "rdfc-bnode-unique": (
        2000,
        lambda n: fixture(f"rdfc-bnode-unique-{n}.nq", lambda: rdfc_persons(n)),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "rdfc-bnode-collide": (
        2000,
        lambda n: fixture(f"rdfc-bnode-collide-{n}.nq", lambda: rdfc_collide(n)),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "group-by-few": (
        2500,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT ?p (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?p"]),
    "group-by-many": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT ?s (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?s"]),
    "count-distinct": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT (COUNT(DISTINCT ?s) AS ?c) WHERE { ?s ?p ?o }"]),
    "count-distinct-star": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT (COUNT(DISTINCT *) AS ?c) WHERE { ?s ?p ?o }"]),
    "select-star": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT * WHERE { ?s ?p ?o }"]),
    "termwire-page-decode": (
        1000,
        lambda n: n,
        lambda n: [str(TERMWIRE_BIN), str(n), "100"]),
    "shacl-person": (
        500,
        lambda n: bl.shacl_manifest(*bl.gen_shacl(n)),
        lambda p: [str(SHACL_BIN), "--conforms-only", str(p)]),
}


def best_of(cmd, runs):
    best = None
    for _ in range(runs):
        t0 = time.perf_counter()
        try:
            r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                               timeout=CAP)
        except subprocess.TimeoutExpired:
            return None, f"timeout after {CAP:.0f} s"
        dt = time.perf_counter() - t0
        if r.returncode != 0:
            return None, f"exit {r.returncode}: {r.stderr.decode('utf-8', 'replace')[:200]}"
        best = dt if best is None else min(best, dt)
        if dt > REPEAT_LIMIT:
            break
    return best, None


STARTUP_BUDGET = 0.020

# Rows that compare a verb with `parse` of the SAME input (gene.ttl, 4x the
# base size): the verb may take at most RATIO times the CPU time and RATIO
# times the peak resident memory of the parse. A COUNT(*) query reads the
# file once and counts; its cost above the parse is the evaluation. The
# command line used to write the parsed dataset as N-Quads text and parse the
# text again (https://github.com/danbri/factoidal/issues/724): 5.7 times the
# CPU time and 3.7 times the memory of `parse` before the repair, 1.6 and 1.0
# after (RDF/DatasetNormalize.lean, Wasm/Ops/FromDataset.lean).
PARSE_RATIO = 2.0
PARSE_RATIO_ROWS = {
    "query-vs-parse": (1250, "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }"),
}


def best_cpu_rss(cmd, runs):
    """Minimum CPU time of `runs` runs and the peak RSS (KB) of that run."""
    best = None
    for _ in range(runs):
        t = bl.run_once(cmd, CAP)
        if t["status"] != "ok":
            return None, f"exit status {t['status']}"
        if best is None or t["cpu"] < best["cpu"]:
            best = t
        if t["wall"] > REPEAT_LIMIT:
            break
    return best, None


def parse_ratio_row(rid, runs):
    x, sparql = PARSE_RATIO_ROWS[rid]
    p = bl.gene_slice(4 * x)
    q, e1 = best_cpu_rss([str(BIN), "query", str(p), "--format", "turtle",
                          "--query-string", sparql], runs)
    r, e2 = best_cpu_rss([str(BIN), "parse", str(p), "--format", "turtle"], runs)
    if e1 or e2:
        return False, f"n={4 * x}: {e1 or e2}"
    ok = (q["cpu"] <= PARSE_RATIO * max(r["cpu"], FLOOR)
          and q["rss_kb"] <= PARSE_RATIO * r["rss_kb"])
    return ok, (f"n={4 * x}: query {q['cpu']:.3f} s CPU {q['rss_kb'] / 1024:.0f} MB, "
                f"parse {r['cpu']:.3f} s CPU {r['rss_kb'] / 1024:.0f} MB "
                f"(ratios {q['cpu'] / max(r['cpu'], 1e-9):.1f} and "
                f"{q['rss_kb'] / max(r['rss_kb'], 1):.1f}; bound {PARSE_RATIO})")


# Rows that bound the peak resident memory of a verb PER INPUT BYTE
# (https://github.com/danbri/factoidal/issues/729). The measure is the slope
#
#     (peak RSS at 4x - peak RSS at x) / (input bytes at 4x - input bytes at x)
#
# so the fixed memory of a started process (about 12 MB) does not enter it,
# and a ratio to the input is not read as a trend (the error recorded in
# docs/designissues/2026-09-05-shard-pack-profile-and-memory.md section 3).
# Peak RSS does not move with load, so one run per size is enough.
#
# query-memory: 32 bytes. The whole document as a Lean `List Char` costs 34
# bytes of peak RSS per input byte on its own (`l4query-phases --stop-after
# chars`), so any path that builds it again fails the row. Measured 36.6
# before the repair (parseTurtle's `text.toList`), 27 after
# (`Syntax.parseTurtleText`), 10,000 to 40,000 paragraphs.
# query-memory-fstar: 6 bytes, 3 times the F* engine's slope on the same
# files (2.0: 16 MB at 10,000 and 42 MB at 160,000 paragraphs). This is the
# survey's memory rule (section 2 of the design record) as a gate row.
MEMORY_ROWS = {
    "query-memory": (10000, "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }", 32.0),
    "query-memory-fstar": (10000, "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }", 6.0),
}


def memory_row(rid):
    x, sparql, bound = MEMORY_ROWS[rid]
    pts = []
    for n in (x, 4 * x):
        p = bl.gene_slice(n)
        t = bl.run_once([str(BIN), "query", str(p), "--format", "turtle",
                         "--query-string", sparql], CAP)
        if t["status"] != "ok":
            return False, f"n={n}: exit status {t['status']}"
        pts.append((n, p.stat().st_size, t["rss_kb"]))
    (n1, b1, r1), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    ok = slope <= bound
    return ok, (f"n={n1} {r1 / 1024:.0f} MB ({b1} bytes) -> n={n4} {r4 / 1024:.0f} MB "
                f"({b4} bytes): {slope:.1f} bytes of peak RSS per input byte (bound {bound})")


def startup_row():
    """Minimum CPU time (user + system) of `l4factoidal version`."""
    best = None
    for _ in range(15):
        t = bl.run_once([str(BIN), "version"], CAP)
        if t["status"] != "ok":
            return None, f"exit status {t['status']}"
        best = t["cpu"] if best is None else min(best, t["cpu"])
    return best, None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--only", default="")
    args = ap.parse_args()
    if not BIN.exists():
        print(f"lean_scaling: {BIN} not built (cd formal/lean4 && lake build l4factoidal)",
              file=sys.stderr)
        return 2
    names = [r for r in args.only.split(",") if r]
    rows = [r for r in names if r in ROWS] or ([] if names else list(ROWS))
    ratio_rows = [r for r in names if r in PARSE_RATIO_ROWS] or (
        [] if names else list(PARSE_RATIO_ROWS))
    memory_rows = [r for r in names if r in MEMORY_ROWS] or (
        [] if names else list(MEMORY_ROWS))
    run_startup = (not names) or ("startup" in names)
    passed = failed = xfailed = 0
    print(f"Lean scaling assertion: time(4x) <= {BOUND} * max(time(x), {FLOOR} s) "
          f"(rows in ROW_BOUND use their own bound); "
          f"minimum of {args.runs} runs; load average {os.getloadavg()[0]:.2f}")
    for rid in rows:
        x, make, cmd = ROWS[rid]
        issue = XFAIL.get(rid)
        t1, e1 = best_of(cmd(make(x)), args.runs)
        t4, e4 = best_of(cmd(make(4 * x)), args.runs)
        if e1 or e4:
            ok = False
            detail = f"n={x} -> n={4 * x}: {e1 or e4}"
        else:
            bound = ROW_BOUND.get(rid, BOUND)
            ok = t4 <= bound * max(t1, FLOOR)
            detail = (f"n={x} {t1:.3f} s -> n={4 * x} {t4:.3f} s "
                      f"(ratio {t4 / max(t1, 1e-9):.1f} for 4x input)")
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    for rid in ratio_rows:
        issue = XFAIL.get(rid)
        ok, detail = parse_ratio_row(rid, args.runs)
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    for rid in memory_rows:
        issue = XFAIL.get(rid)
        ok, detail = memory_row(rid)
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    if run_startup:
        cpu, err = startup_row()
        if err:
            failed += 1
            print(f"  FAIL startup: {err}")
        else:
            ok = cpu <= STARTUP_BUDGET
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} startup: l4factoidal version {cpu * 1000:.1f} ms CPU "
                  f"(budget {STARTUP_BUDGET * 1000:.0f} ms)")
    print(f"scaling: {passed} pass, {failed} fail, {xfailed} expected-fail "
          f"(out of {passed + failed + xfailed})")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
