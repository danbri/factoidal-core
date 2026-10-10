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
  trig-parse       TriG parse, many small graph blocks
  trig-big-graph   TriG parse, one graph block with all the triples
  turtle-serialize Turtle pretty-printer over slices of a real life-sciences file
  rdfc-iri         RDFC-1.0 canonicalisation of a graph with no blank nodes
  rdfc-person      RDFC-1.0 canonicalisation of a graph with one blank node per person
  group-by-few     SPARQL GROUP BY with 6 groups over many rows
  group-by-many    SPARQL GROUP BY with one group per subject
  startup          process start: `l4factoidal version` must take at most
                   STARTUP_BUDGET (20 ms) of CPU time, minimum of 15 runs
                   (305 million instructions and 43 ms before the fixtures were
                   moved out of the executable's modules; 25 million and 7 ms
                   after)

The script measures; it does not compare with the F* engine. Exit status 0
when every pair passes, 1 when a pair fails, 2 when the binary is missing.
Scores print as "N pass, M fail (out of T)".

Usage:  tests/stack/lean_scaling.py [--runs N] [--only ROW[,ROW...]]
Env:    L4_BIN     path of l4factoidal (default formal/lean4/.lake/build/bin/l4factoidal)
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
CAP = float(os.environ.get("L4_SCALING_CAP", "120"))
FIX = Path(os.environ.get("L4_SCALING_FIXTURES", "/tmp/factoidal-lean-scaling"))
EX = "http://example.org/"


def fixture(name: str, text_fn) -> Path:
    FIX.mkdir(parents=True, exist_ok=True)
    p = FIX / name
    if not p.exists():
        p.write_text(text_fn(), encoding="utf-8")
    return p


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
    "trig-parse": (
        2500,
        lambda n: fixture(f"trig-blocks-{n}.trig", lambda: trig_blocks(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "trig"]),
    "trig-big-graph": (
        2500,
        lambda n: fixture(f"trig-one-{n}.trig", lambda: trig_one_graph(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "trig"]),
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
    return best, None


STARTUP_BUDGET = 0.020


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
    run_startup = (not names) or ("startup" in names)
    passed = failed = 0
    print(f"Lean scaling assertion: time(4x) <= {BOUND} * max(time(x), {FLOOR} s); "
          f"minimum of {args.runs} runs; load average {os.getloadavg()[0]:.2f}")
    for rid in rows:
        x, make, cmd = ROWS[rid]
        t1, e1 = best_of(cmd(make(x)), args.runs)
        t4, e4 = best_of(cmd(make(4 * x)), args.runs)
        if e1 or e4:
            failed += 1
            print(f"  FAIL {rid}: n={x} -> n={4 * x}: {e1 or e4}")
            continue
        ok = t4 <= BOUND * max(t1, FLOOR)
        passed += ok
        failed += (not ok)
        print(f"  {'PASS' if ok else 'FAIL'} {rid}: n={x} {t1:.3f} s -> n={4 * x} {t4:.3f} s "
              f"(ratio {t4 / max(t1, 1e-9):.1f} for 4x input)")
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
    print(f"scaling: {passed} pass, {failed} fail (out of {passed + failed})")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
