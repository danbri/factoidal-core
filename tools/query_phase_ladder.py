#!/usr/bin/env python3
"""Time and peak memory of `l4factoidal query` by phase over a size ladder.

For each size n of the ladder (paragraphs of gene.ttl, the slices of
tools/bench_lean_vs_fstar.py) and each phase P of `l4query-phases`
(Harness/QueryPhases.lean), run

    l4query-phases FILE --query-string Q --stop-after P

under /usr/bin/time and record the peak resident set of that process (the most
that P and the phases before it held at one time) and its CPU time. The run
that stops after the last phase also gives the in-process wall time at the end
of each phase (the `ms=` field), so the time of a phase is the difference of
two consecutive `ms=` values of ONE process.

Prints one markdown table of phase times (ms) and one of peak resident set
(MB), and the growth per doubling of each phase (time at 2n over time at n).

Usage:
  tools/query_phase_ladder.py [--sizes 1250,2500,5000,10000]
      [--query 'SELECT * WHERE { ?s ?p ?o }'] [--phases a,b,...]
      [--bin formal/lean4/.lake/build/bin/l4query-phases] [--cap 600]
      [--json-out FILE]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import bench_lean_vs_fstar as bl  # noqa: E402

PHASES = ["read", "parse", "normalize", "index", "solutions", "eval", "decode", "render",
          "output"]
LINE = re.compile(r"phase=(\S+) value=(\d+) rss_kb=(\d+) hwm_kb=(\d+) ms=(\d+)")


def run(binary, path, query, stop, cap):
    cmd = ["/usr/bin/time", "-f", "TIME %e %U %S %M", str(binary), str(path),
           "--query-string", query, "--stop-after", stop]
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                       timeout=cap, text=True)
    lines = {}
    tm = None
    for line in r.stderr.splitlines():
        m = LINE.search(line)
        if m:
            lines[m.group(1)] = {"value": int(m.group(2)), "rss_kb": int(m.group(3)),
                                 "hwm_kb": int(m.group(4)), "ms": int(m.group(5))}
        elif line.startswith("TIME "):
            e, u, s, kb = line.split()[1:]
            tm = {"wall": float(e), "cpu": float(u) + float(s), "peak_kb": int(kb)}
    return {"rc": r.returncode, "phases": lines, "time": tm}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="1250,2500,5000,10000")
    ap.add_argument("--query", default="SELECT * WHERE { ?s ?p ?o }")
    ap.add_argument("--phases", default=",".join(PHASES))
    ap.add_argument("--bin", default=str(ROOT / "formal/lean4/.lake/build/bin/l4query-phases"))
    ap.add_argument("--cap", type=float, default=600)
    ap.add_argument("--json-out", default="")
    args = ap.parse_args()
    sizes = [int(x) for x in args.sizes.split(",")]
    phases = args.phases.split(",")
    out = []
    for n in sizes:
        p = bl.gene_slice(n)
        row = {"n": n, "bytes": p.stat().st_size, "peak_kb": {}, "cpu": {}, "ms": {}}
        for ph in phases:
            r = run(args.bin, p, args.query, ph, args.cap)
            if r["rc"] != 0 or r["time"] is None:
                print(f"n={n} phase={ph}: exit {r['rc']}", file=sys.stderr)
                continue
            row["peak_kb"][ph] = r["time"]["peak_kb"]
            row["cpu"][ph] = r["time"]["cpu"]
            if ph == "solutions" and "solutions" in r["phases"] and "index" in r["phases"]:
                row["solutions_ms"] = r["phases"]["solutions"]["ms"] - r["phases"]["index"]["ms"]
            if ph == phases[-1]:
                row["ms"] = {k: v["ms"] for k, v in r["phases"].items()}
                row["values"] = {k: v["value"] for k, v in r["phases"].items()}
        out.append(row)
        print(json.dumps(row), file=sys.stderr, flush=True)
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(out, indent=1) + "\n")

    # Phase time = end of phase minus end of the phase before, in the run that
    # stopped after the last phase. `solutions` is not run there (a process
    # that goes on to `eval` computes the solutions inside `eval`), so its
    # time is taken from the process that stopped after it: end of
    # `solutions` minus end of `index` in that process.
    def phase_ms(row, ph):
        ms = row["ms"]
        order = ["start"] + [x for x in phases if x in ms]
        if ph == "solutions":
            return row.get("solutions_ms")
        if ph not in ms:
            return None
        i = order.index(ph)
        return ms[ph] - ms[order[i - 1]]

    shown = [ph for ph in phases]
    print("| n | bytes | " + " | ".join(shown) + " | whole (CPU s) |")
    print("|---:|---:|" + "---:|" * len(shown) + "---:|")
    for row in out:
        cells = []
        for ph in shown:
            v = phase_ms(row, ph)
            cells.append("-" if v is None else f"{v:.0f}")
        whole = row["cpu"].get(phases[-1])
        print(f"| {row['n']} | {row['bytes']} | " + " | ".join(cells) +
              f" | {'-' if whole is None else f'{whole:.2f}'} |")
    print()
    print("growth per doubling (phase time at 2n over time at n):")
    for ph in shown:
        gs = []
        for a, b in zip(out, out[1:]):
            x, y = phase_ms(a, ph), phase_ms(b, ph)
            gs.append("-" if not x or y is None or x < 5 else f"{y / x:.1f}")
        print(f"  {ph}: {' '.join(gs)}")
    print()
    print("| n | bytes | " + " | ".join(f"peak MB after {ph}" for ph in shown) + " |")
    print("|---:|---:|" + "---:|" * len(shown))
    for row in out:
        cells = [f"{row['peak_kb'][ph] / 1024:.1f}" if ph in row["peak_kb"] else "-"
                 for ph in shown]
        print(f"| {row['n']} | {row['bytes']} | " + " | ".join(cells) + " |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
