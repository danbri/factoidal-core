#!/usr/bin/env python3
"""tools/qlvr/bench/compare.py — measure several `l4qlvr` binaries as
interleaved rounds (https://github.com/danbri/factoidal/issues/797; record:
docs/designissues/2026-10-12-lean-to-c-performance.md).

    python3 -I tools/qlvr/bench/compare.py ROUNDS INDEXDIR KERNELFILE NAME=BIN [NAME=BIN ...]

Each round runs every binary once, in order (A B C, A B C, ...), so a change
of machine load acts on all binaries of a round alike. Per binary and round:
the q07 kernel (`kernel FILE 10`, median microseconds of each Lean
implementation), `zstd-diff` (Lean decoder MB/s) and the warm execution
median of q07, q10 and q16 (`query --repeat 10`). The first binary is the
baseline: the script prints, per measure, the median over rounds of each
binary and the median over rounds of the ratio binary/baseline of the same
round, and the 1-minute load average before each round.
"""
import os
import re
import statistics
import subprocess
import sys

QUERIES = ["q07-join-three", "q10-orderby-limit-double", "q16-strstarts"]
HERE = os.path.dirname(os.path.abspath(__file__))
QDIR = os.path.join(HERE, "..", "..", "..", "tests", "qlvr", "queries")


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if p.returncode != 0:
        raise SystemExit(f"compare: {' '.join(cmd)} exited {p.returncode}: {p.stderr[-400:]}")
    return p.stdout + p.stderr


def measure(binary, index, kfile):
    out = {}
    for m in re.finditer(r"kernel lean-([\w-]+):.*?us median (\d+)", run([binary, "kernel", kfile, "10"])):
        out["kernel " + m.group(1) + " ms"] = int(m.group(2)) / 1000
    m = re.search(r"Lean (\d+) ms \((\d+) MB/s", run([binary, "zstd-diff", index]))
    out["zstd MB/s"] = int(m.group(2))
    for q in QUERIES:
        t = run([binary, "query", index, "--file", os.path.join(QDIR, q + ".rq"), "--repeat", "10"])
        m = re.search(r"execution us min \d+ median (\d+)", t)
        out[q[:3] + " warm ms"] = int(m.group(1)) / 1000
    return out


def main():
    if len(sys.argv) < 5:
        print(__doc__)
        return 2
    rounds, index, kfile = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    bins = [a.split("=", 1) for a in sys.argv[4:]]
    data = {n: [] for n, _ in bins}
    loads = []
    for r in range(rounds):
        loads.append(os.getloadavg()[0])
        for n, b in bins:
            data[n].append(measure(b, index, kfile))
        print(f"round {r + 1}: load {loads[-1]:.2f}", file=sys.stderr)
    base = bins[0][0]
    keys = list(data[base][0].keys())
    print(f"rounds {rounds}; 1-minute load average before each round: {', '.join(f'{x:.2f}' for x in loads)}")
    print("| measure | " + " | ".join(n for n, _ in bins) + " |")
    print("| --- |" + " ---: |" * len(bins))
    for k in keys:
        cells = []
        for n, _ in bins:
            vals = [d[k] for d in data[n]]
            med = statistics.median(vals)
            if n == base:
                cells.append(f"{med:.1f}")
            else:
                ratio = statistics.median(d[k] / b[k] for d, b in zip(data[n], data[base]) if b[k])
                cells.append(f"{med:.1f} ({ratio:.2f})")
        print(f"| {k} | " + " | ".join(cells) + " |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
