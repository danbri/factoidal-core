#!/usr/bin/env python3
"""tools/qlvr/bench/kernel-targets.py — the q07 kernel on several targets, as
interleaved rounds (https://github.com/danbri/factoidal/issues/797; record:
docs/designissues/2026-10-12-lean-to-c-performance.md, "The support library").

    python3 -I tools/qlvr/bench/kernel-targets.py ROUNDS ITERS KERNELFILE TARGET=PROGRAM [...]

PROGRAM is a native executable or a `.js` file (run with node). Each one is
`l4qlvr-kernel` (Lean; prints `kernel lean-NAME: ... us median N`) or the C
reference tools/qlvr/bench/kernel.c (prints `kernel c-O2: ... us median N`),
called as `PROGRAM KERNELFILE ITERS`. Each round runs every program once, in
the order given, and records the 1-minute load average before the round.

Output: per target and implementation, the median over rounds of the
per-run median (ms), and the median over rounds of the ratio to `c-O2` of the
SAME target and round (the target is the part of the name before the first
`-`, so `native-lean` and `native-c` compare with each other). Every
implementation must print the same checksum, or the script exits 1.
"""
import os
import re
import statistics
import subprocess
import sys

LINE = re.compile(r"kernel ([\w-]+): .*?checksum (\d+); us median (\d+)")


def run(prog, kfile, iters):
    cmd = (["node", prog] if prog.endswith(".js") else [prog]) + [kfile, str(iters)]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=1200)
    if p.returncode != 0:
        raise SystemExit(f"kernel-targets: {' '.join(cmd)} exited {p.returncode}: {p.stderr[-400:]}")
    return [(m.group(1), int(m.group(2)), int(m.group(3))) for m in LINE.finditer(p.stdout)]


def main():
    if len(sys.argv) < 5:
        print(__doc__)
        return 2
    rounds, iters, kfile = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    progs = [a.split("=", 1) for a in sys.argv[4:]]
    data = {}          # (target, impl) -> [ms per round]
    sums = set()
    loads = []
    for r in range(rounds):
        loads.append(os.getloadavg()[0])
        for target, prog in progs:
            for impl, cs, us in run(prog, kfile, iters):
                sums.add(cs)
                data.setdefault((target.split("-")[0], impl), []).append(us / 1000)
        print(f"round {r + 1}: load {loads[-1]:.2f}", file=sys.stderr)
    print(f"rounds {rounds}, {iters} runs per implementation per round; "
          f"1-minute load before each round: {', '.join(f'{x:.2f}' for x in loads)}")
    print("| target | implementation | median ms | times C (median of per-round ratios) |")
    print("| --- | --- | ---: | ---: |")
    for (tgt, impl), xs in sorted(data.items()):
        base = data.get((tgt, "c-O2"))
        ratio = (f"{statistics.median([a / b for a, b in zip(xs, base)]):.2f}"
                 if base and len(base) == len(xs) else "")
        print(f"| {tgt} | {impl} | {statistics.median(xs):.1f} | {ratio} |")
    if len(sums) != 1:
        print(f"kernel-targets: checksums differ: {sorted(sums)}")
        return 1
    print(f"all implementations on all targets: checksum {sums.pop()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
