#!/usr/bin/env python3
"""BubblePopJS benchmark set: run the *.js beside this file on the engines given, as
processes, and report CPU milliseconds (user + system of the child), minus the engine's own
start (empty.js), best of N runs. Ratios are against the first engine named.

  run.py [--runs N] [--only a,b] [--json F] NAME=CMD ...
  e.g. bubblepop=/path/leanjs\ run  qjs=/path/qjs  node-jitless='node --jitless shim.js'

Each CMD gets the script path as its last argument. CPU time, not wall time: the machine
this runs on is usually busy. No script uses the clock, so every run does the same work.
"""
import json, os, resource, shlex, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
ORDER = ["empty", "fib", "props", "method", "array", "string", "closure", "alloc", "json", "regexp", "mixed"]

def run_once(cmd, script):
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.monotonic()
    p = subprocess.run(cmd + [script], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    t1 = time.monotonic()
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    return cpu * 1000, (t1 - t0) * 1000, p.returncode, p.stdout.strip().split("\n")[-1:], p.stderr[:200]

def main():
    args = sys.argv[1:]
    runs = 3; only = None; jsonOut = None; engines = []
    while args:
        a = args.pop(0)
        if a == "--runs": runs = int(args.pop(0))
        elif a == "--only": only = args.pop(0).split(",")
        elif a == "--json": jsonOut = args.pop(0)
        else:
            n, c = a.split("=", 1); engines.append((n, shlex.split(c)))
    if not engines: print(__doc__); return 2
    names = [b for b in ORDER if only is None or b in only or b == "empty"]
    res = {}; expected = {}
    for ename, cmd in engines:
        res[ename] = {}
        for b in names:
            path = os.path.join(HERE, b + ".js")
            best = None
            for _ in range(runs):
                cpu, wall, rc, out, err = run_once(cmd, path)
                if rc != 0:
                    print(f"FAIL {ename} {b}: rc={rc} {err}", file=sys.stderr); best = None; break
                best = cpu if best is None or cpu < best else best
                res[ename].setdefault("_out", {})[b] = out[0] if out else ""
            res[ename][b] = best
    print("| bench | " + " | ".join(e for e, _ in engines) + " |")
    print("|---|" + "---|" * len(engines))
    first = engines[0][0]
    for b in names:
        cells = []
        for e, _ in engines:
            v = res[e].get(b)
            if v is None: cells.append("fail"); continue
            base = 0 if b == "empty" else (res[e].get("empty") or 0)
            net = max(0.0, v - base)
            res[e].setdefault("_net", {})[b] = net
            if e == first or b == "empty":
                cells.append(f"{net:.1f}" if b != "empty" else f"{v:.1f}")
            else:
                fnet = res[first]["_net"].get(b, 0)
                ratio = f" ({fnet/net:.1f}x)" if net > 0 else ""
                cells.append(f"{net:.1f}{ratio}")
        print(f"| {b} | " + " | ".join(cells) + " |")
    mismatch = [b for b in names if len({res[e]["_out"].get(b) for e, _ in engines if res[e].get(b) is not None}) > 1]
    if mismatch: print("OUTPUT DIFFERS:", mismatch, {e: {b: res[e]["_out"].get(b) for b in mismatch} for e, _ in engines})
    if jsonOut: json.dump(res, open(jsonOut, "w"), indent=1)
    return 0
sys.exit(main())
