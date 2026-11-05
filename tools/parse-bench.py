#!/usr/bin/env python3
"""Measure the parse stack with l4parse-bench (formal/lean4/Harness/ParseBench.lean).

    tools/parse-bench.py --bin BIN --dir SCRATCH table       sizes 1 KB, 100 KB, 1 MB, 2 MB
    tools/parse-bench.py --bin BIN --dir SCRATCH stress      stress shapes, size doubled
    tools/parse-bench.py --bin BIN --dir SCRATCH stack       smallest stack that each shape needs
    tools/parse-bench.py --bin BIN --query-bin QBIN --dir SCRATCH query   basic SPARQL, net of `nt`

The main metrics are instructions retired and maximum resident set size from
`/usr/bin/time -l` (macOS); `/usr/bin/time -v` on Linux gives RSS only, so this
tool needs macOS for instructions. Every figure is net of the `null` stage on
the same file (process start, file read, UTF-8 check). The method and the
results: docs/20261105-parse-stack-perf.md.
"""
import argparse, json, math, os, re, subprocess, sys

TIMEOUT = 120
REAL = [("html", "html-tok"), ("html", "html-tree"), ("html", "html-dom"),
        ("xml", "xml"), ("xml", "xml-ns"), ("ttl", "ttl"), ("nt", "nt"), ("nt", "nt-text")]
STRESS = [
    ("html-deep", "html-tree"), ("html-wide", "html-tree"), ("html-list", "html-tree"),
    ("html-table", "html-tree"), ("html-fmt", "html-tree"), ("html-misnest", "html-tree"),
    ("html-text", "html-tree"), ("html-comment", "html-tree"), ("html-script", "html-tree"),
    ("html-attr", "html-tree"), ("html-attrs", "html-tree"), ("html-ents", "html-tree"),
    ("xml-deep", "xml"), ("xml-deep", "xml-ns"), ("xml-wide", "xml"), ("xml-wide", "xml-ns"),
    ("xml-text", "xml"), ("xml-attr", "xml"), ("xml-attrs", "xml"), ("xml-attrs", "xml-ns"),
    ("xml-ents", "xml"), ("xml-nsdecls", "xml-ns"),
    ("ttl-deep", "ttl"), ("ttl-coll-deep", "ttl"), ("ttl-lit", "ttl"), ("nt-lit", "nt"),
    ("ttl-objs", "ttl"), ("ttl-pols", "ttl"), ("ttl-coll", "ttl"), ("ttl-prefixes", "ttl"),
    ("ttl-bnodes", "ttl"),
]


def gen(a, shape, size):
    path = os.path.join(a.dir, f"{shape}.{size}")
    if not os.path.exists(path):
        subprocess.run([a.bin, "gen", shape, str(size), path], check=True)
    return path


def measure(a, stage, path, stack_kb=None):
    """One run: a dict of instructions, rss, allocs, items; or a failure string."""
    env = dict(os.environ)
    if stack_kb:
        # `lean_run_main` runs `main` on a new thread of this size; `ulimit -s` has no effect
        # (skills/danbri-function-precrime-checkers/SKILL.md).
        env["LEAN_STACK_SIZE_KB"] = str(stack_kb)
    try:
        p = subprocess.run(["/usr/bin/time", "-l", a.bin, "run", stage, path], capture_output=True,
                           text=True, timeout=a.timeout, env=env)
    except subprocess.TimeoutExpired:
        return {"fail": f"timeout {a.timeout}s"}
    m = re.search(r"allocs=(\d+)", p.stdout)
    if not m:
        return {"fail": f"exit {p.returncode}"}
    return {
        "instr": int(re.search(r"(\d+)\s+instructions retired", p.stderr).group(1)),
        "rss": int(re.search(r"(\d+)\s+maximum resident", p.stderr).group(1)),
        "allocs": int(m.group(1)),
        "items": int(re.search(r"items=(\d+)", p.stdout).group(1)),
        "bytes": int(re.search(r"bytes=(\d+)", p.stdout).group(1)),
    }


def best(a, stage, path):
    """The smallest instruction count and RSS of `a.runs` runs."""
    rs = [measure(a, stage, path) for _ in range(a.runs)]
    if any("fail" in r for r in rs):
        return next(r for r in rs if "fail" in r)
    r = dict(rs[0])
    r["instr"] = min(x["instr"] for x in rs)
    r["rss"] = min(x["rss"] for x in rs)
    return r


def net(a, shape, stage, size):
    path = gen(a, shape, size)
    base = best(a, "null", path)
    r = best(a, stage, path)
    if "fail" in r:
        return r
    r["instr"] -= base["instr"]
    r["rss"] -= base["rss"]
    return r


def row(a, shape, stage, sizes):
    rs = {s: net(a, shape, stage, s) for s in sizes}
    out = {"shape": shape, "stage": stage, "runs": rs}
    hi, lo = sizes[-1], sizes[-2]
    if "fail" not in rs[hi] and "fail" not in rs[lo]:
        ratio = (rs[hi]["instr"] / rs[hi]["bytes"]) / (rs[lo]["instr"] / rs[lo]["bytes"])
        out["growth"] = ratio
        out["exponent"] = 1 + math.log2(ratio) * math.log(2) / math.log(rs[hi]["bytes"] / rs[lo]["bytes"])
    return out


def show(r):
    for s, x in r["runs"].items():
        if "fail" in x:
            print(f'{r["shape"]:14} {r["stage"]:10} {s:>8} FAIL {x["fail"]}')
        else:
            b = x["bytes"]
            print(f'{r["shape"]:14} {r["stage"]:10} {b:>8} instr/B {x["instr"] / b:9.0f} '
                  f'allocs/B {x["allocs"] / b:7.2f} rss/B {x["rss"] / b:7.1f} items {x["items"]}')
    if "exponent" in r:
        print(f'{"":25} cost exponent over the last doubling: {r["exponent"]:.2f}')
    sys.stdout.flush()


def min_stack(a, stage, path):
    """Smallest stack in KB, to 1/16, with which the run ends well; None if over the top."""
    top = a.max_stack
    if "fail" in measure(a, stage, path, top):
        return None
    lo, hi = 8, top
    while hi - lo > max(8, hi // 16):
        mid = (lo + hi) // 2
        if "fail" in measure(a, stage, path, mid):
            lo = mid
        else:
            hi = mid
    return hi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True)
    ap.add_argument("--dir", required=True)
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=TIMEOUT)
    ap.add_argument("--max-stack", type=int, default=262144)
    ap.add_argument("--json")
    ap.add_argument("--only", help="regular expression over SHAPE/STAGE")
    ap.add_argument("--query-bin")
    ap.add_argument("what", choices=["table", "stress", "stack", "query"])
    a = ap.parse_args()
    os.makedirs(a.dir, exist_ok=True)
    sel = lambda xs: [x for x in xs if not a.only or re.search(a.only, "/".join(x))]
    out = []
    if a.what == "table":
        for shape, stage in sel(REAL):
            r = row(a, shape, stage, [1000, 100000, 1000000, 2000000])
            out.append(r)
            show(r)
    elif a.what == "stress":
        for shape, stage in sel(STRESS):
            r = row(a, shape, stage, [100000, 200000, 400000])
            out.append(r)
            show(r)
    elif a.what == "query":
        gen_bin, a.bin = a.bin, a.query_bin
        for stage in ("sparql-point", "sparql-star"):
            r = {"shape": "nt", "stage": stage, "runs": {}}
            for size in (1000, 100000, 1000000, 2000000):
                a.bin = gen_bin
                path = gen(a, "nt", size)
                a.bin = a.query_bin
                base, x = best(a, "nt", path), best(a, stage, path)
                if "fail" not in x:
                    x["instr"] -= base["instr"]
                    x["rss"] -= base["rss"]
                    x["allocs"] -= base["allocs"]
                r["runs"][size] = x
            lo, hi = r["runs"][1000000], r["runs"][2000000]
            if "fail" not in lo and "fail" not in hi:
                r["exponent"] = 1 + math.log2((hi["instr"] / hi["bytes"]) / (lo["instr"] / lo["bytes"])) * math.log(2) / math.log(hi["bytes"] / lo["bytes"])
            out.append(r)
            show(r)
    else:
        for shape, stage in sel(REAL + STRESS):
            kb = {s: min_stack(a, stage, gen(a, shape, s)) for s in (25000, 50000, 100000)}
            out.append({"shape": shape, "stage": stage, "stack_kb": kb})
            print(f"{shape:14} {stage:10} smallest stack KB at 25k/50k/100k: {list(kb.values())}")
            sys.stdout.flush()
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
