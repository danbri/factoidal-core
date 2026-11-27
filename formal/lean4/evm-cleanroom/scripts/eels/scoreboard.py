#!/usr/bin/env python3
"""EELS state-test scoreboard: every case of the chosen forks through Lean.

The host only moves bytes. It lists fixture files, counts the cases each
file contains (so a case Lean never reports is visible as not-executed),
starts `evm-state-test` processes on shards of the file list, and tallies
the JSON lines they print. Every verdict (pass / fail / unsupported) and
its reason comes from the Lean executable.

    python3 -I scoreboard.py --fixtures DIR/state_tests --bin evm-state-test \
        --forks Cancun,Prague --jobs 4 --out OUTDIR [--ratchet baseline.json]

Outputs OUTDIR/scoreboard.json, OUTDIR/scoreboard.md and OUTDIR/cases.jsonl.
Exit status 1 when the ratchet is given and a fork's pass count fell below
the baseline or a case outside the baseline's known-fail list fails.
"""
import argparse
import collections
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import threading
import time

KECCAK = "--dangerously-enable-unverified-keccak"
SECP = "--dangerously-enable-unverified-secp256k1"


def fork_dir(fork):
    return "for_" + fork.lower()


def expected_cases(path, fork):
    """(id, fork, index) of every post entry in one fixture file."""
    try:
        with open(path, "rb") as fh:
            data = json.load(fh)
    except Exception as exc:  # reported, never skipped
        return None, "unreadable:" + type(exc).__name__
    out = []
    for test_id, test in data.items():
        for post_fork, entries in (test.get("post") or {}).items():
            for i, _ in enumerate(entries):
                out.append((test_id, post_fork, i))
    return out, None


def eip_dir(rel):
    parts = rel.split(os.sep)
    # for_<fork>/<introducing fork>/<eip or suite dir>/.../file.json
    return "/".join(parts[1:3]) if len(parts) >= 4 else "/".join(parts[1:-1])


def run_shard(binary, fork, files, out_path, timeout, log):
    """One Lean process per fixture file, each with a wall-clock limit.

    Lines Lean printed before a limit is reached are kept; the remaining
    cases of that file are counted as not-executed (local-time-limit)."""
    start = time.monotonic()
    timed_out, failed, err = [], [], ""
    with open(out_path, "w") as out:
        for f in files:
            try:
                proc = subprocess.run([binary, KECCAK, SECP, "--forks", fork, f],
                                      stdout=out, stderr=subprocess.PIPE, timeout=timeout)
                if proc.returncode != 0:
                    failed.append(f)
                    err = proc.stderr.decode("utf-8", "replace")[-500:]
            except subprocess.TimeoutExpired:
                timed_out.append(f)
            out.flush()
    log.append({"fork": fork, "files": len(files), "timedOut": timed_out, "nonzeroExit": failed,
                "seconds": round(time.monotonic() - start, 3), "stderr": err})


def percentile(sorted_vals, p):
    if not sorted_vals:
        return 0
    k = min(len(sorted_vals) - 1, max(0, int(round(p / 100.0 * (len(sorted_vals) - 1)))))
    return sorted_vals[k]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fixtures", required=True, help="the state_tests directory")
    ap.add_argument("--bin", required=True)
    ap.add_argument("--forks", default="Cancun,Prague")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 2)
    ap.add_argument("--out", required=True)
    ap.add_argument("--timeout", type=int, default=90, help="seconds per fixture file")
    ap.add_argument("--limit", type=int, default=0, help="first N files per fork (0 = all)")
    ap.add_argument("--ratchet", help="baseline JSON; fail when passes fall or new fails appear")
    ap.add_argument("--source", default="", help="fixture provenance line for the report")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    wall0 = time.monotonic()

    forks = [f for f in args.forks.split(",") if f]
    expected = {}        # (file, id, fork, index) -> eip dir
    file_problems = []
    shards = []          # (fork, [files])
    for fork in forks:
        root = os.path.join(args.fixtures, fork_dir(fork))
        files = []
        for dirpath, _, names in os.walk(root):
            for n in names:
                if n.endswith(".json"):
                    files.append(os.path.join(dirpath, n))
        files.sort()
        if args.limit:
            files = files[: args.limit]
        for f in files:
            rel = os.path.relpath(f, args.fixtures)
            cases, problem = expected_cases(f, fork)
            if problem:
                file_problems.append({"file": rel, "reason": problem})
                continue
            for (tid, pf, i) in cases:
                expected[(f, tid, pf, i)] = eip_dir(rel)
        # Balance shards by file size.
        per = [[] for _ in range(max(1, args.jobs))]
        load = [0] * len(per)
        for f in sorted(files, key=lambda p: -os.path.getsize(p)):
            k = load.index(min(load))
            per[k].append(f)
            load[k] += os.path.getsize(f)
        shards += [(fork, s) for s in per if s]

    log = []
    threads = []
    outs = []
    sem = threading.Semaphore(max(1, args.jobs))

    def worker(fork, files, path):
        with sem:
            run_shard(args.bin, fork, files, path, args.timeout, log)

    for n, (fork, files) in enumerate(shards):
        path = os.path.join(args.out, "shard-%03d.jsonl" % n)
        outs.append(path)
        t = threading.Thread(target=worker, args=(fork, files, path))
        t.start()
        threads.append(t)
    for t in threads:
        t.join()

    seen = {}
    host_lines = []
    for path in outs:
        with open(path) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    x = json.loads(line)
                except ValueError:
                    host_lines.append(line[:200])
                    continue
                if x.get("id") == "*":
                    file_problems.append({"file": os.path.relpath(x["file"], args.fixtures),
                                          "reason": x.get("reason")})
                    continue
                seen[(x["file"], x["id"], x["fork"], x["index"])] = x
        os.unlink(path)

    timed_out_files = {f for entry in log for f in entry.get("timedOut", [])}
    counts = collections.OrderedDict()
    by_eip = collections.defaultdict(lambda: collections.Counter())
    reasons = collections.defaultdict(collections.Counter)
    fails = collections.defaultdict(list)
    nanos = collections.defaultdict(list)
    with open(os.path.join(args.out, "cases.jsonl"), "w") as cases_out:
        for key in sorted(expected):
            f, tid, pf, i = key
            x = seen.get(key)
            if x is None:
                why = "local-time-limit" if f in timed_out_files else "no-lean-output"
                x = {"file": f, "id": tid, "fork": pf, "index": i,
                     "verdict": "not-executed", "reason": why}
            v = x["verdict"]
            c = counts.setdefault(pf, collections.Counter())
            c[v] += 1
            by_eip[(pf, expected[key])][v] += 1
            if v in ("unsupported", "not-executed", "fail"):
                reasons[(pf, v)][x.get("reason")] += 1
            if v == "fail":
                fails[pf].append({"id": tid, "index": i, "reason": x.get("reason"),
                                  "file": os.path.relpath(f, args.fixtures)})
            if "nanos" in x and v != "not-executed":
                nanos[pf].append(x["nanos"])
            x = dict(x, file=os.path.relpath(f, args.fixtures))
            cases_out.write(json.dumps(x, sort_keys=True) + "\n")
    extra = [k for k in seen if k not in expected]

    def timing(vals):
        s = sorted(vals)
        ms = lambda n: round(n / 1e6, 3)
        return {"cases": len(s), "p50ms": ms(percentile(s, 50)), "p95ms": ms(percentile(s, 95)),
                "p99ms": ms(percentile(s, 99)), "maxms": ms(s[-1] if s else 0),
                "totalSeconds": round(sum(s) / 1e9, 3)}

    report = {
        "schemaVersion": 1,
        "fixtures": args.source,
        "forks": forks,
        "wallSeconds": round(time.monotonic() - wall0, 3),
        "jobs": args.jobs,
        "counts": {f: {k: counts.get(f, {}).get(k, 0)
                       for k in ("pass", "fail", "unsupported", "not-executed")} for f in forks},
        "timing": {f: timing(nanos[f]) for f in forks},
        "reasons": {"%s/%s" % k: dict(v.most_common()) for k, v in sorted(reasons.items())},
        "byEip": {"%s %s" % k: dict(v) for k, v in sorted(by_eip.items())},
        "fails": {f: sorted(v, key=lambda r: (r["id"], r["index"])) for f, v in fails.items()},
        "fileProblems": file_problems,
        "unexpectedLines": len(extra),
        "hostUnparsedLines": host_lines[:20],
        "shards": log,
    }
    passing = sorted("%s|%s|%d" % (k[1], k[2], k[3]) for k, x in seen.items()
                     if x.get("verdict") == "pass")
    report["passingDigest"] = hashlib.sha256("\n".join(passing).encode()).hexdigest()
    with open(os.path.join(args.out, "scoreboard.json"), "w") as fh:
        json.dump(report, fh, indent=1, sort_keys=True)
    with open(os.path.join(args.out, "scoreboard.md"), "w") as fh:
        fh.write(markdown(report))

    status = 0
    if args.ratchet:
        with open(args.ratchet) as fh:
            base = json.load(fh)
        problems = []
        for f, c in base.get("counts", {}).items():
            if f in report["counts"] and report["counts"][f]["pass"] < c.get("pass", 0):
                problems.append("%s pass count fell: %d < %d" % (f, report["counts"][f]["pass"], c["pass"]))
        known = {(r["id"], r["index"]) for v in base.get("fails", {}).values() for r in v}
        for f, v in report["fails"].items():
            for r in v:
                if (r["id"], r["index"]) not in known:
                    problems.append("new fail %s [%d]: %s" % (r["id"], r["index"], r["reason"]))
        report["ratchet"] = {"baseline": args.ratchet, "problems": problems}
        with open(os.path.join(args.out, "scoreboard.json"), "w") as fh:
            json.dump(report, fh, indent=1, sort_keys=True)
        for p in problems[:200]:
            print("RATCHET: " + p, file=sys.stderr)
        status = 1 if problems else 0
    print(json.dumps({"counts": report["counts"], "timing": report["timing"],
                      "wallSeconds": report["wallSeconds"],
                      "ratchet": report.get("ratchet", {}).get("problems", [])[:5]}))
    return status


def markdown(r):
    lines = ["# EELS state-test scoreboard", "",
             "Fixtures: %s" % (r["fixtures"] or "(unspecified)"), "",
             "| Fork | pass | fail | unsupported | not executed | p50 ms | p95 ms | max ms |",
             "|---|---:|---:|---:|---:|---:|---:|---:|"]
    for f in r["forks"]:
        c, t = r["counts"][f], r["timing"][f]
        lines.append("| %s | %d | %d | %d | %d | %s | %s | %s |" % (
            f, c["pass"], c["fail"], c["unsupported"], c["not-executed"], t["p50ms"], t["p95ms"], t["maxms"]))
    lines += ["", "Runner wall time: %.1f s with %d jobs." % (r["wallSeconds"], r["jobs"]), ""]
    for key, reasons in r["reasons"].items():
        lines.append("## Top reasons: %s" % key)
        lines.append("")
        for reason, n in list(reasons.items())[:25]:
            lines.append("- %d `%s`" % (n, reason))
        lines.append("")
    for f, v in r["fails"].items():
        lines.append("## Fails: %s (%d)" % (f, len(v)))
        lines.append("")
        for x in v[:100]:
            lines.append("- `%s` [%d]: %s" % (x["id"], x["index"], x["reason"]))
        lines.append("")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
