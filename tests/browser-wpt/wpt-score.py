#!/usr/bin/env python3
"""wpt-score.py: Foafnaut's score over the whole of WPT, as wpt.fyi counts it.

The score is subtests passed divided by the most subtests any browser runs on wpt.fyi
(Chrome's count, from its wpt.fyi summary_v2 file: test name -> {"s": status,
"c": [passed, total]}). Reftests and crashtests have no subtests in that file, so they
weigh 0 there; the report counts them apart.

  sample  stratify the Chrome summary and draw the test names to run
  sparse  point a blobless sparse WPT checkout at those names and the scripts they load
  run     run a list of names with testharness-run.ts (--list), at most --jobs processes,
          each one restarted past a test that makes no progress for --stall seconds
  score   join the results with Chrome's counts: measured lower bound, per-stratum
          estimates and a 95% range

Strata: each top-level WPT directory, and the second level of the big ones (BIG). In a
stratum, the KEEP largest testharness names (by Chrome's subtests) are always run; the
rest of the sample is drawn with probability proportional to Chrome's subtests, with
replacement (Hansen-Hurwitz). The estimate for that rest is its Chrome subtests times
the mean pass ratio of the draws; its variance is that total squared times the
draws' ratio variance over n. A stratum of at most N names is run whole. Worker,
ShadowRealm and module variants, which the engine does not run, count 0 and are not
drawn. Names with --full directories are all run and replace the estimate there.

See README.md ("Whole-WPT score") for how to rerun it.
"""
import argparse, json, math, os, random, re, signal, subprocess, sys, time
from collections import defaultdict

BIG = {"encoding", "css", "wasm", "html", "editing", "WebCryptoAPI", "dom", "third_party", "selection", "svg"}
NOT_RUN = re.compile(r"\.any\.(worker|sharedworker|serviceworker|worker-module|sharedworker-module|serviceworker-module|shadowrealm[a-z-]*|window-module)\.html$|\.worker\.html$|\.test262-module\.html$")
HERE = os.path.dirname(os.path.abspath(__file__))


def stratum(name):
    parts = name.split("?")[0].split("/")[1:]
    if parts[0] in BIG:
        return parts[0] + "/" + (parts[1] if len(parts) > 2 else "(root)")
    return parts[0]


def load_chrome(path):
    with open(path) as f:
        return json.load(f)


def cmd_sample(a):
    chrome = load_chrome(a.chrome)
    rng = random.Random(a.seed)
    strata = defaultdict(list)
    for name, v in chrome.items():
        strata[stratum(name)].append((name, v["c"][1]))
    plan, names = {}, []
    for s, items in sorted(strata.items()):
        runnable = sorted([(n, c) for n, c in items if c > 0 and not NOT_RUN.search(n.split("?")[0])], key=lambda x: (-x[1], x[0]))
        notrun = sum(c for n, c in items if c > 0 and NOT_RUN.search(n.split("?")[0]))
        if len(runnable) <= a.n:
            certain, draws = [n for n, _ in runnable], []
        else:
            certain = [n for n, _ in runnable[:a.keep]]
            rest = runnable[a.keep:]
            draws = rng.choices([n for n, _ in rest], weights=[c for _, c in rest], k=a.n - a.keep)
        plan[s] = {"chromeSubtests": sum(c for _, c in items), "notRunSubtests": notrun,
                   "names": len(items), "runnableNames": len(runnable), "certain": certain, "draws": draws}
        names += certain + draws
    uniq = sorted(set(names))
    with open(a.out, "w") as f:
        json.dump({"chrome": os.path.basename(a.chrome), "seed": a.seed, "n": a.n, "keep": a.keep, "strata": plan}, f, indent=1)
    with open(a.list, "w") as f:
        f.write("\n".join(uniq) + "\n")
    print(f"{len(plan)} strata, {len(uniq)} distinct names to run ({len(names)} with repeated draws)")


def cmd_run(a):
    """Run a list in --jobs parts, restarting a part past a test that stalls."""
    names = [l.strip() for l in open(a.list) if l.strip() and not l.startswith("#")]
    parts = [names[i::a.jobs] for i in range(a.jobs)]
    os.makedirs(a.dir, exist_ok=True)
    procs = []

    def done_in(jsonl):
        try:
            return {json.loads(l)["file"] for l in open(jsonl) if l.strip()}
        except FileNotFoundError:
            return set()

    def start(i):
        lst, jsonl, err = (os.path.join(a.dir, f"part{i}.{x}") for x in ("list", "jsonl", "log"))
        cmd = ["nice", "-n", "10", "deno", "run", "-A", os.path.join(HERE, "testharness-run.ts"), "--engine", "native",
               "--native-engine", a.native_engine, "--wpt-root", a.wpt_root, "--list", lst, "--jsonl", jsonl] + a.extra
        return subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=open(err, "a"), start_new_session=True)

    for i, p in enumerate(parts):
        with open(os.path.join(a.dir, f"part{i}.list"), "w") as f:
            f.write("\n".join(p) + "\n")
        procs.append([start(i), time.time(), len(done_in(os.path.join(a.dir, f"part{i}.jsonl")))])
    t0 = time.time()
    while True:
        alive = 0
        for i, slot in enumerate(procs):
            p, since, count = slot
            jsonl = os.path.join(a.dir, f"part{i}.jsonl")
            now = len(done_in(jsonl))
            if now != count:
                slot[1], slot[2] = time.time(), now
            if p.poll() is None:
                alive += 1
                if time.time() - slot[1] > a.stall:
                    # The test after the last line stalls: record it, and go on past it.
                    log = open(os.path.join(a.dir, f"part{i}.log")).read().split("\n")
                    started = [l[6:] for l in log if l.startswith("START ")]
                    stuck = started[-1] if started else None
                    os.killpg(p.pid, signal.SIGKILL)
                    p.wait()
                    if stuck and stuck not in done_in(jsonl):
                        with open(jsonl, "a") as f:
                            f.write(json.dumps({"file": stuck, "harness": "STALL", "message": f"no result in {a.stall}s of wall time", "subtests": []}) + "\n")
                    slot[0], slot[1], slot[2] = start(i), time.time(), len(done_in(jsonl))
            elif len(done_in(jsonl)) < len(parts[i]) and p.returncode != 0 and slot[2] == now and time.time() - slot[1] > 5:
                # Crashed without a line: mark the started test as a crash and resume.
                log = open(os.path.join(a.dir, f"part{i}.log")).read().split("\n")
                started = [l[6:] for l in log if l.startswith("START ")]
                stuck = started[-1] if started else None
                if stuck and stuck not in done_in(jsonl):
                    with open(jsonl, "a") as f:
                        f.write(json.dumps({"file": stuck, "harness": "CRASH", "message": f"runner exit {p.returncode}", "subtests": []}) + "\n")
                slot[0], slot[1], slot[2] = start(i), time.time(), len(done_in(jsonl))
                alive += 1
        total = sum(len(done_in(os.path.join(a.dir, f"part{i}.jsonl"))) for i in range(a.jobs))
        if alive == 0:
            break
        if time.time() - t0 > a.max_hours * 3600:
            for slot in procs:
                if slot[0].poll() is None:
                    os.killpg(slot[0].pid, signal.SIGKILL)
            print("stopped at --max-hours", file=sys.stderr)
            break
        print(f"{time.strftime('%H:%M:%S')} {total}/{len(names)} done", file=sys.stderr, flush=True)
        time.sleep(20)
    print(f"run: {time.time() - t0:.0f}s wall for {len(names)} names in {a.jobs} processes")


def read_results(dirs):
    out = {}
    for d in dirs:
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".jsonl"):
                for l in open(os.path.join(d, fn)):
                    if l.strip():
                        c = json.loads(l)
                        out["/" + c["file"]] = c
    return out


def passed_of(c, chrome_total):
    p = sum(1 for s in c.get("subtests", []) if s["status"] == "PASS")
    return min(p, chrome_total), p


def cmd_score(a):
    chrome = load_chrome(a.chrome)
    plan = json.load(open(a.sample))
    res = read_results(a.results)
    full = set(a.full or [])
    tests, strata = {}, {}
    for name, c in res.items():
        if name not in chrome:
            continue
        ct = chrome[name]["c"][1]
        p, raw = passed_of(c, ct)
        tests[name] = {"passed": p, "reported": len(c.get("subtests", [])), **({"passedUncapped": raw} if raw != p else {}),
                       "chrome": ct, "harness": c["harness"], **({"message": c["message"][:160]} if c.get("message") and c["harness"] != "OK" else {})}
    measured_total = sum(t["passed"] for t in tests.values())
    est_total, var_total = 0.0, 0.0
    by_s = defaultdict(list)
    for name, v in chrome.items():
        by_s[stratum(name)].append((name, v["c"][1]))
    for s, items in sorted(by_s.items()):
        p = plan["strata"].get(s)
        chrome_sub = sum(c for _, c in items)
        measured = sum(tests[n]["passed"] for n, _ in items if n in tests)
        runnable = [(n, c) for n, c in items if c > 0 and not NOT_RUN.search(n.split("?")[0])]
        whole = all(n in tests for n, _ in runnable)
        if whole:
            est, var, how = float(measured), 0.0, "measured whole"
        else:
            certain = set(p["certain"])
            draws = [n for n in p["draws"] if n in tests]
            cert_pass = sum(tests[n]["passed"] for n in certain if n in tests)
            rest_total = sum(c for n, c in runnable if n not in certain)
            ratios = [tests[n]["passed"] / tests[n]["chrome"] for n in draws]
            mean = sum(ratios) / len(ratios) if ratios else 0.0
            sd2 = sum((r - mean) ** 2 for r in ratios) / (len(ratios) - 1) if len(ratios) > 1 else 0.0
            est = cert_pass + rest_total * mean
            var = rest_total ** 2 * sd2 / len(ratios) if ratios else 0.0
            # Names run outside the sample (a fuller run) are measured; the estimate never falls below them.
            est = max(est, measured)
            how = f"sampled: {len(certain)} largest + {len(draws)} drawn of {len(runnable)}"
        est_total += est
        var_total += var
        strata[s] = {"chromeSubtests": chrome_sub, "notRunSubtests": p["notRunSubtests"] if p else 0,
                     "measuredPassed": measured, "extrapolatedPassed": round(est), "sd": round(math.sqrt(var)),
                     "testsRun": sum(1 for n, _ in items if n in tests), "how": how}
    sd = math.sqrt(var_total)
    denom = a.denominator
    reftests = sum(1 for v in chrome.values() if v["c"][1] == 0 and v["s"] in ("P", "F"))
    report = {
        "format": "factoidal-wpt-score-v1", "measuredAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "wptCommit": a.wpt_commit, "denominator": {"subtests": denom, "browser": "chrome", "source": "wpt.fyi summary_v2 at the WPT commit"},
        "engine": a.engine_note,
        "method": "Stratified by top-level WPT directory (second level for " + ", ".join(sorted(BIG)) + "). Per stratum: the largest testharness names "
                  "always run, the rest drawn with probability proportional to Chrome's subtests; estimate = measured + rest x mean pass ratio. "
                  "Passed subtests of a name are capped at Chrome's count. Worker, ShadowRealm and module variants are not run and count 0. "
                  "Range: 95% normal interval from per-stratum sampling variance (strata whose draws all scored 0 add no variance).",
        "notCounted": {"reftestAndCrashtestNames": reftests, "theirSubtestWeight": 0,
                       "note": "wpt.fyi's summary gives tests without subtests (reftests, crashtests, visual) 0 subtests, so they weigh 0 in this denominator"},
        "totals": {"measuredLowerBound": measured_total, "measuredShare": measured_total / denom,
                   "extrapolated": round(est_total), "extrapolatedShare": est_total / denom,
                   "range95": [round(max(measured_total, est_total - 1.96 * sd)), round(est_total + 1.96 * sd)],
                   "range95Share": [max(measured_total, est_total - 1.96 * sd) / denom, (est_total + 1.96 * sd) / denom],
                   "testsRun": len(tests), "notRunWorkerSubtests": sum(s["notRunSubtests"] for s in strata.values())},
        "strata": strata}
    if a.notes:
        report["notes"] = json.load(open(a.notes))
    # One line a test: the file stays readable and diffable at some 9,000 tests.
    head = json.dumps(report, indent=1)[:-2]
    lines = [f" {json.dumps(n)}: {json.dumps(t, separators=(',', ':'))}" for n, t in sorted(tests.items())]
    with open(a.out, "w") as f:
        f.write(head + ',\n "tests": {\n' + ",\n".join(lines) + "\n }\n}\n")
    t = report["totals"]
    print(f"measured {t['measuredLowerBound']} ({100 * t['measuredShare']:.2f}%); estimate {t['extrapolated']} ({100 * t['extrapolatedShare']:.2f}%), "
          f"95% {t['range95'][0]}-{t['range95'][1]} ({100 * t['range95Share'][0]:.2f}-{100 * t['range95Share'][1]:.2f}%) of {denom}")


def source_of(name):
    p = name.split("?")[0].lstrip("/")
    m = re.match(r"(.*)\.(any|window)\.html$", p)
    if m:
        return f"{m[1]}.{m[2]}.js"
    m = re.match(r"(.*)\.test262(\.strict)?\.html$", p)
    return f"{m[1]}.js" if m else p


def script_deps(root, path, tree):
    """The files a test file loads as scripts: <script src>, META script, Test262 includes."""
    try:
        text = open(os.path.join(root, path), encoding="utf-8", errors="replace").read()
    except FileNotFoundError:
        return set()
    refs = re.findall(r"<script[^>]*\ssrc\s*=\s*[\"']?([^\"' >]+)", text, re.I)
    refs += re.findall(r"^//\s*META:\s*script=(.*)$", text, re.M)
    out = set()
    if path.startswith("third_party/test262/test/"):
        fm = re.search(r"/\*---([\s\S]*?)---\*/", text)
        if fm:
            inc = re.search(r"^includes:\s*\[([^\]]*)\]", fm[1], re.M)
            block = re.search(r"^includes:\s*\n((?:\s+-.*\n?)*)", fm[1], re.M)
            items = inc[1].split(",") if inc else re.findall(r"^\s+-\s*(\S+)", block[1], re.M) if block else []
            out |= {"third_party/test262/harness/" + i.strip() for i in items if i.strip()}
    for r in refs:
        r = r.strip().split("?")[0].split("#")[0]
        m = re.match(r"^[a-z]+://[^/]*(/.*)$", r)
        if m:
            r = m[1]
        elif re.match(r"^[a-z]+:", r):
            continue
        q = r.lstrip("/") if r.startswith("/") else os.path.normpath(os.path.join(os.path.dirname(path), r))
        if q in tree:
            out.add(q)
    return out


def cmd_sparse(a):
    """Point a blobless sparse checkout at a list's test files and the scripts they load."""
    git = ["git", "-C", a.wpt_root]
    tree = set(subprocess.run(git + ["ls-tree", "-r", "--name-only", a.commit], capture_output=True, text=True, check=True).stdout.split("\n"))
    want = {source_of(l.strip()) for f in a.list for l in open(f) if l.strip() and not NOT_RUN.search(l.strip().split("?")[0])}
    want &= tree
    base = ["/resources/", "/common/", "/third_party/test262/harness/"]
    for _ in range(3):
        with open(os.path.join(a.wpt_root, ".git/info/sparse-checkout"), "w") as f:
            f.write("\n".join(base + ["/" + p for p in sorted(want)]) + "\n")
        subprocess.run(git + ["checkout", "-q", a.commit], check=True)
        more = set(want)
        for p in want:
            if p.endswith((".js", ".html", ".htm", ".xhtml", ".xht", ".svg")):
                more |= script_deps(a.wpt_root, p, tree)
        if more == want:
            break
        want = more
    print(f"{len(want)} files besides resources/, common/ and the Test262 harness")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("sample")
    s.add_argument("--chrome", required=True)
    s.add_argument("--seed", type=int, default=20261108)
    s.add_argument("--n", type=int, default=25)
    s.add_argument("--keep", type=int, default=5)
    s.add_argument("--out", required=True)
    s.add_argument("--list", required=True)
    r = sub.add_parser("run")
    r.add_argument("--list", required=True)
    r.add_argument("--dir", required=True)
    r.add_argument("--wpt-root", required=True)
    r.add_argument("--native-engine", required=True)
    r.add_argument("--jobs", type=int, default=3)
    r.add_argument("--stall", type=int, default=300)
    r.add_argument("--max-hours", type=float, default=6)
    r.add_argument("extra", nargs="*")
    sp = sub.add_parser("sparse")
    sp.add_argument("--wpt-root", required=True)
    sp.add_argument("--list", nargs="+", required=True)
    sp.add_argument("--commit", default="fea36e49ddda8a206a5d3489ac377c8b9f406af9")
    c = sub.add_parser("score")
    c.add_argument("--chrome", required=True)
    c.add_argument("--sample", required=True)
    c.add_argument("--results", nargs="+", required=True)
    c.add_argument("--full", nargs="*")
    c.add_argument("--denominator", type=int, default=2267658)
    c.add_argument("--wpt-commit", default="fea36e49ddda8a206a5d3489ac377c8b9f406af9")
    c.add_argument("--engine-note", default="")
    c.add_argument("--notes", help="a JSON file of notes (diagnostics, run times) to keep in the report")
    c.add_argument("--out", required=True)
    a = ap.parse_args()
    {"sample": cmd_sample, "sparse": cmd_sparse, "run": cmd_run, "score": cmd_score}[a.cmd](a)


if __name__ == "__main__":
    main()
