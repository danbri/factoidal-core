#!/usr/bin/env python3
"""wpt-score.py: Foafnaut's score over the whole of WPT, as wpt.fyi counts it.

The score is subtests passed divided by the most subtests any browser runs on wpt.fyi
(Chrome's count, from its wpt.fyi summary_v2 file: test name -> {"s": status,
"c": [passed, total]}). Reftests and crashtests have no subtests in that file, so they
weigh 0 there; the report counts them apart.

  sample  stratify the Chrome summary and draw the test names to run
  tree    write the part of WPT those names need (wptserve, shared files, the tests'
          directories and what they load) from GitHub's tarball of the commit
  sparse  point a blobless sparse WPT checkout at those names and the scripts they load
          (enough for `run --files`, not for wptserve)
  serve   run wptserve from that tree on 127.0.0.1 (WPT test mode; see README.md)
  run     run a list of names with testharness-run.ts (--list), at most --jobs processes,
          each one restarted past a test that makes no progress for --stall seconds;
          through one local wptserve (--wptserve) unless --files
  score   join the results with Chrome's counts: measured lower bound, per-stratum
          estimates and a 95% range

Strata: each top-level WPT directory, and the second level of the big ones (BIG). In a
stratum, the KEEP largest testharness names (by Chrome's subtests) are always run; the
rest of the sample is drawn with probability proportional to Chrome's subtests, with
replacement (Hansen-Hurwitz). The estimate for that rest is its Chrome subtests times
the mean pass ratio of the draws; its variance is that total squared times the
draws' ratio variance over n. A stratum of at most N names is run whole. With
--variants all, worker, shared worker, service worker, ShadowRealm and module variants
form strata of their own ("<stratum> [worker]"), drawn the same way; the runner runs
them when the engine has the API and otherwise records SKIP "not supported by engine"
(0). With --variants window they are not drawn and count 0. Names with --full
directories are all run and replace the estimate there.

See README.md ("Whole-WPT score") for how to rerun it.
"""
import argparse, json, math, os, random, re, signal, subprocess, sys, time
from collections import defaultdict

BIG = {"encoding", "css", "wasm", "html", "editing", "WebCryptoAPI", "dom", "third_party", "selection", "svg"}
NOT_RUN = re.compile(r"\.any\.(worker|sharedworker|serviceworker|worker-module|sharedworker-module|serviceworker-module|shadowrealm[a-z-]*|window-module)\.html$|\.worker\.html$|\.test262-module\.html$")


def variant(name):
    """The wpt.fyi variant of a name beyond a window with classic scripts (worker,
    sharedworker, serviceworker, shadowrealm, module), or None. testharness-run.ts runs
    these when the engine has the API (its probe) and otherwise records them as SKIP
    "not supported by engine", which scores 0."""
    p = name.split("?")[0]
    m = re.search(r"\.any\.([a-z-]+)\.html$", p)
    if m:
        v = m[1]
        return "module" if v == "window-module" else "shadowrealm" if v.startswith("shadowrealm") else v
    if p.endswith(".worker.html"):
        return "worker"
    if p.endswith(".test262-module.html"):
        return "module"
    return None
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
    # With --variants all, each stratum's variant names (worker, sharedworker, ...) form
    # strata of their own, "<stratum> [<variant>]", drawn after the window strata with a
    # second generator, so the window sample stays the one a window-only run draws.
    vstrata = defaultdict(list)
    if a.variants == "all":
        for name, v in chrome.items():
            k = variant(name)
            if k:
                vstrata[f"{stratum(name)} [{k}]"].append((name, v["c"][1]))
    for s, items in sorted(strata.items()) + [(k, vstrata[k]) for k in sorted(vstrata)]:
        if s.endswith("]") and not isinstance(rng, VariantRng):
            rng = VariantRng(a.seed + 1)
        variants = s.endswith("]")
        runnable = sorted([(n, c) for n, c in items if c > 0 and (variants or not NOT_RUN.search(n.split("?")[0]))], key=lambda x: (-x[1], x[0]))
        notrun = 0 if variants or a.variants == "all" else sum(c for n, c in items if c > 0 and NOT_RUN.search(n.split("?")[0]))
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
        json.dump({"chrome": os.path.basename(a.chrome), "seed": a.seed, "n": a.n, "keep": a.keep, "variants": a.variants, "strata": plan}, f, indent=1)
    with open(a.list, "w") as f:
        f.write("\n".join(uniq) + "\n")
    print(f"{len(plan)} strata, {len(uniq)} distinct names to run ({len(names)} with repeated draws)")


class VariantRng(random.Random):
    """The generator of the variant strata (seed + 1)."""


def cmd_run(a):
    """Run a list in --jobs parts, restarting a part past a test that stalls."""
    names = [l.strip() for l in open(a.list) if l.strip() and not l.startswith("#")]
    parts = [names[i::a.jobs] for i in range(a.jobs)]
    os.makedirs(a.dir, exist_ok=True)
    procs = []
    server = None
    if a.wptserve:
        # One wptserve for every runner process; each one finds it up and uses it.
        server = subprocess.Popen([sys.executable, os.path.abspath(__file__), "serve", "--wpt-root", a.wpt_root, "--state", a.dir],
                                  stdout=subprocess.DEVNULL, stderr=open(os.path.join(a.dir, "wptserve.log"), "a"))
        a.extra = ["--wptserve"] + a.extra
        import socket
        for _ in range(120):
            try:
                socket.create_connection(("127.0.0.1", 8000), timeout=1).close()
                break
            except OSError:
                time.sleep(0.5)
        else:
            server.kill()
            sys.exit("wptserve did not start (see wptserve.log in --dir)")

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
    if server:
        server.send_signal(signal.SIGTERM)
        try:
            server.wait(timeout=20)
        except subprocess.TimeoutExpired:
            server.kill()
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
                       **({"kind": c["kind"]} if c.get("kind") in ("engine", "runner") else {}),
                       "chrome": ct, "harness": c["harness"], **({"message": c["message"][:160]} if c.get("message") and c["harness"] != "OK" else {})}
    measured_total = sum(t["passed"] for t in tests.values())
    est_total, var_total = 0.0, 0.0
    by_s = defaultdict(list)
    all_variants = plan.get("variants") == "all"
    for name, v in chrome.items():
        k = variant(name) if all_variants else None
        by_s[f"{stratum(name)} [{k}]" if k else stratum(name)].append((name, v["c"][1]))
    for s, items in sorted(by_s.items()):
        p = plan["strata"].get(s)
        chrome_sub = sum(c for _, c in items)
        measured = sum(tests[n]["passed"] for n, _ in items if n in tests)
        runnable = [(n, c) for n, c in items if c > 0 and (s.endswith("]") or not NOT_RUN.search(n.split("?")[0]))]
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
        unsupported = sum(c for n, c in items if n in tests and tests[n]["harness"] == "SKIP" and tests[n].get("kind") == "engine")
        strata[s] = {"chromeSubtests": chrome_sub, "notRunSubtests": p["notRunSubtests"] if p else 0,
                     **({"engineUnsupportedMeasured": unsupported} if unsupported else {}),
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
                  "Passed subtests of a name are capped at Chrome's count. With variants=all, worker, shared worker, service worker, ShadowRealm and "
                  "module variants are strata of their own, run when the engine has the API and otherwise SKIP 'not supported by engine' (0); "
                  "with variants=window they are not drawn and count 0. "
                  "Range: 95% normal interval from per-stratum sampling variance (strata whose draws all scored 0 add no variance).",
        "notCounted": {"reftestAndCrashtestNames": reftests, "theirSubtestWeight": 0,
                       "note": "wpt.fyi's summary gives tests without subtests (reftests, crashtests, visual) 0 subtests, so they weigh 0 in this denominator"},
        "totals": {"measuredLowerBound": measured_total, "measuredShare": measured_total / denom,
                   "extrapolated": round(est_total), "extrapolatedShare": est_total / denom,
                   "range95": [round(max(measured_total, est_total - 1.96 * sd)), round(est_total + 1.96 * sd)],
                   "range95Share": [max(measured_total, est_total - 1.96 * sd) / denom, (est_total + 1.96 * sd) / denom],
                   "testsRun": len(tests), "notRunWorkerSubtests": sum(s["notRunSubtests"] for s in strata.values()),
                   "variants": plan.get("variants", "window"),
                   "engineUnsupportedNames": sum(1 for t in tests.values() if t.get("kind") == "engine"),
                   "engineUnsupportedChromeSubtests": sum(t["chrome"] for t in tests.values() if t.get("kind") == "engine"),
                   "runnerGapNames": sum(1 for t in tests.values() if t.get("kind") == "runner")},
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


SERVED_TOPS = ("tools/", "resources/", "common/", "fonts/", "images/", "interfaces/", "third_party/test262/harness/")


def served_wanted(names):
    """What wptserve needs to serve a list's tests: its own tree (tools/), the shared
    directories, each test's directory (its files, and resources/ and support/ there and
    one level up) and the test files. CSS directories keep only the tests and their
    support files (their reftest references are not loaded by testharness tests)."""
    files, prefixes = set(), set(SERVED_TOPS)
    dirs = set()
    for n in names:
        p = n.split("?")[0].lstrip("/")
        src = source_of(n)
        files.add(src)
        files.add(src + ".headers")
        if re.match(r"(.*)\.any\.[a-z-]+\.html$", p):
            files.add(re.sub(r"\.any\.[a-z-]+\.html$", ".any.js", p))
        if p.startswith("third_party/test262/"):
            continue
        d = os.path.dirname(p)
        for base in (d, os.path.dirname(d)):
            if base:
                prefixes |= {base + "/resources/", base + "/support/"}
        if not p.startswith("css/"):
            dirs.add(d)
    return files, prefixes, dirs


def page_deps(root, path, tree):
    """What a test page or script loads that the tree has: script_deps() (script src,
    META script, Test262 includes), and stylesheets, frames, images and importScripts
    by their relative or root-relative URLs."""
    out = script_deps(root, path, tree)
    try:
        text = open(os.path.join(root, path), encoding="utf-8", errors="replace").read()
    except (FileNotFoundError, IsADirectoryError):
        return out
    refs = re.findall(r"\s(?:src|href|data)\s*=\s*[\"']?([^\"' >]+)", text, re.I)
    refs += re.findall(r"importScripts\(\s*[\"']([^\"']+)[\"']", text)
    for r in refs:
        r = r.strip().split("?")[0].split("#")[0]
        if not r or "{{" in r or re.match(r"^[a-z][a-z0-9+.-]*:", r, re.I):
            continue
        q = r.lstrip("/") if r.startswith("/") else os.path.normpath(os.path.join(os.path.dirname(path), r))
        if q in tree:
            out.add(q)
    return out


def cmd_tree(a):
    """A WPT tree for wptserve without git: GitHub's tarball of the commit, streamed, with
    only the paths served_wanted() names written (no full checkout on disk), then again
    for what those pages load from elsewhere (page_deps), until nothing is missing."""
    import tarfile, urllib.request
    names = [l.strip() for f in a.list for l in open(f) if l.strip() and not l.startswith("#")]
    files, prefixes, dirs = served_wanted(names)
    url = f"https://codeload.github.com/web-platform-tests/wpt/tar.gz/{a.commit}"
    os.makedirs(a.wpt_root, exist_ok=True)
    tree, written = set(), set()

    def stream(want):
        with urllib.request.urlopen(url) as r, tarfile.open(fileobj=r, mode="r|gz") as tf:
            for m in tf:
                parts = m.name.split("/", 1)
                if len(parts) < 2 or not parts[1] or not (m.isfile() or m.issym()):
                    continue
                path = parts[1]
                tree.add(path)
                if path in written or not want(path):
                    continue
                m.name = path
                tf.extract(m, a.wpt_root, filter="data" if m.isfile() else "fully_trusted")
                written.add(path)

    stream(lambda path: "/" not in path or path in files or path.startswith(tuple(prefixes)) or os.path.dirname(path) in dirs)
    scanned = set()
    for _ in range(4):
        todo = [p for p in written if p not in scanned and p.endswith((".html", ".htm", ".xhtml", ".xht", ".svg", ".js", ".xml"))
                and not p.startswith(("tools/", "resources/"))]
        missing = set()
        for p in todo:
            scanned.add(p)
            missing |= page_deps(a.wpt_root, p, tree) - written
        if not missing:
            break
        print(f"{len(missing)} more files the pages load", file=sys.stderr)
        stream(lambda path: path in missing)
    with open(os.path.join(a.wpt_root, "PROVENANCE"), "w") as f:
        f.write(f"web-platform-tests/wpt at {a.commit} ({url}), the subset for {len(names)} names; BSD-3-Clause (LICENSE.md)\n")
    print(f"{len(written)} files under {a.wpt_root}")


def cmd_serve(a):
    """Run wptserve from a WPT tree on 127.0.0.1 with this runner's config: HTTP on
    8000-8003, HTTPS on 8443-8446 and HTTP/2 on 9000 with WPT's pregenerated test
    certificates, WebSockets on 8888/8889 (no WebTransport, no DNS server). No
    system change: the host names resolve only in the runner (wpt-hosts.ts)."""
    root = os.path.abspath(a.wpt_root)
    config = {"browser_host": "web-platform.test", "alternate_hosts": {"alt": "not-web-platform.test"},
              "server_host": "127.0.0.1", "bind_address": True, "check_subdomains": False,
              # Fixed ports (wpt-hosts.ts maps exactly these): WPT's defaults where it has them.
              "ports": {"http": [8000, 8001], "http-local": [8002], "http-public": [8003], "https": [8443, 8444],
                        "https-local": [8445], "https-public": [8446], "h2": [9000], "ws": [8888], "wss": [8889],
                        "webtransport-h3": [], "dns": []},
              "doc_root": root, "ws_doc_root": os.path.join(root, "websockets", "handlers"),
              "ssl": {"type": "pregenerated", "pregenerated": {"host_key_path": os.path.join(root, "tools/certs/web-platform.test.key"),
                                                               "host_cert_path": os.path.join(root, "tools/certs/web-platform.test.pem")}},
              "logging": {"level": "warning", "suppress_handler_traceback": True}}
    cfg = os.path.join(a.state or root, "factoidal-wptserve.json")
    with open(cfg, "w") as f:
        json.dump(config, f)
    # tools/serve's own entry point with WPT's vendored libraries (tools/localpaths.py);
    # no virtualenv and no network.
    # SIGINT and SIGTERM stop it the way wptserve stops on Ctrl-C (it shuts its server
    # processes down), also when started in the background, where SIGINT is ignored.
    code = ("import signal, sys\n"
            "def stop(*_): raise KeyboardInterrupt\n"
            "signal.signal(signal.SIGINT, stop); signal.signal(signal.SIGTERM, stop)\n"
            "sys.path.insert(0, %r); import tools.localpaths; from tools.serve import serve\n"
            "sys.exit(serve.run(config_path=%r, doc_root=%r))") % (root, cfg, root)
    # wptserve's server processes live in a process group of their own, and a stop takes
    # the whole group down, also when it comes while wptserve is still starting.
    proc = subprocess.Popen([sys.executable, "-c", code], start_new_session=True)
    stopping = []
    signal.signal(signal.SIGTERM, lambda *_: stopping.append(1))
    signal.signal(signal.SIGINT, lambda *_: stopping.append(1))
    # Poll here, not in the handler (Popen.wait in a handler deadlocks on its own lock).
    while proc.poll() is None and not stopping:
        time.sleep(0.2)
    for sig, wait in ((signal.SIGINT, 15), (signal.SIGKILL, 5)):
        try:
            os.killpg(proc.pid, sig)
        except ProcessLookupError:
            break
        deadline = time.time() + wait
        while proc.poll() is None and time.time() < deadline:
            time.sleep(0.1)
    sys.exit(0)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("sample")
    s.add_argument("--chrome", required=True)
    s.add_argument("--seed", type=int, default=20261108)
    s.add_argument("--n", type=int, default=25)
    s.add_argument("--keep", type=int, default=5)
    s.add_argument("--variants", choices=["window", "all"], default="all",
                   help="all (default): also draw worker, sharedworker, serviceworker, ShadowRealm and module variants, "
                        "as their own strata; window: the window variants only (the 2026-11-09 score's sample)")
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
    r.add_argument("--files", dest="wptserve", action="store_false",
                   help="read test files from the checkout and make wptserve's wrappers in the runner (the path before 2026-11-09); "
                        "by default every test runs through one local wptserve (testharness-run.ts --wptserve)")
    r.add_argument("extra", nargs="*")
    sp = sub.add_parser("sparse")
    sp.add_argument("--wpt-root", required=True)
    sp.add_argument("--list", nargs="+", required=True)
    sp.add_argument("--commit", default="fea36e49ddda8a206a5d3489ac377c8b9f406af9")
    t = sub.add_parser("tree")
    t.add_argument("--wpt-root", required=True)
    t.add_argument("--list", nargs="+", required=True)
    t.add_argument("--commit", default="fea36e49ddda8a206a5d3489ac377c8b9f406af9")
    sv = sub.add_parser("serve")
    sv.add_argument("--wpt-root", required=True)
    sv.add_argument("--state", help="directory for the generated config (default: the WPT root)")
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
    {"sample": cmd_sample, "sparse": cmd_sparse, "tree": cmd_tree, "serve": cmd_serve, "run": cmd_run, "score": cmd_score}[a.cmd](a)


if __name__ == "__main__":
    main()
