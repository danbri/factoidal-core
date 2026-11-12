#!/usr/bin/env python3
"""wpt-full.py: the whole-WPT result of a `wpt-score.py run` over every name Chrome runs.

No sampling: every wpt.fyi name with at least one Chrome subtest is run, so the share is
measured, not estimated. Passed subtests of a name are capped at Chrome's count for that
name, as wpt-score.py does; the denominator is Chrome's subtests on wpt.fyi at the commit.

  python3 tests/browser-wpt/wpt-full.py --chrome chrome.json --results RUN_DIR \
    --previous tests/browser-wpt/wpt-score-20261109.json --notes notes.json --out OUT.json

The output keeps, per top-level directory and per stratum (wpt-score.py's strata), the
names, Chrome's subtests, our passed (capped) and reported subtests, and the page
outcomes (OK, ERROR, TIMEOUT, STALL, CRASH, SKIP); and each name that passed at least one
subtest as [passed, reported, chrome]. Names that passed nothing are counted, not listed.
"""
import argparse, json, os, sys, importlib.util
from collections import defaultdict, Counter

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("wptscore", os.path.join(HERE, "wpt-score.py"))
ws = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ws)


def top(name):
    return name.split("?")[0].split("/")[1]


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--chrome", required=True)
    p.add_argument("--results", nargs="+", required=True)
    p.add_argument("--previous", help="a wpt-score.py report to compare with, stratum by stratum")
    p.add_argument("--notes", help="a JSON file of notes kept in the report")
    p.add_argument("--denominator", type=int, default=2267658)
    p.add_argument("--wpt-commit", default="fea36e49ddda8a206a5d3489ac377c8b9f406af9")
    p.add_argument("--out", required=True)
    a = p.parse_args()
    chrome = ws.load_chrome(a.chrome)
    want = {n for n, v in chrome.items() if v["c"][1] > 0}
    res = ws.read_results(a.results)
    zero = lambda: {"names": 0, "run": 0, "chrome": 0, "passed": 0, "reported": 0, "outcomes": Counter()}
    dirs, strata, variants = defaultdict(zero), defaultdict(zero), defaultdict(zero)
    passing, missing = {}, []
    total = zero()
    rawPassed = 0
    for name in sorted(want):
        c = res.get(name)
        ch = chrome[name]["c"][1]
        rows = [total, dirs[top(name)], strata[ws.stratum(name)], variants[ws.variant(name) or "window"]]
        for r in rows:
            r["names"] += 1
            r["chrome"] += ch
        if c is None:
            missing.append(name)
            continue
        capped, raw = ws.passed_of(c, ch)
        rawPassed += raw
        rep = len(c.get("subtests", []))
        h = c.get("harness", "?")
        if h == "SKIP" and c.get("message", "").startswith("not supported by engine"):
            h = "SKIP engine"
        elif h == "SKIP":
            h = "SKIP other"
        for r in rows:
            r["run"] += 1
            r["passed"] += capped
            r["reported"] += rep
            r["outcomes"][h] += 1
        if capped:
            passing[name] = [capped, rep, ch]
    fix = lambda d: {k: {**v, "outcomes": dict(sorted(v["outcomes"].items())),
                         "share": round(v["passed"] / v["chrome"], 6) if v["chrome"] else 0} for k, v in sorted(d.items())}
    report = {
        "format": "factoidal-wpt-full-v1",
        "wptCommit": a.wpt_commit,
        "denominator": {"subtests": a.denominator, "browser": "chrome", "source": "wpt.fyi summary_v2 at the WPT commit"},
        "totals": {"namesInChrome": total["names"], "namesRun": total["run"], "namesMissing": len(missing),
                   "passed": total["passed"], "passedUncapped": rawPassed, "reported": total["reported"],
                   "share": total["passed"] / a.denominator, "outcomes": dict(sorted(total["outcomes"].items()))},
        "variants": fix(variants),
        "directories": fix(dirs),
        "strata": fix(strata),
    }
    if a.previous:
        prev = json.load(open(a.previous))
        cmp = defaultdict(lambda: {"previousMeasured": 0, "previousEstimate": 0})
        for s, v in prev["strata"].items():
            t = s.split("/")[0].split(" ")[0]
            cmp[t]["previousMeasured"] += v.get("measuredPassed", 0)
            cmp[t]["previousEstimate"] += v.get("extrapolatedPassed", 0)
        report["previous"] = {"file": os.path.basename(a.previous), "measuredAt": prev.get("measuredAt"),
                              "engine": prev.get("engine"), "wptCommit": prev.get("wptCommit"),
                              "totals": prev.get("totals"), "byDirectory": dict(sorted(cmp.items()))}
    if a.notes:
        report["notes"] = json.load(open(a.notes))
    report["missing"] = missing
    head = json.dumps(report, indent=1)[:-2]
    lines = [f" {json.dumps(n)}: {json.dumps(v, separators=(',', ':'))}" for n, v in sorted(passing.items())]
    with open(a.out, "w") as f:
        f.write(head + ',\n "passing": {\n' + ",\n".join(lines) + "\n }\n}\n")
    t = report["totals"]
    print(f"{t['passed']} of {a.denominator} ({100 * t['share']:.2f}%); {t['namesRun']}/{t['namesInChrome']} names run; "
          f"{t['reported']} subtests reported; outcomes {t['outcomes']}", file=sys.stderr)


if __name__ == "__main__":
    main()
