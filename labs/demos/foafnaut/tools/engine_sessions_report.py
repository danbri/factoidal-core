#!/usr/bin/env python3
"""The numbers of an engine_sessions_bench.py result, as short labelled lines (issue
https://github.com/danbri/factoidal-core/issues/1031; record
docs/designissues/2026-11-26-foafnaut-engine-sessions.md, section 6).

    engine_sessions_report.py RESULT.json

For each configuration: median over the runs, with the worst run in brackets. Resident memory
per extra tab is (median of `tabs` - median of `one`) / 7: `tabs` opens seven tabs on the start
page, `one` keeps the start page only."""
import json, statistics, sys

def med(rows, key):
    v = [r[key] for r in rows if isinstance(r.get(key), (int, float))]
    return (statistics.median(v), max(v), len(v)) if v else (None, None, 0)

def fmt(x):
    return "-" if x is None else (f"{x:.0f}" if abs(x) >= 10 else f"{x:.1f}")

def main():
    result = json.load(open(sys.argv[1]))
    runs = [r for r in result["runs"] if r.get("rc") == 0]
    failed = [r for r in result["runs"] if r.get("rc") != 0]
    configs = list(dict.fromkeys(r["config"] for r in result["runs"]))
    def rows(scenario, config):
        return [r for r in runs if r["scenario"] == scenario and r["config"] == config]
    lines = []
    def line(label, scenario, key, unit="ms"):
        parts = []
        for c in configs:
            m, worst, n = med(rows(scenario, c), key)
            parts.append(f"{c} {fmt(m)} ({fmt(worst)})")
        lines.append(f"{label}, {unit}, median (worst), n per config {min(med(rows(scenario, c), key)[2] for c in configs)}: " + "; ".join(parts))
    line("Tab B input latency p50, tab A loading 2.4 MB", "heavy", "inputP50Ms")
    line("Tab B input latency p95, tab A loading 2.4 MB", "heavy", "inputP95Ms")
    line("Tab B first frame, tab A loading", "heavy", "tabFirstFrameP50Ms")
    line("Main thread pump gap p95, heavy", "heavy", "pumpGapP95Ms")
    line("New tab first frame p50 (7 new tabs 1 s apart; tabs slower than 1 s not counted)", "tabs", "tabFirstFrameP50Ms")
    line("New tab first frame p95 (7 new tabs 1 s apart; tabs slower than 1 s not counted)", "tabs", "tabFirstFrameP95Ms")
    line("New tabs counted (7 new tabs 1 s apart)", "tabs", "tabs", "tabs")
    line("New tab first frame p50 (7 new tabs 3 s apart)", "tabs-spaced", "tabFirstFrameP50Ms")
    line("New tab first frame p95 (7 new tabs 3 s apart)", "tabs-spaced", "tabFirstFrameP95Ms")
    line("New tabs counted (7 new tabs 3 s apart)", "tabs-spaced", "tabs", "tabs")
    line("Engine start (no warm-up), per extra engine", "tabs", "engineStartMs")
    line("Engine resident memory at start, per extra engine", "tabs", "engineStartRssMB", "MB")
    line("Process resident memory at exit, 8 tabs", "tabs", "processRssMB", "MB")
    line("Process resident memory at exit, 1 tab", "one", "processRssMB", "MB")
    per = []
    for c in configs:
        t, _, _ = med(rows("tabs", c), "processRssMB")
        o, _, _ = med(rows("one", c), "processRssMB")
        per.append(f"{c} {fmt((t - o) / 7) if t is not None and o is not None else '-'}")
    lines.append("Resident memory per extra tab, MB, (tabs - one) / 7 of medians: " + "; ".join(per))
    line("Frame total p50, status.html resize sweep", "status", "frameP50Ms")
    line("Frame total p95, status.html resize sweep", "status", "frameP95Ms")
    line("Frame total p50, particle-rex.html 8 s", "rex", "frameP50Ms")
    line("Frame total p95, particle-rex.html 8 s", "rex", "frameP95Ms")
    line("Frames presented, particle-rex.html 8 s", "rex", "frames", "frames")
    line("Timer turns in 8 s, particle-rex.html", "rex", "timerTurns", "turns")
    line("Engine ms per timer turn p50, particle-rex.html", "rex", "timerLeanP50Ms")
    line("Call beyond the engine per timer turn p50, particle-rex.html", "rex", "timerCallP50Ms")
    line("Page canvas presents in 8 s, particle-rex.html", "rex", "canvasPresents", "presents")
    line("Page canvas present p50, particle-rex.html", "rex", "canvasP50Ms")
    line("Page canvas present p95, particle-rex.html", "rex", "canvasP95Ms")
    line("Main thread pump gap p95, particle-rex.html", "rex", "pumpGapP95Ms")
    print("\n".join(lines))
    if failed:
        print(f"Failed runs: {len(failed)}: " + ", ".join(f"{r['scenario']}/{r['config']}/{r['run']} rc {r['rc']}" for r in failed))

if __name__ == "__main__":
    main()
