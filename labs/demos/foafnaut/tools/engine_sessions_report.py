#!/usr/bin/env python3
"""The numbers of an engine_sessions_bench.py result, as short labelled lines (issue
https://github.com/danbri/factoidal-core/issues/1031; record
docs/designissues/2026-11-26-foafnaut-engine-sessions.md, section 6).

    engine_sessions_report.py RESULT.json [--markdown]

For each configuration: median over the runs, with the worst run in brackets (the largest value).
Resident memory per extra tab is (median of `tabs` - median of `one`) / 7: `tabs` opens seven
tabs on the start page, `one` keeps the start page only. Lines are printed only for the scenarios
in the result; the steady scenarios have their own lines. --markdown: a table per steady
scenario instead."""
import json, statistics, sys

def med(rows, key):
    v = [r[key] for r in rows if isinstance(r.get(key), (int, float))]
    return (statistics.median(v), max(v), len(v)) if v else (None, None, 0)

def fmt(x):
    if x is None:
        return "-"
    return f"{x:.0f}" if abs(x) >= 10 else f"{x:.1f}" if abs(x) >= 1 or x == 0 else f"{x:.2f}"

STEADY_TABLE = [
    ("Pages loaded in the new tabs", "pagesLoaded"),
    ("Resident memory after the loads, MB", "rssLoadedMB"),
    ("Process CPU, 10 s idle, % of one CPU", "idleCpuPct"),
    ("Idle CPU per tab not shown, %", "idleCpuPctPerHiddenTab"),
    ("Hidden tab turns in the 10 s idle", "hiddenTurnsIdle"),
    ("Lean frames after the idle window", "activeFrames"),
    ("Lean frame total p50, ms", "activeFrameP50Ms"),
    ("Lean frame total p95, ms", "activeFrameP95Ms"),
    ("Scroll present total p95, ms", "scrollFrameP95Ms"),
    ("Gestures", "gestures"),
    ("Gesture queuedToActionMs p50, ms", "gestureP50Ms"),
    ("Gesture queuedToActionMs p95 (the largest of 15), ms", "gestureP95Ms"),
    ("Process CPU, gesture and scroll window, %", "activeCpuPct"),
    ("Hidden tab turns in that window", "hiddenTurnsActive"),
    ("Engines live at most", "enginesMaxLive"),
    ("Tabs that shared an engine", "sharedTabs"),
]

def tables(result):
    """Markdown tables of the steady scenarios: median (largest) of the runs per configuration."""
    runs = [r for r in result["runs"] if r.get("rc") == 0]
    configs = list(dict.fromkeys(r["config"] for r in result["runs"]))
    for scenario in sorted({r["scenario"] for r in runs if r["scenario"].startswith("steady")}, key=lambda x: int(x[6:])):
        counts = ", ".join(f"{c} {len([r for r in runs if r['scenario'] == scenario and r['config'] == c])}" for c in configs)
        print(f"\n{scenario[6:]} tabs, median (largest) of the runs (runs: {counts}):\n")
        print("| Number | " + " | ".join(configs) + " |")
        print("|---|" + "---|" * len(configs))
        for label, key in STEADY_TABLE:
            cells = []
            for c in configs:
                m, worst, k = med([r for r in runs if r["scenario"] == scenario and r["config"] == c], key)
                cells.append("-" if m is None else f"{fmt(m)} ({fmt(worst)})")
            print(f"| {label} | " + " | ".join(cells) + " |")

def main():
    if "--markdown" in sys.argv:
        tables(json.load(open([a for a in sys.argv[1:] if a != "--markdown"][0])))
        return
    result = json.load(open(sys.argv[1]))
    runs = [r for r in result["runs"] if r.get("rc") == 0]
    failed = [r for r in result["runs"] if r.get("rc") != 0]
    configs = list(dict.fromkeys(r["config"] for r in result["runs"]))
    def rows(scenario, config):
        return [r for r in runs if r["scenario"] == scenario and r["config"] == config]
    lines = []
    present = {r["scenario"] for r in runs}
    def line(label, scenario, key, unit="ms"):
        if scenario not in present:
            return
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
    for c in configs if {"tabs", "one"} <= present else []:
        t, _, _ = med(rows("tabs", c), "processRssMB")
        o, _, _ = med(rows("one", c), "processRssMB")
        per.append(f"{c} {fmt((t - o) / 7) if t is not None and o is not None else '-'}")
    if per:
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
    # The steady scenarios (N tabs, each after its page loaded; engine_sessions_bench.py).
    for scenario in sorted((x for x in present if x.startswith("steady")), key=lambda x: int(x[6:])):
        n = scenario[6:]
        line(f"{n} tabs: pages loaded in the new tabs", scenario, "pagesLoaded", "pages")
        line(f"{n} tabs: resident memory after the loads", scenario, "rssLoadedMB", "MB")
        line(f"{n} tabs: resident memory at exit", scenario, "processRssMB", "MB")
        line(f"{n} tabs: process CPU in 10 s idle, per cent of one CPU", scenario, "idleCpuPct", "%")
        line(f"{n} tabs: idle CPU per tab not shown", scenario, "idleCpuPctPerHiddenTab", "%")
        line(f"{n} tabs: hidden tab turns in the 10 s idle", scenario, "hiddenTurnsIdle", "turns")
        line(f"{n} tabs: scroll steps presented (count)", scenario, "scrollFrames", "frames")
        line(f"{n} tabs: scroll present total p50", scenario, "scrollFrameP50Ms")
        line(f"{n} tabs: scroll present total p95", scenario, "scrollFrameP95Ms")
        line(f"{n} tabs: Lean frames after the idle window (count)", scenario, "activeFrames", "frames")
        line(f"{n} tabs: Lean frame total p50", scenario, "activeFrameP50Ms")
        line(f"{n} tabs: Lean frame total p95", scenario, "activeFrameP95Ms")
        line(f"{n} tabs: gestures (count)", scenario, "gestures", "gestures")
        line(f"{n} tabs: gesture queuedToActionMs p50", scenario, "gestureP50Ms")
        line(f"{n} tabs: gesture queuedToActionMs p95", scenario, "gestureP95Ms")
        line(f"{n} tabs: gesture queuedToActionMs max", scenario, "gestureMaxMs")
        line(f"{n} tabs: process CPU in the gesture and scroll window, per cent of one CPU", scenario, "activeCpuPct", "%")
        line(f"{n} tabs: hidden tab turns in that window", scenario, "hiddenTurnsActive", "turns")
        line(f"{n} tabs: engine ms of those turns", scenario, "hiddenLeanMsActive")
        line(f"{n} tabs: engines live at most", scenario, "enginesMaxLive", "engines")
        line(f"{n} tabs: tabs that shared an engine", scenario, "sharedTabs", "tabs")
    print("\n".join(lines))
    if failed:
        print(f"Failed runs: {len(failed)}: " + ", ".join(f"{r['scenario']}/{r['config']}/{r['run']} rc {r['rc']}" for r in failed))

if __name__ == "__main__":
    main()
