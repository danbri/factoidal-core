#!/usr/bin/env python3
"""Engine sessions: each tab mode of the desktop host against a base build, on one machine, in
one run (issue https://github.com/danbri/factoidal-core/issues/1031;
docs/designissues/2026-11-26-foafnaut-engine-sessions.md, section 5).

    engine_sessions_bench.py --config NAME=LAB:ENGINE[:MODE[:FLAGS]] ... [--runs N] [--scenario S ...]

FLAGS: more host flags, comma-separated, each `--flag` or `--flag=value` (for example
`--hidden-tabs=running,--engine-workers=64`).
                             [--out FILE]

A configuration is a lab directory (its run_html.ts is the host), a native engine library, and
an --engine-mode (copies, sessions or tasks; none for a host from before the option). Each
scenario runs N times for each configuration, the configurations interleaved, each run under
flock /tmp/foafnaut-timing.lock, in a window under Xvfb with Mesa software Vulkan (the Linux
rig, tools/foafnaut-linux-rig/setup.sh, must have been run for every lab directory). GPU times
are software Vulkan times: compare configurations of one run, never with a Mac.

Scenarios (the steps language of run_html.ts --steps):
  heavy   tab A navigates to a page of 20,000 table rows (2.4 MB); 300 ms later tab B opens and
          gets 21 keys 300 ms apart, each a key press (kind 5, which the host stamps for input
          latency) and its text (kind 9) into the address field, whose frame tab B's engine
          draws. Input latency (all stamped events), tab B first frame.
  tabs    seven new tabs, 1 s apart, from the start page: process resident memory at exit, engine
          start (ms and resident memory, from native-html-engine-worker). Its tab first frame
          counts only the tabs that drew before the next tab opened (run_html.ts times one shown
          tab, `tabShown`): a mode with more slow tabs has fewer counted. Use tabs-spaced for it.
  tabs-spaced  the same seven new tabs, 3 s apart, so that each tab's first frame is counted:
          tab first frame (p50, p95, the number of tabs counted).
  one     the start page and no new tab: process resident memory at exit (the base for tabs).
  status  pages/status.html, resize sweep (7 sizes, a Lean frame each): frame total p50 and p95.
  rex     pages/particle-rex.html for 8 s (its title screen animates): timer turns (count, engine
          ms per turn, call beyond the engine, wait before the next ask) and page-canvas
          presents (count, ms), frame total.
  steady5, steady20, steady50
          N tabs in steady state: from the start page, N-1 new tabs, each then sent to a demo page
          (tab 2 to particle-rex.html), one at a time; then tab 1 is shown again and the host
          marks (`mark` step: process CPU time and resident memory), stays idle 10 s, marks, gets
          3 rounds of the gestures of --gesture-sweep and then 30 scroll steps, and marks. Numbers:
          resident memory after the tabs loaded and at exit; process CPU in the idle window (per
          cent of one CPU, and per tab not shown); after the idle window, scroll frame total
          (`native-html-scroll`), Lean frame total and gesture queuedToActionMs, p50, p95 (and max),
          each with its count; the
          engines live and the tabs that share one (the cap, --engine-workers, applies to every
          mode). With the host's default, --hidden-tabs stopped, only the shown tab's page gets
          timer turns, so the pages of the other tabs run no script; with --hidden-tabs throttled
          or running (a FLAGS item) they do, and their turns are counted (hiddenTurnsIdle,
          hiddenTurnsActive, hiddenLeanMsActive). Run with --idle-checks-only (since 2026-11-26
          09:30 UTC): the other scenarios, as every sweep and --steps run, ask Lean for CPU probes
          in every frame, which an interactive frame of the window in use does not do.

Output: one JSON object, with each run's numbers and, per configuration and scenario, the
median, the worst and the coefficient of variation of each number
(skills/perceived-performance, rules 1 and 2)."""
import argparse, json, os, pathlib, statistics, subprocess, sys, tempfile, time

HERE = pathlib.Path(__file__).resolve().parent.parent

def heavy_page(path):
    rows = "".join(f"<tr><td>{i}</td><td>row {i} of a long table with some words in it</td><td>{i*7%13}</td><td>{i%97}</td></tr>\n"
                   for i in range(20000))
    path.write_text(f"<!doctype html><title>Heavy</title><table>{rows}</table>")

STEADY = (5, 20, 50)

def demo_pages():
    """The HTML demo pages that the app does not refuse, particle-rex.html first."""
    manifest = json.loads((HERE / "pages" / "manifest.json").read_text())
    pages = sorted(p["page"] for p in manifest["pages"]
                   if p["page"].endswith(".html") and not p.get("refused") and not p.get("appRefused"))
    return ["particle-rex.html"] + [p for p in pages if p not in ("particle-rex.html", "index.html")]

# One round of the gestures of --gesture-sweep (run_html.ts): a double and a triple click on text,
# select all and copy, a right click on the link and on the text. Each context menu is closed with
# Escape ([5, 53, 0]): the frame with an open menu has no link to aim at. Left out: the sweep's
# plain click (on index.html the text after the first link is a link, so the click navigates) and
# its middle click (it opens a tab).
ESCAPE = [5, 53, 0]
GESTURE_ROUND = ["atText:2:512", "atText:4:512", "hold", "atText:2:768", "atText:4:768", "hold", "a", "hold", "c", "hold",
                 "atLink:13:65536", "hold", ESCAPE, "hold", "atText:13:65536", "hold", ESCAPE, "hold"]

def steady_steps(n):
    pages = demo_pages()
    steps = []
    for i in range(1, n):
        page = pages[(i - 1) % len(pages)]
        # The next step waits for a settled frame (no load in progress): a new tab before then
        # stops the load (showTab), and that tab keeps the new tab page.
        steps += ["t", f"go:file://{HERE}/pages/{page}"]
    steps += ["1", f"tabs={n}:0", "mark"] + ["hold"] * 33 + ["mark"]
    # Gestures first, at scroll 0 (the sweep's first link must be on screen), then 30 scroll steps.
    steps += GESTURE_ROUND * 3 + ["hold"] + [[11, -120, 0]] * 30 + ["hold", "mark"]
    return steps

def scenarios(work):
    heavy = work / "heavy.html"
    if not heavy.exists():
        heavy_page(heavy)
    steps = {}
    steps["heavy"] = ["now:2:300", f"go:file://{heavy}", "t", "now:42:150"] + [[5, 0, 0], [9, 97, 0]] * 21
    steps["tabs"] = ["now:7:1000"] + ["t"] * 7
    steps["tabs-spaced"] = ["now:7:3000"] + ["t"] * 7
    for n in STEADY:
        steps[f"steady{n}"] = steady_steps(n)
    files = {}
    for name, value in steps.items():
        f = work / f"steps-{name}.json"
        f.write_text(json.dumps(value))
        files[name] = f
    return {
        "heavy": ["--html", "pages/index.html", "--steps", str(files["heavy"])],
        "tabs": ["--html", "pages/index.html", "--steps", str(files["tabs"])],
        "tabs-spaced": ["--html", "pages/index.html", "--steps", str(files["tabs-spaced"])],
        # --log-all: the log gate holds back no line (the numbers are read from the lines).
        # --idle-checks-only: a run with --steps asks Lean for CPU probes in every frame
        # (`everyFrame` in run_html.ts); a window in use asks for none in an interactive frame and
        # one probe frame after it is idle. Frame times here are those of the window in use.
        **{f"steady{n}": ["--html", "pages/index.html", "--log-all", "--idle-checks-only", "--steps", str(files[f"steady{n}"])] for n in STEADY},
        "one": ["--html", "pages/index.html", "--watch-sweep", "4"],
        "status": ["--html", "pages/status.html", "--resize-sweep"],
        "rex": ["--html", "pages/particle-rex.html", "--watch-sweep", "8"],
    }

def host_flags(text):
    """`--a=1,--b` as ["--a", "1", "--b"]."""
    out = []
    for item in filter(None, text.split(",")):
        out += item.split("=", 1)
    return out

def run_once(lab, engine, mode, args, timeout, flags=""):
    cmd = ["flock", "/tmp/foafnaut-timing.lock", "xvfb-run", "-a", "-s", "-screen 0 1280x900x24",
           "deno", "run", "--no-check", "--no-config", "--no-npm", "--node-modules-dir=none",
           "--unstable-webgpu", "--unstable-ffi", "-A", "run_html.ts",
           "--native-engine", engine, "--no-splash", "--no-state", "--perf-summary"] + \
          (["--engine-mode", mode] if mode else []) + host_flags(flags) + args
    env = dict(os.environ)
    env.setdefault("VK_ICD_FILENAMES", "/usr/share/vulkan/icd.d/lvp_icd.json")
    t0 = time.time()
    p = subprocess.run(cmd, cwd=lab, env=env, capture_output=True, text=True, timeout=timeout)
    records = []
    for line in p.stdout.splitlines():
        if line.startswith("{"):
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return p.returncode, time.time() - t0, records, p.stderr[-2000:]

def pct(values, q):
    """Nearest-rank percentile (as the host's `percentile`), or None for no values."""
    if not values:
        return None
    v = sorted(values)
    return round(v[max(0, min(len(v) - 1, -(-int(q * 1000 * len(v)) // 1000) - 1))], 1)

def steady_numbers(records, summary):
    """The numbers of a steady scenario, from its three `mark` records (see the module doc)."""
    out = {}
    marks = [r for r in records if r.get("type") == "native-html-mark"]
    if len(marks) < 3:
        return out
    m0, m1, m2 = marks[0], marks[1], marks[-1]
    n = m0.get("tabs") or 0
    out["steadyTabs"] = n
    # Pages committed in the new tabs (a history push each): N-1 when every load finished.
    out["pagesLoaded"] = len([r for r in records if r.get("type") == "native-html-history" and r.get("action") == "push" and r.get("t", 0) <= m0["t"]])
    out["rssLoadedMB"] = m0.get("rssMB")
    idle = m1["t"] - m0["t"]
    if idle > 0:
        out["idleCpuPct"] = round(100 * (m1["cpuMs"] - m0["cpuMs"]) / idle, 2)
        if n > 1:
            out["idleCpuPctPerHiddenTab"] = round(out["idleCpuPct"] / (n - 1), 3)
    after = lambda r: r.get("t", 0) > m1["t"]
    frames = [r["totalMs"] for r in records if r.get("type") == "native-html-frame" and after(r) and isinstance(r.get("totalMs"), (int, float))]
    gestures = [r["queuedToActionMs"] for r in records if r.get("type") == "native-html-gesture" and after(r)]
    inputs = [r["ms"] for r in records if r.get("type") == "native-html-input-latency" and after(r) and isinstance(r.get("ms"), (int, float))]
    scrolls = [r["totalMs"] for r in records if r.get("type") == "native-html-scroll" and after(r) and isinstance(r.get("totalMs"), (int, float))]
    out["activeFrames"], out["activeFrameP50Ms"], out["activeFrameP95Ms"] = len(frames), pct(frames, 0.5), pct(frames, 0.95)
    out["scrollFrames"], out["scrollFrameP50Ms"], out["scrollFrameP95Ms"] = len(scrolls), pct(scrolls, 0.5), pct(scrolls, 0.95)
    out["gestures"], out["gestureP50Ms"], out["gestureP95Ms"] = len(gestures), pct(gestures, 0.5), pct(gestures, 0.95)
    out["gestureMaxMs"] = max(gestures) if gestures else None
    out["activeInputs"], out["activeInputP95Ms"] = len(inputs), pct(inputs, 0.95)
    if m2["t"] > m1["t"]:
        out["activeCpuPct"] = round(100 * (m2["cpuMs"] - m1["cpuMs"]) / (m2["t"] - m1["t"]), 1)
    ew = (summary or {}).get("engineWorkers") or {}
    out["enginesLive"], out["enginesMaxLive"], out["sharedTabs"] = ew.get("live"), ew.get("maxLive"), ew.get("sharedTabs")
    # The timer turns of the tabs not shown (--hidden-tabs), in the window after the idle marks and
    # in the idle window: count and engine ms.
    hidden = [r for r in records if r.get("type") == "native-html-script" and r.get("cause") == "hidden timers"]
    idle_hidden = [r for r in hidden if m0["t"] < r.get("t", 0) <= m1["t"]]
    out["hiddenTurnsIdle"] = len(idle_hidden)
    out["hiddenTurnsActive"] = len([r for r in hidden if after(r)])
    out["hiddenLeanMsActive"] = round(sum(r.get("leanMs", 0) for r in hidden if after(r)), 1)
    ht = (summary or {}).get("hiddenTabs") or {}
    out["hiddenHeld"], out["hiddenHeldMB"], out["hiddenForced"] = ht.get("held"), ht.get("heldMB"), ht.get("forced")
    out["floods"] = len([r for r in records if r.get("type") == "native-html-log-flood"])
    return out

def numbers(scenario, records):
    """The numbers of one run."""
    out = {}
    summary = next((r for r in reversed(records) if r.get("type") == "native-html-perf-summary"), None)
    if summary:
        lat = summary.get("inputLatency") or {}
        out["inputP50Ms"], out["inputP95Ms"], out["inputMaxMs"], out["inputCount"] = lat.get("p50Ms"), lat.get("p95Ms"), lat.get("maxMs"), lat.get("count")
        fr = summary.get("frames") or {}
        out["frameP50Ms"], out["frameP95Ms"], out["frames"] = fr.get("totalMsP50"), fr.get("totalMsP95"), fr.get("presented")
        out["processRssMB"] = summary.get("processRssMB")
        tf = summary.get("tabFirstFrame") or {}
        out["tabFirstFrameP50Ms"], out["tabFirstFrameP95Ms"], out["tabFirstFrameMaxMs"], out["tabs"] = tf.get("p50Ms"), tf.get("p95Ms"), tf.get("maxMs"), tf.get("count")
        gap = summary.get("pumpGapAfterFirstFrameMs") or {}
        out["pumpGapP95Ms"], out["pumpGapMaxMs"] = gap.get("p95"), gap.get("max")
        tt = summary.get("timerTurns") or {}
        out["timerTurns"], out["timerLeanP50Ms"], out["timerLeanP95Ms"] = tt.get("count"), tt.get("leanMsP50"), tt.get("leanMsP95")
        out["timerCallP50Ms"], out["timerWaitP50Ms"], out["timerWaitP95Ms"] = tt.get("callMsP50"), tt.get("waitMsP50"), tt.get("waitMsP95")
        pc = summary.get("pageCanvasPresents") or {}
        out["canvasPresents"], out["canvasP50Ms"], out["canvasP95Ms"] = pc.get("count"), pc.get("p50Ms"), pc.get("p95Ms")
        ew = summary.get("engineWorkers") or {}
        out["engines"] = ew.get("engines") or ew.get("mode")
    if scenario.startswith("steady"):
        out.update(steady_numbers(records, summary))
    starts = [r for r in records if r.get("type") == "native-html-engine-worker" and r.get("state") == "started"]
    later = [s for s in starts if s.get("worker", 0) > 1]
    if later:
        # A spare's record includes its warm-up layout (warmMs): the start alone is ms - warmMs.
        out["engineStartMs"] = statistics.median(s["ms"] - (s.get("warmMs") or 0) for s in later)
        warm = [s["warmMs"] for s in later if s.get("warmMs") is not None]
        if warm:
            out["engineWarmMs"] = statistics.median(warm)
        out["engineStartRssMB"] = statistics.median(s["rssAfterMB"] - s["rssBeforeMB"] for s in later)
    return out

def spread(values):
    values = [v for v in values if isinstance(v, (int, float))]
    if not values:
        return None
    mean = statistics.mean(values)
    cv = statistics.pstdev(values) / mean if len(values) > 1 and mean else 0
    return {"median": round(statistics.median(values), 1), "worst": round(max(values), 1),
            "best": round(min(values), 1), "cv": round(cv, 3), "n": len(values)}

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config", action="append", required=True, help="NAME=LAB:ENGINE[:MODE]")
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--scenario", action="append")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=int, default=300)
    a = ap.parse_args()
    configs = []
    for c in a.config:
        name, rest = c.split("=", 1)
        parts = rest.split(":")
        configs.append((name, parts[0], parts[1], parts[2] if len(parts) > 2 else "", parts[3] if len(parts) > 3 else ""))
    work = pathlib.Path(tempfile.gettempdir()) / "engine-sessions-bench"
    work.mkdir(exist_ok=True)
    table = scenarios(work)
    chosen = a.scenario or list(table)
    runs = []
    for scenario in chosen:
        for i in range(a.runs):
            for name, lab, engine, mode, flags in configs:
                rc, secs, records, err = run_once(lab, engine, mode, table[scenario], a.timeout, flags)
                row = {"scenario": scenario, "config": name, "run": i, "rc": rc, "seconds": round(secs, 1),
                       **numbers(scenario, records)}
                if rc != 0:
                    row["stderr"] = err
                runs.append(row)
                print(json.dumps(row), flush=True)
    result = {"machine": os.uname().nodename, "cpus": os.cpu_count(), "runs": runs, "summary": {}}
    for scenario in chosen:
        for name, *_ in configs:
            rows = [r for r in runs if r["scenario"] == scenario and r["config"] == name and r["rc"] == 0]
            keys = sorted({k for r in rows for k, v in r.items() if isinstance(v, (int, float)) and k not in ("run", "rc")})
            result["summary"].setdefault(scenario, {})[name] = {k: spread([r.get(k) for r in rows]) for k in keys}
    text = json.dumps(result, indent=1)
    if a.out:
        pathlib.Path(a.out).write_text(text)
    print(json.dumps(result["summary"], indent=1))

if __name__ == "__main__":
    sys.exit(main())
