#!/usr/bin/env python3
"""Engine sessions: each tab mode of the desktop host against a base build, on one machine, in
one run (issue https://github.com/danbri/factoidal-core/issues/1031;
docs/designissues/2026-11-26-foafnaut-engine-sessions.md, section 5).

    engine_sessions_bench.py --config NAME=LAB:ENGINE[:MODE] ... [--runs N] [--scenario S ...]
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
  tabs    seven new tabs, 1 s apart, from the start page: tab first frame, process resident
          memory at exit, engine start (ms and resident memory, from native-html-engine-worker).
  one     the start page and no new tab: process resident memory at exit (the base for tabs).
  status  pages/status.html, resize sweep (7 sizes, a Lean frame each): frame total p50 and p95.
  rex     pages/particle-rex.html for 8 s (its title screen animates): timer turns (count, engine
          ms per turn, call beyond the engine, wait before the next ask) and page-canvas
          presents (count, ms), frame total.

Output: one JSON object, with each run's numbers and, per configuration and scenario, the
median, the worst and the coefficient of variation of each number
(skills/perceived-performance, rules 1 and 2)."""
import argparse, json, os, pathlib, statistics, subprocess, sys, tempfile, time

HERE = pathlib.Path(__file__).resolve().parent.parent

def heavy_page(path):
    rows = "".join(f"<tr><td>{i}</td><td>row {i} of a long table with some words in it</td><td>{i*7%13}</td><td>{i%97}</td></tr>\n"
                   for i in range(20000))
    path.write_text(f"<!doctype html><title>Heavy</title><table>{rows}</table>")

def scenarios(work):
    heavy = work / "heavy.html"
    if not heavy.exists():
        heavy_page(heavy)
    steps = {}
    steps["heavy"] = ["now:2:300", f"go:file://{heavy}", "t", "now:42:150"] + [[5, 0, 0], [9, 97, 0]] * 21
    steps["tabs"] = ["now:7:1000"] + ["t"] * 7
    files = {}
    for name, value in steps.items():
        f = work / f"steps-{name}.json"
        f.write_text(json.dumps(value))
        files[name] = f
    return {
        "heavy": ["--html", "pages/index.html", "--steps", str(files["heavy"])],
        "tabs": ["--html", "pages/index.html", "--steps", str(files["tabs"])],
        "one": ["--html", "pages/index.html", "--watch-sweep", "4"],
        "status": ["--html", "pages/status.html", "--resize-sweep"],
        "rex": ["--html", "pages/particle-rex.html", "--watch-sweep", "8"],
    }

def run_once(lab, engine, mode, args, timeout):
    cmd = ["flock", "/tmp/foafnaut-timing.lock", "xvfb-run", "-a", "-s", "-screen 0 1280x900x24",
           "deno", "run", "--no-check", "--no-config", "--no-npm", "--node-modules-dir=none",
           "--unstable-webgpu", "--unstable-ffi", "-A", "run_html.ts",
           "--native-engine", engine, "--no-splash", "--no-state", "--perf-summary"] + \
          (["--engine-mode", mode] if mode else []) + args
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
        configs.append((name, parts[0], parts[1], parts[2] if len(parts) > 2 else ""))
    work = pathlib.Path(tempfile.gettempdir()) / "engine-sessions-bench"
    work.mkdir(exist_ok=True)
    table = scenarios(work)
    chosen = a.scenario or list(table)
    runs = []
    for scenario in chosen:
        for i in range(a.runs):
            for name, lab, engine, mode in configs:
                rc, secs, records, err = run_once(lab, engine, mode, table[scenario], a.timeout)
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
