#!/usr/bin/env python3
"""Where the engine time of a page goes, by subsystem: BubblePopJS, canvas 2D raster, page paint,
fonts, layout, CSS, DOM. A repeatable answer to "is page JavaScript the cost?" (issue 1031; record
docs/designissues/2026-11-26-foafnaut-engine-time-by-subsystem.md).

Record (tasks mode: DWARF unwinding needs the library file on disk, and copies mode deletes its
copies; the engine code is the same in every mode):

  perf record -e cpu-clock -F 199 --call-graph dwarf,16384 -k CLOCK_REALTIME -o run.data -- \\
    deno run ... run_html.ts --native-engine libweb-render.so --engine-mode tasks --log-all \\
      --perf-summary --html pages/particle-rex.html --watch-sweep 8 > trace.log
  perf script -i run.data -F comm,pid,tid,time,ip,sym,dso > run.script

Report:

  engine_time_split.py --trace trace.log --script run.script --library libweb-render.so \\
      [--window timers|all|load|first-layout] [--json out.json]

Window: `timers` (default) is from 0.5 s after the first timer turn to the last one (an animating
page); `all` is the whole run (page load and script start included); `load` is from the start of
the first page load (native-html-load-phases) to the end of the first frame's engine layout;
`first-layout` is that layout only (native-html-frame 1, its layoutMs). The trace's times are
performance.now() of the main thread; their origin is taken as the process's first sample, and
the report gives the difference between the quit record and the main thread's last sample as a
check of that (a few tens of ms is good enough for windows of seconds).

Each sample with a frame of the engine library is charged to the nearest Lean namespace on its
stack, from the leaf up. Runtime frames (allocation, reference counts, libc, the kernel) are
charged to their Lean caller; the report also gives, per subsystem, how many of its samples had
such a frame as the leaf. A specialised generic function (List, Array, Std) whose name says which
function it was made for (`___at___`) goes to that function's namespace; one that does not say
goes to its nearest named caller, and stays "generic" only when the stack (16 KB of it with the
recording above) has none. One sample is 1/F s of one CPU (F = --hz, the -F of the recording)."""
import argparse, collections, json, re, statistics, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import perf_window_report as P

SUBSYSTEMS = [  # (name, regular expression on the Lean name after the package prefix); the first match wins
    ("BubblePopJS (L4Factoidal.JS)", r"L4Factoidal_JS_"),
    ("DOM (L4Factoidal.DOM)", r"L4Factoidal_DOM_"),
    ("script host bridge (L4Factoidal.WasmVM.Hosts)", r"L4Factoidal_WasmVM_Hosts_"),
    ("WasmVM, other", r"L4Factoidal_WasmVM_"),
    ("canvas 2D raster (L4Factoidal.PageCanvas)", r"L4Factoidal_PageCanvas_"),
    ("event loop (L4Factoidal.EventLoop)", r"L4Factoidal_EventLoop_"),
    ("CSS (Rendering.Css*, Computed*, MediaQuery, Sheet*)", r"L4Factoidal_Rendering_(Css|CSS|Computed|MediaQuery|Sheet)"),
    ("layout (Rendering.Layout, Flex, Grid, Table)", r"L4Factoidal_Rendering_(Layout|Flex|Grid|Table|LU|Geometry)"),
    ("fonts and text (Rendering.Sfnt*, Woff2, Font*, Colr*)", r"L4Factoidal_Rendering_(Sfnt|Woff2|Font|Colr)"),
    ("animation (Rendering.Animation, Smil)", r"L4Factoidal_Rendering_(Animation|Smil)"),
    ("rendering, other (L4Factoidal.Rendering)", r"L4Factoidal_Rendering_"),
    ("script turn glue (WebScripts, WebRenderScript, WebEventLoop)", r"(WebScripts|WebRenderScript|WebEventLoop)_"),
    ("page layer (WebDocument, WebRender, WebPaint, WebState)", r"(WebDocument|WebRender|WebPaint|WebRepaint|WebState|WebSession|WebHit|WebSelection)_"),
    ("page paint: pieces and tiles (NativeSVG*, NativeGraphics, NativeImage)", r"(NativeSVG|NativeGraphics|NativeImage|NativeScene|NativeGeometry|NativeFoafNaut)"),
    ("other L4Factoidal", r"L4Factoidal_"),
]
COMPILED = [(name, re.compile(rx)) for name, rx in SUBSYSTEMS]
GENERIC = "generic Lean with no named caller (List, Array, String, Std)"
NO_CALLER = "runtime with no Lean caller on the stack"
JS = SUBSYSTEMS[0][0]

def subsystem(sym):
    """The subsystem of one frame's function, or None for a runtime or unnamed frame."""
    for prefix in ("lp_l4factoidal_", "l_"):
        if sym.startswith(prefix):
            name = sym[len(prefix):]
            break
    else:
        return None
    for part in name.split("___at___00", 1):  # its own namespace, else the function it was made for
        if part.startswith("__private_") and "_0__" in part:  # _private.Module.0.Name
            part = part.split("_0__", 1)[1]
        for label, rx in COMPILED:
            if rx.match(part):
                return label
    return GENERIC

def charge(stack):
    """The first named subsystem from the leaf up; a generic function goes to its caller."""
    generic = False
    for sym, dso in stack:
        if "libweb-render" in dso:
            label = subsystem(sym)
            if label == GENERIC:
                generic = True
            elif label:
                return label
    return GENERIC if generic else NO_CALLER

def runtime_leaf(stack):
    sym, dso = stack[0]
    return "libweb-render" not in dso or subsystem(sym) is None

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--trace", required=True)
    ap.add_argument("--script", required=True)
    ap.add_argument("--library", required=True)
    ap.add_argument("--window", choices=("timers", "all", "load", "first-layout"), default="timers")
    ap.add_argument("--hz", type=float, default=199)
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--json")
    a = ap.parse_args()
    recs = P.trace_records(a.trace)
    turns = [r for r in recs if r.get("type") == "native-html-script" and r.get("cause") == "timers"]
    quits = [r for r in recs if r.get("type") == "native-html-quit"]
    samples = list(P.samples(a.script, P.Symbols(a.library)))
    if not samples:
        sys.exit("no samples in the perf script")
    pid = collections.Counter(s[2] for s in samples).most_common(1)[0][0]
    origin = min(s[0] for s in samples if s[2] == pid)
    last_main = max(s[0] for s in samples if s[2] == pid and s[3] == pid)
    if a.window == "timers":
        if len(turns) < 5:
            sys.exit(f"{len(turns)} timer turns: use --window all")
        t0, t1 = turns[0]["t"] + 500, turns[-1]["t"]
    elif a.window in ("load", "first-layout"):
        loads = [r for r in recs if r.get("type") == "native-html-load-phases" and "newtab" not in r.get("url", "")]
        frames = [r for r in recs if r.get("type") == "native-html-frame" and r.get("frame") == 1]
        if not loads or not frames:
            sys.exit("no native-html-load-phases or first native-html-frame in the trace")
        f = frames[0]
        f0 = f["t"] - f["totalMs"]
        t0 = loads[0]["t"] - loads[0]["totalMs"] if a.window == "load" else f0
        t1 = f0 + f["layoutMs"]
    else:
        t0, t1 = 0, (last_main - origin) * 1000
    s0, s1 = origin + t0 / 1000, origin + t1 / 1000
    win = [s for s in samples if s[2] == pid and s0 <= s[0] <= s1]
    engine = [s for s in win if any("libweb-render" in d for _, d in s[4])]
    engine_ids = {id(s) for s in engine}
    threads = collections.Counter()
    for s in win:
        threads["main thread" if s[3] == pid else "engine (a thread with an engine frame)" if id(s) in engine_ids
                else "llvmpipe (software GPU)" if s[1].startswith("llvmpipe") else "V8 background" if s[1].startswith("V8")
                else s[1]] += 1
    by = collections.Counter(charge(s[4]) for s in engine)
    rt = collections.Counter(charge(s[4]) for s in engine if s[4] and runtime_leaf(s[4]))
    # Self: the nearest frame of a named engine function (generic List, Array and Std frames go
    # to it). Inclusive: every engine function on the stack, once per sample.
    def fname(sym):
        return re.sub(r"^.*?L4Factoidal_", "", sym).split("___at___")[0][:90]
    lean_fn, lean_incl = collections.Counter(), collections.Counter()
    for s in engine:
        names = [fname(sym) for sym, _ in s[4] if "L4Factoidal_" in sym]
        if names:
            lean_fn[names[0]] += 1
            for n in set(names):
                lean_incl[n] += 1
    js_fn = collections.Counter()
    for s in engine:
        if charge(s[4]) == JS:
            for sym, _ in s[4]:
                if "L4Factoidal_JS_" in sym:
                    js_fn[sym.replace("lp_l4factoidal_", "").split("___at___00")[0][:80]] += 1
                    break
    win_turns = [r for r in turns if t0 <= r["t"] <= t1]
    lean = sorted(r["leanMs"] for r in win_turns)
    span = s1 - s0
    out = {
        "window": a.window, "windowS": round(span, 2),
        "originCheckMs": round((last_main - origin) * 1000 - quits[0]["t"]) if quits else None,
        "timerTurns": len(win_turns), "timerTurnsPerS": round(len(win_turns) / span, 1) if span > 0 else None,
        "turnEngineMsP50": statistics.median(lean) if lean else None,
        "turnEngineMsP95": lean[int(0.95 * (len(lean) - 1))] if lean else None,
        "engineBusyShare": round(sum(lean) / 1000 / span, 2) if lean and span > 0 else None,
        "samples": len(win), "engineSamples": len(engine), "engineCpuS": round(len(engine) / a.hz, 2),
        "threads": threads.most_common(),
        "subsystems": [{"name": n, "samples": c, "share": round(c / max(1, len(engine)), 3), "runtimeLeaf": rt.get(n, 0)}
                       for n, c in by.most_common()],
        "bubblepopFunctions": js_fn.most_common(a.top),
        "leanFunctions": lean_fn.most_common(a.top),
        "leanFunctionsInclusive": lean_incl.most_common(a.top),
    }
    print(f"window {a.window}: {out['windowS']} s, origin check {out['originCheckMs']} ms; engine CPU {out['engineCpuS']} s "
          f"({len(engine)} samples); timer turns {out['timerTurns']}, engine p50 {out['turnEngineMsP50']} ms, "
          f"p95 {out['turnEngineMsP95']} ms, engine busy {out['engineBusyShare']}")
    print("threads: " + ", ".join(f"{k} {v}" for k, v in out["threads"]))
    for s in out["subsystems"]:
        print(f"  {100 * s['share']:5.1f}%  {s['samples']:5d}  {s['name']}  (runtime leaf {s['runtimeLeaf']})")
    print("BubblePopJS functions: " + ", ".join(f"{k} {v}" for k, v in out["bubblepopFunctions"]))
    for title, key in (("engine functions, self (nearest named engine frame):", "leanFunctions"),
                       ("engine functions, inclusive:", "leanFunctionsInclusive")):
        print(title)
        for k, v in out[key]:
            print(f"  {100 * v / max(1, len(engine)):5.1f}%  {v:5d}  {k}")
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)

if __name__ == "__main__":
    main()
