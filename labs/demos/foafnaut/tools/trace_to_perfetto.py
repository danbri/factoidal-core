#!/usr/bin/env python3
"""trace_to_perfetto.py LOG [LOG ...] [-o OUT.json]: a Foafnaut run's trace records as a timeline.

Reads the JSON lines that run_html.ts writes (--log-all, --perf-summary) and writes a file in the
Trace Event Format (JSON object form, times in microseconds). Open it in https://ui.perfetto.dev
(Open trace file) or in the Chrome DevTools Performance panel (Load profile). Nothing leaves the
machine: both read the file locally in the browser.

Each record that says how long its work took becomes a span [t - ms, t]; run_html.ts writes these
records when the work ends, with t in ms since the host started (performance.now()).
  native-html-load-phases   one span per phase of prepareHTML, in order, on the track "load"
  native-html-frame         frame total, engine session and layout, each on its own track (the
                            record gives the three durations, not where session and layout start
                            inside the frame, so they are not drawn as nested)
  native-html-script        engine time of a script turn (leanMs), track "scripts"
  native-html-engine-worker start of an engine worker (ms), track "engine workers"
  native-html-slow-call     a main-thread engine call over 2 ms, track "main-thread calls"
  native-html-pump-gap      a gap in the host's event pump over 50 ms, track "pump"
Every other record with a time is an instant event on the track "events".
Several LOGs are several processes (one row group each), named by the file name.
"""
import argparse, json, os, sys

TRACKS = ["load", "frame total", "engine session", "layout", "scripts", "engine workers",
          "main-thread calls", "pump", "events"]

def records(path):
    out = []
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("{"):
                try:
                    out.append(json.loads(line))
                except ValueError:
                    pass
    return out

def num(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)

def span(pid, track, name, end_ms, dur_ms, args):
    """A complete event that ends at end_ms and lasts dur_ms (both in ms)."""
    dur_ms = max(0.0, float(dur_ms))
    return {"ph": "X", "pid": pid, "tid": TRACKS.index(track) + 1, "name": name,
            "ts": round((end_ms - dur_ms) * 1000), "dur": round(dur_ms * 1000), "args": args}

def small(r, drop):
    return {k: v for k, v in r.items() if k not in drop and not isinstance(v, (dict, list))}

def events(recs, pid):
    ev = []
    for r in recs:
        kind, t = r.get("type", ""), r.get("t")
        if not num(t):
            continue
        if kind == "native-html-load-phases" and isinstance(r.get("phases"), dict) and num(r.get("totalMs")):
            start = t - r["totalMs"]
            ev.append(span(pid, "load", f"load {r.get('url', '')}"[:120], t, r["totalMs"], small(r, {"type", "t"})))
            at = start
            for name, ms in r["phases"].items():
                if num(ms):
                    ev.append(span(pid, "load", name, at + ms, ms, {"url": r.get("url")}))
                    at += ms
        elif kind == "native-html-frame":
            args = small(r, {"type", "t"})
            for track, key in (("frame total", "totalMs"), ("engine session", "sessionMs"), ("layout", "layoutMs")):
                if num(r.get(key)):
                    ev.append(span(pid, track, f"frame {r.get('frame')} {key}", t, r[key], args))
        elif kind == "native-html-script" and num(r.get("leanMs")):
            ev.append(span(pid, "scripts", f"script {r.get('cause', '')}", t, r["leanMs"], small(r, {"type", "t"})))
        elif kind == "native-html-engine-worker" and r.get("state") == "started" and num(r.get("ms")):
            ev.append(span(pid, "engine workers", f"worker {r.get('worker')} start (tab {r.get('tab')})", t, r["ms"], small(r, {"type", "t"})))
        elif kind == "native-html-slow-call" and num(r.get("ms")):
            ev.append(span(pid, "main-thread calls", str(r.get("call")), t, r["ms"], {}))
        elif kind == "native-html-pump-gap" and num(r.get("ms")):
            ev.append(span(pid, "pump", "pump gap", t, r["ms"], small(r, {"type", "t"})))
        else:
            ev.append({"ph": "i", "s": "t", "pid": pid, "tid": TRACKS.index("events") + 1,
                       "name": kind or "record", "ts": round(t * 1000), "args": small(r, {"t"})})
    return ev

def names(pid, label):
    meta = [{"ph": "M", "pid": pid, "name": "process_name", "args": {"name": label}}]
    for i, track in enumerate(TRACKS):
        meta.append({"ph": "M", "pid": pid, "tid": i + 1, "name": "thread_name", "args": {"name": track}})
        meta.append({"ph": "M", "pid": pid, "tid": i + 1, "name": "thread_sort_index", "args": {"sort_index": i}})
    return meta

def convert(paths):
    out = []
    for pid, path in enumerate(paths, 1):
        recs = records(path)
        if not recs:
            sys.exit(f"trace_to_perfetto.py: no JSON trace records in {path}")
        out += names(pid, os.path.basename(path)) + events(recs, pid)
    return {"traceEvents": out, "displayTimeUnit": "ms"}

def self_test():
    recs = [{"type": "native-html-load-phases", "t": 1000, "totalMs": 300, "url": "u", "phases": {"document": 100, "inspect": 200}},
            {"type": "native-html-frame", "t": 2000, "frame": 1, "totalMs": 900, "sessionMs": 700, "layoutMs": 400},
            {"type": "native-html-slow-call", "t": 500, "call": "keyTable", "ms": 400},
            {"type": "native-html-quit", "t": 3000}]
    ev = events(recs, 1)
    x = {e["name"]: e for e in ev if e["ph"] == "X"}
    assert x["document"]["ts"] == 700_000 and x["document"]["dur"] == 100_000, x["document"]
    assert x["inspect"]["ts"] == 800_000 and x["inspect"]["ts"] + x["inspect"]["dur"] == 1_000_000
    assert x["frame 1 layoutMs"]["ts"] == 1_600_000 and x["frame 1 totalMs"]["ts"] == 1_100_000
    assert x["keyTable"]["ts"] == 100_000
    assert [e for e in ev if e["ph"] == "i"][0]["ts"] == 3_000_000
    json.dumps(convert.__doc__)  # the module loads
    print("trace_to_perfetto.py self-test: ok")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("logs", nargs="*")
    ap.add_argument("-o", "--out", default="-")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        self_test(); sys.exit(0)
    if not a.logs:
        ap.error("give at least one LOG")
    doc = convert(a.logs)
    text = json.dumps(doc)
    if a.out == "-":
        sys.stdout.write(text)
    else:
        with open(a.out, "w") as f:
            f.write(text)
        print(f"{a.out}: {len(doc['traceEvents'])} events from {len(a.logs)} log(s)", file=sys.stderr)
