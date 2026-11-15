#!/usr/bin/env python3
# Textnaut on the native engine library against the Wasm engine: the same text grid for each page,
# and the time of the first render and of keys on a pseudo-terminal, for each engine.
#
#   python3 textnaut/engine_parity.py --native LIB --wasm-dir DIR [--cmd "node .../bin/textnaut.mjs"]
#       [--runs 3] [--json out.json] [--expect-auto-native] PAGE...
#
# Run from labs/demos/foafnaut. --cmd is how textnaut is started (default: deno on textnaut.ts here).
# --native LIB is passed as --engine LIB; the Wasm run gets --wasm and TEXTNAUT_WASM_DIR=DIR.
# --expect-auto-native also runs the first page with no engine option and checks that textnaut chose
# the native engine by itself (an installed library in FOAFNAUT_HOME).
# Each check prints PASS or FAIL; the exit code is the number of failed checks.
import argparse, difflib, fcntl, json, os, pty, re, select, shlex, signal, statistics, struct, subprocess, sys, termios, time

DENO = ["deno", "run", "--no-check", "--no-config", "--no-prompt", "--allow-read", "--allow-ffi", "--allow-net", "--allow-env",
        "--import-map=textnaut/import_map.json", "textnaut/textnaut.ts"]
TIMING = re.compile(r"timing: engine (\w+); start (\d+) ms; load (\d+) ms; layout (\d+) ms; cells (\d+) ms")
failed = 0

def check(name, ok, detail=""):
    global failed
    print(("PASS " if ok else "FAIL ") + name + ((" (" + detail + ")") if detail else ""), flush=True)
    failed += 0 if ok else 1

def engine_args(args, engine):
    if engine == "native":
        return ["--engine", args.native], {}
    if engine == "wasm":
        return ["--wasm"], {"TEXTNAUT_WASM_DIR": args.wasm_dir}
    return [], {}

def dump(args, engine, page):
    extra, env = engine_args(args, engine)
    t0 = time.perf_counter()
    run = subprocess.run(args.cmd + ["--dump", "--width", "100", "--colour", "none", "--timing"] + extra + [page],
                         capture_output=True, text=True, env={**os.environ, **env}, timeout=600)
    wall = (time.perf_counter() - t0) * 1000
    m = TIMING.search(run.stderr)
    timing = {"wall": wall, "engine": m[1], "start": int(m[2]), "load": int(m[3]), "layout": int(m[4]), "cells": int(m[5])} if m else None
    return run, timing

def median(xs):
    return round(statistics.median(xs), 1) if xs else None

class Session:
    """textnaut on a pseudo-terminal, 40 rows by 100 columns."""
    def __init__(self, argv, env):
        self.pid, self.fd = pty.fork()
        if self.pid == 0:
            os.environ.update(env)
            # As pty_check.py: a terminal that answers none of textnaut's queries (the worst case).
            os.environ.update({"TERM": "xterm-256color", "COLORTERM": "truecolor", "LANG": "en_GB.UTF-8"})
            os.execvp(argv[0], argv)
        fcntl.ioctl(self.fd, termios.TIOCSWINSZ, struct.pack("HHHH", 40, 100, 0, 0))
        self.out = b""
    def read(self, seconds):
        end = time.perf_counter() + seconds
        while True:
            left = end - time.perf_counter()
            if left <= 0: return
            ready, _, _ = select.select([self.fd], [], [], min(left, 0.02))
            if ready:
                try: chunk = os.read(self.fd, 65536)
                except OSError: return
                if not chunk: return
                self.out += chunk
                return
    def until(self, pred, timeout):
        """Reads until pred(output since now) holds; returns the ms it took, or None."""
        start = len(self.out); t0 = time.perf_counter()
        while time.perf_counter() - t0 < timeout:
            self.read(0.05)
            if pred(self.out[start:]): return (time.perf_counter() - t0) * 1000
        return None
    def quiet(self, ms):
        """Reads until no output for `ms`; returns the time of the last byte, from now, in ms."""
        t0 = time.perf_counter(); last = t0
        while (time.perf_counter() - last) * 1000 < ms:
            n = len(self.out); self.read(0.01)
            if len(self.out) != n: last = time.perf_counter()
        return (last - t0) * 1000
    def send(self, data): os.write(self.fd, data)
    def resize(self, rows, cols):
        fcntl.ioctl(self.fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0)); os.kill(self.pid, signal.SIGWINCH)
    def close(self):
        try: os.write(self.fd, b"q")
        except OSError: pass
        for _ in range(100):
            if os.waitpid(self.pid, os.WNOHANG)[0]: return
            time.sleep(0.02)
        os.kill(self.pid, signal.SIGKILL); os.waitpid(self.pid, 0)

def loaded(name):
    """The top bar names the engine and does not say loading."""
    bar = re.compile(rb"(loading )?" + name.encode() + rb" engine")
    def pred(out):
        found = bar.findall(out)
        return bool(found) and found[-1] == b""
    return pred

def interactive(args, engine, start_page):
    extra, env = engine_args(args, engine)
    argv = args.cmd + extra + [start_page]
    t0 = time.perf_counter()
    s = Session(argv, env)
    out = {}
    try:
        first = s.until(loaded(engine), 300)
        out["first_frame"] = round((time.perf_counter() - t0) * 1000, 1) if first is not None else None
        if first is None: return out
        s.quiet(300)
        # Host-only keys: one draw each.
        for key, name in ((b"j", "scroll_j"), (b"\t", "tab")):
            times = []
            for _ in range(10):
                t = time.perf_counter(); s.send(key); s.until(lambda o: len(o) > 0, 5); times.append((time.perf_counter() - t) * 1000)
                s.quiet(60)
            out[name] = median(times)
        # Follow link 1 (the next page loads and lays out on the engine), then back.
        for key, name in ((b"1\r", "follow_link"), (b"b", "back")):
            times = []
            for _ in range(3):
                t0 = time.perf_counter(); s.send(key)
                ok = s.until(lambda o: b"loading " in o, 30) is not None and s.until(loaded(engine), 120) is not None
                times.append((time.perf_counter() - t0) * 1000 if ok else float("nan"))
                s.quiet(100)
                if key == b"1\r": s.send(b"b"); s.until(loaded(engine), 120); s.quiet(100)
                else: s.send(b"1\r"); s.until(loaded(engine), 120); s.quiet(100)
            out[name] = median([x for x in times if x == x])
        # A resize: the page is laid out again at the new width (after textnaut's 30 ms burst wait).
        times = []
        for rows, cols in ((40, 80), (40, 100), (40, 72)):
            t0 = time.perf_counter(); s.resize(rows, cols)
            last = s.quiet(250)
            times.append(last)
        out["resize"] = median(times)
    finally:
        s.close()
    return out

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--native", required=True)
    p.add_argument("--wasm-dir", required=True)
    p.add_argument("--cmd", default=None)
    p.add_argument("--runs", type=int, default=3)
    p.add_argument("--json")
    p.add_argument("--expect-auto-native", action="store_true")
    p.add_argument("--no-keys", action="store_true")
    p.add_argument("pages", nargs="+")
    args = p.parse_args()
    args.cmd = shlex.split(args.cmd) if args.cmd else DENO
    report = {"pages": {}, "keys": {}}
    if args.expect_auto_native:
        run, timing = dump(args, "auto", args.pages[0])
        check("textnaut chose the installed native engine by itself", bool(timing) and timing["engine"] == "native",
              (timing or {}).get("engine") or run.stderr.strip()[-300:])
    for page in args.pages:
        results = {}
        for engine in ("native", "wasm"):
            runs = [dump(args, engine, page) for _ in range(args.runs)]
            run = runs[0][0]
            timings = [t for _, t in runs if t]
            ok = run.returncode == 0 and len(timings) == len(runs) and all(t["engine"] == engine for t in timings)
            check(f"{page}: {engine} engine renders", ok, f"exit {run.returncode}; {run.stderr.strip()[-300:]}" if not ok else "")
            results[engine] = {"text": run.stdout, "timing": {k: median([t[k] for t in timings]) for k in ("wall", "start", "load", "layout", "cells")} if timings else None}
        # Both runs must have rendered (checked above); a page of boxes alone gives blank rows.
        same = results["native"]["text"] == results["wasm"]["text"] and bool(results["native"]["timing"])
        detail = ""
        if not same:
            detail = "\n" + "".join(list(difflib.unified_diff(results["wasm"]["text"].splitlines(True), results["native"]["text"].splitlines(True), "wasm", "native"))[:40])
        lines = results["native"]["text"].count("\n")
        check(f"{page}: native and Wasm give the same text grid ({lines} rows)", same, detail)
        report["pages"][page] = {e: results[e]["timing"] for e in results} | {"same": same, "rows": lines}
        n, w = results["native"]["timing"], results["wasm"]["timing"]
        if n and w:
            print(f"  first render, ms (median of {args.runs}; wall includes process start): "
                  f"native start {n['start']} load {n['load']} layout {n['layout']} cells {n['cells']} wall {n['wall']:.0f} | "
                  f"wasm start {w['start']} load {w['load']} layout {w['layout']} cells {w['cells']} wall {w['wall']:.0f}", flush=True)
    if not args.no_keys:
        # A start page with one link to the first page given: follow and back load and lay that page out.
        target = os.path.abspath(args.pages[0])
        start = os.path.join(os.environ.get("RUNNER_TEMP") or "/tmp", f"textnaut-parity-start-{os.getpid()}.html")
        with open(start, "w") as f:
            f.write("<!doctype html><title>Parity start</title><h1>Start</h1>"
                    + f"<p><a href=\"file://{target}\">the page</a></p>"
                    + "".join(f"<p>Line {i} of some text to scroll, <a href=\"#l{i}\">anchor {i}</a>.</p>" for i in range(80)))
        for engine in ("native", "wasm"):
            keys = interactive(args, engine, start)
            report["keys"][engine] = keys
            check(f"keys on a pseudo-terminal, {engine} engine: first frame, scroll, Tab, follow, back, resize",
                  all(keys.get(k) is not None for k in ("first_frame", "scroll_j", "tab", "follow_link", "back", "resize")), json.dumps(keys))
            print(f"  {engine}: " + ", ".join(f"{k} {v} ms" for k, v in keys.items()), flush=True)
        os.unlink(start)
    if args.json:
        with open(args.json, "w") as f: json.dump(report, f, indent=1)
    print(f"{failed} failed", flush=True)
    sys.exit(failed)

if __name__ == "__main__":
    main()
