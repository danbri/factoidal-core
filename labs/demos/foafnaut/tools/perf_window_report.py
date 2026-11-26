#!/usr/bin/env python3
"""Where the CPU time of a window of a Foafnaut run went: perf samples cut to the windows that
the host's trace names (issue 1031; docs/designissues/2026-11-26-foafnaut-engine-sessions.md).

Record (the real-time clock, so samples and trace share a clock; the run's steps start with
"mark", whose record carries epochMs, the wall clock of its t):

  perf record -e cpu-clock -F 999 -g -k CLOCK_REALTIME -o run.data -- \\
    deno run --v8-flags=--perf-basic-prof ... run_html.ts ... --steps STEPS > trace.log
  perf script -i run.data --show-mmap-events -F comm,pid,tid,time,ip,sym,dso > run.script

Report:

  perf_window_report.py --trace trace.log --script run.script [--window tab-first-frame:1]
      [--library libweb-render.so]

--library: the native library that the engine's copies were made from (--engine-mode copies
loads a copy per worker and deletes the file, so perf can not read its symbols): frames in a
file named foafnaut-engine-*.so are named from this library's symbol table, through the copy's
memory map (the run.script must have --show-mmap-events).

Windows: `tab-first-frame:N` is the N-th native-html-tab-first-frame record (from the tab shown
to its first frame; 0 is the first); `marks:A:B` is from the A-th to the B-th native-html-mark.
For each window: samples per thread (main is the thread whose id is the process id), per
library, the leaf functions (self) and the functions on any frame of the stack (inclusive), with
the share of the window's samples. One sample is about 1 ms of one CPU (at -F 999).
"""
import argparse, bisect, collections, json, re, subprocess, sys

def trace_records(path):
    out = []
    for line in open(path, errors="replace"):
        if line.startswith("{"):
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return out

HEADER = re.compile(r"^\s*(?P<comm>.+?)\s+(?P<pid>\d+)/(?P<tid>\d+)\s+(?P<time>\d+\.\d+):")
FRAME = re.compile(r"^\s+(?P<ip>[0-9a-f]+)\s+(?P<sym>.*?)\s+\((?P<dso>[^()]*)\)\s*$")
MMAP = re.compile(r"\[0x(?P<start>[0-9a-f]+)\(0x(?P<len>[0-9a-f]+)\) @ 0x(?P<pgoff>[0-9a-f]+) .*\]: r-xp (?P<path>\S+)")
COPY = re.compile(r"foafnaut-engine-[0-9]+-[0-9]+\.(so|dylib)$")

class Symbols:
    """The text symbols of a library, to name an address of a copy of it."""
    def __init__(self, library):
        out = subprocess.run(["nm", "-n", "--defined-only", library], capture_output=True, text=True, check=True).stdout
        self.addrs, self.names = [], []
        for line in out.splitlines():
            parts = line.split(" ", 2)
            if len(parts) == 3 and parts[1] in "tTwW":
                self.addrs.append(int(parts[0], 16)); self.names.append(parts[2])
        # The executable segment's address minus its file offset (readelf -l).
        self.delta = 0
        for line in subprocess.run(["readelf", "-lW", library], capture_output=True, text=True, check=True).stdout.splitlines():
            # LOAD offset vaddr paddr filesz memsz flags... align; the flags of the code are "R E".
            f = line.split()
            if len(f) >= 8 and f[0] == "LOAD" and "E" in f[6:-1]:
                self.delta = int(f[2], 16) - int(f[1], 16)
    def name(self, vaddr):
        i = bisect.bisect_right(self.addrs, vaddr) - 1
        return self.names[i] if i >= 0 else "[unknown]"

def samples(path, symbols=None):
    """(time s, comm, pid, tid, [(sym, dso), ...] leaf first) per sample of `perf script`."""
    cur = None
    maps = {}
    for line in open(path, errors="replace"):
        if "PERF_RECORD_MMAP" in line:
            m = MMAP.search(line)
            if m and COPY.search(m["path"]):
                maps[m["path"].rsplit("/", 1)[-1]] = (int(m["start"], 16), int(m["pgoff"], 16))
            continue
        if not line.strip():
            if cur:
                yield cur
            cur = None
            continue
        m = HEADER.match(line) if not line.startswith(("\t", " " * 8)) else None
        if m:
            if cur:
                yield cur
            cur = (float(m["time"]), m["comm"].strip(), int(m["pid"]), int(m["tid"]), [])
            continue
        f = FRAME.match(line)
        if f and cur:
            sym = re.sub(r"\+0x[0-9a-f]+$", "", f["sym"])
            dso = f["dso"].rsplit("/", 1)[-1]
            if symbols and sym == "[unknown]" and dso in maps:
                start, pgoff = maps[dso]
                sym = symbols.name(int(f["ip"], 16) - start + pgoff + symbols.delta)
                dso = "libweb-render.so (copy)"
            cur[4].append((sym, dso))
    if cur:
        yield cur

def short(sym, width=90):
    return sym if len(sym) <= width else sym[: width - 3] + "..."

def report(name, picked, top):
    total = len(picked)
    print(f"\n== {name}: {total} samples")
    if not total:
        return {"window": name, "samples": 0}
    share = lambda n: f"{100 * n / total:5.1f}%"
    threads = collections.Counter(("main" if s[2] == s[3] else s[1]) for s in picked)
    dsos = collections.Counter(s[4][0][1] if s[4] else "?" for s in picked)
    leaf = collections.Counter(short(s[4][0][0]) if s[4] else "?" for s in picked)
    incl = collections.Counter()
    for s in picked:
        incl.update({short(sym) for sym, _ in s[4]})
    main_leaf = collections.Counter(short(s[4][0][0]) if s[4] else "?" for s in picked if s[2] == s[3])
    for title, counter in (("threads", threads), ("libraries (leaf)", dsos), ("leaf functions", leaf),
                           ("main thread leaf functions", main_leaf), ("inclusive", incl)):
        print(f"-- {title}")
        for k, n in counter.most_common(top):
            print(f"  {n:6d} {share(n)}  {k}")
    return {"window": name, "samples": total, "threads": threads.most_common(top), "libraries": dsos.most_common(top),
            "leaf": leaf.most_common(top), "mainLeaf": main_leaf.most_common(top), "inclusive": incl.most_common(top)}

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--trace", required=True)
    ap.add_argument("--script", required=True)
    ap.add_argument("--window", action="append", default=[])
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("--json")
    ap.add_argument("--library", help="the library the engine copies were made from")
    a = ap.parse_args()
    records = trace_records(a.trace)
    marks = [r for r in records if r.get("type") == "native-html-mark" and "epochMs" in r]
    if not marks:
        sys.exit("no native-html-mark record with epochMs: start the steps with \"mark\"")
    # Wall clock (s) of a trace time t (ms since the process's time origin).
    origin = marks[0]["epochMs"] - marks[0]["t"]
    wall = lambda t: (origin + t) / 1000
    firsts = [r for r in records if r.get("type") == "native-html-tab-first-frame"]
    windows = []
    for w in a.window or ["tab-first-frame:1"]:
        kind, *arg = w.split(":")
        if kind == "tab-first-frame":
            r = firsts[int(arg[0])]
            windows.append((f"{w} (tab {r.get('tab')}, {r.get('ms')} ms)", wall(r["t"] - r["ms"]), wall(r["t"])))
        elif kind == "marks":
            windows.append((w, wall(marks[int(arg[0])]["t"]), wall(marks[int(arg[1])]["t"])))
        else:
            sys.exit(f"unknown window {w}")
    all_samples = list(samples(a.script, Symbols(a.library) if a.library else None))
    out = []
    for name, start, end in windows:
        picked = [s for s in all_samples if start <= s[0] <= end]
        out.append(report(name, picked, a.top))
    if a.json:
        open(a.json, "w").write(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
