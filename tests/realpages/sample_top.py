# Where an engine run spends its time, from a macOS sample(1) report (engine_run.ts --sample): per thread that ran
# engine code, the engine functions with the most samples under them (inclusive, counted once per stack even when a
# function recurses) and the most samples at the top of the stack (self).
# usage: python3 -I sample_top.py sample-N.txt [--top 25] [--match SUBSTRING]
import re, sys
from collections import defaultdict

args = sys.argv[1:]
top = int(args[args.index("--top") + 1]) if "--top" in args else 25
match = args[args.index("--match") + 1] if "--match" in args else None
path = args[0]
LINE = re.compile(r"^(?P<lead>[ +!:|]*)(?P<n>\d+) (?P<name>.+?)  \(in (?P<lib>[^)]+)\)")
THREAD = re.compile(r"^\s+(?P<n>\d+) (?P<name>Thread_\d+.*)$")


def short(name: str) -> str:
    # Lean's C names: l_Mod_Sub_fn___redArg, l___private_Mod_0__fn, lp_pkg_Mod_fn; drop specialisation suffixes
    name = re.sub(r"(___redArg|___boxed|___lam_\d+|___at___.*|_spec__\d+.*)+$", "", name)
    return name


threads = []  # (thread name, total, list of (depth, count, name, lib))
cur = None
in_graph = False
for line in open(path, errors="replace"):
    if line.startswith("Call graph:"):
        in_graph = True
        continue
    if in_graph and (line.startswith("Total number in stack") or line.startswith("Sort by top of stack")):
        break
    if not in_graph:
        continue
    t = THREAD.match(line)
    if t:
        cur = (t["name"].strip(), int(t["n"]), [])
        threads.append(cur)
        continue
    m = LINE.match(line)
    if m and cur:
        cur[2].append((len(m["lead"]), int(m["n"]), m["name"].strip(), m["lib"]))

for tname, total, nodes in threads:
    if not any("libweb-render" in n[3] for n in nodes):
        continue
    incl = defaultdict(int)
    selfc = defaultdict(int)
    stack = []  # (depth, name)
    engine_total = 0
    for i, (d, c, name, lib) in enumerate(nodes):
        while stack and stack[-1][0] >= d:
            stack.pop()
        s = short(name) if "libweb-render" in lib else None
        if s and s not in [x[1] for x in stack]:
            incl[s] += c
        if s and not any("libweb-render" in x[2] for x in stack):
            engine_total += c
        stack.append((d, s or name, lib))
        nxt = nodes[i + 1][0] if i + 1 < len(nodes) else -1
        if nxt <= d:  # a leaf: its samples are self samples
            key = s if s else f"[{lib}] {name[:60]}"
            selfc[key] += c
    print(f"== {tname[:70]}  samples {total}, in engine code {engine_total}")
    items = sorted(incl.items(), key=lambda kv: -kv[1])
    if match:
        items = [kv for kv in items if match in kv[0]]
    print("  inclusive:")
    for k, v in items[:top]:
        print(f"  {v:7d} {100 * v / max(total, 1):5.1f}%  {k[:150]}")
    print("  self (top of stack):")
    for k, v in sorted(selfc.items(), key=lambda kv: -kv[1])[:top // 2]:
        print(f"  {v:7d} {100 * v / max(total, 1):5.1f}%  {k[:150]}")
