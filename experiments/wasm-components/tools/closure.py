#!/usr/bin/env python3
"""Import closure of a Lean module, split into repository modules and
toolchain (Init/Std/Lean) modules.

Usage: closure.py <root.lean> <repo lean dir> <toolchain src/lean dir>
Prints one line per module: `repo <path>` or `core <path>`.
Reads the sources on every run (anti-pattern 30: no cached lists).
"""
import re, sys, pathlib

root, repo, core = (pathlib.Path(a) for a in sys.argv[1:4])
IMPORT = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([\w.]+)', re.M)

def locate(mod):
    rel = pathlib.Path(*mod.split('.')).with_suffix('.lean')
    for kind, base in (("repo", repo), ("core", core)):
        if (base / rel).is_file():
            return kind, base / rel
    raise SystemExit(f"module {mod} not found")

def strip_comments(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)

seen, order, todo = set(), [], [("root", root)]
while todo:
    kind, path = todo.pop()
    if path in seen:
        continue
    seen.add(path)
    order.append((kind, path))
    text = strip_comments(path.read_text())
    head = text.split('\nnamespace', 1)[0].split('\nsection', 1)[0]
    mods = IMPORT.findall(head)
    if not re.search(r'^\s*prelude\b', head, re.M):
        mods.append("Init")
    for m in mods:
        todo.append(locate(m))
if len(order) < 2:
    raise SystemExit("empty closure")
for kind, path in order:
    print(kind, path)
