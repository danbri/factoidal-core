#!/usr/bin/env python3
"""Panic sites reachable from the shipped wasm ops
(https://github.com/danbri/factoidal-core/issues/1181, P4, first step).

The no-crash property of https://www.anthropic.com/research/formal-verification
is fixed and needs no model-written specification. For Lean code the crash
sources are the panicking forms (`panic!`, `unreachable!`, `get!`, `head!`,
`toNat!`, `xs[i]!`, every other `name!` call) and `partial def` (an opaque loop
that no theorem can bound). This tool counts them in the modules that the wasm
dispatch reaches by imports, per top directory, and holds the counts in
`foundation/panic-sites.txt` as a ratchet: a new panic site in shipped code
changes that file in the same commit; a removed one lowers it.

Method: comments removed (the claims gate's comment stripper), then a regular
expression scan of compiled declarations only (theorems, lemmas and examples
are left out, and so are `#guard`, `#eval` and `#print` lines, which run at
build time). `set!`, `modify!` and `swap!` are not counted: out of range they
change nothing and do not panic. A panic in compiled Lean prints a message
and returns the type's default value; it does not stop the program, so in the
wasm a panic site is a place where a wrong answer can come back silently. Reach is by module imports from
`Wasm.Dispatch`, `Wasm.CoreDispatch` and `Wasm.Exports`, so a module counts
when any of its definitions could be in the wasm, which over-counts: the next
step of issue 1181 is reach by definition, per op. A count of 0 at a site does
not prove that op cannot panic (a panic in Lean core or in C is not seen).

Usage:
  python3 -I tools/lean-panic-sites.py            check against the ratchet
  python3 -I tools/lean-panic-sites.py --list     counts per top directory and kind
  python3 -I tools/lean-panic-sites.py --sites DIR  the sites in one top directory
  python3 -I tools/lean-panic-sites.py --record   rewrite the ratchet
"""
import importlib.util
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "formal", "lean4")
RATCHET = os.path.join(ROOT, "foundation", "panic-sites.txt")
ROOTS = ["Wasm.Dispatch", "Wasm.CoreDispatch", "Wasm.Exports"]

_spec = importlib.util.spec_from_file_location("claims_gate", os.path.join(ROOT, "tools", "claims-gate.py"))
_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gate)

KINDS = [
    ("partial-def", re.compile(r"\bpartial\s+def\b")),
    ("panic", re.compile(r"(?<![\w.'])(?:panic|unreachable)!")),
    ("index-bang", re.compile(r"\]!")),
    ("bang-call", re.compile(r"(?<![\w'])(?!panic!|unreachable!)[A-Za-z_][\w.]*[a-z0-9_]!(?=[\s(\[)\],;]|$)")),
]
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def module_path(mod):
    return os.path.join(LEAN, *mod.split(".")) + ".lean"


def reach():
    seen, todo = set(), list(ROOTS)
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        p = module_path(mod)
        if not os.path.exists(p):
            continue
        seen.add(mod)
        with open(p, encoding="utf-8") as f:
            for line in f:
                if line.startswith("import "):
                    todo.extend(m for m in line[len("import "):].split() if m.startswith(("L4Factoidal", "Wasm")))
    if len(seen) < 50:
        sys.exit(f"lean-panic-sites: the walk reached {len(seen)} modules; refusing an empty walk")
    return seen


def top_of(mod):
    parts = mod.split(".")
    return ".".join(parts[:2]) if len(parts) > 1 else mod


NO_PANIC = re.compile(r"(?:^|\.)(?:set|modify|swap)!$")  # out of range: no change, no panic


def sites_of(mod):
    """Sites in compiled declarations only: theorems, lemmas and examples are
    not compiled, so a `get!` in a theorem statement is not counted."""
    out = []
    for name, hits in _gate.declarations(module_path(mod)).items():
        for kw, mods, text, start in hits:
            if kw in ("theorem", "lemma", "example"):
                continue
            for k, line in enumerate(text.split("\n")):
                if re.match(r"\s*#(guard|eval|print|check|reduce)\b", line):
                    continue
                line = STRING.sub('""', line)
                for kind, pat in KINDS:
                    for m in pat.finditer(line):
                        if kind == "bang-call" and NO_PANIC.search(m.group(0)):
                            continue
                        out.append((start + k, kind, line.strip()[:140]))
    return out


def count():
    per_top = Counter()
    per_kind = Counter()
    mods = sorted(reach())
    for m in mods:
        for _, kind, _ in sites_of(m):
            per_top[top_of(m)] += 1
            per_kind[kind] += 1
    return mods, per_top, per_kind


def read_ratchet():
    want, total = {}, None
    if os.path.exists(RATCHET):
        for line in open(RATCHET, encoding="utf-8"):
            m = re.match(r"#\s*max-total:\s*(\d+)", line)
            if m:
                total = int(m.group(1))
            m = re.match(r"^(\S+)\s+sites=(\d+)", line)
            if m:
                want[m.group(1)] = int(m.group(2))
    return want, total


def check():
    mods, per_top, per_kind = count()
    want, total_want = read_ratchet()
    errors = []
    total = sum(per_top.values())
    for top in sorted(set(per_top) | set(want)):
        got, w = per_top.get(top, 0), want.get(top)
        if w is None:
            errors.append(f"{top}: {got} panic sites, no line in foundation/panic-sites.txt")
        elif got > w:
            errors.append(f"{top}: {got} panic sites, more than the {w} recorded (a new panic site in code the wasm reaches)")
        elif got < w:
            errors.append(f"{top}: {got} panic sites, fewer than the {w} recorded (lower the count: it only goes down)")
    if total_want is None or total != total_want:
        errors.append(f"total {total}, max-total {total_want}")
    for e in errors:
        print("lean-panic-sites: FAIL " + e)
    kinds = ", ".join(f"{k} {per_kind[k]}" for k, _ in KINDS)
    print(f"lean-panic-sites: {len(mods)} modules reached from the wasm dispatch, {total} panic sites ({kinds}), {len(errors)} errors")
    return 1 if errors else 0


def record():
    mods, per_top, per_kind = count()
    total = sum(per_top.values())
    head = ["# Panic sites in Lean modules that the wasm dispatch reaches by imports",
            "# (https://github.com/danbri/factoidal-core/issues/1181, P4). Written by",
            "# `python3 -I tools/lean-panic-sites.py --record`; checked by the same tool.",
            "# A ratchet: counts must match the tree, and they only go down.",
            f"# modules reached: {len(mods)}; kinds: " + ", ".join(f"{k} {per_kind[k]}" for k, _ in KINDS),
            f"# max-total: {total}"]
    rows = [f"{top} sites={n}" for top, n in sorted(per_top.items())]
    open(RATCHET, "w", encoding="utf-8").write("\n".join(head + rows) + "\n")
    print(f"recorded {len(rows)} directories, {total} sites")
    return 0


def main(argv):
    if not argv:
        return check()
    if argv[0] == "--record":
        return record()
    if argv[0] == "--list":
        mods, per_top, per_kind = count()
        for top, n in per_top.most_common():
            print(f"{n:6d}  {top}")
        print(f"{sum(per_top.values()):6d}  total in {len(mods)} modules; " + ", ".join(f"{k} {per_kind[k]}" for k, _ in KINDS))
        return 0
    if argv[0] == "--sites":
        for m in sorted(reach()):
            if top_of(m) == argv[1]:
                for n, kind, text in sites_of(m):
                    print(f"{os.path.relpath(module_path(m), ROOT)}:{n}  {kind:11s} {text}")
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
