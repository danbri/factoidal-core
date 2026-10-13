#!/usr/bin/env python3
"""List Lean modules under formal/lean4/L4Factoidal that no build root reaches.

`lake build` checks only the modules in the import closure of the roots that
lakefile.lean declares (the `L4Factoidal` library root, the `Harness` globs,
the `l4wasm` roots and every `lean_exe` root). A theorem file outside that
closure is never type-checked, so a record that calls its theorems proved has
no build behind it. Found 2026-10-13: `Storage.Sbm11.ParallelScanTheorems`
(issue 799 stage 1) had been reported as proved for a day and had never been
built; `OWL.ComprehensionTheorems` and `RDF.GraphPatterns` were in the same
state.

Usage: python3 tools/lean-unbuilt-modules.py [--gate]
With --gate the exit code is 1 when a module is unreached. The walk is derived
from the tree on every run (anti-pattern 30); an empty walk is an error.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "formal", "lean4")
LAKEFILE = os.path.join(LEAN, "lakefile.lean")

def module_path(mod):
    return os.path.join(LEAN, *mod.split(".")) + ".lean"


def imports_of(mod):
    """Every `import` line at column 0 (Lean allows imports only at the head
    of a file, so a later column-0 `import` does not occur)."""
    path = module_path(mod)
    if not os.path.exists(path):
        return []
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.startswith("import "):
                out.extend(line[len("import "):].split())
    return out


def roots_from_lakefile():
    text = open(LAKEFILE, encoding="utf-8").read()
    roots = {"L4Factoidal"}
    # lean_exe ... where root := `X.Y
    roots.update(re.findall(r"root\s*:=\s*`([\w.]+)", text))
    # roots := #[`A, `B, ...] and globs := #[`A, ...]
    for block in re.findall(r"(?:roots|globs)\s*:=\s*#\[(.*?)\]", text, re.S):
        roots.update(re.findall(r"`([\w.]+)", block))
    return roots


def main():
    gate = "--gate" in sys.argv[1:]
    roots = roots_from_lakefile()
    seen = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for i in imports_of(m):
            if i not in seen and os.path.exists(module_path(i)):
                stack.append(i)
    all_mods = []
    for dirpath, _, files in os.walk(os.path.join(LEAN, "L4Factoidal")):
        for fn in files:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), LEAN)[:-5]
                all_mods.append(rel.replace(os.sep, "."))
    if not all_mods or len(seen) < 10:
        print("error: empty walk (no modules found or no roots reached)", file=sys.stderr)
        return 2
    unreached = sorted(m for m in all_mods if m not in seen)
    print(f"{len(all_mods)} modules under L4Factoidal; {len(all_mods) - len(unreached)} reached from "
          f"{len(roots)} lakefile roots; {len(unreached)} not reached")
    for m in unreached:
        print(f"  NOT BUILT: {m}")
    return 1 if (gate and unreached) else 0


if __name__ == "__main__":
    sys.exit(main())
