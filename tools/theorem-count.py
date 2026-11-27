#!/usr/bin/env python3
"""Count the Lean theorems, with closed-value tests apart
(https://github.com/danbri/factoidal-core/issues/1186, P9).

A theorem whose statement has no binder, no `forall` and no implication is
about one closed value (for example `theorem t : f 3 = 7 := by decide`). It is
a test in theorem form. This tool reports the two numbers apart, so that a
count of theorems is not read as a count of general properties. Give both
numbers, labelled, whenever a theorem count is reported (anti-pattern 25).

Comments are removed first. The walk is derived from the tree on every run and
an empty walk is an error (anti-pattern 30).

Usage: python3 -I tools/theorem-count.py [--json FILE] [--by-dir]
"""
import importlib.util
import json
import os
import re
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "formal", "lean4", "L4Factoidal")

_spec = importlib.util.spec_from_file_location("claims_gate", os.path.join(ROOT, "tools", "claims-gate.py"))
_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gate)


def is_closed(statement, name):
    """True when the statement has no binder before its type and no `forall`,
    implication or bound-variable notation in the type."""
    rest = statement.split(name, 1)[1] if name in statement else statement
    depth, i = 0, 0
    while i < len(rest):
        c = rest[i]
        if c in "([{⦃⟨":
            if depth == 0 and c in "([{⦃":
                return False  # a binder before the colon
            depth += 1
        elif c in ")]}⦄⟩":
            depth -= 1
        elif c == ":" and depth == 0:
            break
        i += 1
    ty = rest[i + 1:]
    return not re.search(r"∀|→|->|∃|\bfun\b|λ|↔", ty)


def main(argv):
    total, closed = 0, 0
    by_dir = Counter()
    by_dir_closed = Counter()
    files = 0
    for dp, _, fs in os.walk(SRC):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            files += 1
            path = os.path.join(dp, f)
            top = os.path.relpath(path, SRC).split(os.sep)[0].removesuffix(".lean")
            for name, hits in _gate.declarations(path).items():
                for kw, _mods, text, _line in hits:
                    if kw not in ("theorem", "lemma"):
                        continue
                    total += 1
                    by_dir[top] += 1
                    if is_closed(_gate.statement_of(text), name.rsplit(".", 1)[-1]):
                        closed += 1
                        by_dir_closed[top] += 1
    if files == 0 or total == 0:
        sys.exit("theorem-count: no Lean files or no theorems found; refusing an empty walk")
    general = total - closed
    print(f"theorems: {total} in {files} files; {general} general (with a binder, "
          f"forall, implication or exists), {closed} closed-value tests ({100 * closed / total:.1f}%)")
    if "--by-dir" in argv:
        for d, n in by_dir.most_common():
            print(f"  {d:32s} {n - by_dir_closed[d]:6d} general {by_dir_closed[d]:6d} closed")
    if "--json" in argv:
        out = argv[argv.index("--json") + 1]
        with open(out, "w") as fh:
            json.dump({"theorems": total, "general": general, "closed_value_tests": closed,
                       "files": files, "by_dir": {d: {"general": n - by_dir_closed[d], "closed": by_dir_closed[d]}
                                                  for d, n in by_dir.items()}}, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
