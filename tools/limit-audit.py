#!/usr/bin/env python3
"""List the resource limits of Foafnaut and say which ones report a hit.

Issue: https://github.com/danbri/factoidal-core/issues/865 (report every resource limit
that a page reaches).

A limit is a Lean definition `def max<Name> : Nat|Float|UIntN` or a TypeScript constant
`MAX_<NAME>` in the Foafnaut and rendering sources. A limit "reports" when a line that
names it, or one of the 12 lines after such a line, also calls a reporting function
(`WebAccept.skip`, `limitHit`, `Limit.hit`, or a TypeScript `limitHit(`). This is a
textual check: it can call a limit reported that is not (the report is for something
else) and it cannot see a limit compared through another name. Read the table, not only
the count.

Usage:
  python3 tools/limit-audit.py            # the table
  python3 tools/limit-audit.py --gate     # exit 1 when the number of limits that do not
                                          # report is above the baseline below
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_DIRS = ["labs/demos/foafnaut", "formal/lean4/L4Factoidal/Rendering"]
TS_DIRS = ["labs/demos/foafnaut", "tests/browser-wpt"]
REPORTERS = re.compile(r"WebAccept\.skip|limitHit|Limit\.hit")
# Limits that do not report, measured 2026-11-24. Lower it as reports land; never raise it.
BASELINE_UNREPORTED = 105

LEAN_DEF = re.compile(r"^\s*(?:private\s+)?def\s+(max[A-Z]\w*)\s*:\s*(Nat|Float|UInt\d+)\s*:=\s*(.*)$")
TS_DEF = re.compile(r"\b(MAX_[A-Z_]+)\s*=\s*([^,;]+)")


def files(dirs, exts):
    out = []
    for d in dirs:
        base = os.path.join(ROOT, d)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = [x for x in dirnames if not x.startswith(".") and x != "node_modules"]
            for f in filenames:
                if f.endswith(exts) and "Test" not in f and not f.endswith("_test.ts"):
                    out.append(os.path.join(dirpath, f))
    if not out:
        sys.exit("limit-audit: no source files found (wrong ROOT?)")
    return sorted(out)


def main():
    lean = files(LEAN_DIRS, (".lean",))
    ts = files(TS_DIRS, (".ts",))
    texts = {p: open(p, encoding="utf-8", errors="replace").read().splitlines() for p in lean + ts}
    limits = []
    for p in lean:
        for i, line in enumerate(texts[p]):
            m = LEAN_DEF.match(line)
            if m:
                limits.append((m.group(1), m.group(3).strip()[:40], os.path.relpath(p, ROOT), i + 1, "lean"))
    for p in ts:
        for i, line in enumerate(texts[p]):
            for m in TS_DEF.finditer(line):
                if "const" in line or "export" in line:
                    limits.append((m.group(1), m.group(2).strip()[:40], os.path.relpath(p, ROOT), i + 1, "ts"))
    # one name can be defined in two files (maxImagePixels): check uses in all sources of its kind
    rows = []
    for name, value, path, line, kind in limits:
        pool = lean if kind == "lean" else ts
        uses = 0
        reported = False
        word = re.compile(r"\b" + re.escape(name) + r"\b")
        for p in pool:
            t = texts[p]
            for i, l in enumerate(t):
                if word.search(l) and not (os.path.relpath(p, ROOT) == path and i + 1 == line):
                    uses += 1
                    if any(REPORTERS.search(x) for x in t[i:i + 13]):
                        reported = True
        rows.append((reported, name, value, path, line, uses))
    rows.sort(key=lambda r: (r[0], r[3], r[4]))
    if "--gate" not in sys.argv:
        print("reports\tlimit\tvalue\tuses\twhere")
        for reported, name, value, path, line, uses in rows:
            print(f"{'yes' if reported else 'NO'}\t{name}\t{value}\t{uses}\t{path}:{line}")
    unreported = sum(1 for r in rows if not r[0])
    print(f"limits: {len(rows)}; report a hit: {len(rows) - unreported}; do not: {unreported}")
    if "--gate" in sys.argv and BASELINE_UNREPORTED is not None and unreported > BASELINE_UNREPORTED:
        print(f"limit-audit: {unreported} limits do not report, above the baseline {BASELINE_UNREPORTED}")
        sys.exit(1)


if __name__ == "__main__":
    main()
