#!/usr/bin/env python3
"""Foafnaut host policy audit (https://github.com/danbri/factoidal-core/issues/1188, P11).

The Foafnaut host (TypeScript and JavaScript under labs/demos/foafnaut) is
outside every Lean proof. Most of it moves bytes, but some of it decides:
time limits, sizes, thresholds, clamps. This audit counts those POLICY SITES
in each host runtime file and holds the counts in
`foundation/foafnaut-host-policy.txt`, one line per file with a reason. The
counts are a ratchet: a new decision in the host changes that file in the same
commit, where a reviewer sees it; a decision moved into Lean lowers a count.

A policy site, after comments are removed, is one of:
  const-num   a named numeric constant: `const NAME = 60_000;`, `let n = 8,`
              (not 0, 1 or -1, which start counters and indexes)
  default-num a numeric default: `x ?? 100`, `x || 250`
  threshold   a comparison with a number of two or more digits: `ms > 16`
  clamp       a call of Math.min, Math.max or Math.round(... * ...)
This is a regular-expression scan. It cannot see a decision made with a
variable named after nothing, so it is a measurement for review, not a proof.

Host runtime files are the tracked .ts/.mjs/.js files of labs/demos/foafnaut,
less tests (`*_test.*`, `*.test.*`, `test*/`), benchmarks, surveys, sweeps and
developer tools (the same classes as the 2026-11-27 count in
docs/designissues/2026-11-27-formal-verification-post-review.md).

Usage:
  python3 -I tools/foafnaut-host-policy-audit.py            check, exit 0 or 1
  python3 -I tools/foafnaut-host-policy-audit.py --list     per-file counts
  python3 -I tools/foafnaut-host-policy-audit.py --sites F  the sites in file F
  python3 -I tools/foafnaut-host-policy-audit.py --record   rewrite the counts
      (keeps reasons; a new file gets the reason "TO REVIEW", which the check
      refuses, so a person must write one)
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HOST_DIR = "labs/demos/foafnaut"
ALLOW = os.path.join(ROOT, "foundation", "foafnaut-host-policy.txt")

NOT_RUNTIME = re.compile(
    r"(_test|\.test)\.(ts|mjs|js)$|/tests?/|bench|perf|survey|snapshot|bisect|feel_check|showcase|"
    r"_check\.|_report|sweep|/tools/|/realpages/|_diff\.|spinal_variants")

PATTERNS = [
    ("const-num", re.compile(r"\b(?:const|let)\s+[A-Za-z_$][\w$]*\s*(?::\s*[\w$<>\[\]|]+)?\s*=\s*-?\d[\d_]*(?:\.\d+)?(?:\s*[*+/-]\s*\d[\d_]*(?:\.\d+)?)*\s*[;,\n]")),
    ("default-num", re.compile(r"(?:\?\?|\|\|)\s*-?\d[\d_]*(?:\.\d+)?\b")),
    ("threshold", re.compile(r"(?<![=!<>])(?:<=?|>=?)\s*-?\d{2,}[\d_]*(?:\.\d+)?\b|\b\d{2,}[\d_]*(?:\.\d+)?\s*(?:<=?|>=?)(?![=>])")),
    ("clamp", re.compile(r"\bMath\.(?:min|max)\s*\(|\bMath\.round\s*\([^)]*\*")),
]


def strip_js_comments(src):
    out, i, n = [], 0, len(src)
    quote = None
    while i < n:
        c = src[i]
        if quote:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(src[i + 1]); i += 2; continue
            if c == quote:
                quote = None
            i += 1; continue
        if c in "\"'`":
            quote = c; out.append(c); i += 1; continue
        if src.startswith("//", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src.startswith("/*", i):
            j = src.find("*/", i + 2); seg = src[i:(n if j < 0 else j + 2)]
            out.append("\n" * seg.count("\n")); i = n if j < 0 else j + 2; continue
        out.append(c); i += 1
    return "".join(out)


def host_files():
    files = subprocess.check_output(["git", "-C", ROOT, "ls-files", HOST_DIR], text=True).split()
    files = [f for f in files if re.search(r"\.(ts|mjs|js)$", f) and not NOT_RUNTIME.search(f)]
    if not files:
        sys.exit("foafnaut-host-policy-audit: no host files found; refusing an empty walk")
    return sorted(files)


def sites(rel):
    text = strip_js_comments(open(os.path.join(ROOT, rel), encoding="utf-8").read())
    found = []
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, pat in PATTERNS:
            for m in pat.finditer(line + "\n" if kind == "const-num" else line):
                value = re.sub(r"^.*?=\s*", "", m.group(0)).strip(" ;,\n") if kind == "const-num" else ""
                if kind == "const-num" and value in ("0", "1", "-1"):
                    continue  # a counter or index start, not a policy
                found.append((lineno, kind, line.strip()[:140]))
    return found


def read_allow():
    entries, max_total = {}, None
    if not os.path.exists(ALLOW):
        return entries, max_total, []
    lines = open(ALLOW, encoding="utf-8").read().split("\n")
    for line in lines:
        m = re.match(r"#\s*max-total:\s*(\d+)", line)
        if m:
            max_total = int(m.group(1))
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = re.match(r"^(\S+)\s+sites=(\d+)\s*(?:#\s*(.*))?$", line)
        if not m:
            entries.setdefault("__bad__", []).append(line)
            continue
        entries[m.group(1)] = (int(m.group(2)), (m.group(3) or "").strip())
    return entries, max_total, lines


def check():
    files = host_files()
    entries, max_total, _ = read_allow()
    errors = []
    for bad in entries.pop("__bad__", []):
        errors.append(f"cannot read line: {bad}")
    total = 0
    for f in files:
        n = len(sites(f))
        total += n
        if f not in entries:
            if n:
                errors.append(f"{f}: {n} policy sites and no line in {os.path.relpath(ALLOW, ROOT)}")
            continue
        want, reason = entries[f]
        if not reason or reason.startswith("TO REVIEW"):
            errors.append(f"{f}: the line has no reason")
        if n > want:
            errors.append(f"{f}: {n} policy sites, more than the {want} recorded (a new host decision: move it to Lean, or record it with a reason)")
        elif n < want:
            errors.append(f"{f}: {n} policy sites, fewer than the {want} recorded (lower the count: the ratchet only goes down)")
    for f in entries:
        if f not in files:
            errors.append(f"{f}: listed, but not a host runtime file now (remove the line)")
    if max_total is None:
        errors.append("the allow list has no `# max-total:` line")
    elif total > max_total:
        errors.append(f"{total} policy sites in all, more than max-total {max_total}")
    elif total < max_total:
        errors.append(f"{total} policy sites in all, fewer than max-total {max_total} (lower it)")
    for e in errors:
        print("foafnaut-host-policy: FAIL " + e)
    print(f"foafnaut-host-policy: {len(files)} host runtime files, {total} policy sites, {len(errors)} errors")
    return 1 if errors else 0


def record():
    files = host_files()
    entries, _, lines = read_allow()
    entries.pop("__bad__", None)
    header = [l for l in lines if l.startswith("#") and not l.startswith("# max-total:")]
    counts = {f: len(sites(f)) for f in files}
    total = sum(counts.values())
    out = header + [f"# max-total: {total}"]
    for f in files:
        if counts[f] == 0 and f not in entries:
            continue
        reason = entries.get(f, (0, "TO REVIEW"))[1] or "TO REVIEW"
        out.append(f"{f} sites={counts[f]}  # {reason}")
    open(ALLOW, "w", encoding="utf-8").write("\n".join(out) + "\n")
    print(f"recorded {len(out) - len(header) - 1} files, {total} sites")
    return 0


def main(argv):
    if not argv:
        return check()
    if argv[0] == "--list":
        rows = [(len(sites(f)), f) for f in host_files()]
        for n, f in sorted(rows, reverse=True):
            print(f"{n:5d}  {f}")
        print(f"{sum(n for n, _ in rows):5d}  total")
        return 0
    if argv[0] == "--sites":
        for lineno, kind, text in sites(argv[1]):
            print(f"{argv[1]}:{lineno}  {kind:11s} {text}")
        return 0
    if argv[0] == "--record":
        return record()
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
