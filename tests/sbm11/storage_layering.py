#!/usr/bin/env python3
"""Layering gate of the source layer (owner, 2026-10-14,
https://github.com/danbri/factoidal/issues/837): no module under
formal/lean4/L4Factoidal/Storage/ imports an L4Factoidal.Syntax module, and none
names one in its code. The store takes RDF quads from L4Factoidal.RDF.Source and
does not know a concrete syntax.

The producer interface of the packer, formal/lean4/L4Factoidal/RDF/QuadSource.lean
(https://github.com/danbri/factoidal/issues/866), is held to the same rule: it imports
no Syntax module and names none, so that a module under Storage/ can take it.

Usage: storage_layering.py [STORAGE_DIR]
Prints one line per violation and a count. Exit 0 when there is none, 1 when
there is one, 2 when the directory has no .lean file or the producer interface is
missing (an empty walk is not a pass, anti-pattern 28)."""
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else
                    pathlib.Path(__file__).resolve().parents[2] / "formal/lean4/L4Factoidal/Storage")
files = sorted(root.rglob("*.lean"))
if not files:
    print(f"no .lean file under {root}", file=sys.stderr)
    sys.exit(2)
producer = root.parent / "RDF" / "QuadSource.lean"
if not producer.exists():
    print(f"the producer interface {producer} is missing", file=sys.stderr)
    sys.exit(2)
files.append(producer)


def code_only(text: str) -> str:
    """The text with Lean block comments (nested) and line comments blanked,
    string literals kept. Line structure is kept, so line numbers stay."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif two == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and two == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth == 0 and two == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(text[i] if (depth == 0 or text[i] == "\n") else " ")
            i += 1
    return "".join(out)


bad = []
for f in files:
    text = f.read_text(encoding="utf-8")
    for no, line in enumerate(text.splitlines(), 1):
        if re.match(r"\s*import\s+L4Factoidal\.Syntax\b", line):
            bad.append(f"{f.relative_to(root.parent.parent)}:{no}: import {line.split()[1]}")
    for no, line in enumerate(code_only(text).splitlines(), 1):
        if re.search(r"\bL4Factoidal\.Syntax\b", line) or re.match(r"\s*open\s+(.*\s)?Syntax\b", line):
            bad.append(f"{f.relative_to(root.parent.parent)}:{no}: names a Syntax module in code: {line.strip()[:80]}")
for b in bad:
    print(b)
print(f"storage layering: {len(files)} files read, {len(bad)} violations")
sys.exit(1 if bad else 0)
