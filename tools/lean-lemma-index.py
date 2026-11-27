#!/usr/bin/env python3
"""Search the Lean tree's theorems and definitions before you write a new one
(https://github.com/danbri/factoidal-core/issues/1187, P10).

Reason: in https://www.anthropic.com/research/formal-verification agents that
shared proofs used 17% fewer tokens; here, two sessions wrote the same
`escapeString` fast form on 2026-10-13 (CLAUDE.md). The index is built from the
tree on every run (anti-pattern 30); nothing is cached. It needs no Lean build,
so it works where `lean_local_search` has no language server.

Each entry: fully qualified name, kind (theorem, def, structure, ...), file and
line, and the statement (for a theorem) or the signature (for a definition),
comments removed.

Usage:
  python3 -I tools/lean-lemma-index.py QUERY [QUERY ...]   entries whose name
      or statement matches every QUERY (Python regular expressions, case
      insensitive); at most 40 lines unless --all
  python3 -I tools/lean-lemma-index.py --kind theorem escape
  python3 -I tools/lean-lemma-index.py --out FILE          write all entries as
      JSON lines (for an agent's own search)
"""
import importlib.util
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "formal", "lean4")
SKIP = {".lake", ".wasm-work", "build"}

_spec = importlib.util.spec_from_file_location("claims_gate", os.path.join(ROOT, "tools", "claims-gate.py"))
_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gate)


def entries():
    n = 0
    for dp, dns, fs in os.walk(SRC):
        dns[:] = [d for d in dns if d not in SKIP]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dp, f)
            rel = os.path.relpath(path, ROOT)
            for name, hits in _gate.declarations(path).items():
                for kw, mods, text, line in hits:
                    if kw == "example":
                        continue
                    n += 1
                    yield {"name": name, "kind": kw, "private": "private" in mods,
                           "file": rel, "line": line, "statement": _gate.statement_of(text)[:600]}
    if n == 0:
        sys.exit("lean-lemma-index: no declarations found; refusing an empty walk")


def main(argv):
    if "--out" in argv:
        out = argv[argv.index("--out") + 1]
        with open(out, "w", encoding="utf-8") as fh:
            k = 0
            for e in entries():
                fh.write(json.dumps(e, ensure_ascii=False) + "\n"); k += 1
        print(f"lean-lemma-index: {k} entries written to {out}")
        return 0
    kind = None
    if "--kind" in argv:
        i = argv.index("--kind"); kind = argv[i + 1]; argv = argv[:i] + argv[i + 2:]
    show_all = "--all" in argv
    queries = [re.compile(q, re.I) for q in argv if q != "--all"]
    if not queries:
        print(__doc__); return 2
    shown = matched = 0
    for e in entries():
        if kind and e["kind"] != kind:
            continue
        hay = e["name"] + " " + e["statement"]
        if all(q.search(hay) for q in queries):
            matched += 1
            if show_all or shown < 40:
                shown += 1
                print(f"{e['file']}:{e['line']}  {e['kind']}{' (private)' if e['private'] else ''}  {e['name']}\n    {e['statement'][:300]}")
    print(f"lean-lemma-index: {matched} matches" + ("" if show_all or matched <= 40 else f", 40 shown (--all for every one)"))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
