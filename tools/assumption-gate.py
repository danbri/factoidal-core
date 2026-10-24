#!/usr/bin/env python3
"""The named-assumption ratchet (https://github.com/danbri/factoidal/issues/975, item 4).

The interface types of the data-access and reader components carry the
assumptions their laws rest on as named fields:

  RdfReader     formal/lean4/L4Factoidal/Dataflow/Reader.lean; no assumption
                field (every reader law is proved);
  LawfulStore,  formal/lean4/L4Factoidal/Dataflow/Store.lean; the field
  LawfulDataset `assumed_contracts : List Assumption`, each with a name from
                `inductive AssumptionName`.

The gate reads, on every run:

  1. the constructors of `inductive AssumptionName` (Dataflow/Store.lean);
  2. for each constructor, the number of places in formal/lean4 (L4Factoidal,
     Wasm, Harness) that build an assumption with that name: `⟨.name,` or
     `⟨AssumptionName.name,` or `name := .name` in an `Assumption` literal.
     Comment lines are skipped;
  3. the interface structures: which of RdfReader, LawfulStore, LawfulDataset
     declare an `assumed_contracts` field (the `assumed_<what>` naming rule
     for unproved contract fields).

foundation/assumptions.txt lists one line per constructor:

  <name>  uses=<N>  # <reason it is not proved>

The gate fails (exit 1) when: the inductive is not found or has no
constructor; a constructor has no line; a line names no constructor; a line
has no reason; the `uses` count of a line differs from the count in the tree
(it may not grow, and a line that over-counts is stale); the number of lines
differs from the `# max-entries: N` header; RdfReader declares an assumption
field while the list has no line for it; or a file under formal/lean4/Wasm or
formal/lean4/Harness calls the backend evaluator over a bare dataset record
(`runSelectQueryBackendDataset`, `runAskQueryBackendDataset`,
`evalPatternBackend`, `evalBgpBackend`, `indexedDatasetBackend`) instead of a
`LawfulDataset` / `LawfulStore`.

Usage: python3 -I tools/assumption-gate.py [--root DIR]
"""
import argparse
import glob
import os
import re
import sys

STORE = "formal/lean4/L4Factoidal/Dataflow/Store.lean"
READER = "formal/lean4/L4Factoidal/Dataflow/Reader.lean"
LIST = "foundation/assumptions.txt"
SEARCH_DIRS = ["formal/lean4/L4Factoidal", "formal/lean4/Wasm", "formal/lean4/Harness"]
CONSUMER_DIRS = ["formal/lean4/Wasm", "formal/lean4/Harness"]
BARE_EVAL = ["runSelectQueryBackendDataset", "runAskQueryBackendDataset", "evalPatternBackend",
             "evalBgpBackend", "indexedDatasetBackend"]


def strip_lean_comments(text):
    """Remove `--` line comments and `/- ... -/` block comments (nesting)."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def constructors(store_text):
    m = re.search(r"inductive AssumptionName where(.*?)\n\s*deriving", store_text, re.S)
    if not m:
        return None
    return re.findall(r"^\s*\|\s*(\w+)", m.group(1), re.M)


def structure_has_field(text, name, field):
    m = re.search(r"structure %s\b[^\n]*where(.*?)(?:\n\S|\Z)" % re.escape(name), text, re.S)
    if not m:
        return None
    return re.search(r"^\s+%s\s*:" % re.escape(field), m.group(1), re.M) is not None


def lean_files(root, dirs):
    out = []
    for d in dirs:
        out += glob.glob(os.path.join(root, d, "**", "*.lean"), recursive=True)
    return sorted(out)


def count_uses(root, names):
    counts = {n: 0 for n in names}
    for p in lean_files(root, SEARCH_DIRS):
        text = strip_lean_comments(open(p, encoding="utf-8").read())
        for n in names:
            pat = r"(?:⟨\s*(?:AssumptionName)?\.%s\s*,|name\s*:=\s*(?:AssumptionName)?\.%s\b)" % (n, n)
            counts[n] += len(re.findall(pat, text))
    return counts


def bare_eval_calls(root):
    bad = []
    for p in lean_files(root, CONSUMER_DIRS):
        text = strip_lean_comments(open(p, encoding="utf-8").read())
        for k, line in enumerate(text.split("\n"), 1):
            for w in BARE_EVAL:
                if re.search(r"(?<![\w.`])(?:[\w.]*\.)?%s\b" % w, line):
                    bad.append("%s:%d: %s" % (os.path.relpath(p, root), k, w))
    return bad


def read_list(path):
    lines, header, errs = {}, None, []
    for k, raw in enumerate(open(path, encoding="utf-8"), 1):
        line = raw.rstrip("\n")
        h = re.match(r"#\s*max-entries:\s*(\d+)", line)
        if h:
            header = int(h.group(1))
            continue
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = re.match(r"^(\w+)\s+uses=(\d+)\s*(?:#\s*(.*))?$", line)
        if not m:
            errs.append("%s:%d: not '<name>  uses=<N>  # reason'" % (LIST, k))
            continue
        if not (m.group(3) or "").strip():
            errs.append("%s:%d: %s has no reason" % (LIST, k, m.group(1)))
        lines[m.group(1)] = int(m.group(2))
    return lines, header, errs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    root = ap.parse_args().root
    errs = []
    store_path = os.path.join(root, STORE)
    if not os.path.exists(store_path):
        print("assumption gate: %s not found" % STORE, file=sys.stderr)
        return 1
    store_text = strip_lean_comments(open(store_path, encoding="utf-8").read())
    names = constructors(store_text)
    if not names:
        print("assumption gate: no constructor of inductive AssumptionName in %s" % STORE, file=sys.stderr)
        return 1
    uses = count_uses(root, names)
    listed, header, lerrs = read_list(os.path.join(root, LIST))
    errs += lerrs
    for n in names:
        if n not in listed:
            errs.append("%s: assumption %s (uses=%d) has no line" % (LIST, n, uses[n]))
        elif listed[n] != uses[n]:
            errs.append("%s: %s uses=%d listed, %d in the tree%s" % (
                LIST, n, listed[n], uses[n],
                " (a new use: add it with a reason)" if uses[n] > listed[n] else " (stale: lower it)"))
    for n in listed:
        if n not in names:
            errs.append("%s: %s is not a constructor of AssumptionName" % (LIST, n))
    if header is None:
        errs.append("%s: no '# max-entries: N' header" % LIST)
    elif header != len(listed):
        errs.append("%s: max-entries %d, %d lines" % (LIST, header, len(listed)))
    ifaces = {}
    reader_path = os.path.join(root, READER)
    reader_text = strip_lean_comments(open(reader_path, encoding="utf-8").read()) if os.path.exists(reader_path) else ""
    ifaces["RdfReader"] = structure_has_field(reader_text, "RdfReader", "assumed_contracts")
    ifaces["LawfulStore"] = structure_has_field(store_text, "LawfulStore", "assumed_contracts")
    ifaces["LawfulDataset"] = structure_has_field(store_text, "LawfulDataset", "assumed_contracts")
    for k, v in ifaces.items():
        if v is None:
            errs.append("interface structure %s not found" % k)
    if ifaces.get("LawfulStore") is False or ifaces.get("LawfulDataset") is False:
        errs.append("LawfulStore and LawfulDataset must declare the field `assumed_contracts`")
    for b in bare_eval_calls(root):
        errs.append("%s: backend evaluator over a bare DatasetBackend; use LawfulDataset.runSelect / runAsk or LawfulStore" % b)
    total = sum(uses.values())
    fields = ", ".join("%s %s" % (k, "has" if v else "has no") for k, v in ifaces.items())
    if errs:
        for e in errs:
            print(e, file=sys.stderr)
        print("assumption gate: fail", file=sys.stderr)
        return 1
    print("assumption gate: %d named assumptions, %d uses (%s); interface assumption fields: %s; pass" % (
        len(names), total, ", ".join("%s %d" % (n, uses[n]) for n in names), fields))
    return 0


if __name__ == "__main__":
    sys.exit(main())
