#!/usr/bin/env python3
"""The RUNNERS gate (https://github.com/danbri/factoidal/issues/1002).

npm/factoidal/lib/nodes.mjs holds a hand-written table `RUNNERS`: stage name
-> the function that runs the stage. This gate checks the table on every run,
from the tree (no cached lists):

  1. each RUNNERS key is a stage name in docs/dataflow-inventory.md (a stage
     is named by its `stage` cell, or by its `area` cell when the entry has no
     stage declaration);
  2. each RUNNERS entry calls at least one package function (a name from the
     `const { ... } = deps` list of buildNodes, resolved through the local
     helper factories such as `reader(...)`) or wasm op (`e.<op>(`), and every
     one it calls is an entry in foundation/entrypoints.toml (`npm:.#<fn>` or
     `wasm:<op>`) whose stage list contains the key.

An entry that calls no package function or wasm op fails (nothing shows what
it runs). An empty RUNNERS table, an empty inventory, or an empty mapping
fails.

nodes.mjs may also hold a table `PORT_RUNNERS`: a stage with more than one
input port (a port stage, https://github.com/danbri/factoidal/issues/1130) ->
the function that runs it. A port stage is not a registry entry. The gate
checks: 3. each PORT_RUNNERS key is a name of the Lean list `portStageNames`
(formal/lean4/Wasm/Ops/GraphNodes.lean, read on every run; an absent or empty
list fails when PORT_RUNNERS is present); 4. each PORT_RUNNERS entry calls at
least one package function or wasm op, and every one it calls is an [[entry]]
in foundation/entrypoints.toml.

Usage: python3 -I tools/runners-gate.py [--root DIR]
"""
import argparse
import importlib.util
import os
import re
import sys
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))


def text_of(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()
_spec = importlib.util.spec_from_file_location("entrypoint_gate", os.path.join(HERE, "entrypoint-gate.py"))
eg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(eg)

# Names in the deps list that are engine plumbing, not package functions.
PLUMBING = {"entry", "entryResult", "requireEntryFn", "Dataset"}


def balanced(text, i, open_ch, close_ch):
    """Index just past the group opened at text[i]."""
    depth, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in "'\"`":
            j = i + 1
            while j < n and text[j] != c:
                j += 2 if text[j] == "\\" else 1
            i = j
        elif c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return -1


def split_top(body):
    """Split a table body at top-level commas."""
    parts, depth, cur, i, n = [], 0, "", 0, len(body)
    while i < n:
        c = body[i]
        if c in "'\"`":
            j = i + 1
            while j < n and body[j] != c:
                j += 2 if body[j] == "\\" else 1
            cur += body[i:j + 1]
            i = j + 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
        i += 1
    parts.append(cur)
    return [p for p in parts if p.strip()]


def parse_table(text, name, errors):
    """{key: body} of `const <name> = { ... }`, or None when there is none."""
    rm = re.search(r"const\s+" + name + r"\s*=\s*\{", text)
    if not rm:
        return None
    start = rm.end() - 1
    end = balanced(text, start, "{", "}")
    if end < 0:
        errors.append(f"nodes.mjs: {name} table is not balanced")
        return {}
    out = {}
    for part in split_top(text[start + 1:end - 1]):
        km = re.match(r"\s*(?:'([^']+)'|\"([^\"]+)\"|([A-Za-z_$][\w$]*))\s*:", part)
        if not km:
            errors.append(f"nodes.mjs: cannot read a {name} entry: {part.strip()[:60]!r}")
            continue
        key = km.group(1) or km.group(2) or km.group(3)
        if key in out:
            errors.append(f"nodes.mjs: {name} key {key} appears twice")
        out[key] = part[km.end():]
    return out


def port_stage_names(path, errors):
    """The string literals of `def portStageNames : List String := [...]`."""
    if not os.path.isfile(path):
        errors.append(f"{path}: missing (the Lean list portStageNames)")
        return set()
    with open(path, encoding="utf-8") as fh:
        text = fh.read()
    m = re.search(r"^def\s+portStageNames\s*:\s*List\s+String\s*:=\s*\[(.*?)\]", text, re.S | re.M)
    if not m:
        errors.append(f"{path}: no `def portStageNames : List String := [...]`")
        return set()
    names = set(re.findall(r'"([^"]+)"', m.group(1)))
    if not names:
        errors.append(f"{path}: portStageNames is empty (empty enumeration)")
    return names


def parse_nodes(text, errors):
    """Return (runners {key: body}, deps set, helpers {name: body})."""
    text = eg.strip_js_comments(text)
    m = re.search(r"const\s*\{([^}]*)\}\s*=\s*deps\s*;", text)
    deps = set()
    if m:
        deps = {d.split(":")[-1].strip() for d in m.group(1).split(",") if d.strip()} - PLUMBING
    else:
        errors.append("nodes.mjs: no `const { ... } = deps;` list found")
    helpers = {}
    for hm in re.finditer(r"^([ \t]*)const\s+(\w+)\s*=\s*\(\w*\)\s*=>", text, re.M):
        # helper factory: runs to the next declaration at the same indentation
        end = re.search(r"^" + hm.group(1) + r"(?:const|let|function|async function)\s",
                        text[hm.end():], re.M)
        helpers[hm.group(2)] = text[hm.end():hm.end() + (end.start() if end else 0)]
    rm = re.search(r"const\s+RUNNERS\s*=\s*\{", text)
    runners = {}
    if not rm:
        errors.append("nodes.mjs: no `const RUNNERS = {` table found")
        return runners, deps, helpers
    start = rm.end() - 1
    end = balanced(text, start, "{", "}")
    if end < 0:
        errors.append("nodes.mjs: RUNNERS table is not balanced")
        return runners, deps, helpers
    for part in split_top(text[start + 1:end - 1]):
        km = re.match(r"\s*(?:'([^']+)'|\"([^\"]+)\"|([A-Za-z_$][\w$]*))\s*:", part)
        if not km:
            errors.append(f"nodes.mjs: cannot read a RUNNERS entry: {part.strip()[:60]!r}")
            continue
        key = km.group(1) or km.group(2) or km.group(3)
        if key in runners:
            errors.append(f"nodes.mjs: RUNNERS key {key} appears twice")
        runners[key] = part[km.end():]
    return runners, deps, helpers


def called_targets(body, deps, helpers, seen=()):
    """Package functions (`npm:.#f`) and wasm ops (`wasm:op`) a body calls."""
    out = set()
    for m in re.finditer(r"(?<![\w$.])([A-Za-z_$][\w$]*)\s*\(", body):
        name = m.group(1)
        if name in deps:
            out.add(f"npm:.#{name}")
        elif name in helpers and name not in seen:
            out |= called_targets(helpers[name], deps, helpers, seen + (name,))
    for m in re.finditer(r"(?<![\w$])e\.([A-Za-z_$][\w$]*)\s*\(", body):
        out.add(f"wasm:{m.group(1)}")
    return out


def check(root):
    errors = []
    nodes_path = os.path.join(root, "npm", "factoidal", "lib", "nodes.mjs")
    with open(nodes_path, encoding="utf-8") as fh:
        runners, deps, helpers = parse_nodes(fh.read(), errors)
    if not runners:
        errors.append("nodes.mjs: RUNNERS is empty (empty enumeration)")
    stages = eg.registry_stages(os.path.join(root, "docs", "dataflow-inventory.md"), errors)
    if not stages:
        errors.append("docs/dataflow-inventory.md: no registry stages found")
    with open(os.path.join(root, "foundation", "entrypoints.toml"), "rb") as fh:
        mapping = tomllib.load(fh)
    stage_of = {e.get("id", ""): set(e.get("stages", [])) for e in mapping.get("entry", [])}
    if not stage_of:
        errors.append("foundation/entrypoints.toml: no [[entry]] mappings")
    for key, body in runners.items():
        if key not in stages:
            errors.append(f"RUNNERS.{key}: not a stage in docs/dataflow-inventory.md")
        targets = called_targets(body, deps, helpers)
        if not targets:
            errors.append(f"RUNNERS.{key}: calls no package function or wasm op; nothing shows what it runs")
        for t in sorted(targets):
            if t not in stage_of:
                errors.append(f"RUNNERS.{key}: calls {t}, which has no [[entry]] in foundation/entrypoints.toml")
            elif key not in stage_of[t]:
                errors.append(f"RUNNERS.{key}: calls {t}, whose mapped stages "
                              f"({', '.join(sorted(stage_of[t]))}) do not include {key}")
    ports = parse_table(eg.strip_js_comments(text_of(nodes_path)), "PORT_RUNNERS", errors)
    if ports is not None:
        names = port_stage_names(os.path.join(root, "formal", "lean4", "Wasm", "Ops", "GraphNodes.lean"), errors)
        for key, body in ports.items():
            if names and key not in names:
                errors.append(f"PORT_RUNNERS.{key}: not a name of portStageNames (formal/lean4/Wasm/Ops/GraphNodes.lean)")
            targets = called_targets(body, deps, helpers)
            if not targets:
                errors.append(f"PORT_RUNNERS.{key}: calls no package function or wasm op; nothing shows what it runs")
            for t in sorted(targets):
                if t not in stage_of:
                    errors.append(f"PORT_RUNNERS.{key}: calls {t}, which has no [[entry]] in foundation/entrypoints.toml")
    return errors, (len(runners), len(ports) if ports else 0)


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(HERE, ".."))
    args = ap.parse_args(argv)
    errors, (n, n_ports) = check(os.path.abspath(args.root))
    for e in errors:
        print("ERROR " + e)
    if errors:
        print(f"runners gate: {n} RUNNERS keys, {n_ports} PORT_RUNNERS keys; {len(errors)} errors")
        return 1
    print(f"runners gate: {n} RUNNERS keys, each a registry stage that calls only entries mapped to it; "
          f"{n_ports} PORT_RUNNERS keys, each in portStageNames and calling only mapped entries; pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
