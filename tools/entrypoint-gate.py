#!/usr/bin/env python3
"""The entry-point gate (https://github.com/danbri/factoidal/issues/975, item 3).

Every shipped entry point must map to a registered dataflow stage. The gate
enumerates the entry points from the tree on every run:

  npm   the subpaths of npm/factoidal/package.json "exports", and the named
        exports of each subpath's entry files (ES module `export` forms;
        CommonJS `module.exports = {...}` or `= require('./x')`). A subpath
        whose target is not a script (package.json, l4-assets/*) is one
        entry. Ids: `npm:<subpath>#<name>`, or `npm:<subpath>`.
  wasm  the op names of the Lean dispatch: the string literals of every
        `def ...OpNames... : List String` (or `opNames`) in formal/lean4/Wasm/*.lean and
        Wasm/Ops/*.lean, and the `| "op" =>` arms of Wasm/Dispatch.lean and
        Wasm/CoreDispatch.lean. Ids: `wasm:<op>`.
  cli   the keys of `const COMMANDS = {...}` in npm/factoidal/bin/factoidal.mjs.
        Ids: `cli:<command>`.

and reads the stages from docs/dataflow-inventory.md (generated from
formal/lean4/L4Factoidal/Dataflow/Registry.lean; tests/dataflow/run.sh checks
it is current). A stage is named by its `stage` cell, or by its `area` cell
when the entry has no stage declaration.

foundation/entrypoints.toml maps entry ids to stages ([[entry]]: id, stages,
covers = "whole" | "part", note) or marks them as running no stage
([[nonstage]]: id, reason). An npm export that is a literal constant
(`export const X = 1 | '...' | [...] | {...} | Object.freeze(...)`) or an
Error subclass is a nonstage export without a mapping line.

The gate fails (exit 1) when an enumeration is empty; an entry has no
mapping and is not in foundation/unbound-entrypoints.txt; a mapping names an
entry that does not exist, a stage that does not exist, or a stage whose
status is "missing"; or the unbound list names an entry that does not exist
or is mapped, or has more or fewer entries than its `# max-entries: N`
header (the ratchet).

Usage: python3 -I tools/entrypoint-gate.py [--root DIR] [--list]
"""
import argparse
import glob
import json
import os
import re
import sys
import tomllib

RANK = {"tested": 1, "assumed": 2, "proved": 3}


# ------------------------------------------------------------------ npm

def strip_js_comments(text):
    """Remove // and /* */ comments, keeping string and template literals."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c in "'\"`":
            j = i + 1
            while j < n and text[j] != c:
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


LITERAL_RE = re.compile(r"\s*(?:-?\d|['\"`\[{]|Object\.freeze\b|true\b|false\b|null\b)")


def module_exports(path, seen=None):
    """Return {name: kind} for one JS file; kind is 'value', 'error' or
    'callable'. 'value' and 'error' are the statically visible nonstage
    forms; everything else counts as callable."""
    seen = seen or set()
    if path in seen or not os.path.isfile(path):
        return {}
    seen.add(path)
    with open(path, encoding="utf-8") as fh:
        text = strip_js_comments(fh.read())
    names = {}
    for m in re.finditer(r"^export\s+(?:async\s+)?function\s*\*?\s*([A-Za-z_$][\w$]*)", text, re.M):
        names[m.group(1)] = "callable"
    for m in re.finditer(r"^export\s+class\s+([A-Za-z_$][\w$]*)(\s+extends\s+([\w$.]+))?", text, re.M):
        base = m.group(3) or ""
        names[m.group(1)] = "error" if base.endswith("Error") else "callable"
    for m in re.finditer(r"^export\s+(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=", text, re.M):
        names[m.group(1)] = "value" if LITERAL_RE.match(text, m.end()) else "callable"
    for m in re.finditer(r"^export\s*\{([^}]*)\}", text, re.M):
        for part in m.group(1).split(","):
            part = part.strip()
            if part:
                names[re.split(r"\s+as\s+", part)[-1].strip()] = "callable"
    if re.search(r"^export\s+default\b", text, re.M):
        names["default"] = "callable"
    for m in re.finditer(r"^export\s*\*\s*from\s*['\"]([^'\"]+)['\"]", text, re.M):
        names.update(module_exports(os.path.join(os.path.dirname(path), m.group(1)), seen))
    m = re.search(r"module\.exports\s*=\s*require\(\s*['\"]([^'\"]+)['\"]\s*\)", text)
    if m:
        names.update(module_exports(os.path.join(os.path.dirname(path), m.group(1)), seen))
    m = re.search(r"module\.exports\s*=\s*\{", text)
    if m:
        depth, i, start = 1, m.end(), m.end()
        while i < len(text) and depth:
            depth += {"{": 1, "}": -1}.get(text[i], 0)
            i += 1
        body, depth, cur, parts = text[start:i - 1], 0, "", []
        for ch in body:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            if ch == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += ch
        parts.append(cur)
        for p in parts:
            km = re.match(r"\s*([A-Za-z_$][\w$]*)", p)
            if km:
                names[km.group(1)] = "callable"
    for m in re.finditer(r"^(?:module\.)?exports\.([A-Za-z_$][\w$]*)\s*=", text, re.M):
        names[m.group(1)] = "callable"
    return names


def npm_entries(npm_dir):
    """Return {id: (kind, file)}."""
    with open(os.path.join(npm_dir, "package.json"), encoding="utf-8") as fh:
        pkg = json.load(fh)
    exports = pkg.get("exports") or {}
    out = {}
    for sub, target in exports.items():
        files = []
        if isinstance(target, str):
            files = [target]
        elif isinstance(target, dict):
            files = [v for k, v in target.items() if k != "types" and isinstance(v, str)]
        scripts = [f for f in dict.fromkeys(files)
                   if re.search(r"\.(m?js|cjs)$", f) and "*" not in f]
        if not scripts:
            out[f"npm:{sub}"] = ("callable", ", ".join(files))
            continue
        found = {}
        for f in scripts:
            for name, kind in module_exports(os.path.normpath(os.path.join(npm_dir, f))).items():
                found.setdefault(name, (kind, f))
        if not found:
            out[f"npm:{sub}"] = ("callable", ", ".join(scripts))
        for name, (kind, f) in found.items():
            out[f"npm:{sub}#{name}"] = (kind, f)
    return out


# ------------------------------------------------------------------ wasm

def wasm_entries(wasm_dir):
    out = {}
    paths = sorted(glob.glob(os.path.join(wasm_dir, "*.lean")) +
                   glob.glob(os.path.join(wasm_dir, "Ops", "*.lean")))
    for p in paths:
        if p.endswith("Tests.lean"):
            continue
        with open(p, encoding="utf-8") as fh:
            text = fh.read()
        rel = os.path.relpath(p, os.path.dirname(os.path.dirname(wasm_dir)))
        for m in re.finditer(r"^(?:private\s+)?def\s+(\w*[oO]pNames\w*)\s*:\s*List\s+String\s*:=(.*?)(?=^\S)",
                             text + "\nEND", re.S | re.M):
            for op in re.findall(r'"([A-Za-z0-9_]+)"', m.group(2)):
                out.setdefault(f"wasm:{op}", ("callable", rel))
        if os.path.basename(p) in ("Dispatch.lean", "CoreDispatch.lean"):
            for m in re.finditer(r'^\s*\|\s*((?:"[A-Za-z0-9_]+"\s*\|?\s*)+)=>', text, re.M):
                for op in re.findall(r'"([A-Za-z0-9_]+)"', m.group(1)):
                    out.setdefault(f"wasm:{op}", ("callable", rel))
    return out


# ------------------------------------------------------------------ cli

def cli_entries(cli_path):
    out = {}
    if not os.path.isfile(cli_path):
        return out
    with open(cli_path, encoding="utf-8") as fh:
        text = strip_js_comments(fh.read())
    m = re.search(r"const\s+COMMANDS\s*=\s*\{(.*?)^\}", text, re.S | re.M)
    if not m:
        return out
    for km in re.finditer(r"^\s*(?:'([^']+)'|\"([^\"]+)\"|([A-Za-z_$][\w$-]*))\s*:", m.group(1), re.M):
        name = km.group(1) or km.group(2) or km.group(3)
        out[f"cli:{name}"] = ("callable", "npm/factoidal/bin/factoidal.mjs")
    return out


# ------------------------------------------------------------------ registry

def registry_stages(inventory_path, errors):
    """{key: status}; key = stage name, or area when the entry has none."""
    stages = {}
    with open(inventory_path, encoding="utf-8") as fh:
        for line in fh:
            if not line.startswith("| ") or line.startswith("| area ") or line.startswith("|---"):
                continue
            cells = [c.strip().replace("\\|", "|")
                     for c in re.split(r"(?<!\\)\|", line.strip())[1:-1]]
            if len(cells) != 11:
                errors.append(f"{inventory_path}: row with {len(cells)} cells: {line.strip()[:80]}")
                continue
            area, stage, status = cells[0], cells[2].strip("`"), cells[6]
            key = area if stage in ("", "-") else stage
            if key in stages:
                errors.append(f"{inventory_path}: stage key {key!r} appears twice")
            stages[key] = status
    return stages


def read_unbound(path, errors):
    max_entries, ids = None, {}
    if not os.path.exists(path):
        errors.append(f"{path}: unbound list missing")
        return 0, ids
    with open(path, encoding="utf-8") as fh:
        for no, raw in enumerate(fh, 1):
            s = raw.strip()
            m = re.match(r"#\s*max-entries:\s*(\d+)\s*$", s)
            if m:
                max_entries = int(m.group(1))
                continue
            if not s or s.startswith("#"):
                continue
            eid = s.split()[0]  # an id has no spaces; text after it is a comment
            if eid in ids:
                errors.append(f"{path}:{no}: {eid}: listed twice")
            ids[eid] = no
    if max_entries is None:
        errors.append(f"{path}: no '# max-entries: N' header")
        max_entries = len(ids)
    return max_entries, ids


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--list", action="store_true", help="print every entry id and its disposition")
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root)
    errors = []

    kinds = {
        "npm": npm_entries(os.path.join(root, "npm", "factoidal")),
        "wasm": wasm_entries(os.path.join(root, "formal", "lean4", "Wasm")),
        "cli": cli_entries(os.path.join(root, "npm", "factoidal", "bin", "factoidal.mjs")),
    }
    for k, v in kinds.items():
        if not v:
            errors.append(f"{k}: no entry points found (empty enumeration)")
    entries = {eid: info for v in kinds.values() for eid, info in v.items()}

    stages = registry_stages(os.path.join(root, "docs", "dataflow-inventory.md"), errors)
    if not stages:
        errors.append("docs/dataflow-inventory.md: no registry stages found")

    mapping_path = os.path.join(root, "foundation", "entrypoints.toml")
    with open(mapping_path, "rb") as fh:
        mapping = tomllib.load(fh)
    bound, nonstage = {}, {}
    for e in mapping.get("entry", []):
        eid, sts = e.get("id", ""), e.get("stages", [])
        if eid in bound or eid in nonstage:
            errors.append(f"{eid}: mapped twice in {mapping_path}")
        if eid not in entries:
            errors.append(f"{eid}: mapped, but no such entry point in the tree")
        if not sts:
            errors.append(f"{eid}: mapping has no stages")
        if e.get("covers") not in ("whole", "part"):
            errors.append(f"{eid}: covers must be 'whole' or 'part'")
        worst = 3
        for s in sts:
            if s not in stages:
                errors.append(f"{eid}: stage {s} is not in the registry (docs/dataflow-inventory.md)")
                continue
            if stages[s] == "missing":
                errors.append(f"{eid}: stage {s} has status missing; a shipped entry may not map to it")
                continue
            worst = min(worst, RANK.get(stages[s], 0))
        bound[eid] = (worst, e.get("covers"))
    for e in mapping.get("nonstage", []):
        eid = e.get("id", "")
        if eid in bound or eid in nonstage:
            errors.append(f"{eid}: mapped twice in {mapping_path}")
        if eid not in entries:
            errors.append(f"{eid}: mapped, but no such entry point in the tree")
        if not str(e.get("reason", "")).strip():
            errors.append(f"{eid}: nonstage entry has no reason")
        nonstage[eid] = e.get("reason", "")
    auto = {eid for eid, (kind, _) in entries.items()
            if kind in ("value", "error") and eid not in bound and eid not in nonstage}

    unbound_path = os.path.join(root, "foundation", "unbound-entrypoints.txt")
    max_entries, unbound = read_unbound(unbound_path, errors)
    for eid in sorted(unbound):
        if eid not in entries:
            errors.append(f"{eid}: listed as unbound, but no such entry point; remove it and lower max-entries")
        elif eid in bound or eid in nonstage or eid in auto:
            errors.append(f"{eid}: listed as unbound, but it is mapped; remove it and lower max-entries")
    for eid in sorted(entries):
        if eid not in bound and eid not in nonstage and eid not in auto and eid not in unbound:
            errors.append(f"{eid}: no stage mapping and not in foundation/unbound-entrypoints.txt "
                          f"({entries[eid][1]})")
    if len(unbound) != max_entries:
        errors.append(f"{unbound_path}: unbound list has {len(unbound)} entries, max-entries is "
                      f"{max_entries} (the list may only shrink; lower the header with it)")

    if args.list:
        for eid in sorted(entries):
            d = ("bound" if eid in bound else "nonstage" if eid in nonstage or eid in auto
                 else "unbound" if eid in unbound else "UNLISTED")
            print(f"{d}\t{eid}\t{entries[eid][1]}")

    def counts(ids):
        b = [bound[i] for i in ids if i in bound]
        return (len(ids), len(b), sum(1 for w, _ in b if w == 3), sum(1 for w, _ in b if w == 1),
                sum(1 for w, _ in b if w == 2), sum(1 for _, c in b if c == "part"),
                sum(1 for i in ids if i in nonstage or i in auto),
                sum(1 for i in ids if i in unbound))
    total = counts(list(entries))
    per = "; ".join(f"{k} {len(v)}: {counts(list(v))[1]} bound, {counts(list(v))[6]} nonstage, "
                    f"{counts(list(v))[7]} unbound" for k, v in kinds.items())
    summary = (f"entry-point gate: {total[0]} entry points: {total[1]} bound (proved {total[2]}, "
               f"tested {total[3]}, assumed {total[4]}; {total[5]} part), {total[6]} nonstage, "
               f"{total[7]} unbound. By kind: {per}")
    if errors:
        for e in errors:
            print("ERROR " + e)
        print(summary + f"; {len(errors)} errors")
        return 1
    print(summary + "; pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
