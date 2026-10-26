#!/usr/bin/env python3
"""The FOUNDATION gate (https://github.com/danbri/factoidal/issues/975, item 1).

Reads `foundation/manifest.toml` and the leading `import` lines of every
`.lean` file under `<source_root>/L4Factoidal`. No Lean build is needed.

It fails (exit 1) when:
  * a module listed in the manifest has no file;
  * a foundation module imports an L4Factoidal module that is not in the
    manifest ("impl": the specification depends on an implementation);
  * a level-k foundation module imports a foundation module of level > k
    ("level");
  * a violation is not in `foundation/allow-imports.txt`;
  * the allow list names an edge that is no longer a violation ("stale"),
    has an entry with no reason, or has more or fewer entries than its
    `# max-entries: N` header (the ratchet).

Imports outside `L4Factoidal.` (Lean core, Std, Mathlib) are allowed.
The inputs come from the tree on every run; an empty walk is a failure.

Usage: python3 -I tools/foundation-gate.py [--root DIR]
"""
import argparse
import os
import re
import sys
import tomllib

PKG = "L4Factoidal"
IMPORT_RE = re.compile(r"import\s+([A-Za-z0-9_.']+)")


def leading_imports(text):
    """The (module, line) pairs of the import block at the start of a Lean
    file. Line comments and nested block comments are skipped; the block
    ends at the first token that is not `import`."""
    i, n, line, out = 0, len(text), 1, []
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif c.isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    if text[i] == "\n":
                        line += 1
                    i += 1
        else:
            m = IMPORT_RE.match(text, i)
            if not m:
                break
            out.append((m.group(1), line))
            i = m.end()
    return out


def walk_sources(lean_root):
    """Map module name -> (relative path, [(import, line)])."""
    mods = {}
    base = os.path.join(lean_root, PKG)
    for d, dirs, files in os.walk(base):
        dirs.sort()
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            name = os.path.relpath(p, lean_root)[: -len(".lean")].replace(os.sep, ".")
            with open(p, encoding="utf-8") as fh:
                mods[name] = (p, leading_imports(fh.read()))
    return mods


def read_allow(path, errors):
    """Return (max_entries, {(src, dst): reason})."""
    max_entries, entries = None, {}
    if not os.path.exists(path):
        errors.append(f"{path}: allow list missing")
        return 0, entries
    with open(path, encoding="utf-8") as fh:
        for no, raw in enumerate(fh, 1):
            s = raw.strip()
            if not s:
                continue
            m = re.match(r"#\s*max-entries:\s*(\d+)\s*$", s)
            if m:
                max_entries = int(m.group(1))
                continue
            if s.startswith("#"):
                continue
            edge, _, reason = s.partition("#")
            parts = [x.strip() for x in edge.split("->")]
            if len(parts) != 2 or not all(parts):
                errors.append(f"{path}:{no}: cannot read entry {s!r} (want 'A -> B  # reason')")
                continue
            key = (parts[0], parts[1])
            if not reason.strip():
                errors.append(f"{path}:{no}: {key[0]} -> {key[1]}: no reason")
            if key in entries:
                errors.append(f"{path}:{no}: {key[0]} -> {key[1]}: listed twice")
            entries[key] = reason.strip()
    if max_entries is None:
        errors.append(f"{path}: no '# max-entries: N' header")
        max_entries = len(entries)
    return max_entries, entries


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root)
    manifest_path = os.path.join(root, "foundation", "manifest.toml")
    allow_path = os.path.join(root, "foundation", "allow-imports.txt")
    errors = []

    with open(manifest_path, "rb") as fh:
        manifest = tomllib.load(fh)
    head = manifest.get("manifest", {})
    if head.get("version") is None:
        errors.append(f"{manifest_path}: [manifest] has no version")
    lean_root = os.path.join(root, head.get("source_root", "formal/lean4"))

    level_of, spec_of = {}, {}
    for entry in manifest.get("module", []):
        name, level, spec = entry.get("name"), entry.get("level"), entry.get("spec")
        if not name:
            errors.append(f"{manifest_path}: a [[module]] has no name")
            continue
        if not isinstance(level, int) or not 0 <= level <= 3:
            errors.append(f"{manifest_path}: {name}: level {level} is not 0, 1, 2 or 3")
            continue
        if not spec:
            errors.append(f"{manifest_path}: {name}: no spec citation")
        if name in level_of:
            errors.append(f"{manifest_path}: {name}: listed twice")
        level_of[name], spec_of[name] = level, spec
    if not level_of:
        errors.append(f"{manifest_path}: no modules listed")

    sources = walk_sources(lean_root)
    if not sources:
        errors.append(f"{lean_root}/{PKG}: no .lean files found (empty walk)")

    violations = {}  # (src, dst) -> message
    for name in sorted(level_of):
        if name not in sources:
            if sources:
                errors.append(f"{name}: listed in the manifest, no file under {lean_root}")
            continue
        path, imports = sources[name]
        rel = os.path.relpath(path, root)
        for dst, line in imports:
            if not dst.startswith(PKG + "."):
                continue
            if dst not in level_of:
                violations[(name, dst)] = (
                    f"{rel}:{line}: impl: {name} -> {dst} "
                    f"(a foundation module imports a module outside the foundation)")
            elif level_of[dst] > level_of[name]:
                violations[(name, dst)] = (
                    f"{rel}:{line}: level: {name} -> {dst} "
                    f"(level {level_of[name]} imports level {level_of[dst]})")

    max_entries, allow = read_allow(allow_path, errors)
    for key in sorted(violations):
        if key not in allow:
            errors.append(violations[key] + " -- not in foundation/allow-imports.txt")
    for key in sorted(allow):
        if key not in violations:
            errors.append(f"{allow_path}: stale entry {key[0]} -> {key[1]}: "
                          f"no longer a violation; remove it and lower max-entries")
    if len(allow) != max_entries:
        errors.append(f"{allow_path}: allow list has {len(allow)} entries, max-entries is "
                      f"{max_entries} (the list may only shrink; lower the header with it)")

    counts = [sum(1 for v in level_of.values() if v == k) for k in range(4)]
    kinds = {"impl": 0, "level": 0}
    for msg in violations.values():
        kinds[msg.split(": ", 2)[1]] += 1
    if args.verbose:
        for key in sorted(violations):
            print("allowed: " + violations[key] if key in allow else violations[key])
    summary = (f"foundation gate: {len(level_of)} foundation modules "
               f"(level 0: {counts[0]}, level 1: {counts[1]}, level 2: {counts[2]}, "
               f"level 3: {counts[3]}); {len(sources)} Lean files read; "
               f"{len(violations)} import violations ({kinds['impl']} impl, "
               f"{kinds['level']} level), {len(allow)} allowed")
    if errors:
        for e in errors:
            print("ERROR " + e)
        print(summary + f"; {len(errors)} errors")
        return 1
    print(summary + "; pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
