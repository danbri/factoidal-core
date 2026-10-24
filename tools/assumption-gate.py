#!/usr/bin/env python3
"""The ASSUMPTION gate (https://github.com/danbri/factoidal/issues/975, item 4).

Counts the named assumptions in the tree and the registry rows that are
`proved`, and compares both with the ratchet files. No Lean build is needed;
it reads `docs/dataflow-inventory.md` (generated from the Lean registry and
checked against it by step 2 of tests/dataflow/run.sh, which runs before this
gate) and the `.lean` files under `formal/lean4/L4Factoidal`.

Two kinds of named assumption are counted:

  io:<Name>                  an IO assumption named in the "IO assumptions"
                             column of the inventory (an `IOStage`
                             `assumption` in the registry). Distinct names.
  field:<Module>.<Struct>.<name>
                             a structure or class field whose name starts
                             with `assumed_`. This is the naming rule for an
                             interface type (LawfulStore, LawfulEvaluator,
                             RdfWriter, SoundReasoner, LawfulValidator,
                             SoundChecker) whose contract is not yet proved:
                             the field holds the contract and is named
                             `assumed_<what>`. Found by regex over comment-
                             stripped source, because the registry does not
                             export interface-type fields.

It fails (exit 1) when:
  * a counted assumption has no line in `foundation/assumptions.txt`
    ("new assumption"; add a line with a reason in the same change);
  * a line names an assumption that no longer exists ("stale"; remove it and
    lower max-entries), or has no reason, or is listed twice;
  * the line count differs from the `# max-entries: N` header;
  * a stage pinned in `foundation/proved-stages.txt` is no longer `proved`
    in the inventory, and `foundation/assumptions.txt` has no
    `demoted:<stage>  # reason` line for it. A `demoted:` line whose stage is
    proved again is stale. `demoted:` lines count toward max-entries.
  * the walk is empty (no registry rows, no Lean files, no proved stages).

A proved stage that is not pinned yet is reported, not failed; pin it with
`--pin`, which rewrites foundation/proved-stages.txt from the inventory.

Usage: python3 -I tools/assumption-gate.py [--root DIR] [--pin] [--list]
"""
import argparse
import os
import re
import sys

PKG = "L4Factoidal"
ASSUMED_FIELD_RE = re.compile(r"^[ \t]*\(?[ \t]*(assumed_[A-Za-z0-9_']+)[ \t]*:", re.M)
DECL_RE = re.compile(r"^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*"
                     r"(?:structure|class)[ \t]+([A-Za-z0-9_.']+)", re.M)


def strip_lean_comments(text):
    """Remove `-- ...` and nested `/- ... -/` comments, keeping newlines."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
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
                        out.append("\n")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lean_fields(lean_root, errors):
    """{id: path} for every `assumed_*` field; also the number of files walked."""
    found, nfiles = {}, 0
    base = os.path.join(lean_root, PKG)
    for d, dirs, files in os.walk(base):
        dirs.sort()
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            nfiles += 1
            p = os.path.join(d, f)
            mod = os.path.relpath(p, lean_root)[: -len(".lean")].replace(os.sep, ".")
            with open(p, encoding="utf-8") as fh:
                text = strip_lean_comments(fh.read())
            decls = [(m.start(), m.group(1)) for m in DECL_RE.finditer(text)]
            for m in ASSUMED_FIELD_RE.finditer(text):
                owner = "?"
                for pos, name in decls:
                    if pos < m.start():
                        owner = name
                aid = f"field:{mod}.{owner}.{m.group(1)}"
                if aid in found:
                    errors.append(f"{aid}: declared twice")
                found[aid] = os.path.relpath(p, lean_root)
    return found, nfiles


def inventory_rows(path, errors):
    """[(key, status, [io assumption names])]; key = stage, or area when no stage."""
    rows = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if not line.startswith("| ") or line.startswith("| area ") or line.startswith("|---"):
                continue
            cells = [c.strip().replace("\\|", "|")
                     for c in re.split(r"(?<!\\)\|", line.strip())[1:-1]]
            if len(cells) != 11:
                errors.append(f"{path}: row with {len(cells)} cells: {line.strip()[:80]}")
                continue
            area, stage, status, io = cells[0], cells[2].strip("`"), cells[6], cells[8]
            key = area if stage in ("", "-") else stage
            names = [n.strip().strip("`") for n in io.split(",")]
            names = [n for n in names if n and n != "-"]
            rows.append((key, status, names))
    return rows


def read_ratchet(path, errors):
    """(max_entries, {id: line}); every id line needs a '# reason'."""
    max_entries, ids = None, {}
    if not os.path.isfile(path):
        errors.append(f"{path}: ratchet file missing")
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
            parts = re.split(r"\s+#\s*", s, maxsplit=1)
            aid = parts[0].strip()
            if len(parts) < 2 or not parts[1].strip():
                errors.append(f"{path}:{no}: {aid}: no reason (write 'id  # reason')")
            if aid in ids:
                errors.append(f"{path}:{no}: {aid}: listed twice")
            ids[aid] = no
    if max_entries is None:
        errors.append(f"{path}: no '# max-entries: N' header")
        max_entries = len(ids)
    return max_entries, ids


def read_pins(path, errors):
    pins = set()
    if not os.path.isfile(path):
        errors.append(f"{path}: pinned-stage file missing (run with --pin)")
        return pins
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            s = raw.split("#", 1)[0].strip()
            if s:
                pins.add(s)
    return pins


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--pin", action="store_true", help="rewrite foundation/proved-stages.txt")
    ap.add_argument("--list", action="store_true", help="print every counted assumption")
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root)
    errors = []

    inv_path = os.path.join(root, "docs", "dataflow-inventory.md")
    rows = inventory_rows(inv_path, errors) if os.path.isfile(inv_path) else []
    if not rows:
        errors.append(f"{inv_path}: no registry rows found (empty walk)")
    proved = {k for k, s, _ in rows if s == "proved"}
    if rows and not proved:
        errors.append("inventory: no proved stages found (empty walk)")

    found = {}
    for key, _, names in rows:
        for n in names:
            found.setdefault(f"io:{n}", f"stage {key}")
    fields, nfiles = lean_fields(os.path.join(root, "formal", "lean4"), errors)
    if nfiles == 0:
        errors.append("formal/lean4/L4Factoidal: no .lean files found (empty walk)")
    found.update(fields)

    pins_path = os.path.join(root, "foundation", "proved-stages.txt")
    if args.pin:
        with open(pins_path, "w", encoding="utf-8") as fh:
            fh.write("# Registry stages that are `proved`, pinned by tools/assumption-gate.py --pin.\n"
                     "# tools/assumption-gate.py fails when a pinned stage is no longer proved\n"
                     "# unless foundation/assumptions.txt has a 'demoted:<stage>' line with a reason.\n")
            for k in sorted(proved):
                fh.write(k + "\n")
        print(f"pinned {len(proved)} proved stages")
        return 1 if errors else 0
    pins = read_pins(pins_path, errors)

    ratchet_path = os.path.join(root, "foundation", "assumptions.txt")
    max_entries, listed = read_ratchet(ratchet_path, errors)

    demoted_now = {k for k in pins if k not in proved}
    for aid in sorted(found):
        if aid not in listed:
            errors.append(f"{aid}: new assumption ({found[aid]}); add '{aid}  # reason' to "
                          f"foundation/assumptions.txt and raise max-entries")
    for k in sorted(demoted_now):
        if f"demoted:{k}" not in listed:
            errors.append(f"{k}: was proved (foundation/proved-stages.txt) and is not now; "
                          f"restore the proof or add 'demoted:{k}  # reason'")
    for aid in sorted(listed):
        if aid.startswith("demoted:"):
            if aid[len("demoted:"):] not in demoted_now:
                errors.append(f"{aid}: listed, but the stage is proved again or not pinned; "
                              f"remove it and lower max-entries")
        elif aid not in found:
            errors.append(f"{aid}: listed, but no such assumption in the tree; "
                          f"remove it and lower max-entries")
    if len(listed) != max_entries:
        errors.append(f"{ratchet_path}: {len(listed)} entries, max-entries is {max_entries} "
                      f"(change both together; the count may only shrink without a reason)")
    unpinned = sorted(proved - pins)

    if args.list:
        for aid in sorted(found):
            print(f"{aid}\t{found[aid]}")

    summary = (f"assumption gate: {len(found)} named assumptions "
               f"({sum(1 for a in found if a.startswith('io:'))} io, "
               f"{sum(1 for a in found if a.startswith('field:'))} field), "
               f"{len(proved)} proved stages ({len(pins)} pinned, {len(unpinned)} not yet pinned), "
               f"{len(demoted_now)} demoted")
    if unpinned:
        print("note: proved but not pinned (run --pin): " + ", ".join(unpinned[:10])
              + (" ..." if len(unpinned) > 10 else ""))
    if errors:
        for e in errors:
            print("ERROR " + e)
        print(summary + f"; {len(errors)} errors")
        return 1
    print(summary + "; pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
