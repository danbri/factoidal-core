#!/usr/bin/env python3
"""Generate docs/dataflow-inventory.md from the Lean dataflow registry.

https://github.com/danbri/factoidal/issues/975, phase A3.

Every run derives the table from the Lean sources (anti-pattern 30: no
cache):

1. `lake build L4Factoidal.Dataflow.Registry L4Factoidal.Dataflow.RegistryTests`
   in formal/lean4;
2. `lake env lean ../../tools/dataflow-inventory.lean`, which elaborates
   against the built library, checks every entry of
   `L4Factoidal.Dataflow.registry` (names exist, axioms, status agrees with
   fields) and prints one tab-separated line per entry;
3. a walk of formal/lean4/L4Factoidal for the component directories, to list
   the directories that no entry names.

It also writes formal/lean4/L4Factoidal/Dataflow/StageKinds.lean: for each
entry with a stage declaration, the constant at the head of that
declaration's type (its interface type), as the report program reads it from
the environment. The wasm op `stageList` (formal/lean4/Wasm/Ops/StageList.lean)
reads the registry at run time and this table for the kinds, because the
environment is not available at run time (issue 1002).

The registry is a declared list (anti-pattern 31): this tool does not guess
stages from file or declaration names.

Usage:
  tools/dataflow-inventory.py           write docs/dataflow-inventory.md
  tools/dataflow-inventory.py --check   exit 1 when either file differs from
                                        a fresh generation
"""

import difflib
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "formal" / "lean4"
LIB = LEAN / "L4Factoidal"
OUT = ROOT / "docs" / "dataflow-inventory.md"
KINDS = LIB / "Dataflow" / "StageKinds.lean"
REPORT = ROOT / "tools" / "dataflow-inventory.lean"
TIMEOUT = 600
STATUSES = ["proved", "tested", "assumed", "missing"]
FIELDS = ["area", "dir", "stage", "wire_in", "wire_out", "contract", "status",
          "theorems", "io", "tests", "note"]


def fail(msg):
    print(f"dataflow-inventory: {msg}", file=sys.stderr)
    sys.exit(1)


def run(cmd):
    try:
        p = subprocess.run(cmd, cwd=LEAN, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        fail(f"timeout after {TIMEOUT} s: {' '.join(cmd)}")
    if p.returncode != 0:
        sys.stderr.write(p.stdout[-4000:])
        sys.stderr.write(p.stderr[-4000:])
        fail(f"exit {p.returncode}: {' '.join(cmd)}")
    return p.stdout


def registry_rows():
    run(["lake", "build", "L4Factoidal.Dataflow.Registry", "L4Factoidal.Dataflow.RegistryTests"])
    out = run(["lake", "env", "lean", str(REPORT)])
    lines = out.splitlines()
    if "BEGIN-INVENTORY" not in lines or "END-INVENTORY" not in lines:
        fail("the report program printed no inventory block")
    body = lines[lines.index("BEGIN-INVENTORY") + 1:lines.index("END-INVENTORY")]
    rows = []
    for line in body:
        parts = line.split("\t")
        if len(parts) != len(FIELDS):
            fail(f"bad row ({len(parts)} fields): {line!r}")
        row = dict(zip(FIELDS, parts))
        if row["status"] not in STATUSES:
            fail(f"bad status {row['status']!r} in {row['area']!r}")
        rows.append(row)
    if not rows:
        fail("the registry is empty")
    if "BEGIN-KINDS" not in lines or "END-KINDS" not in lines:
        fail("the report program printed no kinds block")
    kinds = []
    for line in lines[lines.index("BEGIN-KINDS") + 1:lines.index("END-KINDS")]:
        parts = line.split("\t")
        if len(parts) != 2 or not parts[0] or not parts[1]:
            fail(f"bad kinds row: {line!r}")
        kinds.append((parts[0], parts[1]))
    staged = [r["stage"] for r in rows if r["stage"]]
    if [k for k, _ in kinds] != staged:
        fail("the kinds block does not list the stage declarations of the inventory in order")
    return rows, kinds


def component_dirs():
    if not LIB.is_dir():
        fail(f"no directory {LIB}")
    dirs = sorted(p.name for p in LIB.iterdir()
                  if p.is_dir() and any(p.rglob("*.lean")))
    if not dirs:
        fail(f"the walk of {LIB} found no component directory")
    return dirs


def code(s):
    return f"`{s}`" if s else "-"


def codes(s):
    return ", ".join(f"`{x}`" for x in s.split(", ")) if s else "-"


def short(name):
    for pre in ("L4Factoidal.Dataflow.", "L4Factoidal."):
        if name.startswith(pre):
            return name[len(pre):]
    return name


def shorts(s):
    return ", ".join(short(x) for x in s.split(", ")) if s else ""


def render(rows, dirs):
    counts = {s: sum(1 for r in rows if r["status"] == s) for s in STATUSES}
    registered = sorted({r["dir"] for r in rows})
    for d in registered:
        if d not in dirs:
            fail(f"registry names directory {d!r}, which has no .lean file under {LIB}")
    unregistered = [d for d in dirs if d not in registered]
    out = []
    out.append("# Dataflow inventory")
    out.append("")
    out.append("Generated by `tools/dataflow-inventory.py` from "
               "`formal/lean4/L4Factoidal/Dataflow/Registry.lean`. Do not edit; "
               "`tests/dataflow/run.sh` fails when this file differs from a fresh "
               "generation. Issue: https://github.com/danbri/factoidal/issues/975 "
               "(phase A3).")
    out.append("")
    out.append("Status: `proved` = a `Stage`, an `RdfReader` (the reader interface type) or an `RdfWriter` with nothing assumed, whose soundness is a Lean proof; "
               "`assumed` = an IO stage, or an `RdfWriter`, whose contract is a named assumption; "
               "`tested` = no Lean contract, a named suite checks it; "
               "`missing` = no Lean contract and no suite named here. Every named "
               "declaration exists and depends only on propext, Classical.choice "
               "and Quot.sound (checked on each run). Names are relative to "
               "`L4Factoidal.Dataflow` or `L4Factoidal`.")
    out.append("")
    out.append(f"Entries: {len(rows)}. " + ", ".join(
        f"{counts[s]} {s}" for s in STATUSES) + f" (out of {len(rows)}).")
    out.append("")
    out.append("| area | dir | stage | in | out | contract | status | theorems | IO assumptions | tests | note |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        cells = [r["area"], r["dir"], code(short(r["stage"])), r["wire_in"], r["wire_out"],
                 code(short(r["contract"])), r["status"], codes(shorts(r["theorems"])),
                 codes(shorts(r["io"])), r["tests"] or "-", r["note"] or "-"]
        out.append("| " + " | ".join(c.replace("|", "\\|") for c in cells) + " |")
    out.append("")
    out.append(f"Directories under `formal/lean4/L4Factoidal/` that no entry names "
               f"({len(unregistered)} of {len(dirs)}): "
               + (", ".join(f"`{d}`" for d in unregistered) if unregistered else "none") + ".")
    out.append("")
    out.append("Hand-over findings: module header of "
               "`formal/lean4/L4Factoidal/Dataflow/Instances.lean`.")
    out.append("")
    return "\n".join(out)


def lean_string(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def render_kinds(kinds):
    out = []
    out.append("/-")
    out.append("L4Factoidal.Dataflow.StageKinds -- generated by tools/dataflow-inventory.py.")
    out.append("Do not edit; `tests/dataflow/run.sh` fails when this file differs from a")
    out.append("fresh generation (https://github.com/danbri/factoidal/issues/1002).")
    out.append("")
    out.append("For each entry of `L4Factoidal.Dataflow.registry` with a `stage`")
    out.append("declaration, in registry order: the declaration and the constant at the head")
    out.append("of its type (its interface type: `Stage`, `RdfReader`, `IOStage`, ...), as")
    out.append("`tools/dataflow-inventory.lean` reads them from the environment. The wasm op")
    out.append("`stageList` (`Wasm/Ops/StageList.lean`) reads the registry itself at run")
    out.append("time and this table for the kinds, because the environment is not available")
    out.append("at run time.")
    out.append("-/")
    out.append("namespace L4Factoidal.Dataflow")
    out.append("")
    out.append("/-- (stage declaration, interface type), in registry order. -/")
    out.append("def stageKinds : List (String × String) := [")
    for i, (k, v) in enumerate(kinds):
        sep = "," if i + 1 < len(kinds) else ""
        out.append(f"  ({lean_string(k)}, {lean_string(v)}){sep}")
    out.append("]")
    out.append("")
    out.append("end L4Factoidal.Dataflow")
    out.append("")
    return "\n".join(out)


def main():
    check = "--check" in sys.argv[1:]
    rows, kinds = registry_rows()
    outputs = [(OUT, render(rows, component_dirs())), (KINDS, render_kinds(kinds))]
    if check:
        for path, text in outputs:
            old = path.read_text() if path.exists() else ""
            if old != text:
                sys.stdout.writelines(difflib.unified_diff(
                    old.splitlines(True), text.splitlines(True),
                    str(path), "fresh generation"))
                fail(f"{path} differs from a fresh generation; run tools/dataflow-inventory.py")
            print(f"dataflow-inventory: {path.relative_to(ROOT)} is current")
        return
    for path, text in outputs:
        path.write_text(text)
        print(f"dataflow-inventory: wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
