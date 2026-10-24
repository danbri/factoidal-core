#!/usr/bin/env python3
"""The ASSUMPTION gate (https://github.com/danbri/factoidal/issues/975, item 4).

One ratchet over every named assumption in the tree and over the registry
stages that are `proved`. No Lean build is needed. Inputs, derived on every
run (anti-pattern 30):

  * `docs/dataflow-inventory.md` (generated from the Lean registry and checked
    against it by step 2 of tests/dataflow/run.sh, which runs before this gate);
  * the comment-stripped `.lean` files under `formal/lean4` (L4Factoidal, Wasm,
    Harness).

Four kinds of line in `foundation/assumptions.txt`, each `id ... # reason`:

  io:<Name>                  an IO assumption named in the "IO assumptions"
                             column of the inventory (an `IOStage` `assumption`
                             or an `RdfWriter` round-trip name). Distinct names.
  field:<Module>.<Struct>.<f>
                             a structure or class field whose name starts with
                             `assumed_` (declarations only: `f : T`, not
                             `f := v`). The naming rule for an interface type
                             (RdfReader, LawfulStore, LawfulDataset,
                             LawfulEvaluator, RdfWriter, SoundReasoner,
                             LawfulValidator, SoundChecker): a contract field
                             that is not proved is named `assumed_<what>`.
  name:<Ctor>  uses=<N>      a constructor of `inductive AssumptionName`
                             (Dataflow/Store.lean), with the number of places
                             that build an `Assumption` of that name
                             (`⟨.ctor,`, `⟨AssumptionName.ctor,`,
                             `name := .ctor`).
  demoted:<stage>            a stage pinned in `foundation/proved-stages.txt`
                             that is no longer `proved`.

It fails (exit 1) when:
  * a counted io, field or name has no line ("new assumption");
  * a line names an assumption, constructor or demotion that is gone
    ("stale"), has no reason, or is listed twice;
  * the `uses=` count of a name line differs from the count in the tree;
  * the number of lines differs from the `# max-entries: N` header;
  * a pinned proved stage is not proved now and has no `demoted:` line;
  * `inductive AssumptionName` is missing or empty, LawfulStore or
    LawfulDataset do not declare `assumed_contracts`, or RdfReader is missing;
  * a file under formal/lean4/Wasm or formal/lean4/Harness calls the backend
    evaluator over a bare dataset record (`runSelectQueryBackendDataset`,
    `runAskQueryBackendDataset`, `evalPatternBackend`, `evalBgpBackend`,
    `indexedDatasetBackend`) and not through `LawfulDataset` / `LawfulStore`;
  * a walk is empty (no registry rows, no proved stage, no Lean files).

A proved stage that is not pinned is reported, not failed; `--pin` rewrites
foundation/proved-stages.txt from the inventory.

Usage: python3 -I tools/assumption-gate.py [--root DIR] [--pin] [--list]
"""
import argparse
import glob
import os
import re
import sys

PKG = "L4Factoidal"
STORE = "formal/lean4/L4Factoidal/Dataflow/Store.lean"
READER = "formal/lean4/L4Factoidal/Dataflow/Reader.lean"
SEARCH_DIRS = ["formal/lean4/L4Factoidal", "formal/lean4/Wasm", "formal/lean4/Harness"]
CONSUMER_DIRS = ["formal/lean4/Wasm", "formal/lean4/Harness"]
BARE_EVAL = ["runSelectQueryBackendDataset", "runAskQueryBackendDataset", "evalPatternBackend",
             "evalBgpBackend", "indexedDatasetBackend"]
# A field declaration `assumed_x : T` (also `(assumed_x : T)` in a binder list);
# `assumed_x := v` in a structure instance is a value, not a declaration.
ASSUMED_FIELD_RE = re.compile(r"^[ \t]*\(?[ \t]*(assumed_[A-Za-z0-9_']+)[ \t]*:(?!=)", re.M)
DECL_RE = re.compile(r"^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*"
                     r"(?:structure|class)[ \t]+([A-Za-z0-9_.']+)", re.M)


def strip_lean_comments(text):
    """Remove `--` line comments and nested `/- ... -/` block comments, keeping
    newlines; string literals are kept whole."""
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


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def lean_files(root, dirs):
    out = []
    for d in dirs:
        out += glob.glob(os.path.join(root, d, "**", "*.lean"), recursive=True)
    return sorted(out)


# --- field: assumptions -----------------------------------------------------

def lean_fields(root, errors):
    """{id: path} for every `assumed_*` field declaration under L4Factoidal."""
    found, nfiles = {}, 0
    lean_root = os.path.join(root, "formal", "lean4")
    for p in lean_files(root, ["formal/lean4/" + PKG]):
        nfiles += 1
        mod = os.path.relpath(p, lean_root)[: -len(".lean")].replace(os.sep, ".")
        text = strip_lean_comments(read(p))
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


# --- io: assumptions and proved stages --------------------------------------

def inventory_rows(path, errors):
    """[(key, status, [io names])]; key = stage, or area when there is no stage."""
    rows = []
    for line in read(path).splitlines():
        if not line.startswith("| ") or line.startswith("| area ") or line.startswith("|---"):
            continue
        cells = [c.strip().replace("\\|", "|") for c in re.split(r"(?<!\\)\|", line.strip())[1:-1]]
        if len(cells) != 11:
            errors.append(f"{path}: row with {len(cells)} cells: {line.strip()[:80]}")
            continue
        area, stage, status, io = cells[0], cells[2].strip("`"), cells[6], cells[8]
        key = area if stage in ("", "-") else stage
        names = [n.strip().strip("`") for n in io.split(",")]
        rows.append((key, status, [n for n in names if n and n != "-"]))
    return rows


def read_pins(path, errors):
    pins = set()
    if not os.path.isfile(path):
        errors.append(f"{path}: pinned-stage file missing (run with --pin)")
        return pins
    for raw in read(path).splitlines():
        s = raw.split("#", 1)[0].strip()
        if s:
            pins.add(s)
    return pins


# --- name: assumptions (AssumptionName) -------------------------------------

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


def count_uses(root, names):
    counts = {n: 0 for n in names}
    for p in lean_files(root, SEARCH_DIRS):
        text = strip_lean_comments(read(p))
        for n in names:
            pat = r"(?:⟨\s*(?:AssumptionName)?\.%s\s*,|name\s*:=\s*(?:AssumptionName)?\.%s\b)" % (n, n)
            counts[n] += len(re.findall(pat, text))
    return counts


def bare_eval_calls(root):
    bad = []
    for p in lean_files(root, CONSUMER_DIRS):
        text = strip_lean_comments(read(p))
        for k, line in enumerate(text.split("\n"), 1):
            for w in BARE_EVAL:
                if re.search(r"(?<![\w.`])(?:[\w.]*\.)?%s\b" % w, line):
                    bad.append("%s:%d: %s" % (os.path.relpath(p, root), k, w))
    return bad


# --- the ratchet file --------------------------------------------------------

def read_ratchet(path, errors):
    """(max_entries, {id: uses or None})."""
    max_entries, ids = None, {}
    if not os.path.isfile(path):
        errors.append(f"{path}: ratchet file missing")
        return 0, ids
    for no, raw in enumerate(read(path).splitlines(), 1):
        s = raw.strip()
        m = re.match(r"#\s*max-entries:\s*(\d+)\s*$", s)
        if m:
            max_entries = int(m.group(1))
            continue
        if not s or s.startswith("#"):
            continue
        parts = re.split(r"\s+#\s*", s, maxsplit=1)
        head = parts[0].split()
        aid, uses = head[0], None
        if aid.startswith("name:"):
            um = re.fullmatch(r"uses=(\d+)", head[1]) if len(head) == 2 else None
            if not um:
                errors.append(f"{path}:{no}: {aid}: not 'name:<Ctor>  uses=<N>  # reason'")
            else:
                uses = int(um.group(1))
        elif len(head) != 1:
            errors.append(f"{path}:{no}: {aid}: not 'id  # reason'")
        if not any(aid.startswith(k) for k in ("io:", "field:", "name:", "demoted:")):
            errors.append(f"{path}:{no}: {aid}: unknown kind (io:, field:, name:, demoted:)")
        if len(parts) < 2 or not parts[1].strip():
            errors.append(f"{path}:{no}: {aid}: no reason (write 'id  # reason')")
        if aid in ids:
            errors.append(f"{path}:{no}: {aid}: listed twice")
        ids[aid] = uses
    if max_entries is None:
        errors.append(f"{path}: no '# max-entries: N' header")
        max_entries = len(ids)
    return max_entries, ids


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--pin", action="store_true", help="rewrite foundation/proved-stages.txt")
    ap.add_argument("--list", action="store_true", help="print every counted assumption")
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root)
    errors = []

    # io: and proved stages
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

    # field:
    fields, nfiles = lean_fields(root, errors)
    if nfiles == 0:
        errors.append("formal/lean4/L4Factoidal: no .lean files found (empty walk)")
    found.update(fields)

    # name:
    uses = {}
    store_path = os.path.join(root, STORE)
    store_text = strip_lean_comments(read(store_path)) if os.path.isfile(store_path) else ""
    if not store_text:
        errors.append(f"{STORE}: not found")
    ctors = constructors(store_text) if store_text else None
    if store_text and not ctors:
        errors.append(f"{STORE}: no constructor of inductive AssumptionName")
    if ctors:
        uses = count_uses(root, ctors)
        for c in ctors:
            found[f"name:{c}"] = f"uses={uses[c]}"
    if store_text:
        for s in ("LawfulStore", "LawfulDataset"):
            has = structure_has_field(store_text, s, "assumed_contracts")
            if has is None:
                errors.append(f"interface structure {s} not found in {STORE}")
            elif not has:
                errors.append(f"{s} must declare the field `assumed_contracts`")
    reader_path = os.path.join(root, READER)
    reader_text = strip_lean_comments(read(reader_path)) if os.path.isfile(reader_path) else ""
    if structure_has_field(reader_text, "RdfReader", "assumed_contracts") is None:
        errors.append(f"interface structure RdfReader not found in {READER}")
    for b in bare_eval_calls(root):
        errors.append("%s: backend evaluator over a bare DatasetBackend; use "
                      "LawfulDataset.runSelect / runAsk or LawfulStore" % b)

    pins_path = os.path.join(root, "foundation", "proved-stages.txt")
    if args.pin:
        with open(pins_path, "w", encoding="utf-8") as fh:
            fh.write("# Registry stages that are `proved`, pinned by tools/assumption-gate.py --pin.\n"
                     "# tools/assumption-gate.py fails when a pinned stage is no longer proved\n"
                     "# unless foundation/assumptions.txt has a 'demoted:<stage>' line with a reason.\n")
            for k in sorted(proved):
                fh.write(k + "\n")
        print(f"pinned {len(proved)} proved stages")
        return 0
    pins = read_pins(pins_path, errors)

    ratchet_path = os.path.join(root, "foundation", "assumptions.txt")
    max_entries, listed = read_ratchet(ratchet_path, errors)

    demoted_now = {k for k in pins if k not in proved}
    for aid in sorted(found):
        if aid not in listed:
            hint = (f"'{aid}  uses={uses[aid[5:]]}  # reason'" if aid.startswith("name:")
                    else f"'{aid}  # reason'")
            errors.append(f"{aid}: new assumption ({found[aid]}); add {hint} to "
                          f"foundation/assumptions.txt and raise max-entries")
        elif aid.startswith("name:") and listed[aid] is not None and listed[aid] != uses[aid[5:]]:
            n = uses[aid[5:]]
            errors.append(f"{aid}: uses={listed[aid]} listed, {n} in the tree"
                          + (" (a new use: raise it, with a reason)" if n > listed[aid]
                             else " (stale: lower it)"))
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

    def count(prefix):
        return sum(1 for a in found if a.startswith(prefix))

    summary = (f"assumption gate: {len(found)} named assumptions "
               f"({count('io:')} io, {count('field:')} field, {count('name:')} name "
               f"with {sum(uses.values())} uses), "
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
