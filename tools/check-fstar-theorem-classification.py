#!/usr/bin/env python3
"""Check docs/fstar-theorem-classification.tsv against the F* tree and the
Lean tree (https://github.com/danbri/factoidal/issues/757, step 4).

    python3 tools/check-fstar-theorem-classification.py
    python3 tools/check-fstar-theorem-classification.py --add-missing
    python3 tools/check-fstar-theorem-classification.py --no-lean   # skip (c)

The F* side is the live inventory: tools/fstar-theorem-inventory.py walks
formal/fstar on this run (anti-pattern 30). `--inventory PATH` reads an
inventory TSV instead; it exists for the self-test.

CHECKS
------
(a) Every RELEVANT theorem of the inventory has exactly one row, and every
    row names a theorem (module + name) that the inventory finds. A row for a
    HELPER theorem is allowed and reported.
(b) The row's statement_sha256 equals the current one. A changed F*
    statement reopens its row: the row is reported STALE and the check
    fails. There is no option that rewrites a hash; a person reads the new
    statement, re-decides the class and writes the new hash.
(c) Every Lean theorem named in lean_theorems exists. A temporary Lean file
    imports the modules whose source declares the last name component and
    holds one `#check @Name` per name; it is run as `lake env lean FILE` with
    formal/lean4 as the working directory. Lean is the authority: a name is
    missing when Lean reports an error on its `#check` line, or when no
    source file declares it (then Lean is not asked). The grep only chooses
    the imports.
(d) The class is one of R, S, F, A, U. R, S and F name at least one Lean
    theorem. S, F and A have a non-empty note (S: in what way the Lean
    theorem is stronger; F: the justification or a link to it; A: the loss
    of assurance in one sentence).
(e) Counts per class, "N of T", per F* module family (RDF, RDFS, OWL,
    SPARQL, parsers, other) and in total, where T is the number of RELEVANT
    theorems of the family.

Exit 0 when (a) to (d) hold. U rows are reported, not a failure. Exit 1 on
any failure of (a) to (d). Exit 2 on a usage or environment error.

`--add-missing` appends a U row for each relevant theorem with no row, then
checks. It never changes an existing row.
"""

import argparse, csv, importlib.util, os, re, subprocess, sys, tempfile
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
DEFAULT_TSV = os.path.join(REPO, "docs", "fstar-theorem-classification.tsv")
DEFAULT_LEAN = os.path.join(REPO, "formal", "lean4")
INVENTORY_TOOL = os.path.join(HERE, "fstar-theorem-inventory.py")

COLUMNS = ["fstar_module", "fstar_name", "statement_sha256", "class",
           "lean_theorems", "note"]
CLASSES = ["R", "S", "F", "A", "U"]
FAMILIES = ["RDF", "RDFS", "OWL", "SPARQL", "parsers", "other"]
NEEDS_LEAN = {"R", "S", "F"}
NEEDS_NOTE = {"S", "F", "A"}


def load_inventory(path):
    spec = importlib.util.spec_from_file_location("fstar_inventory", INVENTORY_TOOL)
    inv = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inv)
    if path:
        with open(path, encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh, delimiter="\t", quoting=csv.QUOTE_NONE))
        for r in rows:
            r.setdefault("family", inv.family_of(r["module"]))
        return rows
    rows, _stats = inv.build(inv.DEFAULT_ROOT, check_tables=True)
    return rows


def read_tsv(path):
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as fh:
        lines = [l for l in fh.read().split("\n") if l.strip() and not l.startswith("#")]
    if not lines:
        return []
    head = lines[0].split("\t")
    if head != COLUMNS:
        sys.exit("check-fstar-theorem-classification: %s: header must be %s, got %s"
                 % (path, "\t".join(COLUMNS), "\t".join(head)))
    rows = []
    for k, l in enumerate(lines[1:], start=2):
        cells = l.split("\t")
        cells += [""] * (len(COLUMNS) - len(cells))
        r = dict(zip(COLUMNS, cells[:len(COLUMNS)]))
        r["_line"] = k
        r["_extra"] = len(cells) > len(COLUMNS)
        rows.append(r)
    return rows


def append_rows(path, rows):
    new = not os.path.exists(path) or os.path.getsize(path) == 0
    with open(path, "a", encoding="utf-8") as fh:
        if new:
            fh.write("\t".join(COLUMNS) + "\n")
        for r in rows:
            fh.write("\t".join(r[c] for c in COLUMNS) + "\n")


DECL_RE = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|axiom|opaque)"


def lean_sources(lean_dir):
    out = []
    for dp, dn, fn in os.walk(os.path.join(lean_dir, "L4Factoidal")):
        dn.sort()
        for f in sorted(fn):
            if f.endswith(".lean"):
                out.append(os.path.join(dp, f))
    return out


def module_name(lean_dir, path):
    return os.path.relpath(path, lean_dir)[:-5].replace(os.sep, ".")


def check_lean(names, lean_dir, lean_cmd):
    """Return (missing: dict name -> reason, error: str or None)."""
    srcs = lean_sources(lean_dir)
    if not srcs:
        return {}, "no .lean file under %s/L4Factoidal" % lean_dir
    texts = {p: open(p, encoding="utf-8", errors="replace").read() for p in srcs}
    missing, imports, checked = {}, set(), []
    for n in sorted(names):
        last = n.split(".")[-1]
        pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|"
                         r"partial|unsafe)\s+)*" + DECL_RE + r"\s+(?:[\w'.]*\.)?"
                         + re.escape(last) + r"(?![\w'.])", re.M)
        hits = [p for p, t in texts.items() if pat.search(t)]
        if not hits:
            missing[n] = "no Lean source declares `%s`" % last
            continue
        for p in hits:
            imports.add(module_name(lean_dir, p))
        checked.append(n)
    if not checked:
        return missing, None
    fd, tmp = tempfile.mkstemp(prefix="fstar_theorem_check_", suffix=".lean")
    lines = ["import %s" % m for m in sorted(imports)]
    first = len(lines) + 1
    lines += ["#check @%s" % n for n in checked]
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(lean_cmd + [tmp], cwd=lean_dir, capture_output=True,
                           text=True, timeout=1800)
    except FileNotFoundError as e:
        os.unlink(tmp)
        return missing, "cannot run %s: %s" % (" ".join(lean_cmd), e)
    except subprocess.TimeoutExpired:
        os.unlink(tmp)
        return missing, "Lean check timed out after 1800 s"
    out = r.stdout + "\n" + r.stderr
    os.unlink(tmp)
    err_lines = {}
    for m in re.finditer(r"^(?:[^\n:]*):(\d+):(\d+): error:?\s*(.*)$", out, re.M):
        err_lines.setdefault(int(m.group(1)), m.group(3).strip())
    if any(l < first for l in err_lines) or (r.returncode != 0 and not err_lines):
        return missing, "Lean could not load the imports (exit %d):\n%s" % (r.returncode, out.strip()[:4000])
    for k, n in enumerate(checked):
        if first + k in err_lines:
            missing[n] = "Lean: " + err_lines[first + k]
    return missing, None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tsv", default=DEFAULT_TSV)
    ap.add_argument("--inventory", default=None,
                    help="read this inventory TSV instead of walking formal/fstar (self-test)")
    ap.add_argument("--lean-dir", default=DEFAULT_LEAN)
    ap.add_argument("--lean-cmd", default="lake env lean",
                    help="command run in --lean-dir with the temporary file appended")
    ap.add_argument("--no-lean", action="store_true", help="skip check (c)")
    ap.add_argument("--add-missing", action="store_true",
                    help="append a U row for each relevant theorem without one")
    a = ap.parse_args(argv)

    inv = load_inventory(a.inventory)
    if not inv:
        print("check-fstar-theorem-classification: the inventory is empty")
        return 2
    by_key = {(r["module"], r["name"]): r for r in inv}
    relevant = {k for k, r in by_key.items() if r["relevance"] == "RELEVANT"}

    rows = read_tsv(a.tsv)
    have = {(r["fstar_module"], r["fstar_name"]) for r in rows}
    if a.add_missing:
        add = [{"fstar_module": m, "fstar_name": n,
                "statement_sha256": by_key[(m, n)]["statement_sha256"],
                "class": "U", "lean_theorems": "", "note": ""}
               for (m, n) in sorted(relevant - have)]
        if add:
            append_rows(a.tsv, add)
            print("added %d U rows to %s" % (len(add), a.tsv))
        rows = read_tsv(a.tsv)

    fail = defaultdict(list)
    seen = defaultdict(list)
    for r in rows:
        seen[(r["fstar_module"], r["fstar_name"])].append(r["_line"])
        if r["_extra"]:
            fail["format"].append("line %d: more than %d columns" % (r["_line"], len(COLUMNS)))
    for k, ls in seen.items():
        if len(ls) > 1:
            fail["a"].append("%s.%s has %d rows (lines %s)" % (k[0], k[1], len(ls),
                                                               ", ".join(map(str, ls))))
    for k in sorted(relevant - set(seen)):
        fail["a"].append("MISSING row for relevant theorem %s.%s (%s)"
                         % (k[0], k[1], by_key[k]["location"]))
    helper_rows = 0
    for r in rows:
        k = (r["fstar_module"], r["fstar_name"])
        if k not in by_key:
            fail["a"].append("line %d: %s.%s is not an F* theorem the inventory finds"
                             % (r["_line"], k[0], k[1]))
            continue
        if k not in relevant:
            helper_rows += 1
        cur = by_key[k]["statement_sha256"]
        if r["statement_sha256"] != cur:
            fail["b"].append("STALE line %d: %s.%s statement changed (row %s, now %s) at %s"
                             % (r["_line"], k[0], k[1], r["statement_sha256"][:12],
                                cur[:12], by_key[k]["location"]))
        c = r["class"]
        if c not in CLASSES:
            fail["d"].append("line %d: %s.%s class %r is not one of %s"
                             % (r["_line"], k[0], k[1], c, " ".join(CLASSES)))
            continue
        if c in NEEDS_LEAN and not r["lean_theorems"].strip():
            fail["d"].append("line %d: %s.%s class %s names no Lean theorem"
                             % (r["_line"], k[0], k[1], c))
        if c in NEEDS_NOTE and not r["note"].strip():
            fail["d"].append("line %d: %s.%s class %s needs a note"
                             % (r["_line"], k[0], k[1], c))

    names = sorted({n for r in rows for n in r["lean_theorems"].split() if n})
    lean_note = "not run (--no-lean)"
    if not a.no_lean and names:
        missing, err = check_lean(names, a.lean_dir, a.lean_cmd.split())
        if err:
            print("check-fstar-theorem-classification: (c) " + err)
            return 2
        for n, why in sorted(missing.items()):
            users = ["%s.%s" % (r["fstar_module"], r["fstar_name"]) for r in rows
                     if n in r["lean_theorems"].split()]
            fail["c"].append("Lean theorem %s does not exist (%s); named by %s"
                             % (n, why, ", ".join(users)))
        lean_note = "%d names, %d missing (`%s` in %s)" % (
            len(names), len(missing), a.lean_cmd, os.path.relpath(a.lean_dir, REPO)
            if a.lean_dir.startswith(REPO) else a.lean_dir)
    elif not names:
        lean_note = "no Lean theorem named"

    # (e) counts.
    fam_total = defaultdict(int)
    for k in relevant:
        fam_total[by_key[k]["family"]] += 1
    fam_class = defaultdict(lambda: defaultdict(int))
    for r in rows:
        k = (r["fstar_module"], r["fstar_name"])
        if k in relevant and r["class"] in CLASSES:
            fam_class[by_key[k]["family"]][r["class"]] += 1
    print("F* theorem classification (issue 757): %d relevant of %d F* lemmas; "
          "%d rows; %d rows for HELPER theorems" % (len(relevant), len(by_key),
                                                    len(rows), helper_rows))
    print("(c) Lean names: " + lean_note)
    hdr = "%-8s %8s" % ("family", "relevant") + "".join("  %-14s" % c for c in CLASSES)
    print(hdr)
    tot = defaultdict(int)
    for f in FAMILIES:
        t = fam_total.get(f, 0)
        cells = []
        for c in CLASSES:
            n = fam_class[f][c]
            tot[c] += n
            cells.append("  %-14s" % ("%d of %d" % (n, t)))
        print("%-8s %8d" % (f, t) + "".join(cells))
    T = len(relevant)
    print("%-8s %8d" % ("total", T) + "".join("  %-14s" % ("%d of %d" % (tot[c], T))
                                            for c in CLASSES))
    nfail = 0
    for key, label in [("format", "format"), ("a", "(a) rows"), ("b", "(b) stale"),
                       ("c", "(c) Lean names"), ("d", "(d) class/note")]:
        for msg in fail.get(key, []):
            print("FAIL %s: %s" % (label, msg))
            nfail += 1
    if nfail:
        print("check-fstar-theorem-classification: %d failure(s)" % nfail)
        return 1
    print("check-fstar-theorem-classification: (a)-(d) hold; %d of %d relevant "
          "theorems are U" % (tot["U"] + (T - sum(tot.values())), T))
    return 0


if __name__ == "__main__":
    sys.exit(main())
