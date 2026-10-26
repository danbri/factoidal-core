#!/usr/bin/env python3
"""Self-test for tools/check-fstar-theorem-classification.py
(https://github.com/danbri/factoidal/issues/757, step 4).

    python3 tools/test_check_fstar_theorem_classification.py

Builds a small synthetic inventory TSV, a classification TSV and a Lean
source directory in a temporary directory. Lean itself is replaced by a
stub command that answers `#check @Name` the way `lake env lean` does: no
output for a declared name, `FILE:LINE:COL: error: unknown constant` for an
undeclared one. The real `lake env lean` run is the gate on the real tree.

Cases: the good classification exits 0 with U rows reported; a STALE row,
a missing row, a row naming no F* theorem, a Lean name that the stub Lean
rejects, a Lean name that no source declares, an S row without a note, an R
row without a Lean theorem, and a bad class each exit 1; an import error
exits 2. Exit 0 when every case gives the expected exit code.
"""

import os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKER = os.path.join(HERE, "check-fstar-theorem-classification.py")

INV_COLS = ["module", "name", "kind", "location", "family", "relevance",
            "reasons", "refs_local", "refs_external", "statement_sha256",
            "statement"]
INVENTORY = [
    ["RDF.Entailment.X", "thm_a", "val", "formal/fstar/RDF.Entailment.X.fst:10", "RDFS",
     "RELEVANT", "SEM:entails", "", "", "a" * 64, "thm_a : Lemma True"],
    ["OWL.Semantics.Y", "thm_b", "let", "formal/fstar/OWL.Semantics.Y.fst:20", "OWL",
     "RELEVANT", "TOP", "", "", "b" * 64, "thm_b : Lemma True"],
    ["OWL.Semantics.Y", "thm_c", "let", "formal/fstar/OWL.Semantics.Y.fst:30", "OWL",
     "RELEVANT", "EXT", "", "Z.q", "c" * 64, "thm_c : Lemma True"],
    ["OWL.Semantics.Y", "helper_d", "let", "formal/fstar/OWL.Semantics.Y.fst:40", "OWL",
     "HELPER", "LOCAL1", "thm_b", "", "d" * 64, "helper_d : Lemma True"],
]
COLS = ["fstar_module", "fstar_name", "statement_sha256", "class", "lean_theorems", "note"]
GOOD = [
    ["RDF.Entailment.X", "thm_a", "a" * 64, "R", "L4Factoidal.Demo.good_one", ""],
    ["OWL.Semantics.Y", "thm_b", "b" * 64, "S", "Demo.good_two",
     "every rule instead of four"],
    ["OWL.Semantics.Y", "thm_c", "c" * 64, "U", "", ""],
]
LEAN_SRC = """namespace L4Factoidal.Demo
theorem good_one : True := trivial
end L4Factoidal.Demo
theorem Demo.good_two : True := trivial
theorem declared_but_rejected : True := trivial
"""
STUB = r'''import re, sys
path = sys.argv[-1]
ok = set(open(%r).read().split())
bad = False
for k, line in enumerate(open(path).read().split("\n"), start=1):
    m = re.match(r"import (\S+)", line)
    if m and m.group(1) == "L4Factoidal.Broken":
        print("%%s:%%d:0: error: unknown module prefix" %% (path, k)); bad = True
    m = re.match(r"#check @(\S+)", line)
    if m and m.group(1) not in ok:
        print("%%s:%%d:7: error: unknown constant '%%s'" %% (path, k, m.group(1))); bad = True
sys.exit(1 if bad else 0)
'''


def tsv(path, cols, rows):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\t".join(cols) + "\n")
        for r in rows:
            fh.write("\t".join(r) + "\n")


def main():
    tmp = tempfile.mkdtemp(prefix="fstar-class-test-")
    results = []
    try:
        inv = os.path.join(tmp, "inventory.tsv")
        tsv(inv, INV_COLS, INVENTORY)
        lean = os.path.join(tmp, "lean")
        os.makedirs(os.path.join(lean, "L4Factoidal"))
        with open(os.path.join(lean, "L4Factoidal", "Demo.lean"), "w") as fh:
            fh.write(LEAN_SRC)
        allowed = os.path.join(tmp, "allowed.txt")
        with open(allowed, "w") as fh:
            fh.write("L4Factoidal.Demo.good_one Demo.good_two\n")
        stub = os.path.join(tmp, "stub_lean.py")
        with open(stub, "w") as fh:
            fh.write(STUB % allowed)

        def run(name, rows, expect, extra_lean_src=None):
            cls = os.path.join(tmp, name + ".tsv")
            tsv(cls, COLS, rows)
            if extra_lean_src is not None:
                with open(os.path.join(lean, "L4Factoidal", "Broken.lean"), "w") as fh:
                    fh.write(extra_lean_src)
            r = subprocess.run([sys.executable, CHECKER, "--tsv", cls, "--inventory", inv,
                                "--lean-dir", lean, "--lean-cmd", "%s %s" % (sys.executable, stub)],
                               capture_output=True, text=True)
            if extra_lean_src is not None:
                os.unlink(os.path.join(lean, "L4Factoidal", "Broken.lean"))
            ok = r.returncode == expect
            results.append((ok, name, expect, r.returncode, r.stdout + r.stderr))
            return r

        r = run("good", GOOD, 0)
        if "1 of 3" not in r.stdout or "U" not in r.stdout:
            results.append((False, "good: U row reported in the counts", 0, 0, r.stdout))
        stale = [list(x) for x in GOOD]; stale[0][2] = "e" * 64
        run("stale_row", stale, 1)
        run("missing_row", GOOD[:2], 1)
        run("row_names_no_fstar_theorem", GOOD + [["OWL.Semantics.Y", "no_such", "f" * 64, "U", "", ""]], 1)
        bad_lean = [list(x) for x in GOOD]; bad_lean[0][4] = "declared_but_rejected"
        run("lean_name_rejected_by_lean", bad_lean, 1)
        undeclared = [list(x) for x in GOOD]; undeclared[0][4] = "L4Factoidal.Demo.nowhere"
        run("lean_name_declared_nowhere", undeclared, 1)
        no_note = [list(x) for x in GOOD]; no_note[1][5] = ""
        run("S_row_without_note", no_note, 1)
        no_lean = [list(x) for x in GOOD]; no_lean[0][4] = ""
        run("R_row_without_lean_theorem", no_lean, 1)
        bad_class = [list(x) for x in GOOD]; bad_class[2][3] = "X"
        run("bad_class", bad_class, 1)
        run("helper_row_allowed", GOOD + [["OWL.Semantics.Y", "helper_d", "d" * 64, "U", "", ""]], 0)
        imp = [list(x) for x in GOOD]; imp[0][4] = "Broken.thing"
        run("import_error", imp, 2, extra_lean_src="theorem Broken.thing : True := trivial\n")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    fails = [x for x in results if not x[0]]
    for ok, name, expect, got, out in fails:
        print("FAIL: %s: expected exit %d, got %d\n%s" % (name, expect, got, out))
    print("test_check_fstar_theorem_classification: %d pass, %d fail (out of %d)"
          % (len(results) - len(fails), len(fails), len(results)))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
