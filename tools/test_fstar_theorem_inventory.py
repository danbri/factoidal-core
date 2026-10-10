#!/usr/bin/env python3
"""Self-test for tools/fstar-theorem-inventory.py
(https://github.com/danbri/factoidal/issues/757, step 1).

    python3 tools/test_fstar_theorem_inventory.py

Writes a small synthetic F* tree to a temporary directory, runs the inventory
on it with --root, and checks:

  * every recognised lemma form is found (val + proof let, let, let rec, and,
    assume val, the arrow form, a qualifier on its own line, an .fsti val);
  * a lemma inside a NESTED block comment, a lemma after `//`, and a lemma
    inside a string literal are not found (F* block comments nest: CLAUDE.md,
    "F* Syntax Traps", 1);
  * a declaration whose only `Lemma` is a binder type is not a lemma;
  * a `=` inside `requires (...)` does not end a let's statement;
  * a multi-line statement has the same sha256 after a white-space change,
    and a different one after a token change;
  * the relevance codes: LOCAL1 (one local user), MULTI, EXT, TOP, PAT,
    ASSUMED, SPEC, SEM;
  * an empty tree exits non-zero.

Exit 0 when every check passes.
"""

import csv, importlib.util, io, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "fstar-theorem-inventory.py")

A_FST = r'''module Demo.A

open Demo.Spec

(* Section header. A commented lemma after a nested comment:
   (* inner comment *)
let hidden_nested (x : int) : Lemma (x == x) = ()
   This line is still inside the outer comment: block comments nest. *)

// let hidden_line (x : int) : Lemma (x == x) = ()

let not_a_lemma_string : string = "let hidden_string (x:int) : Lemma True = ()"

val stated (x : nat)
  : Lemma (requires x > 0)
          (ensures x + 0 > 0)

let stated x = helper_one x

let helper_one (x : nat) : Lemma (x + 0 == x) = ()

let helper_two (x : nat) : Lemma (x * 1 == x) = ()

let user_a (x : nat) : Lemma (x * 1 + 0 == x) = helper_two x; helper_one x

let user_b (x : nat) : Lemma (1 * x == x) = helper_two x

let rec rec_lemma (n : nat) : Lemma (ensures n >= 0) (decreases n) =
  if n = 0 then () else rec_lemma (n - 1)

let rec even_ok (n : nat) : Lemma (ensures n >= 0) (decreases n) =
  if n = 0 then () else odd_ok (n - 1)
and odd_ok (n : nat) : Lemma (ensures n >= 0) (decreases n) =
  if n = 0 then () else even_ok (n - 1)

val arrow_form : x:int -> y:int -> Lemma (x + y == y + x)
let arrow_form x y = ()

val takes_a_lemma : (x:int -> Lemma (x == x)) -> Tot unit
let takes_a_lemma f = ()

let eq_in_requires (x : nat) : Lemma (requires (x = 1)) (ensures (x + 0 = 1)) [SMTPat (x + 0)] =
  ()

private
let qualified_alone (x : int) : Lemma (x == x) = ()

assume val axiom_lemma (x : int) : Lemma (x - x == 0)

let spec_use (x : int) : Lemma (spec_pred x) = ()

let sem_use (x : int) : Lemma (entails_thing x) = ()

let multi_line_stmt (a : int)
    (b : int)
  : Lemma (a + b
           == b + a) = ()
'''

SPEC_FST = r'''module Demo.Spec

let spec_pred (x : int) : prop = True
let entails_thing (x : int) : prop = True
'''

B_FST = r'''module Demo.B

open Demo.A

let uses_a (x : nat) : Lemma (x + 0 == x) = helper_one x
'''

I_FSTI = r'''module Demo.I

val iface_lemma (x : int) : Lemma (x == x)
'''

I_FST = r'''module Demo.I

let iface_lemma (x : int) : Lemma (x == x) = ()
'''


def load_tool():
    spec = importlib.util.spec_from_file_location("inv", TOOL)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run(root):
    out = os.path.join(root, "..", "out.tsv")
    r = subprocess.run([sys.executable, TOOL, "--root", root, "--out", out],
                       capture_output=True, text=True)
    rows = []
    if r.returncode == 0:
        with open(out, encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh, delimiter="\t", quoting=csv.QUOTE_NONE))
    return r.returncode, rows, r.stderr


def write_tree(root, a_text):
    os.makedirs(root, exist_ok=True)
    for name, text in [("Demo.A.fst", a_text), ("Demo.Spec.fst", SPEC_FST),
                       ("Demo.B.fst", B_FST), ("Demo.I.fsti", I_FSTI),
                       ("Demo.I.fst", I_FST)]:
        with open(os.path.join(root, name), "w", encoding="utf-8") as fh:
            fh.write(text)


def main():
    failures = []
    passes = 0

    def check(cond, what):
        nonlocal passes
        if cond:
            passes += 1
        else:
            failures.append(what)

    tmp = tempfile.mkdtemp(prefix="fstar-inv-test-")
    try:
        root = os.path.join(tmp, "tree")
        write_tree(root, A_FST)
        rc, rows, err = run(root)
        check(rc == 0, "inventory exits 0 on the synthetic tree (stderr: %s)" % err.strip())
        by = {(r["module"], r["name"]): r for r in rows}

        for name, kind in [("stated", "val"), ("helper_one", "let"),
                           ("helper_two", "let"), ("user_a", "let"),
                           ("user_b", "let"), ("rec_lemma", "let rec"),
                           ("even_ok", "let rec"), ("odd_ok", "and"),
                           ("arrow_form", "val"), ("eq_in_requires", "let"),
                           ("qualified_alone", "let"),
                           ("axiom_lemma", "assume val"), ("spec_use", "let"),
                           ("sem_use", "let"), ("multi_line_stmt", "let")]:
            r = by.get(("Demo.A", name))
            check(r is not None, "form found: %s" % name)
            if r is not None:
                check(r["kind"] == kind, "%s has kind %r (got %r)" % (name, kind, r["kind"]))
        check(("Demo.B", "uses_a") in by, "form found: Demo.B.uses_a")
        i_rows = [r for r in rows if r["module"] == "Demo.I"]
        check(len(i_rows) == 1, "an .fsti val and its .fst let give ONE row (got %d)" % len(i_rows))
        check(bool(i_rows) and i_rows[0]["location"].endswith("Demo.I.fsti:3"),
              "the .fsti val is the row kept")

        for hidden in ("hidden_nested", "hidden_line", "hidden_string"):
            check(("Demo.A", hidden) not in by, "commented or quoted lemma NOT found: %s" % hidden)
        check(("Demo.A", "takes_a_lemma") not in by,
              "a Lemma that is only a binder type does not make a lemma")
        check(("Demo.A", "not_a_lemma_string") not in by, "a string definition is not a lemma")

        r = by.get(("Demo.A", "eq_in_requires"))
        check(r is not None and r["statement"].endswith("[SMTPat (x + 0)]"),
              "a `=` inside requires (...) does not end the statement")
        r = by.get(("Demo.A", "multi_line_stmt"))
        check(r is not None and r["statement"] ==
              "multi_line_stmt (a : int) (b : int) : Lemma (a + b == b + a)",
              "multi-line statement normalised (got %r)" % (r and r["statement"]))

        def codes(name, mod="Demo.A"):
            r = by.get((mod, name))
            return set(c.split(":")[0] for c in r["reasons"].split(",")) if r else set()

        check(by[("Demo.A", "helper_two")]["relevance"] == "RELEVANT" and "MULTI" in codes("helper_two"),
              "a lemma used by two proofs of its module is RELEVANT with MULTI")
        check("EXT" in codes("helper_one") and by[("Demo.A", "helper_one")]["relevance"] == "RELEVANT",
              "a lemma used from another module is RELEVANT with EXT")
        check(by[("Demo.A", "odd_ok")]["relevance"] == "HELPER" and codes("odd_ok") == {"LOCAL1"},
              "a lemma used by exactly one local proof, stating nothing listed, is a HELPER")
        check("TOP" in codes("user_a"), "an unreferenced lemma has TOP")
        check("PAT" in codes("eq_in_requires"), "an SMT-pattern lemma has PAT")
        check("ASSUMED" in codes("axiom_lemma"), "an assume val lemma has ASSUMED")
        check("SPEC" in codes("spec_use"), "a statement using a Spec-module definition has SPEC")
        check("SEM" in codes("sem_use"), "a statement naming an entailment has SEM")
        check(by[("Demo.A", "even_ok")]["refs_local"] == "odd_ok",
              "references: even_ok is referenced by odd_ok only (own val/let excluded)")

        # Hash: white-space change -> same hash; token change -> new hash.
        h1 = by[("Demo.A", "multi_line_stmt")]["statement_sha256"]
        h_stated = by[("Demo.A", "stated")]["statement_sha256"]
        a2 = A_FST.replace("let multi_line_stmt (a : int)\n    (b : int)\n  : Lemma (a + b\n           == b + a) = ()",
                           "let multi_line_stmt   (a : int) (b : int) :\tLemma (a + b ==\n\n b + a)\n  = ()")
        a2 = a2.replace("val stated (x : nat)\n  : Lemma (requires x > 0)",
                        "val stated (x : nat) : Lemma (requires x > 0)")
        check(a2 != A_FST, "the white-space variant differs from the original text")
        root2 = os.path.join(tmp, "tree2")
        write_tree(root2, a2)
        rc2, rows2, _ = run(root2)
        by2 = {(r["module"], r["name"]): r for r in rows2}
        check(rc2 == 0 and by2[("Demo.A", "multi_line_stmt")]["statement_sha256"] == h1,
              "a multi-line statement hashes the same after a white-space change")
        check(rc2 == 0 and by2[("Demo.A", "stated")]["statement_sha256"] == h_stated,
              "a val statement hashes the same after a white-space change")
        a3 = A_FST.replace("Lemma (a + b\n           == b + a)", "Lemma (a + b\n           == a + b)")
        root3 = os.path.join(tmp, "tree3")
        write_tree(root3, a3)
        rc3, rows3, _ = run(root3)
        by3 = {(r["module"], r["name"]): r for r in rows3}
        check(rc3 == 0 and by3[("Demo.A", "multi_line_stmt")]["statement_sha256"] != h1,
              "a token change changes the hash")

        empty = os.path.join(tmp, "empty")
        os.makedirs(empty)
        rc4, _, _ = run(empty)
        check(rc4 != 0, "an empty walk exits non-zero")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    for f in failures:
        print("FAIL:", f)
    print("test_fstar_theorem_inventory: %d pass, %d fail (out of %d)"
          % (passes, len(failures), passes + len(failures)))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
