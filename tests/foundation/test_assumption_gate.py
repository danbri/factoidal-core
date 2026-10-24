"""Tests for tools/assumption-gate.py (https://github.com/danbri/factoidal/issues/975, item 4).

Each test builds a small fixture tree in a temporary directory (Store.lean with
`inductive AssumptionName`, Reader.lean, a consumer under Wasm/, and
foundation/assumptions.txt) and runs the gate on it with `--root <tmp>`. Run:

    python3 -I tests/foundation/test_assumption_gate.py
"""
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
GATE = os.path.join(HERE, "..", "..", "tools", "assumption-gate.py")

STORE = """/- header `runSelectQueryBackendDataset` -/
inductive AssumptionName where
  /-- doc -/
  | readerExact
  | isSet
  deriving Repr

structure LawfulStore where
  backend : Nat
  assumed_contracts : List Assumption := []
  law : True

structure LawfulDataset where
  backend : Nat
  assumed_contracts : List Assumption := []
  law : True

def a : LawfulStore where
  backend := 0
  assumed_contracts := [⟨.readerExact, True⟩]
  law := trivial

-- ⟨.isSet, True⟩ in a comment is not a use
def b : LawfulStore where
  backend := 0
  assumed_contracts := [⟨.isSet, True⟩, ⟨AssumptionName.isSet, True⟩]
  law := trivial
"""

READER = """structure RdfReader where
  run : Nat
  sound : True
"""

CONSUMER_OK = """-- runSelectQueryBackendDataset in a comment
def q (L : LawfulDataset) := L.runSelect env q
"""

LIST_OK = """# max-entries: 2
readerExact  uses=1  # file access
isSet  uses=2  # no proof at the call site
"""


def write(path, text):
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def tree(store=STORE, reader=READER, consumer=CONSUMER_OK, lst=LIST_OK):
    d = tempfile.mkdtemp()
    os.makedirs(os.path.join(d, "formal/lean4/L4Factoidal/Dataflow"))
    os.makedirs(os.path.join(d, "formal/lean4/Wasm"))
    os.makedirs(os.path.join(d, "foundation"))
    write(os.path.join(d, "formal/lean4/L4Factoidal/Dataflow/Store.lean"), store)
    write(os.path.join(d, "formal/lean4/L4Factoidal/Dataflow/Reader.lean"), reader)
    write(os.path.join(d, "formal/lean4/Wasm/Q.lean"), consumer)
    write(os.path.join(d, "foundation/assumptions.txt"), lst)
    return d


def run(d):
    p = subprocess.run([sys.executable, "-I", GATE, "--root", d], capture_output=True, text=True)
    shutil.rmtree(d)
    return p.returncode, p.stdout + p.stderr


class AssumptionGateTests(unittest.TestCase):
    def test_pass(self):
        rc, out = run(tree())
        self.assertEqual(rc, 0, out)
        self.assertIn("2 named assumptions, 3 uses", out)
        self.assertIn("RdfReader has no", out)

    def test_new_use_fails(self):
        rc, out = run(tree(store=STORE + "\ndef c : List Assumption := [⟨.readerExact, True⟩]\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("readerExact uses=1 listed, 2 in the tree", out)

    def test_stale_count_fails(self):
        rc, out = run(tree(lst=LIST_OK.replace("isSet  uses=2", "isSet  uses=3")))
        self.assertEqual(rc, 1, out)
        self.assertIn("stale", out)

    def test_new_name_fails(self):
        rc, out = run(tree(store=STORE.replace("| isSet\n", "| isSet\n  | other\n")))
        self.assertEqual(rc, 1, out)
        self.assertIn("assumption other (uses=0) has no line", out)

    def test_no_reason_fails(self):
        rc, out = run(tree(lst=LIST_OK.replace("  # file access", "")))
        self.assertEqual(rc, 1, out)
        self.assertIn("has no reason", out)

    def test_header_fails(self):
        rc, out = run(tree(lst=LIST_OK.replace("max-entries: 2", "max-entries: 3")))
        self.assertEqual(rc, 1, out)
        self.assertIn("max-entries 3, 2 lines", out)

    def test_bare_evaluator_fails(self):
        rc, out = run(tree(consumer=CONSUMER_OK + "def r := runSelectQueryBackendDataset env q dsb\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("Wasm/Q.lean:3: runSelectQueryBackendDataset", out)

    def test_qualified_bare_evaluator_fails(self):
        rc, out = run(tree(consumer=CONSUMER_OK + "def r := StoreDataset.indexedDatasetBackend ds\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("indexedDatasetBackend", out)

    def test_no_inductive_fails(self):
        rc, out = run(tree(store="structure LawfulStore where\n  x : Nat\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("no constructor", out)


if __name__ == "__main__":
    unittest.main()
