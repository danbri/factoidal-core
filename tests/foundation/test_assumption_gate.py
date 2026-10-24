"""Tests for tools/assumption-gate.py (https://github.com/danbri/factoidal/issues/975, item 4).

Each test builds a small fixture tree in a temporary directory (inventory,
Lean sources, a consumer under Wasm/, the ratchet file, the pinned-stage file)
and runs the gate on it with `--root <tmp>`. Two groups:

  IoFieldAndPins   io: assumptions from the inventory, field: assumptions
                   (`assumed_*` field declarations), pinned proved stages;
  AssumptionNames  name: assumptions (constructors of `AssumptionName` and
                   their uses), the interface-structure checks, and the
                   bare-evaluator check over Wasm/ and Harness/.

The negative tests are the point: a gate never seen to fail measures nothing.
Run:

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

HEADER = ("| area | dir | stage | in | out | contract | status | theorems | IO assumptions "
          "| tests | note |\n|---|---|---|---|---|---|---|---|---|---|---|\n")


def row(stage, status, io="-"):
    return f"| Area {stage} | D | `{stage}` | A | B | `C` | {status} | `t` | {io} | - | n |\n"


INVENTORY = HEADER + row("readA", "proved") + row("readB", "proved") + \
    row("diskIO", "assumed", "`ReadsWritten`") + row("hashIO", "assumed", "`Sha256Agrees`, `ReadsWritten`") + \
    row("suiteOnly", "tested")

LEAN = """import Foo
/-- `assumed_commented : Prop` in a comment is not a field. -/
-- assumed_linecomment : Prop
structure Plain where
  set : Nat
class HdtStore (α : Type) where
  exact : α → Nat
  assumed_hdtRead : ∀ a : α, True
"""

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

BASE_LINES = """io:ReadsWritten  # disk
io:Sha256Agrees  # hash
field:L4Factoidal.HdtStore.HdtStore.assumed_hdtRead  # hdt reader law
field:L4Factoidal.Dataflow.Store.LawfulStore.assumed_contracts  # carries the name: lines
field:L4Factoidal.Dataflow.Store.LawfulDataset.assumed_contracts  # carries the name: lines
name:readerExact  uses=1  # file access
name:isSet  uses=2  # no proof at the call site
"""
BASE_COUNT = 7
RATCHET = f"# max-entries: {BASE_COUNT}\n" + BASE_LINES

PINS = "readA\nreadB\n"


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def make(inventory=INVENTORY, lean=LEAN, store=STORE, reader=READER, consumer=CONSUMER_OK,
         ratchet=RATCHET, pins=PINS, leanfiles=True):
    d = tempfile.mkdtemp()
    os.makedirs(os.path.join(d, "docs"))
    os.makedirs(os.path.join(d, "foundation"))
    os.makedirs(os.path.join(d, "formal", "lean4", "L4Factoidal"))
    if inventory is not None:
        write(os.path.join(d, "docs", "dataflow-inventory.md"), inventory)
    if leanfiles:
        write(os.path.join(d, "formal/lean4/L4Factoidal/HdtStore.lean"), lean)
        write(os.path.join(d, "formal/lean4/L4Factoidal/Dataflow/Store.lean"), store)
        write(os.path.join(d, "formal/lean4/L4Factoidal/Dataflow/Reader.lean"), reader)
        write(os.path.join(d, "formal/lean4/Wasm/Q.lean"), consumer)
    write(os.path.join(d, "foundation", "assumptions.txt"), ratchet)
    write(os.path.join(d, "foundation", "proved-stages.txt"), pins)
    return d


def ratchet_with(extra, n_extra):
    return f"# max-entries: {BASE_COUNT + n_extra}\n" + BASE_LINES + extra


def gate(root, *extra):
    p = subprocess.run([sys.executable, "-I", GATE, "--root", root, *extra],
                       capture_output=True, text=True)
    shutil.rmtree(root)
    return p.returncode, p.stdout + p.stderr


class IoFieldAndPins(unittest.TestCase):
    def test_baseline_passes(self):
        rc, out = gate(make())
        self.assertEqual(rc, 0, out)
        self.assertIn("7 named assumptions (2 io, 3 field, 2 name with 3 uses)", out)

    def test_field_value_is_not_a_declaration(self):
        # `assumed_contracts := ...` in the instances of STORE is not counted;
        # a second declaration in one structure would be.
        lean = LEAN + "def x : HdtStore Nat where\n  exact := id\n  assumed_hdtRead := fun _ => trivial\n"
        rc, out = gate(make(lean=lean))
        self.assertEqual(rc, 0, out)

    def test_new_io_assumption_fails(self):
        inv = INVENTORY + row("netIO", "assumed", "`SocketHonest`")
        rc, out = gate(make(inventory=inv))
        self.assertEqual(rc, 1, out)
        self.assertIn("io:SocketHonest: new assumption", out)

    def test_new_field_assumption_fails(self):
        lean = LEAN + "structure RdfWriter where\n  assumed_roundTrip : True\n"
        rc, out = gate(make(lean=lean))
        self.assertEqual(rc, 1, out)
        self.assertIn("RdfWriter.assumed_roundTrip: new assumption", out)

    def test_new_assumption_passes_when_ratcheted(self):
        lean = LEAN + "structure RdfWriter where\n  assumed_roundTrip : True\n"
        ratchet = ratchet_with("field:L4Factoidal.HdtStore.RdfWriter.assumed_roundTrip  # writer law\n", 1)
        rc, out = gate(make(lean=lean, ratchet=ratchet))
        self.assertEqual(rc, 0, out)

    def test_ratchet_entry_without_reason_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace("  # disk", "")))
        self.assertEqual(rc, 1, out)
        self.assertIn("no reason", out)

    def test_max_entries_mismatch_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace(f"max-entries: {BASE_COUNT}", "max-entries: 9")))
        self.assertEqual(rc, 1, out)
        self.assertIn("max-entries is 9", out)

    def test_stale_entry_fails(self):
        rc, out = gate(make(ratchet=ratchet_with("io:Gone  # old\n", 1)))
        self.assertEqual(rc, 1, out)
        self.assertIn("io:Gone: listed, but no such assumption", out)

    def test_proved_to_tested_fails(self):
        lines = INVENTORY.splitlines(keepends=True)
        lines = [l.replace("| proved |", "| tested |") if "`readB`" in l else l for l in lines]
        rc, out = gate(make(inventory="".join(lines)))
        self.assertEqual(rc, 1, out)
        self.assertIn("readB: was proved", out)

    def test_removed_proved_stage_fails(self):
        lines = [l for l in INVENTORY.splitlines(keepends=True) if "`readB`" not in l]
        rc, out = gate(make(inventory="".join(lines)))
        self.assertEqual(rc, 1, out)
        self.assertIn("readB: was proved", out)

    def test_demotion_passes_when_recorded(self):
        lines = INVENTORY.splitlines(keepends=True)
        lines = [l.replace("| proved |", "| tested |") if "`readB`" in l else l for l in lines]
        ratchet = ratchet_with("demoted:readB  # contract rewritten, proof pending\n", 1)
        rc, out = gate(make(inventory="".join(lines), ratchet=ratchet))
        self.assertEqual(rc, 0, out)

    def test_demoted_line_stale_when_proved_again(self):
        rc, out = gate(make(ratchet=ratchet_with("demoted:readB  # x\n", 1)))
        self.assertEqual(rc, 1, out)
        self.assertIn("demoted:readB: listed, but the stage is proved again", out)

    def test_empty_inventory_fails(self):
        rc, out = gate(make(inventory=HEADER))
        self.assertEqual(rc, 1, out)
        self.assertIn("empty walk", out)

    def test_no_lean_files_fails(self):
        rc, out = gate(make(leanfiles=False))
        self.assertEqual(rc, 1, out)
        self.assertIn("no .lean files found", out)

    def test_unpinned_proved_stage_is_a_note_not_a_failure(self):
        rc, out = gate(make(pins="readA\n"))
        self.assertEqual(rc, 0, out)
        self.assertIn("proved but not pinned", out)

    def test_unknown_kind_fails(self):
        rc, out = gate(make(ratchet=ratchet_with("other:x  # y\n", 1)))
        self.assertEqual(rc, 1, out)
        self.assertIn("unknown kind", out)


class AssumptionNames(unittest.TestCase):
    def test_new_use_fails(self):
        rc, out = gate(make(store=STORE + "\ndef c : List Assumption := [⟨.readerExact, True⟩]\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("name:readerExact: uses=1 listed, 2 in the tree", out)

    def test_stale_count_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace("name:isSet  uses=2", "name:isSet  uses=3")))
        self.assertEqual(rc, 1, out)
        self.assertIn("stale", out)

    def test_new_name_fails(self):
        rc, out = gate(make(store=STORE.replace("| isSet\n", "| isSet\n  | other\n")))
        self.assertEqual(rc, 1, out)
        self.assertIn("name:other: new assumption (uses=0)", out)

    def test_name_line_without_uses_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace("name:isSet  uses=2", "name:isSet")))
        self.assertEqual(rc, 1, out)
        self.assertIn("not 'name:<Ctor>  uses=<N>  # reason'", out)

    def test_no_reason_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace("  # file access", "")))
        self.assertEqual(rc, 1, out)
        self.assertIn("no reason", out)

    def test_bare_evaluator_fails(self):
        rc, out = gate(make(consumer=CONSUMER_OK + "def r := runSelectQueryBackendDataset env q dsb\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("Wasm/Q.lean:3: runSelectQueryBackendDataset", out)

    def test_qualified_bare_evaluator_fails(self):
        rc, out = gate(make(consumer=CONSUMER_OK + "def r := StoreDataset.indexedDatasetBackend ds\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("indexedDatasetBackend", out)

    def test_no_inductive_fails(self):
        rc, out = gate(make(store="structure LawfulStore where\n  x : Nat\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("no constructor", out)

    def test_store_without_assumption_field_fails(self):
        store = STORE.replace("structure LawfulDataset where\n  backend : Nat\n  assumed_contracts : List Assumption := []\n",
                              "structure LawfulDataset where\n  backend : Nat\n")
        rc, out = gate(make(store=store))
        self.assertEqual(rc, 1, out)
        self.assertIn("LawfulDataset must declare the field `assumed_contracts`", out)

    def test_missing_reader_fails(self):
        rc, out = gate(make(reader="structure Other where\n  x : Nat\n"))
        self.assertEqual(rc, 1, out)
        self.assertIn("RdfReader not found", out)


if __name__ == "__main__":
    unittest.main()
