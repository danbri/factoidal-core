"""Tests for tools/assumption-gate.py (https://github.com/danbri/factoidal/issues/975, item 4).

Each test builds a small fixture tree (inventory, Lean sources, ratchet file,
pinned-stage file) in a temporary directory and runs the gate on it with
`--root <tmp>`. The negative tests are the point: a gate never seen to fail
measures nothing. Run:

    python3 -I tests/foundation/test_assumption_gate.py
"""
import os
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
class LawfulStore (α : Type) where
  exact : α → Nat
  assumed_hdtRead : ∀ a : α, True
"""

RATCHET = """# max-entries: 3
io:ReadsWritten  # disk
io:Sha256Agrees  # hash
field:L4Factoidal.Store.LawfulStore.assumed_hdtRead  # hdt reader law
"""

PINS = "readA\nreadB\n"


def make(inventory=INVENTORY, lean=LEAN, ratchet=RATCHET, pins=PINS, leanfile=True):
    d = tempfile.mkdtemp()
    os.makedirs(os.path.join(d, "docs"))
    os.makedirs(os.path.join(d, "foundation"))
    os.makedirs(os.path.join(d, "formal", "lean4", "L4Factoidal"))
    if inventory is not None:
        open(os.path.join(d, "docs", "dataflow-inventory.md"), "w").write(inventory)
    if leanfile:
        open(os.path.join(d, "formal", "lean4", "L4Factoidal", "Store.lean"), "w").write(lean)
    open(os.path.join(d, "foundation", "assumptions.txt"), "w").write(ratchet)
    open(os.path.join(d, "foundation", "proved-stages.txt"), "w").write(pins)
    return d


def gate(root, *extra):
    p = subprocess.run([sys.executable, "-I", GATE, "--root", root, *extra],
                       capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


class AssumptionGate(unittest.TestCase):
    def test_baseline_passes(self):
        rc, out = gate(make())
        self.assertEqual(rc, 0, out)
        self.assertIn("3 named assumptions (2 io, 1 field)", out)

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
        ratchet = RATCHET.replace("max-entries: 3", "max-entries: 4") + \
            "field:L4Factoidal.Store.RdfWriter.assumed_roundTrip  # writer law\n"
        rc, out = gate(make(lean=lean, ratchet=ratchet))
        self.assertEqual(rc, 0, out)

    def test_ratchet_entry_without_reason_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace("  # disk", "")))
        self.assertEqual(rc, 1, out)
        self.assertIn("no reason", out)

    def test_max_entries_mismatch_fails(self):
        rc, out = gate(make(ratchet=RATCHET.replace("max-entries: 3", "max-entries: 9")))
        self.assertEqual(rc, 1, out)
        self.assertIn("max-entries is 9", out)

    def test_stale_entry_fails(self):
        ratchet = RATCHET.replace("max-entries: 3", "max-entries: 4") + "io:Gone  # old\n"
        rc, out = gate(make(ratchet=ratchet))
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
        ratchet = RATCHET.replace("max-entries: 3", "max-entries: 4") + \
            "demoted:readB  # contract rewritten, proof pending\n"
        rc, out = gate(make(inventory="".join(lines), ratchet=ratchet))
        self.assertEqual(rc, 0, out)

    def test_demoted_line_stale_when_proved_again(self):
        ratchet = RATCHET.replace("max-entries: 3", "max-entries: 4") + "demoted:readB  # x\n"
        rc, out = gate(make(ratchet=ratchet))
        self.assertEqual(rc, 1, out)
        self.assertIn("demoted:readB: listed, but the stage is proved again", out)

    def test_empty_inventory_fails(self):
        rc, out = gate(make(inventory=HEADER))
        self.assertEqual(rc, 1, out)
        self.assertIn("empty walk", out)

    def test_no_lean_files_fails(self):
        rc, out = gate(make(leanfile=False))
        self.assertEqual(rc, 1, out)
        self.assertIn("no .lean files found", out)

    def test_unpinned_proved_stage_is_a_note_not_a_failure(self):
        rc, out = gate(make(pins="readA\n"))
        self.assertEqual(rc, 0, out)
        self.assertIn("proved but not pinned", out)


if __name__ == "__main__":
    unittest.main()
