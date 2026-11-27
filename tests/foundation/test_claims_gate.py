"""Tests for tools/claims-gate.py (https://github.com/danbri/factoidal-core/issues/1178
and https://github.com/danbri/factoidal-core/issues/1179).

Each test builds a small tree in a temporary directory (a lakefile, eleven
modules, one register) and runs a copy of the gate there.
Run: python3 -I -m unittest tests/foundation/test_claims_gate.py -v
"""
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
GATE = os.path.join(HERE, "..", "..", "tools", "claims-gate.py")

THEOREMS = textwrap.dedent('''\
    import L4Factoidal.Spec
    namespace L4Factoidal.Demo

    /-- doc -/
    theorem double_pos (n : Nat) (h : 0 < n) : let m := n + n
        0 < m := by
      omega

    theorem double_pos_witness : let m := 1 + 1
        0 < m := double_pos 1 (by decide)

    end L4Factoidal.Demo
    ''')

SPEC = textwrap.dedent('''\
    namespace L4Factoidal.Demo
    mutual
    def Good : Nat -> Prop
      | _ => True
    end
    end L4Factoidal.Demo
    ''')

REGISTER = textwrap.dedent('''\
    [meta]
    max-entries = 5

    [[claim]]
    id = "double-pos"
    theorem = "L4Factoidal.Demo.double_pos"
    file = "formal/lean4/L4Factoidal/Demo.lean"
    about = "double"
    says = "doubling a positive number is positive"
    does_not_say = "nothing about zero"
    assumptions = ["h: n is positive"]
    status = "proposed"
    statement_sha256 = "TBD"
    spec_defs = [
      { name = "L4Factoidal.Demo.Good", file = "formal/lean4/L4Factoidal/Spec.lean", sha256 = "TBD" },
    ]
    witness = { name = "L4Factoidal.Demo.double_pos_witness", file = "formal/lean4/L4Factoidal/Demo.lean" }
    ''')


class ClaimsGateTest(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        os.makedirs(os.path.join(self.root, "tools"))
        shutil.copy(GATE, os.path.join(self.root, "tools", "claims-gate.py"))
        lean = os.path.join(self.root, "formal", "lean4")
        os.makedirs(os.path.join(lean, "L4Factoidal"))
        open(os.path.join(lean, "lakefile.lean"), "w").write("lean_lib L4Factoidal\n")
        fillers = [f"L4Factoidal.M{i}" for i in range(10)]
        for m in fillers:
            open(os.path.join(lean, *m.split(".")) + ".lean", "w").write("-- filler\n")
        open(os.path.join(lean, "L4Factoidal.lean"), "w").write(
            "".join(f"import {m}\n" for m in fillers + ["L4Factoidal.Demo"]))
        self.demo = os.path.join(lean, "L4Factoidal", "Demo.lean")
        self.spec = os.path.join(lean, "L4Factoidal", "Spec.lean")
        open(self.demo, "w").write(THEOREMS)
        open(self.spec, "w").write(SPEC)
        os.makedirs(os.path.join(self.root, "foundation"))
        self.reg = os.path.join(self.root, "foundation", "claims.toml")
        open(self.reg, "w").write(REGISTER)
        self.run_gate("--record", "--all")

    def tearDown(self):
        shutil.rmtree(self.root)

    def run_gate(self, *args):
        p = subprocess.run([sys.executable, "-I", os.path.join(self.root, "tools", "claims-gate.py"), *args],
                           capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr

    def edit(self, path, old, new):
        s = open(path).read()
        self.assertIn(old, s)
        open(path, "w").write(s.replace(old, new))

    def test_pass(self):
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("1 claims", out)
        self.assertIn("1 with a hypothesis witness", out)

    def test_statement_change_fails(self):
        self.edit(self.demo, "0 < m", "0 <= m")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("statement of L4Factoidal.Demo.double_pos changed", out)

    def test_hypothesis_change_fails(self):
        self.edit(self.demo, "(h : 0 < n)", "(h : 0 < n) (h2 : n = 0)")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)

    def test_proof_and_comment_change_passes(self):
        self.edit(self.demo, "  omega", "  simp only []\n  omega -- other proof")
        self.edit(self.demo, "/-- doc -/", "/-- other doc -/")
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)

    def test_spec_change_fails(self):
        self.edit(self.spec, "| _ => True", "| _ => False")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("specification definition L4Factoidal.Demo.Good changed", out)

    def test_record_after_review_passes(self):
        self.edit(self.demo, "0 < m", "0 <= m")
        self.run_gate("--record", "double-pos")
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)

    def test_missing_theorem_fails(self):
        self.edit(self.demo, "theorem double_pos", "theorem double_pos'")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("no theorem L4Factoidal.Demo.double_pos", out)

    def test_unreached_module_fails(self):
        self.edit(os.path.join(self.root, "formal", "lean4", "L4Factoidal.lean"), "import L4Factoidal.Demo\n", "")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("reached by no build root", out)

    def test_witness_must_apply_claim(self):
        self.edit(self.demo, "0 < m := double_pos 1 (by decide)", "0 < m := by decide")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("does not apply", out)

    def test_private_fails(self):
        self.edit(self.demo, "theorem double_pos", "private theorem double_pos")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)

    def test_missing_field_and_status(self):
        self.edit(self.reg, 'does_not_say = "nothing about zero"\n', "")
        self.edit(self.reg, 'status = "proposed"', 'status = "approved"')
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("field does_not_say is missing", out)
        self.assertIn("status 'approved'", out)

    def test_reviewed_needs_record(self):
        self.edit(self.reg, 'status = "proposed"', 'status = "reviewed"')
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("needs a `reviewed` field", out)

    def test_axioms(self):
        good = os.path.join(self.root, "good.log")
        open(good, "w").write("claim double-pos\n'L4Factoidal.Demo.double_pos' depends on axioms: [propext, Quot.sound]\n")
        rc, out = self.run_gate("--check-axioms", good)
        self.assertEqual(rc, 0, out)
        bad = os.path.join(self.root, "bad.log")
        open(bad, "w").write("claim double-pos\n'L4Factoidal.Demo.double_pos' depends on axioms: [propext, sorryAx]\n")
        rc, out = self.run_gate("--check-axioms", bad)
        self.assertEqual(rc, 1, out)
        self.assertIn("sorryAx", out)
        nd = os.path.join(self.root, "nd.log")
        open(nd, "w").write("claim double-pos\n'x' depends on axioms: [Lean.ofReduceBool]\n")
        self.assertEqual(self.run_gate("--check-axioms", nd)[0], 1)
        empty = os.path.join(self.root, "empty.log")
        open(empty, "w").write("")
        self.assertEqual(self.run_gate("--check-axioms", empty)[0], 1)

    def test_axioms_lean_file(self):
        out = os.path.join(self.root, "Claims.lean")
        self.run_gate("--axioms-lean", out)
        text = open(out).read()
        self.assertIn("import L4Factoidal.Demo", text)
        self.assertIn("#print axioms L4Factoidal.Demo.double_pos", text)


if __name__ == "__main__":
    unittest.main()
