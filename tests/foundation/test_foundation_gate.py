"""Tests for tools/foundation-gate.py (https://github.com/danbri/factoidal/issues/975).

Each test builds a small fixture tree in a temporary directory:

    <tmp>/foundation/manifest.toml
    <tmp>/foundation/allow-imports.txt
    <tmp>/formal/lean4/L4Factoidal/**.lean

and runs the gate on it with `--root <tmp>`. Run:

    python3 -I tests/foundation/test_foundation_gate.py
"""
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
GATE = os.path.join(HERE, "..", "..", "tools", "foundation-gate.py")

MANIFEST = """\
[manifest]
version = 0
status = "version 0, to be refined by experts"
source_root = "formal/lean4"

[[module]]
name = "L4Factoidal.A.Core"
level = 0
spec = "RDF 1.1 Concepts §3"

[[module]]
name = "L4Factoidal.B.Algebra"
level = 1
spec = "SPARQL 1.1 Query §18"
"""

CORE = """/-! L4Factoidal.A.Core -- a doc comment that says
import L4Factoidal.Impl.Fast
inside a comment, which the gate must ignore. -/
import Std.Data.HashMap
-- import L4Factoidal.Impl.Other (a line comment, also ignored)

def x := 1
"""

ALGEBRA = """import L4Factoidal.A.Core
import Lean

def y := 2
"""

IMPL = """import L4Factoidal.B.Algebra

def z := 3
"""


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


class FoundationGateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = self.tmp.name
        lean = os.path.join(self.root, "formal", "lean4", "L4Factoidal")
        self.lean = lean
        write(os.path.join(self.root, "foundation", "manifest.toml"), MANIFEST)
        self.set_allow([])
        write(os.path.join(lean, "A", "Core.lean"), CORE)
        write(os.path.join(lean, "B", "Algebra.lean"), ALGEBRA)
        write(os.path.join(lean, "Impl", "Fast.lean"), IMPL)

    def tearDown(self):
        self.tmp.cleanup()

    def set_allow(self, lines, max_entries=None):
        if max_entries is None:
            max_entries = len(lines)
        body = "# max-entries: %d\n" % max_entries + "".join(l + "\n" for l in lines)
        write(os.path.join(self.root, "foundation", "allow-imports.txt"), body)

    def run_gate(self):
        p = subprocess.run(
            [sys.executable, "-I", GATE, "--root", self.root],
            capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr

    def test_clean_tree_passes(self):
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("2 foundation modules", out)

    def test_missing_module_fails(self):
        os.remove(os.path.join(self.lean, "B", "Algebra.lean"))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("L4Factoidal.B.Algebra: listed in the manifest, no file", out)

    def test_foundation_imports_implementation_fails(self):
        write(os.path.join(self.lean, "B", "Algebra.lean"),
              "import L4Factoidal.A.Core\nimport L4Factoidal.Impl.Fast\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("formal/lean4/L4Factoidal/B/Algebra.lean:2: impl", out)
        self.assertIn("L4Factoidal.B.Algebra -> L4Factoidal.Impl.Fast", out)

    def test_level_violation_fails(self):
        write(os.path.join(self.lean, "A", "Core.lean"),
              "import L4Factoidal.B.Algebra\n")
        write(os.path.join(self.lean, "B", "Algebra.lean"), "def y := 2\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("formal/lean4/L4Factoidal/A/Core.lean:1: level", out)
        self.assertIn("level 0 imports level 1", out)

    def test_allowed_edge_passes(self):
        write(os.path.join(self.lean, "B", "Algebra.lean"),
              "import L4Factoidal.A.Core\nimport L4Factoidal.Impl.Fast\n")
        self.set_allow(["L4Factoidal.B.Algebra -> L4Factoidal.Impl.Fast  # fixture reason"])
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)

    def test_allow_entry_without_reason_fails(self):
        write(os.path.join(self.lean, "B", "Algebra.lean"),
              "import L4Factoidal.A.Core\nimport L4Factoidal.Impl.Fast\n")
        self.set_allow(["L4Factoidal.B.Algebra -> L4Factoidal.Impl.Fast"])
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("no reason", out)

    def test_stale_allow_entry_fails(self):
        self.set_allow(["L4Factoidal.B.Algebra -> L4Factoidal.Impl.Fast  # gone"])
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("stale", out)

    def test_allow_list_growth_fails(self):
        write(os.path.join(self.lean, "B", "Algebra.lean"),
              "import L4Factoidal.A.Core\nimport L4Factoidal.Impl.Fast\n")
        self.set_allow(["L4Factoidal.B.Algebra -> L4Factoidal.Impl.Fast  # new"],
                       max_entries=0)
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("allow list has 1 entries, max-entries is 0", out)

    def test_empty_walk_fails(self):
        for d, _, fs in os.walk(self.lean):
            for f in fs:
                os.remove(os.path.join(d, f))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("no .lean files", out)

    def test_bad_level_fails(self):
        write(os.path.join(self.root, "foundation", "manifest.toml"),
              MANIFEST.replace("level = 1", "level = 7"))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("level 7", out)


if __name__ == "__main__":
    unittest.main()
