#!/usr/bin/env python3
"""Exercise premerge's actual Std walk with the builder's shared roots."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
PREMERGE = (ROOT / "tools/premerge.sh").read_text()
WALK = "std_in_wasm() {\n" + PREMERGE.split("std_in_wasm() {\n", 1)[1].split("\n}\n", 1)[0] + "\n}"
BUILDER = (ROOT / "labs/demos/foafnaut/build-web-render.sh").read_text()


class StdWalkTests(unittest.TestCase):
    def run_walk(self, second_import="Std.Data.HashMap", roots="L4Factoidal.First L4Factoidal.Second"):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            project = tree / "formal/lean4"
            modules = project / "L4Factoidal"
            modules.mkdir(parents=True)
            (project / ".gitignore").write_text("")
            (modules / "First.lean").write_text("import Std.Data.HashMap\n")
            (modules / "Second.lean").write_text(f"import {second_import}\n")
            lab = tree / "labs/demos/foafnaut"
            lab.mkdir(parents=True)
            builder = re.sub(r"^CORE=\([^\n]*\)$", f"CORE=({roots})", BUILDER, flags=re.M)
            (lab / "build-web-render.sh").write_text(builder)
            env = dict(os.environ, ROOT=str(ROOT), TREE=str(tree), LAB=str(lab))
            return subprocess.run(["bash", "-uc", WALK + "\nstd_in_wasm"], env=env,
                                  text=True, capture_output=True)

    def test_allowed_std_imports(self):
        result = self.run_walk()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_forbidden_std_in_second_shared_root(self):
        result = self.run_walk(second_import="Std")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Second.lean: import Std:", result.stderr)

    def test_empty_shared_roots_fail_closed(self):
        for roots in ("", "   ", "not-a-Lean-module"):
            with self.subTest(roots=roots):
                result = self.run_walk(roots=roots)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("CORE root", result.stdout)


if __name__ == "__main__":
    unittest.main()
