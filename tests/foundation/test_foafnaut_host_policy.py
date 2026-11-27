"""Tests for tools/foafnaut-host-policy-audit.py (https://github.com/danbri/factoidal-core/issues/1188).
Run: python3 -I tests/foundation/test_foafnaut_host_policy.py"""
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "..", "..", "tools", "foafnaut-host-policy-audit.py")

HOST = "// limits\nconst LIMIT = 300000; // ms\nlet i = 0;\nconst x = y ?? 256;\nif (ms > 16) go();\n/* const NOT = 5; */\nconst n = Math.max(0, k);\n"


class PolicyAuditTest(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        os.makedirs(os.path.join(self.root, "tools"))
        os.makedirs(os.path.join(self.root, "foundation"))
        d = os.path.join(self.root, "labs", "demos", "foafnaut")
        os.makedirs(d)
        shutil.copy(TOOL, os.path.join(self.root, "tools", "foafnaut-host-policy-audit.py"))
        self.host = os.path.join(d, "host.ts")
        open(self.host, "w").write(HOST)
        open(os.path.join(d, "host_test.ts"), "w").write("const T = 99;\n")
        open(os.path.join(self.root, "foundation", "foafnaut-host-policy.txt"), "w").write("# header\n")
        subprocess.run(["git", "init", "-q", self.root], check=True)
        subprocess.run(["git", "-C", self.root, "add", "-A"], check=True)
        self.run_tool("--record")
        self.allow = os.path.join(self.root, "foundation", "foafnaut-host-policy.txt")
        s = open(self.allow).read().replace("TO REVIEW", "test reason")
        open(self.allow, "w").write(s)

    def tearDown(self):
        shutil.rmtree(self.root)

    def run_tool(self, *args):
        p = subprocess.run([sys.executable, "-I", os.path.join(self.root, "tools", "foafnaut-host-policy-audit.py"), *args],
                           capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr

    def test_counts(self):
        rc, out = self.run_tool("--sites", "labs/demos/foafnaut/host.ts")
        kinds = [l.split()[1] for l in out.strip().split("\n")]
        self.assertEqual(sorted(kinds), ["clamp", "const-num", "default-num", "threshold"])
        rc, out = self.run_tool()
        self.assertEqual(rc, 0, out)
        self.assertIn("1 host runtime files, 4 policy sites", out)

    def test_new_site_fails(self):
        open(self.host, "a").write("const MORE = 42;\n")
        rc, out = self.run_tool()
        self.assertEqual(rc, 1, out)
        self.assertIn("more than the 4 recorded", out)

    def test_removed_site_must_lower(self):
        open(self.host, "w").write(HOST.replace("const LIMIT = 300000; // ms\n", ""))
        rc, out = self.run_tool()
        self.assertEqual(rc, 1, out)
        self.assertIn("fewer than the 4 recorded", out)

    def test_reason_required(self):
        s = open(self.allow).read().replace("test reason", "TO REVIEW")
        open(self.allow, "w").write(s)
        rc, out = self.run_tool()
        self.assertEqual(rc, 1, out)
        self.assertIn("no reason", out)


if __name__ == "__main__":
    unittest.main()
