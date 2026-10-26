"""Native harness regressions: missing/unreadable/empty fixtures must fail.

Requires `cd formal/lean4 && lake build`. Synthetic recognized-but-unsupported
entries isolate fixture discovery from validator semantics; they are not
conformance tests. No downloaded fixtures are needed.
"""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "formal/lean4/.lake/build/bin"
PREFIX = '''@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix sht: <http://www.w3.org/ns/shacl-test#> .
'''
NODE_STUB = PREFIX + '<urn:test> a sht:Validate .\n'
RULE_STUB = PREFIX + '<> mf:entries ( <urn:test> ) . <urn:test> a <urn:unknown> .\n'


class HarnessTests(unittest.TestCase):
    def run_harness(self, name, fixture):
        binary = BIN / name
        self.assertTrue(binary.is_file(), f"Build the native harness first: {binary}")
        return subprocess.run([str(binary), str(fixture)], cwd=ROOT,
                              capture_output=True, text=True, timeout=30)

    def assert_failure(self, result, diagnostic):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(diagnostic, result.stdout)

    def test_nodeexpr_manifest_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = Path(tmp) / "manifest.ttl"
            self.assert_failure(self.run_harness("l4shacl-nodeexpr", manifest), "MISSING")
            for body, diagnostic in [("@prefix", "UNPARSED"),
                                     (PREFIX, "EMPTY")]:
                manifest.write_text(body)
                self.assert_failure(self.run_harness("l4shacl-nodeexpr", manifest), diagnostic)
            manifest.write_text(NODE_STUB)
            valid = self.run_harness("l4shacl-nodeexpr", manifest)
            self.assertEqual(valid.returncode, 0, valid.stdout + valid.stderr)
            self.assertIn("1 unsupported", valid.stdout)

    def test_missing_nodeexpr_include_is_not_dropped(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "valid.ttl").write_text(NODE_STUB)
            manifest = root / "manifest.ttl"
            manifest.write_text(PREFIX + '<> mf:include <valid.ttl>, <missing.ttl> .\n')
            result = self.run_harness("l4shacl-nodeexpr", manifest)
            self.assert_failure(result, "MISSING")
            self.assertIn("1 unsupported", result.stdout)
            self.assertIn("1 fail", result.stdout)

    def test_rules_manifest_errors_among_readable_siblings(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for category in ["syntax", "wellformed", "stratification", "eval"]:
                directory = root / category
                directory.mkdir()
                (directory / "manifest.ttl").write_text(RULE_STUB)
            valid = self.run_harness("l4shacl-rules", root)
            self.assertEqual(valid.returncode, 0, valid.stdout + valid.stderr)
            self.assertIn("4 unsupported", valid.stdout)
            manifest = root / "syntax/manifest.ttl"
            manifest.unlink()
            self.assert_failure(self.run_harness("l4shacl-rules", root), "MISSING")
            for body, diagnostic in [("@prefix", "UNPARSED"),
                                     (PREFIX, "EMPTY")]:
                manifest.write_text(body)
                self.assert_failure(self.run_harness("l4shacl-rules", root), diagnostic)


if __name__ == "__main__":
    unittest.main()
