#!/usr/bin/env python3
"""Small filesystem tests for npm evidence capture and verification."""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


TOOL = Path(__file__).with_name("snapshot-npm-audit.py")
SPEC = importlib.util.spec_from_file_location("snapshot_npm_audit", TOOL)
SNAPSHOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SNAPSHOT)


class SnapshotTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="npm-audit-test-", dir="/private/tmp")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "review"
        self.source.mkdir()
        self.output = self.root / "snapshot"
        self.original = {
            "REVIEW-0.11.0.md": b"review\n\x00exact bytes\r\n",
            "REPAIR-NOTES.md": b"notes\r\n",
            "audit/run.mjs": b"run()\n",
            "audit/LICENSE": b"license\n",
            "logs/original-setup-failure.log": b"not found\n",
            "_LEAN/specifications/rdf.html": b"<html>raw</html>\n",
            "_LEAN/docs/findings.md": b"findings\n",
            "_LEAN/ledger/obligations.json": b"{}\n",
        }
        for name, data in self.original.items():
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        for excluded in ("audit/node_modules/dep.json", "package/bundle.mjs",
                         "suites/tests.json", "_LEAN/specifications/rdf-tests/test.md"):
            path = self.source / excluded
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"external dependency\n")

    def capture(self):
        return SNAPSHOT.capture(self.source, self.output, 1024)

    def rewrite_manifest(self, manifest):
        (self.output / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")

    def test_exact_bytes_and_exclusions_and_exclusive_output(self):
        manifest = self.capture()
        self.assertEqual(len(self.original), manifest["file_count"])
        self.assertEqual(sum(map(len, self.original.values())), manifest["total_bytes"])
        self.assertEqual(set(self.original), {entry["path"] for entry in manifest["files"]})
        for name, data in self.original.items():
            self.assertEqual(data, (self.output / name).read_bytes())
            self.assertEqual(data, (self.source / name).read_bytes())
        self.assertEqual(manifest, SNAPSHOT.verify(self.output))
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.capture()

    def test_tampered_missing_and_unexpected_files_fail(self):
        self.capture()
        path = self.output / "audit/run.mjs"
        path.write_bytes(b"tampered")
        with self.assertRaisesRegex(ValueError, "mismatch"):
            SNAPSHOT.verify(self.output)
        path.unlink()
        with self.assertRaises(OSError):
            SNAPSHOT.verify(self.output)
        path.write_bytes(self.original["audit/run.mjs"])
        (self.output / "unexpected.txt").write_text("extra")
        with self.assertRaisesRegex(ValueError, "unexpected"):
            SNAPSHOT.verify(self.output)

    def test_manifest_rejects_traversal_and_duplicate_paths(self):
        manifest = self.capture()
        original = manifest["files"][0]["path"]
        for unsafe in ("../escape", "/absolute", "audit/../escape", "audit//run.mjs", "audit\\run.mjs", "manifest.json"):
            with self.subTest(path=unsafe):
                manifest["files"][0]["path"] = unsafe
                self.rewrite_manifest(manifest)
                with self.assertRaises(ValueError):
                    SNAPSHOT.verify(self.output)
        manifest["files"][0]["path"] = original
        manifest["files"].append(dict(manifest["files"][0]))
        self.rewrite_manifest(manifest)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            SNAPSHOT.verify(self.output)

    def test_symlinks_fail_in_source_and_snapshot(self):
        source_file = self.source / "audit/run.mjs"
        source_file.unlink()
        source_file.symlink_to(self.source / "REPAIR-NOTES.md")
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.capture()
        source_file.unlink()
        source_file.write_bytes(self.original["audit/run.mjs"])
        self.capture()
        for relative in ("audit/run.mjs", "manifest.json"):
            path = self.output / relative
            data = path.read_bytes()
            path.unlink()
            path.symlink_to(source_file)
            with self.assertRaises((OSError, ValueError)):
                SNAPSHOT.verify(self.output)
            path.unlink()
            path.write_bytes(data)
        (self.output / "external-directory").symlink_to(self.source, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            SNAPSHOT.verify(self.output)

    def test_missing_source_and_empty_inventory_exit_nonzero(self):
        for source in (self.root / "absent", self.source):
            if source == self.source:
                (source / "audit/run.mjs").unlink()
                (source / "audit/LICENSE").unlink()
            result = subprocess.run([sys.executable, str(TOOL), "--source", str(source),
                                     "--output", str(self.output)], capture_output=True, text=True)
            self.assertNotEqual(0, result.returncode)
            self.assertFalse(self.output.exists())
            self.assertIn("missing" if source != self.source else "empty source inventory", result.stderr)

    def test_specification_budget_is_recorded(self):
        manifest = SNAPSHOT.capture(self.source, self.output, 0)
        self.assertNotIn("_LEAN/specifications/rdf.html", {entry["path"] for entry in manifest["files"]})
        self.assertTrue(any(entry["reason"] == "specification byte budget"
                            for entry in manifest["excluded_specification_entries"]))


if __name__ == "__main__":
    unittest.main()
