"""Runner regressions. These synthetic transport tests are not WPT results."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import suite


class RunnerTests(unittest.TestCase):
    def test_missing_and_corrupt_fixtures(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = {"files": [{"path": "test.svg", "sha256": hashlib.sha256(b"svg").hexdigest()}]}
            manifest["revision"] = "pin"
            (root / "source.json").write_text(json.dumps({"revision": "pin", "paths": ["test.svg"]}))
            (root / "manifest.json").write_text(json.dumps(manifest))
            self.assertIn("missing", suite.fixtures(root)[1][0])
            (root / "upstream").mkdir()
            (root / "upstream/test.svg").write_bytes(b"changed")
            self.assertIn("hash mismatch", suite.fixtures(root)[1][0])

    def test_process_failures_are_distinct(self):
        with tempfile.TemporaryDirectory() as directory:
            for log, status in [("SVG profile: unsupported SVG element: path", "unsupported"),
                                ("SVG profile: malformed XML", "rejected"),
                                ("GPU BLOCKED adapter=null", "unavailable")]:
                with self.subTest(status=status), patch("suite.subprocess.run", return_value=
                        subprocess.CompletedProcess([], 2, "", log)):
                    self.assertEqual(suite.invoke(["engine"], Path("x.svg"), Path(directory)/"out", True, 1)[0], status)
            with patch("suite.subprocess.run", side_effect=FileNotFoundError("engine missing")):
                self.assertEqual(suite.invoke(["engine"], Path("x.svg"), Path(directory)/"out", True, 1)[0], "unavailable")

    def test_accepted_is_not_an_image_match(self):
        manifest = {"revision": "pin", "scope": {}, "cases": [
            {"test": "test.svg", "reference": "ref.svg", "requiredRuntime": [], "fuzzy": [[0,0],[0,0]]}]}
        with patch("suite.invoke", return_value=("accepted", "compiled")):
            report = suite.run(manifest, ["engine"])
        self.assertEqual(report["counts"]["accepted"], 1)
        self.assertEqual(report["counts"]["match"], 0)

    def test_render_match_mismatch_and_fuzzy(self):
        manifest = {"revision": "pin", "scope": {}, "cases": [
            {"test": "test.svg", "reference": "ref.svg", "requiredRuntime": [], "fuzzy": [[0,0],[0,0]]}]}
        for difference, fuzzy, expected in [(0, [[0,0],[0,0]], "match"),
                                             (1, [[0,0],[0,0]], "mismatch"),
                                             (1, [[0,1],[0,1]], "match")]:
            def invoke(command, source, output, artifact, timeout):
                pixels = bytearray([32, 10, 13] * (800 * 600))
                if source.name == "test.svg":
                    pixels[0] += difference
                output.write_bytes(b"P6\n800 600\n255\n" + pixels)
                return "accepted", "rendered"
            manifest["cases"][0]["fuzzy"] = fuzzy
            with self.subTest(expected=expected), patch("suite.invoke", side_effect=invoke):
                report = suite.run(manifest, ["engine"], render=True)
            self.assertEqual(report["counts"][expected], 1)

    def test_missing_reference_render_and_runtime_cannot_pass(self):
        case = {"test": "test.svg", "reference": "ref.svg", "requiredRuntime": [], "fuzzy": [[0,0],[0,0]]}
        manifest = {"revision": "pin", "scope": {}, "cases": [case]}
        with patch("suite.invoke", side_effect=[("accepted", ""), ("unsupported", "reference path")]):
            self.assertEqual(suite.run(manifest, ["engine"], render=True)["counts"]["unsupported"], 1)
        case["requiredRuntime"] = ["script/reftest-wait runtime"]
        with patch("suite.invoke", return_value=("accepted", "")):
            self.assertEqual(suite.run(manifest, ["engine"], render=True)["counts"]["unsupported"], 1)

    def test_no_output_is_unavailable(self):
        with tempfile.TemporaryDirectory() as directory, patch("suite.subprocess.run", return_value=
                subprocess.CompletedProcess([], 0, "", "")):
            self.assertEqual(suite.invoke(["engine"], Path("x.svg"), Path(directory)/"out", True, 1)[0], "unavailable")


if __name__ == "__main__":
    unittest.main()
