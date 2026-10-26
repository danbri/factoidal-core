#!/usr/bin/env python3
"""Exercise real CSVW runners: warnings convert; unsupported is never a pass."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "formal/lean4/.lake/build/bin"


class CsvwDiagnosticsTest(unittest.TestCase):
    def test_both_output_runners(self):
        with tempfile.TemporaryDirectory(prefix="factoidal-csvw-diagnostics-") as td:
            directory = Path(td)
            (directory / "data.csv").write_text("v\na\n")
            (directory / "empty.csv").write_text("v\n")
            (directory / "value.ttl").write_text(
                '_:row <http://www.w3.org/2013/csvw/tests/data.csv#v> "a" .\n'
            )
            (directory / "value.json").write_text('[{"v":"a"}]')
            (directory / "empty.ttl").write_text("")
            (directory / "empty.json").write_text("[]")
            entries = []
            for name, pattern, empty in [
                ("warning", "+", False),
                ("unsupported", "(?=a)a", False),
                ("nonmatch", "^b$", False),
                ("empty-warning", "[", True),
            ]:
                metadata = {
                    "@context": "http://www.w3.org/ns/csvw",
                    "url": "empty.csv" if empty else "data.csv",
                    "tableSchema": {"columns": [{
                        "name": "v", "datatype": {"base": "string", "format": pattern}
                    }]},
                }
                (directory / f"{name}-metadata.json").write_text(json.dumps(metadata))
                entries.append({"id": name, "action": f"{name}-metadata.json",
                                "option": {"minimal": True},
                                "result": "empty" if empty else "value"})
            for mode, extension in [("rdf", "ttl"), ("json", "json")]:
                with self.subTest(mode=mode):
                    manifest = {"entries": [dict(e, result=f"{e['result']}.{extension}")
                                            for e in entries]}
                    (directory / f"manifest-{mode}.jsonld").write_text(json.dumps(manifest))
                    result = subprocess.run([str(BIN / f"l4csvw-{mode}"), td],
                                            cwd=ROOT, text=True, capture_output=True, timeout=30)
                    output = result.stdout + result.stderr
                    self.assertEqual(result.returncode, 0, output)
                    self.assertIn("UNSUPPORTED unsupported:", output)
                    self.assertIn("WARNING warning ", output)
                    self.assertIn("WARNING empty-warning ", output)
                    self.assertIn("3 pass, 0 fail", output)
                    self.assertIn("1 unsupported (out of 4", output)
                    self.assertNotIn("4 pass", output)


if __name__ == "__main__":
    unittest.main()
