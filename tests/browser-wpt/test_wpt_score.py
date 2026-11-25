import json
from pathlib import Path
import runpy
import tempfile
import unittest


done_in = runpy.run_path(str(Path(__file__).with_name("wpt-score.py")))["done_in"]


class ResultProgressTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.results = Path(directory.name) / "part0.jsonl"

    def test_split_write_is_counted_after_the_newline(self):
        with self.results.open("wb") as writer:
            writer.write(b'{"file":"first.html"}\n{"file":"caf\xc3')
            writer.flush()
            self.assertEqual(done_in(self.results), {"first.html"})

            writer.write(b'\xa9.html"}')
            writer.flush()
            self.assertEqual(done_in(self.results), {"first.html"})

            writer.write(b"\n")
            writer.flush()
            self.assertEqual(done_in(self.results), {"first.html", "caf\N{LATIN SMALL LETTER E WITH ACUTE}.html"})

    def test_complete_corrupt_line_is_reported(self):
        self.results.write_bytes(b'{"file":"first.html"}\n{"file":"broken\n')
        with self.assertRaises(json.JSONDecodeError):
            done_in(self.results)

    def test_missing_worker_file_is_empty(self):
        self.assertEqual(done_in(self.results), set())


if __name__ == "__main__":
    unittest.main()
