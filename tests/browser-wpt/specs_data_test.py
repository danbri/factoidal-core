"""specs-data.py writes exactly tests/hub/specs-fixtures/sample from runs-sample.csv (so the sample
the page tests use is what the generator writes), and its statuses follow the rules in its header."""
import json, os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
FIX = os.path.join(HERE, "..", "hub", "specs-fixtures")


def generate(out):
    subprocess.run([sys.executable, os.path.join(HERE, "specs-data.py"), "--runs", os.path.join(FIX, "runs-sample.csv"),
                    "--meta-dir", os.path.join(FIX, "meta"), "--only-recorded", "--now", "2026-11-16T06:00:00Z", "--out", out],
                   check=True, capture_output=True)


class SpecsData(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        generate(cls.tmp.name)
        with open(os.path.join(cls.tmp.name, "data.json")) as f:
            cls.D = json.load(f)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_sample_is_current(self):
        for name in ("data.json", "history.json", "records.csv"):
            with open(os.path.join(self.tmp.name, name)) as a, open(os.path.join(FIX, "sample", name)) as b:
                self.assertEqual(a.read(), b.read(), f"{name}: regenerate the sample (tests/hub/specs-fixtures/README.md)")

    def suite(self, sid):
        return next(s for s in self.D["suites"] if s["suite"] == sid)

    def test_statuses(self):
        self.assertEqual(self.suite("l4-xslt")["status"], "partial")
        self.assertIn("1 of 88 not decided", self.suite("l4-xslt")["reason"])
        rif = self.suite("l4-rif_core")
        self.assertEqual((rif["status"], rif["lastValid"]["passed"], rif["lastValid"]["total"]), ("invalid", 42, 43))
        self.assertTrue(self.suite("l4-mathml")["stale"])
        self.assertFalse(self.suite("l4-xslt")["stale"])
        self.assertIn("superseded by l4-xslt", self.suite("xslt")["staleReason"])
        self.assertIn("covered by l4-shacl12_rules", self.suite("shacl12_rules_syntax")["staleReason"])
        self.assertEqual(self.D["unmapped"], ["l4-geosparql"])

    def test_headlines_count_only_current_headline_suites(self):
        fam = {f["id"]: f["headline"] for f in self.D["families"]}
        self.assertEqual((fam["sparql"]["passed"], fam["sparql"]["total"]), (650, 650))
        self.assertIsNone(fam["owl"]["total"])
        self.assertEqual(fam["rif"]["invalid"], 1)
        self.assertEqual(fam["rif"]["total"], 0, "an invalid run is not counted in the headline")
        self.assertEqual(fam["mathml"]["suites"], 0, "a stale suite is not in the headline")


if __name__ == "__main__":
    unittest.main()
