"""Scanner regressions: false source text must not become reuse evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "audit", Path(__file__).with_name("lean-reuse-audit.py"))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuditTests(unittest.TestCase):
    def test_mask_nested_comments_literals_and_keep_lines(self):
        source = '''/- outer /- nested -/
def hexFake := 1
-/
def text := "escaped \\" quote\nimport L4Factoidal.XSD.Lexical"
def quote := '"'
-- def hexComment := 2
private def hexVal? := 3
def name' := 4
'''
        masked = audit.code_only(source)
        self.assertEqual(len(masked), len(source))
        self.assertEqual(masked.count("\n"), source.count("\n"))
        self.assertEqual([m.group(1) for m in audit.DECL.finditer(masked)],
                         ["text", "quote", "hexVal?", "name'"])
        self.assertEqual(list(audit.IMPORT.finditer(masked)), [])

    def test_cross_family_candidates_and_actual_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            base = root / "formal/lean4/L4Factoidal"
            fixtures = {
                "A/Main.lean": "import L4Factoidal.Encoding.Hex\ndef hexVal := 1\n",
                "A/Other.lean": "def sameFamily := 1\ndef onlyHere := 0\n",
                "A/More.lean": "def sameFamily := 2\n",
                "B/Main.lean": "-- import L4Factoidal.Regex.Profiles\ndef hexVal? := 2\n",
                "B/Tests.lean": "def onlyHere := 5\n",
            }
            for name, source in fixtures.items():
                path = base / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            result = audit.audit(root, all_names=True)
            self.assertEqual(result['source_modules'], 4)
            self.assertEqual([c['name'] for c in result['candidates']], ['hexVal'])
            self.assertEqual(result['candidates'][0]['declarations'][0]['line'], 2)
            self.assertEqual(len(result['shared_direct_imports']['Encoding.Hex']), 1)
            self.assertEqual(result['shared_direct_imports']['Regex.Profiles'], [])

    def test_missing_tree_is_not_an_empty_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):
                audit.audit(Path(tmp))

    def test_harness_is_an_explicit_audit_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixtures = {
                "L4Factoidal/Fn/Main.lean": "def numericLiteralEqual := true\n",
                "Harness/Compare.lean": "import Harness.RifImport\ndef numericLiteralEqual := false\n",
                "Harness/HarnessTests.lean": "def numericLiteralEqual := true\n",
            }
            for name, source in fixtures.items():
                path = root / "formal/lean4" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            ordinary = audit.audit(root, all_names=True)
            expanded = audit.audit(root, all_names=True, include_harness=True)
            self.assertFalse(ordinary['includes_harness'])
            self.assertEqual(ordinary['source_modules'], 1)
            self.assertEqual(ordinary['candidates'], [])
            self.assertTrue(expanded['includes_harness'])
            self.assertEqual(expanded['source_modules'], 2)
            self.assertEqual(len(expanded['shared_direct_imports']['Harness.RifImport']), 1)
            self.assertEqual(expanded['candidates'][0]['families'], ['Fn', 'Harness'])
            self.assertEqual([m['family'] for m in expanded['semantic_mentions']['numericLiteralEqual']],
                             ['Fn', 'Harness'])

    def test_semantic_mentions_keep_spelling_and_ignore_prose(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "formal/lean4/L4Factoidal/A/Main.lean"
            source.parent.mkdir(parents=True)
            source.write_text('''-- Term.eqb is deliberately not evidence here.
def prose := "literalPromote x; x.sameTerm y"
def identity x y := x.sameTerm y
def legacy x y := Term.eqb x y || x.eqb y
def projected x := x.toTerm?
def unrelated := sameTermExtra
''')
            mentions = audit.audit(root)['semantic_mentions']
            self.assertEqual([m['line'] for m in mentions['sameTerm']], [3])
            self.assertEqual([m['spelling'] for m in mentions['eqb']],
                             ['Term.eqb', 'x.eqb'])
            self.assertEqual(mentions['literalPromote'], [])
            self.assertEqual(mentions['toTerm?'][0]['line'], 5)


if __name__ == "__main__":
    unittest.main()
