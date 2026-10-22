"""Native RIF/SPARQL boundary regressions, using only temporary fixtures.

Requires `cd formal/lean4 && lake build`. These exercise failure reporting and
import resolution, not complete RIF conformance. No network access is needed.
"""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "formal/lean4/.lake/build/bin"
RIF = "http://www.w3.org/2007/rif#"
XSD = "http://www.w3.org/2001/XMLSchema#"
MANIFEST = '''@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .
@prefix qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#> .
@prefix sd: <http://www.w3.org/ns/sparql-service-description#> .
<> a mf:Manifest; mf:entries (<urn:test>) .
<urn:test> a mf:QueryEvaluationTest;
 mf:name "RIF Core WG tests: Frames";
 mf:action [qt:query <query.rq>; qt:data <data.ttl>;
   sd:entailmentRegime (<http://www.w3.org/ns/entailment/RIF>)];
 mf:result <result.srj> .
'''


def frame(n):
    return (f'<Frame><object><Const type="{RIF}iri">urn:s</Const></object>'
            f'<slot ordered="yes"><Const type="{RIF}iri">urn:p</Const>'
            f'<Const type="{XSD}integer">{n}</Const></slot></Frame>')


def sentence(body):
    return f"<sentence>{body}</sentence>"


def document(body="", imported=False):
    directive = ("<directive><Import><location>https://example.test/base/data</location>"
                 "</Import></directive>") if imported else ""
    return f'<Document xmlns="{RIF}">{directive}<payload><Group>{body}</Group></payload></Document>'


class BoundaryTests(unittest.TestCase):
    def run_binary(self, binary, args, cwd):
        path = BIN / binary
        self.assertTrue(path.is_file(), f"Build native harness first: {path}")
        result = subprocess.run([str(path), *map(str, args)], cwd=cwd,
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_native_declared_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fact = '<urn:s>[<urn:p> -> <urn:o>]'
            cases = [
                ("PositiveEntailmentTest", "fact", f"Document(Group({fact}))", fact, {}),
                ("NegativeEntailmentTest", "missing", "Document(Import(<https://example.test/data>))", fact, {}),
                ("NegativeEntailmentTest", "malformed", "Document(Import(<https://example.test/data>))", fact,
                 {"data.ttl": "@prefix"}),
                ("PositiveEntailmentTest", "relative", "Document(Import(<https://example.test/base/data>))",
                 '<https://example.test/base/s>[<https://example.test/base/p> -> <https://example.test/base/o>]',
                 {"data.ttl": "<s> <p> <o> ."}),
                ("PositiveEntailmentTest", "stray", f"Document(Group({fact}))", fact,
                 {"undeclared.ttl": "@prefix"}),
                ("PositiveEntailmentTest", "turtle_prefixes", "Document(Import(<https://example.test/base/data>))",
                 "ex:s[ex:p -> ex:o]",
                 {"data.ttl": "PREFIX ex: <urn:shadowed:>\nPREFIX ex:\n <terms/>\nex:s ex:p ex:o ."}),
                ("PositiveEntailmentTest", "xml_prefixes", "Document(Import(<https://example.test/base/data.rdf>))",
                 "ex:s[ex:p -> ex:o]",
                 {"data.rdf": '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" '
                  'xmlns:ex="https://example.test/base/">'
                  '<rdf:Description rdf:about="s"><ex:p rdf:resource="o"/></rdf:Description></rdf:RDF>'}),
            ]
            for kind, name, premise, conclusion, imports in cases:
                directory = root / kind / name
                directory.mkdir(parents=True)
                (directory / f"{name}-premise.rifps").write_text(premise)
                (directory / f"{name}-conclusion.rifps").write_text(conclusion)
                for filename, contents in imports.items():
                    (directory / filename).write_text(contents)
            output = self.run_binary("l4rif", [root, "--verbose"], root)
            self.assertIn("5 pass, 0 fail", output)
            self.assertIn("NOT READ: 2 cases", output)
            self.assertIn("RIF import missing:", output)
            self.assertIn("RIF import parse error:", output)
            self.assertIn("UNDECIDED: 0 cases", output)

    def sparql_case(self, xml, imported=None, diagnostic=None):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            premise = root / "third_party/testing/rif/tc/Frames"
            premise.mkdir(parents=True)
            (premise / "Frames-premise.rif").write_text(xml)
            if imported is not None:
                (premise / "data.ttl").write_text(imported)
            (root / "manifest.ttl").write_text(MANIFEST)
            (root / "data.ttl").write_text("")
            (root / "query.rq").write_text("ASK { <urn:absent> <urn:p> <urn:o> }")
            (root / "result.srj").write_text('{"head":{},"boolean":false}')
            output = self.run_binary("l4w3c", [root / "manifest.ttl"], root)
            if diagnostic is None:
                self.assertIn("1 pass, 0 fail, 0 skip, 0 unsupported", output)
            else:
                self.assertIn("0 pass, 0 fail, 0 skip, 1 unsupported", output)
                self.assertIn(diagnostic, output)

    def test_sparql_complete_empty_graph(self):
        self.sparql_case(document())

    def test_sparql_empty_import(self):
        self.sparql_case(document(imported=True), imported="")

    def test_sparql_missing_import(self):
        self.sparql_case(document(imported=True), diagnostic="RIF import missing:")

    def test_sparql_malformed_import(self):
        self.sparql_case(document(imported=True), imported="@prefix", diagnostic="RIF import parse error:")

    def test_sparql_blocked_rule(self):
        external = (f'<External><content><Atom><op><Const type="{RIF}iri">'
                    'urn:unsupported-predicate</Const></op><args ordered="yes"/>'
                    '</Atom></content></External>')
        rule = sentence(f"<Implies><if>{external}</if><then>{frame(1)}</then></Implies>")
        self.sparql_case(document(rule), diagnostic="RIF evaluation blocked")

    def test_sparql_round_limit(self):
        rules = sentence(frame(0)) + "".join(
            sentence(f"<Implies><if>{frame(n)}</if><then>{frame(n + 1)}</then></Implies>")
            for n in range(101))
        self.sparql_case(document(rules), diagnostic="RIF saturation round limit reached")

    def test_sparql_unrepresentable_output(self):
        invalid_frame = frame(0).replace(f'type="{RIF}iri">urn:s', f'type="{XSD}string">literal-subject')
        self.sparql_case(document(sentence(invalid_frame)), diagnostic="derived RIF fact cannot be represented as RDF")


if __name__ == "__main__":
    unittest.main()
