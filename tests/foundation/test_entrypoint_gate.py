"""Tests for tools/entrypoint-gate.py (https://github.com/danbri/factoidal/issues/975, item 3).

Each test builds a small fixture tree in a temporary directory (npm package,
wasm dispatch tables, CLI command table, dataflow inventory, mapping file,
unbound list) and runs the gate on it with `--root <tmp>`. Run:

    python3 -I tests/foundation/test_entrypoint_gate.py
"""
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
GATE = os.path.join(HERE, "..", "..", "tools", "entrypoint-gate.py")

PACKAGE = """{
  "name": "fixture",
  "exports": {
    ".": { "types": "./index.d.ts", "browser": "./browser.js", "import": "./index.mjs",
           "require": "./index.js" },
    "./fn": { "default": "./fn.js" },
    "./package.json": "./package.json"
  },
  "bin": { "fixture": "./bin/cli.mjs" }
}
"""

INDEX_MJS = """// export const commented = 1;
export const parse = api.parse;
export async function query(a, b) { return 1; }
export class FixtureError extends Error {}
export const LIMIT = 65536;
export { helper as renamed } from './lib/x.mjs';
export default api;
"""

INDEX_JS = "module.exports = require('./index.mjs');\n"
BROWSER_JS = "export const parse = api.parse;\nexport function setAssetsUrl(u) {}\n"
FN_JS = "module.exports = {\n  canonicalize,\n  hash: x.hash,\n};\n"

CLI = """const COMMANDS = {
  version: (p, o) => commandVersion(o),
  'sample-store': commandSample,
  query: commandQuery
}
"""

DISPATCH = """def opNames : List String :=
  [ "parseToDatasetJson"
  , "shaclValidate" ]

def callIO (op : String) : String :=
  match op with
  | "ops" => reflection
  | _ => ""
"""

INVENTORY = """# Dataflow inventory

| area | dir | stage | in | out | contract | status | theorems | IO assumptions | tests | note |
|---|---|---|---|---|---|---|---|---|---|---|
| Parse | RDF | `parseStage` | a | b | `C` | proved | - | - | - | - |
| SHACL | SHACL | `shaclStage` | a | b | `C` | proved | - | - | - | - |
| SPARQL query evaluation (reference evaluator) | SPARQL | - | a | b | - | tested | - | - | suite | - |
| XML parser | XML | - | a | b | - | missing | - | - | - | - |
"""

ENTRYPOINTS = """[manifest]
version = 0

[[entry]]
id = "wasm:parseToDatasetJson"
stages = ["parseStage"]
covers = "part"
note = "fixture"

[[entry]]
id = "wasm:shaclValidate"
stages = ["shaclStage"]
covers = "whole"

[[entry]]
id = "npm:.#query"
stages = ["SPARQL query evaluation (reference evaluator)"]
covers = "whole"

[[nonstage]]
id = "wasm:ops"
reason = "reflection of the op table"

[[nonstage]]
id = "cli:version"
reason = "prints the package version"
"""

UNBOUND = [
    "npm:.#parse",
    "npm:.#renamed",
    "npm:.#default",
    "npm:.#setAssetsUrl",
    "npm:./fn#canonicalize",
    "npm:./fn#hash",
    "npm:./package.json",
    "cli:sample-store",
    "cli:query",
]


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


class EntrypointGateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        r = self.root = self.tmp.name
        npm = os.path.join(r, "npm", "factoidal")
        write(os.path.join(npm, "package.json"), PACKAGE)
        write(os.path.join(npm, "index.mjs"), INDEX_MJS)
        write(os.path.join(npm, "index.js"), INDEX_JS)
        write(os.path.join(npm, "browser.js"), BROWSER_JS)
        write(os.path.join(npm, "fn.js"), FN_JS)
        write(os.path.join(npm, "bin", "factoidal.mjs"), CLI)
        write(os.path.join(r, "formal", "lean4", "Wasm", "Dispatch.lean"), DISPATCH)
        write(os.path.join(r, "docs", "dataflow-inventory.md"), INVENTORY)
        write(os.path.join(r, "foundation", "entrypoints.toml"), ENTRYPOINTS)
        self.set_unbound(UNBOUND)

    def tearDown(self):
        self.tmp.cleanup()

    def set_unbound(self, ids, max_entries=None):
        if max_entries is None:
            max_entries = len(ids)
        body = "# max-entries: %d\n" % max_entries + "".join(i + "\n" for i in ids)
        write(os.path.join(self.root, "foundation", "unbound-entrypoints.txt"), body)

    def set_mapping(self, text):
        write(os.path.join(self.root, "foundation", "entrypoints.toml"), text)

    def run_gate(self):
        p = subprocess.run([sys.executable, "-I", GATE, "--root", self.root],
                           capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr

    def test_clean_tree_passes(self):
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)
        # 9 npm (2 auto nonstage: FixtureError, LIMIT), 3 wasm, 3 cli.
        self.assertIn("npm 10", out)
        self.assertIn("wasm 3", out)
        self.assertIn("cli 3", out)
        self.assertIn("3 bound (proved 2, tested 1, assumed 0; 1 part)", out)

    def test_unmapped_entry_fails(self):
        self.set_unbound([u for u in UNBOUND if u != "cli:query"], max_entries=len(UNBOUND))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("cli:query: no stage mapping and not in foundation/unbound-entrypoints.txt", out)

    def test_unknown_stage_fails(self):
        self.set_mapping(ENTRYPOINTS.replace('"shaclStage"', '"noSuchStage"'))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("wasm:shaclValidate: stage noSuchStage is not in the registry", out)

    def test_missing_status_stage_fails(self):
        self.set_mapping(ENTRYPOINTS.replace('"shaclStage"', '"XML parser"'))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("status missing", out)

    def test_mapping_names_nonexistent_entry_fails(self):
        self.set_mapping(ENTRYPOINTS.replace('"wasm:shaclValidate"', '"wasm:gone"'))
        self.set_unbound(UNBOUND + ["wasm:shaclValidate"])
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("wasm:gone: mapped, but no such entry point", out)

    def test_unbound_growth_fails(self):
        self.set_mapping(ENTRYPOINTS.replace('id = "wasm:shaclValidate"', 'id = "wasm:xx"'))
        self.set_unbound(UNBOUND + ["wasm:shaclValidate"], max_entries=len(UNBOUND))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("unbound list has 10 entries, max-entries is 9", out)

    def test_stale_unbound_entry_fails(self):
        self.set_unbound(UNBOUND + ["npm:.#gone"])
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("npm:.#gone: listed as unbound, but no such entry point", out)

    def test_unbound_entry_now_mapped_fails(self):
        self.set_unbound(UNBOUND + ["wasm:shaclValidate"])
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("wasm:shaclValidate: listed as unbound, but it is mapped", out)

    def test_new_wasm_op_fails(self):
        write(os.path.join(self.root, "formal", "lean4", "Wasm", "Dispatch.lean"),
              DISPATCH.replace('"shaclValidate" ]', '"shaclValidate", "newOp" ]'))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("wasm:newOp: no stage mapping", out)

    def test_empty_cli_enumeration_fails(self):
        write(os.path.join(self.root, "npm", "factoidal", "bin", "factoidal.mjs"), "// none\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("cli: no entry points found", out)

    def test_empty_wasm_enumeration_fails(self):
        write(os.path.join(self.root, "formal", "lean4", "Wasm", "Dispatch.lean"), "-- none\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("wasm: no entry points found", out)

    def test_nonstage_without_reason_fails(self):
        self.set_mapping(ENTRYPOINTS.replace('reason = "prints the package version"', 'reason = ""'))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("cli:version: nonstage entry has no reason", out)


if __name__ == "__main__":
    unittest.main()
