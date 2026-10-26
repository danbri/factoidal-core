"""Tests for tools/runners-gate.py (https://github.com/danbri/factoidal/issues/1002).

Each test builds a small fixture tree (nodes.mjs, inventory, mapping) in a
temporary directory and runs the gate with `--root <tmp>`. Run:

    python3 -I tests/foundation/test_runners_gate.py
"""
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
GATE = os.path.join(HERE, "..", "..", "tools", "runners-gate.py")

NODES = """export function buildNodes(deps) {
  const { entry, parse, closure, query } = deps;
  const reader = (format) => async (wire, params) => {
    const ds = await parse(wire.graph, { format, ...params });
    return { graph: ds };
  };
  const RUNNERS = {
    turtleDocumentReader: reader('turtle'),
    rdfsReasoner: async (wire) => ({ graph: await closure(wire.graph, 'rdfs') }),
    shippedEvaluator: async (wire, p) => ({ artefact: await query(wire.graph, p.query) }),
  };
}
"""

ROW = "| {a} | x | {s} | x | x | x | tested | x | x | x | x |\n"
INVENTORY = "| area | kind | stage | c | c | c | status | c | c | c | c |\n|---|---|---|---|---|---|---|---|---|---|---|\n" + \
    "".join(ROW.format(a="a" + s, s=s) for s in ("turtleDocumentReader", "rdfsReasoner", "shippedEvaluator", "otherStage"))

MAPPING = """[manifest]
version = 0
[[entry]]
id = "npm:.#parse"
stages = ["turtleDocumentReader"]
covers = "part"
note = "n"
[[entry]]
id = "npm:.#closure"
stages = ["rdfsReasoner"]
covers = "part"
note = "n"
[[entry]]
id = "npm:.#query"
stages = ["shippedEvaluator"]
covers = "part"
note = "n"
"""


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


class RunnersGateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = self.tmp.name
        self.put(nodes=NODES, inventory=INVENTORY, mapping=MAPPING)

    def tearDown(self):
        self.tmp.cleanup()

    def put(self, nodes=None, inventory=None, mapping=None):
        r = self.root
        if nodes is not None:
            write(os.path.join(r, "npm", "factoidal", "lib", "nodes.mjs"), nodes)
        if inventory is not None:
            write(os.path.join(r, "docs", "dataflow-inventory.md"), inventory)
        if mapping is not None:
            write(os.path.join(r, "foundation", "entrypoints.toml"), mapping)

    def run_gate(self):
        p = subprocess.run([sys.executable, "-I", GATE, "--root", self.root],
                           capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr

    def test_clean_tree_passes(self):
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("3 RUNNERS keys", out)

    def test_key_not_in_registry_fails(self):
        self.put(nodes=NODES.replace("rdfsReasoner:", "noSuchStage:"))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("RUNNERS.noSuchStage: not a stage", out)

    def test_op_maps_to_different_stage_fails(self):
        # shippedEvaluator runs `closure`, which is mapped to rdfsReasoner only.
        self.put(nodes=NODES.replace("await query(", "await closure("))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("RUNNERS.shippedEvaluator: calls npm:.#closure", out)

    def test_helper_call_is_resolved(self):
        # reader() calls parse; remap turtleDocumentReader to a mapping without it.
        self.put(mapping=MAPPING.replace('stages = ["turtleDocumentReader"]', 'stages = ["otherStage"]'))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("RUNNERS.turtleDocumentReader: calls npm:.#parse", out)

    def test_unmapped_function_fails(self):
        self.put(mapping=MAPPING.replace('id = "npm:.#query"', 'id = "npm:.#other"'))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("npm:.#query, which has no [[entry]]", out)

    def test_entry_calling_nothing_fails(self):
        self.put(nodes=NODES.replace("await closure(wire.graph, 'rdfs')", "wire.graph"))
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("RUNNERS.rdfsReasoner: calls no package function", out)

    def test_empty_runners_fails(self):
        self.put(nodes="const { parse } = deps;\nconst RUNNERS = {\n};\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("RUNNERS is empty", out)

    def test_empty_inventory_fails(self):
        self.put(inventory="")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("no registry stages found", out)


if __name__ == "__main__":
    unittest.main()
