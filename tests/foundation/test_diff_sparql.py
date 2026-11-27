"""Tests for the comparer of tools/diffcampaign/sparql.py (https://github.com/danbri/factoidal-core/issues/1184).
Run: python3 -I tests/foundation/test_diff_sparql.py"""
import importlib.util
import json
import os
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("ds", os.path.join(HERE, "..", "..", "tools", "diffcampaign", "sparql.py"))
ds = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ds)
X = "http://www.w3.org/2001/XMLSchema#"


def answer(*vals):
    return json.dumps({"head": {"vars": ["a"]}, "results": {"bindings": [{"a": v} for v in vals]}})


S = {"type": "literal", "value": "w0"}
L = {"type": "literal", "value": "w1", "xml:lang": "fr"}
I1 = {"type": "literal", "value": "1", "datatype": X + "integer"}
I2 = {"type": "literal", "value": "2", "datatype": X + "integer"}
U = {"type": "uri", "value": "http://e/x"}


class CompareTest(unittest.TestCase):
    def test_undefined_order_both_allowed(self):
        a, b = ds.norm(answer(S, L), True), ds.norm(answer(L, S), True)
        self.assertEqual(a[0], b[0])
        self.assertTrue(a[1] and b[1])

    def test_defined_order_enforced(self):
        self.assertTrue(ds.norm(answer(I1, I2), True)[1])
        self.assertFalse(ds.norm(answer(I2, I1), True)[1])
        self.assertFalse(ds.norm(answer(I1, U), True)[1])  # IRIs before literals

    def test_multiset(self):
        self.assertEqual(ds.norm(answer(I1, I2), False)[0], ds.norm(answer(I2, I1), False)[0])
        self.assertNotEqual(ds.norm(answer(I1, I1), False)[0], ds.norm(answer(I1), False)[0])


if __name__ == "__main__":
    unittest.main()
