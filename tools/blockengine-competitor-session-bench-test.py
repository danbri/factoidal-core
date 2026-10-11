#!/usr/bin/env python3
"""Negative guards for competitor-answer exclusions and extension handling."""
import copy
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location("bench", Path(__file__).with_name(
    "blockengine-competitor-session-bench.py"))
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


class Exactness(unittest.TestCase):
    def setUp(self):
        self.expected = next(w["expected"] for w in M.D.workloads(10) if w["name"] == "predicate-count")

    def test_count_exclusion_checks_full_document(self):
        alternate = copy.deepcopy(self.expected)
        alternate["results"]["bindings"][0]["count"]["datatype"] = "http://www.w3.org/2001/XMLSchema#int"
        self.assertIsNotNone(M.known_difference("qlever", "predicate-count", alternate, self.expected))
        for mutation in ("value", "extra-row", "extra-variable"):
            broken = copy.deepcopy(alternate)
            if mutation == "value":
                broken["results"]["bindings"][0]["count"]["value"] = "wrong"
            elif mutation == "extra-row":
                broken["results"]["bindings"].append({})
            else:
                broken["head"]["vars"].append("extra")
            self.assertIsNone(M.known_difference("qlever", "predicate-count", broken, self.expected))

    def test_ask_exclusion_checks_value_and_datatype(self):
        expected = {"head": {}, "boolean": True}
        alternate = {"head": {"vars": ["__ASK_RETVAL"]}, "results": {"bindings": [
            {"__ASK_RETVAL": {"type": "literal", "datatype": "http://www.w3.org/2001/XMLSchema#integer", "value": "1"}}]}}
        self.assertIsNotNone(M.known_difference("virtuoso", "ask-present", alternate, expected))
        alternate["results"]["bindings"][0]["__ASK_RETVAL"]["value"] = "0"
        self.assertIsNone(M.known_difference("virtuoso", "ask-present", alternate, expected))
        alternate["results"]["bindings"][0]["__ASK_RETVAL"]["value"] = "1"
        alternate["results"]["bindings"][0]["__ASK_RETVAL"]["datatype"] = "urn:wrong"
        self.assertIsNone(M.known_difference("virtuoso", "ask-present", alternate, expected))

    def test_qlever_removes_only_meta_without_mutating_input(self):
        answer = dict(copy.deepcopy(self.expected), meta={"time": 0}, unknown=True)
        original = copy.deepcopy(answer)
        self.assertEqual(M.clean("qlever", answer), dict(self.expected, unknown=True))
        self.assertEqual(answer, original)

    def test_virtuoso_removes_only_named_extensions(self):
        answer = copy.deepcopy(self.expected)
        answer["head"]["link"] = []
        answer["results"].update(distinct=False, ordered=True, unknown=True)
        cleaned = M.clean("virtuoso", answer)
        self.assertTrue(cleaned["results"]["unknown"])
        self.assertEqual(cleaned["results"]["bindings"], self.expected["results"]["bindings"])
        self.assertNotIn("link", cleaned["head"])
        self.assertNotIn("distinct", cleaned["results"])
        self.assertNotIn("ordered", cleaned["results"])

    def test_correct_count_is_not_an_excluded_difference(self):
        self.assertIsNone(M.known_difference("qlever", "predicate-count", self.expected, self.expected))


if __name__ == "__main__":
    unittest.main()
