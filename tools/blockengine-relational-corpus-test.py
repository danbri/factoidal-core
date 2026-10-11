#!/usr/bin/env python3
"""Hand-checked small cases for the varied corpus and its independent oracle."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location("corpus", Path(__file__).with_name(
    "blockengine-relational-corpus.py"))
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)


def rows(workloads, name):
    return next(w['expected']['results']['bindings'] for w in workloads if w['name'] == name)


class Corpus(unittest.TestCase):
    def test_small_graph_cardinality_and_cycle(self):
        data = C.fixture_bytes(10).decode()
        self.assertEqual(C.triple_count(10), 63)
        self.assertEqual(len(data.splitlines()), 63)
        self.assertIn('<urn:rel:person:00000009> <urn:rel:next> <urn:rel:person:00000000> .', data)
        self.assertIn('<urn:rel:person:00000007> <urn:rel:alias> "alias Ω-00000007" .', data)

    def test_paths_wrap_at_the_end(self):
        workloads = C.workloads(10)
        two, three = rows(workloads, 'chain-two'), rows(workloads, 'chain-three')
        self.assertEqual(len(two), 10)
        self.assertEqual(two[0]['name']['value'], 'person-00000001')
        self.assertEqual(two[-1]['name']['value'], 'person-00000000')
        self.assertEqual(three[-2]['name']['value'], 'person-00000000')
        self.assertEqual(three[-1]['name']['value'], 'person-00000001')

    def test_optional_keeps_unbound_rows(self):
        answer = rows(C.workloads(10), 'optional-alias')
        self.assertEqual(len(answer), 10)
        self.assertEqual(answer[0]['alias']['value'], 'alias Ω-00000000')
        self.assertNotIn('alias', answer[1])
        self.assertEqual(answer[7]['alias']['value'], 'alias Ω-00000007')

    def test_groups_and_distinct_have_complete_small_answers(self):
        workloads = C.workloads(10)
        self.assertEqual(len(rows(workloads, 'union-distinct')), 10)
        grouped = rows(workloads, 'group-count-string')
        self.assertEqual(len(grouped), 10)
        self.assertEqual(grouped[0], {'org': {'type': 'uri', 'value': 'urn:rel:org:000'},
                                     'count': {'type': 'literal', 'value': '1'}})

    def test_selectivity_and_numeric_order(self):
        workloads = C.workloads(1000)
        selected = rows(workloads, 'selective-chain')
        self.assertEqual([r['subject']['value'] for r in selected],
                         [f'urn:rel:person:{n:08d}' for n in range(0, 1000, 100)])
        ranked = rows(workloads, 'numeric-top')
        self.assertEqual([r['subject']['value'] for r in ranked],
                         [f'urn:rel:person:{n:08d}' for n in range(999, 974, -1)])
        self.assertEqual(len(rows(workloads, 'values-chain')), 50)


if __name__ == '__main__':
    unittest.main()
