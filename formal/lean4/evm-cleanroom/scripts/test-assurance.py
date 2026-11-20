#!/usr/bin/env python3
"""Adversarial controls for the evidence consistency check."""
import copy
import importlib.util
import json
import pathlib
import unittest

root = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_assurance', root/'scripts/check-assurance.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)
manifest = json.loads((root/'evidence/claim-manifest-v1.json').read_text())
replay = manifest['replay']
baseline = json.loads((root/replay['result_snapshot']).read_text())

class EvidenceControls(unittest.TestCase):
    def test_reference(self):
        check.check_result(baseline, replay)

    def test_mutations_are_rejected(self):
        mutations = [
            lambda x: x.update(passed=3),
            lambda x: x['cases'].pop(),
            lambda x: x['cases'][2].update(computedStateRoot='0x'+'00'*32),
            lambda x: x['cases'][0].update(status='pass'),
            lambda x: x['provenance'].update(sha256='0'*64),
            lambda x: x['cases'][0].update(reason='other'),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                result = copy.deepcopy(baseline)
                mutate(result)
                with self.assertRaises(ValueError):
                    check.check_result(result, replay)

if __name__ == '__main__':
    unittest.main()
