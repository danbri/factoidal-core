#!/usr/bin/env python3
"""Adversarial controls for active evidence: reject source and case drift."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("active_assurance",
    ROOT / "scripts/check-active-ledger.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)
MANIFEST = json.loads((ROOT / "evidence/active-claim-manifest-v2.json").read_text())

class ActiveLedgerControls(unittest.TestCase):
    def test_selected_inventory_and_theorems(self):
        inventory = check.check_inventory(MANIFEST)
        check.check_theorems(MANIFEST, inventory)

    def test_tampered_blobs_rejected(self):
        for mutation in [
            lambda x: x["source_blobs"].update({"EVMCleanroom/Core.lean":"0"*40}),
            lambda x: x["source_blobs"].update({"EVMCleanroom/CallGas.lean":"0"*40}),
            lambda x: x["source_blobs"].update({"EVMCleanroom/Frame.lean":"0"*40}),
            lambda x: x["source_blobs"].update({"EVMCleanroom/CLI.lean":"0"*40}),
            lambda x: x["source_blobs"].update({"EVMCleanroom/World.lean":"0"*40}),
        ]:
            m=copy.deepcopy(MANIFEST)
            mutation(m)
            with self.assertRaises(ValueError):
                check.check_inventory(m)

    def test_missing_theorem_claim_rejected(self):
        m=copy.deepcopy(MANIFEST)
        m["theorem_inventory"][0]["name"]="EVMCleanroom.nonexistent_fabricated_proof"
        with self.assertRaises(ValueError):
            check.check_theorems(m, check.check_inventory(m))

    def test_qualified_theorem_symbol_mismatch_rejected(self):
        m=copy.deepcopy(MANIFEST)
        m["theorem_inventory"][0]["source_symbol"]="Word.signedLt_correct"
        with self.assertRaises(ValueError):
            check.check_theorems(m, check.check_inventory(m))

    def test_falsified_contract_root_and_counts_rejected(self):
        path=ROOT/".lake/eels/lean-contract-results.json"
        if not path.exists():
            self.skipTest("EELS result produced by dedicated replay job")
        baseline=json.loads(path.read_text())
        check.check_contract_report(MANIFEST, baseline)
        mutations=[
            lambda x: x["cases"][0].update(computedStateRoot="0x"+"00"*32),
            lambda x: x["cases"].pop(),
            lambda x: x["totals"].update(passed=5),
            lambda x: x["totals"].update(unsupported=1),
            lambda x: x["provenance"].update(fixtureSha256="0"*64),
            lambda x: next(c for c in x["cases"] if
                "stack_overflow" in c["id"]).update(slot0="1"),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                m=copy.deepcopy(baseline)
                mutation(m)
                with self.assertRaises(ValueError):
                    check.check_contract_report(MANIFEST,m)

if __name__ == "__main__":
    unittest.main()
