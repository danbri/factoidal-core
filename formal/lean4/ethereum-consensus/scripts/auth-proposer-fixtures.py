"""Test-only reuse of the independent proposer SSZ fixture generator."""
import json
import random
import runpy
from pathlib import Path

oracle = runpy.run_path(str(Path(__file__).with_name("check-proposer-slashing.py")))
key = bytes.fromhex("97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb")

class FixtureRandom(random.Random):
    def randbytes(self, n):
        raw = super().randbytes(n)
        return key if n == 48 else raw

cases = []
for serial in (3, 6):
    rows = list(oracle["make_case"](FixtureRandom(1019 + serial), serial))
    line, expected = rows[0]
    label, pk, a, b = expected.split()
    assert label == "candidate_not_authenticated" and pk == key.hex() and a != b
    cases.append({"line": line, "evidence": [pk, a, b], "rejections": rows[1:]})
print(json.dumps(cases))
