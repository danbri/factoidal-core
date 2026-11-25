#!/usr/bin/env python3
"""Independent EIP-1559 arithmetic oracle. Never used by the Lean runtime.

This is deliberately not an Ethereum client or imported EELS implementation.
Only the selected London header arithmetic is compared. The case fixture is
generated independently of the Lean executable with a fixed seed.
"""
import argparse
import json
import random
from pathlib import Path

MAX_GAS = 2**64
MAX_FEE = 2**256
INITIAL = 1_000_000_000


def reference(case):
    first, parent_limit, parent_used, parent_fee, child_limit, child_used, claimed = case
    if (parent_limit >= MAX_GAS or parent_used >= MAX_GAS or
        child_limit >= MAX_GAS or child_used >= MAX_GAS or
        claimed >= MAX_FEE or (parent_fee is not None and parent_fee >= MAX_FEE)):
        return {"status": "indeterminate", "reason": "resource-limit"}
    if parent_used > parent_limit:
        return {"status": "error", "reason": "parent-gas-exceeds-limit"}
    if child_used > child_limit:
        return {"status": "error", "reason": "child-gas-exceeds-limit"}
    reference_limit = parent_limit * (2 if first else 1)
    delta = reference_limit // 1024
    if (parent_limit < 5000 or child_limit < 5000 or
        child_limit >= reference_limit + delta or
        child_limit <= reference_limit - delta):
        return {"status": "error", "reason": "invalid-gas-limit"}
    if first:
        if parent_fee is not None:
            return {"status": "error", "reason": "unexpected-parent-fee"}
        expected = INITIAL
    else:
        if parent_fee is None:
            return {"status": "indeterminate", "reason": "missing-parent-fee"}
        target = parent_limit // 2
        if parent_used == target:
            expected = parent_fee
        elif parent_used > target:
            difference = parent_used - target
            expected = parent_fee + max(parent_fee * difference // target // 8, 1)
        else:
            difference = target - parent_used
            expected = parent_fee - (parent_fee * difference // target // 8)
    if claimed != expected:
        return {"status": "error", "reason": "incorrect-base-fee"}
    return {"status": "ok", "expectedBaseFee": str(expected)}


def serialise(case):
    first, parent_limit, parent_used, parent_fee, child_limit, child_used, claimed = case
    fields = ["1" if first else "0", str(parent_limit), str(parent_used),
              "-" if parent_fee is None else str(parent_fee),
              str(child_limit), str(child_used), str(claimed)]
    return "\t".join(fields)


def cases():
    rng = random.Random(1559)
    cases = []
    # EIP-1559 activation: the effective reference gas limit doubles.
    for i in range(256):
        parent_limit = rng.randrange(5_000_000, 31_000_000)
        doubled = parent_limit * 2
        change = doubled // 1024
        child_limit = doubled + rng.randrange(1 - change, change)
        parent_used = rng.randrange(parent_limit + 1)
        claimed = INITIAL if i % 7 else INITIAL + 1
        cases.append((True, parent_limit, parent_used, None, child_limit, 0, claimed))
    # Subsequent London-family blocks: three branches and two floor operations.
    for i in range(1280):
        parent_limit = rng.randrange(10_000, 40_000_000)
        limit_change = parent_limit // 1024
        child_limit = parent_limit + rng.randrange(1 - limit_change, limit_change)
        target = parent_limit // 2
        if i % 3 == 0:
            used = target
        elif i % 3 == 1:
            used = rng.randrange(target + 1, parent_limit + 1)
        else:
            used = rng.randrange(target)
        fee = rng.randrange(1, 2**64)
        base = reference((False, parent_limit, used, fee, child_limit, 0, 0))
        assert base["status"] == "error" and base["reason"] == "incorrect-base-fee"
        # Independent expected price; calculate via the same integer math above.
        if used == target:
            expected = fee
        elif used > target:
            expected = fee + max((fee * (used - target) // target) // 8, 1)
        else:
            expected = fee - (fee * (target - used) // target // 8)
        claimed = expected + 1 if i % 11 == 0 else expected
        cases.append((False, parent_limit, used, fee, child_limit,
                      rng.randrange(child_limit + 1), claimed))
    # Explicit strict endpoint, admission, absence and numeric controls.
    neutral = (False, 30_000_000, 15_000_000, INITIAL, 30_000_000, 0, INITIAL)
    cases.extend([
        neutral,
        (False, 30_000_000, 30_000_000, INITIAL, 30_000_000, 0, 1_125_000_000),
        (False, 30_000_000, 0, INITIAL, 30_000_000, 0, 875_000_000),
        (False, 30_000_000, 15_000_001, 1, 30_000_000, 0, 2),
        (False, 30_000_000, 15_000_000, None, 30_000_000, 0, 0),
        (True, 15_000_000, 14_000_000, None, 30_000_000, 0, INITIAL),
        (True, 15_000_000, 14_000_000, INITIAL, 30_000_000, 0, INITIAL),
        (False, 30_000_000, 30_000_001, INITIAL, 30_000_000, 0, INITIAL),
        (False, 30_000_000, 15_000_000, INITIAL, 30_000_000, 30_000_001, INITIAL),
        (False, 30_000_000, 15_000_000, INITIAL, 30_029_296, 0, INITIAL),
        (False, 30_000_000, 15_000_000, INITIAL, 29_970_704, 0, INITIAL),
        (False, 30_000_000, 15_000_000, INITIAL, 30_029_295, 0, INITIAL),
        (False, 30_000_000, 15_000_000, INITIAL, 29_970_705, 0, INITIAL),
        (False, 30_000_000, 15_000_000, INITIAL, 30_000_000, 0, INITIAL+1),
        (False, 30_000_000, 15_000_000, INITIAL, 30_000_000, 0, MAX_FEE),
        (False, MAX_GAS, 0, INITIAL, 30_000_000, 0, INITIAL),
        (False, 30_000_000, 15_000_000, MAX_FEE, 30_000_000, 0, INITIAL),
        (False, 4999, 0, INITIAL, 5000, 0, INITIAL),
        (True, 15_000_000, 0, None, 30_029_296, 0, INITIAL),
    ])
    assert len(cases) == 1555, len(cases)
    return cases


def mismatch(expected, observed):
    return sum(a != b for a, b in zip(expected, observed)) + abs(len(expected) - len(observed))


def generate(inputs, expected_path):
    samples = cases()
    inputs.write_text("\n".join(serialise(x) for x in samples) + "\n")
    results = [reference(x) for x in samples]
    expected_path.write_text("\n".join(json.dumps(x, sort_keys=True) for x in results) + "\n")
    tally = {}
    for row in results:
        key = (row["status"], row.get("reason", "accepted"))
        tally[str(key)] = tally.get(str(key), 0) + 1
    print(json.dumps({"status": "generated", "seed": 1559,
                      "cases": len(samples), "outcomes": tally}, sort_keys=True))


def check(expected_path, output_path):
    expected = [json.loads(line) for line in expected_path.read_text().splitlines()]
    observed = [json.loads(line) for line in output_path.read_text().splitlines()]
    different = mismatch(expected, observed)
    if different:
        for i, (a, b) in enumerate(zip(expected, observed)):
            if a != b:
                raise SystemExit(f"case {i}: expected {a!r}; Lean emitted {b!r}")
        raise SystemExit(f"row count mismatch: {len(expected)} expected, {len(observed)} actual")
    # Comparator mutation testing must REJECT fake success, numeric output and error.
    mutations = []
    for target in ("status", "expectedBaseFee", "reason"):
        forged = [dict(x) for x in observed]
        index = next((i for i, x in enumerate(forged) if target in x), None)
        assert index is not None
        forged[index][target] = "FORGED"
        mutations.append(mismatch(expected, forged) != 0)
    if not all(mutations):
        raise SystemExit("falsification control did not detect mutation")
    print(json.dumps({"status": "native-oracle-match", "cases": len(observed),
                      "mismatches": different, "mutationControls": sum(mutations),
                      "seed": 1559, "notRun": 0}, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--generate", nargs=2, metavar=("INPUT_TSV", "EXPECTED_JSONL"))
    group.add_argument("--check", nargs=2, metavar=("EXPECTED_JSONL", "OBSERVED_JSONL"))
    args = parser.parse_args()
    if args.generate:
        generate(*(Path(x) for x in args.generate))
    else:
        check(*(Path(x) for x in args.check))
