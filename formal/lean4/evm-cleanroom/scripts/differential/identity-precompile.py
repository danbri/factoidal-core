#!/usr/bin/env python3
"""Independent direct identity-precompile oracle: no external EVM package.

The Python logic below is a test oracle only. The implementation that emits
each result is the Lean executable passed as argv[1]. This does not exercise
CALL dispatch, account state, or transaction settlement.
"""
import copy
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

COUNT = 1056
BOUNDARIES = (0, 1, 2, 3, 31, 32, 33, 34, 63, 64, 65, 66,
              95, 96, 97, 127, 128, 129, 159, 160, 161, 255, 256, 257)


def oracle(payload, gas, limit):
    if len(payload) > limit:
        return {"status": "indeterminate", "reason": "resourceLimit"}
    charge = 15 + 3 * ((len(payload) + 31) // 32)
    if gas < charge:
        return {"status": "exceptional", "reason": "outOfGas"}
    return {"status": "ok", "dataHex": payload.hex(),
            "gasRemaining": str(gas - charge), "gasUsed": str(charge)}


def cases():
    rng = random.Random(0xE711D4)
    rows = []
    for i in range(COUNT):
        length = BOUNDARIES[i % len(BOUNDARIES)] if i % 4 else rng.randrange(0, 321)
        payload = bytes(rng.randrange(256) for _ in range(length))
        if i % 7 == 0:
            payload = bytes(min(3, length)) + payload[min(3, length):]
        if i % 11 == 0:
            payload = bytes(length)
        charge = 15 + 3 * ((length + 31) // 32)
        mode = i % 6
        if mode == 0:      # Exact forwarded gas, including empty data.
            gas, limit = charge, length
        elif mode == 1:    # One unit below required gas.
            gas, limit = charge - 1, length
        elif mode == 2:    # Explicit local resource failure, including empty case.
            gas, limit = charge + 30, max(0, length - 1)
        elif mode == 3:    # A larger forwarding budget must be returned.
            gas, limit = charge + rng.randrange(1, 300), length + 1
        elif mode == 4:    # Oversize refusal has priority over gas shortage.
            gas, limit = 0, max(0, length - 1)
        else:              # A warm ordinary caller could supply exact short input.
            gas, limit = charge + i % 17, length
        rows.append((payload, gas, limit))
    return rows


def compare(observed, expected):
    return (isinstance(observed, list) and len(observed) == len(expected)
            and all(got == want for got, want in zip(observed, expected)))


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: identity-precompile.py PATH_TO_LEAN_EXECUTABLE")
    binary = str(Path(sys.argv[1]).resolve())
    rows = cases()
    expected = [oracle(*row) for row in rows]
    with tempfile.TemporaryDirectory(prefix="lean-evm-identity-") as temporary:
        request = Path(temporary) / "cases.tsv"
        request.write_text("".join(
            f"{payload.hex()}\t{gas}\t{limit}\n"
            for payload, gas, limit in rows))
        proc = subprocess.run([binary, "--batch", str(request)], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=90, check=False)
        if proc.returncode != 0:
            raise RuntimeError(f"Lean batch returned {proc.returncode}: {proc.stderr[-1200:]}")
        observed = [json.loads(line) for line in proc.stdout.splitlines()]
        if not compare(observed, expected):
            mismatch = next((i for i, (a, b) in enumerate(zip(observed, expected))
                             if a != b), None)
            raise AssertionError(f"Lean/precompile mismatch: rows={len(observed)} "
                                 f"expected={len(expected)} first={mismatch} "
                                 f"observed={observed[mismatch] if mismatch is not None and mismatch < len(observed) else None} "
                                 f"expectedRow={expected[mismatch] if mismatch is not None else None}")

        # The comparator must reject altered data, gas and failure category.
        successes = [i for i, x in enumerate(observed) if x["status"] == "ok"]
        failures = [i for i, x in enumerate(observed) if x["status"] != "ok"]
        assert successes and failures
        mutated_data = copy.deepcopy(observed)
        mutated_data[successes[0]]["dataHex"] += "00"
        mutated_gas = copy.deepcopy(observed)
        mutated_gas[successes[0]]["gasRemaining"] = "999999999"
        mutated_refusal = copy.deepcopy(observed)
        mutated_refusal[failures[0]]["status"] = "ok"
        assert all(not compare(m, expected)
                   for m in (mutated_data, mutated_gas, mutated_refusal))

        request.write_text("0x00\t17\t1\ninvalid_hex\t20\t10\n")
        rejected = subprocess.run([binary, "--batch", str(request)], text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  timeout=30, check=False)
        rejected_rows = [json.loads(line) for line in rejected.stdout.splitlines()]
        if rejected.returncode != 2 or len(rejected_rows) != 2 or (
                rejected_rows[1].get("status") != "inputError"):
            raise AssertionError("malformed batch record was not rejected")

    counts = {status: sum(x["status"] == status for x in observed)
              for status in ("ok", "exceptional", "indeterminate")}
    assert sum(counts.values()) == COUNT
    assert counts["ok"] >= 400 and counts["exceptional"] >= 100 and counts["indeterminate"] >= 100
    print(json.dumps({
        "status": "pass", "leanExecuted": len(observed),
        "oracle": "independent Python stdlib length/gas/bytes",
        "matched": COUNT, "mismatches": 0,
        "outcomes": counts, "mutationsRejected": 3,
        "malformedBatchRejected": True, "inputBytesCompared": sum(len(p) for p, _, _ in rows),
        "scope": "direct identity precompile, not CALL dispatch"}))


if __name__ == "__main__":
    main()
