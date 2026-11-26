#!/usr/bin/env python3
"""Check the native ordered-list JSON boundary, including the exact input cap.

This uses one fixed synthetic transport fixture. Independent signed whole-list
execution comparison is in scripts/differential/transaction-list.mjs; these
checks do not establish signature, trie or full-block validity.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "scripts/fixtures/transaction-list-transport.json"


def check_transport(executable):
    fixture = json.loads(FIXTURE.read_text())
    base = fixture["input"]
    empty = copy.deepcopy(base)
    empty["transactions"] = []
    empty["childHeader"][10] = ""
    empty["childHeader"][17] = ""
    rows = []
    with tempfile.TemporaryDirectory(prefix="lean-transaction-list-transport-") as temporary:
        directory = Path(temporary)

        def check(name, data, status, *, code=0, reason=None, index="absent", opt_in=True):
            path = directory / (name + ".json")
            raw = data if isinstance(data, bytes) else (json.dumps(data) + "\n").encode()
            path.write_bytes(raw)
            command = [str(executable)]
            if opt_in:
                command.append("--dangerously-enable-unverified-keccak")
            command.extend(["--transaction-list", str(path)])
            process = subprocess.run(command, capture_output=True, timeout=30, check=False)
            assert process.returncode == code, (name, process.returncode, process.stderr)
            assert not process.stderr, (name, process.stderr)
            value = json.loads(process.stdout)
            assert value["schemaVersion"] == 1 and value["status"] == status, (name, value)
            assert value["keccakOptIn"] == opt_in, (name, value)
            if reason is not None:
                assert value["reason"] == reason, (name, value)
            if index != "absent":
                assert value["index"] == index, (name, value)
            if status != "executed":
                assert "accounts" not in value and "receipts" not in value, (name, value)
            rows.append({
                "id": name, "matched": True, "status": status, "exitCode": code,
                "reason": value.get("reason"), "index": value.get("index"), "inputBytes": len(raw),
            })
            return value

        assert check("single-blob", base, "executed") == fixture["expected"]
        result = check("empty", empty, "executed")
        assert result["accounts"] == empty["accounts"] and result["receipts"] == []
        assert result["gasUsed"] == result["blobGasUsed"] == "0"
        for name, key in [("unknown-top-block", "block"), ("unknown-top-counter", "gasUsedBefore")]:
            value = copy.deepcopy(base)
            value[key] = {}
            check(name, value, "inputError", code=2, reason="unexpected field: " + key)
        for name, key in [("unknown-entry-accounts", "accounts"), ("unknown-entry-counter", "priorBlobGas")]:
            value = copy.deepcopy(base)
            value["transactions"][0][key] = []
            check(name, value, "inputError", code=2, reason="unexpected field: " + key)
        for name, key in [("missing-blob-hashes", "blobVersionedHashes"), ("missing-blob-cap", "maxFeePerBlobGas")]:
            value = copy.deepcopy(base)
            del value["transactions"][0][key]
            check(name, value, "inputError", code=2,
                  reason="blobVersionedHashes and maxFeePerBlobGas must be supplied together")
        value = copy.deepcopy(base)
        value["transactions"][0]["blobVersionedHashes"] = None
        check("null-blob-hashes", value, "inputError", code=2)
        value = copy.deepcopy(base)
        value["schemaVersion"] = 2
        check("schema-version", value, "inputError", code=2, reason="expected transaction-list schema version 1")
        check("missing-keccak-opt-in", base, "inputError", code=2, opt_in=False)
        check("invalid-utf8", b"\xff", "inputError", code=2, reason="transaction-list input must be UTF-8")
        check("invalid-json", b"{", "inputError", code=2)
        value = copy.deepcopy(base)
        value["transactions"] *= 257
        check("entry-count", value, "inputError", code=2, reason="too many entries in transactions")
        value = copy.deepcopy(base)
        value["parentHeader"] = [""] * 25
        check("header-count", value, "inputError", code=2, reason="header-field-count")
        value = copy.deepcopy(base)
        value["transactions"][0]["fuel"] = "1000001"
        check("aggregate-fuel", value, "indeterminate", reason="resourceLimit", index=None)
        value = copy.deepcopy(base)
        value["transactions"][0]["transaction"]["type"] = 4
        check("unsupported-kind", value, "indeterminate", reason="unsupported-transaction-type", index=0)
        value = copy.deepcopy(base)
        value["transactions"][0]["transaction"]["type"] = 2
        check("ordinary-blob-fields", value, "rejected", reason="ordinary-blob-fields", index=0)
        value = copy.deepcopy(base)
        target = value["transactions"][0]["transaction"]["to"]
        value["accounts"] = [account for account in value["accounts"] if account["address"] != target]
        result = check("incomplete-state", value, "indeterminate", reason="incompleteState", index=0)
        assert result["address"] == target and result["slot"] is None
        value = copy.deepcopy(base)
        gas = int(value["childHeader"][10], 16) + 1
        value["childHeader"][10] = gas.to_bytes((gas.bit_length() + 7) // 8, "big").hex()
        check("wrong-final-gas", value, "rejected", reason="execution-gas-total-mismatch", index=None)
        cap = 16 * 1024 * 1024
        encoded = (json.dumps(empty) + "\n").encode()
        result = check("input-exact-cap", encoded + b" " * (cap - len(encoded)), "executed")
        assert result["receipts"] == [] and result["accounts"] == empty["accounts"]
        check("input-over-cap", encoded + b" " * (cap + 1 - len(encoded)), "inputError", code=2,
              reason="transaction-list input exceeds the byte limit")
    assert len(rows) == 22 and len({row["id"] for row in rows}) == 22
    return {
        "cases": len(rows), "matched": len(rows), "failures": [], "rows": rows,
        "nativeSha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "fixtureSha256": hashlib.sha256(FIXTURE.read_bytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("executable", nargs="?", type=Path,
                        default=ROOT / ".lake/build/bin/evm-transaction-list")
    args = parser.parse_args()
    print(json.dumps(check_transport(args.executable.resolve()), sort_keys=True))


if __name__ == "__main__":
    main()
