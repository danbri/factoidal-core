#!/usr/bin/env python3
"""Negative controls for the state-test scoreboard.

Takes one official fixture file whose cases pass, writes tampered copies
(published state root changed, logs hash changed, a spurious expected
exception, a changed signed transaction byte) and checks that the Lean
executable reports each tampered case as a fail, never a pass. Also checks
that the untampered file passes, so the controls are not vacuous.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

FLAGS = ["--dangerously-enable-unverified-keccak", "--dangerously-enable-unverified-secp256k1"]


def run(binary, path):
    out = subprocess.run([binary] + FLAGS + [path], check=True, capture_output=True).stdout
    return [json.loads(l) for l in out.decode().splitlines() if l.strip()]


def flip(hexstr, pos=-1):
    digits = list(hexstr)
    digits[pos] = "1" if digits[pos] != "1" else "2"
    return "".join(digits)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True)
    ap.add_argument("--fixture", required=True)
    args = ap.parse_args()
    with open(args.fixture) as fh:
        data = json.load(fh)
    base = run(args.bin, args.fixture)
    passing = [r for r in base if r["verdict"] == "pass"]
    assert passing, "control fixture has no passing case"
    target = passing[0]
    tid, fork, idx = target["id"], target["fork"], target["index"]

    def tampered(mutate):
        copy = json.loads(json.dumps(data))
        mutate(copy[tid]["post"][fork][idx])
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
            json.dump({tid: copy[tid]}, fh)
            path = fh.name
        rows = [r for r in run(args.bin, path) if r["fork"] == fork and r["index"] == idx]
        os.unlink(path)
        assert len(rows) == 1, rows
        return rows[0]

    def txbyte(entry):
        tx = entry["txbytes"]
        # Change one byte of the calldata region near the end of the envelope
        # (before the signature) so the recovered sender or execution changes.
        entry["txbytes"] = tx[:-140] + flip(tx[-140:-138], 0) + tx[-138:]

    controls = {
        "root": (lambda e: e.__setitem__("hash", flip(e["hash"])), {"fail"}),
        "logs": (lambda e: e.__setitem__("logs", flip(e["logs"])), {"fail"}),
        "exception": (lambda e: e.__setitem__("expectException", "TransactionException.INTRINSIC_GAS_TOO_LOW"), {"fail"}),
        "txbytes": (txbyte, {"fail", "unsupported"}),
    }
    report = {"control": target["id"], "untampered": target["verdict"], "results": {}}
    ok = True
    for name, (mutate, allowed) in controls.items():
        row = tampered(mutate)
        report["results"][name] = {"verdict": row["verdict"], "reason": row.get("reason")}
        if row["verdict"] not in allowed:
            ok = False
    report["status"] = "negative-controls-pass" if ok else "negative-controls-FAILED"
    print(json.dumps(report, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
