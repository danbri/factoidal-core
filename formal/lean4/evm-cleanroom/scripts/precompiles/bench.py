#!/usr/bin/env python3
"""Time per call of each precompile in the native Lean binary, against its gas price.

Inputs are the published vectors (same pinned files as run-vectors.py) plus a
few sized hash inputs. Each case is called REPEATS times in one process; the
per-precompile row gives the spread over cases of the per-case median, the
slowest single call, and nanoseconds per gas unit. The published ECRECOVER
vectors are mostly invalid signatures, which return early; `--valid-ecrecover
FILE` adds a row of valid signatures only (one `PROFILE 1 GAS HEX` line each,
as written by `evm-secpperf --emit-valid COUNT`). As a ballpark, clients
that execute around 100 million gas per second spend about 10 ns per gas
unit; `slowdown` is the measured ns/gas divided by that. This is a report,
not a gate: timings on a shared runner are noisy.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCES = json.loads((HERE / "sources.json").read_text())
NAMES = {1: "ecrecover", 2: "sha256", 3: "ripemd160", 5: "modexp", 6: "bn254-add", 7: "bn254-mul",
         8: "bn254-pairing", 9: "blake2f", 10: "kzg-point-evaluation", 11: "bls-g1add", 12: "bls-g1msm",
         13: "bls-g2add", 14: "bls-g2msm", 15: "bls-pairing", 16: "bls-map-fp-to-g1", 17: "bls-map-fp2-to-g2", 256: "p256verify"}
REFERENCE_NS_PER_GAS = 10.0


def percentile(values, percent):
    ordered = sorted(values)
    return ordered[(len(ordered) - 1) * percent // 100]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--max-cases-per-file", type=int, default=40)
    parser.add_argument("--valid-ecrecover", type=Path, help="batch file of valid ECRECOVER calls, timed as a row of its own")
    args = parser.parse_args()
    cases = []
    for entry in SOURCES["files"]:
        if entry["kind"] != "ok":
            continue
        data = (args.cache / entry["file"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["file"]
        for vector in json.loads(data)[:args.max_cases_per_file]:
            cases.append((entry["profile"], entry["address"], int(vector["Gas"]), vector["Input"].lower()))
    labels = [""] * len(cases)
    for size in (0, 32, 1024, 65536):
        words = (size + 31) // 32
        cases.append(("shanghaiPlus", 2, 60 + 12 * words, "ab" * size))
        cases.append(("shanghaiPlus", 3, 600 + 120 * words, "ab" * size))
        labels += ["", ""]
    if args.valid_ecrecover:
        for line in args.valid_ecrecover.read_text().split("\n"):
            if line.strip():
                profile, address, gas, data = line.split()
                assert address == "1", line
                cases.append((profile, 1, int(gas), data))
                labels.append("valid signatures only")
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as handle:
        for profile, address, gas, data in cases:
            handle.write("%s %d %d %s\n" % (profile, address, gas, data or "-"))
        name = handle.name
    done = subprocess.run([args.binary, "--dangerously-enable-unverified-keccak", "--bench", name,
                           str(args.repeats)], capture_output=True, text=True, timeout=3600)
    Path(name).unlink()
    if done.returncode != 0:
        raise SystemExit(done.stderr[:400])
    rows = {}
    lines = done.stdout.splitlines()
    assert len(lines) == len(cases) == len(labels), (len(lines), len(cases), len(labels))
    for line, label in zip(lines, labels):
        address, size, used, low, median, high, top = (int(x) for x in line.split())
        rows.setdefault((address, label), []).append((size, used, low, median, high, top))
    report = []
    for address, label in sorted(rows):
        key = (address, label)
        medians = [r[3] for r in rows[key]]
        per_gas = sorted(r[3] / r[1] for r in rows[key] if r[1] > 0)
        typical = per_gas[len(per_gas) // 2] if per_gas else None
        report.append({
            "address": address, "name": NAMES.get(address, "?") + (" (%s)" % label if label else ""), "cases": len(medians),
            "p50_us": round(percentile(medians, 50) / 1000, 1),
            "p95_us": round(percentile(medians, 95) / 1000, 1),
            "max_us": round(max(r[5] for r in rows[key]) / 1000, 1),
            "ns_per_gas_p50": None if typical is None else round(typical, 1),
            "ns_per_gas_max": None if not per_gas else round(per_gas[-1], 1),
            "slowdown_vs_10ns_per_gas": None if typical is None else round(typical / REFERENCE_NS_PER_GAS, 1),
        })
    print(json.dumps({"repeats": args.repeats, "referenceNsPerGas": REFERENCE_NS_PER_GAS, "rows": report}, indent=1))


if __name__ == "__main__":
    sys.exit(main())
