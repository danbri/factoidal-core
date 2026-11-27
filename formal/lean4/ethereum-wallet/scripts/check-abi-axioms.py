#!/usr/bin/env python3
"""Axiom audit for the ABI, typed-data and call theorems, from a `lake build` log.

Every theorem named in scripts/theorems/abi.txt must have a `#print axioms`
report in the log, and every report for a declaration under `EthereumWallet.`
must name only propext, Classical.choice and Quot.sound.

usage: check-abi-axioms.py <build.log> [--out report.json]
"""
import json
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    args = sys.argv[1:]
    out = None
    if "--out" in args:
        i = args.index("--out")
        out = Path(args[i + 1])
        del args[i:i + 2]
    log = Path(args[0]).read_text()
    reports = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S):
        reports[name] = sorted(set(re.findall(r"[\w.]+", body)))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        reports[name] = []
    wallet = {n: a for n, a in reports.items() if n.startswith("EthereumWallet.")}
    listed = Path(__file__).resolve().parent / "theorems" / "abi.txt"
    expected = [line.split("#")[0].strip() for line in listed.read_text().splitlines()]
    expected = [name for name in expected if name]
    missing = [name for name in expected if name not in wallet]
    bad = {n: a for n, a in wallet.items() if not set(a) <= ALLOWED}
    by_set = {}
    for name in expected:
        if name in wallet:
            by_set.setdefault(",".join(wallet[name]) or "none", []).append(name)
    report = {
        "allowedAxioms": sorted(ALLOWED),
        "expected": len(expected),
        "reported": len([n for n in expected if n in wallet]),
        "missingReports": missing,
        "outsideAllowed": bad,
        "countByAxiomSet": {k: len(v) for k, v in sorted(by_set.items())},
        "passed": bool(expected) and not missing and not bad,
    }
    if out:
        out.write_text(json.dumps({**report, "reports": {n: wallet[n] for n in expected if n in wallet}}, indent=2) + "\n")
    print(json.dumps(report))
    sys.exit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
