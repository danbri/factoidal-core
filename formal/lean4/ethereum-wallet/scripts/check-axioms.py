#!/usr/bin/env python3
"""Axiom audit for the Ethereum wallet package, from a `lake build` log.

Every `#print axioms` report for a declaration under `EthereumWallet.` must
name only propext, Classical.choice and Quot.sound, and every theorem listed
in scripts/theorems/*.txt (one fully qualified name per line, `#` comments)
must have a report. Each area keeps its own list file, so adding theorems
never touches another area's file.

usage: check-axioms.py <build.log> [--out report.json]
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
    here = Path(__file__).resolve().parent
    reports = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S):
        reports[name] = sorted(set(re.findall(r"[\w.]+", body)))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        reports[name] = []
    wallet = {name: axioms for name, axioms in reports.items() if name.startswith("EthereumWallet.")}
    bad = {name: axioms for name, axioms in wallet.items() if not set(axioms) <= ALLOWED}
    expected = {}
    for path in sorted((here / "theorems").glob("*.txt")):
        names = [line.split("#")[0].strip() for line in path.read_text().splitlines()]
        expected[path.name] = [name for name in names if name]
    missing = {area: [name for name in names if name not in wallet]
               for area, names in expected.items()}
    missing = {area: names for area, names in missing.items() if names}
    report = {
        "allowedAxioms": sorted(ALLOWED),
        "walletReports": len(wallet),
        "expectedByArea": {area: len(names) for area, names in expected.items()},
        "outsideAllowed": bad,
        "missingReports": missing,
        "axiomsUsed": sorted({axiom for axioms in wallet.values() for axiom in axioms}),
        "passed": not bad and not missing and bool(wallet),
    }
    if out:
        out.write_text(json.dumps({**report, "reports": wallet}, indent=2) + "\n")
    print(json.dumps(report))
    sys.exit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
