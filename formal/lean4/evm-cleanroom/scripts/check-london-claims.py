#!/usr/bin/env python3
"""Fail-closed actual Lean axiom and source-blob audit for the London slice."""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "evidence/2026-11-23-london-header/claims.json"
PATTERN = re.compile(
    r"'EVMCleanroom\.HeaderFees\.([A-Za-z0-9_]+)' depends on axioms: \[([^\]]*)\]"
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def read_axioms(text):
    result = {}
    for match in PATTERN.finditer(text):
        name = match.group(1)
        deps = [piece.strip() for piece in match.group(2).split(",") if piece.strip()]
        if name in result:
            raise ValueError(f"duplicate report: {name}")
        result[name] = deps
    if "sorryAx" in text or "native_decide" in text or "unsafe" in text:
        raise ValueError("banned proof-bypass text in Lean report")
    return result


def compare(expected, transcript):
    got = read_axioms(transcript)
    if set(got) != set(expected):
        raise ValueError(f"declaration set mismatch: {set(got) ^ set(expected)}")
    for name, values in expected.items():
        if set(values) - ALLOWED:
            raise ValueError(f"unpermitted ledger axiom: {name} {values}")
        if got[name] != values:
            raise ValueError(f"actual axiom mismatch: {name} {got[name]} != {values}")
    return len(got)


def verify_sources(ledger):
    for relative, expected in ledger["sourceBlobs"].items():
        actual = subprocess.check_output(
            ["git", "hash-object", relative], cwd=ROOT, text=True
        ).strip()
        if actual != expected:
            raise ValueError(f"source drift: {relative} {actual} != {expected}")
    return len(ledger["sourceBlobs"])


def selftest(expected):
    original = "\n".join(
        f"'EVMCleanroom.HeaderFees.{name}' depends on axioms: [{', '.join(deps)}]"
        for name, deps in expected.items()
    )
    assert compare(expected, original) == len(expected)
    mutants = [
        original.replace("propext", "unexpectedAxiom", 1),
        original.replace("'EVMCleanroom.HeaderFees.checkHeader_sound'", "'EVMCleanroom.HeaderFees.unrecorded'", 1),
        original.replace("depends on axioms", "does NOT depend on axioms", 1),
    ]
    rejects = 0
    for altered in mutants:
        try:
            compare(expected, altered)
        except ValueError:
            rejects += 1
    if rejects != len(mutants):
        raise ValueError("an axiom-ledger falsification control was accepted")
    return rejects


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--selftest", action="store_true")
    p.add_argument("--report", type=Path)
    args = p.parse_args()
    ledger = json.loads(LEDGER.read_text())
    if args.selftest:
        print(json.dumps({
            "status": "negative-controls-pass",
            "rejected": selftest(ledger["axioms"]),
        }, sort_keys=True))
    else:
        if args.report is None:
            p.error("--report required unless --selftest")
        pinned = verify_sources(ledger)
        actual = compare(ledger["axioms"], args.report.read_text())
        print(json.dumps({
            "status": "printed-axioms-source-pinned",
            "sourceBlobs": pinned,
            "selectedTheorems": actual,
        }, sort_keys=True))
