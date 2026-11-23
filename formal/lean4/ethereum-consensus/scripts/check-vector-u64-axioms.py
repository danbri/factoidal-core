#!/usr/bin/env python3
"""Fail-closed source/inventory/allowed-axiom audit for fixed uint64 SSZ vectors.

This first-stage ledger pins the exact implementation/CLI source blobs and
theorem names. It audits ACTUAL Lean #print axioms, but it deliberately does
not claim the exact per-theorem axiom sets until verified source output is
captured and added to a versioned ledger.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

REPOSITORY = Path(__file__).resolve().parents[4]
NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*"
PRINT = re.compile(rf"^\s*#print\s+axioms\s+({NAME})\s*$", re.M)
OUTPUT = re.compile(
    rf"^\s*'({NAME})' "
    r"(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$",
    re.M
)


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def git_blob(content):
    return hashlib.sha1(f"blob {len(content)}\0".encode() + content).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("ledger")
    parser.add_argument("lean_output")
    args = parser.parse_args()
    ledger = json.loads(Path(args.ledger).read_text())
    demand(ledger.get("schema") == "factoidal.ethereum-consensus.vector-u64-claims.v1",
           "invalid source ledger schema")
    expected = set(ledger["theorems"])
    demand(len(expected) == len(ledger["theorems"]) == 9, "theorem inventory mismatch")
    seen = set()
    for pin in ledger["sources"]:
        rel = Path(pin["path"])
        path = REPOSITORY / rel
        demand(not rel.is_absolute() and path.resolve().is_relative_to(REPOSITORY.resolve()),
               "non-canonical source path")
        demand(path not in seen and path.suffix == ".lean", "duplicate/non-Lean source")
        seen.add(path)
        demand(git_blob(path.read_bytes()) == pin["git_blob_sha"],
               f"source blob mismatch: {rel}")
    selected = REPOSITORY / "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/VectorU64.lean"
    source = selected.read_text()
    declarations = set(PRINT.findall(source))
    demand(declarations == expected,
           f"source theorem prints differ: {sorted(declarations ^ expected)}")
    actual = {}
    for name, listed, empty in OUTPUT.findall(Path(args.lean_output).read_text()):
        demand(name not in actual, f"duplicate printed theorem: {name}")
        axioms = [] if empty or not listed.strip() else [s.strip() for s in listed.split(",")]
        demand(len(axioms) == len(set(axioms)), f"duplicate printed axioms: {name}")
        demand(set(axioms) <= set(ledger["axiom_allowlist"]),
               f"unpermitted proof axioms: {name} => {axioms}")
        actual[name] = axioms
    demand(set(actual) == expected,
           f"missing/extra actual theorem outputs: {sorted(set(actual) ^ expected)}")
    print(json.dumps({"source_pins_checked": len(seen), "theorems_checked": len(actual),
          "axioms": dict(sorted(actual.items()))}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Vector source/axiom audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
