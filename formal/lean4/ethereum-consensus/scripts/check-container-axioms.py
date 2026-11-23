#!/usr/bin/env python3
"""Fail-closed exact-source and Lean axiom ledger audit for SSZ containers.

This checker consumes the real Lean 4.33.1 #print axioms stream. A ledger is
not proof evidence until the matching Lean compilation has succeeded.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

REPOSITORY = Path(__file__).resolve().parents[4]
NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*"
DECLARATIONS = re.compile(rf"^\s*#print\s+axioms\s+({NAME})\s*$", re.M)
ACTUAL = re.compile(
    rf"^\s*'({NAME})' "
    r"(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$",
    re.M,
)


def demand(test, reason):
    if not test:
        raise ValueError(reason)


def blob_sha(raw):
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("ledger")
    parser.add_argument("lean_output")
    args = parser.parse_args()
    ledger = json.loads(Path(args.ledger).read_text())
    demand(ledger.get("schema") == "factoidal.ethereum-consensus.ssz-container-claims.v1",
           "unexpected evidence schema")
    selected = REPOSITORY / "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ContainerRoots.lean"
    found = set(DECLARATIONS.findall(selected.read_text()))
    expected = ledger["theorem_axioms"]
    demand(len(found) == len(expected) == 10 and set(expected) == found,
           "source declaration inventory differs from the ledger")
    checked_paths = set()
    for source in ledger["sources"]:
        path = REPOSITORY / source["path"]
        demand(path.resolve().is_relative_to(REPOSITORY.resolve()), "path escape")
        demand(path.suffix == ".lean" and path not in checked_paths,
               "duplicate or non-Lean source")
        checked_paths.add(path)
        demand(blob_sha(path.read_bytes()) == source["git_blob_sha"],
               f"changed audited source: {source['path']}")
    output = Path(args.lean_output).read_text()
    actual = {}
    for name, listed, empty in ACTUAL.findall(output):
        demand(name not in actual, "duplicate printed axiom report")
        names = [] if empty or not listed.strip() else [x.strip() for x in listed.split(",")]
        demand(len(names) == len(set(names)), f"duplicate axiom: {name}")
        demand(set(names) <= set(ledger["axiom_allowlist"]),
               f"unpermitted Lean axiom: {name}: {names}")
        actual[name] = names
    demand(set(actual) == found, f"missing or extra Lean axiom result: {sorted(set(actual) ^ found)}")
    demand(actual == expected, "actual printed axiom sets differ from ledger")
    print(json.dumps({"theorems_checked": len(actual),
                      "source_blobs_checked": len(checked_paths),
                      "axioms": dict(sorted(actual.items()))}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"SSZ container axiom audit failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
