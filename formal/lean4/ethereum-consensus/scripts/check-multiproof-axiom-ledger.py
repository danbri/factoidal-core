#!/usr/bin/env python3
"""Fail-closed, source-pinned audit of actual Lean #print axioms output.

This checks the source *blob*, each declared printed theorem and the real
Lean-emitted axiom set. It is not proof of normative equivalence to SSZ.
"""
import hashlib
import json
from pathlib import Path
import re
import sys


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\x00" + data).hexdigest()


def check(ledger_path: Path, output_path: Path) -> None:
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    if ledger.get("schema") != "factoidal.ethereum-consensus.ssz-multiproof-claims.v1":
        raise AssertionError("unknown claim ledger schema")
    source = Path(ledger["source"]["path"])
    blob = source.read_bytes()
    actual_hash = git_blob_sha(blob)
    if actual_hash != ledger["source"]["git_blob_sha"]:
        raise AssertionError(
            f"source blob changed without evidence update: {actual_hash} "
            f"vs {ledger['source']['git_blob_sha']}"
        )

    expected = ledger["theorem_axioms"]
    if not expected or len(expected) != 13:
        raise AssertionError("incomplete theorem ledger")
    if len(set(expected)) != len(expected):
        raise AssertionError("repeated theorem names")
    declared = re.findall(r"^#print axioms\s+([A-Za-z0-9_.]+)\s*$", blob.decode("utf-8"), re.M)
    if len(declared) != len(set(declared)) or set(declared) != set(expected):
        raise AssertionError(f"source #print axiom declarations drifted: {declared}")

    output = output_path.read_text(encoding="utf-8")
    pattern = re.compile(
        r"'(EthereumConsensus\.SSZ\.[A-Za-z0-9_]+)' "
        r"(?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))"
    )
    observed = {}
    for name, axiom_list, empty_marker in pattern.findall(output):
        if name in observed:
            raise AssertionError(f"duplicate Lean output for {name}")
        observed[name] = [] if empty_marker else [
            x.strip() for x in axiom_list.split(",") if x.strip()
        ]
    if set(observed) != set(expected):
        raise AssertionError(
            f"Lean theorem inventory mismatch: missing={set(expected) - set(observed)}, "
            f"extra={set(observed) - set(expected)}"
        )
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    for name, recorded in expected.items():
        if len(recorded) != len(set(recorded)):
            raise AssertionError(f"duplicate recorded axiom in {name}")
        if not set(recorded).issubset(allowed):
            raise AssertionError(f"unpermitted recorded axiom in {name}: {recorded}")
        if observed[name] != recorded:
            raise AssertionError(
                f"theorem {name}: actual {observed[name]}, recorded {recorded}"
            )
    empty = sum(not v for v in observed.values())
    print(
        f"Lean SSZ multiproof claim ledger: {len(expected)} actual printed "
        f"axiom sets matched source blob {actual_hash}; {empty} empty, "
        f"{len(expected)-empty} permitted-foundation-only"
    )


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: check-multiproof-axiom-ledger.py <ledger.json> <lean-output.txt>")
    check(Path(sys.argv[1]), Path(sys.argv[2]))
