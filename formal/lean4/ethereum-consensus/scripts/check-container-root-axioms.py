#!/usr/bin/env python3
"""Record the actual fixed-container axiom inventory, bound to checked sources."""
import argparse
import json
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[4]
PREFIX = "formal/lean4/ethereum-consensus/"
MODULE = PREFIX + "EthereumConsensus/SSZ/ContainerRoots.lean"
PATHS = [PREFIX + "EthereumConsensus/SSZ/" + name + ".lean" for name in
         ("AttestationData", "SigningDomains", "ContainerRoots", "BasicTypes", "ByteProof", "MultiProofHelpers", "CheckedBranch", "GIndex")]
PATHS += ["formal/lean4/L4Factoidal/Crypto/" + name + ".lean" for name in ("SHA2", "SHA2Theorems")]
PATHS += [PREFIX + name for name in ("ContainerRootsMain.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
NAMES = {"EthereumConsensus.SSZ." + name for name in (
    "checkedContainerRoot_wrong_width", "checkedVersionRoot_wrong_width",
    "checkedBeaconBlockHeader_bad_parent", "beaconBlockHeaderWire_size",
    "beaconHeaderTree_ordered", "beaconBlockHeaderRoot_delegates", "checkpointWire_size",
    "signingDataRoot_ordered", "forkDataRoot_ordered", "signingDataWire_size")}
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
PATTERN = re.compile(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$", re.M)


def require(test, reason):
    if not test:
        raise ValueError(reason)


def parse(log):
    actual = {}
    for name, body, empty in PATTERN.findall(log):
        require(name not in actual, "duplicate print: " + name)
        axioms = [] if empty else [x.strip() for x in body.split(",") if x.strip()]
        require(len(axioms) == len(set(axioms)), "duplicate axiom: " + name)
        require(set(axioms) <= ALLOWED, "unpermitted axiom: " + name)
        actual[name] = axioms
    require(set(actual) == NAMES, "theorem inventory mismatch")
    return actual


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True).strip()


def source_pins():
    declared = re.findall(r"^#print axioms (\S+)\s*$", (REPO / MODULE).read_text(), re.M)
    require(len(declared) == len(NAMES) and set(declared) == NAMES, "source print inventory mismatch")
    pins = {}
    for path in PATHS:
        actual = git("hash-object", path)
        require(actual == git("rev-parse", "HEAD:" + path), "dirty source: " + path)
        pins[path] = actual
    return pins


def self_test():
    # Deliberately synthetic parser inputs: not Lean evidence.
    rows = [f"'{name}' does not depend on any axioms" for name in sorted(NAMES)]
    good = "\n".join(rows)
    assert set(parse(good)) == NAMES
    changed = rows[0].replace("does not depend on any axioms", "depends on axioms: [propext]")
    assert "propext" in parse("\n".join([changed] + rows[1:]))[sorted(NAMES)[0]]
    invalid = ["\n".join(rows[1:]), good + "\n" + rows[0],
               good + "\n'Other.claim' does not depend on any axioms",
               good.replace("does not depend on any axioms", "depends on axioms: [sorryAx]", 1),
               good.replace("does not depend on any axioms", "depends on axioms: [propext, propext]", 1),
               good.replace(sorted(NAMES)[0], "Other.claim", 1)]
    for log in invalid:
        try:
            parse(log)
        except ValueError:
            continue
        raise AssertionError("accepted corrupted inventory")
    print(f"Axiom inventory self-test: 2 synthetic accepted cases; {len(invalid)} refused mutations")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("log", type=Path, nargs="?")
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    if args.self_test:
        self_test()
    else:
        if args.log is None:
            p.error("log is required")
        actual = parse(args.log.read_text())
        print(json.dumps(dict(commit=git("rev-parse", "HEAD"), tree=git("rev-parse", "HEAD^{tree}"),
                              theorem_axioms=actual, sources=source_pins()), sort_keys=True))


if __name__ == "__main__":
    main()
