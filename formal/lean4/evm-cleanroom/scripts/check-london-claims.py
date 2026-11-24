#!/usr/bin/env python3
"""Fail-closed actual Lean axiom and source-blob audit for the London slice."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "evidence/active-london-claims.json"
HISTORICAL = "evidence/2026-11-23-london-header/claims.json"
SOURCE_PATHS = {
    "EVMCleanroom/HeaderFees.lean", "EVMCleanroom/HeaderFeeCLI.lean",
    "EVMCleanroom.lean", "lakefile.toml", "lakefile-london.toml",
    "scripts/check-london-header-fees.py",
}
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


def source_blob(relative):
    return subprocess.check_output(
        ["git", "hash-object", relative], cwd=ROOT, text=True
    ).strip()


def verify_sources(ledger, read_blob=source_blob):
    if set(ledger["sourceBlobs"]) != SOURCE_PATHS:
        raise ValueError("London source inventory must contain exactly the six reviewed paths")
    for relative, expected in ledger["sourceBlobs"].items():
        if re.fullmatch(r"[0-9a-f]{40}", expected) is None:
            raise ValueError(f"invalid source pin: {relative}")
        actual = read_blob(relative)
        if actual != expected:
            raise ValueError(f"source drift: {relative} {actual} != {expected}")
    return len(ledger["sourceBlobs"])


def verify_manifest(ledger):
    if ledger["historicalManifest"] != HISTORICAL:
        raise ValueError("unexpected historical London manifest")
    historical = (ROOT / HISTORICAL).read_bytes()
    if hashlib.sha256(historical).hexdigest() != ledger["historicalManifestSha256"]:
        raise ValueError("historical London evidence changed")
    if ledger["leanToolchain"] != (ROOT / "lean-toolchain").read_text().strip():
        raise ValueError("London toolchain pin mismatch")
    if json.loads((ROOT / "lake-manifest.json").read_text())["packages"] != []:
        raise ValueError("external Lake packages are not allowed")


def selftest(ledger):
    expected = ledger["axioms"]
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
    # Exercise the same source verifier without mutating any working file.
    # Corrupt one reviewed pin while retaining the baseline observed blobs.
    baseline = ledger["sourceBlobs"]
    assert verify_sources(ledger, baseline.__getitem__) == 6
    corrupted = dict(ledger, sourceBlobs=dict(baseline))
    path = "EVMCleanroom.lean"
    corrupted["sourceBlobs"][path] = "0" * 40 if baseline[path] != "0" * 40 else "1" * 40
    try:
        verify_sources(corrupted, baseline.__getitem__)
    except ValueError:
        rejects += 1
    if rejects != len(mutants) + 1:
        raise ValueError("a corrupted source pin was accepted")
    return rejects


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--selftest", action="store_true")
    p.add_argument("--report", type=Path)
    args = p.parse_args()
    ledger = json.loads(LEDGER.read_text())
    verify_manifest(ledger)
    if args.selftest:
        print(json.dumps({
            "status": "negative-controls-pass",
            "rejected": selftest(ledger),
            "sourceDriftRejected": True,
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
