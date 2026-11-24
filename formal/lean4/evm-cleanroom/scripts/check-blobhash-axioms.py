#!/usr/bin/env python3
"""Audit the selected blob-call/BLOBHASH proofs and their executable sources.

The inventory is explicit and checked against actual Lean 4.33.1 output and
the active ledger's exact axiom sets. This is a local-model proof audit, not
Ethereum refinement, signed-envelope authentication or KZG verification.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "evidence/active-claim-manifest-v2.json"
SPEC = importlib.util.spec_from_file_location("active_axioms", ROOT / "scripts/check-axiom-output.py")
ACTIVE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ACTIVE)

# Keep the inherited seven BlobCall claims as well as every newly selected
# context/admission/opcode theorem. Existing unrelated proofs are audited by
# check-axiom-output.py, not counted again as BLOBHASH claims here.
INVENTORY = {
    "EVMCleanroom/Core.lean": [
        "EVMCleanroom.step_blobHash", "EVMCleanroom.step_blobHash_underflow",
        "EVMCleanroom.step_blobHash_unknown_fork",
    ],
    "EVMCleanroom/World.lean": [
        "EVMCleanroom.World.frameInput_txBlobHashes",
        "EVMCleanroom.World.commitFrame_txBlobHashes",
    ],
    "EVMCleanroom/CallOpcode.lean": [
        "EVMCleanroom.CallOpcode.beginCall_entered_txBlobHashes",
        "EVMCleanroom.CallOpcode.beginVariant_entered_txBlobHashes",
    ],
    "EVMCleanroom/CallTransaction.lean": [
        "EVMCleanroom.CallTransaction.run_empty_blobHashes",
        "EVMCleanroom.CallTransaction.debitSender_blobHashes",
        "EVMCleanroom.CallTransaction.entryFrame_blobHashes",
    ],
    "EVMCleanroom/BlobHashProofs.lean": [
        "EVMCleanroom.World.pay_txBlobHashes",
        "EVMCleanroom.step_blobHash_success",
        "EVMCleanroom.step_blobHash_in_range",
        "EVMCleanroom.step_blobHash_out_of_range",
        "EVMCleanroom.step_blobHash_outOfGas",
        "EVMCleanroom.commit_txBlobHashes",
        "EVMCleanroom.step_txBlobHashes",
    ],
    "EVMCleanroom/BlobCall.lean": [
        "EVMCleanroom.BlobCall." + name for name in (
            "burn_sender", "burn_other", "burn_exact", "funds_refused",
            "prepared_exact", "header_refused", "execute_exact", "prepared_blobHashes",
        )
    ],
    "EVMCleanroom/BlobCallProofs.lean": [
        "EVMCleanroom.BlobCall." + name for name in (
            "prepareWithFees_checked", "prepare_blobHashes_checked",
            "prepared_entry_blobHashes", "admitted_entry_blobHashes", "validated_entry_blobHashes",
        )
    ],
}
EXACT_SOURCES = {
    "EVMCleanroom/BlobHashProofs.lean", "EVMCleanroom/BlobCall.lean",
    "EVMCleanroom/BlobCallProofs.lean",
}
SOURCE_ROOTS = [
    "EVMCleanroom/BlobCallCLI.lean", "EVMCleanroom/CLITransaction.lean",
    "EVMCleanroom/BlobCallProofs.lean", "EVMCleanroom/BlobHashTests.lean",
]
SUPPORT_SOURCES = {
    "EVMCleanroom.lean", "lakefile.toml", "lakefile-blob-call.toml",
    "lean-toolchain", "lake-manifest.json", "scripts/check-blobhash-axioms.py",
    "scripts/check-axiom-output.py", "scripts/differential/blob-call.mjs",
    "scripts/differential/blobhash-transactions.mjs",
    "scripts/differential/geth-byte-oracle.mjs",
    "scripts/differential/package.json", "scripts/differential/package-lock.json",
    "scripts/eels/package.json",
}
require = ACTIVE.require


def check(expected, transcript, exact=False):
    printed = ACTIVE.extract_printed(transcript)
    ACTIVE.verify_printed(expected, printed)
    if exact:
        require(set(printed) == {x["name"] for x in expected},
                "unexpected theorem output in dedicated source")
    return {x["name"]: list(printed[x["name"]][0]) for x in expected}


def selftest():
    expected = [
        {"name": "EVMCleanroom.BlobCall.execute_exact", "axioms_printed": ["propext", "Quot.sound"]},
        {"name": "EVMCleanroom.BlobCall.prepared_blobHashes", "axioms_printed": []},
    ]
    good = "\n".join([
        "info: source.lean:1:0: 'EVMCleanroom.BlobCall.execute_exact' "
        "depends on axioms: [propext,\n Quot.sound]",
        "'EVMCleanroom.BlobCall.prepared_blobHashes' does not depend on any axioms",
    ])
    require(len(check(expected, good, True)) == 2, "wrapped positive control failed")
    corrupt = {
        "missing-theorem": good.split("\n'", 1)[0],
        "duplicate-wrapped-report": good + "\n" + good,
        "wrapped-sorryAx": good.replace("Quot.sound]", "sorryAx,\n Quot.sound]"),
        "wrapped-custom-axiom": good.replace("Quot.sound]", "EVMCleanroom.unproved,\n Quot.sound]"),
        "duplicate-axiom": good.replace("Quot.sound]", "Quot.sound, propext]"),
        "dropped-required-axiom": good.replace("propext,\n ", ""),
        "extra-theorem": good + "\n'EVMCleanroom.BlobCall.extra' does not depend on any axioms",
        "truncated-wrapped-list": good.replace("Quot.sound]", "Quot.sound"),
    }
    rejected = []
    for label, transcript in corrupt.items():
        try:
            check(expected, transcript, True)
        except ValueError:
            rejected.append(label)
    require(len(rejected) == len(corrupt), "adversarial transcript survived")
    return {"status": "negative-controls-pass", "rejected": len(rejected),
            "controls": rejected, "wrappedPositiveAccepted": True}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def source_pins(manifest, require_head):
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1",
            "unexpected Lean toolchain")
    require(json.loads((ROOT / "lake-manifest.json").read_text())["packages"] == [],
            "external Lake packages are not allowed")
    paths = set(SUPPORT_SOURCES)
    pending = list(SOURCE_ROOTS)
    while pending:
        source = pending.pop()
        if source in paths:
            continue
        paths.add(source)
        text = (ROOT / source).read_text()
        require(not re.search(r"\b(sorry|native_decide|unsafe|implemented_by|axiom)\b|partial\s+def", text),
                "unpermitted token in executable/proof closure: " + source)
        for line in text.splitlines():
            if not line.startswith("import "):
                continue
            for module in line.split()[1:]:
                if module == "Std" or module.startswith("Std.") or module == "Lean.Data.Json":
                    continue
                require(module.startswith("EVMCleanroom."), "unapproved import: " + module)
                pending.append(module.replace(".", "/") + ".lean")
    pins = {}
    for source in sorted(paths):
        contents = (ROOT / source).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(contents)).encode() + b"\0" + contents).hexdigest()
        require(manifest["source_blobs"].get(source) == blob, "unpinned or changed source: " + source)
        if require_head:
            require(git("rev-parse", "HEAD:formal/lean4/evm-cleanroom/" + source) == blob,
                    "source differs from checked-out HEAD: " + source)
        pins[source] = blob
    return pins


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--require-head", action="store_true",
                        help="also require every reviewed source to match Git HEAD (hosted CI)")
    parser.add_argument("--out", type=Path)
    parser.add_argument("--transcripts-dir", type=Path)
    args = parser.parse_args()
    if args.selftest:
        print(json.dumps(selftest(), sort_keys=True))
        return
    manifest = json.loads(MANIFEST.read_text())
    claims = manifest["theorem_inventory"]
    selected = {}
    for source, names in INVENTORY.items():
        selected[source] = []
        for name in names:
            matches = [x for x in claims if x["name"] == name]
            require(len(matches) == 1 and matches[0]["source"] == source,
                    "missing, duplicate or misattributed active claim: " + name)
            selected[source].append(matches[0])
    pins = source_pins(manifest, args.require_head)
    actual = {}
    if args.transcripts_dir:
        args.transcripts_dir.mkdir(parents=True, exist_ok=True)
    for source, expected in selected.items():
        result = subprocess.run(
            ["lake", "-d", "evm-cleanroom", "env", "lean", str(ROOT / source)],
            cwd=ROOT.parent, capture_output=True, text=True, timeout=120, check=False,
        )
        transcript = result.stdout + "\n" + result.stderr
        if args.transcripts_dir:
            (args.transcripts_dir / (Path(source).stem + ".txt")).write_text(transcript)
        require(result.returncode == 0, "Lean elaboration failed: " + source + ": " + transcript[-2500:])
        actual.update(check(expected, transcript, source in EXACT_SOURCES))
    evidence = {
        "status": "actual-lean-axioms-audited", "theorems": len(actual),
        "sourceFiles": len(selected), "actualAxioms": actual,
        "allowedFoundations": sorted(ACTIVE.ALLOWED), "sources": pins,
        "head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
        "requireHead": args.require_head,
    }
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as exc:
        print("blob hash axiom check failed:", exc, file=sys.stderr)
        sys.exit(1)
