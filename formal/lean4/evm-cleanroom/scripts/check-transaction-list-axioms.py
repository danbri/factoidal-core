#!/usr/bin/env python3
"""Audit the exact ordered-list proof inventory and executable source closure.

This invokes Lean 4.33.1 for the selected production-connected list proofs,
checks exact actual axiom sets against the active ledger, and pins the native
codec, runner, tests and oracle transport. It is not signed-byte authentication,
Ethereum semantic refinement or complete block validation.
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

# This explicit list is checked against the active ledger and every actual
# printed theorem in the dedicated proof module. Dropping a ledger claim or
# changing a printed dependency cannot silently reduce the gate.
INVENTORY = {
    "EVMCleanroom/TransactionListProofs.lean": [
        "EVMCleanroom.TransactionList." + name for name in (
            "witnessWorld_fresh",
            "witnessWorld_fresh_warmth",
            "finish_cumulativeGasUsed",
            "settleFrame_cumulativeGasUsed",
            "runAdmitted_cumulativeGasUsed",
            "runWithBlobHashes_cumulativeGasUsed",
            "refreshWitness_projection",
            "refreshWitness_listed_storage",
            "refreshWitnesses_inventory",
            "refreshWitnesses_find",
            "refreshed_request_coverage",
            "refreshed_request_original",
            "countFits_iff",
            "preflight_bounded",
            "preflight_too_many",
            "preflight_aggregate_limit",
            "advance_observation_limit",
            "advance_exact",
            "advance_checked",
            "runEntry_cumulativeGasUsed",
            "loop_receipt_trace",
            "loop_order",
            "loop_accounting",
            "loop_entry_refused",
            "loop_advance_refused",
            "finish_checked",
            "run_accepted",
            "run_preflight_refused",
            "blob_position_refused",
        )
    ],
    "EVMCleanroom/TransactionTransportProofs.lean": [
        "EVMCleanroom.TransactionTransport." + name for name in (
            "structural_bounded", "step_bounded", "feed_error", "feed_bounded", "scan_bounded",
            "step_depth_limit", "step_number_limit", "step_exponent_limit", "step_exponent_exact",
            "step_quoted_escaped", "step_quoted_escape", "step_quoted_close", "step_quoted_literal",
            "parseWith_refused", "parseWith_checked", "parseJSON_scan_refused", "parseJSON_checked",
        )
    ],
}
EXACT_SOURCES = {
    "EVMCleanroom/TransactionListProofs.lean", "EVMCleanroom/TransactionTransportProofs.lean",
}
SOURCE_ROOTS = [
    "EVMCleanroom/TransactionListCLI.lean", "EVMCleanroom/TransactionListProofs.lean",
    "EVMCleanroom/TransactionListTests.lean",
    "EVMCleanroom/TransactionTransportProofs.lean", "EVMCleanroom/TransactionTransportTests.lean",
]
SUPPORT_SOURCES = {
    "EVMCleanroom.lean", "lakefile.toml", "lakefile-transaction-list.toml",
    "lean-toolchain", "lake-manifest.json", "scripts/check-transaction-list-axioms.py",
    "scripts/check-axiom-output.py", "scripts/check-transaction-list-transport.py",
    "scripts/check-transaction-json-guard.py",
    "scripts/fixtures/transaction-list-transport.json",
    "scripts/differential/transaction-list.mjs", "scripts/differential/transaction-cli-timing.mjs",
    "scripts/differential/geth-byte-oracle.mjs", "scripts/eels/package.json",
    "scripts/differential/package.json", "scripts/differential/package-lock.json",
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
        {"name": "EVMCleanroom.TransactionList.loop_accounting", "axioms_printed": ["propext", "Quot.sound"]},
        {"name": "EVMCleanroom.TransactionList.witnessWorld_fresh", "axioms_printed": []},
    ]
    good = "\n".join([
        "info: source.lean:1:0: 'EVMCleanroom.TransactionList.loop_accounting' "
        "depends on axioms: [propext,\n Quot.sound]",
        "'EVMCleanroom.TransactionList.witnessWorld_fresh' does not depend on any axioms",
    ])
    require(len(check(expected, good, True)) == 2, "wrapped positive control failed")
    corrupt = {
        "missing-theorem": good.split("\n'", 1)[0],
        "duplicate-wrapped-report": good + "\n" + good,
        "wrapped-sorryAx": good.replace("Quot.sound]", "sorryAx,\n Quot.sound]"),
        "wrapped-custom-axiom": good.replace("Quot.sound]", "EVMCleanroom.unproved,\n Quot.sound]"),
        "duplicate-axiom": good.replace("Quot.sound]", "Quot.sound, propext]"),
        "dropped-required-axiom": good.replace("propext,\n ", ""),
        "extra-theorem": good + "\n'EVMCleanroom.TransactionList.extra' does not depend on any axioms",
        "truncated-wrapped-list": good.replace("Quot.sound]", "Quot.sound"),
    }
    rejected = []
    for label, transcript in corrupt.items():
        try:
            check(expected, transcript, True)
        except ValueError:
            rejected.append(label)
    require(len(rejected) == len(corrupt), "adversarial transcript survived")
    sample = b"def checked : Nat := 1\n"
    pin = git_blob(sample)
    require(checked_blob("sample.lean", sample, {"sample.lean": pin}) == pin,
            "valid source pin rejected")
    try:
        checked_blob("sample.lean", sample + b"-- source drift\n", {"sample.lean": pin})
    except ValueError:
        rejected.append("changed-reviewed-source")
    require(len(rejected) == len(corrupt) + 1, "source drift survived")
    return {"status": "negative-controls-pass", "rejected": len(rejected),
            "controls": rejected, "wrappedPositiveAccepted": True, "sourceDriftRejected": True}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def git_blob(contents):
    return hashlib.sha1(b"blob " + str(len(contents)).encode() + b"\0" + contents).hexdigest()


def checked_blob(source, contents, reviewed):
    blob = git_blob(contents)
    require(reviewed.get(source) == blob, "unpinned or changed source: " + source)
    return blob


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
                if module == "Std" or module.startswith("Std.") or module in {
                        "Lean.Data.Json.Parser", "Lean.Data.Json.FromToJson.Basic"}:
                    continue
                require(module.startswith("EVMCleanroom."), "unapproved import: " + module)
                pending.append(module.replace(".", "/") + ".lean")
    pins = {}
    for source in sorted(paths):
        contents = (ROOT / source).read_bytes()
        blob = checked_blob(source, contents, manifest["source_blobs"])
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
        print("transaction-list axiom check failed:", exc, file=sys.stderr)
        sys.exit(1)
