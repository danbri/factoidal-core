#!/usr/bin/env python3
"""Run finite model-preservation acceptance checks against the real OWL reader.

Builds the fixture's dependencies, checks its Lean model proofs and guards,
and requires every reported certificate check on these satisfiable inputs
to reject. This is finite QA, not a universal reader or public-API proof.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "formal/lean4"
FIXTURE = ROOT / "tests/assurance/OwlModelPreservation.lean"
PREFIX = "OWL_MODEL_PRESERVATION_REPORT="
CASE_IDS = {"annotation-domain", "generated-name-collision"}
DEPENDENCIES = [
    "L4Factoidal.OWL.CertifiedDecision",
    "L4Factoidal.OWL.RefuteCert",
    "L4Factoidal.OWL.RLClosureIndexed",
    "L4Factoidal.Syntax.NQuadsFast",
]


def run_phase(command, timeout):
    process = subprocess.Popen(
        command, cwd=LEAN_ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, start_new_session=True,
    )
    timed_out = False
    try:
        output, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
    return {"command": command, "cwd": str(LEAN_ROOT),
            "exit_code": process.returncode, "timed_out": timed_out,
            "output": output}


def parse_cases(output):
    lines = [line[len(PREFIX):] for line in output.splitlines()
             if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError("missing or duplicate executed case report")
    payload = json.loads(lines[0])
    if not isinstance(payload, dict) or set(payload) != {"cases"}:
        raise ValueError("invalid case report envelope")
    cases = payload["cases"]
    if not isinstance(cases, list) or len(cases) != len(CASE_IDS):
        raise ValueError("wrong or empty executed case inventory")
    if any(not isinstance(case, dict) for case in cases):
        raise ValueError("invalid case report")
    if {case.get("id") for case in cases} != CASE_IDS:
        raise ValueError("missing, duplicate or unknown case id")
    for case in cases:
        if case.get("expectedCheckCert") is not False:
            raise ValueError("expected rejection was removed or changed")
        if type(case.get("actualCheckCert")) is not bool:
            raise ValueError("missing or non-Boolean observed checker result")
    return cases


def check_model_proof_audits(output):
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for short in ["annotationIntended_model", "collisionIntended_model"]:
        name = "OwlModelPreservation." + short
        lines = [line for line in output.splitlines()
                 if line.startswith(f"'{name}' ") and "axioms" in line]
        if len(lines) != 1:
            raise ValueError(f"missing or duplicate model proof audit: {name}")
        if lines[0] == f"'{name}' does not depend on any axioms":
            continue
        prefix = f"'{name}' depends on axioms: ["
        if not lines[0].startswith(prefix) or not lines[0].endswith("]"):
            raise ValueError(f"unrecognized model proof audit: {name}")
        axioms = {a.strip() for a in lines[0][len(prefix):-1].split(",") if a.strip()}
        if axioms - allowed:
            raise ValueError(f"disallowed model proof axioms: {sorted(axioms - allowed)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--json", type=Path, required=True,
                        help="New report path; existing files are never overwritten")
    args = parser.parse_args()
    if args.json.exists():
        parser.error("report already exists; choose a new path")
    report = {
        "format": "owl-model-preservation-acceptance-v1",
        "time_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "two real-reader model-preservation cases; no universal or public-API assurance",
        "status": "error", "phases": [], "cases": [],
    }
    exit_code = 2
    try:
        lake = shutil.which(args.lake) if args.lake else None
        if not lake:
            raise ValueError("Lake executable missing; supply --lake")
        if not FIXTURE.is_file() or not FIXTURE.read_bytes():
            raise ValueError("model-preservation fixture missing or empty")
        sources = [FIXTURE, LEAN_ROOT / "lean-toolchain"] + [
            LEAN_ROOT / (name.replace(".", "/") + ".lean")
            for name in DEPENDENCIES
        ] + [LEAN_ROOT / "L4Factoidal/OWL/DirectCert.lean",
             LEAN_ROOT / "L4Factoidal/OWL/Tableau.lean"]
        report["source_hashes"] = {
            path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sources
        }
        report["hash_scope"] = "fixture and selected semantic inputs; not the full transitive build closure"
        build = run_phase([lake, "build", *DEPENDENCIES], 300)
        report["phases"].append(build)
        if build["timed_out"] or build["exit_code"] != 0:
            raise ValueError("dependency build failed or timed out")
        check = run_phase([lake, "env", "lean", str(FIXTURE)], 60)
        report["phases"].append(check)
        if check["timed_out"]:
            raise ValueError("model-preservation check timed out")
        cases = parse_cases(check["output"])
        report["cases"] = cases
        check_model_proof_audits(check["output"])
        report["model_proof_axiom_audits_passed"] = True
        bad = [case["id"] for case in cases if case["actualCheckCert"]]
        accepted = check["exit_code"] == 0 and not bad
        report["status"] = "pass" if accepted else "fail"
        report["failed_model_preservation_cases"] = bad
        report["lean_checks_passed"] = check["exit_code"] == 0
        exit_code = 0 if accepted else 1
    except (OSError, ValueError, TypeError) as error:
        report["error"] = str(error)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    with args.json.open("x", encoding="utf-8") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(f"OWL model-preservation acceptance: {report['status']}")
    for case in report["cases"]:
        print(f"  {case['id']}: checkCert={case['actualCheckCert']}; expected False")
    if "error" in report:
        print(report["error"], file=sys.stderr)
    print(f"Evidence: {args.json}")
    print("Finite reader/preprocessing QA; not a universal proof or a public API certification.")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
