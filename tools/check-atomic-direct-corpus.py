#!/usr/bin/env python3
"""Measure the proved atomic reader on unchanged W3C OWL RDF/XML inputs.

Select all Approved, DIRECT, DL consistency/inconsistency units in all.rdf.
No unsupported input, unknown answer, or missing serialization is a
conformance pass. Exit 0 means the run is complete and no wrong definitive
answer was observed; it does NOT mean conformance or decision completeness.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "formal/lean4"
HARNESS = ROOT / "tests/assurance/AtomicDirectCorpus.lean"
CATALOG = ROOT / "third_party/testing/owl/all.rdf"
TEST = "http://www.w3.org/2007/OWL/testOntology#"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
PREFIX = "ATOMIC_DIRECT_CASE="


def select_cases(catalog):
    cases = []
    root = ET.parse(catalog).getroot()
    for case in root.findall("{" + TEST + "}TestCase"):
        def resources(namespace, name):
            return {node.get("{" + RDF + "}resource")
                    for node in case.findall("{" + namespace + "}" + name)}
        if not (TEST + "Approved" in resources(TEST, "status")
                and TEST + "DIRECT" in resources(TEST, "semantics")
                and TEST + "DL" in resources(TEST, "species")):
            continue
        iri = case.get("{" + RDF + "}about")
        if not iri:
            raise ValueError("selected case has no original IRI")
        premise = case.find("{" + TEST + "}rdfXmlPremiseOntology")
        for kind in ["ConsistencyTest", "InconsistencyTest"]:
            if TEST + kind not in resources(RDF, "type"):
                continue
            input_text = premise.text if premise is not None else None
            cases.append({"id": iri + " [" + kind + "]", "iri": iri,
                          "kind": kind, "expectedConsistent": kind == "ConsistencyTest",
                          "input": input_text, "base": iri,
                          "input_sha256": hashlib.sha256(input_text.encode()).hexdigest()
                          if input_text is not None else None})
    ids = [case["id"] for case in cases]
    if not ids or len(ids) != len(set(ids)):
        raise ValueError("empty or duplicate selected case inventory")
    if not any(case["input"] is not None for case in cases):
        raise ValueError("no executable RDF/XML inputs")
    return cases


def run_phase(command, seconds):
    process = subprocess.Popen(command, cwd=LEAN_ROOT, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               start_new_session=True)
    timed_out = False
    try:
        output, _ = process.communicate(timeout=seconds)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
    return {"command": command, "cwd": str(LEAN_ROOT), "exit_code": process.returncode,
            "timed_out": timed_out, "output": output}


def read_results(output, expected_ids):
    rows = [json.loads(line[len(PREFIX):]) for line in output.splitlines()
            if line.startswith(PREFIX)]
    if (len(rows) != len(expected_ids) or any(not isinstance(row, dict) for row in rows)
            or {row.get("id") for row in rows} != expected_ids):
        raise ValueError("missing, duplicate, or extra executed W3C cases")
    for row in rows:
        if row.get("status") not in {"supported", "unsupported", "parse-error"}:
            raise ValueError("invalid case status")
        if row["status"] != "parse-error":
            if "consistent" not in row or (row["consistent"] is not None
                                          and type(row["consistent"]) is not bool):
                raise ValueError("missing or invalid verdict")
            if row["status"] == "unsupported" and row["consistent"] is not None:
                raise ValueError("unsupported input received a definitive verdict")
    return {row["id"]: row for row in rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--catalog", type=Path, default=CATALOG)
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    if args.json.exists():
        parser.error("report exists; choose a new path")
    report = {"format": "atomic-direct-w3c-measurement-v1", "status": "error",
              "time_utc": datetime.now(timezone.utc).isoformat(), "cases": [], "phases": [],
              "selection": "Approved AND DIRECT AND DL; consistency/inconsistency units",
              "certificate": "Cert.close only; no search or RL preprocessing",
              "scope": "source reader/checker QA; neither npm validation nor full OWL conformance",
              "catalog": str(args.catalog),
              "catalog_source": "https://www.w3.org/2009/11/owl-test/all.rdf",
              "license": "W3C Document License; vendored inputs unchanged"}
    result = 2
    try:
        lake = shutil.which(args.lake) if args.lake else None
        if not lake:
            raise ValueError("Lake executable missing; supply --lake")
        cases = select_cases(args.catalog)
        report["catalog_sha256"] = hashlib.sha256(args.catalog.read_bytes()).hexdigest()
        sources = [HARNESS, Path(__file__), LEAN_ROOT / "lean-toolchain"] + [
            LEAN_ROOT / ("L4Factoidal/OWL/" + module + ".lean")
            for module in ["AtomicDirect", "CertifiedDecision", "DirectCert", "Tableau"]]
        report["source_hashes"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sources}
        report["hash_scope"] = "selected semantic sources; not full transitive build closure"
        build = run_phase([lake, "build", "L4Factoidal.OWL.AtomicDirect",
                           "L4Factoidal.Syntax.RdfXml"], 300)
        report["phases"].append(build)
        if build["exit_code"] != 0 or build["timed_out"]:
            raise ValueError("dependency build failed or timed out")
        runnable = [case for case in cases if case["input"] is not None]
        with tempfile.TemporaryDirectory(prefix="atomic-direct-w3c-") as tmp:
            input_path = Path(tmp) / "cases.jsonl"
            input_path.write_text("".join(json.dumps(case) + "\n" for case in runnable))
            phase = run_phase([lake, "env", "lean", "--run", str(HARNESS), str(input_path)], 180)
        report["phases"].append(phase)
        if phase["exit_code"] != 0 or phase["timed_out"]:
            raise ValueError("W3C harness failed or timed out; incomplete execution")
        rows = read_results(phase["output"], {case["id"] for case in runnable})
        counts = Counter()
        for case in cases:
            entry = {k: v for k, v in case.items() if k != "input"}
            if case["input"] is None:
                classification = "missing-rdfxml-serialization"
            else:
                observed = rows[case["id"]]
                entry["observed"] = observed
                if observed["status"] != "supported":
                    classification = observed["status"]
                elif observed["consistent"] is None:
                    classification = "supported-unknown"
                elif observed["consistent"] == case["expectedConsistent"]:
                    classification = "correct-definitive-verdict"
                else:
                    classification = "wrong-definitive-verdict"
            entry["classification"] = classification
            report["cases"].append(entry)
            counts[classification] += 1
        report["counts"] = {"selected": len(cases), "executed": len(runnable), **dict(counts)}
        bad = counts["wrong-definitive-verdict"] + counts["parse-error"]
        report["status"] = "fail" if bad else "complete-no-wrong-verdict-observed"
        result = 1 if bad else 0
    except (OSError, ValueError, TypeError, ET.ParseError) as error:
        report["error"] = str(error)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    with args.json.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(report["status"])
    print(json.dumps(report.get("counts", {}), sort_keys=True))
    if "error" in report:
        print(report["error"], file=sys.stderr)
    print(f"Evidence: {args.json}")
    print("Unknown and unsupported are not conformance passes.")
    return result


if __name__ == "__main__":
    sys.exit(main())
