#!/usr/bin/env python3
"""Check real OWL reader contracts, adversarial cases and proof mutation controls.

This source gate does not certify the old reader, public wire adapters or npm.
Mutations must fail inside the named proof, not merely at a finite test,
syntax error or missing dependency. Raw output is preserved in a new report.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "formal/lean4"
FIXTURE = ROOT / "tests/assurance/AtomicDirectAcceptance.lean"
WITNESSES = ROOT / "tests/assurance/AtomicDirect.lean"
NAMES = LEAN_ROOT / "L4Factoidal/OWL/CertNames.lean"
ATOMIC = LEAN_ROOT / "L4Factoidal/OWL/AtomicDirect.lean"
PREFIX = "ATOMIC_DIRECT_ACCEPTANCE="
CASE_IDS = {
    "empty", "annotation-domain", "annotation-declaration-last", "annotation-range",
    "annotation-blank-value", "builtin-comment", "builtin-label", "builtin-version-info",
    "empty-named-class", "generated-prefix-user-class", "data-prefix-user-class",
    "empty-class-with-member", "bottom-membership", "top-subclass-bottom",
    "same-and-different", "same-only", "different-only", "self-different",
    "class-individual-punning", "annotation-and-real-contradiction", "duplicate-statements",
    "ontology-header", "blank-ontology-header", "named-individual-declaration",
    "unsupported-object-property", "unsupported-undeclared-predicate", "unsupported-import",
    "unsupported-restriction", "forbidden-logical-predicate-annotation", "mixed-property-roles",
    "sameas-does-not-merge-classes", "unsupported-builtin-seeAlso", "unsupported-builtin-isDefinedBy",
    "unsupported-builtin-deprecated", "unsupported-builtin-priorVersion",
    "unsupported-builtin-backwardCompatibleWith", "unsupported-builtin-incompatibleWith",
    "unsupported-reserved-individual-declaration", "unsupported-reserved-individual-assertion",
    "unsupported-reserved-individual-same", "unsupported-reserved-individual-different",
    "unsupported-triple-among-annotations", "unsupported-directional-annotation",
    "unsupported-triple-term-annotation", "multiple-headers-fragment-admission",
    "object-property-declaration", "some-values-from-cyclic", "some-values-from-assertion",
    "some-values-from-typed-restriction", "some-values-from-witness-clash",
    "some-values-from-nothing-filler", "unsupported-restriction-two-properties",
    "unsupported-restriction-no-filler", "unsupported-annotation-property-restriction",
}
UNSUPPORTED_IDS = {
    "unsupported-object-property", "unsupported-undeclared-predicate", "unsupported-import",
    "unsupported-restriction", "forbidden-logical-predicate-annotation", "mixed-property-roles",
    "unsupported-builtin-seeAlso", "unsupported-builtin-isDefinedBy", "unsupported-builtin-deprecated",
    "unsupported-builtin-priorVersion", "unsupported-builtin-backwardCompatibleWith",
    "unsupported-builtin-incompatibleWith", "unsupported-reserved-individual-declaration",
    "unsupported-reserved-individual-assertion", "unsupported-reserved-individual-same",
    "unsupported-reserved-individual-different", "unsupported-triple-among-annotations",
    "unsupported-directional-annotation", "unsupported-triple-term-annotation",
    "unsupported-restriction-two-properties", "unsupported-restriction-no-filler",
    "unsupported-annotation-property-restriction",
}
INCONSISTENT_IDS = {
    "empty-class-with-member", "bottom-membership", "top-subclass-bottom", "same-and-different",
    "self-different", "annotation-and-real-contradiction", "duplicate-statements",
    "some-values-from-witness-clash", "some-values-from-nothing-filler",
}
AUDITS = ["AtomicDirect.readOntology_preserves_models", "AtomicDirect.readOntology_hasModel",
          "AtomicDirect.accepted_covers_triples",
          "AtomicDirect.decide_sound", "AtomicDirect.isAnnotation_sound",
          "AtomicDirect.addAxiom_preserves_model", "AtomicDirect.erase_sound",
          "AtomicDirect.definitive_admitted", "AtomicDirect.unsupported_is_unknown",
          "CertNames.decode_encode", "CertNames.encode_injective",
          "CertNames.source_ne_nominal", "CertNames.source_ne_dataMin", "CertNames.source_ne_dataMax",
          "CertNames.frame_eq_frameTR"]
WITNESS_AUDITS = ["AtomicDirectModels." + name for name in [
    "annotation_source_model", "collision_source_model", "annotation_ne_inconsistent",
    "collision_ne_inconsistent", "unsupported_source_model", "unsupported_read_none",
    "unsupported_not_admitted", "unsupported_no_definitive",
]]
MUTATIONS = [
    ("source-name-becomes-nominal", NAMES,
     '| .source s => ["source", s]', '| .source s => ["nominal", s]',
     "theorem decode_encode", "theorem encode_injective"),
    ("maximum-name-becomes-minimum", NAMES,
     '| .dataMax n p => ["dataMax", n.repr, p]', '| .dataMax n p => ["dataMin", n.repr, p]',
     "theorem decode_encode", "theorem encode_injective"),
    ("annotation-lookup-accepts-any-property", ATOMIC,
     "builtinAnnotation name || graph.any", "true || graph.any",
     "theorem isAnnotation_sound", "def annotationValue"),
    ("reverse-subclass-compilation", ATOMIC,
     "tbox := (compileClass left, compileClass right) :: ontology.tbox",
     "tbox := (compileClass right, compileClass left) :: ontology.tbox",
     "theorem addAxiom_preserves_model", "def initialOntology"),
    ("silently-drop-all-input-triples", ATOMIC,
     "  graph.attach.mapM (fun ⟨triple, member⟩ => do\n"
     "    let ⟨clause, mapped⟩ ← readTriple graph index triple\n"
     "    pure ⟨clause, triple, member, mapped⟩)",
     "  some []",
     "theorem accepted_covers_triples", "theorem readOntology_preserves_models"),
    ("existential-compiles-to-top", ATOMIC,
     "tbox := (compileClass left, .ex role (compileClass filler)) :: ontology.tbox",
     "tbox := (compileClass left, .top) :: ontology.tbox",
     "theorem addAxiom_preserves_model", "def initialOntology"),
    ("bypass-actual-certificate-check", ATOMIC,
     "if accepted : checkCert ontology certificate = true then", "if accepted : True then",
     "def checkedRefutation", "def erase"),
    ("report-inconsistency-as-consistency", ATOMIC,
     "| .inconsistent _ _ => ⟨some false, none⟩", "| .inconsistent _ _ => ⟨some true, none⟩",
     "theorem erase_sound", "def decide"),
]


def load_runner():
    spec = importlib.util.spec_from_file_location("owl_corpus_runner", ROOT / "tools/check-atomic-direct-corpus.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def audit_named_axioms(output, names):
    for name in names:
        lines = [line for line in output.splitlines() if line.startswith(f"'{name}' ") and "axioms" in line]
        if len(lines) != 1:
            raise ValueError("missing or duplicate axiom audit: " + name)
        if lines[0] == f"'{name}' does not depend on any axioms":
            continue
        prefix = f"'{name}' depends on axioms: ["
        if not lines[0].startswith(prefix) or not lines[0].endswith("]"):
            raise ValueError("unrecognized axiom report: " + name)
        axioms = {a.strip() for a in lines[0][len(prefix):-1].split(",") if a.strip()}
        if axioms - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError("unapproved axioms in " + name + ": " + str(axioms))


def audit_axioms(output):
    audit_named_axioms(output, ["L4Factoidal.OWL." + short for short in AUDITS])


def invalid_proof_failure(output):
    """Resource exhaustion and infrastructure failures do not refute a mutation."""
    return any(marker in output.lower() for marker in [
        "unknown module prefix", "does not exist", "unexpected token", "unknown constant",
        "unknown identifier", "maximum recursion depth", "maxrecdepth", "maxheartbeats",
        "maximum number of heartbeats", "deterministic timeout", "(deterministic) timeout",
        "out of memory", "stack overflow", "interrupted",
    ])


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON field: " + key)
        result[key] = value
    return result


def acceptance_cases(output):
    lines = [line[len(PREFIX):] for line in output.splitlines() if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError("missing or duplicate acceptance report")
    cases = json.loads(lines[0], object_pairs_hook=unique_object)
    if (not isinstance(cases, list) or len(cases) != len(CASE_IDS)
            or any(not isinstance(case, dict) for case in cases)
            or {case.get("id") for case in cases} != CASE_IDS):
        raise ValueError("missing, duplicate, or unexpected acceptance cases")
    for case in cases:
        if set(case) != {"id", "expectedSupported", "expectedConsistent", "passed", "observed"}:
            raise ValueError("invalid acceptance case fields")
        if type(case["passed"]) is not bool:
            raise ValueError("missing acceptance result")
        expected = (case["expectedSupported"], case["expectedConsistent"])
        if type(expected[0]) is not bool or (expected[1] is not None and type(expected[1]) is not bool):
            raise ValueError("invalid expected acceptance values")
        # A supported input answers false when it is inconsistent and true
        # otherwise (a checked model, https://github.com/danbri/factoidal/issues/960).
        required = (case["id"] not in UNSUPPORTED_IDS,
                    False if case["id"] in INCONSISTENT_IDS else
                    None if case["id"] in UNSUPPORTED_IDS else True)
        if expected != required:
            raise ValueError("acceptance expectation weakened or changed: " + case["id"])
        observed = case.get("observed")
        if not isinstance(observed, dict) or set(observed) != {"supported", "consistent"}:
            raise ValueError("parse error or missing observed values")
        if type(observed["supported"]) is not bool or (observed["consistent"] is not None
                                                      and type(observed["consistent"]) is not bool):
            raise ValueError("invalid observed acceptance values")
        agrees = expected == (observed["supported"], observed["consistent"])
        if case["passed"] != agrees:
            raise ValueError("acceptance summary disagrees with observation")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    if args.json.exists():
        parser.error("report exists; choose a new path")
    report = {"format": "owl-reader-contracts-v1", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": "error", "phases": [], "mutations": [], "cases": [],
              "scope": "restricted source reader and generated-name contracts; no public API certification"}
    result = 2
    try:
        lake = shutil.which(args.lake) if args.lake else None
        if not lake:
            raise ValueError("Lake executable missing; supply --lake")
        runner = load_runner()
        files = [FIXTURE, WITNESSES, NAMES, ATOMIC, Path(__file__),
                 LEAN_ROOT / "L4Factoidal/OWL/DirectCert.lean"]
        report["source_hashes"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                   for path in files}
        report["hash_scope"] = "selected sources; not full transitive build closure"
        build = runner.run_phase([lake, "build", "L4Factoidal.OWL.AtomicDirect",
                                  "L4Factoidal.OWL.RefuteCertTests", "L4Factoidal.Syntax.NQuadsFast"], 300)
        report["phases"].append(build)
        if build["exit_code"] != 0 or build["timed_out"]:
            raise ValueError("dependency build failed or timed out")
        check = runner.run_phase([lake, "env", "lean", str(FIXTURE)], 60)
        report["phases"].append(check)
        if check["timed_out"]:
            raise ValueError("acceptance fixture timed out")
        report["cases"] = acceptance_cases(check["output"])
        audit_axioms(check["output"])
        if check["exit_code"] != 0 or not all(case["passed"] for case in report["cases"]):
            report["status"] = "fail"
            result = 1
        else:
            witnesses = runner.run_phase([lake, "env", "lean", str(WITNESSES)], 60)
            report["phases"].append(witnesses)
            if witnesses["exit_code"] != 0 or witnesses["timed_out"]:
                raise ValueError("independent source-model witnesses failed or timed out")
            audit_named_axioms(witnesses["output"], WITNESS_AUDITS)
            report["source_model_witnesses_passed"] = True
            for name, source, anchor, replacement, proof_start, proof_end in MUTATIONS:
                text = source.read_text()
                if text.count(anchor) != 1 or text.count(proof_start) != 1 or text.count(proof_end) != 1:
                    raise ValueError("mutation anchor missing/ambiguous: " + name)
                changed = text.replace(anchor, replacement)
                first = changed[:changed.index(proof_start)].count("\n") + 1
                last = changed[:changed.index(proof_end)].count("\n") + 1
                with tempfile.TemporaryDirectory(prefix="owl-reader-mutation-") as tmp:
                    target = Path(tmp) / source.name
                    target.write_text(changed)
                    phase = runner.run_phase([lake, "env", "lean", str(target)], 60)
                    errors = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", phase["output"])
                proof_failed = any(first <= int(line) < last for line in errors)
                infrastructure_error = invalid_proof_failure(phase["output"])
                rejected = (phase["exit_code"] != 0 and not phase["timed_out"]
                            and proof_failed and not infrastructure_error)
                report["mutations"].append({"name": name, "source": str(source.relative_to(ROOT)),
                                             "proof_lines": [first, last], "rejected_by_proof": rejected,
                                             "changed_sha256": hashlib.sha256(changed.encode()).hexdigest(),
                                             "phase": phase})
                if not rejected:
                    raise ValueError("mutation was not rejected by its semantic proof: " + name)
            report["status"] = "pass"
            result = 0
    except (OSError, ValueError, TypeError) as error:
        report["error"] = str(error)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    with args.json.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print("OWL reader contracts: " + report["status"])
    print(f"{sum(c['passed'] for c in report['cases'])}/{len(report['cases'])} acceptance cases")
    print(f"{sum(m['rejected_by_proof'] for m in report['mutations'])}/{len(report['mutations'])} proof mutations rejected")
    if "error" in report:
        print(report["error"], file=sys.stderr)
    print(f"Evidence: {args.json}")
    return result


if __name__ == "__main__":
    sys.exit(main())
