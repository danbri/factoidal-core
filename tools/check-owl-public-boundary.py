#!/usr/bin/env python3
"""Check the actual OWL consistency producer, adapters and proof bypass controls.

This gate checks a restricted source implementation. It does not certify
owlEntails, complete OWL coverage, or an npm artifact. Unknown is not a
successful semantic decision. `true` needs a checked model and `false` a
checked refutation (https://github.com/danbri/factoidal/issues/960). Every
report path must be new.
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
LEAN = ROOT / "formal/lean4"
PUBLIC = LEAN / "Wasm/Ops/ReasonDl.lean"
JSON_SOURCE = LEAN / "Wasm/Ops/ReasonDlCertified.lean"
MODEL_SOURCE = LEAN / "L4Factoidal/OWL/AtomicModel.lean"
FIXTURE = ROOT / "tests/assurance/OwlPublicBoundary.lean"
IDS = {
    "empty", "annotation-domain", "annotation-plus-real-clash", "same-different",
    "same-chain", "top-below-bottom", "generated-looking-source-name", "class-individual-punning",
    "unsupported-equivalence-contradiction", "unsupported-import", "unsupported-negative-property",
    "named-contradiction-is-outside-default", "default-clash-with-named-data",
    "default-annotation-with-named-clash", "named-declaration-does-not-classify-default",
    "zero-search-fuel", "malformed-options", "rdf12-refusal", "named-rdf12-preflight", "parse-error",
    "cyclic-some-values-from", "cyclic-some-values-from-fuel-one", "some-values-from-witness-clash",
}
TRUE_IDS = {"empty", "annotation-domain", "generated-looking-source-name", "class-individual-punning",
            "named-contradiction-is-outside-default", "default-annotation-with-named-clash",
            "cyclic-some-values-from"}
BUDGET_IDS = {"cyclic-some-values-from-fuel-one"}
FALSE_IDS = {"some-values-from-witness-clash", "annotation-plus-real-clash", "same-different", "same-chain", "top-below-bottom",
             "default-clash-with-named-data", "zero-search-fuel", "malformed-options"}
ERROR_IDS = {"rdf12-refusal", "named-rdf12-preflight", "parse-error"}
UNSUPPORTED_IDS = {"unsupported-equivalence-contradiction", "unsupported-import",
                   "unsupported-negative-property", "named-declaration-does-not-classify-default"}
OWL_RDF12_SPEC = ("https://www.w3.org/TR/owl2-mapping-to-rdf/"
                  "#Mapping_from_RDF_Graphs_to_the_Structural_Specification")
AUDITS = ["L4Wasm.Ops." + name for name in [
    "owlConsistencyJson_sound", "owlIsConsistentParsed_certified", "owlIsConsistent_certified",
    "owlConsistencyJson_success_schema", "owlConsistencyJson_refusal_schema",
    "owlConsistencyJson_unique_fields", "owlEntailsJson_false_sound"]] + [
    "L4Factoidal.OWL.AtomicModel." + name for name in [
        "checkModel_sound", "checkCountermodel_sound", "decideFuel_sound", "entailsFuel_sound"]]
MUTATIONS = [
    ("invert-json-boolean", JSON_SOURCE, "| some answer => .bool answer",
     "| some answer => .bool (!answer)",
     "theorem owlConsistencyJson_sound", "theorem owlConsistencyJson_success_schema"),
    ("reason-over-named-graphs-instead", JSON_SOURCE,
     "let verdict := AtomicModel.decideFuel ds.default fuel",
     "let verdict := AtomicModel.decideFuel (ds.named.flatMap (fun graph => graph.graph)) fuel",
     "theorem owlConsistencyJson_sound", "theorem owlConsistencyJson_success_schema"),
    ("public-producer-bypasses-certified-json", PUBLIC,
     "  (owlConsistencyJson ds (owlRefuteFuelOfOpts optsJson)).toString",
     '  okWith [("consistent", .bool true)]',
     "theorem owlIsConsistentParsed_certified", "def owlIsConsistent (nq"),
    ("model-checker-skips-element-check", MODEL_SOURCE,
     "  elementsOk M && graph.all (tripleOk M)",
     "  graph.all (tripleOk M)",
     "theorem checkModel_sound", "theorem checkModel_satisfiable"),
    ("entailment-false-without-countermodel", PUBLIC,
     "    | none => owlEntailsLegacyJson dsP dsC fuel",
     '    | none => .object [("ok", .bool true), ("entailed", .bool false)]',
     "theorem owlEntailsJson_false_sound", "#print axioms owlEntailsLegacyJson_ne_false"),
]


def load_tool(name):
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), ROOT / "tools" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON field: " + key)
        result[key] = value
    return result


def read_cases(output):
    prefix = "OWL_PUBLIC_BOUNDARY="
    lines = [line[len(prefix):] for line in output.splitlines() if line.startswith(prefix)]
    if len(lines) != 1:
        raise ValueError("missing or duplicate executed report")
    cases = json.loads(lines[0], object_pairs_hook=unique_object)
    if (not isinstance(cases, list) or len(cases) != len(IDS)
            or any(not isinstance(case, dict) for case in cases)
            or {case.get("id") for case in cases} != IDS):
        raise ValueError("missing, duplicate, or unexpected public cases")
    for case in cases:
        if set(case) != {"id", "input", "options", "expectedOk", "expectedConsistent", "expectedReasonPrefix",
                         "passed", "response", "dispatchResponse", "adapterAgrees"}:
            raise ValueError("invalid public case fields")
        if not isinstance(case["input"], str) or not isinstance(case["options"], str):
            raise ValueError("invalid replay input/options")
        name = case["id"]
        expected_ok = name not in ERROR_IDS
        expected_verdict = (False if name in FALSE_IDS else True if name in TRUE_IDS else None)
        expected_reason = ("unsupported-syntax" if name in UNSUPPORTED_IDS else
                           "budget-out" if name in BUDGET_IDS else
                           "incomplete-search" if name not in FALSE_IDS | TRUE_IDS | ERROR_IDS else "")
        if (type(case.get("expectedOk")) is not bool or case["expectedOk"] != expected_ok
                or case.get("expectedConsistent") is not expected_verdict
                or case.get("expectedReasonPrefix") != expected_reason):
            raise ValueError("weakened or invalid expected result: " + name)
        if type(case.get("passed")) is not bool or type(case.get("adapterAgrees")) is not bool:
            raise ValueError("invalid case summary or adapter observation: " + name)
        if not isinstance(case["response"], str) or not isinstance(case["dispatchResponse"], str):
            raise ValueError("invalid raw or dispatch response: " + name)
        response = json.loads(case["response"], object_pairs_hook=unique_object)
        if not isinstance(response, dict):
            raise ValueError("public response is not an object: " + name)
        actual_ok = response.get("ok")
        positive = actual_ok is True and response.get("consistent") is True
        shape = (type(actual_ok) is bool and
                 (set(response) == ({"ok", "consistent"} if positive else {"ok", "consistent", "reason"})
                  if actual_ok else set(response) == {"ok", "error"}))
        if actual_ok:
            shape = (shape and (response["consistent"] is None or type(response["consistent"]) is bool)
                     and (positive or isinstance(response["reason"], str)))
        else:
            shape = shape and isinstance(response.get("error"), str) and bool(response["error"])
        dispatched = json.loads(case["dispatchResponse"], object_pairs_hook=unique_object)
        # Pin the current dispatch ABI independently of ErrorModel.attachCode.
        # Successful envelopes are unchanged. Raw OWL parse refusals currently
        # use reason.failed with no spec/position; the facade's preliminary
        # parser has its own structured parse error contract, tested on artifacts.
        if expected_ok:
            dispatch_agrees = (isinstance(dispatched, dict) and
                               set(dispatched) == set(response) and
                               dispatched.get("ok") is actual_ok and
                               dispatched.get("consistent") is response.get("consistent") and
                               (positive or isinstance(dispatched.get("reason"), str)) and
                               dispatched == response)
        else:
            expected_dispatch = {"ok": False, "error": response.get("error"),
                                 "code": "reason.failed" if name == "parse-error" else
                                         "owl.unsupported-rdf12"}
            if name != "parse-error":
                expected_dispatch["spec"] = OWL_RDF12_SPEC
            dispatch_agrees = (isinstance(dispatched, dict) and
                               type(dispatched.get("ok")) is bool and
                               dispatched == expected_dispatch)
        agrees = (shape and actual_ok is expected_ok and response.get("consistent") is expected_verdict
                  and (not expected_reason or response.get("reason", "").startswith(expected_reason))
                  and dispatch_agrees and case["adapterAgrees"])
        if case["passed"] != agrees:
            raise ValueError("case summary disagrees with observed response: " + name)
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    if args.json.exists():
        parser.error("report exists; choose a new path")
    report = {"format": "owl-public-boundary-v1", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": "error", "phases": [], "cases": [], "mutations": [],
              "scope": "restricted consistency producer; no entailment or npm artifact certification"}
    result = 2
    try:
        lake = shutil.which(args.lake) if args.lake else None
        if not lake:
            raise ValueError("Lake executable missing; supply --lake")
        runner = load_tool("check-atomic-direct-corpus")
        audit = load_tool("check-owl-reader-contracts")
        sources = [PUBLIC, JSON_SOURCE, FIXTURE, Path(__file__), LEAN / "Wasm/Dispatch.lean",
                   LEAN / "Wasm/Ops/ErrorModel.lean",
                   LEAN / "L4Factoidal/OWL/DirectCert.lean",
                   LEAN / "L4Factoidal/OWL/AtomicDirect.lean", MODEL_SOURCE]
        report["source_hashes"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sources}
        report["hash_scope"] = "selected sources; not full transitive build closure"
        phase = runner.run_phase([lake, "build", "Wasm.Dispatch"], 300)
        report["phases"].append(phase)
        if phase["exit_code"] != 0 or phase["timed_out"]:
            raise ValueError("public dependencies failed to build or timed out")
        phase = runner.run_phase([lake, "env", "lean", str(FIXTURE)], 90)
        report["phases"].append(phase)
        if phase["timed_out"]:
            raise ValueError("public fixture timed out")
        report["cases"] = read_cases(phase["output"])
        audit.audit_named_axioms(phase["output"], AUDITS)
        if phase["exit_code"] != 0 or not all(c["passed"] for c in report["cases"]):
            report["status"] = "fail"
            result = 1
        else:
            for name, source, anchor, replacement, start, end in MUTATIONS:
                text = source.read_text()
                if any(text.count(marker) != 1 for marker in [anchor, start, end]):
                    raise ValueError("missing or ambiguous mutation anchor: " + name)
                changed = text.replace(anchor, replacement)
                first = changed[:changed.index(start)].count("\n") + 1
                last = changed[:changed.index(end)].count("\n") + 1
                with tempfile.TemporaryDirectory(prefix="owl-public-mutation-") as tmp:
                    target = Path(tmp) / source.name
                    target.write_text(changed)
                    phase = runner.run_phase([lake, "env", "lean", str(target)], 90)
                    errors = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", phase["output"])
                rejected = (phase["exit_code"] != 0 and not phase["timed_out"]
                            and any(first <= int(line) < last for line in errors)
                            and not audit.invalid_proof_failure(phase["output"]))
                report["mutations"].append({"name": name, "source": str(source.relative_to(ROOT)),
                    "changed_sha256": hashlib.sha256(changed.encode()).hexdigest(),
                    "proof_lines": [first, last], "rejected_by_proof": rejected, "phase": phase})
                if not rejected:
                    raise ValueError("mutation not rejected by the relevant proof: " + name)
            report["status"] = "pass"
            result = 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        report["error"] = str(error)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    with args.json.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print("OWL public boundary: " + report["status"])
    print(f"{sum(c['passed'] for c in report['cases'])}/{len(report['cases'])} public cases")
    print(f"{sum(m['rejected_by_proof'] for m in report['mutations'])}/{len(report['mutations'])} proof mutations rejected")
    if "error" in report:
        print(report["error"], file=sys.stderr)
    print(f"Evidence: {args.json}")
    return result


if __name__ == "__main__":
    sys.exit(main())
