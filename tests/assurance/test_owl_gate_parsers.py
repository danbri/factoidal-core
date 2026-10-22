"""Synthetic report-parser controls; these do not execute Lean or certify OWL.

Run from the repository root with:
    python3 -m unittest discover -s tests/assurance -p test_owl_gate_parsers.py -v
The real source gates must still run their fixtures, axiom audits and mutations.
"""

import copy
import importlib.util
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]


def load_tool(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "tools" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


READER = load_tool("check-owl-reader-contracts")
PUBLIC = load_tool("check-owl-public-boundary")


def reader_cases():
    cases = []
    for name in sorted(READER.CASE_IDS):
        supported = name not in READER.UNSUPPORTED_IDS
        consistent = False if name in READER.INCONSISTENT_IDS else None
        cases.append({"id": name, "expectedSupported": supported,
                      "expectedConsistent": consistent, "passed": True,
                      "observed": {"supported": supported, "consistent": consistent}})
    return cases


def public_cases():
    cases = []
    for name in sorted(PUBLIC.IDS):
        ok = name not in PUBLIC.ERROR_IDS
        consistent = False if name in PUBLIC.FALSE_IDS else None
        reason = ("unsupported-syntax" if name in PUBLIC.UNSUPPORTED_IDS else
                  "incomplete-search" if name not in PUBLIC.FALSE_IDS | PUBLIC.ERROR_IDS else "")
        raw = ({"ok": True, "consistent": consistent, "reason": reason} if ok else
               {"ok": False, "error": "synthetic refusal for " + name})
        dispatched = dict(raw)
        if not ok:
            dispatched["code"] = "reason.failed" if name == "parse-error" else "owl.unsupported-rdf12"
            if name != "parse-error":
                dispatched["spec"] = PUBLIC.OWL_RDF12_SPEC
        cases.append({"id": name, "input": "", "options": "{}", "expectedOk": ok,
                      "expectedConsistent": consistent, "expectedReasonPrefix": reason,
                      "passed": True, "adapterAgrees": True,
                      "response": json.dumps(raw), "dispatchResponse": json.dumps(dispatched)})
    return cases


def case_named(cases, name):
    return next(case for case in cases if case["id"] == name)


class ReportInventoryControls(unittest.TestCase):
    def parsers(self):
        return [(READER.acceptance_cases, READER.PREFIX, reader_cases()),
                (PUBLIC.read_cases, "OWL_PUBLIC_BOUNDARY=", public_cases())]

    def test_valid_synthetic_inventories(self):
        self.assertEqual(len(READER.CASE_IDS), 45)
        self.assertEqual(len(PUBLIC.IDS), 20)
        for parse, prefix, cases in self.parsers():
            with self.subTest(parser=parse.__name__):
                self.assertEqual(parse(prefix + json.dumps(cases)), cases)

    def test_zero_missing_duplicate_and_unknown_cases(self):
        for parse, prefix, cases in self.parsers():
            unknown = copy.deepcopy(cases)
            unknown[0]["id"] = "unknown-case"
            for broken in [[], cases[:-1], cases + [cases[0]], cases[:-1] + [cases[0]], unknown]:
                with self.subTest(parser=parse.__name__, ids=[case["id"] for case in broken]):
                    with self.assertRaises(ValueError):
                        parse(prefix + json.dumps(broken))

    def test_report_marker_must_appear_once(self):
        for parse, prefix, cases in self.parsers():
            line = prefix + json.dumps(cases)
            for output in ["", "irrelevant output", line + "\n" + line]:
                with self.subTest(parser=parse.__name__, output_length=len(output)):
                    with self.assertRaises(ValueError):
                        parse(output)

    def test_every_case_field_is_required_including_null(self):
        for parse, prefix, cases in self.parsers():
            for field in case_named(cases, "empty"):
                broken = copy.deepcopy(cases)
                del case_named(broken, "empty")[field]
                with self.subTest(parser=parse.__name__, field=field):
                    with self.assertRaises(ValueError):
                        parse(prefix + json.dumps(broken))

    def test_unexpected_case_field_rejected(self):
        for parse, prefix, cases in self.parsers():
            cases[0]["unexpected"] = "must not be silently ignored"
            with self.subTest(parser=parse.__name__):
                with self.assertRaises(ValueError):
                    parse(prefix + json.dumps(cases))

    def test_conflicting_duplicate_case_fields_rejected(self):
        for parse, prefix, cases in self.parsers():
            for field, earlier in [("passed", False), ("expectedConsistent", True)]:
                body = json.dumps(cases)
                anchor = json.dumps(field) + ": "
                body = body.replace(anchor, anchor + json.dumps(earlier) + ", " + anchor, 1)
                with self.subTest(parser=parse.__name__, field=field):
                    with self.assertRaises(ValueError):
                        parse(prefix + body)


class ReaderReportControls(unittest.TestCase):
    def parse(self, cases):
        return READER.acceptance_cases(READER.PREFIX + json.dumps(cases))

    def test_strict_boolean_fields(self):
        for field in ["expectedSupported", "expectedConsistent", "passed", "supported", "consistent"]:
            for value in [0, 1, "false", "true"]:
                cases = reader_cases()
                case = case_named(cases, "same-and-different")
                target = case["observed"] if field in {"supported", "consistent"} else case
                target[field] = value
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        self.parse(cases)

    def test_observed_fields_are_exact(self):
        for field in ["supported", "consistent", "extra"]:
            cases = reader_cases()
            observed = case_named(cases, "empty")["observed"]
            if field == "extra":
                observed[field] = None
            else:
                del observed[field]
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    self.parse(cases)

    def test_duplicate_observed_field_rejected(self):
        body = json.dumps(reader_cases()).replace('"supported": true',
                                                  '"supported": false, "supported": true', 1)
        with self.assertRaises(ValueError):
            READER.acceptance_cases(READER.PREFIX + body)

    def test_weakened_expectation_rejected(self):
        cases = reader_cases()
        case_named(cases, "same-and-different")["expectedConsistent"] = None
        with self.assertRaises(ValueError):
            self.parse(cases)

    def test_failed_observation_cannot_claim_pass(self):
        cases = reader_cases()
        case_named(cases, "same-and-different")["observed"]["consistent"] = None
        with self.assertRaises(ValueError):
            self.parse(cases)

    def test_honest_failure_remains_failed_for_gate(self):
        cases = reader_cases()
        case = case_named(cases, "same-and-different")
        case["observed"]["consistent"] = None
        case["passed"] = False
        self.assertFalse(all(case["passed"] for case in self.parse(cases)))


class PublicReportControls(unittest.TestCase):
    def parse(self, cases):
        return PUBLIC.read_cases("OWL_PUBLIC_BOUNDARY=" + json.dumps(cases))

    def test_strict_boolean_fields(self):
        for field in ["expectedOk", "expectedConsistent", "passed", "adapterAgrees"]:
            for value in [0, 1, "false", "true"]:
                cases = public_cases()
                case_named(cases, "same-different")[field] = value
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        self.parse(cases)

    def test_duplicate_raw_or_dispatch_response_key_rejected(self):
        for field in ["response", "dispatchResponse"]:
            cases = public_cases()
            case = case_named(cases, "same-different")
            case[field] = case[field].replace('"consistent": false',
                                              '"consistent": true, "consistent": false')
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    self.parse(cases)

    def test_raw_and_dispatch_boolean_types_are_strict(self):
        for response_field in ["response", "dispatchResponse"]:
            for key in ["ok", "consistent"]:
                cases = public_cases()
                case = case_named(cases, "same-different")
                response = json.loads(case[response_field])
                response[key] = 1 if key == "ok" else 0
                case[response_field] = json.dumps(response)
                with self.subTest(field=response_field, key=key):
                    with self.assertRaises(ValueError):
                        self.parse(cases)

    def test_dispatch_error_contract_is_checked(self):
        for name in ["parse-error", "rdf12-refusal"]:
            for field in ["code", "error", "spec"]:
                cases = public_cases()
                case = case_named(cases, name)
                dispatched = json.loads(case["dispatchResponse"])
                dispatched[field] = "unrelated runtime failure"
                case["dispatchResponse"] = json.dumps(dispatched)
                with self.subTest(name=name, field=field):
                    with self.assertRaises(ValueError):
                        self.parse(cases)

    def test_missing_raw_consistent_is_not_explicit_unknown(self):
        cases = public_cases()
        case = case_named(cases, "empty")
        case["response"] = json.dumps({"ok": True, "reason": "incomplete-search"})
        with self.assertRaises(ValueError):
            self.parse(cases)


class ProofEvidenceControls(unittest.TestCase):
    def test_resource_and_infrastructure_failures_are_not_proof_rejections(self):
        for diagnostic in ["unknown module prefix", "file does not exist", "unexpected token",
                           "unknown constant", "unknown identifier", "maximum recursion depth",
                           "maxRecDepth", "maxHeartbeats", "maximum number of heartbeats",
                           "deterministic timeout", "(deterministic) timeout", "out of memory",
                           "stack overflow", "interrupted"]:
            with self.subTest(diagnostic=diagnostic):
                self.assertTrue(READER.invalid_proof_failure("/tmp/Mutation.lean:42:1: error: " + diagnostic))
                self.assertTrue(READER.invalid_proof_failure(diagnostic.upper()))

    def test_ordinary_proof_failure_is_not_an_infrastructure_failure(self):
        self.assertFalse(READER.invalid_proof_failure("/tmp/Mutation.lean:42:1: error: unsolved goals"))

    def test_axiom_audit_rejects_unapproved_missing_and_duplicate_reports(self):
        name = "Synthetic.witness"
        good = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        READER.audit_named_axioms(good, [name])
        READER.audit_named_axioms(f"'{name}' does not depend on any axioms", [name])
        for output in ["", good + "\n" + good, good.replace("Quot.sound", "sorryAx"),
                       good.replace("Quot.sound", "Synthetic.unproved")]:
            with self.subTest(output=output):
                with self.assertRaises(ValueError):
                    READER.audit_named_axioms(output, [name])


if __name__ == "__main__":
    unittest.main()
