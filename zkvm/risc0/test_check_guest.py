"""Refusal tests for the guest execution gate; no guest or prover is run."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check-guest.py")
SPEC = importlib.util.spec_from_file_location("ask_guest_check", SCRIPT)
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
NATIVE = CHECK.native_checker()


class HostResultTests(unittest.TestCase):
    def setUp(self):
        self.journal = bytes(127) + b"\x01"
        self.result = {"kind": "execution-only", "imageId": "a" * 64, "satisfied": True,
                       "userCycles": 123, "segments": 1, "seconds": 0.125}

    def success(self, result=None, stdout=None):
        return CHECK.check_host(0, json.dumps(result or self.result).encode() if stdout is None else stdout,
                                b"", self.journal, None, None)

    def test_success_records_actual_execution_metrics(self):
        self.assertEqual(self.success(), self.result)

    def test_false_answer_is_successful_execution(self):
        self.result["satisfied"] = False
        value = CHECK.check_host(0, json.dumps(self.result).encode(), b"", bytes(128), None, None)
        self.assertFalse(value["satisfied"])

    def test_success_refuses_non_json_duplicate_fields_and_nonfinite_time(self):
        for stdout in (b"noise\n" + json.dumps(self.result).encode(), b"{}\n{}", b"[]",
                       b'{"kind":"execution-only","kind":"verified-composite"}', b'{"seconds":NaN}'):
            with self.subTest(stdout=stdout), self.assertRaises((RuntimeError, ValueError)):
                self.success(stdout=stdout)

    def test_success_refuses_missing_fields_wrong_kind_boolean_cycles_and_image(self):
        for field, value in (("kind", "verified-composite"), ("satisfied", False),
                             ("userCycles", True), ("userCycles", 0), ("userCycles", 67108865),
                             ("segments", 0), ("seconds", -1), ("imageId", "wrong")):
            result = dict(self.result, **{field: value})
            with self.subTest(field=field, value=value), self.assertRaises(RuntimeError):
                self.success(result=result)
        result = dict(self.result)
        del result["userCycles"]
        with self.assertRaises(RuntimeError):
            self.success(result=result)
        with self.assertRaises(RuntimeError):
            CHECK.check_host(0, json.dumps(self.result).encode(), b"", self.journal, None, "b" * 64)

    def test_refusal_requires_empty_stdout_exit_one_and_exact_category(self):
        diagnostic = b"Error: checked Lean computation refused: status 2\n"
        value = CHECK.check_host(1, b"", diagnostic, self.journal, CHECK.ADMISSION, None)
        self.assertEqual(value["category"], "lean-admission")
        self.assertIsNone(value["userCycles"])
        for code, stdout, stderr in ((0, b"", diagnostic), (-9, b"", diagnostic),
                                     (1, b"{}", diagnostic), (1, b"\n", diagnostic),
                                     (1, b"", b"unexpected runtime crash"),
                                     (1, b"", diagnostic.replace(b"status 2", b"status 20"))):
            with self.subTest(code=code, stdout=stdout, stderr=stderr), self.assertRaises(RuntimeError):
                CHECK.check_host(code, stdout, stderr, self.journal, CHECK.ADMISSION, None)


class NativeEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = {"commit": "a" * 40, "toolchain": NATIVE.TOOLCHAIN,
                       "sources": NATIVE.source_manifest(), "scope": "test byte fixtures"}
        self.result = dict(self.source, result="pass", nativeFileCases=24, nativeSelfTests=28,
                           checkedTheorems=NATIVE.REQUIRED_THEOREMS, nativeSha256="b" * 64)
        self.write_records()
        self.cases = self.root / "cases-test"
        self.cases.mkdir()
        # These are synthetic byte-record fixtures for the evidence validator.
        # Their Boolean labels are supplied, never calculated by an RDF evaluator.
        for name, expected in CHECK.NATIVE_CASES.items():
            directory = self.cases / name
            directory.mkdir()
            values = (name.encode(), b"s" * 32, b"query", b"rules", b"context")
            for field, value in zip(CHECK.FIELDS, values, strict=True):
                (directory / field).write_bytes(value)
            if type(expected) is bool:
                journal = NATIVE.expected_journal(*values, int(name == "rdfs-before-rules"), expected)
                (directory / "journal.bin").write_bytes(journal)
                (directory / "expected.hex").write_text(journal.hex() + "\n")
                (directory / "stdout.txt").write_text(f"satisfied={str(expected).lower()}\njournal={journal.hex()}\n")
                (directory / "stderr.txt").write_bytes(b"")
            else:
                (directory / "stdout.txt").write_bytes(b"")
                (directory / "stderr.txt").write_text(f"ASK attestation refused: status={expected}; no journal\n")

    def tearDown(self):
        self.temporary.cleanup()

    def write_records(self):
        (self.root / "source.json").write_text(json.dumps(self.source))
        (self.root / "result.json").write_text(json.dumps(self.result))

    def load(self):
        return CHECK.load_native(self.root, NATIVE)

    def test_complete_inventory_has_all_four_controls(self):
        _, _, cases = self.load()
        self.assertEqual(len(cases), 28)
        self.assertEqual([case["name"] for case in cases[-4:]],
                         ["trailing-frame", "truncated-field", "invalid-regime", "retained-triple-limit"])
        base = cases[0]["frame"]
        self.assertEqual(cases[-4]["frame"], base + b"x")
        self.assertEqual(cases[-3]["frame"], base[:-1])
        self.assertEqual(cases[-2]["frame"], b"\x02" + base[1:])
        retained = cases[-1]["frame"]
        size = int.from_bytes(retained[1:5], "little")
        self.assertEqual(retained[5:5 + size].count(b"\n"), 257)

    def test_nonpassing_or_incomplete_native_result_refused(self):
        for key, bad in (("result", "fail"), ("nativeFileCases", 23),
                         ("nativeSelfTests", 0), ("checkedTheorems", [])):
            old = self.result[key]
            self.result[key] = bad
            self.write_records()
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                self.load()
            self.result[key] = old

    def test_changed_or_omitted_source_hash_refused_even_if_both_records_agree(self):
        original = dict(self.source["sources"])
        for sources in ({}, {**original, next(iter(original)): "0" * 64}):
            self.source["sources"] = sources
            self.result["sources"] = sources
            self.write_records()
            with self.assertRaises(RuntimeError):
                self.load()

    def test_missing_or_extra_case_and_multiple_case_roots_refused(self):
        extra = self.cases / "unreviewed"
        extra.mkdir()
        with self.assertRaises(RuntimeError):
            self.load()
        extra.rmdir()
        (self.cases / "false").rename(self.root / "missing-case")
        with self.assertRaises(RuntimeError):
            self.load()
        (self.root / "missing-case").rename(self.cases / "false")
        (self.root / "cases-second").mkdir()
        with self.assertRaises(RuntimeError):
            self.load()

    def test_missing_success_journal_cannot_become_refusal(self):
        (self.cases / "true/journal.bin").unlink()
        with self.assertRaises(RuntimeError):
            self.load()

    def test_input_or_journal_tampering_refused(self):
        path = self.cases / "true/input.nt"
        original = path.read_bytes()
        path.write_bytes(original + b"changed")
        with self.assertRaises(RuntimeError):
            self.load()
        path.write_bytes(original)
        (self.cases / "true/expected.hex").write_text("0" * 256 + "\n")
        with self.assertRaises(RuntimeError):
            self.load()

    def test_refusal_stdout_or_journal_is_refused(self):
        path = self.cases / "short-salt/stdout.txt"
        path.write_bytes(b"false")
        with self.assertRaises(RuntimeError):
            self.load()
        path.write_bytes(b"")
        (path.parent / "journal.bin").write_bytes(bytes(128))
        with self.assertRaises(RuntimeError):
            self.load()

    def test_cli_refuses_existing_output_without_replacing_anything(self):
        marker = self.root / "marker"
        marker.write_text("keep")
        env = dict(os.environ)
        env.pop("RISC0_DEV_MODE", None)
        run = subprocess.run([sys.executable, str(SCRIPT), "--output-dir", str(self.root),
                              "--native-evidence", str(self.root), "--host-tool", "/missing",
                              "--r0vm", "/missing", "--program", "/missing"],
                             env=env, capture_output=True, timeout=10)
        self.assertEqual(run.returncode, 1)
        self.assertIn(b"output directory must be NEW", run.stderr)
        self.assertEqual(marker.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
