#!/usr/bin/env python3
"""Cheap lifecycle/refusal tests. Process doubles here do not count as proofs."""
from __future__ import annotations

from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import common
import workflow
from verify import verify_package

ROOT = Path(__file__).resolve().parent


class PrivateWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ask-lifecycle-test-")
        self.work = Path(self.temp.name)
        self.policy = common.load_policy(ROOT / "authorisation.example.json")

    def tearDown(self):
        self.temp.cleanup()

    def test_entropy_failure_or_short_read_never_falls_back(self):
        for value in (b"", bytes(31), bytes(33), None):
            with patch("workflow.os.urandom", return_value=value):
                with self.assertRaisesRegex(common.Refusal, "^entropy-unavailable$"):
                    workflow.fresh_salt()
        with patch("workflow.os.urandom", side_effect=OSError("private diagnostic")):
            with self.assertRaisesRegex(common.Refusal, "^entropy-unavailable$"):
                workflow.fresh_salt()
        self.assertEqual(len(workflow.fresh_salt()), 32)

    def test_duplicate_and_unknown_policy_fields_refused(self):
        with self.assertRaises(common.Refusal):
            common.decode_json(b'{"a":1,"a":2}')
        for change in ({"extra": 1}, {"requireTrue": False}, {"expectedCommitment": "0x00"}):
            policy = {**self.policy, **change}
            path = self.work / "policy.json"
            path.write_bytes(common.encoded(policy))
            with self.assertRaises(common.Refusal):
                common.load_policy(path)

    def test_no_overwrite_of_existing_files_or_symlinks(self):
        file = self.work / "file"
        common.write_new(file, b"original")
        for path in (file, self.work / "alias"):
            if path != file:
                path.symlink_to(file)
            with self.assertRaises(FileExistsError):
                common.write_new(path, b"changed")
        self.assertEqual(file.read_bytes(), b"original")

    def test_private_reads_refuse_symlinks_hardlinks_and_exposed_modes(self):
        file = self.work / "file"
        common.write_new(file, b"input")
        self.assertEqual(common.read_bytes(file, 5, private=True), b"input")
        file.chmod(0o644)
        with self.assertRaises(common.Refusal):
            common.read_bytes(file, 5, private=True)
        file.chmod(0o600)
        alias = self.work / "alias"
        alias.symlink_to(file)
        with self.assertRaises(OSError):
            common.read_bytes(alias, 5, private=True)
        alias.unlink()
        os.link(file, alias)
        with self.assertRaises(common.Refusal):
            common.read_bytes(file, 5, private=True)

    def test_tools_are_private_verified_snapshots(self):
        public_tool = self.work / "public-tool"
        public_tool.write_bytes(b"public software bytes")
        snapshot = self.work / "snapshot"
        digest = hashlib.sha256(public_tool.read_bytes()).hexdigest()
        common.snapshot_software(public_tool, snapshot, digest, True)
        public_tool.write_bytes(b"changed source")
        self.assertEqual(snapshot.read_bytes(), b"public software bytes")
        self.assertEqual(stat.S_IMODE(snapshot.stat().st_mode), 0o700)
        with self.assertRaises(common.Refusal):
            common.snapshot_software(public_tool, self.work / "bad", digest, True)

    def test_publication_is_atomic_and_refuses_existing_names(self):
        for kind in ("directory", "symlink", "file"):
            with self.subTest(kind=kind):
                target = self.work / kind
                if kind == "directory":
                    target.mkdir()
                elif kind == "symlink":
                    target.symlink_to(self.work / "missing")
                else:
                    target.write_bytes(b"keep")
                staging = self.work / (kind + "-staging")
                staging.mkdir()
                with self.assertRaisesRegex(common.Refusal, "public-destination-exists"):
                    common.publish_noreplace(staging, target)
                self.assertTrue(staging.is_dir())
        staging = self.work / "valid-staging"
        staging.mkdir()
        (staging / "a").write_bytes(b"public")
        common.publish_noreplace(staging, self.work / "valid")
        self.assertFalse(staging.exists())
        self.assertEqual((self.work / "valid/a").read_bytes(), b"public")

    def test_child_diagnostics_and_exceptions_are_not_retained(self):
        marker = os.urandom(24).hex()
        script = "import sys;print(sys.argv[1]);print(sys.argv[1],file=sys.stderr);sys.exit(7)"
        console = io.StringIO()
        with redirect_stdout(console), self.assertRaisesRegex(common.Refusal, "^child-failed$"):
            common.run_child([sys.executable, "-c", script, marker], self.work, "injected-failure")
        recorded = b"".join(p.read_bytes() for p in self.work.iterdir() if p.is_file())
        self.assertTrue(marker.encode() not in recorded)
        self.assertTrue(marker not in console.getvalue())
        record = json.loads((self.work / "stages.jsonl").read_text())
        self.assertEqual(set(record), {"stage", "status", "exitCode", "elapsedSeconds"})
        self.assertEqual(record["exitCode"], 7)

    def test_captured_response_is_bounded(self):
        with self.assertRaisesRegex(common.Refusal, "^child-output-limit$"):
            common.run_child([sys.executable, "-c", "print('x'*20000)"], self.work,
                             "oversized-response", capture=True)
        self.assertLess((self.work / "stages.jsonl").stat().st_size, 1024)

    def test_real_groth16_stage_names_record_success_and_failure(self):
        marker = "private-child-diagnostic"
        script = "import sys;print(sys.argv[1]);print(sys.argv[1],file=sys.stderr);sys.exit(int(sys.argv[2]))"
        console = io.StringIO()
        expected = []
        for stage in ("groth16-proving", "groth16-verification"):
            for code in (0, 7):
                with self.subTest(stage=stage, code=code), redirect_stdout(console):
                    command = [sys.executable, "-c", script, marker, str(code)]
                    if code == 0:
                        self.assertEqual(common.run_child(command, self.work, stage), b"")
                    else:
                        with self.assertRaisesRegex(common.Refusal, "^child-failed$"):
                            common.run_child(command, self.work, stage)
                expected.append((stage, "ok" if code == 0 else "failed", code))
        data = (self.work / "stages.jsonl").read_text()
        records = [json.loads(line) for line in data.splitlines()]
        self.assertEqual([(r["stage"], r["status"], r["exitCode"]) for r in records], expected)
        self.assertNotIn(marker, data)
        self.assertNotIn(marker, console.getvalue())

    def test_invalid_stage_is_refused_before_starting_a_child(self):
        for stage in ("", "Groth16", "groth16 proving", "groth16\n", "../groth16", "16-proving", None):
            with self.subTest(stage=stage), patch("common.subprocess.Popen") as popen:
                with self.assertRaisesRegex(common.Refusal, "^invalid-stage-record$"):
                    common.run_child([sys.executable, "-c", "raise SystemExit(0)"], self.work, stage)
                popen.assert_not_called()
                with self.assertRaisesRegex(common.Refusal, "^invalid-stage-record$"):
                    common.stage_record(self.work, stage, "ok", 0, 0.0)
        self.assertFalse((self.work / "stages.jsonl").exists())
        self.assertFalse((self.work / "tmp").exists())

    def test_exited_wrapper_live_grandchild_is_cleaned_on_timeout(self):
        pidfile = self.work / "grandchild.pid"
        grandchild = "import os,time,pathlib;pathlib.Path('grandchild.pid').write_text(str(os.getpid()));time.sleep(30)"
        parent = "import subprocess,sys;subprocess.Popen([sys.executable,'-c',sys.argv[1]]);sys.exit(0)"
        with self.assertRaisesRegex(common.Refusal, "^child-timeout$"):
            common.run_child([sys.executable, "-c", parent, grandchild], self.work,
                             "exited-wrapper", capture=True, timeout=1)
        pid = int(pidfile.read_text())
        proc = Path(f"/proc/{pid}/stat")
        deadline = time.monotonic() + 2
        while proc.exists() and proc.read_text().split()[2] not in ("Z", "X") and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertTrue(not proc.exists() or proc.read_text().split()[2] in ("Z", "X"))

    def test_stage_fifo_does_not_block(self):
        os.mkfifo(self.work / "stages.jsonl", 0o600)
        start = time.monotonic()
        with self.assertRaises((OSError, common.Refusal)):
            common.stage_record(self.work, "test", "ok", 0, 0.0)
        self.assertLess(time.monotonic() - start, 1)

    def test_public_allowlist_is_structural(self):
        fixture = ROOT.parent / "evm/fixtures/ask-proof.json"
        proof = common.public_proof(fixture.read_bytes(), self.policy)
        software = {key: "0" * 64 for key in set(workflow.SOFTWARE_NAMES) | set(common.HOST_SOURCES) | {"python"}}
        provenance = common.provenance(self.policy, software)
        self.assertEqual(common.check_provenance(common.encoded(provenance), self.policy), provenance)
        for key in ("inputSha256", "saltSha256", "privatePath", "witnessLength", "diagnostics"):
            with self.assertRaises(common.Refusal):
                common.check_provenance(common.encoded({**provenance, key: "disallowed"}), self.policy)
        (self.work / "ask-proof.json").write_bytes(common.encoded(proof))
        (self.work / "public-provenance.json").write_bytes(common.encoded(provenance))
        (self.work / "witness.bin").write_bytes(b"private")
        with self.assertRaisesRegex(common.Refusal, "^public-file-allowlist$"):
            verify_package(self.work, self.policy, Path("missing-verifier"), "0" * 64)

    def test_false_is_distinct_from_an_invalid_journal_and_true_policy(self):
        proof = common.decode_json((ROOT.parent / "evm/fixtures/ask-proof.json").read_bytes())
        journal = bytearray(common.hex_bytes(proof["journal"], 128))
        journal[127] = 0
        self.assertFalse(common.journal_binding(bytes(journal), self.policy))
        with self.assertRaisesRegex(common.Refusal, "^true-policy-refusal$"):
            common.journal_binding(bytes(journal), self.policy, require_true=True)
        journal[127] = 2
        with self.assertRaisesRegex(common.Refusal, "^noncanonical-journal$"):
            common.journal_binding(bytes(journal), self.policy)

    def test_independent_commitment_is_optional_but_enforced_when_supplied(self):
        proof = common.decode_json((ROOT.parent / "evm/fixtures/ask-proof.json").read_bytes())
        common.public_proof(common.encoded(proof), self.policy)
        policy = {**self.policy, "expectedCommitment": "0x" + "00" * 32}
        with self.assertRaisesRegex(common.Refusal, "^commitment-binding-mismatch$"):
            common.public_proof(common.encoded(proof), policy)

    def test_stale_prepare_destination_is_refused_before_input_or_tools(self):
        with self.assertRaisesRegex(common.Refusal, "^destination-exists$"):
            workflow.prepare(ROOT / "authorisation.example.json", Path("missing-tools"),
                             Path("missing-input"), self.work)

    def test_entropy_failure_cannot_create_a_prepared_checkpoint(self):
        source = self.work / "input.nt"
        common.write_new(source, b"<urn:a> <urn:p> <urn:b> .")
        target = self.work / "new-private"
        with patch("workflow.reserve"), patch("workflow.os.urandom", side_effect=OSError("sensitive diagnostic")):
            with self.assertRaisesRegex(common.Refusal, "^entropy-unavailable$"):
                workflow.prepare(ROOT / "authorisation.example.json", Path("missing-tools"), source, target)
        self.assertFalse((target / "prepared.json").exists())
        self.assertFalse((target / "inputs/salt.bin").exists())


if __name__ == "__main__":
    unittest.main()
