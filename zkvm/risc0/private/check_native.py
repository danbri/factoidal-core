#!/usr/bin/env python3
"""Private synthetic native/executor controls; never run a prover.

Inputs, canaries, salts and journals are retained only beneath --work-dir.
The console reports aggregate checks, never witness bytes, hashes or lengths.
The example query/rules are public; the intermediate RDF node is generated
locally and never printed. This is execution evidence, not a ZK proof.
"""
from __future__ import annotations

import os
from pathlib import Path
import stat

from common import Refusal, decode_json, encoded, load_policy, read_bytes, require, write_new
from verify import Parser
import workflow


def refusal(action, code: str) -> None:
    try:
        action()
    except Refusal as error:
        require(str(error) == code, "unexpected-control-refusal")
    else:
        raise Refusal("control-not-refused")


def controls(policy_path: Path, tools_path: Path, directory: Path) -> int:
    policy = load_policy(policy_path)
    example = load_policy(Path(__file__).with_name("authorisation.example.json"))
    require(all(policy["request"][k] == example["request"][k] for k in ("query", "rules", "regime")),
            "control-needs-example-query")
    work = workflow.fresh_path(directory)
    workflow.reserve(work.parent)
    work.mkdir(mode=0o700)
    inputs = work / "source"
    inputs.mkdir(mode=0o700)
    # The CSPRNG produces test input independently of each prepare call's salt.
    marker = workflow.fresh_salt().hex()
    middle = "urn:private:" + marker
    source = inputs / "input.nt"
    true_input = f"<urn:a> <urn:p> <{middle}> .\n<{middle}> <urn:p> <urn:c> .\n".encode()
    write_new(source, true_input)
    true_work = work / "true"
    require(workflow.prepare(policy_path, tools_path, source, true_work) == "prepared-true", "true-control-failed")
    checks = 1
    for entry in true_work.rglob("*"):
        mode = entry.lstat().st_mode
        require((stat.S_ISDIR(mode) or stat.S_ISREG(mode)) and mode & 0o077 == 0, "private-mode-control-failed")
    checks += 1
    # A changed original file must not change resume's prepared snapshot.
    source.write_bytes(b"changed original; not the prepared witness")
    expected = read_bytes(true_work / "initial/journal.bin", 128, private=True)
    journal, frame = workflow.native_and_frame(true_work, policy, true_work / "resume-control")
    require(journal == expected, "source-snapshot-control-failed")
    require(workflow.executor_check(true_work, policy, journal, frame, true_work / "resume-control/journal.bin"),
            "resume-executor-control-failed")
    checks += 1
    # The saved salt/input is immutable in meaning: modifying either must change
    # the native/HACL journal, which prove compares with the saved one.
    salt = read_bytes(true_work / "inputs/salt.bin", 32, private=True)
    (true_work / "inputs/salt.bin").write_bytes(bytes([salt[0] ^ 1]) + salt[1:])
    changed, _ = workflow.native_and_frame(true_work, policy, true_work / "changed-salt-control")
    require(changed != expected, "salt-binding-control-failed")
    (true_work / "inputs/salt.bin").write_bytes(salt)
    checks += 1
    wrong_policy = {**policy, "policyHash": "0x" + "00" * 32}
    refusal(lambda: workflow.native_and_frame(true_work, wrong_policy, true_work / "wrong-policy-control"),
            "policy-binding-mismatch")
    checks += 1
    wrong_context = {**policy, "contextHash": "0x" + "00" * 32}
    refusal(lambda: workflow.native_and_frame(true_work, wrong_context, true_work / "wrong-context-control"),
            "context-binding-mismatch")
    checks += 1
    refusal(lambda: workflow.prepare(policy_path, tools_path, source, true_work), "destination-exists")
    checks += 1
    source.write_bytes(true_input.replace(b"<urn:c>", b"<urn:d>"))
    false_work = work / "false"
    require(workflow.prepare(policy_path, tools_path, source, false_work) == "not-satisfied", "false-control-failed")
    require(workflow.prove(policy_path, false_work, work / "absent-public") == "not-satisfied", "false-resume-failed")
    require(not (false_work / "composite.receipt").exists() and not (work / "absent-public").exists(),
            "false-published-control-failed")
    checks += 1
    # A parser refusal can include private input in arbitrary child diagnostics;
    # this host never retains those bytes, even on failure.
    source.write_bytes(("<urn:a> <urn:p> \"" + marker).encode())
    malformed = work / "malformed"
    refusal(lambda: workflow.prepare(policy_path, tools_path, source, malformed), "child-failed")
    require(not (malformed / "prepared.json").exists(), "malformed-prepared-control-failed")
    checks += 1
    for record in work.rglob("stages.jsonl"):
        data = record.read_bytes()
        require(marker.encode() not in data and salt not in data, "diagnostic-privacy-control-failed")
        for line in data.splitlines():
            require(set(decode_json(line)) == {"stage", "status", "exitCode", "elapsedSeconds"},
                    "diagnostic-schema-control-failed")
    checks += 1
    write_new(work / "control-result.json", encoded({"schema": "factoidal.ask.private-controls.v1",
              "passed": checks, "proverStarted": False, "scope": "native-and-executor-only"}))
    return checks


def main() -> None:
    os.umask(0o077)
    parser = Parser(description=__doc__)
    parser.add_argument("--policy", required=True, type=Path)
    parser.add_argument("--tools", required=True, type=Path)
    parser.add_argument("--work-dir", required=True, type=Path)
    args = parser.parse_args()
    count = controls(args.policy, args.tools, args.work_dir)
    print(f"passed:{count}; scope:native-and-executor-only; prover-started:false")


if __name__ == "__main__":
    try:
        main()
    except Refusal as error:
        print("refused:" + str(error))
        raise SystemExit(2) from None
    except (Exception, KeyboardInterrupt):
        print("refused:operation-failed")
        raise SystemExit(2) from None
