#!/usr/bin/env python3
"""Prepare, prove and publish a true ASK using the reviewed, unchanged guest.

All private input, salt, frames and receipts stay in the exclusive private work
directory. A false ASK is classified only after native/executor agreement.
The public output is a two-file package accepted by the independent verifier.
Tracking: https://github.com/danbri/factoidal-core/issues/801
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import re
import shutil
import stat
import sys
import tempfile

from common import (GUEST_SOURCE, HOST_SOURCES, Refusal, decode_json, digest_software, encoded, hex_bytes,
                    journal_binding, load_policy, object_keys, private_directory, provenance,
                    public_proof, publish_noreplace, read_bytes, require, run_child,
                    snapshot_software, write_new)
from verify import Parser, verify_package

SOFTWARE_NAMES = {"native": "native", "host": "host", "receiptTool": "receipt-tool",
                  "r0vm": "r0vm", "program": "program.bin", "cpuRunner": "run_cpu_prover.py",
                  "cpuFetcher": "fetch_cpu_prover.py", "cpuPins": "cpu-prover-pins.json"}
TEXT_FILES = {"query": "query.rq", "rules": "rules.srl", "context": "context.bin"}


def fresh_path(path: Path) -> Path:
    require(path.name not in ("", ".", ".."), "invalid-destination")
    destination = path.parent.resolve(strict=True) / path.name
    require(not os.path.lexists(destination), "destination-exists")
    return destination


def reserve(work: Path) -> None:
    require(shutil.disk_usage(work).free >= 5 * 1024**3, "insufficient-disk-reserve")


def install_tools(config_path: Path, work: Path) -> tuple[dict, dict]:
    config = decode_json(read_bytes(config_path, 16384))
    object_keys(config, set(SOFTWARE_NAMES) | {"schema", "cpuInstall"})
    require(config["schema"] == "factoidal.ask.private-tools.v1", "invalid-tools-schema")
    require(type(config["cpuInstall"]) is str and Path(config["cpuInstall"]).is_absolute(), "invalid-cpu-install")
    require(Path(config["cpuInstall"]).is_dir(), "invalid-cpu-install")
    software = work / "software"
    software.mkdir(mode=0o700)
    hashes = {}
    for key, name in SOFTWARE_NAMES.items():
        record = object_keys(config[key], {"path", "sha256"})
        require(type(record["path"]) is str and Path(record["path"]).is_absolute(), "invalid-tool-path")
        require(type(record["sha256"]) is str, "invalid-tool-pin")
        snapshot_software(Path(record["path"]), software / name, record["sha256"],
                          key in {"native", "host", "receiptTool", "r0vm"})
        hashes[key] = record["sha256"]
    require(hashes["program"] == GUEST_SOURCE["programSha256"], "unreviewed-program")
    # The interpreter and OS are trusted host prerequisites, not guest semantics.
    hashes["python"] = digest_software(Path(sys.executable).resolve(strict=True))
    for key, name in HOST_SOURCES.items():
        source = Path(__file__).with_name(name)
        hashes[key] = digest_software(source)
        snapshot_software(source, software / name, hashes[key], False)
    return config, hashes


def tool(work: Path, name: str) -> str:
    return str(work / "software" / SOFTWARE_NAMES[name])


def check_software(work: Path, hashes: dict) -> None:
    object_keys(hashes, set(SOFTWARE_NAMES) | set(HOST_SOURCES) | {"python"})
    for key, name in SOFTWARE_NAMES.items():
        require(digest_software(work / "software" / name) == hashes[key], "prepared-tool-changed")
    require(digest_software(Path(sys.executable).resolve(strict=True)) == hashes["python"], "python-changed")
    for key, name in HOST_SOURCES.items():
        require(digest_software(work / "software" / name) == hashes[key]
                and digest_software(Path(__file__).with_name(name)) == hashes[key], "workflow-source-changed")
    require(hashes["program"] == GUEST_SOURCE["programSha256"], "unreviewed-program")


def fresh_salt() -> bytes:
    # os.urandom delegates to the host OS CSPRNG. No time/process/counter fallback
    # and no deterministic seed option are provided by this private workflow.
    try:
        salt = os.urandom(32)
    except Exception:
        raise Refusal("entropy-unavailable") from None
    require(type(salt) is bytes and len(salt) == 32, "entropy-unavailable")
    return salt


@contextmanager
def work_lock(work: Path):
    private_directory(work)
    fd = os.open(work / "lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, "r+b") as lock:
        info = os.fstat(lock.fileno())
        require(stat.S_ISREG(info.st_mode) and info.st_uid == os.getuid()
                and info.st_mode & 0o077 == 0 and info.st_nlink == 1, "private-lock-permissions")
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise Refusal("private-work-busy") from None
        yield


def native_and_frame(work: Path, policy: dict, output: Path) -> tuple[bytes, Path]:
    output.mkdir(mode=0o700)
    inputs = work / "inputs"
    for name, maximum in [("input.nt", 65536), ("salt.bin", 32), ("query.rq", 16384),
                          ("rules.srl", 16384), ("context.bin", 4096)]:
        read_bytes(inputs / name, maximum, private=True)
    require(len(read_bytes(inputs / "salt.bin", 32, private=True)) == 32, "invalid-salt")
    for key, name in TEXT_FILES.items():
        require(read_bytes(inputs / name, 16384, private=True) == policy["request"][key].encode(),
                "prepared-policy-changed")
    journal_path = output / "journal.bin"
    paths = [str(inputs / name) for name in ("input.nt", "salt.bin", "query.rq", "rules.srl", "context.bin")]
    run_child([tool(work, "native"), *paths, policy["request"]["regime"], str(journal_path)], work, "native-evaluation")
    journal = read_bytes(journal_path, 128, private=True)
    journal_binding(journal, policy)
    frame = output / "frame.bin"
    regime = "0" if policy["request"]["regime"] == "simple" else "1"
    run_child([tool(work, "host"), "frame", regime, *paths, str(frame)], work, "witness-framing")
    return journal, frame


def executor_check(work: Path, policy: dict, journal: bytes, frame: Path, journal_path: Path) -> bool:
    data = run_child([tool(work, "host"), "execute", tool(work, "r0vm"), tool(work, "program"),
                      str(frame), str(journal_path)], work, "guest-execution", capture=True, timeout=600)
    result = decode_json(data, 16384)
    object_keys(result, {"kind", "imageId", "satisfied", "userCycles", "segments", "seconds"})
    satisfied = journal_binding(journal, policy)
    require(result["kind"] == "execution-only" and result["imageId"] == policy["imageId"][2:]
            and result["satisfied"] is satisfied, "guest-native-mismatch")
    return satisfied


def prepare(policy_path: Path, tools_path: Path, input_path: Path, destination: Path) -> str:
    policy = load_policy(policy_path)
    work = fresh_path(destination)
    # Private data must never be placed under this tracked source checkout.
    repository = Path(__file__).resolve().parents[3]
    require(not work.is_relative_to(repository), "private-work-inside-repository")
    reserve(work.parent)
    work.mkdir(mode=0o700)
    with work_lock(work):
        inputs = work / "inputs"
        inputs.mkdir(mode=0o700)
        # Snapshot input once. Later prove/resume has no --input argument.
        write_new(inputs / "input.nt", read_bytes(input_path, 65536))
        write_new(inputs / "salt.bin", fresh_salt())
        for key, name in TEXT_FILES.items():
            write_new(inputs / name, policy["request"][key].encode())
        config, hashes = install_tools(tools_path, work)
        write_new(work / "policy.json", encoded(policy))
        journal, frame = native_and_frame(work, policy, work / "initial")
        satisfied = executor_check(work, policy, journal, frame, work / "initial/journal.bin")
        write_new(work / "prepared.json", encoded({"schema": "factoidal.ask.prepared.v1",
                   "satisfied": satisfied, "softwareSha256": hashes, "cpuInstall": config["cpuInstall"]}))
    return "prepared-true" if satisfied else "not-satisfied"


def read_prepared(work: Path, policy: dict) -> tuple[dict, bytes]:
    private_directory(work / "inputs")
    private_directory(work / "software")
    require(decode_json(read_bytes(work / "policy.json", 32768, private=True)) == policy, "prepared-policy-changed")
    state = decode_json(read_bytes(work / "prepared.json", 16384, private=True))
    object_keys(state, {"schema", "satisfied", "softwareSha256", "cpuInstall"})
    require(state["schema"] == "factoidal.ask.prepared.v1" and type(state["satisfied"]) is bool,
            "invalid-prepared-state")
    require(type(state["cpuInstall"]) is str and Path(state["cpuInstall"]).is_absolute(), "invalid-cpu-install")
    check_software(work, state["softwareSha256"])
    journal = read_bytes(work / "initial/journal.bin", 128, private=True)
    require(journal_binding(journal, policy) is state["satisfied"], "prepared-result-mismatch")
    return state, journal


def verify_receipt(work: Path, policy: dict, receipt: Path) -> None:
    read_bytes(receipt, 64 * 1024**2, private=True)
    run_child([tool(work, "host"), "verify", policy["imageId"][2:], str(receipt),
               str(work / "initial/journal.bin")], work, "receipt-verification")


def publish(work: Path, policy: dict, state: dict, receipt: Path, destination: Path) -> None:
    destination = fresh_path(destination)
    require(not destination.is_relative_to(work), "public-output-inside-private-work")
    staging = Path(tempfile.mkdtemp(prefix=".ask-public-", dir=destination.parent))
    try:
        run_child([tool(work, "receiptTool"), "export", policy["imageId"], str(receipt),
                   str(work / "initial/journal.bin"), str(staging / "ask-proof.json")], work, "public-export")
        # Re-encode only the strict schema; never copy private metadata.
        proof = public_proof(read_bytes(staging / "ask-proof.json", 4096), policy)
        write_new(staging / "public-provenance.json", encoded(provenance(policy, state["softwareSha256"])))
        verify_package(staging, policy, Path(tool(work, "receiptTool")), state["softwareSha256"]["receiptTool"])
        require(hex_bytes(proof["journal"], 128) == read_bytes(work / "initial/journal.bin", 128, private=True),
                "export-journal-mismatch")
        publish_noreplace(staging, destination)
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def prove(policy_path: Path, directory: Path, destination: Path) -> str:
    policy = load_policy(policy_path)
    # Preserve lstat's refusal of a symlink naming the private root.
    private_directory(directory)
    work = directory.resolve(strict=True)
    fresh_path(destination)
    with work_lock(work):
        state, expected = read_prepared(work, policy)
        reserve(work)
        attempt = Path(tempfile.mkdtemp(prefix="attempt-", dir=work))
        # Native/HACL binds the exact saved input and salt again. No private
        # hashes in Python, and no reopening the original input path on resume.
        journal, frame = native_and_frame(work, policy, attempt / "native")
        require(journal == expected, "prepared-witness-changed")
        require(read_bytes(frame, 102453, private=True)
                == read_bytes(work / "initial/frame.bin", 102453, private=True), "prepared-frame-changed")
        satisfied = executor_check(work, policy, journal, frame, attempt / "native/journal.bin")
        if not satisfied:
            return "not-satisfied"
        composite = work / "composite.receipt"
        if not os.path.lexists(composite):
            pending = attempt / "composite.receipt"
            run_child([tool(work, "host"), "prove", tool(work, "r0vm"), tool(work, "program"),
                       str(frame), str(work / "initial/journal.bin"), str(pending)], work, "composite-proving",
                      timeout=10800, memory_gib=8, jobs=8)
            verify_receipt(work, policy, pending)
            publish_noreplace(pending, composite)
            print("checkpoint:verified-composite", flush=True)
        verify_receipt(work, policy, composite)
        groth16 = work / "groth16.receipt"
        if not os.path.lexists(groth16):
            source = composite
            # An ordinary succinct checkpoint is independently verified before
            # reuse. Rebuild identity input in a fresh attempt directory rather
            # than trust an old input.json or witness after an interrupted run.
            for checkpoint in sorted(work.glob("attempt-*/sdk/succinct.receipt")):
                try:
                    verify_receipt(work, policy, checkpoint)
                except (Refusal, OSError):
                    # A killed SDK write may leave a partial candidate. Preserve
                    # it, but use the independently verified composite instead
                    # of accepting or overwriting unverified checkpoint bytes.
                    print("checkpoint:ignored-unverified-succinct", flush=True)
                    continue
                source = checkpoint
                break
            sdk = attempt / "sdk"
            reserve(work)
            run_child([tool(work, "receiptTool"), "prepare", policy["imageId"], str(source),
                       str(work / "initial/journal.bin"), tool(work, "r0vm"), str(sdk)], work, "sdk-preparation",
                      timeout=10800, memory_gib=8, jobs=8)
            print("checkpoint:verified-succinct-and-identity", flush=True)
            reserve(work)
            run_child([sys.executable, "-B", tool(work, "cpuRunner"), "--install-dir", state["cpuInstall"],
                       "--work-dir", str(sdk), "--jobs", "8", "--max-memory-gib", "8",
                       "--timeout-seconds", "1800", "--redact-diagnostics"], work, "groth16-proving",
                      timeout=3900, memory_gib=8, jobs=8)
            pending = attempt / "groth16.receipt"
            run_child([tool(work, "receiptTool"), "finish", policy["imageId"], str(composite),
                       str(work / "initial/journal.bin"), str(sdk / "proof.json"), str(pending)],
                      work, "groth16-verification")
            verify_receipt(work, policy, pending)
            publish_noreplace(pending, groth16)
        verify_receipt(work, policy, groth16)
        publish(work, policy, state, groth16, destination)
    return "published-verified-true"


def main() -> None:
    os.umask(0o077)
    parser = Parser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True, parser_class=Parser)
    prep = commands.add_parser("prepare")
    prep.add_argument("--policy", required=True, type=Path)
    prep.add_argument("--tools", required=True, type=Path)
    prep.add_argument("--input", required=True, type=Path)
    prep.add_argument("--work-dir", required=True, type=Path)
    one = commands.add_parser("run")
    one.add_argument("--policy", required=True, type=Path)
    one.add_argument("--tools", required=True, type=Path)
    one.add_argument("--input", required=True, type=Path)
    one.add_argument("--work-dir", required=True, type=Path)
    one.add_argument("--public-dir", required=True, type=Path)
    proof = commands.add_parser("prove")
    proof.add_argument("--policy", required=True, type=Path)
    proof.add_argument("--work-dir", required=True, type=Path)
    proof.add_argument("--public-dir", required=True, type=Path)
    args = parser.parse_args()
    if args.action == "prepare":
        result = prepare(args.policy, args.tools, args.input, args.work_dir)
    elif args.action == "run":
        fresh_path(args.public_dir)
        result = prepare(args.policy, args.tools, args.input, args.work_dir)
        if result != "not-satisfied":
            result = prove(args.policy, args.work_dir, args.public_dir)
    else:
        result = prove(args.policy, args.work_dir, args.public_dir)
    print(result)
    if result == "not-satisfied":
        raise SystemExit(3)


if __name__ == "__main__":
    try:
        main()
    except Refusal as error:
        print("refused:" + str(error))
        raise SystemExit(2) from None
    except (Exception, KeyboardInterrupt):
        print("refused:operation-failed")
        raise SystemExit(2) from None
