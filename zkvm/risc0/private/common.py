"""Strict byte I/O and process lifecycle for the private ASK host workflow.

RDF, policy semantics and private commitment hashing stay in native Lean/HACL.
SHA-256 here is used only to identify public software. No private input or salt
is hashed by this host module. Linux is the supported orchestration platform.
"""
from __future__ import annotations

import ctypes
import errno
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import selectors
import signal
import stat
import subprocess
import time

IMAGE = "0xc6d11ad4ba2b40d049bd3c117779816c73b3247d7bc50bb00e1c5c898618239b"
PARAMETERS = "0xe71e6620a834f4d8dc1998476b865a9a6437a14474f9442cf8664f9ec22a5eee"
GUEST_SOURCE = {
    "commit": "1bf9c1b430f7ddc3489d72991c82b01bd625600c",
    "tree": "985a6bd54f57da71530fc24f84b54bcd3e9f2192",
    "programSha256": "b62a0fbaf80f1660e75a9df2143c2ca540d7755db6481daf49e3d7eeb21cf56b",
    "buildManifestSha256": "6c943875c91d6bed1c5133849ceb4b408e95ccc85da2dc5fcd0bfc00f5eb0880",
}
PUBLIC_FILES = {"ask-proof.json", "public-provenance.json"}
HOST_SOURCES = {"workflowSource": "workflow.py", "commonSource": "common.py", "verifierSource": "verify.py"}


class Refusal(Exception):
    """Only fixed, non-input-derived codes may cross the console boundary."""


def require(condition: bool, code: str) -> None:
    if not condition:
        raise Refusal(code)


def object_keys(value: object, keys: set[str], code: str = "invalid-schema") -> dict:
    require(type(value) is dict and set(value) == keys, code)
    return value


def _pairs(items: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in items:
        require(key not in result, "duplicate-json-field")
        result[key] = value
    return result


def decode_json(data: bytes, maximum: int = 65536) -> dict:
    require(len(data) <= maximum, "json-size-limit")
    try:
        value = json.loads(data, object_pairs_hook=_pairs,
                           parse_constant=lambda _: (_ for _ in ()).throw(Refusal("invalid-json")))
    except (ValueError, UnicodeError, RecursionError):
        raise Refusal("invalid-json") from None
    require(type(value) is dict, "invalid-schema")
    return value


def encoded(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def read_bytes(path: Path, maximum: int, *, private: bool = False) -> bytes:
    # O_NOFOLLOW refuses file symlinks and O_NONBLOCK prevents a malicious FIFO
    # from blocking before its file type can be checked.
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as source:
        info = os.fstat(source.fileno())
        require(stat.S_ISREG(info.st_mode), "not-regular-file")
        require(info.st_size <= maximum, "file-size-limit")
        if private:
            require(info.st_uid == os.getuid() and info.st_mode & 0o077 == 0
                    and info.st_nlink == 1, "private-file-permissions")
        data = source.read(maximum + 1)
        require(len(data) <= maximum, "file-size-limit")
        return data


def write_new(path: Path, data: bytes, mode: int = 0o600) -> None:
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, mode)
    with os.fdopen(fd, "wb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())


def private_directory(path: Path) -> None:
    info = path.lstat()
    require(stat.S_ISDIR(info.st_mode) and info.st_uid == os.getuid()
            and info.st_mode & 0o077 == 0, "private-directory-permissions")


def digest_software(path: Path) -> str:
    """Public software identity only; never call on input, salt or witness."""
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as source:
        require(stat.S_ISREG(os.fstat(source.fileno()).st_mode), "invalid-tool")
        digest = hashlib.sha256()
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
        return digest.hexdigest()


def snapshot_software(source: Path, destination: Path, expected: str, executable: bool) -> None:
    """Hash the exact stream copied into a fresh private software snapshot."""
    require(re.fullmatch(r"[a-f0-9]{64}", expected) is not None, "invalid-tool-pin")
    src_fd = os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(src_fd, "rb") as src:
        info = os.fstat(src.fileno())
        require(stat.S_ISREG(info.st_mode) and info.st_size <= 512 * 1024**2, "invalid-tool")
        dst_fd = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o700 if executable else 0o600)
        with os.fdopen(dst_fd, "wb") as dst:
            digest = hashlib.sha256()
            total = 0
            for block in iter(lambda: src.read(1024 * 1024), b""):
                total += len(block)
                require(total <= 512 * 1024**2, "tool-size-limit")
                digest.update(block)
                dst.write(block)
            dst.flush()
            os.fsync(dst.fileno())
        require(digest.hexdigest() == expected, "tool-pin-mismatch")


def hex_bytes(value: object, count: int) -> bytes:
    require(type(value) is str and re.fullmatch("0x[a-f0-9]{" + str(count * 2) + "}", value)
            is not None, "invalid-hex")
    return bytes.fromhex(value[2:])


def load_policy(path: Path) -> dict:
    policy = decode_json(read_bytes(path, 32768))
    object_keys(policy, {"schema", "imageId", "policyHash", "contextHash", "requireTrue",
                         "expectedCommitment", "request"})
    require(policy["schema"] == "factoidal.ask.authorisation.v1", "invalid-policy-schema")
    require(policy["imageId"] == IMAGE, "unreviewed-guest-image")
    for key in ("imageId", "policyHash", "contextHash"):
        hex_bytes(policy[key], 32)
    require(policy["requireTrue"] is True, "unsupported-boolean-policy")
    if policy["expectedCommitment"] is not None:
        hex_bytes(policy["expectedCommitment"], 32)
    request = object_keys(policy["request"], {"query", "rules", "context", "regime"})
    require(request["regime"] in ("simple", "rdfs"), "unsupported-regime")
    for key in ("query", "rules", "context"):
        require(type(request[key]) is str, "invalid-request")
    require(len(request["query"].encode()) + len(request["rules"].encode()) <= 16384
            and len(request["context"].encode()) <= 4096, "request-size-limit")
    return policy


def journal_binding(journal: bytes, policy: dict, *, require_true: bool = False) -> bool:
    require(len(journal) == 128 and journal[96:127] == bytes(31)
            and journal[127] in (0, 1), "noncanonical-journal")
    require(journal[32:64] == hex_bytes(policy["policyHash"], 32), "policy-binding-mismatch")
    require(journal[64:96] == hex_bytes(policy["contextHash"], 32), "context-binding-mismatch")
    commitment = policy["expectedCommitment"]
    if commitment is not None:
        require(journal[:32] == hex_bytes(commitment, 32), "commitment-binding-mismatch")
    if require_true:
        require(journal[127] == 1, "true-policy-refusal")
    return journal[127] == 1


def public_proof(data: bytes, policy: dict) -> dict:
    proof = decode_json(data, 4096)
    object_keys(proof, {"schema", "sdk", "receiptKind", "imageId", "journal", "seal", "verifierParameters"})
    require(proof["schema"] == "factoidal.ask.evm.v1" and proof["sdk"] == "3.1.0"
            and proof["receiptKind"] == "groth16", "unsupported-proof-schema")
    require(proof["imageId"] == policy["imageId"], "image-binding-mismatch")
    require(proof["verifierParameters"] == PARAMETERS, "verifier-parameters-mismatch")
    journal_binding(hex_bytes(proof["journal"], 128), policy, require_true=True)
    require(hex_bytes(proof["seal"], 260)[:4] == bytes.fromhex(PARAMETERS[2:10]), "verifier-selector-mismatch")
    return proof


def provenance(policy: dict, software: dict[str, str]) -> dict:
    # Construct, never filter, public metadata. No private filenames, input/salt
    # hashes, witness lengths, diagnostic statistics or arbitrary source strings.
    object_keys(software, {"native", "host", "receiptTool", "r0vm", "program", "cpuRunner",
                           "cpuFetcher", "cpuPins", "python"} | set(HOST_SOURCES), "invalid-software-provenance")
    for value in software.values():
        require(type(value) is str and re.fullmatch(r"[a-f0-9]{64}", value) is not None,
                "invalid-software-provenance")
    return {"schema": "factoidal.ask.public-provenance.v1", "imageId": policy["imageId"],
            "policyHash": policy["policyHash"], "contextHash": policy["contextHash"],
            "requireTrue": True, "guestSource": dict(GUEST_SOURCE), "softwareSha256": software,
            "sdk": "3.1.0", "verifierParameters": PARAMETERS}


def check_provenance(data: bytes, policy: dict) -> dict:
    value = decode_json(data, 8192)
    object_keys(value, {"schema", "imageId", "policyHash", "contextHash", "requireTrue",
                        "guestSource", "softwareSha256", "sdk", "verifierParameters"})
    require(value == provenance(policy, value["softwareSha256"]), "invalid-public-provenance")
    return value


def validate_stage(stage: str) -> None:
    require(type(stage) is str and re.fullmatch(r"[a-z][a-z0-9-]*", stage) is not None,
            "invalid-stage-record")


def stage_record(work: Path, stage: str, status: str, code: int, elapsed: float) -> None:
    validate_stage(stage)
    require(status in ("ok", "failed", "timeout", "output-limit"), "invalid-stage-record")
    path = work / "stages.jsonl"
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    with os.fdopen(fd, "ab") as output:
        info = os.fstat(output.fileno())
        require(stat.S_ISREG(info.st_mode) and info.st_uid == os.getuid()
                and info.st_mode & 0o077 == 0 and info.st_nlink == 1 and info.st_size <= 1024**2,
                "private-file-permissions")
        output.write((json.dumps({"stage": stage, "status": status, "exitCode": code,
                                  "elapsedSeconds": round(elapsed, 3)}) + "\n").encode())


def run_child(command: list[str], work: Path, stage: str, *, capture: bool = False,
              timeout: int = 120, memory_gib: int = 3, jobs: int = 2) -> bytes:
    """Discard diagnostics, bound the one required JSON response, kill own process group on failure."""
    # Refuse a bad internal identifier before starting work, not after an
    # expensive successful child exits and its status must be recorded.
    validate_stage(stage)
    require("RISC0_DEV_MODE" not in os.environ, "development-mode-refused")
    require(1 <= jobs <= 8 and 1 <= memory_gib <= 8, "invalid-resource-limit")
    environment = {key: os.environ[key] for key in ("HOME", "PATH", "RISC0_HOME")
                   if key in os.environ}
    environment.update(RAYON_NUM_THREADS=str(jobs), RUST_LOG="error", RUST_BACKTRACE="0",
                       LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="16384",
                       FACTOIDAL_ZK_SEGMENT_PO2="19", PYTHONDONTWRITEBYTECODE="1",
                       TMPDIR=str(work / "tmp"))
    (work / "tmp").mkdir(mode=0o700, exist_ok=True)
    private_directory(work / "tmp")

    def limits() -> None:
        os.umask(0o077)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_STACK, (16 * 1024**2, 16 * 1024**2))
        cap = memory_gib * 1024**3
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    start = time.monotonic()
    try:
        child = subprocess.Popen(command, cwd=work, env=environment, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.PIPE if capture else subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL, start_new_session=True, preexec_fn=limits)
    except (OSError, subprocess.SubprocessError):
        stage_record(work, stage, "failed", -1, time.monotonic() - start)
        raise Refusal("child-start-failed") from None
    output = bytearray()
    status = "ok"
    selector = selectors.DefaultSelector()
    if capture:
        selector.register(child.stdout, selectors.EVENT_READ)
    try:
        while child.poll() is None or selector.get_map():
            if time.monotonic() - start > timeout:
                status = "timeout"
                raise Refusal("child-timeout")
            if capture:
                for key, _ in selector.select(0.1):
                    block = os.read(key.fd, 4096)
                    if block:
                        output.extend(block)
                        if len(output) > 16384:
                            status = "output-limit"
                            raise Refusal("child-output-limit")
                    else:
                        selector.unregister(key.fileobj)
            else:
                try:
                    child.wait(timeout=min(0.2, timeout))
                except subprocess.TimeoutExpired:
                    pass
        require(child.returncode == 0, "child-failed")
        return bytes(output)
    finally:
        # The direct child may already have exited while an owned descendant
        # holds a pipe open or continues running. Clean the session's process
        # group even then; never signal a process group created by another run.
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait()
        selector.close()
        if child.stdout is not None:
            child.stdout.close()
        if child.returncode != 0 and status == "ok":
            status = "failed"
        stage_record(work, stage, status, child.returncode, time.monotonic() - start)


def publish_noreplace(staging: Path, destination: Path) -> None:
    """Atomic same-filesystem publication; never replace an existing name."""
    require(staging.parent.stat().st_dev == destination.parent.stat().st_dev, "publication-filesystem-mismatch")
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        rename = libc.renameat2
    except AttributeError:
        raise Refusal("atomic-publication-unavailable") from None
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    if rename(-100, os.fsencode(staging), -100, os.fsencode(destination), 1) != 0:
        code = ctypes.get_errno()
        if code in (errno.EEXIST, errno.ENOTEMPTY):
            raise Refusal("public-destination-exists")
        raise Refusal("atomic-publication-failed")
