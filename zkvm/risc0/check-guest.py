#!/usr/bin/env python3
"""Check local ASK guest execution against existing native fixture evidence.

This runner frames bytes and checks host results. It has no RDF evaluator,
does not build a guest, and never generates or verifies a cryptographic proof.
"""

import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
FIELDS = ("input.nt", "salt.bin", "query.rq", "rules.srl", "context.bin")
# Keep the complete reviewed native inventory: a missing journal cannot turn
# a successful fixture into a refusal, and deleting a case cannot shrink a pass.
NATIVE_CASES = {
    "true": True, "false": False, "rdf-duplicates": True,
    "context-binding": True, "salt-binding": True, "rule-inference": True,
    "rule-base-retained": True, "rdfs-before-rules": True,
    "simple-no-rdfs": False, "blank-node-independent": True,
    "blank-node-groups": True, "invalid-data-utf8": 2,
    "invalid-query-utf8": 2, "invalid-rules-utf8": 2,
    "invalid-ntriples-tail": 2, "short-salt": 2,
    "oversized-input": 4, "oversized-policy": 4, "oversized-context": 4,
    "select-refused": 2, "service-refused": 2, "modifier-refused": 2,
    "blank-node-collision": 2, "blank-node-scope": 2,
}
ADMISSION = ("lean-admission", "checked Lean computation refused: status 2")
ALLOCATION = ("guest-allocation-limit", "input frame exceeds allocation limit")
SUCCESS_KEYS = {"kind", "imageId", "satisfied", "userCycles", "segments", "seconds"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_hash(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_file(path, limit=2 * 1024 * 1024):
    require(not path.is_symlink() and path.is_file(), f"not a regular file: {path}")
    require(path.stat().st_size <= limit, f"file exceeds evidence limit: {path}")
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    require(len(data) <= limit, f"file grew beyond evidence limit: {path}")
    return data


def json_object(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def invalid(value):
        raise RuntimeError(f"non-finite JSON value: {value}")

    result = json.loads(data.decode("utf-8"), object_pairs_hook=pairs, parse_constant=invalid)
    require(isinstance(result, dict), "expected a JSON object")
    return result


def native_checker():
    spec = importlib.util.spec_from_file_location("ask_native_check", ROOT / "tools/check-ask-attestation.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def frame(regime, values):
    return bytes([regime]) + b"".join(len(value).to_bytes(4, "little") + value for value in values)


def journal_boolean(journal):
    require(len(journal) == 128 and journal[96:127] == bytes(31)
            and journal[127] in (0, 1), "noncanonical native journal")
    return bool(journal[127])


def load_native(evidence, native):
    source = json_object(read_file(evidence / "source.json"))
    result = json_object(read_file(evidence / "result.json"))
    require(result.get("result") == "pass" and type(result.get("nativeFileCases")) is int
            and result["nativeFileCases"] == 24 and type(result.get("nativeSelfTests")) is int
            and result["nativeSelfTests"] == 28, "native gate did not pass the complete inventory")
    require(result.get("checkedTheorems") == native.REQUIRED_THEOREMS,
            "native theorem inventory differs from the current gate")
    require(re.fullmatch(r"[0-9a-f]{64}", result.get("nativeSha256", "")) is not None,
            "native executable hash is missing")
    require(re.fullmatch(r"[0-9a-f]{40}", source.get("commit", "")) is not None,
            "native source commit is missing")
    require(source.get("toolchain") == native.TOOLCHAIN, "native toolchain mismatch")
    require(all(result.get(key) == source.get(key) for key in ("commit", "toolchain", "sources", "scope")),
            "native result and source records disagree")
    current = native.source_manifest()  # Source/import walk only; does not start Lean or Lake.
    require(bool(current) and source.get("sources") == current,
            "native source hashes or complete source inventory differ from this checkout")
    roots = list(evidence.glob("cases-*"))
    require(len(roots) == 1 and roots[0].is_dir() and not roots[0].is_symlink(),
            "expected exactly one native cases directory")
    case_root = roots[0]
    require({p.name for p in case_root.iterdir()} == set(NATIVE_CASES),
            "native case inventory must contain exactly the 24 reviewed cases")
    cases = []
    for name, expected in NATIVE_CASES.items():
        directory = case_root / name
        require(directory.is_dir() and not directory.is_symlink(), f"invalid case directory: {name}")
        success = type(expected) is bool
        files = set(FIELDS) | {"stdout.txt", "stderr.txt"}
        if success:
            files |= {"journal.bin", "expected.hex"}
        require({p.name for p in directory.iterdir()} == files, f"unexpected or missing native files: {name}")
        values = [read_file(directory / field, 65537) for field in FIELDS]
        regime = int(name == "rdfs-before-rules")
        stdout = read_file(directory / "stdout.txt")
        stderr = read_file(directory / "stderr.txt")
        journal = None
        if success:
            journal = read_file(directory / "journal.bin", 128)
            require(journal_boolean(journal) is expected, f"wrong native Boolean: {name}")
            require(read_file(directory / "expected.hex", 257) == (journal.hex() + "\n").encode(),
                    f"native journal and independent oracle disagree: {name}")
            # Recheck public byte commitments only; the truth value is the fixed
            # native fixture expectation, not an RDF computation in Python.
            require(journal == native.expected_journal(*values, regime, expected),
                    f"native fixture bytes no longer match their journal: {name}")
            require(stdout == (f"satisfied={str(expected).lower()}\njournal={journal.hex()}\n").encode()
                    and not stderr, f"native successful output mismatch: {name}")
        else:
            require(not stdout and stderr == f"ASK attestation refused: status={expected}; no journal\n".encode(),
                    f"native refusal output mismatch: {name}")
        cases.append({"name": name, "frame": frame(regime, values), "journal": journal,
                      "refusal": None if success else ALLOCATION if expected == 4 else ADMISSION,
                      "inputs": {field: {"bytes": len(value), "sha256": digest(value)}
                                 for field, value in zip(FIELDS, values, strict=True)}})
    base = cases[0]
    controls = [
        ("trailing-frame", base["frame"] + b"x", ("trailing-frame", "trailing input bytes")),
        ("truncated-field", base["frame"][:-1], ("truncated-field", "truncated input field")),
        ("invalid-regime", b"\x02" + base["frame"][1:], ADMISSION),
    ]
    values = [read_file(case_root / "true" / field, 65537) for field in FIELDS]
    values[0] = b"".join(f"<urn:a{i}> <urn:p> <urn:b> .\n".encode() for i in range(257))
    controls.append(("retained-triple-limit", frame(0, values),
                     ("lean-limit", "checked Lean computation refused: status 4")))
    cases.extend({"name": name, "frame": data, "journal": None, "refusal": refusal,
                  "derivedFrom": "true"} for name, data, refusal in controls)
    return source, result, cases


def check_host(returncode, stdout, stderr, journal, refusal, image):
    if refusal is not None:
        category, diagnostic = refusal
        require(returncode == 1 and not stdout, "refusal must exit 1 with empty stdout")
        require(re.search(re.escape(diagnostic.encode()) + rb"(?![A-Za-z0-9_])", stderr) is not None,
                f"expected refusal category {category}: {diagnostic}")
        return {"kind": "refused", "category": category, "diagnostic": diagnostic,
                "imageId": None, "userCycles": None, "segments": None, "seconds": None}
    require(returncode == 0, "successful fixture exited unsuccessfully")
    result = json_object(stdout)
    require(set(result) == SUCCESS_KEYS and result["kind"] == "execution-only",
            "host success must be the execution-only JSON result")
    require(isinstance(result["imageId"], str) and re.fullmatch(r"[0-9a-f]{64}", result["imageId"]) is not None,
            "invalid image ID")
    require(image is None or result["imageId"] == image, "guest image changed between cases")
    require(type(result["satisfied"]) is bool and result["satisfied"] is journal_boolean(journal),
            "host Boolean differs from native journal")
    require(type(result["userCycles"]) is int and 0 < result["userCycles"] <= 64 * 1024 * 1024,
            "invalid user cycle count")
    require(type(result["segments"]) is int and result["segments"] > 0, "invalid segment count")
    require(type(result["seconds"]) in (int, float) and math.isfinite(result["seconds"])
            and result["seconds"] >= 0, "invalid execution time")
    return result


def write_private(path, data):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as stream:
        stream.write(data)


def save_report(output, report):
    with tempfile.NamedTemporaryFile(mode="w", dir=output, delete=False) as stream:
        json.dump(report, stream, indent=2, allow_nan=False)
        stream.write("\n")
        temporary = stream.name
    os.replace(temporary, output / "result.json")


def execute(command, directory, timeout):
    env = dict(os.environ, RAYON_NUM_THREADS="1", FACTOIDAL_ZK_SEGMENT_PO2="18")
    started = time.monotonic()
    with (directory / "stdout.log").open("xb") as stdout, (directory / "stderr.log").open("xb") as stderr:
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                   stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            returncode = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            # This process group belongs to this invocation, including its r0vm.
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise RuntimeError(f"guest execution exceeded {timeout} seconds") from None
    return returncode, read_file(directory / "stdout.log"), read_file(directory / "stderr.log"), time.monotonic() - started


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("host-tool", "r0vm", "program", "native-evidence", "output-dir"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=float, default=180)
    args = parser.parse_args()
    require(math.isfinite(args.timeout_seconds) and 0 < args.timeout_seconds <= 600, "timeout must be in (0, 600]")
    require("RISC0_DEV_MODE" not in os.environ, "unset RISC0_DEV_MODE; development mode is refused")
    output = args.output_dir.absolute()
    require(not output.exists() and not output.is_symlink(), "output directory must be NEW")
    evidence = args.native_evidence.resolve(strict=True)
    require(not output.resolve().is_relative_to(evidence), "output must be outside native evidence")
    tools = {name: getattr(args, name.replace("-", "_")).resolve(strict=True)
             for name in ("host-tool", "r0vm", "program")}
    for name, path in tools.items():
        require(path.is_file(), f"{name} is not a file")
        if name != "program":
            require(os.access(path, os.X_OK), f"{name} is not executable")
    require(tools["program"].stat().st_size <= 128 * 1024 * 1024, "packaged program exceeds host bound")
    output.mkdir(mode=0o700)
    report = {"kind": "execution-only", "result": "running", "expectedCases": 28,
              "scope": "Observed local guest/native execution parity and refusals; no cryptographic proof claim.",
              "cases": []}
    save_report(output, report)
    try:
        source, native, cases = load_native(evidence, native_checker())
        report.update(sourceCommit=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                      workingTreeDirty=bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
                      runnerSha256=file_hash(Path(__file__)), nativeSource=source,
                      nativeEvidence={"path": str(evidence), "nativeSha256": native["nativeSha256"],
                                      "sourceSha256": file_hash(evidence / "source.json"),
                                      "resultSha256": file_hash(evidence / "result.json")},
                      executables={name: {"path": str(path), "bytes": path.stat().st_size,
                                          "sha256": file_hash(path)} for name, path in tools.items()},
                      imageId=None)
        fallback_journal = cases[0]["journal"]
        for case in cases:
            directory = output / case["name"]
            directory.mkdir(mode=0o700)
            comparison = case["journal"] if case["journal"] is not None else fallback_journal
            write_private(directory / "private.frame", case["frame"])
            write_private(directory / "comparison.journal", comparison)
            record = {key: value for key, value in case.items() if key not in ("frame", "journal", "refusal")}
            record.update(result="running", frameSha256=digest(case["frame"]), frameBytes=len(case["frame"]),
                          journalSha256=digest(case["journal"]) if case["journal"] is not None else None,
                          comparisonJournalSha256=digest(comparison),
                          expectedCategory=case["refusal"][0] if case["refusal"] else "journal",
                          stdoutLog=str(directory / "stdout.log"), stderrLog=str(directory / "stderr.log"))
            report["cases"].append(record)
            save_report(output, report)
            command = [str(tools["host-tool"]), "execute", str(tools["r0vm"]), str(tools["program"]),
                       str(directory / "private.frame"), str(directory / "comparison.journal")]
            started = time.monotonic()
            try:
                code, stdout, stderr, _ = execute(command, directory, args.timeout_seconds)
            finally:
                record["wallSeconds"] = round(time.monotonic() - started, 6)
                for label in ("stdout", "stderr"):
                    path = directory / f"{label}.log"
                    if path.is_file():
                        record[label + "Sha256"] = file_hash(path)
            record["exit"] = code
            record.update(check_host(code, stdout, stderr, comparison, case["refusal"], report["imageId"]))
            if case["refusal"] is None:
                report["imageId"] = record["imageId"]
            record["result"] = "pass"
            save_report(output, report)
            print(json.dumps({"case": case["name"], "result": "pass", "wallSeconds": record["wallSeconds"]}), flush=True)
        require(all(file_hash(path) == report["executables"][name]["sha256"] for name, path in tools.items()),
                "host, executor or packaged program changed during the run")
        require(len(report["cases"]) == 28, "guest case inventory incomplete")
        report["result"] = "pass"
    except Exception as error:
        report.update(result="fail", error=str(error))
        if report["cases"] and report["cases"][-1]["result"] == "running":
            report["cases"][-1].update(result="fail", error=str(error))
        raise
    finally:
        save_report(output, report)
    print(json.dumps({"kind": "execution-only", "result": "pass", "cases": 28,
                      "imageId": report["imageId"], "report": str(output / "result.json")}), flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, TypeError, subprocess.SubprocessError) as error:
        print(f"ASK guest check failed: {error}", file=sys.stderr)
        sys.exit(1)
