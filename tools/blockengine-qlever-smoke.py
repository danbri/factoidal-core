#!/usr/bin/env python3
"""Bounded native QLever/Shardborough complete-answer differential smoke.

Accepts the exact generated subjects-N fixture/store from core-scale.py.
Installs nothing. Builds an isolated QLever index and stops its own server.
This is a correctness probe, not a latency or industry-parity benchmark.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import urllib.parse
import urllib.request

SPEC = importlib.util.spec_from_file_location(
    "repeat_driver", Path(__file__).with_name("blockengine-core-repeat.py"))
D = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(D)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qlever-index", required=True, type=Path)
    parser.add_argument("--qlever-server", required=True, type=Path)
    parser.add_argument("--fixture-dir", required=True, type=Path)
    parser.add_argument("--subjects", type=D.bounded_number(10, 10000), default=1000)
    parser.add_argument("--library-dir", type=Path,
                        help="Optional scratch dylib directory for native macOS packages")
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    fixture_dir = args.fixture_dir.resolve()
    fixture = fixture_dir / "fixture.ttl"
    collection = fixture_dir / "collection"
    directory = args.output_dir.resolve()
    index_binary, server_binary = args.qlever_index.resolve(), args.qlever_server.resolve()
    native = D.BIN / "l4block-id-v3-query"
    if any(not path.is_file() for path in (index_binary, server_binary, native)):
        parser.error("all three native binaries must exist")
    if not fixture.is_file() or fixture.read_bytes() != D.fixture_bytes(args.subjects):
        parser.error("fixture does not exactly match --subjects")
    if directory.exists() and any(directory.iterdir()):
        parser.error("output directory must be absent or empty")
    original_collection = D.collection_hashes(collection)
    directory.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    if args.library_dir:
        env["DYLD_LIBRARY_PATH"] = str(args.library_dir.resolve())
    report = {
        "scope": "Complete-answer correctness only. No performance claim; fresh Shardborough processes and a native QLever server are different process models.",
        "subjects": args.subjects, "triples": args.subjects * 3,
        "fixture_sha256": D.sha256(fixture), "collection_sha256": original_collection,
        "binary_sha256": {path.name: D.sha256(path) for path in (index_binary, server_binary, native)},
        "driver_sha256": D.sha256(Path(__file__)), "workloads": [], "all_checks_passed": False,
        "comparison": "Exact complete JSON answers, including ordered rows and RDF datatypes. Exclude only QLever's top-level meta extension. COUNT xsd:int is separately reported as a known exact-term difference, never coerced to xsd:integer.",
    }
    server = None

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    save()
    try:
        report["qlever_version"] = subprocess.check_output(
            [str(server_binary), "--version"], env=env, text=True, timeout=10).strip()
        command = [str(index_binary), "-i", str(directory / "db"), "-f", str(fixture),
                   "-F", "ttl", "-m", "256 MB"]
        report["index_command"] = command
        with (directory / "index.log").open("w") as log:
            subprocess.run(command, cwd=directory, env=env, stdout=log,
                           stderr=subprocess.STDOUT, timeout=120, check=True)
        with socket.socket() as available:
            available.bind(("127.0.0.1", 0))
            port = available.getsockname()[1]
        command = [str(server_binary), "-i", str(directory / "db"), "-p", str(port),
                   "-m", "1 GB", "-c", "0 B", "-k", "0",
                   "--no-metrics-log", "--no-resource-usage-log"]
        report["server_command"] = command
        # QLever 0.6.0 has no listen-address option. Its listener uses the
        # engine default; requests here go to loopback. Use generated data only.
        report["listener"] = "QLever default bind address, temporary port; requests use 127.0.0.1"
        with (directory / "server.log").open("w") as log:
            server = subprocess.Popen(command, cwd=directory, env=env, stdout=log,
                                      stderr=subprocess.STDOUT)
            deadline = time.monotonic() + 20
            while True:
                if server.poll() is not None or time.monotonic() >= deadline:
                    raise ValueError("QLever server failed to start within 20 seconds")
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=0.2):
                        break
                except OSError:
                    time.sleep(0.1)
            for workload in D.workloads(args.subjects):
                name, expected = workload["name"], workload["expected"]
                request = urllib.request.Request(
                    f"http://127.0.0.1:{port}/",
                    data=urllib.parse.urlencode({"query": workload["query"]}).encode(),
                    headers={"Accept": "application/sparql-results+json",
                             "Content-Type": "application/x-www-form-urlencoded"})
                with urllib.request.urlopen(request, timeout=30) as response:
                    raw = response.read(8 * 1024 * 1024 + 1)
                if len(raw) > 8 * 1024 * 1024:
                    raise ValueError("QLever answer exceeded 8 MiB")
                qlever_file = directory / f"{name}.qlever.json"
                qlever_file.write_bytes(raw)
                answer = json.loads(raw, object_pairs_hook=D.unique_keys,
                                    parse_constant=D.reject_constant)
                core_answer = {key: value for key, value in answer.items() if key != "meta"}
                equal = D.canonical(core_answer) == D.canonical(expected)
                sample = D.capture([str(native), str(collection), "--json", "--query", workload["query"]],
                                   directory, name, 30, 8 * 1024 * 1024,
                                   D.Budget(8 * 1024 * 1024, time.monotonic() + 30))
                if sample["failure"] or sample["exit_code"]:
                    raise ValueError(f"{name}: Shardborough failed")
                D.validate_results(Path(sample["stdout_file"]), expected, 1)
                row = {"name": name, "query": workload["query"],
                       "shardborough_exact_expected_answer": True,
                       "qlever_exact_expected_answer": equal,
                       "qlever_output_sha256": D.sha256(qlever_file),
                       "shardborough_output_sha256": sample["stdout_sha256"],
                       "ignored_extension_keys": ["meta"] if "meta" in answer else []}
                if not equal and name == "predicate-count":
                    alternate = json.loads(json.dumps(expected))
                    alternate["results"]["bindings"][0]["count"]["datatype"] = "http://www.w3.org/2001/XMLSchema#int"
                    row["known_count_datatype_difference"] = D.canonical(core_answer) == D.canonical(alternate)
                report["workloads"].append(row)
                save()
                if not equal and not row.get("known_count_datatype_difference"):
                    raise ValueError(f"{name}: unexpected QLever answer difference")
        if D.collection_hashes(collection) != original_collection:
            raise ValueError("Shardborough collection changed during the probe")
        if any(D.sha256(path) != report["binary_sha256"][path.name]
               for path in (index_binary, server_binary, native)):
            raise ValueError("a binary changed during the probe")
        report["all_checks_passed"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    finally:
        if server is not None:
            server.terminate()
            try:
                server.wait(timeout=5)
            except subprocess.TimeoutExpired:
                server.kill()
                server.wait()
    save()
    print(f"report={directory / 'report.json'} all_checks_passed={report['all_checks_passed']}")
    return 0 if report["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
