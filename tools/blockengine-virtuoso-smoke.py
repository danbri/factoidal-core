#!/usr/bin/env python3
"""Isolated native Virtuoso complete-answer smoke on the core-scale fixture.

No latency claim. Uses loopback SQL/HTTP ports and stops only its own server.
The installed unixODBC isql is unsuitable: supply Virtuoso's own client.
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


def free_port():
    with socket.socket() as available:
        available.bind(("127.0.0.1", 0))
        return available.getsockname()[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--virtuoso-server", required=True, type=Path)
    parser.add_argument("--virtuoso-isql", required=True, type=Path)
    parser.add_argument("--fixture-dir", required=True, type=Path)
    parser.add_argument("--subjects", type=D.bounded_number(10, 10000), default=1000)
    parser.add_argument("--library-dir", type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    server_binary, client = args.virtuoso_server.resolve(), args.virtuoso_isql.resolve()
    fixture = args.fixture_dir.resolve() / "fixture.ttl"
    directory = args.output_dir.resolve()
    if not server_binary.is_file() or not client.is_file():
        parser.error("supply native Virtuoso server and isql binaries")
    if not fixture.is_file() or fixture.read_bytes() != D.fixture_bytes(args.subjects):
        parser.error("fixture must exactly match --subjects")
    if directory.exists() and any(directory.iterdir()):
        parser.error("output directory must be absent or empty")
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "fixture.ttl").write_bytes(fixture.read_bytes())
    env = dict(os.environ)
    if args.library_dir:
        env["DYLD_LIBRARY_PATH"] = str(args.library_dir.resolve())
    sql_port, http_port = free_port(), free_port()
    config = f"""[Database]
DatabaseFile = db.db
ErrorLogFile = db.log
LockFile = db.lck
TransactionFile = db.trx
FileExtend = 200
TempStorage = TempDatabase
[TempDatabase]
DatabaseFile = temp.db
TransactionFile = temp.trx
[Parameters]
ServerPort = 127.0.0.1:{sql_port}
DisableUnixSocket = 1
NumberOfBuffers = 10000
MaxDirtyBuffers = 6000
DirsAllowed = .
MaxQueryMem = 256M
ThreadsPerQuery = 1
AsyncQueueMaxThreads = 1
CheckpointInterval = 0
[HTTPServer]
ServerPort = 127.0.0.1:{http_port}
ServerRoot = .
MaxClientConnections = 4
[SPARQL]
ResultSetMaxRows = 20000
MaxQueryExecutionTime = 30
"""
    (directory / "virtuoso.ini").write_text(config)
    command = [str(server_binary), "+foreground", "+configfile", str(directory / "virtuoso.ini")]
    report = {
        "scope": "Native Virtuoso correctness probe only; no performance claim. Compare complete ordered answers to the independently generated fixture oracle used for Shardborough and QLever.",
        "subjects": args.subjects, "triples": args.subjects * 3,
        "fixture_sha256": D.sha256(fixture), "configuration": config,
        "server_command": command, "binary_sha256": D.sha256(server_binary),
        "client_sha256": D.sha256(client), "driver_sha256": D.sha256(Path(__file__)),
        "protocol_dataset": "default-graph-uri=urn:shardborough:fixture; fixture loaded into that graph",
        "comparison": "Exact bindings, RDF term fields and row positions. Explicitly remove only head.link and Virtuoso results.distinct/results.ordered extensions. No RDF datatype coercion.",
        "workloads": [], "all_checks_passed": False,
    }
    server = None

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    save()
    try:
        with (directory / "server.log").open("w") as log:
            server = subprocess.Popen(command, cwd=directory, env=env, stdout=log,
                                      stderr=subprocess.STDOUT)
            deadline = time.monotonic() + 30
            while True:
                if server.poll() is not None or time.monotonic() >= deadline:
                    raise ValueError("Virtuoso failed to start within 30 seconds")
                try:
                    with socket.create_connection(("127.0.0.1", sql_port), timeout=0.2):
                        break
                except OSError:
                    time.sleep(0.1)
            sql = "DB.DBA.TTLP(file_to_string('fixture.ttl'), '', 'urn:shardborough:fixture');\ncheckpoint;\n"
            report["load_sql"] = sql
            load = subprocess.run([str(client), f"127.0.0.1:{sql_port}", "dba", "dba",
                                   "VERBOSE=OFF", "PROMPT=OFF"], input=sql, env=env,
                                  cwd=directory, capture_output=True, text=True, timeout=60)
            (directory / "load.stdout").write_text(load.stdout)
            (directory / "load.stderr").write_text(load.stderr)
            if load.returncode or "*** Error" in load.stdout + load.stderr:
                raise ValueError("Virtuoso fixture load failed; inspect load logs")
            for workload in D.workloads(args.subjects):
                name = workload["name"]
                params = urllib.parse.urlencode({"query": workload["query"],
                    "default-graph-uri": "urn:shardborough:fixture",
                    "format": "application/sparql-results+json"})
                # The bare native installation returned 406 for a strict
                # JSON Accept header. Explicit format plus */* yields JSON;
                # retain its actual Content-Type as a protocol observation.
                request = urllib.request.Request(f"http://127.0.0.1:{http_port}/sparql?{params}",
                                                 headers={"Accept": "*/*"})
                with urllib.request.urlopen(request, timeout=30) as response:
                    content_type = response.headers.get("Content-Type")
                    raw = response.read(8 * 1024 * 1024 + 1)
                if len(raw) > 8 * 1024 * 1024:
                    raise ValueError("Virtuoso answer exceeded 8 MiB")
                output = directory / f"{name}.json"
                output.write_bytes(raw)
                answer = json.loads(raw, object_pairs_hook=D.unique_keys,
                                    parse_constant=D.reject_constant)
                extensions = {"head.link": answer["head"].pop("link", None)}
                if "results" in answer:
                    for key in ("distinct", "ordered"):
                        extensions[f"results.{key}"] = answer["results"].pop(key, None)
                equal = D.canonical(answer) == D.canonical(workload["expected"])
                row = {"name": name, "query": workload["query"], "content_type": content_type,
                       "exact_expected_answer": equal, "answer_sha256": D.sha256(output),
                       "ignored_extensions": extensions}
                report["workloads"].append(row)
                if not equal:
                    report.setdefault("answer_differences", []).append(name)
                save()
        if D.sha256(fixture) != report["fixture_sha256"] or D.sha256(server_binary) != report["binary_sha256"]:
            raise ValueError("fixture or binary changed during probe")
        report["all_checks_passed"] = not report.get("answer_differences")
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    finally:
        if server is not None:
            server.terminate()
            try:
                server.wait(timeout=10)
            except subprocess.TimeoutExpired:
                server.kill()
                server.wait()
    save()
    print(f"report={directory / 'report.json'} all_checks_passed={report['all_checks_passed']}")
    return 0 if report["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
