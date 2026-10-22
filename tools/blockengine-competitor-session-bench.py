#!/usr/bin/env python3
"""Native Shardborough snapshot versus one isolated QLever/Virtuoso server.

Exact full answers gate paired timings. Generated data only; no parity claim.
Build before running. This tool stops only the server/session it starts.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import platform
import socket
import statistics
import subprocess
import sys
import time
import urllib.parse
import urllib.request

SPEC = importlib.util.spec_from_file_location(
    "snapshot_bench", Path(__file__).with_name("blockengine-snapshot-session-bench.py"))
B = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(B)
D = B.D
LIMIT = 64 * 1024 * 1024


def clean(engine, answer):
    """Remove documented extensions only; preserve all RDF term fields."""
    answer = json.loads(json.dumps(answer))
    if engine == "qlever":
        answer.pop("meta", None)
    if engine == "virtuoso":
        answer.get("head", {}).pop("link", None)
        for key in ("distinct", "ordered"):
            answer.get("results", {}).pop(key, None)
    return answer


def known_difference(engine, name, answer, expected):
    if engine == "qlever" and name == "predicate-count":
        alternate = json.loads(json.dumps(expected))
        alternate["results"]["bindings"][0]["count"]["datatype"] = "http://www.w3.org/2001/XMLSchema#int"
        if D.canonical(answer) == D.canonical(alternate):
            return "COUNT returns xsd:int rather than xsd:integer; excluded from paired timings"
    if engine == "virtuoso" and name in ("ask-present", "ask-absent"):
        alternate = {"head": {"vars": ["__ASK_RETVAL"]}, "results": {"bindings": [
            {"__ASK_RETVAL": {"type": "literal", "datatype": "http://www.w3.org/2001/XMLSchema#integer",
                              "value": "1" if expected["boolean"] else "0"}}]}}
        if D.canonical(answer) == D.canonical(alternate):
            return "bare endpoint returns SELECT-shaped ASK result; excluded from paired timings"
    return None


def free_port():
    with socket.socket() as available:
        available.bind(("127.0.0.1", 0))
        return available.getsockname()[1]


def wait_port(server, port):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if server.poll() is not None:
            raise ValueError("competitor server exited before readiness")
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.2):
                return
        except OSError:
            time.sleep(0.05)
    raise ValueError("competitor readiness timed out")


def virtuoso_config(sql, http, rows):
    return f"""[Database]
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
ServerPort = 127.0.0.1:{sql}
DisableUnixSocket = 1
NumberOfBuffers = 10000
MaxDirtyBuffers = 6000
DirsAllowed = .
MaxQueryMem = 256M
ThreadsPerQuery = 1
AsyncQueueMaxThreads = 1
CheckpointInterval = 0
[HTTPServer]
ServerPort = 127.0.0.1:{http}
ServerRoot = .
MaxClientConnections = 4
[SPARQL]
ResultSetMaxRows = {max(20000, rows + 10)}
MaxQueryExecutionTime = 60
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", choices=["qlever", "virtuoso"], required=True)
    parser.add_argument("--server", type=Path, required=True)
    parser.add_argument("--loader", type=Path, required=True, help="qlever-index or Virtuoso's own isql")
    parser.add_argument("--library-dir", type=Path)
    parser.add_argument("--fixture-dir", type=Path, required=True)
    parser.add_argument("--subjects", type=D.bounded_number(10, 300000), required=True)
    parser.add_argument("--samples", type=D.bounded_number(1, 10), default=3)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--corpus", choices=["scale", "relational"], default="scale")
    parser.add_argument("--workload", action="append")
    parser.add_argument("--capture-mib", type=D.bounded_number(1, 2048), default=512)
    parser.add_argument("--collection-max-files", type=D.bounded_number(128, 4096), default=1024)
    parser.add_argument("--loader-memory", choices=["256 MB", "1 GB"], default="256 MB")
    args = parser.parse_args()
    corpus = D.load_corpus(args.corpus)
    names = {w["name"] for w in corpus.workloads(10)}
    if args.workload and not set(args.workload) <= names:
        parser.error("unknown workload for selected corpus")
    collection_limits = {"max_bytes": 512 * 1024 * 1024, "max_files": args.collection_max_files}
    fixture = args.fixture_dir.resolve() / "fixture.ttl"
    collection = args.fixture_dir.resolve() / "collection"
    directory = args.output_dir.resolve()
    native = D.BIN / "l4block-snapshot-session"
    loader, server_binary = args.loader.resolve(), args.server.resolve()
    if not fixture.is_file() or fixture.read_bytes() != corpus.fixture_bytes(args.subjects):
        parser.error("fixture must exactly match generated --subjects corpus")
    if any(not path.is_file() for path in (native, loader, server_binary)):
        parser.error("all three binaries must exist")
    if directory.exists() and any(directory.iterdir()):
        parser.error("output directory must be absent or empty")
    directory.mkdir(parents=True, exist_ok=True)
    engine_dir = directory / "engine"
    engine_dir.mkdir()
    env = dict(os.environ)
    if args.library_dir:
        env["DYLD_LIBRARY_PATH"] = str(args.library_dir.resolve())
    hashes = {label: D.sha256(path) for label, path in
              (("native", native), ("loader", loader), ("server", server_binary))}
    artifacts = D.collection_hashes(collection, **collection_limits)
    clock = B.ClockWindow()
    report = {
        "benchmark": "shardborough-competitor-sessions-v1", "measurement_valid": False,
        "all_answers_exact": True, "engine": args.engine,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "host": platform.platform(), "machine": platform.machine(), "cpu_count": os.cpu_count(),
        "subjects": args.subjects, "triples": corpus.triple_count(args.subjects), "samples": args.samples,
        "binary_sha256": hashes, "fixture_sha256": D.sha256(fixture), "collection_sha256": artifacts,
        "driver_sha256": D.sha256(Path(__file__)),
        "corpus": args.corpus, "corpus_sha256": D.sha256(corpus.source_file),
        "selected_workloads": args.workload, "capture_mib": args.capture_mib,
        "collection_limits": collection_limits, "pipe_driver_sha256": D.sha256(Path(B.__file__)),
        "oracle_driver_sha256": D.sha256(Path(D.__file__)),
        "source_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=D.ROOT, text=True, timeout=10).strip(),
        "scope": "Sequential single-client warm queries. Shardborough uses a pinned full-graph JSONL snapshot; competitor uses native HTTP with a new loopback connection per request. Both include full serialization and body transfer; JSON parsing, validation and capture-file writes are outside timing. One warmup, alternating paired order, no OS cache eviction. Transport and admission models differ; no industry parity claim.",
        "answer_comparison": "Exact ordered bindings and RDF term fields. Remove only QLever meta or Virtuoso head.link/results.distinct/results.ordered extensions. Known term/shape differences are reported and excluded from latency comparisons, never coerced.",
        "cache_policy": "Shardborough has no answer cache. QLever uses -c '0 B' -k 0. Virtuoso uses the retained minimal native configuration; no claim that all of its internal caches are disabled.",
        "cpu_before": B.cpu_snapshot(), "workloads": [],
    }
    session, server, log = None, None, None
    remaining_bytes = args.capture_mib * 1024 * 1024
    deadline = time.monotonic() + 1200

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    def http_query(query):
        if args.engine == "qlever":
            request = urllib.request.Request(f"http://127.0.0.1:{http}/",
                data=urllib.parse.urlencode({"query": query}).encode(),
                headers={"Accept": "application/sparql-results+json", "Content-Type": "application/x-www-form-urlencoded"})
        else:
            params = urllib.parse.urlencode({"query": query, "default-graph-uri": "urn:shardborough:fixture",
                                             "format": "application/sparql-results+json"})
            request = urllib.request.Request(f"http://127.0.0.1:{http}/sparql?{params}", headers={"Accept": "*/*"})
        with urllib.request.urlopen(request, timeout=60) as response:
            raw = response.read(LIMIT + 1)
            content_type = response.headers.get("Content-Type")
        if len(raw) > LIMIT:
            raise ValueError("HTTP result exceeded 64 MiB")
        return raw, content_type

    save()
    try:
        version_args = ["--version"] if args.engine == "qlever" else ["+version"]
        version = subprocess.run([str(server_binary), *version_args], env=env,
                                 capture_output=True, text=True, timeout=10)
        report["server_version_output"] = (version.stdout + version.stderr)[:1500]
        http, sql = free_port(), free_port()
        if args.engine == "qlever":
            load_command = [str(loader), "-i", str(engine_dir / "db"), "-f", str(fixture), "-F", "ttl", "-m", args.loader_memory]
            report["load_command"] = load_command
            started = time.perf_counter_ns()
            with (directory / "load.log").open("w") as load_log:
                subprocess.run(load_command, env=env, cwd=engine_dir, stdout=load_log,
                               stderr=subprocess.STDOUT, timeout=120, check=True)
            report["competitor_load_ns"] = time.perf_counter_ns() - started
            server_command = [str(server_binary), "-i", str(engine_dir / "db"), "-p", str(http),
                              "-m", "1 GB", "-c", "0 B", "-k", "0", "-j", "1",
                              "--no-metrics-log", "--no-resource-usage-log"]
            report["listener"] = "QLever default bind address, temporary port; requests use loopback"
        else:
            (engine_dir / "fixture.ttl").write_bytes(fixture.read_bytes())
            config = virtuoso_config(sql, http, args.subjects)
            (engine_dir / "virtuoso.ini").write_text(config)
            report["configuration"] = config
            server_command = [str(server_binary), "+foreground", "+configfile", str(engine_dir / "virtuoso.ini")]
            report["listener"] = "Virtuoso SQL/HTTP bind 127.0.0.1 on temporary ports"
        report["server_command"] = server_command
        log = (directory / "server.log").open("w")
        started = time.perf_counter_ns()
        server = subprocess.Popen(server_command, cwd=engine_dir, env=env, stdout=log, stderr=subprocess.STDOUT)
        wait_port(server, http if args.engine == "qlever" else sql)
        report["competitor_start_to_port_ns"] = time.perf_counter_ns() - started
        if args.engine == "virtuoso":
            load_sql = ("ld_dir('.', 'fixture.ttl', 'urn:shardborough:fixture');\n"
                        "rdf_loader_run();\ncheckpoint;\n"
                        "select case when count(*) = 1 and min(LL_STATE) = 2 and max(LL_ERROR) is null "
                        "then 'SHARDBOROUGH_LOAD_OK' else 'SHARDBOROUGH_LOAD_FAILED' end from DB.DBA.LOAD_LIST;\n")
            report["load_sql"] = load_sql
            started = time.perf_counter_ns()
            loaded = subprocess.run([str(loader), f"127.0.0.1:{sql}", "dba", "dba", "VERBOSE=OFF", "PROMPT=OFF"],
                                    input=load_sql, cwd=engine_dir, env=env, capture_output=True, text=True, timeout=120)
            report["competitor_load_ns"] = time.perf_counter_ns() - started
            (directory / "load.stdout").write_text(loaded.stdout)
            (directory / "load.stderr").write_text(loaded.stderr)
            if loaded.returncode or "*** Error" in loaded.stdout + loaded.stderr or "SHARDBOROUGH_LOAD_OK" not in loaded.stdout:
                raise ValueError("Virtuoso load failed")
        started = time.perf_counter_ns()
        session = B.Process([native, collection], directory / "snapshot.stderr", 120)
        ready = json.loads(session.line())
        report["snapshot_open_ns"] = time.perf_counter_ns() - started
        if not ready.get("ready") or ready.get("triples") != corpus.triple_count(args.subjects):
            raise ValueError("invalid snapshot admission")
        report["snapshot_ready"] = ready
        report["rss_after_ready_kib"] = {label: int(subprocess.check_output(
            ["ps", "-o", "rss=", "-p", str(pid)], text=True, timeout=10).strip())
            for label, pid in (("snapshot", session.proc.pid), (args.engine, server.pid))}
        save()
        for workload in corpus.workloads(args.subjects):
            if args.workload and workload["name"] not in args.workload:
                continue
            entry = {"name": workload["name"], "query": workload["query"], "warmups": {},
                     "samples": {"snapshot": [], args.engine: []}}
            report["workloads"].append(entry)
            excluded = False
            for ordinal in range(args.samples + 1):
                modes = ["snapshot", args.engine] if ordinal % 2 == 0 else [args.engine, "snapshot"]
                for mode in modes:
                    if time.monotonic() > deadline:
                        raise ValueError("overall benchmark deadline exceeded")
                    label = f"{workload['name']}-{ordinal}-{mode}"
                    print(f"start corpus={args.corpus} subjects={args.subjects} triples={corpus.triple_count(args.subjects)} {label}", file=sys.stderr, flush=True)
                    started = time.perf_counter_ns()
                    if mode == "snapshot":
                        raw, content_type = session.request(workload["query"]), "application/sparql-results+json"
                    else:
                        raw, content_type = http_query(workload["query"])
                    wall = time.perf_counter_ns() - started
                    remaining_bytes -= len(raw)
                    if remaining_bytes < 0:
                        raise ValueError(f"capture budget exceeded {args.capture_mib} MiB")
                    output = directory / f"{label}.json"
                    output.write_bytes(raw)
                    answer = json.loads(raw, object_pairs_hook=D.unique_keys, parse_constant=D.reject_constant)
                    if mode != "snapshot":
                        answer = clean(args.engine, answer)
                    exact = D.canonical(answer) == D.canonical(workload["expected"])
                    sample = {"wall_ns": wall, "bytes": len(raw), "sha256": D.sha256(output),
                              "content_type": content_type, "exact_expected_answer": exact}
                    if not exact:
                        report["all_answers_exact"] = False
                        difference = known_difference(args.engine, workload["name"], answer, workload["expected"]) if mode != "snapshot" else None
                        if not difference:
                            raise ValueError(f"unexpected complete-answer mismatch: {label}")
                        entry["timing_excluded_reason"] = difference
                        excluded = True
                    if ordinal == 0:
                        entry["warmups"][mode] = sample
                    else:
                        entry["samples"][mode].append(sample)
                    save()
                if excluded:
                    break
            if not excluded:
                entry["median_ms"] = {mode: statistics.median(s["wall_ns"] for s in samples) / 1e6
                                      for mode, samples in entry["samples"].items()}
                entry["snapshot_over_competitor"] = entry["median_ms"]["snapshot"] / entry["median_ms"][args.engine]
            save()
        if D.collection_hashes(collection, **collection_limits) != artifacts or any(D.sha256(path) != hashes[label] for label, path in
              (("native", native), ("loader", loader), ("server", server_binary))):
            raise ValueError("a binary or Shardborough collection changed")
        report["measurement_valid"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    finally:
        if session:
            try:
                session.close()
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                report["measurement_valid"] = False
                report["snapshot_shutdown_error"] = str(error)
        if server:
            server.terminate()
            try:
                server.wait(timeout=10)
            except subprocess.TimeoutExpired:
                server.kill()
                server.wait()
        if log:
            log.close()
        try:
            report["clock_check"] = clock.check()
        except ValueError as error:
            report["measurement_valid"] = False
            report["clock_error"] = str(error)
        report["cpu_after"] = B.cpu_snapshot()
        save()
    print(f"report={directory / 'report.json'} measurement_valid={report['measurement_valid']}")
    return 0 if report["measurement_valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
