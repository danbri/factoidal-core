#!/usr/bin/env python3
"""Alternate archived/current pinned snapshots; validate every complete answer.

No ingestion or build. Both snapshots remain open; opening is excluded from
query times. Timings include JSONL transfer and use the same exact oracle as
the competitor benchmark. This measures one local implementation change.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time

SPEC = importlib.util.spec_from_file_location(
    "snapshot_driver", Path(__file__).with_name("blockengine-snapshot-session-bench.py"))
B = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(B)
D = B.D


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, type=Path)
    parser.add_argument("--after", required=True, type=Path)
    parser.add_argument("--fixture-dir", required=True, type=Path)
    parser.add_argument("--subjects", required=True, type=D.bounded_number(10, 300000))
    parser.add_argument("--samples", default=5, type=D.bounded_number(1, 10))
    parser.add_argument("--workload", action="append")
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--corpus", choices=["scale", "relational"], default="scale")
    parser.add_argument("--capture-mib", type=D.bounded_number(1, 2048), default=512)
    parser.add_argument("--collection-max-files", type=D.bounded_number(128, 4096), default=1024)
    args = parser.parse_args()
    corpus = D.load_corpus(args.corpus)
    names = {w["name"] for w in corpus.workloads(10)}
    if args.workload and not set(args.workload) <= names:
        parser.error("unknown workload for selected corpus")
    collection_limits = {"max_bytes": 512 * 1024 * 1024, "max_files": args.collection_max_files}
    binaries = {mode: getattr(args, mode).resolve() for mode in ("before", "after")}
    fixture = args.fixture_dir.resolve() / "fixture.ttl"
    collection = args.fixture_dir.resolve() / "collection"
    directory = args.output_dir.resolve()
    if not fixture.is_file() or fixture.read_bytes() != corpus.fixture_bytes(args.subjects):
        parser.error("fixture must exactly match --subjects")
    if any(not path.is_file() or not os.access(path, os.X_OK) for path in binaries.values()):
        parser.error("both binaries must exist and be executable")
    if directory.exists() and any(directory.iterdir()):
        parser.error("output directory must be absent or empty")
    artifacts = D.collection_hashes(collection, **collection_limits)
    hashes = {mode: D.sha256(path) for mode, path in binaries.items()}
    directory.mkdir(parents=True, exist_ok=True)
    report = {
        "benchmark": "shardborough-snapshot-pair-v1", "all_checks_passed": False,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "host": platform.platform(), "cpu_count": os.cpu_count(),
        "subjects": args.subjects, "triples": corpus.triple_count(args.subjects),
        "samples": args.samples, "selected_workloads": args.workload,
        "fixture_sha256": D.sha256(fixture), "collection_sha256": artifacts,
        "binary_sha256": hashes, "binary_paths": {k: str(v) for k, v in binaries.items()},
        "driver_sha256": D.sha256(Path(__file__)),
        "corpus": args.corpus, "corpus_sha256": D.sha256(corpus.source_file),
        "capture_mib": args.capture_mib, "collection_limits": collection_limits,
        "session_driver_sha256": D.sha256(Path(B.__file__)),
        "oracle_driver_sha256": D.sha256(Path(D.__file__)),
        "source_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=D.ROOT, text=True).strip(),
        "cpu_before": B.cpu_snapshot(), "opening": {}, "workloads": [],
        "process_model": "two immutable snapshots; alternating sequential requests; JSONL transfer included",
    }

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    sessions = {}
    total_bytes = 0
    deadline = time.monotonic() + 1200
    save()
    try:
        for mode, binary in binaries.items():
            started = time.perf_counter_ns()
            session = B.Process([binary, collection], directory / f"{mode}.stderr", 120)
            sessions[mode] = session
            ready_raw = session.line()
            wall = time.perf_counter_ns() - started
            (directory / f"{mode}-ready.json").write_bytes(ready_raw)
            ready = json.loads(ready_raw, object_pairs_hook=D.unique_keys, parse_constant=D.reject_constant)
            if (ready.get("ready"), ready.get("triples"), ready.get("admissions"), ready.get("index-builds")) != (True, corpus.triple_count(args.subjects), 1, 1):
                raise ValueError("unexpected snapshot admission")
            report["opening"][mode] = {"wall_ns": wall, "ready": ready}
            report["opening"][mode]["rss_after_ready_kib"] = int(subprocess.check_output(
                ["ps", "-o", "rss=", "-p", str(session.proc.pid)], text=True, timeout=10).strip())
        for workload in corpus.workloads(args.subjects):
            if args.workload and workload["name"] not in args.workload:
                continue
            entry = {"name": workload["name"], "query": workload["query"],
                     "samples": {"before": [], "after": []}, "warmups": {}}
            report["workloads"].append(entry)
            for ordinal in range(args.samples + 1):
                modes = ["before", "after"] if ordinal % 2 == 0 else ["after", "before"]
                for mode in modes:
                    if time.monotonic() > deadline or total_bytes >= args.capture_mib * 1024 * 1024:
                        raise ValueError("benchmark time or output budget exceeded")
                    label = f"{workload['name']}-{ordinal}-{mode}"
                    print(f"start corpus={args.corpus} subjects={args.subjects} triples={corpus.triple_count(args.subjects)} {label}", file=sys.stderr, flush=True)
                    started = time.perf_counter_ns()
                    raw = sessions[mode].request(workload["query"])
                    wall = time.perf_counter_ns() - started
                    total_bytes += len(raw)
                    if total_bytes > args.capture_mib * 1024 * 1024:
                        raise ValueError("benchmark output budget exceeded")
                    output = directory / f"{label}.stdout"
                    output.write_bytes(raw)
                    validation = D.validate_results(output, workload["expected"], 1)
                    sample = {"wall_ns": wall, "bytes": len(raw), "sha256": D.sha256(output),
                              "validation": validation}
                    if ordinal == 0:
                        entry["warmups"][mode] = sample
                    else:
                        entry["samples"][mode].append(sample)
                    save()
            entry["median_ms"] = {mode: statistics.median(s["wall_ns"] for s in samples) / 1e6
                                  for mode, samples in entry["samples"].items()}
            entry["before_over_after"] = entry["median_ms"]["before"] / entry["median_ms"]["after"]
        if D.collection_hashes(collection, **collection_limits) != artifacts or any(D.sha256(path) != hashes[mode] for mode, path in binaries.items()):
            raise ValueError("collection or binary changed during measurement")
        report["all_checks_passed"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    finally:
        for mode, session in sessions.items():
            try:
                session.close()
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                report["all_checks_passed"] = False
                report.setdefault("shutdown_errors", {})[mode] = str(error)
        report["cpu_after"] = B.cpu_snapshot()
        save()
    print(f"report={directory / 'report.json'} all_checks_passed={report['all_checks_passed']}")
    return 0 if report["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
