#!/usr/bin/env python3
"""Paired native page-selection timings; validate every complete ordered answer.

Build first. Supply an archived baseline binary and a subjects-N directory
from blockengine-core-scale.py. No build, ingestion or activation is timed.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time

SPEC = importlib.util.spec_from_file_location(
    "repeat_driver", Path(__file__).with_name("blockengine-core-repeat.py"))
D = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(D)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True, type=Path)
    parser.add_argument("--fixture-dir", required=True, type=Path)
    parser.add_argument("--subjects", required=True, type=D.bounded_number(10, 100000))
    parser.add_argument("--samples", default=3, type=D.bounded_number(1, 10))
    parser.add_argument("--timeout", default=60, type=D.bounded_number(0.1, 120, False))
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    baseline = args.baseline.resolve()
    optimized = D.BIN / "l4block-id-v3-query"
    fixture_dir = args.fixture_dir.resolve()
    fixture = fixture_dir / "fixture.ttl"
    collection = fixture_dir / "collection"
    directory = args.output_dir.resolve()
    if not baseline.is_file() or not optimized.is_file():
        parser.error("both native binaries must exist")
    if not fixture.is_file() or fixture.read_bytes() != D.fixture_bytes(args.subjects):
        parser.error("fixture must exactly match the generated corpus for --subjects")
    if directory.exists() and any(directory.iterdir()):
        parser.error("output directory must be absent or empty")
    artifacts = D.collection_hashes(collection)
    directory.mkdir(parents=True, exist_ok=True)
    binaries = {"baseline": baseline, "optimized": optimized}
    report = {
        "benchmark": "shardborough-paired-page-selection-v1",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "host": platform.platform(), "machine": platform.machine(),
        "subjects": args.subjects, "triples": 3 * args.subjects,
        "source_head": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=D.ROOT, text=True, timeout=10).strip(),
        "toolchain": (D.ROOT / "formal/lean4/lean-toolchain").read_text().strip(),
        "binary_sha256": {name: D.sha256(path) for name, path in binaries.items()},
        "driver_sha256": D.sha256(Path(__file__)),
        "validation_driver_sha256": D.sha256(Path(D.__file__)),
        "fixture_sha256": D.sha256(fixture), "collection_sha256": artifacts,
        "samples": args.samples, "warmups_per_binary_per_query": 1,
        "scope": "Fresh native processes; startup, admission, reads, evaluation and complete JSON output. OS cache not evicted. No competitor measurement.",
        "validation": "Every complete ordered answer equals the independently generated expected JSON. Exact term fields, variables, row positions and multiplicities.",
        "counter_scope": "Artifact range counters only; excludes some control/sidecar/delta and failed speculative reads.",
        "workloads": [], "all_checks_passed": False,
    }
    budget = D.Budget(512 * 1024 * 1024, time.monotonic() + 1200)

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    save()
    try:
        for workload in D.workloads(args.subjects):
            if workload["name"] not in ("object-subject-join", "subject-join", "subject-triple-join"):
                continue
            entry = {"name": workload["name"], "query": workload["query"],
                     "samples": {name: [] for name in binaries}, "warmups": {}}
            report["workloads"].append(entry)
            counters = []
            for ordinal in range(args.samples + 1):
                order = list(binaries) if ordinal % 2 == 0 else list(reversed(binaries))
                for name in order:
                    label = f"{entry['name']}-{ordinal}-{name}"
                    print(f"start subjects={args.subjects} {label}", file=sys.stderr, flush=True)
                    sample = D.capture([str(binaries[name]), str(collection), "--json", "--query",
                                        workload["query"]], directory, label, args.timeout,
                                       64 * 1024 * 1024, budget)
                    if ordinal == 0:
                        entry["warmups"][name] = sample
                    else:
                        entry["samples"][name].append(sample)
                    save()
                    if sample["failure"] or sample["exit_code"]:
                        raise ValueError(f"{label}: native process failed")
                    sample.update(D.validate_results(Path(sample["stdout_file"]), workload["expected"], 1))
                    sample["counter"] = D.read_counters(Path(sample["stderr_file"]), 1)[0]
                    counters.append(sample["counter"])
                    sample["validation_passed"] = True
                    print(f"pass {label} wall_ms={sample['wall_ns'] / 1e6:.3f}", file=sys.stderr, flush=True)
                    save()
            if any(counter != counters[0] for counter in counters):
                raise ValueError(f"{entry['name']}: physical modes or counters changed")
            entry["median_ms"] = {
                name: statistics.median(s["wall_ns"] for s in samples) / 1e6
                for name, samples in entry["samples"].items()}
            entry["speedup"] = entry["median_ms"]["baseline"] / entry["median_ms"]["optimized"]
            save()
        if D.collection_hashes(collection) != artifacts:
            raise ValueError("collection changed during measurement")
        if any(D.sha256(path) != report["binary_sha256"][name] for name, path in binaries.items()):
            raise ValueError("binary changed during measurement")
        report["all_checks_passed"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    save()
    print(f"report={directory / 'report.json'} all_checks_passed={report['all_checks_passed']}")
    return 0 if report["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
