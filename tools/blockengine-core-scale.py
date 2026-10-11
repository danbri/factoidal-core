#!/usr/bin/env python3
"""Measure bounded native IBK3 lifecycle and query scaling on synthetic RDF."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time


def subject_sizes(text):
    try:
        values = [int(value) for value in text.split(",")]
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected comma-separated integers") from error
    if not values or len(values) > 8 or any(value < 10 or value > 100_000 for value in values):
        raise argparse.ArgumentTypeError("use one to eight subject counts between 10 and 100000")
    if any(value % 10 for value in values):
        raise argparse.ArgumentTypeError("subject counts must be multiples of ten")
    if len(set(values)) != len(values):
        raise argparse.ArgumentTypeError("subject counts must be distinct")
    return values


def positive_integer(text):
    value = int(text)
    if value < 1 or value > 20:
        raise argparse.ArgumentTypeError("must be between one and twenty")
    return value


def bounded_seconds(text):
    value = float(text)
    if not 0 < value <= 120:
        raise argparse.ArgumentTypeError("must be positive and at most 120 seconds")
    return value


def sha256(file_path):
    digest = hashlib.sha256()
    with file_path.open("rb") as source:
        for chunk in iter(lambda: source.read(1_048_576), b""):
            digest.update(chunk)
    return digest.hexdigest()


def generate_fixture(file_path, subjects):
    with file_path.open("w", encoding="utf-8") as fixture:
        for ordinal in range(subjects):
            subject = f"urn:scale:subject:{ordinal:08d}"
            fixture.write(f"<{subject}> <urn:scale:type> <urn:scale:Person> .\n")
            fixture.write(f'<{subject}> <urn:scale:name> "person-{ordinal:08d}" .\n')
            fixture.write(f"<{subject}> <urn:scale:group> <urn:scale:group:{ordinal % 10}> .\n")


def measure(command, label, directory, timeout, markers):
    started_utc = datetime.now(timezone.utc).isoformat()
    started = time.perf_counter_ns()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    print(f"start {directory.name}/{label} pid={process.pid}", file=sys.stderr, flush=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        process.kill()
        stdout, stderr = process.communicate()
    wall_ms = (time.perf_counter_ns() - started) / 1_000_000
    finished_utc = datetime.now(timezone.utc).isoformat()
    stdout_path = directory / f"{label}.stdout"
    stderr_path = directory / f"{label}.stderr"
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    missing = [marker for marker in markers if not re.search(marker, stdout)]
    succeeded = not timed_out and process.returncode == 0 and not missing
    read_bytes = re.search(r"logical-read-bytes=(\d+) fetched-bytes=(\d+)", stdout)
    result = {
        "command": command,
        "started_utc": started_utc,
        "finished_utc": finished_utc,
        "pid": process.pid,
        "wall_ms": wall_ms,
        "exit_code": process.returncode,
        "timed_out": timed_out,
        "validation_passed": succeeded,
        "missing_markers": missing,
        "stdout_file": str(stdout_path),
        "stderr_file": str(stderr_path),
        "native_status": stdout.splitlines()[0] if stdout else None,
        "logical_read_bytes": int(read_bytes[1]) if read_bytes else None,
        "fetched_bytes": int(read_bytes[2]) if read_bytes else None,
    }
    print(f"finish {directory.name}/{label} wall_ms={wall_ms:.3f} exit={process.returncode} "
          f"timeout={timed_out} valid={succeeded}", file=sys.stderr, flush=True)
    return result


def query_workloads(subjects):
    prefix = "?subject <urn:scale:type> ?type"
    name = "?subject <urn:scale:name> ?name"
    selected = "?subject <urn:scale:group> <urn:scale:group:0>"
    return [
        ("limit-zero", f"SELECT ?subject WHERE {{ {prefix} }} LIMIT 0", 0, None),
        ("limit-two", f"SELECT ?subject WHERE {{ {prefix} }} LIMIT 2", 2, None),
        ("predicate-count", f"SELECT (COUNT(*) AS ?count) WHERE {{ {prefix} }}", 1, subjects),
        ("object-index", f"SELECT ?subject WHERE {{ {selected} }}", subjects // 10, None),
        ("subject-join", f"SELECT ?subject ?name WHERE {{ {prefix} . {name} }}", subjects, None),
        ("object-subject-join", f"SELECT ?subject ?name WHERE {{ {selected} . {name} }}",
         subjects // 10, None),
        ("subject-triple-join", f"SELECT ?subject ?name ?group WHERE {{ {prefix} . {name} . "
         "?subject <urn:scale:group> ?group }", subjects, None),
    ]


def compare_existing(args, repository, binaries, directory, report):
    subjects = args.subjects[0]
    baseline = args.baseline_query.resolve()
    collection = args.existing_collection.resolve()
    if not baseline.is_file() or not collection.is_dir():
        raise ValueError("baseline binary and existing collection must exist")
    query = next(query for name, query, _, _ in query_workloads(subjects)
                 if name == "subject-join")
    report.update({
        "benchmark": "factoidal-core-native-selection-comparison-v1",
        "subjects": subjects,
        "triples": subjects * 3,
        "query": query,
        "collection": str(collection),
        "baseline_binary_sha256": sha256(baseline),
        "baseline_binary": str(baseline),
        "measured_runs_per_binary": args.warm_runs,
        "warmup_runs": 0,
        "process_model": "paired baseline/optimized fresh processes; OS cache is not evicted",
        "validation": "Generated cardinality and identical ten-row previews; not complete bags",
        "source_state": "working-tree-on-" + report["source_head"],
        "samples": {"baseline": [], "optimized": []},
        "source_file_sha256": {
            name: sha256(repository / name) for name in (
                "formal/lean4/L4Factoidal/Storage/SubjectRowIndexWireV2.lean",
                "formal/lean4/L4Factoidal/Storage/SubjectRowIndexWireV2Theorems.lean",
                "formal/lean4/Harness/IndexedBlockV3Materialize.lean",
                "formal/lean4/Harness/IndexedBlockV3Query.lean",
            )
        },
    })
    fixture = collection.parent / "fixture.ttl"
    if fixture.is_file():
        report["fixture_sha256"] = sha256(fixture)
        report["fixture_bytes"] = fixture.stat().st_size

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    save()
    markers = [rf"rows={subjects}(?:\s|$)"]
    for ordinal in range(args.warm_runs):
        for name, binary in (("baseline", baseline),
                             ("optimized", binaries["l4block-id-v3-query"])):
            sample = measure([str(binary), str(collection), "--query", query],
                             f"{name}-{ordinal}", directory, args.timeout, markers)
            report["samples"][name].append(sample)
            save()
            if not sample["validation_passed"]:
                return 1
    report["median_ms"] = {
        name: statistics.median(sample["wall_ms"] for sample in samples)
        for name, samples in report["samples"].items()
    }
    samples = [sample for group in report["samples"].values() for sample in group]
    report["same_read_counters"] = len({
        (sample["logical_read_bytes"], sample["fetched_bytes"]) for sample in samples
    }) == 1
    report["same_preview_rows"] = len({
        tuple(Path(sample["stdout_file"]).read_text().splitlines()[1:]) for sample in samples
    }) == 1
    report["all_native_checks_passed"] = all(sample["validation_passed"] for sample in samples)
    save()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["same_read_counters"] and report["same_preview_rows"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--subjects", type=subject_sizes, default=[1000, 10000, 100000])
    parser.add_argument("--warm-runs", type=positive_integer, default=3)
    parser.add_argument("--timeout", type=bounded_seconds, default=120)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--baseline-query", type=Path,
                        help="compare this preserved binary against the current query binary")
    parser.add_argument("--existing-collection", type=Path,
                        help="reuse an activated collection for paired full-join measurements")
    args = parser.parse_args()
    if bool(args.baseline_query) != bool(args.existing_collection):
        parser.error("--baseline-query and --existing-collection must be used together")
    if args.baseline_query and len(args.subjects) != 1:
        parser.error("comparison mode requires exactly one --subjects value")
    repository = Path(__file__).resolve().parent.parent
    lean = repository / "formal/lean4"
    binary_directory = lean / ".lake/build/bin"
    names = ("l4block-shard-pack", "l4block-shard-activate", "l4block-id-v3-query")
    binaries = {name: binary_directory / name for name in names}
    for binary in binaries.values():
        if not binary.is_file():
            parser.error(f"build the native target first: {binary.name}")
    directory = args.output_dir or Path(tempfile.mkdtemp(prefix="factoidal-core-scale-"))
    directory.mkdir(parents=True, exist_ok=True)
    if (directory / "report.json").exists():
        parser.error("output directory already contains report.json; choose a fresh directory")
    report = {
        "benchmark": "factoidal-core-native-scale-v1",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "source_head": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=repository, text=True, timeout=10).strip(),
        "lean_toolchain": (lean / "lean-toolchain").read_text().strip(),
        "binary_sha256": {name: sha256(binary) for name, binary in binaries.items()},
        "timeout_seconds": args.timeout,
        "warm_runs": args.warm_runs,
        "process_model": "fresh native process for every sample; OS page cache is not evicted",
        "validation": "Exact generated cardinalities and COUNT scalar, not complete result bags",
        "scope": "Includes startup, artifact admission and preview output; fixture construction excluded",
        "sizes": [],
    }
    if args.baseline_query:
        try:
            return compare_existing(args, repository, binaries, directory, report)
        except ValueError as error:
            parser.error(str(error))

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    failed = False
    print(f"results={directory}", file=sys.stderr, flush=True)
    for subjects in args.subjects:
        size_directory = directory / f"subjects-{subjects}"
        size_directory.mkdir()
        fixture = size_directory / "fixture.ttl"
        generate_fixture(fixture, subjects)
        collection = size_directory / "collection"
        generation = collection / "first"
        size_result = {
            "subjects": subjects,
            "triples": subjects * 3,
            "fixture_bytes": fixture.stat().st_size,
            "fixture_sha256": sha256(fixture),
            "expected_rows": {name: rows for name, _, rows, _ in query_workloads(subjects)},
            "queries": {},
        }
        report["sizes"].append(size_result)
        save()
        packed = measure([str(binaries[names[0]]), str(fixture), str(generation), "ibk3"],
                         "pack", size_directory, args.timeout,
                         [rf"triples={subjects * 3}(?:\s|$)", r"wire-version=6(?:\s|$)"])
        size_result["pack"] = packed
        save()
        if not packed["validation_passed"]:
            failed = True
            size_result["skipped"] = "activation and queries skipped after pack failure/cap"
            save()
            continue
        size_result["artifact_bytes"] = sum(
            artifact.stat().st_size for artifact in generation.iterdir() if artifact.is_file())
        activated = measure([str(binaries[names[1]]), str(collection), "first"],
                            "activate", size_directory, args.timeout, [r"pointer=CURRENT(?:\s|$)"])
        size_result["activate"] = activated
        save()
        if not activated["validation_passed"]:
            failed = True
            size_result["skipped"] = "queries skipped after activation failure/cap"
            save()
            continue
        for name, query, rows, scalar in query_workloads(subjects):
            markers = [rf"rows={rows}(?:\s|$)"]
            if scalar is not None:
                markers.append(re.escape(
                    f'("{scalar}", "http://www.w3.org/2001/XMLSchema#integer", none)'))
            samples = []
            size_result["queries"][name] = {
                "query": query, "expected_rows": rows, "expected_scalar": scalar, "samples": samples,
            }
            for ordinal in range(args.warm_runs + 1):
                measured = measure([str(binaries[names[2]]), str(collection), "--query", query],
                                   f"{name}-{ordinal}", size_directory, args.timeout, markers)
                samples.append(measured)
                save()
                if not measured["validation_passed"]:
                    failed = True
                    break
            successful_times = [sample["wall_ms"] for sample in samples[1:]
                                if sample["validation_passed"]]
            if successful_times:
                size_result["queries"][name]["subsequent_median_ms"] = statistics.median(successful_times)
            if not samples[-1]["validation_passed"]:
                size_result["skipped"] = "remaining queries skipped after query failure/cap"
                save()
                break
        save()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
