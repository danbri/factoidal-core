#!/usr/bin/env python3
"""Measure the native persisted route on the pinned binding-site fixture."""

import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
import time


def positive_integer(text):
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("must be at least one")
    return value


def positive_seconds(text):
    value = float(text)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError("must be finite and positive")
    return value


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def measure(command, markers, timeout):
    started = time.perf_counter_ns()
    result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    elapsed = time.perf_counter_ns() - started
    if result.returncode:
        raise RuntimeError(f"{command[0]} exited {result.returncode}: {result.stderr}")
    for marker in markers:
        if not re.search(marker, result.stdout):
            raise RuntimeError(f"missing result /{marker}/ in {result.stdout}")
    return {
        "wall_ms": elapsed / 1_000_000,
        "native_status": result.stdout.splitlines()[0],
    }


def series(command, markers, warm_runs, timeout):
    first = measure(command, markers, timeout)
    warm = [measure(command, markers, timeout) for _ in range(warm_runs)]
    times = [sample["wall_ms"] for sample in warm]
    return {
        "first_process": first,
        "subsequent_processes": warm,
        "subsequent_median_ms": statistics.median(times),
        "subsequent_min_ms": min(times),
        "subsequent_max_ms": max(times),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--warm-runs", type=positive_integer, default=5)
    parser.add_argument("--timeout", type=positive_seconds, default=120)
    args = parser.parse_args()
    repository = Path(__file__).resolve().parent.parent
    lean = repository / "formal/lean4"
    binary_directory = lean / ".lake/build/bin"
    names = ("l4block-shard-pack", "l4block-shard-activate", "l4block-id-v3-query")
    binaries = {name: binary_directory / name for name in names}
    for binary in binaries.values():
        if not binary.is_file():
            parser.error(f"build the native target first: {binary.name}")
    fixture = repository / "examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl"
    report = {
        "benchmark": "factoidal-core-native-binding-site-v1",
        "platform": platform.platform(),
        "machine": platform.machine(),
        "lean_toolchain": (lean / "lean-toolchain").read_text().strip(),
        "fixture": str(fixture.relative_to(repository)),
        "fixture_sha256": sha256(fixture),
        "fixture_bytes": fixture.stat().st_size,
        "fixture_triples": 368,
        "binary_sha256": {name: sha256(binary) for name, binary in binaries.items()},
        "warm_runs": args.warm_runs,
        "process_model": "fresh native process for every sample",
        "cache_note": "OS page cache is not evicted; first process is not disk-cold",
        "scope": "Includes process startup, artifact admission and output; no competitor comparison",
        "validation": "Expected physical modes, row cardinalities and COUNT scalar; not complete answer bags",
        "workloads": {},
    }
    predicate = "http://www.wikidata.org/prop/direct/P31"
    whole = "http://www.wikidata.org/prop/direct/P361"
    workloads = [
        ("limit-zero", f"SELECT ?x WHERE {{ ?x <{predicate}> ?type }} LIMIT 0",
         0, "ibk3-limit-zero", None),
        ("predicate-count", f"SELECT (COUNT(*) AS ?count) WHERE {{ ?x <{predicate}> ?type }}",
         1, "ibk3-paged-merkle-count", '"78"'),
        ("object-index", f"SELECT ?x WHERE {{ ?x <{predicate}> <http://www.wikidata.org/entity/Q616005> }}",
         78, "ibk3-sri2-tli1-oli2-object-scan", None),
        ("subject-join", f"SELECT ?x ?type ?whole WHERE {{ ?x <{predicate}> ?type . ?x <{whole}> ?whole }}",
         290, "ibk3-sri2-tli1-subject-join", None),
        ("object-subject-join", f"SELECT ?x ?whole WHERE {{ ?x <{predicate}> <http://www.wikidata.org/entity/Q616005> . ?x <{whole}> ?whole }}",
         290, "ibk3-sri2-tli1-oli2-object-subject-direct-select", None),
    ]
    with tempfile.TemporaryDirectory(prefix="factoidal-core-baseline-") as temporary:
        collection = Path(temporary) / "collection"
        pack_samples = []
        for ordinal in range(args.warm_runs + 1):
            destination = collection / f"generation-{ordinal}"
            pack_samples.append(measure(
                [str(binaries[names[0]]), str(fixture), str(destination), "ibk3"],
                [r"triples=368 blocks=2(?:\s|$)", r"wire-version=6(?:\s|$)"], args.timeout))
        pack_times = [sample["wall_ms"] for sample in pack_samples[1:]]
        report["workloads"]["pack"] = {
            "first_process": pack_samples[0],
            "subsequent_processes": pack_samples[1:],
            "subsequent_median_ms": statistics.median(pack_times),
            "subsequent_min_ms": min(pack_times),
            "subsequent_max_ms": max(pack_times),
        }
        report["workloads"]["activate"] = series(
            [str(binaries[names[1]]), str(collection), "generation-0"],
            [r"pointer=CURRENT(?:\s|$)"], args.warm_runs, args.timeout)
        for name, query, row_count, mode, value in workloads:
            markers = [rf"rows={row_count}(?:\s|$)", "open-mode=" + re.escape(mode) + r"\("]
            if value is not None:
                markers.append(re.escape(value))
            report["workloads"][name] = series(
                [str(binaries[names[2]]), str(collection), "--query", query],
                markers, args.warm_runs, args.timeout)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
