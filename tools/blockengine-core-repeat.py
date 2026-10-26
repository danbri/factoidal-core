#!/usr/bin/env python3
"""Bounded native fresh-admission repeats with every complete answer checked.

Example: python3 tools/blockengine-core-repeat.py --subjects 1000 --repeat 20
Use --subjects 10 --repeat 2 --samples 1 for a small validation run.
No build is performed. Run only when other builds/benchmarks/servers are idle.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import selectors
import statistics
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "formal/lean4/.lake/build/bin"
STATUS = re.compile(r"^l4block-id-v3-query shards=(\d+) open-mode=(\S+) "
                    r"delta=(\S+) logical-read-bytes=(\d+) fetched-bytes=(\d+)$")


def sha256(file_path):
    digest = hashlib.sha256()
    with file_path.open("rb") as source:
        for chunk in iter(lambda: source.read(1_048_576), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":"), allow_nan=False)


def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f"non-JSON constant: {value}")


def validate_results(file_path, expected, repeats):
    reference = canonical(expected)
    documents = 0
    with file_path.open("r", encoding="utf-8") as source:
        for line in source:
            documents += 1
            if documents > repeats or not line.endswith("\n"):
                raise ValueError("extra document or truncated NDJSON line")
            actual = json.loads(line, object_pairs_hook=unique_keys,
                                parse_constant=reject_constant)
            if canonical(actual) != reference:
                raise ValueError(f"complete ordered answer mismatch at iteration {documents}")
    if documents != repeats:
        raise ValueError(f"expected {repeats} documents, received {documents}")
    return {"documents": documents,
            "expected_canonical_sha256": hashlib.sha256(reference.encode()).hexdigest()}


def fixture_bytes(subjects):
    return "".join(
        f'<urn:scale:subject:{ordinal:08d}> <urn:scale:type> <urn:scale:Person> .\n'
        f'<urn:scale:subject:{ordinal:08d}> <urn:scale:name> "person-{ordinal:08d}" .\n'
        f'<urn:scale:subject:{ordinal:08d}> <urn:scale:group> <urn:scale:group:{ordinal % 10}> .\n'
        for ordinal in range(subjects)
    ).encode("utf-8")


def workloads(subjects):
    def uri(value):
        return {"type": "uri", "value": value}

    def row(ordinal, name=False, group=False):
        result = {"subject": uri(f"urn:scale:subject:{ordinal:08d}")}
        if name:
            result["name"] = {"type": "literal", "value": f"person-{ordinal:08d}"}
        if group:
            result["group"] = uri(f"urn:scale:group:{ordinal % 10}")
        return result

    def select(name, query, variables, rows):
        return {"name": name, "query": query,
                "expected": {"head": {"vars": variables}, "results": {"bindings": rows}}}

    kind = "?subject <urn:scale:type> ?type"
    name = "?subject <urn:scale:name> ?name"
    group = "?subject <urn:scale:group> <urn:scale:group:0>"
    return [
        select("limit-zero", f"SELECT ?subject WHERE {{ {kind} }} LIMIT 0", ["subject"], []),
        select("predicate-count", f"SELECT (COUNT(*) AS ?count) WHERE {{ {kind} }}",
               ["count"], [{"count": {"type": "literal", "value": str(subjects),
                                     "datatype": "http://www.w3.org/2001/XMLSchema#integer"}}]),
        {"name": "ask-present", "query": f"ASK {{ {kind} }}",
         "expected": {"head": {}, "boolean": True}},
        {"name": "ask-absent", "query": "ASK { ?subject <urn:scale:absent> ?object }",
         "expected": {"head": {}, "boolean": False}},
        select("object-index", f"SELECT ?subject WHERE {{ {group} }} ORDER BY ?subject",
               ["subject"], [row(ordinal) for ordinal in range(0, subjects, 10)]),
        select("subject-join", f"SELECT ?subject ?name WHERE {{ {kind} . {name} }} ORDER BY ?subject",
               ["subject", "name"], [row(ordinal, name=True) for ordinal in range(subjects)]),
        select("object-subject-join", f"SELECT ?subject ?name WHERE {{ {group} . {name} }} ORDER BY ?subject",
               ["subject", "name"], [row(ordinal, name=True) for ordinal in range(0, subjects, 10)]),
        select("subject-triple-join", f"SELECT ?subject ?name ?group WHERE {{ {kind} . {name} . "
               "?subject <urn:scale:group> ?group } ORDER BY ?subject", ["subject", "name", "group"],
               [row(ordinal, name=True, group=True) for ordinal in range(subjects)]),
        select("limit-slice", f"SELECT ?subject ?name WHERE {{ {name} }} ORDER BY ?subject OFFSET 3 LIMIT 7",
               ["subject", "name"], [row(ordinal, name=True) for ordinal in range(3, min(subjects, 10))]),
    ]


def load_corpus(name):
    """Known local corpora only; preserve the original scale corpus by default."""
    from types import SimpleNamespace
    if name == "scale":
        return SimpleNamespace(name=name, source_file=Path(__file__),
            fixture_bytes=fixture_bytes, workloads=workloads, triple_count=lambda n: 3 * n)
    if name != "relational":
        raise ValueError("unknown corpus")
    import importlib.util
    source = Path(__file__).with_name("blockengine-relational-corpus.py")
    spec = importlib.util.spec_from_file_location("relational_corpus", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return SimpleNamespace(name=name, source_file=source, fixture_bytes=module.fixture_bytes,
        workloads=module.workloads, triple_count=module.triple_count)


class Budget:
    def __init__(self, remaining, deadline):
        self.remaining = remaining
        self.deadline = deadline


def capture(command, directory, label, timeout, output_limit, budget):
    stdout_file = directory / f"{label}.stdout"
    stderr_file = directory / f"{label}.stderr"
    started = time.perf_counter_ns()
    deadline = min(time.monotonic() + timeout, budget.deadline)
    failure = None
    written = 0
    with stdout_file.open("xb") as stdout, stderr_file.open("xb") as stderr:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        with selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ, stdout)
            selector.register(process.stderr, selectors.EVENT_READ, stderr)
            try:
                while selector.get_map():
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        failure = "timeout"
                        break
                    for key, _ in selector.select(min(remaining, 0.1)):
                        chunk = os.read(key.fileobj.fileno(), 65536)
                        if not chunk:
                            selector.unregister(key.fileobj)
                            continue
                        allowed = min(len(chunk), output_limit - written, budget.remaining)
                        key.data.write(chunk[:allowed])
                        written += allowed
                        budget.remaining -= allowed
                        if allowed < len(chunk):
                            failure = "output budget exceeded"
                            break
                    if failure:
                        break
                if not failure:
                    try:
                        process.wait(timeout=max(0.001, deadline - time.monotonic()))
                    except subprocess.TimeoutExpired:
                        failure = "timeout"
            finally:
                if process.poll() is None:
                    process.kill()
                process.wait()
                process.stdout.close()
                process.stderr.close()
    wall_ns = time.perf_counter_ns() - started
    return {"command": command, "pid": process.pid, "wall_ns": wall_ns,
            "exit_code": process.returncode, "failure": failure,
            "output_bytes": written, "stdout_file": str(stdout_file),
            "stderr_file": str(stderr_file), "stdout_sha256": sha256(stdout_file),
            "stderr_sha256": sha256(stderr_file)}


def read_counters(file_path, repeats):
    counters = []
    with file_path.open(encoding="utf-8") as source:
        for line in source:
            matched = STATUS.fullmatch(line.rstrip("\n"))
            if matched:
                counters.append({"shards": int(matched[1]), "open_mode": matched[2],
                                 "delta": matched[3], "logical_read_bytes": int(matched[4]),
                                 "fetched_bytes": int(matched[5])})
    if len(counters) != repeats:
        raise ValueError(f"expected {repeats} physical status lines, received {len(counters)}")
    return counters


def collection_hashes(collection, *, max_bytes=64 * 1024 * 1024, max_files=128):
    files = sorted(collection.rglob("*"))
    if len(files) > max_files or any(file_path.is_symlink() for file_path in files):
        raise ValueError("fixture collection must be small and contain no symbolic links")
    files = [file_path for file_path in files if file_path.is_file()]
    if sum(file_path.stat().st_size for file_path in files) > max_bytes:
        raise ValueError("fixture collection exceeds byte limit")
    if (collection / "CURRENT").read_text().strip() != "first":
        raise ValueError("known fixture collection must have CURRENT=first")
    if not (collection / "first/manifest.sbm2").is_file():
        raise ValueError("missing fixture generation manifest")
    return {str(file_path.relative_to(collection)): sha256(file_path) for file_path in files}


def bounded_number(lower, upper, integer=True):
    def parse(text):
        value = int(text) if integer else float(text)
        if not lower <= value <= upper or not math.isfinite(value):
            raise argparse.ArgumentTypeError(f"must be between {lower} and {upper}")
        return value
    return parse


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--subjects", type=bounded_number(10, 10000), default=1000)
    parser.add_argument("--repeat", type=bounded_number(1, 1000), default=20)
    parser.add_argument("--samples", type=bounded_number(1, 10), default=3)
    parser.add_argument("--timeout", type=bounded_number(0.1, 120, False), default=30)
    parser.add_argument("--total-timeout", type=bounded_number(1, 1800, False), default=300)
    parser.add_argument("--max-output-mib", type=bounded_number(1, 128), default=32)
    parser.add_argument("--total-output-mib", type=bounded_number(1, 512), default=128)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--reuse-dir", type=Path,
                        help="existing subjects-N directory with exact known fixture.ttl and collection/")
    args = parser.parse_args()
    if args.subjects % 10:
        parser.error("--subjects must be a multiple of ten")
    entries = workloads(args.subjects)
    output_limit = args.max_output_mib * 1024 * 1024
    total_limit = args.total_output_mib * 1024 * 1024
    expected_sizes = [(len(canonical(entry["expected"]).encode()) + 1) * args.repeat
                      for entry in entries]
    if max(expected_sizes) > output_limit or sum(expected_sizes) * (args.samples + 1) > total_limit:
        parser.error("expected complete answers exceed output budgets; reduce subjects/repeat/samples")
    binaries = {name: BIN / name for name in
                ("l4block-shard-pack", "l4block-shard-activate", "l4block-id-v3-query")}
    if any(not binary.is_file() for binary in binaries.values()):
        parser.error("native pack/activate/query binaries must already be built")
    directory = args.output_dir.resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix="factoidal-core-repeat-"))
    if directory.exists() and any(directory.iterdir()):
        parser.error("--output-dir must be absent or empty")
    directory.mkdir(parents=True, exist_ok=True)
    budget = Budget(total_limit, time.monotonic() + args.total_timeout)
    report = {
        "benchmark": "factoidal-core-complete-result-repeat-v1",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "host": {"platform": platform.platform(), "machine": platform.machine()},
        "toolchain": (ROOT / "formal/lean4/lean-toolchain").read_text().strip(),
        "driver_sha256": sha256(Path(__file__)), "subjects": args.subjects,
        "triples": args.subjects * 3, "repeat": args.repeat, "samples": args.samples,
        "warmup_processes_per_workload": 1, "arguments": vars(args) | {
            "output_dir": str(directory), "reuse_dir": str(args.reuse_dir) if args.reuse_dir else None},
        "binary_sha256": {name: sha256(binary) for name, binary in binaries.items()},
        "process_model": "Each sample is one native process with N repetitions. EVERY iteration performs fresh admission; NOT a pinned generation/session or shared decoded/chunk cache.",
        "timing_scope": "Process launch through exit and bounded stdout/stderr capture; includes repeated parsing/admission/authenticated reads/evaluation/full JSON serialization/transport. Fixture setup, hashing and complete-answer validation are excluded.",
        "cache_scope": "One excluded, fully validated warmup process per workload. OS page cache is not evicted; not disk-cold. Batch wall/N is amortized time, not individual-query latency.",
        "counter_scope": "Native logical/fetched artifact-range counters; NOT total disk IO (control files, Merkle sidecars, DLOG and failed speculative paths are not all counted).",
        "validation_scope": "Every complete NDJSON document, exact ordered bindings/duplicates/variables/term fields or exact COUNT/ASK. Known ASCII IRI/string fixture only; no bnode matching, RDF coercion, general semantic comparison or competitor parity claim.",
        "setup": [], "workloads": [], "all_checks_passed": False,
    }

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    def invoke(command, label):
        result = capture(command, directory, label, args.timeout, output_limit, budget)
        if result["failure"] or result["exit_code"]:
            report["failed_process"] = result
            raise ValueError(f"{label}: {result['failure'] or 'nonzero exit'} ({result['exit_code']})")
        return result

    try:
        fixture = fixture_bytes(args.subjects)
        fixture_directory = args.reuse_dir.resolve() if args.reuse_dir else directory
        fixture_file = fixture_directory / "fixture.ttl"
        collection = fixture_directory / "collection"
        if args.reuse_dir:
            if not fixture_file.is_file() or fixture_file.stat().st_size != len(fixture) or fixture_file.read_bytes() != fixture:
                raise ValueError("--reuse-dir fixture is not the exact generated corpus for --subjects")
        else:
            fixture_file.write_bytes(fixture)
            report["setup"].append(invoke([str(binaries["l4block-shard-pack"]), str(fixture_file),
                                           str(collection / "first"), "ibk3"], "pack"))
            report["setup"].append(invoke([str(binaries["l4block-shard-activate"]), str(collection),
                                           "first"], "activate"))
        report.update({"fixture_file": str(fixture_file), "fixture_bytes": len(fixture),
                       "fixture_sha256": hashlib.sha256(fixture).hexdigest(),
                       "collection": str(collection), "collection_sha256": collection_hashes(collection)})
        save()
        for entry in entries:
            measured = {"name": entry["name"], "query": entry["query"], "samples": []}
            report["workloads"].append(measured)
            for ordinal in range(args.samples + 1):
                label = f"{entry['name']}-{'warmup' if ordinal == 0 else ordinal}"
                print(f"start {label}", file=sys.stderr, flush=True)
                sample = invoke([str(binaries["l4block-id-v3-query"]), str(collection), "--json",
                                 "--repeat", str(args.repeat), "--query", entry["query"]], label)
                sample["validation_passed"] = False
                if ordinal == 0:
                    measured["excluded_warmup"] = sample
                else:
                    measured["samples"].append(sample)
                sample.update(validate_results(Path(sample["stdout_file"]), entry["expected"], args.repeat))
                sample["counters"] = read_counters(Path(sample["stderr_file"]), args.repeat)
                sample["amortized_ms"] = sample["wall_ns"] / args.repeat / 1_000_000
                sample["validation_passed"] = True
                print(f"pass {label} documents={sample['documents']} wall_ms={sample['wall_ns'] / 1_000_000:.3f}",
                      file=sys.stderr, flush=True)
                save()
            measured["median_process_ms"] = statistics.median(sample["wall_ns"] for sample in measured["samples"]) / 1_000_000
            measured["median_amortized_ms"] = measured["median_process_ms"] / args.repeat
        if collection_hashes(collection) != report["collection_sha256"] or sha256(fixture_file) != report["fixture_sha256"]:
            raise ValueError("fixture or collection changed during the run")
        if any(sha256(binaries[name]) != digest for name, digest in report["binary_sha256"].items()):
            raise ValueError("native binaries changed during the run")
        report["all_checks_passed"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    report["captured_output_bytes"] = total_limit - budget.remaining
    save()
    print(f"report={directory / 'report.json'} all_checks_passed={str(report['all_checks_passed']).lower()}")
    return 0 if report["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
