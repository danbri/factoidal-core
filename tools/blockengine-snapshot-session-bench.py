#!/usr/bin/env python3
"""Paired fresh-admission and pinned-snapshot measurements; every answer checked.

No builds or ingestion. Snapshot admission is measured separately. The two
modes have different freshness and memory costs; this is no competitor claim.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import platform
import selectors
import statistics
import subprocess
import sys
import time

SPEC = importlib.util.spec_from_file_location(
    "repeat_driver", Path(__file__).with_name("blockengine-core-repeat.py"))
D = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(D)


class ClockWindow:
    """Reject >1 second wall/uptime divergence, including macOS suspend.

    perf_counter excludes system sleep on macOS. Its elapsed values alone
    can hide a long pause while a competitor's query timeout keeps running.
    Clock steps also invalidate this conservative window check.
    """
    def __init__(self, wall=None, uptime=None):
        self.wall = wall or time.time_ns
        self.uptime = uptime or time.perf_counter_ns
        self.start_wall = self.wall()
        self.start_uptime = self.uptime()

    def check(self):
        wall_elapsed = self.wall() - self.start_wall
        uptime_elapsed = self.uptime() - self.start_uptime
        skew = wall_elapsed - uptime_elapsed
        if abs(skew) > 1_000_000_000 or wall_elapsed < 0 or uptime_elapsed < 0:
            raise ValueError(f"clock discontinuity: wall={wall_elapsed} ns "
                             f"uptime={uptime_elapsed} ns skew={skew} ns")
        return {"wall_elapsed_ns": wall_elapsed, "uptime_elapsed_ns": uptime_elapsed,
                "clock_skew_ns": skew, "tolerance_ns": 1_000_000_000}


class Process:
    def __init__(self, command, log, timeout):
        self.log = log.open("wb")
        self.proc = subprocess.Popen(list(map(str, command)), stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=self.log, bufsize=0)
        self.timeout = timeout
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)

    def line(self):
        deadline = time.monotonic() + self.timeout
        chunks, size = [], 0
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not self.selector.select(timeout=remaining):
                raise ValueError("native response timed out")
            chunk = os.read(self.proc.stdout.fileno(), 1024 * 1024)
            if not chunk:
                raise ValueError("native process ended before a complete response")
            size += len(chunk)
            if size > 64 * 1024 * 1024:
                raise ValueError("native response exceeded 64 MiB")
            chunks.append(chunk)
            if b"\n" in chunk:
                if chunk.count(b"\n") != 1 or not chunk.endswith(b"\n"):
                    raise ValueError("extra stdout frame")
                return b"".join(chunks)

    def request(self, query):
        self.proc.stdin.write(json.dumps(query).encode() + b"\n")
        self.proc.stdin.flush()
        return self.line()

    def close(self):
        try:
            self.proc.stdin.close()
            if self.proc.wait(timeout=10):
                raise ValueError("native process returned nonzero")
            if self.proc.stdout.read(1):
                raise ValueError("unexpected extra stdout")
        finally:
            if self.proc.poll() is None:
                self.proc.kill()
                self.proc.wait()
            self.proc.stdout.close()
            self.selector.close()
            self.log.close()


def cpu_snapshot():
    return subprocess.check_output(["ps", "-A", "-o", "pid,pcpu,comm"], text=True,
                                   timeout=10).splitlines()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture-dir", required=True, type=Path)
    parser.add_argument("--subjects", required=True, type=D.bounded_number(10, 100000))
    parser.add_argument("--samples", default=3, type=D.bounded_number(1, 10))
    parser.add_argument("--timeout", default=120, type=D.bounded_number(1, 120, False))
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--workload", action="append", choices=[w["name"] for w in D.workloads(10)],
                        help="Measure only these workloads (repeatable); default: all nine")
    args = parser.parse_args()
    fixture = args.fixture_dir.resolve() / "fixture.ttl"
    collection = args.fixture_dir.resolve() / "collection"
    directory = args.output_dir.resolve()
    if not fixture.is_file() or fixture.read_bytes() != D.fixture_bytes(args.subjects):
        parser.error("fixture must exactly match --subjects")
    if directory.exists() and any(directory.iterdir()):
        parser.error("output directory must be absent or empty")
    directory.mkdir(parents=True, exist_ok=True)
    binaries = {name: D.BIN / name for name in ("l4block-id-v3-query", "l4block-snapshot-session")}
    hashes = {name: D.sha256(path) for name, path in binaries.items()}
    artifacts = D.collection_hashes(collection)
    clock = ClockWindow()
    report = {
        "benchmark": "shardborough-pinned-snapshot-v1", "all_checks_passed": False,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "host": platform.platform(), "machine": platform.machine(), "cpu_count": os.cpu_count(),
        "subjects": args.subjects, "triples": args.subjects * 3, "samples": args.samples,
        "selected_workloads": args.workload,
        "fixture_sha256": D.sha256(fixture), "collection_sha256": artifacts,
        "binary_sha256": hashes, "driver_sha256": D.sha256(Path(__file__)),
        "oracle_driver_sha256": D.sha256(Path(D.__file__)),
        "source_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=D.ROOT,
                                               text=True, timeout=10).strip(),
        "toolchain": (D.ROOT / "formal/lean4/lean-toolchain").read_text().strip(),
        "scope": "Fresh CLI startup/admission/evaluation/full stdout versus already-open snapshot JSONL request/evaluation/full stdout. OS cache retained. One warmup per workload per mode; alternating order. Parse/validation and output-file writes are outside timing. Session admission/indexing measured separately. No competitor timings.",
        "freshness": "CLI resolves CURRENT and DLOG on every call. Session pins both once and keeps the full graph and indexes in RAM until exit.",
        "validation": "Every full ordered answer, including warmups, equals independent generated JSON with exact RDF term fields, variable headers, multiplicities and row positions.",
        "cpu_before": cpu_snapshot(), "workloads": [],
    }

    def save():
        (directory / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    session = None
    save()
    try:
        started = time.perf_counter_ns()
        session = Process([binaries["l4block-snapshot-session"], collection],
                          directory / "session.stderr", args.timeout)
        ready_raw = session.line()
        report["snapshot_open_ns"] = time.perf_counter_ns() - started
        (directory / "ready.json").write_bytes(ready_raw)
        ready = json.loads(ready_raw, object_pairs_hook=D.unique_keys, parse_constant=D.reject_constant)
        if (ready.get("ready"), ready.get("triples"), ready.get("admissions"), ready.get("index-builds")) != (True, args.subjects * 3, 1, 1):
            raise ValueError("unexpected snapshot admission")
        report["snapshot_ready"] = ready
        report["snapshot_rss_after_ready_kib"] = int(subprocess.check_output(
            ["ps", "-o", "rss=", "-p", str(session.proc.pid)], text=True, timeout=10).strip())
        for workload in D.workloads(args.subjects):
            if args.workload and workload["name"] not in args.workload:
                continue
            entry = {"name": workload["name"], "query": workload["query"],
                     "samples": {"fresh": [], "snapshot": []}, "warmups": {}}
            report["workloads"].append(entry)
            for ordinal in range(args.samples + 1):
                modes = ["fresh", "snapshot"] if ordinal % 2 == 0 else ["snapshot", "fresh"]
                for mode in modes:
                    label = f"{workload['name']}-{ordinal}-{mode}"
                    print(f"start subjects={args.subjects} {label}", file=sys.stderr, flush=True)
                    started = time.perf_counter_ns()
                    if mode == "snapshot":
                        raw = session.request(workload["query"])
                    else:
                        fresh = Process([binaries["l4block-id-v3-query"], collection,
                                         "--json", "--query", workload["query"]],
                                        directory / f"{label}.stderr", args.timeout)
                        try:
                            raw = fresh.line()
                        finally:
                            fresh.close()
                    wall = time.perf_counter_ns() - started
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
            entry["fresh_over_snapshot"] = entry["median_ms"]["fresh"] / entry["median_ms"]["snapshot"]
            save()
        if D.collection_hashes(collection) != artifacts or any(D.sha256(path) != hashes[name] for name, path in binaries.items()):
            raise ValueError("collection or binary changed during measurement")
        report["all_checks_passed"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    finally:
        if session:
            try:
                session.close()
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                report["all_checks_passed"] = False
                report["shutdown_error"] = str(error)
        try:
            report["clock_check"] = clock.check()
        except ValueError as error:
            report["all_checks_passed"] = False
            report["clock_error"] = str(error)
        report["cpu_after"] = cpu_snapshot()
        save()
    print(f"report={directory / 'report.json'} all_checks_passed={report['all_checks_passed']}")
    return 0 if report["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
