#!/usr/bin/env python3
"""Ratchet for the beacon-chain vector runner.

Reads the JSON written by `beacon-spec-tests --json` and compares it, handler
by handler, with the committed baseline for the same preset. The run fails
when a handler is missing, its case count differs from the baseline (cases
may not silently disappear), its pass count is lower, or its fail or
unsupported count is higher, or fewer cases ran with real signature checks.
`--update` rewrites the baseline entry from the run (only ever done by hand,
in a commit that says why).

The vectors are a test oracle. This script reads counts; it never supplies
an expected answer to the runner.
"""
import argparse
import json
import pathlib
import sys

KEYS = ("total", "pass", "fail", "unsupported", "bls_required", "bls_required_pass",
        "bls_off", "bls_off_pass", "bls_optional", "bls_optional_pass", "signatures_checked")


def summarise(run):
    return {f'{h["runner"]}/{h["handler"]}': {k: h[k] for k in KEYS} for h in run["handlers"]}


def table(run):
    rows = ["| handler | total | pass | fail | unsupported | BLS required (pass) | BLS off (pass) | "
            "BLS optional (pass) | p50 ms | p95 ms | max ms |",
            "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for h in run["handlers"]:
        rows.append(
            f'| {h["runner"]}/{h["handler"]} | {h["total"]} | {h["pass"]} | {h["fail"]} | {h["unsupported"]} '
            f'| {h["bls_required"]} ({h["bls_required_pass"]}) | {h["bls_off"]} ({h["bls_off_pass"]}) '
            f'| {h["bls_optional"]} ({h["bls_optional_pass"]}) '
            f'| {h["p50_us"] / 1000:.1f} | {h["p95_us"] / 1000:.1f} | {h["max_us"] / 1000:.1f} |')
    total = {k: sum(h[k] for h in run["handlers"]) for k in ("total", "pass", "fail", "unsupported")}
    rows.append(f'| **all** | {total["total"]} | {total["pass"]} | {total["fail"]} | {total["unsupported"]} '
                '| | | | | | |')
    return "\n".join(rows)


def compare(current, baseline):
    problems = []
    for name, want in baseline.items():
        got = current.get(name)
        if got is None:
            problems.append(f"{name}: handler missing from the run")
            continue
        if got["total"] != want["total"]:
            problems.append(f'{name}: {got["total"]} cases, baseline has {want["total"]}')
        if got["pass"] < want["pass"]:
            problems.append(f'{name}: pass {got["pass"]} below baseline {want["pass"]}')
        if got["fail"] > want["fail"]:
            problems.append(f'{name}: fail {got["fail"]} above baseline {want["fail"]}')
        if got["unsupported"] > want["unsupported"]:
            problems.append(f'{name}: unsupported {got["unsupported"]} above baseline {want["unsupported"]}')
        if got["signatures_checked"] < want["signatures_checked"]:
            problems.append(f'{name}: signatures checked in {got["signatures_checked"]} cases, '
                            f'baseline {want["signatures_checked"]}')
    for name in current:
        if name not in baseline:
            problems.append(f"{name}: handler not in the baseline (add it with --update)")
    return problems


def self_test():
    base = {"a/b": dict.fromkeys(KEYS, 0) | {"total": 3, "pass": 3, "signatures_checked": 3}}
    same = json.loads(json.dumps(base))
    assert compare(same, base) == []
    for key, value in (("pass", 2), ("fail", 1), ("unsupported", 1), ("total", 2), ("signatures_checked", 0)):
        bad = json.loads(json.dumps(base))
        bad["a/b"][key] = value
        assert compare(bad, base), key
    assert compare({}, base)
    assert compare(base | {"c/d": base["a/b"]}, base)
    print("ratchet self-test: 8 controls behaved")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run")
    ap.add_argument("--baseline")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--summary")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return 0
    run = json.loads(pathlib.Path(args.run).read_text())
    current = summarise(run)
    key = run["preset"] + ("" if run["optional_bls_verified"] else "+optional-bls-skipped")
    path = pathlib.Path(args.baseline)
    doc = json.loads(path.read_text()) if path.exists() else {"presets": {}}
    text = f'### Beacon vectors, {run["preset"]} preset, {run["fork"]}\n\n{table(run)}\n'
    print(text)
    if args.summary:
        with open(args.summary, "a") as out:
            out.write(text + "\n")
    for h in run["handlers"]:
        for case in h["not_passing"]:
            print(f'NOT PASSING {h["runner"]}/{h["handler"]} {case["case"]}: {case["status"]}: {case["detail"]}')
    if args.update:
        doc["presets"][key] = current
        path.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")
        print(f"baseline for {key} written")
        return 0
    if key not in doc["presets"]:
        print(f"no baseline for {key}")
        return 1
    problems = compare(current, doc["presets"][key])
    for problem in problems:
        print("RATCHET:", problem)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
