#!/usr/bin/env python3
"""Ratchet for the beacon-chain vector runner.

Reads the JSON written by `beacon-spec-tests --json` and compares it, handler
by handler, with the committed baseline for the same preset. The run fails
when a handler is missing, its case count differs from the baseline (cases
may not silently disappear), its pass count is lower, or its fail or
unsupported count is higher, or fewer cases ran in signature-verification mode.
Reject duplicate handlers, inconsistent count partitions, wrong fork metadata
and BLS class drift. The signatures_checked field is a case-mode flag, not
a count of actual cryptographic calls.
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


BLS_CLASSES = ("bls_required", "bls_off", "bls_optional")


def validate_counts(name, h):
    if any(type(h[k]) is not int or h[k] < 0 for k in KEYS):
        raise ValueError(f"{name}: nonnegative integer counts required")
    if h["total"] != h["pass"] + h["fail"] + h["unsupported"]:
        raise ValueError(f"{name}: inconsistent status counts")
    if h["total"] != sum(h[k] for k in BLS_CLASSES):
        raise ValueError(f"{name}: inconsistent BLS class counts")
    if h["pass"] != sum(h[k + "_pass"] for k in BLS_CLASSES):
        raise ValueError(f"{name}: inconsistent BLS pass counts")
    if any(h[k + "_pass"] > h[k] for k in BLS_CLASSES):
        raise ValueError(f"{name}: BLS pass count exceeds class count")
    if h["signatures_checked"] > h["total"] - h["bls_off"]:
        raise ValueError(f"{name}: verification-mode count exceeds eligible cases")



PAYLOAD_KEYS = ("payload_control_passed", "payload_control_failed",
                "payload_decode_refused", "payload_control_not_reached")


def validate_payload_coverage(name, h):
    if any(type(h[k]) is not int or h[k] < 0 for k in PAYLOAD_KEYS):
        raise ValueError(f"{name}: nonnegative integer payload control counts required")
    passed, failed, refused, not_reached = (h[k] for k in PAYLOAD_KEYS)
    if passed + failed + refused + not_reached != h["total"]:
        raise ValueError(f"{name}: inconsistent payload control partition")
    if name == "operations/execution_payload":
        if failed or not_reached or not passed:
            raise ValueError(f"{name}: failed, missing or vacuous payload control evidence")
    elif passed or failed or refused:
        raise ValueError(f"{name}: unexpected payload control evidence")


def summarise(run):
    if (run["fork"] != "fulu" or run["preset"] not in ("minimal", "mainnet")
            or type(run["optional_bls_verified"]) is not bool):
        raise ValueError("unexpected fork, preset or BLS verification mode")
    current = {}
    for h in run["handlers"]:
        if any(not isinstance(h[k], str) or not h[k] or "/" in h[k]
               for k in ("runner", "handler")):
            raise ValueError("invalid handler identity")
        name = f'{h["runner"]}/{h["handler"]}'
        if name in current:
            raise ValueError(f"{name}: duplicate handler")
        counts = {k: h[k] for k in KEYS}
        validate_counts(name, counts)
        validate_payload_coverage(name, h)
        current[name] = counts
    if not current:
        raise ValueError("empty handler inventory")
    return current


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
        validate_counts(name, want)
        validate_counts(name, got)
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
        for key in BLS_CLASSES:
            if got[key] != want[key]:
                problems.append(f"{name}: {key} count differs from baseline")
            if got[key + "_pass"] < want[key + "_pass"]:
                problems.append(f"{name}: {key} pass count below baseline")
    for name in current:
        if name not in baseline:
            problems.append(f"{name}: handler not in the baseline (add it with --update)")
    return problems


def self_test():
    import copy
    row = dict.fromkeys(KEYS, 0) | {"runner": "a", "handler": "b", "total": 3, "pass": 3,
                                    "bls_required": 2, "bls_required_pass": 2,
                                    "bls_optional": 1, "bls_optional_pass": 1,
                                    "signatures_checked": 3,
                                    "payload_control_passed": 0, "payload_control_failed": 0,
                                    "payload_decode_refused": 0, "payload_control_not_reached": 3}
    run = {"fork": "fulu", "preset": "minimal", "optional_bls_verified": True, "handlers": [row]}
    base = summarise(run)
    assert compare(base, base) == []
    controls = 0
    for changes in ({"pass": 2, "fail": 1, "bls_required_pass": 1},
                    {"pass": 2, "unsupported": 1, "bls_required_pass": 1},
                    {"total": 2, "pass": 2, "bls_required": 1, "bls_required_pass": 1, "signatures_checked": 2,
                     "payload_control_not_reached": 2},
                    {"signatures_checked": 0},
                    {"bls_required": 1, "bls_required_pass": 1, "bls_optional": 2, "bls_optional_pass": 2}):
        bad = copy.deepcopy(run)
        bad["handlers"][0].update(changes)
        assert compare(summarise(bad), base), changes
        controls += 1
    # Same total and total passes, but passing BLS-required cases decline.
    partial = copy.deepcopy(run)
    partial["handlers"][0].update({"pass": 2, "fail": 1, "bls_optional_pass": 0})
    shifted = copy.deepcopy(partial)
    shifted["handlers"][0].update({"bls_optional_pass": 1, "bls_required_pass": 1})
    assert compare(summarise(shifted), summarise(partial))
    controls += 1
    assert compare({}, base)
    assert compare(base | {"c/d": base["a/b"]}, base)
    controls += 2
    malformed = [run | {"handlers": [row, row]}, run | {"handlers": []},
                 run | {"fork": "deneb"}, run | {"preset": "other"},
                 run | {"optional_bls_verified": 1}]
    for changes in ({"total": True}, {"fail": -1}, {"pass": 2}, {"bls_off": 1},
                    {"bls_optional_pass": 0}, {"bls_optional_pass": 2, "bls_required_pass": 1},
                    {"signatures_checked": 4}, {"handler": "b/c"}):
        malformed.append(run | {"handlers": [row | changes]})
    for bad in malformed:
        try:
            summarise(bad)
        except ValueError:
            controls += 1
        else:
            raise AssertionError(f"malformed evidence accepted: {bad}")
    # The control runs on decoded operations; refused SSZ is distinct.
    payload = row | {"runner": "operations", "handler": "execution_payload",
                     "payload_control_passed": 2, "payload_decode_refused": 1,
                     "payload_control_not_reached": 0}
    summarise(run | {"handlers": [payload]})
    for changes in ({"payload_control_passed": 0, "payload_decode_refused": 3},
                    {"payload_control_passed": 1, "payload_control_failed": 1},
                    {"payload_control_passed": 1, "payload_control_not_reached": 1},
                    {"payload_control_passed": 3}, {"payload_control_passed": True},
                    {"payload_control_passed": -1},
                    {"runner": "unrelated"}):
        try:
            summarise(run | {"handlers": [payload | changes]})
        except ValueError:
            controls += 1
        else:
            raise AssertionError(f"invalid control coverage accepted: {changes}")
    missing = dict(payload)
    del missing["payload_control_passed"]
    try:
        summarise(run | {"handlers": [missing]})
    except KeyError:
        controls += 1
    else:
        raise AssertionError("missing payload control evidence accepted")
    print(f"ratchet self-test: {controls} negative controls behaved")

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
    for h in run["handlers"]:
        if h["runner"] == "operations" and h["handler"] == "execution_payload":
            text += ("\nExecution payload control coverage: " +
                     ", ".join(f"{k}={h[k]}" for k in PAYLOAD_KEYS) + "\n")
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
