#!/usr/bin/env python3
"""Independent oracle for four fixed consensus SSZ container codecs and roots.

The production executable is pure Lean. Only this test process uses Python's
hashlib and direct bytes packing, with a separate bottom-up Merkle algorithm.
No third-party package or reference-client runtime is involved.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys


def require(condition, reason):
    if not condition:
        raise AssertionError(reason)


def merkle(leaves):
    require(leaves and all(len(x) == 32 for x in leaves), "invalid oracle tree")
    count = 1 << (len(leaves) - 1).bit_length()
    level = list(leaves) + [bytes(32)] * (count - len(leaves))
    while len(level) > 1:
        level = [hashlib.sha256(a + b).digest()
                 for a, b in zip(level[::2], level[1::2])]
    return level[0]


def u64(value):
    return value.to_bytes(8, "little")


def basic(value):
    return value.ljust(32, b"\0")


def make_case(op, **fields):
    request = {"op": op, **fields}
    if op == "beacon_header":
        slot = u64(fields["slot"])
        proposer = u64(fields["proposer_index"])
        parent = bytes.fromhex(fields["parent_root"])
        state = bytes.fromhex(fields["state_root"])
        body = bytes.fromhex(fields["body_root"])
        wire = slot + proposer + parent + state + body
        root = merkle([basic(slot), basic(proposer), parent, state, body])
    elif op == "checkpoint":
        epoch = u64(fields["epoch"])
        point = bytes.fromhex(fields["root"])
        wire = epoch + point
        root = merkle([basic(epoch), point])
    elif op == "fork_data":
        version = bytes.fromhex(fields["current_version"])
        genesis = bytes.fromhex(fields["genesis_validators_root"])
        wire = version + genesis
        root = merkle([basic(version), genesis])
    elif op == "signing_data":
        obj = bytes.fromhex(fields["object_root"])
        domain = bytes.fromhex(fields["domain"])
        wire = obj + domain
        root = merkle([obj, domain])
    else:
        raise AssertionError(op)
    return request, {"status": "ok", "bytes": wire.hex(), "root": root.hex()}


def invalid(request, code):
    return request, {"status": "error", "error": code}


def corpus():
    rng = random.Random(84420261123)
    cases = []
    edge = [0, 1, 255, 256, 2**32, 2**63, 2**64 - 1]
    zeros = bytes(32)
    for j in range(400):
        slot = edge[j % len(edge)] if j < 70 else rng.getrandbits(64)
        proposer = edge[(j + 3) % len(edge)] if j < 70 else rng.getrandbits(64)
        fields = [zeros if j % 13 == k else rng.randbytes(32) for k in (0, 1, 2)]
        req, expected = make_case(
            "beacon_header", slot=slot, proposer_index=proposer,
            parent_root=fields[0].hex(), state_root=fields[1].hex(),
            body_root=fields[2].hex())
        cases.append((req, expected, f"header/{j}"))
    for j in range(350):
        epoch = edge[j % len(edge)] if j < 70 else rng.getrandbits(64)
        leaf = zeros if j % 9 == 0 else rng.randbytes(32)
        req, exp = make_case("checkpoint", epoch=epoch, root=leaf.hex())
        cases.append((req, exp, f"checkpoint/{j}"))
    for j in range(350):
        version = bytes(4) if j % 17 == 0 else rng.randbytes(4)
        genesis = zeros if j % 11 == 0 else rng.randbytes(32)
        req, exp = make_case(
            "fork_data", current_version=version.hex(),
            genesis_validators_root=genesis.hex())
        cases.append((req, exp, f"fork/{j}"))
    for j in range(350):
        obj = zeros if j % 7 == 0 else rng.randbytes(32)
        domain = zeros if j % 13 == 0 else rng.randbytes(32)
        req, exp = make_case(
            "signing_data", object_root=obj.hex(), domain=domain.hex())
        cases.append((req, exp, f"signing/{j}"))
    for op, req in [
        ("beacon_header", {"slot": 0, "proposer_index": 0, "parent_root": "00"*31,
                           "state_root": "00"*32, "body_root": "00"*32}),
        ("beacon_header", {"slot": 0, "proposer_index": 0, "parent_root": "00"*32,
                           "state_root": "00"*33, "body_root": "00"*32}),
        ("checkpoint", {"epoch": 0, "root": "00"*33}),
        ("checkpoint", {"epoch": 2**64, "root": "00"*32}),
        ("fork_data", {"current_version": "00"*3,
                       "genesis_validators_root": "00"*32}),
        ("fork_data", {"current_version": "00"*4,
                       "genesis_validators_root": "00"*31}),
        ("signing_data", {"object_root": "gg"*32, "domain": "00"*32}),
        ("signing_data", {"object_root": "00"*32, "domain": "00"*30}),
    ]:
        code = ("out_of_range" if req.get("epoch", 0) == 2**64 else
                "invalid_hex" if "gg" in str(req) else "invalid_width")
        cases.append(invalid({"op": op, **req}, code) + (f"invalid/{op}",))
    cases.append(invalid({"op": "unknown"}, "unknown_operation") + ("unknown",))
    cases.append(invalid({"op": "checkpoint", "epoch": 0, "root": "00"*32,
                          "extra": 0}, "parse_error") + ("extra-field",))
    cases.append(invalid({"op": "checkpoint", "epoch": 0},
                         "parse_error") + ("missing-field",))
    return cases


def check_one(actual, expected, label):
    require(actual == expected, f"{label}: Lean={actual!r}, oracle={expected!r}")


def execute(binary, cases):
    wire = b"".join(json.dumps(request, separators=(",", ":")).encode() + b"\n"
                    for request, _, _ in cases)
    output = subprocess.run(
        [binary], input=wire, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=180, check=False)
    require(output.returncode == 0,
            f"native process returned {output.returncode}: {output.stderr[:2000]!r}")
    lines = output.stdout.splitlines()
    require(len(lines) == len(cases),
            f"native process returned {len(lines)} responses for {len(cases)} requests")
    categories = Counter()
    for (request, expected, label), line in zip(cases, lines):
        try:
            actual = json.loads(line)
        except ValueError as error:
            raise AssertionError(f"{label}: bad native JSON: {line[:120]!r}") from error
        check_one(actual, expected, label)
        categories[label.split("/")[0]] += 1
    for corrupt_key, corrupt_value in [
        ("status", "error"), ("root", "ff" * 32), ("bytes", "00")
    ]:
        good = cases[0][1]
        forged = dict(good)
        forged[corrupt_key] = corrupt_value
        require(forged != good, "mutation did not change expected result")
        try:
            check_one(forged, good, f"mutant/{corrupt_key}")
        except AssertionError:
            pass
        else:
            raise AssertionError(f"mutated {corrupt_key} wrongly accepted")
    return dict(sorted(categories.items()))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary")
    parser.add_argument("--report")
    args = parser.parse_args()
    cases = corpus()
    counts = execute(args.binary, cases)
    report = {
        "total": len(cases), "passed": len(cases), "failed": 0,
        "unsupported": 0, "not_run": 0,
        "comparator_mutations_detected": 3,
        "groups": counts,
        "reference": "independent standard-library byte packing and hashlib tree",
        "scope": "four fixed-shape SSZ beacon container roots, not authenticated consensus"
    }
    if args.report:
        Path(args.report).write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
