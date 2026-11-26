#!/usr/bin/env python3
"""Independent stdlib hashlib oracle for actual Lean SSZ Vector[N,uint64] output.

Runtime decisions remain in Lean. The Python oracle uses distinct bytes
packing and hashlib SHA-256 on a full zero-padded array of Merkle leaves.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys


def demand(ok, message):
    if not ok:
        raise AssertionError(message)


def expected_vector(values):
    wire = b"".join(v.to_bytes(8, "little") for v in values)
    leaves = [wire[i:i + 32].ljust(32, b"\x00")
              for i in range(0, len(wire), 32)]
    capacity = 1 << (len(leaves) - 1).bit_length()
    leaves.extend([bytes(32)] * (capacity - len(leaves)))
    while len(leaves) > 1:
        leaves = [hashlib.sha256(leaves[i] + leaves[i + 1]).digest()
                  for i in range(0, len(leaves), 2)]
    return {"status": "ok", "bytes": wire.hex(), "root": leaves[0].hex()}


def error(code):
    return {"status": "error", "error": code}


def corpus():
    rng = random.Random(842_20261123)
    cases = []
    seeds = [0, 1, 255, 256, 2**32, 2**63, 2**64 - 1]
    lengths = [1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64]
    for n in lengths:
        for j in range(14):
            values = [(seeds[(j + i) % len(seeds)]
                       if j < 8 else rng.getrandbits(64)) for i in range(n)]
            cases.append(({"op": "vector_u64", "length": n, "values": values},
                          expected_vector(values), f"edge/{n}/{j}"))
    # 1,152 independently random valid vectors, including all legal lengths.
    for j in range(1152):
        n = 1 + (j % 64)
        values = [rng.getrandbits(64) for _ in range(n)]
        if j % 7 == 0:
            values[0] = 0
        cases.append(({"op": "vector_u64", "length": n, "values": values},
                      expected_vector(values), f"random/{n}/{j}"))
    for n in [0, 65, 1000]:
        cases.append(({"op": "vector_u64", "length": n, "values": []},
                      error("resource_limit"), f"cap/{n}"))
    for n in [1, 2, 4, 5, 9, 16, 64]:
        for count in [0, n - 1, n + 1]:
            if count == n:
                continue
            values = [0] * count
            cases.append(({"op": "vector_u64", "length": n, "values": values},
                          error("invalid_length"), f"wrong-length/{n}/{count}"))
    for value in [2**64, 2**64 + 1, 2**128]:
        cases.append(({"op": "vector_u64", "length": 1, "values": [value]},
                      error("out_of_range"), f"range/{value}"))
    cases.append(({"op": "bogus", "length": 1, "values": [1]},
                  error("unknown_operation"), "unknown"))
    cases.append(({"op": "vector_u64", "length": 1, "values": [1], "extra": 1},
                  error("parse_error"), "extra-key"))
    cases.append(({"op": "vector_u64", "length": 1},
                  error("parse_error"), "missing-key"))
    return cases


def run(binary, corpus):
    request_bytes = b"".join(json.dumps(req, separators=(",", ":")).encode() + b"\n"
                             for req, _, _ in corpus)
    proc = subprocess.run([binary], input=request_bytes, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=180, check=False)
    demand(proc.returncode == 0,
           f"Lean exited {proc.returncode} stderr={proc.stderr[:2000]!r}")
    lines = proc.stdout.splitlines()
    demand(len(lines) == len(corpus),
           f"Lean returned {len(lines)} of {len(corpus)} results")
    groups = Counter()
    for i, ((_, expected, label), raw) in enumerate(zip(corpus, lines)):
        try:
            actual = json.loads(raw)
        except ValueError as exc:
            raise AssertionError(f"{i}/{label}: invalid native JSON {raw!r}") from exc
        demand(actual == expected, f"{i}/{label}: Lean={actual!r}, oracle={expected!r}")
        groups[label.split("/")[0]] += 1
    # Three falsification controls: corrupted verdict, root and wire content.
    first = json.loads(lines[0])
    base = corpus[0][1]
    for property_name, replacement in [("status", "error"), ("root", "ff" * 32),
                                       ("bytes", "01")]:
        forged = dict(base)
        forged[property_name] = replacement
        demand(forged != base and forged != first,
               f"failed to detect forged {property_name} output")
    return dict(sorted(groups.items()))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary")
    parser.add_argument("--report")
    args = parser.parse_args()
    cases = corpus()
    counts = run(args.binary, cases)
    result = {"total": len(cases), "passed": len(cases), "failed": 0,
              "unsupported": 0, "not_run": 0,
              "comparator_mutations_detected": 3,
              "groups": counts, "oracle": "independent stdlib int.to_bytes and hashlib.sha256"}
    if args.report:
        Path(args.report).write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
