#!/usr/bin/env python3
"""Independent Python standard-library oracle for the actual Lean SSZ basic CLI.

The production implementation is pure Lean. Python's int.to_bytes/from_bytes,
not its transcribed arithmetic, supplies independent expected wire values.
No Python code or test digest is consulted by the Lean execution path.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import subprocess
import sys


class Mismatch(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Mismatch(message)


def ok_wire(wire):
    return {"status": "ok", "bytes": wire.hex(),
            "root": wire.ljust(32, b"\x00").hex()}


def failure(code):
    return {"status": "error", "error": code}


def case(op, payload, expected, label):
    return ({"op": op, **payload}, expected, label)


def cases():
    result = []
    edges = [0, 1, 2, 127, 128, 255, 256, 257, 65535,
             65536, 2**32 - 1, 2**32, 2**63 - 1, 2**63, 2**64 - 1]
    rng = random.Random(840_20261123)
    integers = edges + [rng.getrandbits(64) for _ in range(1200)]
    for idx, value in enumerate(integers):
        wire = value.to_bytes(8, "little")
        result.append(case("encode_u64", {"value": value}, ok_wire(wire),
                           f"encode_u64/{idx}"))
        result.append(case("decode_u64", {"bytes": list(wire)},
                           {"status": "ok", "value": str(value)},
                           f"decode_u64/{idx}"))
        if idx % 8 == 0:
            mutated = bytearray(wire)
            mutated[idx % 8] ^= 0x80
            changed = int.from_bytes(mutated, "little")
            result.append(case("decode_u64", {"bytes": list(mutated)},
                               {"status": "ok", "value": str(changed)},
                               f"decode_u64/mutated/{idx}"))
    for idx, value in enumerate([False, True] * 128):
        wire = bytes([int(value)])
        result.append(case("encode_bool", {"value": value}, ok_wire(wire),
                           f"encode_bool/{idx}"))
        result.append(case("decode_bool", {"bytes": list(wire)},
                           {"status": "ok", "value": value},
                           f"decode_bool/{idx}"))
    for raw in [2, 3, 127, 128, 254, 255]:
        result.append(case("decode_bool", {"bytes": [raw]},
                           failure("noncanonical_boolean"), f"noncanonical/{raw}"))
    for width in [0, 1, 2, 3, 7, 9, 16, 31, 32, 64]:
        if width != 8:
            result.append(case("decode_u64", {"bytes": [0] * width},
                               failure("invalid_length"), f"u64-width/{width}"))
        if width != 1:
            result.append(case("decode_bool", {"bytes": [0] * width},
                               failure("invalid_length"), f"bool-width/{width}"))
    for value in [2**64, 2**64 + 1, 2**128]:
        result.append(case("encode_u64", {"value": value},
                           failure("out_of_range"), f"range/{value}"))
    for op in ["decode_u64", "decode_bool"]:
        result.append(case(op, {"bytes": [0] * 65},
                           failure("resource_limit"), f"length_cap/{op}"))
        result.append(case(op, {"bytes": [0, 256]},
                           failure("invalid_byte"), f"bad-byte/{op}"))
    return result


def falsification_controls(expected):
    # A comparator which accepts these forged rows cannot support a claim.
    mutations = []
    changed = dict(expected)
    changed["status"] = "error"
    mutations.append(changed)
    changed = dict(expected)
    changed["root"] = "00" * 32
    mutations.append(changed)
    changed = dict(expected)
    changed["bytes"] = "ff"
    mutations.append(changed)
    return mutations


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary")
    parser.add_argument("--report")
    args = parser.parse_args()
    corpus = cases()
    wire = b"".join(
        json.dumps(request, separators=(",", ":")).encode() + b"\n"
        for request, _, _ in corpus
    )
    output = subprocess.run([args.binary], input=wire,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=180, check=False)
    require(output.returncode == 0,
            f"Lean CLI exit={output.returncode}, stderr={output.stderr[:1000]!r}")
    lines = output.stdout.splitlines()
    require(len(lines) == len(corpus),
            f"Lean returned {len(lines)} rows for {len(corpus)} inputs")
    counts = Counter()
    for idx, ((_, expected, label), line) in enumerate(zip(corpus, lines)):
        try:
            actual = json.loads(line)
        except (ValueError, UnicodeError) as exc:
            raise Mismatch(f"invalid JSON at {idx}/{label}: {exc}") from exc
        require(actual == expected,
                f"{idx}/{label}: actual {actual!r}, oracle {expected!r}")
        counts[label.split("/")[0]] += 1
    seed = corpus[0][1]
    for idx, wrong in enumerate(falsification_controls(seed)):
        require(wrong != seed, f"mutation {idx} failed to alter the expected output")
        require(json.loads(lines[0]) != wrong,
                f"mutation {idx} was accepted")
    report = {"cases": len(corpus), "matched": len(corpus), "mismatches": 0,
              "controls_detected": 3, "case_groups": dict(sorted(counts.items())),
              "lean_exit": output.returncode,
              "reference": "Python 3 int.to_bytes/from_bytes, bool canonical encoding"}
    if args.report:
        Path(args.report).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Mismatch, subprocess.TimeoutExpired) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
