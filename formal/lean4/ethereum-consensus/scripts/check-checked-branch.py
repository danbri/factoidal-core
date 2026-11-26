#!/usr/bin/env python3
"""Independent branch-policy and ordered-fold reference for the real Lean CLI.

Normative policy: ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1
src/ssz/gindex.py: gindex_length rejects 0 and root 1. Pairing here is a
deliberately non-cryptographic arithmetic test function, not SHA-256.
"""
import sys


def expected(index: int) -> tuple[int, int]:
    if index < 2:
        return -1, -1
    depth = index.bit_length() - 1
    value = 7
    step = index
    for _ in range(depth):
        if step & 1:
            value = 5 * 3 + value
        else:
            value = 5 * value + 3
        step >>= 1
    assert step == 1, (index, step)
    return depth, value


# A few fixed specification-policy controls independent of generated rows.
for index, wanted in [(0, -1), (1, -1), (2, 1), (3, 1), (9, 3)]:
    assert expected(index)[0] == wanted

observed = 0
refused = 0
for line in sys.stdin:
    fields = line.rstrip("\n").split("\t")
    assert len(fields) == 4, ("malformed row", observed, line)
    index, length, result, bad_result = map(int, fields)
    assert index == observed, ("index continuity", index, observed)
    wanted_length, wanted_result = expected(index)
    assert length == wanted_length, (index, length, wanted_length)
    assert result == wanted_result, (index, result, wanted_result)
    assert bad_result == -1, ("incorrect-length branch admitted", index, bad_result)
    refused += result == -1
    observed += 1

assert observed == 1025, ("incomplete Lean stream", observed)
assert refused == 2, ("zero/root refusal", refused)
print(
    f"SSZ checked-branch oracle: {observed} Lean rows matched; "
    "2 index refusals and 1025 malformed-length refusals; "
    "arithmetic pairing only, no SHA-256 or complete SSZ conformance"
)
