#!/usr/bin/env python3
"""Independent arithmetic reference for Ethereum consensus SSZ gindex helpers.

This does not test SHA-256 or beacon consensus. Reads the ACTUAL Lean CLI.
"""
import sys

seen = 0
for line in sys.stdin:
    cols = line.strip().split()
    if len(cols) != 4:
        raise AssertionError(f"bad output row: {line!r}")
    index, parent, sibling, depth = map(int, cols)
    assert index == seen, (index, seen)
    assert parent == index // 2, (index, parent)
    expected_sibling = (index ^ 1) if index > 0 else 1
    assert sibling == expected_sibling, (index, sibling, expected_sibling)
    expected_depth = max(index.bit_length() - 1, 0)
    assert depth == expected_depth, (index, depth, expected_depth)
    seen += 1

assert seen == 1025, seen
print(f"SSZ generalized-index oracle: {seen} rows matched, including index-zero refusal boundary; no hash/consensus claim")
