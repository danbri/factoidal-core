#!/usr/bin/env python3
"""SSZ helper indices: independent bit-walk oracle, 2048 Lean-emitted rows.

Normative pin: ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1,
src/ssz/gindex.py. The Lean emitter chooses inputs; this script computes
expected output from scratch. This verifies neither hash bytes nor root values.
"""
import sys


def expected(claims: list[int], claim_cap: int = 4, depth_cap: int = 64):
    if len(claims) > claim_cap:
        return None
    if any(n.bit_length() - 1 > depth_cap for n in claims):
        return None
    if not claims or any(n < 2 for n in claims):
        return None
    positions = set(claims)
    if len(positions) != len(claims):
        return None

    for index in claims:
        ancestor = index >> 1
        while ancestor > 1:
            if ancestor in positions:
                return None
            ancestor >>= 1

    paths = set()
    siblings = set()
    for index in claims:
        cursor = index
        while cursor > 1:
            paths.add(cursor)
            siblings.add(cursor ^ 1)
            cursor >>= 1
    return sorted(siblings - paths, reverse=True)


def representation(result):
    if result is None:
        return "reject"
    return "ok:" + ",".join(map(str, result))


def agrees(claims, observed):
    return representation(expected(claims)) == observed


# Adversarial comparator mutation controls: ordering, omission, and a
# malformed-request acceptance must each be detected.
assert expected([4]) == [5, 3]
assert expected([4, 5]) == [3]
assert expected([4, 6]) == [7, 5]
assert expected([2, 3]) == []
assert expected([2, 4]) is None
assert expected([1]) is None
assert expected([0]) is None
assert expected([2, 2]) is None
assert expected([2**65]) is None
assert expected([2, 3, 4, 5, 6]) is None
assert not agrees([4], "ok:3,5")
assert not agrees([4], "ok:5")
assert not agrees([2, 4], "ok:")

counts = {"accepted": 0, "refused": 0, "empty_helpers": 0}
observed = 0
for line in sys.stdin:
    parts = line.rstrip("\n").split("\t")
    assert len(parts) == 2, ("malformed Lean row", observed, line)
    raw, actual = parts
    claims = list(map(int, raw.split(","))) if raw else []
    wanted = expected(claims)
    assert actual == representation(wanted), (observed, claims, actual, wanted)
    counts["refused" if wanted is None else "accepted"] += 1
    counts["empty_helpers"] += wanted == [] if wanted is not None else 0
    observed += 1

assert observed == 2048, ("incomplete Lean stream", observed)
assert counts["refused"] > 600, counts
assert counts["accepted"] > 300, counts
assert counts["empty_helpers"] > 100, counts
print(
    f"SSZ multiproof positional oracle: {observed} actual Lean rows matched; "
    f"{counts['accepted']} admitted, {counts['refused']} refused, "
    f"{counts['empty_helpers']} valid empty-helper cases; "
    "3 comparator mutations detected; no cryptographic claim"
)
