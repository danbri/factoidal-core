#!/usr/bin/env python3
"""Independent dictionary oracle for the actual Lean VoteStore transition trace.

Reads 1,024 sequential observations from lake exe lmd-store; checks every
input, stored before/after target, unrelated neighbour and equivocation flag.
The integer roots and admission flags are synthetic, not signed attestations.
"""
import sys
from collections import Counter

state = {0: (4, 100), 2: (6, 500)}
counts = Counter()
seen = 0

for line in sys.stdin:
    fields = line.rstrip("\n").split("\t")
    if len(fields) != 15:
        raise AssertionError(f"row {seen}: expected 15 fields, got {line!r}")
    (
        index, validator, admitted, equiv, cand_epoch, cand_root,
        old_epoch, old_root, next_epoch, next_root, other,
        other_old_epoch, other_old_root, other_new_epoch, other_new_root
    ) = map(int, fields)

    assert index == seen, (index, seen)
    assert validator == index % 8, index
    assert admitted == int(index % 11 != 0), index
    assert equiv == int(validator == 2), index
    expected_candidate = (
        index % 7 if index % 5 == 0 else index // 8,
        (index * 17 + 3) % 65536,
    )
    assert (cand_epoch, cand_root) == expected_candidate, index

    absent = (-1, -1)
    old = state.get(validator, absent)
    assert (old_epoch, old_root) == old, (index, old)
    assert other == (validator + 1) % 8, index
    other_old = state.get(other, absent)
    assert (other_old_epoch, other_old_root) == other_old, index

    if not admitted:
        counts["invalid_refused"] += 1
    elif equiv:
        counts["equivocator_refused"] += 1
    elif old == absent:
        state[validator] = expected_candidate
        counts["first_accepted"] += 1
    elif expected_candidate[0] > old[0]:
        state[validator] = expected_candidate
        counts["newer_accepted"] += 1
    else:
        counts["equal_refused" if expected_candidate[0] == old[0] else "stale_refused"] += 1

    assert (next_epoch, next_root) == state.get(validator, absent), (
        index, old, expected_candidate, (next_epoch, next_root), state
    )
    assert (other_new_epoch, other_new_root) == other_old, (index, other)
    seen += 1

assert seen == 1024, seen
for required in (
    "invalid_refused", "equivocator_refused", "first_accepted",
    "newer_accepted", "equal_refused", "stale_refused"
):
    assert counts[required] > 0, (required, counts)

print(
    f"LMD VoteStore: {seen} sequential Lean transitions matched independent "
    "Python keyed-state oracle; "
    + ", ".join(f"{k}={counts[k]}" for k in sorted(counts))
    + "; no signed attestation, bounded map, fork-choice-head or finality claim"
)
