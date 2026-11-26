#!/usr/bin/env python3
"""Independent reference for the phase0 fork-choice per-validator LMD update.

Checks the *actual Lean executable* over 2,048 deterministic rows, including
equal-epoch conflicting roots, equivocation and first-vote admission.
No claim about BLS, attestation validity, or live beacon state.
"""
import sys
from collections import Counter

counts = Counter()
seen = 0
for line in sys.stdin:
    columns = line.rstrip("\n").split("\t")
    if len(columns) != 8:
        raise AssertionError(f"row {seen}: expected eight tab fields, got {line!r}")
    index, equiv, old_epoch, old_root, cand_epoch, cand_root, out_epoch, out_root = map(int, columns)
    assert index == seen, (index, seen)
    exp_equiv = int(index % 7 == 0)
    exp_old = None if index % 4 == 0 else (index % 29, (index * 7 + 5) % 65536)
    exp_candidate = (index % 29 if index % 5 == 0 else index % 31,
                     (index * 17 + 3) % 65536)
    assert equiv == exp_equiv, (index, equiv)
    assert (old_epoch, old_root) == (exp_old if exp_old is not None else (-1, -1))
    assert (cand_epoch, cand_root) == exp_candidate, (index, cand_epoch, cand_root)
    if equiv:
        expected = exp_old
        counts["equivocating"] += 1
    elif exp_old is None:
        expected = exp_candidate
        counts["first"] += 1
    elif exp_candidate[0] > exp_old[0]:
        expected = exp_candidate
        counts["newer"] += 1
    else:
        expected = exp_old
        if exp_candidate[0] == exp_old[0]:
            counts["equal_epoch"] += 1
            if exp_candidate[1] != exp_old[1]:
                counts["conflicting_equal_epoch"] += 1
        else:
            counts["stale"] += 1
    assert (out_epoch, out_root) == (expected if expected is not None else (-1, -1)), (
        index, equiv, exp_old, exp_candidate, (out_epoch, out_root), expected
    )
    seen += 1

assert seen == 2048, seen
for required in ("equivocating", "first", "newer", "equal_epoch",
                 "conflicting_equal_epoch", "stale"):
    assert counts[required] > 0, (required, counts)
print("Beacon LMD latest-message: 2048 Lean rows matched Python reference; "
      + ", ".join(f"{key}={counts[key]}" for key in sorted(counts))
      + "; no signature, FFG or fork-choice-head claim")
