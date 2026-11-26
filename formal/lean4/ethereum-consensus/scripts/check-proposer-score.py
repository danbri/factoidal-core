#!/usr/bin/env python3
"""Independent source-pinned Python oracle for the Lean proposer-score bridge.

Reference: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3
specs/phase0/fork-choice.md, compute_proposer_score and get_weight.
The input snapshots, ancestries and updates are synthetic, not authenticated.
Only the Lean CLI supplies the observed output rows.
"""
import sys


def roster(case):
    entries = [
        (0, 7 + case % 11),
        (1, 3 + (case // 2) % 5),
        (2, case % 29),
        (3, 10 + (3 * case) % 13),
    ]
    if case % 13 == 0:
        entries.insert(0, (0, 1))
    return entries


def total_active_balance(case):
    if case % 127 == 0:
        return 80
    if case % 17 == 0:
        return case % 101
    return 1_000_000_000 + (case % 41) * 123_456_789


def proposer_score(balance):
    # Division order is material. E.g. 80 => 0, not 1.
    committee_weight = balance // 32
    return committee_weight * 40 // 100


def ancestor(supported, node):
    return supported % 7 == node % 7


def vote(case, index, updated):
    original = (
        None if (case + index) % 5 == 0
        else (case % 12, (13 * case + 7 * index) % 31)
    )
    if not updated or index != case % 4 or case % 5 == 0:
        return original
    if (case + 3 * index) % 11 == 0:
        return original
    candidate = (case % 12 + 1, (19 * case + 1) % 37)
    if original is not None and candidate[0] <= original[0]:
        return original
    return candidate


def attestation(case, node, updated):
    entries = roster(case)
    indices = [index for index, _ in entries]
    if len(set(indices)) != len(indices):
        return None
    result = 0
    for index, balance in entries:
        if (case + 3 * index) % 11 == 0:
            continue
        latest = vote(case, index, updated)
        if latest is not None and ancestor(latest[1], node):
            result += balance
    return result


def score(case, node, updated, base, computed):
    if base is None:
        return None
    if case % 3 == 0:
        return base
    boost_root = (5 * case + 3) % 37
    return base + (computed if ancestor(boost_root, node) else 0)


def encoded(value):
    return "R" if value is None else str(value)


def expected_row(case):
    node = (11 * case + 2) % 37
    balance = total_active_balance(case)
    computed = proposer_score(balance)
    base = attestation(case, node, False)
    updated_base = attestation(case, node, True)
    now = score(case, node, False, base, computed)
    after = score(case, node, True, updated_base, computed)
    return [
        str(case), str(balance), str(computed),
        encoded(base), encoded(now), encoded(after),
    ], base, now, after, balance


def main():
    observed = [row.rstrip("\n") for row in sys.stdin]
    if len(observed) != 1024:
        raise SystemExit(f"Expected 1024 Lean rows, observed {len(observed)}")
    refusals = boosts = updates = short_rounds = 0
    for case, line in enumerate(observed):
        expected, base, now, after, balance = expected_row(case)
        actual = line.split("\t")
        if actual != expected:
            raise SystemExit(
                f"Case {case}: observed Lean {actual!r}; independent Python {expected!r}"
            )
        refusals += base is None
        boosts += base is not None and now > base
        updates += now is not None and now != after
        short_rounds += proposer_score(balance) != balance * 40 // 3200
    if refusals != 79:
        raise SystemExit(f"Duplicate-validator refusals changed: {refusals}")
    if not boosts or not updates or not short_rounds:
        raise SystemExit(
            f"Insufficient coverage: boost={boosts} updates={updates} "
            f"two-rounding-discriminators={short_rounds}"
        )
    print(
        f"Matched 1024/1024 Lean rows: {refusals} duplicate refusals, "
        f"{boosts} positive boosts, {updates} observable vote changes, "
        f"{short_rounds} rounding discriminators, 0 mismatches",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
