#!/usr/bin/env python3
"""Independent Python reference for the finite Lean LMD attestation-score CLI.

Normative comparison target (limited input adapter):
ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md: get_attestation_score/get_weight.
The modulo-7 ancestry relation and eligible roster are synthetic inputs,
not authenticated consensus data. Only Lean emits observed result rows.
"""
import sys


def roster_for(case):
    values = [
        (0, 7 + case % 11),
        (1, 3 + (case // 2) % 5),
        (2, case % 29),
        (3, 10 + (3 * case) % 13),
    ]
    return [(0, 1), *values] if case % 13 == 0 else values


def original_vote(case, validator):
    if (case + validator) % 5 == 0:
        return None
    return (case % 12, (13 * case + 7 * validator) % 31)


def equivocating(case, validator):
    return (case + 3 * validator) % 11 == 0


def latest_vote(case, validator, update):
    original = original_vote(case, validator)
    if not update or validator != case % 4 or case % 5 == 0:
        return original
    if equivocating(case, validator):
        return original
    candidate = (case % 12 + 1, (19 * case + 1) % 37)
    if original is not None and original[0] >= candidate[0]:
        return original
    return candidate


def ancestor(supported_root, candidate_root):
    return supported_root % 7 == candidate_root % 7


def score_for(case, node, update):
    roster = roster_for(case)
    validators = [index for index, _balance in roster]
    if len(validators) != len(set(validators)):
        return None

    total = 0
    for index, balance in roster:
        if equivocating(case, index):
            continue
        vote = latest_vote(case, index, update)
        if vote is not None and ancestor(vote[1], node):
            total += balance
    return total


def weighted_for(case, node, update):
    score = score_for(case, node, update)
    if score is None:
        return None
    if case % 3 == 0:
        return score
    boost_root = (5 * case + 3) % 37
    boost_value = case % 17
    return score + (boost_value if ancestor(boost_root, node) else 0)


def encoded(value):
    return "R" if value is None else str(value)


def main():
    lines = [line.rstrip("\n") for line in sys.stdin]
    if len(lines) != 1024:
        raise SystemExit(f"Expected exactly 1024 Lean rows, got {len(lines)}")
    refused = 0
    boosted = 0
    changed_after_update = 0
    for case, line in enumerate(lines):
        fields = line.split("\t")
        if len(fields) != 4 or fields[0] != str(case):
            raise SystemExit(f"Case {case}: malformed/out-of-order Lean row {line!r}")
        node = (11 * case + 2) % 37
        first = score_for(case, node, False)
        total = weighted_for(case, node, False)
        after = weighted_for(case, node, True)
        expected = [str(case), encoded(first), encoded(total), encoded(after)]
        if fields != expected:
            raise SystemExit(
                f"Case {case}: Lean {fields!r}, Python {expected!r}"
            )
        refused += first is None
        boosted += first is not None and total > first
        changed_after_update += total is not None and after != total

    if refused != 79:
        raise SystemExit(f"Duplicate roster refusal count changed: {refused}")
    if boosted == 0 or changed_after_update == 0:
        raise SystemExit("Missing proposer-boost or admitted-vote effect coverage")
    print(
        f"Matched 1024 actual Lean cases: {refused} duplicate-index refusals, "
        f"{boosted} positive boosts, {changed_after_update} updated scores; "
        "0 mismatches",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
