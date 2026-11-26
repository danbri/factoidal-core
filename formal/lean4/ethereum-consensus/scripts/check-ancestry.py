#!/usr/bin/env python3
"""Independent Python reference for bounded Lean ancestry and LMD weights.

Source ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md: get_ancestor/is_ancestor/get_weight.

Inputs are synthetic blocks, slots, votes and balance, not authenticated.
"""
import sys


def block(case, root):
    if root == 0:
        return (0, None)
    if root >= 28:
        return None
    if case % 19 == 0 and root == case % 13 + 1:
        return None
    if case % 23 == 0 and root == 7:
        return (7, 8)  # Parent with later slot; refuse
    return (root, root // 2)


def get_ancestor(case, supported, target_slot, fuel):
    while fuel:
        current = block(case, supported)
        if current is None:
            return None
        slot, parent = current
        if slot <= target_slot:
            return supported
        if parent is None:
            return None
        preceding = block(case, parent)
        if preceding is None or preceding[0] >= slot:
            return None
        supported = parent
        fuel -= 1
    return None


def descends(case, supported, candidate, fuel):
    target = block(case, candidate)
    if target is None:
        return None
    ancestor = get_ancestor(case, supported, target[0], fuel)
    return None if ancestor is None else ancestor == candidate


def roster(case):
    entries = [(0, 7 + case % 11), (1, 3 + (case // 2) % 5),
               (2, case % 29), (3, 10 + (3 * case) % 13)]
    return [(0, 1), *entries] if case % 13 == 0 else entries


def equiv(case, i):
    return (case + 3 * i) % 11 == 0


def vote(case, i, updated):
    old = None if (case + i) % 5 == 0 else (case % 12, (13 * case + 7 * i) % 31)
    if not updated or i != case % 4 or case % 5 == 0 or equiv(case, i):
        return old
    candidate = (case % 12 + 1, (19 * case + 1) % 37)
    if old is not None and candidate[0] <= old[0]:
        return old
    return candidate


def total_active_balance(case):
    if case % 127 == 0:
        return 80
    if case % 17 == 0:
        return case % 101
    return 1_000_000_000 + (case % 41) * 123_456_789


def boost_root(case):
    return None if case % 3 == 0 else (5 * case + 3) % 32


def score(case, node, fuel, boost, updated):
    if block(case, node) is None:
        return None
    entries = roster(case)
    if len({i for i, _ in entries}) != len(entries):
        return None
    amount = 0
    for i, balance in entries:
        if equiv(case, i):
            continue
        v = vote(case, i, updated)
        if v is None:
            continue
        known = descends(case, v[1], node, fuel)
        if known is None:
            return None
        if known:
            amount += balance
    if boost is not None:
        known_boost = descends(case, boost, node, fuel)
        if known_boost is None:
            return None
        if known_boost:
            amount += (total_active_balance(case) // 32) * 40 // 100
    return amount


def encoded(value):
    return 'R' if value is None else str(value)


def encoded_bool(value):
    return 'U' if value is None else ('T' if value else 'F')


def expected(case):
    node = (11 * case + 2) % 28
    fuel = case % 11
    probe = (13 * case + 7) % 32
    boost = boost_root(case)
    trial = descends(case, probe, node, fuel)
    boosted_trial = descends(case, boost, node, fuel) if boost is not None else None
    base = score(case, node, fuel, None, False)
    current = score(case, node, fuel, boost, False)
    after = score(case, node, fuel, boost, True)
    return [str(case), str(node), str(fuel), encoded_bool(trial),
            '-' if boost is None else encoded_bool(boosted_trial),
            encoded(base), encoded(current), encoded(after)], (base, current, after, trial)


def main():
    observed = [line.rstrip('\n') for line in sys.stdin]
    if len(observed) != 1024:
        raise SystemExit(f'Expected 1024 Lean rows; got {len(observed)}')
    refused = accepted = unknown_probe = positive_boost = changed = 0
    for case, line in enumerate(observed):
        target, (base, now, after, probe) = expected(case)
        actual = line.split('\t')
        if actual != target:
            raise SystemExit(f'Case {case}: Lean {actual!r}; Python {target!r}')
        refused += now is None
        accepted += now is not None
        unknown_probe += probe is None
        positive_boost += now is not None and base is not None and now > base
        changed += now is not None and after is not None and after != now
    if min(refused, accepted, unknown_probe, positive_boost, changed) == 0:
        raise SystemExit('A necessary ancestry/refusal/score branch was not exercised')
    print(f'Matched 1024/1024 Lean rows: {refused} refusals, {accepted} completed scores, '
          f'{unknown_probe} inconclusive probes, {positive_boost} positive boosts, '
          f'{changed} observable vote updates; 0 mismatches', file=sys.stderr)


if __name__ == '__main__':
    main()
