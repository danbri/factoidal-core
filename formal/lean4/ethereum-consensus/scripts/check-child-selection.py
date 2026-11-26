#!/usr/bin/env python3
"""Independent reference for the finite LMD-GHOST child-selection adapter.

Pinned source: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3
specs/phase0/fork-choice.md (get_head, get_weight, get_ancestor).
All inputs are synthetic; the finite viable-child inventory is trusted.
This Python code constructs expected results without importing Lean code.
"""
import sys


def block(case, root):
    if root == 0:
        return 0, None
    if root >= 13:
        return None
    if case % 19 == 0 and root == case % 12 + 1:
        return None
    if case % 23 == 0 and root == 3:
        return 3, 12
    if case % 29 == 0 and root == 4:
        return 0, 0
    return (root, 0) if root < 5 else (root, 1 + (root - 5) % 4)


def ancestor_at_slot(case, supported, target_slot, fuel):
    while fuel > 0:
        entry = block(case, supported)
        if entry is None:
            return None
        slot, parent = entry
        if slot <= target_slot:
            return supported
        if parent is None:
            return None
        previous = block(case, parent)
        if previous is None or previous[0] >= slot:
            return None
        supported = parent
        fuel -= 1
    return None


def descends(case, supported, candidate, fuel):
    target = block(case, candidate)
    if target is None:
        return None
    reached = ancestor_at_slot(case, supported, target[0], fuel)
    return reached == candidate if reached is not None else None


def roster(case):
    entries = [(0, 7 + case % 11), (1, 3 + (case // 2) % 5),
               (2, case % 29), (3, 10 + (3 * case) % 13)]
    return [(0, 1), *entries] if case % 13 == 0 else entries


def equiv(case, validator):
    return (case + 3 * validator) % 11 == 0


def latest(case, validator, updated):
    original = None if (case + validator) % 5 == 0 else (
        case % 12, 5 + (17 * case + 3 * validator) % 8
    )
    if not updated or case % 5 == 0 or validator != case % 4:
        return original
    if equiv(case, validator):
        return original
    candidate = (case % 12 + 1, (19 * case + 1) % 13)
    if original is None or original[0] < candidate[0]:
        return candidate
    return original


def boost_root(case):
    return None if case % 3 == 0 else 5 + (7 * case) % 8


def total_active_balance(case):
    if case % 127 == 0:
        return 80
    if case % 17 == 0:
        return case % 101
    return 1_000_000_000 + (case % 41) * 123_456_789


def score(case, node, fuel, boost, updated):
    if block(case, node) is None:
        return None
    entries = roster(case)
    if len({validator for validator, _ in entries}) != len(entries):
        return None
    value = 0
    for validator, balance in entries:
        if equiv(case, validator):
            continue
        message = latest(case, validator, updated)
        if message is None:
            continue
        result = descends(case, message[1], node, fuel)
        if result is None:
            return None
        if result:
            value += balance
    if boost is not None:
        result = descends(case, boost, node, fuel)
        if result is None:
            return None
        if result:
            value += (total_active_balance(case) // 32) * 40 // 100
    return value


def children(mode):
    alternatives = {
        0: [], 1: [1], 2: [1, 2], 3: [1, 2, 3],
        4: [1, 1], 5: [3, 4], 6: [1, 2, 4],
        7: [2, 5], 8: [1, 99], 9: [3],
        10: [2, 3, 4], 11: [4, 2, 1],
    }
    return alternatives[mode]


def select(case, parent, fuel, mode, boost, updated):
    parent_entry = block(case, parent)
    candidates = children(mode)
    if parent_entry is None or len(set(candidates)) != len(candidates):
        return 'R', False
    for candidate in candidates:
        entry = block(case, candidate)
        if entry is None or entry[1] != parent or entry[0] <= parent_entry[0]:
            return 'R', False
    pairs = []
    for candidate in candidates:
        amount = score(case, candidate, fuel, boost, updated)
        if amount is None:
            return 'R', False
        pairs.append((amount, candidate))
    if not pairs:
        return 'E', False
    winner = max(pairs)
    best_balance = winner[0]
    tied = sum(v == best_balance for v, _ in pairs) >= 2
    return str(winner[1]), tied


def expected(case):
    parent = 99 if case % 31 == 0 else 0
    fuel = case % 11
    mode = case % 12
    boost = boost_root(case)
    base, _ = select(case, parent, fuel, mode, None, False)
    current, tied = select(case, parent, fuel, mode, boost, False)
    after, _ = select(case, parent, fuel, mode, boost, True)
    return [str(case), str(parent), str(fuel), str(mode),
            base, current, after, current], (base, current, after, tied)


def main():
    rows = [line.rstrip('\n') for line in sys.stdin]
    if len(rows) != 1024:
        raise SystemExit(f'Expected exactly 1024 Lean outputs; got {len(rows)}')
    refusals = empty = selected = ties = boost_changed = update_changed = 0
    for case, row in enumerate(rows):
        target, (base, current, after, tied) = expected(case)
        actual = row.split('\t')
        if actual != target:
            raise SystemExit(f'Case {case}: Lean {actual!r}; Python {target!r}')
        refusals += current == 'R'
        empty += current == 'E'
        selected += current not in ('R', 'E')
        ties += tied
        boost_changed += current not in ('R', 'E') and base not in ('R', 'E') and current != base
        update_changed += current not in ('R', 'E') and after not in ('R', 'E') and current != after
    if min(refusals, empty, selected, ties) == 0:
        raise SystemExit('Missing required refusal/empty/selection/tie coverage')
    if selected + empty + refusals != 1024:
        raise SystemExit('Selection categories do not partition all inputs')
    print(f'Matched 1024/1024 Lean rows: {refusals} refusals, '
          f'{empty} genuine empty inventories, {selected} selected heads, '
          f'{ties} selected-score ties, {boost_changed} boost winner changes, '
          f'{update_changed} admitted-vote winner changes; 0 mismatches',
          file=sys.stderr)


if __name__ == '__main__':
    main()
