#!/usr/bin/env python3
"""Independent finite-store / fuel-bounded GHOST reference, 1024 Lean rows.

This intentionally does NOT import Lean code. All votes and proposer boost
are absent, so each known viable child's actual Lean score is zero. The
exercise isolates finite child enumeration, fail-closed admission, the
canonical argmax root tie break, and the iterative head/leaf budget. It
does not test real checkpoint viability, authentication, BLS or FFG.
"""
from __future__ import annotations

import sys


def entries_for(n: int) -> list[tuple[int, int, int | None]]:
    root0 = [] if n % 11 == 0 else [(0, 0, None)]
    one = (1, 0 if n % 17 == 0 else 1, 0)
    two = (2, 1, 99 if n % 19 == 0 else 0)
    three = (3, 1 if n % 23 == 0 else 2, 1)
    entries = root0 + [one, two, three, (4, 2, 2)]
    if n % 13 == 0:
        entries.append((2, 10, 0))
    return entries


def lookup(entries: list[tuple[int, int, int | None]],
           root: int) -> tuple[int, int, int | None] | None:
    for item in entries:
        if item[0] == root:
            return item
    return None


def viable(n: int, root: int) -> bool | None:
    if n % 7 == 0 and root == 2:
        return None
    if n % 5 == 0 and root == 2:
        return False
    if n % 29 == 0 and root == 1:
        return None
    return True


def scan(entries: list[tuple[int, int, int | None]],
         n: int, parent: int) -> list[int] | None:
    anchor = lookup(entries, parent)
    if anchor is None:
        return None
    parent_slot = anchor[1]
    output: list[int] = []
    for root, slot, parent_root in entries:
        if parent_root != parent:
            continue
        if slot <= parent_slot:
            return None
        admitted = viable(n, root)
        if admitted is None:
            return None
        if admitted:
            output.append(root)
    return output


def select(entries: list[tuple[int, int, int | None]],
           n: int, parent: int) -> str:
    roots = [entry[0] for entry in entries]
    if len(roots) != len(set(roots)):
        return "R"
    children = scan(entries, n, parent)
    if children is None:
        return "R"
    if not children:
        return "E"
    # All admitted source cases have empty active vote roster and no boost.
    # The existing Lean scorer must therefore return zero per child.
    # On a zero-score tie the numerically larger provisional root wins.
    return str(max(children))


def get_head(entries: list[tuple[int, int, int | None]],
             n: int, start: int, fuel: int) -> str:
    current = start
    for _ in range(fuel):
        result = select(entries, n, current)
        if result == "R":
            return "R"
        if result == "E":
            return str(current)
        current = int(result)
    return "R"  # Fuel exhausted without a confirmed leaf.


def reference(n: int) -> tuple[str, ...]:
    entries = entries_for(n)
    start = 99 if n % 31 == 0 else 0
    budget = n % 5
    scanned = scan(entries, n, start)
    scan_text = "R" if scanned is None else ",".join(map(str, scanned))
    step = select(entries, n, start)
    head = get_head(entries, n, start, budget)
    # An admission rejected by Lean's actual VoteStore must not change head.
    return tuple(map(str, (n, start, budget))) + (scan_text, step, head, head)


def main() -> None:
    received = 0
    heads: dict[str, int] = {}
    steps: dict[str, int] = {}
    for line in sys.stdin:
        fields = tuple(line.rstrip("\n").split("\t"))
        expected = reference(received)
        if fields != expected:
            raise SystemExit(
                f"row {received}: Lean={fields!r}, independent={expected!r}"
            )
        steps[fields[4]] = steps.get(fields[4], 0) + 1
        heads[fields[5]] = heads.get(fields[5], 0) + 1
        received += 1
        if received > 1024:
            raise SystemExit("Lean produced extra rows")
    if received != 1024:
        raise SystemExit(f"Lean emitted {received} rows, expected 1024")
    if not any(k not in ("R", "E") for k in steps):
        raise SystemExit("No selected child cases exercised")
    if not any(k != "R" for k in heads):
        raise SystemExit("No completed heads exercised")
    if heads.get("R", 0) == 0 or steps.get("R", 0) == 0:
        raise SystemExit("No refusal boundary exercised")
    print(
        f"PASS {received} independent finite-store head comparisons; "
        f"step_outcomes={steps}; terminal_heads={heads}; mismatches=0"
    )


if __name__ == "__main__":
    main()
