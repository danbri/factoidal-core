#!/usr/bin/env python3
"""Independent standard-library SSZ registry oracle; no client runtime code."""
import hashlib
import functools
import random
import subprocess
import sys

LIMIT = 1 << 40
MAX64 = (1 << 64) - 1
ZERO = bytes(32)

def pair(a, b):
    return hashlib.sha256(a + b).digest()

def basic(value):
    return value.to_bytes(32, "little")

def merkle(fields):
    assert len(fields) and len(fields) & (len(fields) - 1) == 0
    while len(fields) > 1:
        fields = [pair(a, b) for a, b in zip(fields[::2], fields[1::2])]
    return fields[0]

def leaf(v):
    key, cred, balance, slashed, eligible, activation, exit_epoch, withdrawable = v
    return merkle([pair(key[:32], key[32:] + bytes(16)), cred, basic(balance),
                   basic(slashed), basic(eligible), basic(activation),
                   basic(exit_epoch), basic(withdrawable)])

def fixture(v, count, index):
    """Materialise only non-uniform subtrees; all other actual leaves
    contain the same valid-width filler validator, padding is zero."""
    value = leaf(v)
    filler = leaf((bytes(48), ZERO, 0, 0, 0, 0, MAX64, MAX64))
    @functools.cache
    def uniform(node, depth):
        if depth == 0:
            return node
        child = uniform(node, depth - 1)
        return pair(child, child)
    @functools.cache
    def subtree(start, depth):
        end = start + (1 << depth)
        if start >= count:
            return uniform(ZERO, depth)
        if end <= count and not start <= index < end:
            return uniform(filler, depth)
        if depth == 0:
            return value
        half = 1 << (depth - 1)
        return pair(subtree(start, depth-1), subtree(start+half, depth-1))
    siblings = [subtree(((index >> d) ^ 1) << d, d) for d in range(40)]
    return pair(subtree(0, 40), basic(count)), siblings

def reconstruct(value, index, count, siblings):
    for d, sibling in enumerate(siblings):
        value = pair(sibling, value) if index & (1 << d) else pair(value, sibling)
    return pair(value, basic(count))

def changed(b):
    return bytes([b[0] ^ 1]) + b[1:]

def cases():
    rng = random.Random(881)
    rows = []
    def add(op, count, index, epoch, common, v, root, siblings, expected):
        key, cred, *numbers = v
        row = " ".join(map(str, [op, count, index, epoch, common, key.hex(), cred.hex(),
                                   *numbers, root.hex(), *(s.hex() for s in siblings)]))
        assert len(row.encode()) + 1 <= 4096
        rows.append((row, expected))
    for i in range(128):
        count = [1, 2, 3, 7, 8, 9, 1 << 20, LIMIT-1, LIMIT][i % 9]
        index = [0, count-1, rng.randrange(count)][i % 3]
        activation = rng.randrange(1, 1000)
        withdrawable = activation + rng.randrange(1, 1000)
        epoch = [activation-1, activation, withdrawable-1, withdrawable][i % 4]
        slashed = (i // 4) % 2
        # Deliberately place exit at or before activation to detect an incorrect
        # use of exit_epoch. Root admission is SSZ, not semantic state validation.
        v = (rng.randbytes(48), rng.randbytes(32), [0, MAX64, 32_000_000_000][i % 3],
             slashed, 0, activation, activation-1, withdrawable)
        root, siblings = fixture(v, count, index)
        assert reconstruct(leaf(v), index, count, siblings) == root
        good = "candidate_not_authenticated" if not slashed and activation <= epoch < withdrawable else "not_slashable"
        add("root", count, index, epoch, 1, v, root, [], leaf(v).hex())
        add("proof", count, index, epoch, 1, v, root, siblings, "match " + root.hex())
        add("candidate", count, index, epoch, 1, v, root, siblings, good)
        add("candidate", count, index, epoch, 0, v, root, siblings, "error not_common")
        add("candidate", count, index, epoch, 1, v, changed(root), siblings, "root_mismatch")
        # Change one sibling, one leaf field, and the claimed length independently.
        wrong = list(siblings)
        wrong[i % 40] = changed(wrong[i % 40])
        add("proof", count, index, epoch, 1, v, root, wrong,
            "mismatch " + reconstruct(leaf(v), index, count, wrong).hex())
        bad_v = (changed(v[0]), *v[1:])
        add("proof", count, index, epoch, 1, bad_v, root, siblings,
            "mismatch " + reconstruct(leaf(bad_v), index, count, siblings).hex())
        alt_count = count+1 if count < LIMIT else count-1
        if index < alt_count:
            add("proof", alt_count, index, epoch, 1, v, root, siblings,
                "mismatch " + reconstruct(leaf(v), index, alt_count, siblings).hex())
        else:
            add("proof", alt_count, index, epoch, 1, v, root, siblings, "error index_outside")
        add("proof", count, count, epoch, 1, v, root, siblings, "error index_outside")
        add("proof", LIMIT+1, index, epoch, 1, v, root, siblings, "error registry_length")
        add("proof", count, index, epoch, 1, v, root, siblings[:-1], "error branch_length")
        if i == 0:
            add("proof", count, index, epoch, 1, v, root, siblings + [ZERO], "error branch_length")
            add("proof", count, index, epoch, 1, v, root, [b"x"] + siblings[1:], "error chunk_width")
            add("proof", count, index, epoch, 1, v, b"x", siblings, "error chunk_width")
            add("proof", count, index, epoch, 1, (v[0][:-1], *v[1:]), root, siblings, "error public_key_width")
            add("proof", count, index, epoch, 1, (v[0], v[1][:-1], *v[2:]), root, siblings, "error credentials_width")
        if count > 1:
            other = (index + 1) % count
            add("proof", count, other, epoch, 1, v, root, siblings,
                "mismatch " + reconstruct(leaf(v), other, count, siblings).hex())
    rows.extend([("bad", "error parse_error"), ("x" * 4097, "error resource_limit")])
    return rows

def compare(rows, actual):
    expected = [want for _, want in rows]
    if len(actual) != len(expected):
        raise ValueError(f"output count {len(actual)} != {len(expected)}")
    for i, (a, e) in enumerate(zip(actual, expected)):
        if a != e:
            raise ValueError(f"row {i}: got {a!r}, expected {e!r}")

def main():
    rows = cases()
    expected = [want for _, want in rows]
    compare(rows, expected)
    for corrupt in [expected[:-1], ["forged"] + expected[1:],
                    expected[:2] + ["candidate_not_authenticated"] + expected[3:],
                    expected + ["extra"]]:
        try:
            compare(rows, corrupt)
        except ValueError:
            pass
        else:
            raise ValueError("comparator corruption not detected")
    print(f"Prepared {len(rows)} rows; four comparator controls detected", flush=True)
    if sys.argv[1:] == ["--self-test"]:
        return
    if len(sys.argv) < 2:
        raise ValueError("provide Lean runner command")
    proc = subprocess.run(sys.argv[1:], input="\n".join(row for row, _ in rows)+"\n",
                          text=True, capture_output=True, timeout=240, check=True)
    compare(rows, proc.stdout.splitlines())
    print(f"PASS {len(rows)}/{len(rows)} actual Lean registry cases")

if __name__ == "__main__":
    main()
