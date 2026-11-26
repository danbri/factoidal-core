#!/usr/bin/env python3
"""Independent standard-library fixture oracle for proposer evidence (#938).

Build synthetic complete field trees and sparse registry trees; no runtime
implementation or trusted state root is supplied by this Python program.
"""
import argparse
import hashlib
import random
import struct
import subprocess
import time

ZERO = bytes(32)
MAX = (1 << 64) - 1
ELECTRA = 364032 * 32

def h(a, b):
    return hashlib.sha256(a + b).digest()

def u64(n):
    return struct.pack("<Q", n) + bytes(24)

def tree(leaves, index=0):
    assert leaves and len(leaves) & (len(leaves)-1) == 0
    siblings = []
    while len(leaves) > 1:
        siblings.append(leaves[index ^ 1])
        index //= 2
        leaves = [h(leaves[i], leaves[i+1]) for i in range(0, len(leaves), 2)]
    return leaves[0], siblings

def change(b):
    return bytes([b[0] ^ 1]) + b[1:]

def val_root(v):
    key, cred, balance, slashed, eligible, activation, exit_epoch, withdrawable = v
    return tree([h(key[:32], key[32:] + bytes(16)), cred, u64(balance),
                 bytes([slashed]) + bytes(31), u64(eligible), u64(activation),
                 u64(exit_epoch), u64(withdrawable)])[0]

def header_root(header):
    slot, index, parent, state, body = header
    return tree([u64(slot), u64(index), parent, state, body, ZERO, ZERO, ZERO])[0]

def sign(header, previous, current, epoch, genesis):
    version = previous if header[0] // 32 < epoch else current
    domain = bytes(4) + h(version + bytes(28), genesis)[:28]
    return h(header_root(header), domain)

def tokens(xs):
    return [x.hex() if isinstance(x, bytes) else str(int(x)) for x in xs]

def make_case(rng, serial):
    # Use both layout widths and epochs around activation; header epoch can
    # differ from state epoch. Other BeaconState fields are synthetic chunks.
    slot = [31, 32, ELECTRA-1, ELECTRA, ELECTRA+32, MAX][serial % 6]
    current_epoch = slot // 32
    epoch = current_epoch
    header_slot = max(0, slot-32) if serial % 2 else slot
    length, index = 8, serial % 8
    previous, current, genesis = rng.randbytes(4), rng.randbytes(4), rng.randbytes(32)
    v = [rng.randbytes(48), rng.randbytes(32), 32_000_000_000, 0, 0,
         current_epoch, 0, current_epoch+1]
    # Exit epoch deliberately differs from withdrawable epoch.
    if serial % 11 == 0:
        v[3] = 1
    elif serial % 11 == 1:
        v[7] = current_epoch
    elif serial % 11 == 2:
        v[5] = current_epoch+1
    leaves = [val_root([rng.randbytes(48), rng.randbytes(32), 32, 0, 0, 0, MAX, MAX])
              for _ in range(length)]
    leaves[index] = val_root(v)
    root, member = tree(leaves, index)
    zero = ZERO
    for _ in range(3):
        zero = h(zero, zero)
    for _ in range(3, 40):
        member.append(zero)
        root = h(root, zero)
        zero = h(zero, zero)
    registry = h(root, u64(length))
    fields = [ZERO] * (64 if slot >= ELECTRA else 32)
    fields[1] = genesis
    fields[2] = u64(slot)
    fields[3] = tree([previous + bytes(28), current + bytes(28), u64(epoch), ZERO])[0]
    fields[11] = registry
    state, rs = tree(fields[:], 11)
    _, sl = tree(fields[:], 2)
    _, fs = tree(fields[:], 3)
    _, gs = tree(fields[:], 1)
    a = [header_slot, index, rng.randbytes(32), rng.randbytes(32), rng.randbytes(32)]
    b = a[:]
    b[2 + serial % 3] = change(b[2 + serial % 3])
    line = tokens([slot, length, *v, previous, current, epoch, genesis, registry, state,
                   *a, *b, *member, *rs, *sl, *fs, *gs])
    eligible = not v[3] and v[5] <= current_epoch < v[7]
    expected = ("candidate_not_authenticated " + v[0].hex() + " " +
                sign(a, previous, current, epoch, genesis).hex() + " " +
                sign(b, previous, current, epoch, genesis).hex()
                if eligible else "error not_slashable")
    yield line, expected

    def mutate(pos, value, expected):
        x = line[:]
        x[pos] = str(value)
        return x, "error " + expected

    yield mutate(21, (header_slot+1) & MAX, "different_slot")
    yield mutate(22, (index+1) % length, "different_proposer")
    identical = line[:]
    identical[21:26] = identical[16:21]
    yield identical, "error identical_headers"
    yield mutate(10, change(previous).hex(), "fork_mismatch")
    yield mutate(13, change(genesis).hex(), "genesis_mismatch")
    yield mutate(14, change(registry).hex(), "registry_mismatch")
    yield mutate(2, change(v[0]).hex(), "validator_mismatch")
    yield mutate(26, change(member[0]).hex(), "validator_mismatch")
    yield mutate(1, 0, "index_outside")
    yield mutate(1, length+1, "validator_mismatch")
    yield mutate(18, "aa", "header_width")
    yield mutate(5, 2, "parse_error")
    yield mutate(16, MAX+1, "out_of_range")
    depth = len(rs)
    yield mutate(66, change(rs[0]).hex(), "registry_mismatch")
    yield mutate(66+depth, change(sl[0]).hex(), "slot_mismatch")
    yield mutate(66+2*depth, change(fs[0]).hex(), "fork_mismatch")
    yield mutate(66+3*depth, change(gs[0]).hex(), "genesis_mismatch")
    yield line[:-1], "error branch_length"

def compare(actual, expected):
    if len(actual) != len(expected):
        raise ValueError(f"row count {len(actual)} != {len(expected)}")
    for i, (a, e) in enumerate(zip(actual, expected)):
        if a != e:
            raise ValueError(f"row {i}: {a!r} != {e!r}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("binary", nargs="?")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    rng = random.Random(938)
    rows = [( " ".join(line), expected) for i in range(64)
            for line, expected in make_case(rng, i)]
    rows += [("x"*8193, "error resource_limit"), ("", "error parse_error")]
    requests, expected = zip(*rows)
    assert len(rows) == 1218
    assert len(set(requests)) == len(rows)
    assert any(e.startswith("candidate_not_authenticated ") for e in expected)
    controls = [list(expected[:-1]), list(expected) + ["extra"], list(expected)]
    controls[-1][0] = "candidate_not_authenticated forged"
    for mutated in controls:
        try:
            compare(mutated, expected)
        except ValueError:
            pass
        else:
            raise AssertionError("forged comparator output accepted")
    print(f"Prepared {len(rows)} independent expectations; 3 comparator controls rejected")
    if args.self_test:
        return
    if not args.binary:
        ap.error("native binary required")
    start = time.monotonic()
    completed = subprocess.run([args.binary], input="\n".join(requests)+"\n",
                               text=True, capture_output=True, check=True, timeout=240)
    assert not completed.stderr, completed.stderr
    compare(completed.stdout.splitlines(), expected)
    print(f"Native proposer evidence: {len(rows)}/{len(rows)} matched; "
          f"{sum(e.startswith('candidate_not_authenticated ') for e in expected)} candidates; "
          f"{time.monotonic()-start:.3f}s total")

if __name__ == "__main__":
    main()
