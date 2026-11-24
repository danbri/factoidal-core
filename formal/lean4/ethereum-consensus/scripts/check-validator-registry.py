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

def state_fixture(registry_root, fields_count, rng):
    # Build the complete padded container in a heap. Only the validators
    # field is a real registry root; other fields are synthetic roots.
    width = 1 << (fields_count - 1).bit_length()
    heap = [ZERO] * (2 * width)
    for i in range(fields_count):
        heap[width + i] = rng.randbytes(32)
    heap[width + 11] = registry_root
    for i in range(width - 1, 0, -1):
        heap[i] = pair(heap[2*i], heap[2*i+1])
    index = width + 11
    siblings = []
    while index > 1:
        siblings.append(heap[index ^ 1])
        index //= 2
    # Independent layer-based Merkle calculation must match the heap.
    assert merkle(heap[width:]) == heap[1]
    return width, heap[1], siblings

def slot_state_fixture(registry_root, slot, fields_count, rng):
    width = 1 << (fields_count - 1).bit_length()
    fields = [rng.randbytes(32) for _ in range(fields_count)] + [ZERO] * (width-fields_count)
    fields[2] = basic(slot)
    fields[11] = registry_root
    layers = [fields]
    while len(layers[-1]) > 1:
        q = layers[-1]
        layers.append([pair(x, y) for x, y in zip(q[::2], q[1::2])])
    root = layers[-1][0]
    def branch(pos):
        return [layer[(pos >> d) ^ 1] for d, layer in enumerate(layers[:-1])]
    def reconstruct_field(pos, value, siblings):
        for d, sibling in enumerate(siblings):
            value = pair(sibling, value) if pos & (1 << d) else pair(value, sibling)
        return value
    reg, sl = branch(11), branch(2)
    assert reconstruct_field(11, registry_root, reg) == root
    assert reconstruct_field(2, basic(slot), sl) == root
    assert reconstruct_field(2, basic(slot ^ 1), sl) != root
    return root, reg, sl

def cases():
    rng = random.Random(881)
    state_rng = random.Random(896)
    slot_rng = random.Random(901)
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
        # Exercise the exact transport mapping for every Validator field,
        # including equal-width fields that a swapped assignment could conceal.
        if i < 8:
            for field in range(8):
                edited = list(v)
                edited[field] = changed(v[field]) if field < 2 else v[field] ^ 1
                edited = tuple(edited)
                edited_root = leaf(edited)
                assert edited_root != leaf(v)
                add("root", count, index, epoch, 1, edited, root, [], edited_root.hex())
                add("proof", count, index, epoch, 1, edited, root, siblings,
                    "mismatch " + reconstruct(edited_root, index, count, siblings).hex())
        # State layouts are derived from the pinned BeaconState field counts
        # (Phase0, Altair, Bellatrix, Capella, Deneb, Electra, Fulu).
        width, state_root, state_sibs = state_fixture(
            root, [21, 24, 25, 28, 28, 37, 38][i % 7], state_rng)
        op = "state" + str(width)
        other_op = "state64" if width == 32 else "state32"
        combined = siblings + [state_root] + state_sibs
        add(op, count, index, epoch, 1, v, root, combined, good)
        add(op, count, index, epoch, 0, v, root, combined, "error not_common")
        add(op, count, index, epoch, 1, v, root,
            siblings + [changed(state_root)] + state_sibs, "state_root_mismatch")
        add(op, count, index, epoch, 1, v, changed(root), combined, "state_root_mismatch")
        changed_state = list(state_sibs)
        changed_state[i % len(state_sibs)] = changed(changed_state[i % len(state_sibs)])
        add(op, count, index, epoch, 1, v, root,
            siblings + [state_root] + changed_state, "state_root_mismatch")
        add(op, count, index, epoch, 1, v, root,
            wrong + [state_root] + state_sibs, "root_mismatch")
        add(op, count, index, epoch, 1, bad_v, root, combined, "root_mismatch")
        add(other_op, count, index, epoch, 1, v, root, combined, "error branch_length")
        add(op, count, index, epoch, 1, v, root, combined[:-1], "error branch_length")
        add(op, count, index, epoch, 1, v, root,
            siblings + [b"x"] + state_sibs, "error chunk_width")
        add(op, count, index, epoch, 1, v, b"x", combined, "error chunk_width")
        # Mainnet slot proves the epoch used in slashability and selects
        # the layout at Electra. All non-target fields are synthetic.
        electra_slot = 364032 * 32
        slot = [0, 31, 32, 33, activation*32-1, activation*32,
                withdrawable*32-1, withdrawable*32, electra_slot-1,
                electra_slot, electra_slot+31, MAX64][i % 12]
        slot_epoch = slot // 32
        slot_v = v
        if i % 12 >= 8:
            slot_v = (*v[:5], slot_epoch, slot_epoch, slot_epoch+1)
        slot_root, slot_reg = fixture(slot_v, count, index)
        fields_count = 28 if slot < electra_slot else 37
        sr, reg, sl = slot_state_fixture(slot_root, slot, fields_count, slot_rng)
        both = slot_reg + [sr] + reg + sl
        expected_slot = ("candidate_not_authenticated" if not slot_v[3]
                         and slot_v[5] <= slot_epoch < slot_v[7] else "not_slashable")
        add("slotstate", count, index, slot, 1, slot_v, slot_root, both, expected_slot)
        add("slotstate", count, index, slot, 0, slot_v, slot_root, both, "error not_common")
        add("slotstate", count, index, slot ^ 1, 1, slot_v, slot_root, both, "slot_root_mismatch")
        bad_sl = sl.copy()
        bad_sl[i % len(sl)] = changed(bad_sl[i % len(sl)])
        add("slotstate", count, index, slot, 1, slot_v, slot_root,
            slot_reg + [sr] + reg + bad_sl, "slot_root_mismatch")
        add("slotstate", count, index, slot, 1, slot_v, slot_root,
            slot_reg + [changed(sr)] + reg + sl, "slot_root_mismatch")
        add("slotstate", count, index, slot, 1, slot_v, changed(slot_root), both, "state_root_mismatch")
        bad_reg = slot_reg.copy()
        bad_reg[i % 40] = changed(bad_reg[i % 40])
        add("slotstate", count, index, slot, 1, slot_v, slot_root,
            bad_reg + [sr] + reg + sl, "root_mismatch")
        add("slotstate", count, index, slot, 1, (changed(slot_v[0]), *slot_v[1:]),
            slot_root, both, "root_mismatch")
        add("slotstate", count, index, slot, 1, slot_v, slot_root, both[:-1], "error branch_length")
        add("slotstate", count, index, slot, 1, slot_v, slot_root, both + [ZERO], "error branch_length")
        add("slotstate", count, index, slot, 1, slot_v, slot_root,
            slot_reg + [sr] + reg + [b"x"] + sl[1:], "error chunk_width")
        wrong_sr, wrong_reg, wrong_sl = slot_state_fixture(
            slot_root, slot, 37 if fields_count == 28 else 28, slot_rng)
        add("slotstate", count, index, slot, 1, slot_v, slot_root,
            slot_reg + [wrong_sr] + wrong_reg + wrong_sl, "error branch_length")
    # Transport errors must not turn into proof or candidate verdicts.
    valid = rows[0][0].split(" ")
    for field, value, error in [
        (1, "-1", "parse_error"), (2, str(MAX64 + 1), "out_of_range"),
        (3, str(MAX64 + 1), "out_of_range"), (4, "2", "parse_error"),
        (5, "gg", "invalid_hex"), (6, "a", "invalid_hex"),
        (7, str(MAX64 + 1), "out_of_range"), (8, "2", "parse_error"),
        (9, str(MAX64 + 1), "out_of_range"), (10, str(MAX64 + 1), "out_of_range"),
        (11, str(MAX64 + 1), "out_of_range"), (12, str(MAX64 + 1), "out_of_range"),
        (0, "unknown", "unknown_operation"),
    ]:
        edited = valid.copy()
        edited[field] = value
        rows.append((" ".join(edited), "error " + error))
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
    state_row = next(i for i, (row, _) in enumerate(rows) if row.startswith("state32 "))
    forged = expected.copy()
    forged[state_row] = "state_root_mismatch" if expected[state_row] != "state_root_mismatch" else "candidate_not_authenticated"
    try:
        compare(rows, forged)
    except ValueError:
        pass
    else:
        raise ValueError("state comparator corruption not detected")
    slot_row = next(i for i, (row, _) in enumerate(rows) if row.startswith("slotstate "))
    forged = expected.copy()
    forged[slot_row] = "slot_root_mismatch"
    try:
        compare(rows, forged)
    except ValueError:
        pass
    else:
        raise ValueError("slot comparator corruption not detected")
    assert len(rows) == 4613
    print(f"Prepared {len(rows)} rows; six comparator controls detected", flush=True)
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
