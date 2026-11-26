#!/usr/bin/env python3
"""Independent test-only RFC 9380 oracle. hashlib is never a runtime provider."""
import hashlib
import random
import subprocess
import sys
import time

P = int("1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab", 16)
POP = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"
RFC = b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"
# Published RFC 9380 J.10.1 empty-message u[0], u[1], real then imaginary.
KAT = tuple(int(x, 16) for x in (
    "03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8",
    "05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a",
    "02f99798e8a5acdeed60d7e18e9120521ba1f47ec090984662846bc825de191b5b7641148c0dbc237726a334473eee94",
    "145a81e418d4010cc027a68f14391b30074e89e60ee7a22f87217b2f6eb0c4b94c9115b436e6fa4607e95a98de30a435",
))


def oracle(msg, dst):
    dp = dst + len(dst).to_bytes(1, "big")
    h = lambda x: hashlib.sha256(x).digest()
    b0 = h(bytes(64) + msg + (256).to_bytes(2, "big") + bytes(1) + dp)
    blocks = [h(b0 + bytes([1]) + dp)]
    for counter in range(2, 9):
        # Integer XOR provides an independent representation of the digest operation.
        mask = int.from_bytes(b0, "big") ^ int.from_bytes(blocks[-1], "big")
        blocks.append(h(mask.to_bytes(32, "big") + bytes([counter]) + dp))
    expanded = b"".join(blocks)
    return tuple(int.from_bytes(expanded[i:i + 64], "big") % P for i in range(0, 256, 64))


assert oracle(b"", RFC) == KAT
assert oracle(b"", POP) != KAT
rng = random.Random(9380)
rows = []


def token(data):
    return data.hex() or "-"


def field(msg, dst):
    rows.append((f"field {token(msg)} {token(dst)}", "ok " + " ".join(map(str, oracle(msg, dst)))))


def pop(root):
    rows.append((f"pop {token(root)}", "ok " + " ".join(map(str, oracle(root, POP)))))


field(b"", RFC)
field(b"abc", RFC)
for root in (bytes(32), bytes([255]) * 32, bytes(range(32))):
    pop(root)
    field(root, POP)
for _ in range(128):
    root = rng.randbytes(32)
    pop(root)
for size in (0, 1, 31, 32, 33, 55, 56, 63, 64, 65, 127, 128, 129, 255, 256, 1024, 4095, 4096):
    for dst_len in (1, 43, 254, 255):
        field(rng.randbytes(size), rng.randbytes(dst_len))
for size in (0, 1, 31, 33, 96):
    rows.append((f"pop {token(bytes(size))}", "error signing_root_width"))
rows.extend([
    ("field - -", "error dst_width"),
    (f"field - {token(bytes(256))}", "error dst_width"),
    (f"field {token(bytes(4097))} 01", "error resource_limit"),
    (f"field {token(bytes(4097))} -", "error resource_limit"),
    ("pop 0", "error invalid_hex"),
    ("pop gg", "error invalid_hex"),
    ("field - zz", "error invalid_hex"),
    ("field 01", "error operation"),
    ("pop " + "00" * 4500, "error resource_limit"),
])

expected = [y for _, y in rows]


def compare(actual):
    if len(actual) != len(expected):
        raise ValueError("row count")
    for i, (a, b) in enumerate(zip(actual, expected)):
        if a != b:
            raise ValueError(f"row {i}: {a!r} != {b!r}")


compare(expected)
parts = expected[0].split()
mutations = [
    expected[1:], expected + ["ok"],
    [" ".join([parts[0], parts[2], parts[1], *parts[3:]])] + expected[1:],
    ["ok 0 0 0 0"] + expected[1:],
    [*expected[:-1], "error signing_root_width"],
]
for mutation in mutations:
    try:
        compare(mutation)
    except ValueError:
        continue
    raise AssertionError("comparator mutation escaped")
print(f"RFC J.10.1 known answer matched; {len(rows)} expectations; {len(mutations)} controls detected", flush=True)
if sys.argv[1] != "--self-test":
    start = time.monotonic()
    run = subprocess.run([sys.argv[1]], input="\n".join(x for x, _ in rows) + "\n",
                         text=True, capture_output=True, timeout=120, check=True)
    compare(run.stdout.splitlines())
    print(f"PASS {len(rows)}/{len(rows)} actual Lean hash-to-field rows; batch {(time.monotonic() - start)*1000:.3f} ms")
