#!/usr/bin/env python3
"""differential.py BIN TMPDIR -- see run.sh."""
import hashlib
import random
import shutil
import subprocess
import sys

BIN, TMP = sys.argv[1], sys.argv[2]
CHUNK = 65536
READERS = ("leaves", "tree", "cached")
# (chunks, bytes in the last chunk): one chunk whole, short and tiny, exact multiples, short tails
SHAPES = [(1, 65536), (1, 1), (1, 777), (2, 65536), (2, 1), (3, 65535), (4, 5), (5, 1000),
          (8, 65536), (9, 31), (17, 65536)]
passed = failed = 0


def run(args):
    r = subprocess.run([BIN] + args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return r.returncode, r.stdout.decode(), r.stderr.decode()


def check(ok, what):
    global passed, failed
    if ok:
        passed += 1
    else:
        failed += 1
        print("FAIL " + what)


random.seed(7)
for chunks, tail in SHAPES:
    d = f"{TMP}/c{chunks}_{tail}"
    rc, out, err = run(["make", d, str(chunks), str(tail)])
    if rc != 0:
        check(False, f"make {chunks} {tail}: exit {rc}: {err[:200]}")
        continue
    data = open(f"{d}/file.bin", "rb").read()
    n = len(data)
    check(n == (chunks - 1) * CHUNK + tail, f"make {chunks} {tail}: {n} bytes")
    ranges = [(0, n), (0, 1), (n - 1, 1)] + ([(CHUNK - 1, 2)] if n > CHUNK else [])
    for _ in range(10):
        o = random.randrange(n)
        ranges.append((o, random.randrange(1, n - o + 1)))
    for o, l in ranges:
        want = hashlib.sha256(data[o:o + l]).hexdigest()
        for reader in READERS:
            rc, out, err = run(["read", d, "--reader", reader, "--offset", str(o), "--length", str(l), "--check"])
            check(rc == 0 and f"sha256={want}" in out and "match=true" in out,
                  f"{reader} {chunks} chunks tail {tail} range {o}+{l}: exit {rc} {out[:160]!r} {err[:120]!r}")
    for o, l in [(n, 1), (0, n + 1), (n - 1, 2), (0, 0)]:
        for reader in READERS:
            rc, out, err = run(["read", d, "--reader", reader, "--offset", str(o), "--length", str(l)])
            check(rc == 1, f"{reader} {chunks} chunks tail {tail}: range {o}+{l} outside the file or empty: exit {rc}")
    for k in range(chunks):
        d2 = f"{TMP}/t{chunks}_{tail}_{k}"
        shutil.copytree(d, d2)
        b = bytearray(data)
        pos = min(k * CHUNK + 100, n - 1)
        b[pos] ^= 1
        open(f"{d2}/file.bin", "wb").write(b)
        other = 0 if k != 0 else chunks - 1
        for reader in READERS:
            for o, l in [(0, n), (pos, 1), (k * CHUNK, min(CHUNK, n - k * CHUNK))]:
                rc, out, err = run(["read", d2, "--reader", reader, "--offset", str(o), "--length", str(l)])
                check(rc == 1, f"{reader} {chunks} chunks tail {tail}: byte {pos} changed, range {o}+{l} not refused: exit {rc}")
            if chunks > 1:
                o = other * CHUNK
                rc, out, err = run(["read", d2, "--reader", reader, "--offset", str(o), "--length", str(min(CHUNK, n - o))])
                check(rc == 0, f"{reader} {chunks} chunks tail {tail}: byte {pos} changed, chunk {other} refused: exit {rc} {err[:120]!r}")
        shutil.rmtree(d2)
    shutil.rmtree(d)
print(f"merkle-range: {passed} pass, {failed} fail (out of {passed + failed})")
sys.exit(0 if failed == 0 else 1)
