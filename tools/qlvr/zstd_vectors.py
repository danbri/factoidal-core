#!/usr/bin/env python3
"""Write the zstd test vectors for L4Factoidal.Codec.Zstd.

Usage: python3 -I tools/qlvr/zstd_vectors.py OUTDIR

Writes OUTDIR/<name>.zst and OUTDIR/expected.tsv with one line per vector:
name, decompressed size, sha256 of the decompressed bytes. The compressor is
the `zstandard` Python package (libzstd); its version is in the header line
of expected.tsv. Inputs are deterministic, so a rerun with the same libzstd
writes the same files.
"""
import hashlib
import os
import random
import struct
import sys

import zstandard


def text(n):
    words = ("subject predicate object graph literal datatype language "
             "iri blank node triple quad dataset zstd frame block huffman "
             "fse sequence offset match literal-length").split()
    rnd = random.Random(778)
    out = []
    size = 0
    while size < n:
        w = rnd.choice(words)
        out.append(w)
        size += len(w) + 1
    return (" ".join(out))[:n].encode()


def ids(n):
    """QLever-like column: little-endian 8-byte Ids, slowly increasing."""
    rnd = random.Random(8878)
    v = (4 << 60) | 137024
    b = bytearray()
    for _ in range(n):
        v += rnd.choice((0, 0, 1, 1, 2, 7, 300))
        b += struct.pack("<Q", v)
    return bytes(b)


def comp(data, level, checksum, content_size=True):
    c = zstandard.ZstdCompressor(level=level, write_checksum=checksum,
                                 write_content_size=content_size)
    return c.compress(data)


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    rnd = random.Random(1)
    noise = bytes(rnd.getrandbits(8) for _ in range(3000))
    big = (text(16000) * 20)[:300 * 1024]
    vectors = {
        "empty-l3-checksum": (comp(b"", 3, True), b""),
        "hello-l1": (comp(b"hello hello hello hello", 1, False), b"hello hello hello hello"),
        "text-l1": (comp(text(20000), 1, False), text(20000)),
        "text-l3-checksum": (comp(text(20000), 3, True), text(20000)),
        "text-l19-checksum": (comp(text(20000), 19, True), text(20000)),
        "rle-zeros-l3": (comp(bytes(200000), 3, True), bytes(200000)),
        "noise-raw-l1": (comp(noise, 1, True), noise),
        "multiblock-300k-l3-checksum": (comp(big, 3, True), big),
        "multiblock-300k-l19": (comp(big, 19, False), big),
        "ids-l3": (comp(ids(4000), 3, False), ids(4000)),
        "ids-l19-checksum": (comp(ids(4000), 19, True), ids(4000)),
        "no-content-size-l3": (comp(text(5000), 3, True, content_size=False), text(5000)),
    }
    runs = b"".join(bytes([i % 7]) * (500 + i) for i in range(200))
    vectors["rle-runs-l19"] = (comp(runs, 19, True), runs)
    # Two frames with a skippable frame between them.
    skippable = struct.pack("<II", 0x184D2A53, 5) + b"skip!"
    vectors["two-frames-skippable"] = (
        comp(b"first frame ", 3, True) + skippable + comp(text(1000), 3, False),
        b"first frame " + text(1000))
    with open(os.path.join(out, "expected.tsv"), "w") as f:
        f.write("# zstandard %s, libzstd %s; name, size, sha256 of the decompressed bytes\n"
                % (zstandard.__version__, ".".join(map(str, zstandard.ZSTD_VERSION))))
        for name in sorted(vectors):
            blob, raw = vectors[name]
            # Check the expectation against libzstd itself.
            back = zstandard.ZstdDecompressor().decompressobj().decompress(blob) \
                if name != "two-frames-skippable" else raw
            assert back == raw, name
            with open(os.path.join(out, name + ".zst"), "wb") as g:
                g.write(blob)
            f.write("%s\t%d\t%s\n" % (name, len(raw), hashlib.sha256(raw).hexdigest()))


if __name__ == "__main__":
    main()
