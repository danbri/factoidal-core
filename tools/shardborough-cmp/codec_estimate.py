#!/usr/bin/env python3
"""Size of QLever's sorted ID columns under three codecs.

Usage: python3 -I tools/shardborough-cmp/codec_estimate.py INDEXDIR [BASE]

Reads the six permutations of a QLever index (the format record
docs/designissues/2026-10-11-qlever-index-format.md, section 3), decodes
columns 0, 1 and 2 of every block, and prints per permutation:

  raw8      8 bytes per Id (QLever's in-memory width)
  zstd      QLever's zstd frames for the same three columns (from metadata)
  delta     per block, per column: a column that is constant in the block
            costs 0 bytes (its value is in the block metadata); otherwise
            each value is coded as an unsigned LEB128 of
              col0: the gap to the previous row's col0,
              col1: the gap to the previous col1 when col0 is unchanged,
                    else the value itself,
              col2: the gap to the previous col2 when col0 and col1 are
                    unchanged, else the value itself;
            values are the 60-bit payload of the Id (tag dropped, since a
            Shardborough global id would carry its tag in its own bits).
  for-bits  per block, per column: frame of reference, ceil(log2(max-min+1))
            bits per row.

This is an estimate for the design record
docs/designissues/2026-10-11-shardborough-vs-qlever.md; it writes nothing.
Needs the `zstandard` package (as tools/qlvr/probe_index.py does).
"""
import os
import struct
import sys

import zstandard

I64 = struct.Struct("<q")


class Reader:
    def __init__(self, buf, pos=0):
        self.buf, self.pos = buf, pos

    def u64(self):
        v = struct.unpack_from("<Q", self.buf, self.pos)[0]
        self.pos += 8
        return v

    def i64(self):
        v = struct.unpack_from("<q", self.buf, self.pos)[0]
        self.pos += 8
        return v

    def u8(self):
        v = self.buf[self.pos]
        self.pos += 1
        return v

    def bytes(self, n):
        v = self.buf[self.pos:self.pos + n]
        self.pos += n
        return v


def blocks_of(path):
    with open(path, "rb") as f:
        buf = f.read()
    start = I64.unpack_from(buf, len(buf) - 8)[0]
    r = Reader(buf, start)
    r.u64(); r.u64()
    r.bytes(r.u64())
    out = []
    for _ in range(r.u64()):
        ncol = r.u64()
        cols = [(r.i64(), r.u64()) for _ in range(ncol)]
        rows = r.u64()
        [r.u64() for _ in range(8)]
        if r.u8():
            [r.u64() for _ in range(r.u64())]
        r.u8(); r.u64()
        out.append((cols, rows))
    return buf, out


def leb(n):
    c = 1
    while n >= 128:
        n >>= 7
        c += 1
    return c


PAYLOAD = (1 << 60) - 1


def main():
    d = sys.argv[1]
    base = sys.argv[2] if len(sys.argv) > 2 else "olympics"
    dz = zstandard.ZstdDecompressor()
    print("perm\trows\traw8\tzstd\tdelta\tfor-bits")
    totals = [0, 0, 0, 0]
    for p in ("spo", "sop", "pso", "pos", "osp", "ops"):
        buf, blocks = blocks_of(os.path.join(d, f"{base}.index.{p}"))
        raw = z = dl = fb = nrows = 0
        for cols, rows in blocks:
            nrows += rows
            vals = []
            for c in range(3):
                off, size = cols[c]
                z += size
                data = dz.decompress(buf[off:off + size])
                vals.append([v & PAYLOAD for v in struct.unpack("<%dQ" % rows, data)])
            raw += 3 * 8 * rows
            for c in range(3):
                col = vals[c]
                lo, hi = min(col), max(col)
                if lo == hi:
                    continue
                fb += ((hi - lo).bit_length() * rows + 7) // 8
                for i in range(rows):
                    if i == 0:
                        dl += leb(col[i]); continue
                    same_prefix = all(vals[k][i] == vals[k][i - 1] for k in range(c))
                    if same_prefix and col[i] >= col[i - 1]:
                        dl += leb(col[i] - col[i - 1])
                    else:
                        dl += leb(col[i])
        print(f"{p}\t{nrows}\t{raw}\t{z}\t{dl}\t{fb}")
        for i, v in enumerate((raw, z, dl, fb)):
            totals[i] += v
    print("all6\t-\t" + "\t".join(str(t) for t in totals))


if __name__ == "__main__":
    main()
