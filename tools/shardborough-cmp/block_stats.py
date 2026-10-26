#!/usr/bin/env python3
"""Split the bytes of a Shardborough generation's primary blocks into rows
and dictionary, and count dictionary terms.

Usage: python3 -I tools/shardborough-cmp/block_stats.py GEN-DIR

Reads only the fixed headers (spec section 6.1):
  IBK3: magic 'IBK3', version 3, u32 rowCount, u32 dictionaryBytes; rows of
        16 bytes (position, s, p, o as u32) follow the 13-byte header, then
        the PTD1 dictionary (IndexedBlockWireV3.lean:40-52).
  IBK4/IBK5: magic, version, u32 rowCount, u32 dictionaryBytes,
        u32 graphCount; graphCount * 4 bytes of graph summary; rows of 20
        bytes; then the PTD1/PTD2 dictionary (IndexedBlockWireV4.lean:212-254).
  PTD1/PTD2 prefix: magic, version, u32 termCount, u32 pageTerms,
        u32 pageCount (PagedTermDictionaryCore.lean:54-58).
Prints blocks, rows, row bytes, dictionary bytes, the sum of per-block term
counts, and the dictionary bytes per row. Writes nothing.
"""
import os
import struct
import sys


def main():
    d = sys.argv[1]
    blocks = rows = rowb = dictb = terms = 0
    for n in sorted(os.listdir(d)):
        if not n.startswith("predicate-") or "." not in n:
            continue
        ext = n.rsplit(".", 1)[1]
        if ext not in ("ibk3", "ibk4", "ibk5"):
            continue
        with open(os.path.join(d, n), "rb") as f:
            head = f.read(17)
            rc, db = struct.unpack_from("<II", head, 5)
            if ext == "ibk3":
                rsize, hdr, gc = 16, 13, 0
            else:
                gc = struct.unpack_from("<I", head, 13)[0]
                rsize, hdr = 20, 17
            dstart = hdr + 4 * gc + rsize * rc
            f.seek(dstart)
            ptd = f.read(17)
            tc = struct.unpack_from("<I", ptd, 5)[0]
        blocks += 1
        rows += rc
        rowb += rsize * rc
        dictb += db
        terms += tc
    print(f"blocks\t{blocks}")
    print(f"rows\t{rows}")
    print(f"row_bytes\t{rowb}")
    print(f"dictionary_bytes\t{dictb}")
    print(f"dictionary_terms_summed_over_blocks\t{terms}")
    if rows:
        print(f"dictionary_bytes_per_row\t{dictb / rows:.1f}")
        print(f"terms_per_row\t{terms / rows:.3f}")


if __name__ == "__main__":
    main()
