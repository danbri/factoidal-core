#!/usr/bin/env python3
"""Size of one global term dictionary sorted in unsigned byte order, under
front coding, for the design record
docs/designissues/2026-10-11-shardborough-vs-qlever.md.

Usage: python3 -I tools/shardborough-cmp/dict_estimate.py SIDE-DIR [NT-FILE]

SIDE-DIR is the side index `l4qlvr side-index` writes next to a QLever index
(format record, section "String to Id: the side index"): `words.sorted`
holds every vocabulary word in its stored form (`<iri>`, `"lex"@lang`,
`"lex"^^<dt>`) in unsigned byte order, and `words.entries` holds 24 bytes per
word (u64 offset, u64 length, u64 VocabIndex).

For page sizes 16, 64 and 256 terms it prints:
  raw       the words' bytes
  front     front coding per page: the first word complete (LEB128 length +
            bytes), every next word as LEB128(shared prefix with the previous
            word) + LEB128(suffix length) + suffix bytes; plus 8 bytes of page
            directory per page
  front+z   the same pages each compressed with zstd level 3 (needs the
            `zstandard` package; skipped without it)

With NT-FILE it also counts the xsd:int, xsd:integer, xsd:double and
xsd:decimal literals of the source and how many have a canonical lexical form
(XML Schema 1.1 Part 2 canonical mappings: integers with no leading zeros
or '+'; doubles as the shortest-round-trip mantissa 'D.DDDE[-]N'). Only those
could be stored inline in a 64-bit id without losing RDF term identity.
"""
import os
import re
import struct
import sys

try:
    import zstandard
except ImportError:
    zstandard = None


def leb(n):
    c = 1
    while n >= 128:
        n >>= 7
        c += 1
    return c


def lebb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def shared(a, b):
    n = min(len(a), len(b))
    i = 0
    while i < n and a[i] == b[i]:
        i += 1
    return i


def words(side):
    with open(os.path.join(side, "words.sorted"), "rb") as f:
        data = f.read()
    with open(os.path.join(side, "words.entries"), "rb") as f:
        ent = f.read()
    out = []
    for i in range(len(ent) // 24):
        off, ln, _ = struct.unpack_from("<QQQ", ent, 24 * i)
        out.append(data[off:off + ln])
    return out


def canonical_double(lex):
    try:
        v = float(lex)
    except ValueError:
        return False
    if v != v or v in (float("inf"), float("-inf")):
        return lex in ("NaN", "INF", "-INF")
    r = repr(v)  # shortest round trip
    m = re.fullmatch(r"(-?)(\d+)(?:\.(\d+))?(?:e([+-]?\d+))?", r)
    if not m:
        return False
    sign, ip, fp, ex = m.group(1), m.group(2), m.group(3) or "", int(m.group(4) or 0)
    digits = (ip + fp).lstrip("0") or "0"
    exp = len(ip) - 1 + ex - (len(ip + fp) - len((ip + fp).lstrip("0")))
    if digits == "0":
        canon = sign + "0.0E0"
    else:
        d = digits.rstrip("0") or "0"
        canon = sign + d[0] + "." + (d[1:] or "0") + "E" + str(exp)
    return lex == canon


def main():
    side = sys.argv[1]
    ws = words(side)
    raw = sum(len(w) for w in ws)
    print(f"words\t{len(ws)}\nraw_bytes\t{raw}")
    for page in (16, 64, 256):
        front = 0
        fz = 0
        for p in range(0, len(ws), page):
            chunk = ws[p:p + page]
            buf = bytearray()
            prev = b""
            for i, w in enumerate(chunk):
                if i == 0:
                    buf += lebb(len(w)) + w
                else:
                    s = shared(prev, w)
                    buf += lebb(s) + lebb(len(w) - s) + w[s:]
                prev = w
            front += len(buf) + 8
            if zstandard:
                fz += len(zstandard.ZstdCompressor(level=3).compress(bytes(buf))) + 8
        z = f"\t{fz}" if zstandard else "\t-"
        print(f"page{page}\tfront\t{front}\tfront+z{z}")
    if len(sys.argv) > 2:
        pat = re.compile(rb'"([^"]*)"\^\^<http://www\.w3\.org/2001/XMLSchema#(int|integer|double|decimal)> \.\s*$')
        tot = {}
        can = {}
        distinct = {}
        with open(sys.argv[2], "rb") as f:
            for line in f:
                m = pat.search(line)
                if not m:
                    continue
                lex, dt = m.group(1).decode(), m.group(2).decode()
                tot[dt] = tot.get(dt, 0) + 1
                distinct.setdefault(dt, set()).add(lex)
                if dt in ("int", "integer"):
                    ok = re.fullmatch(r"-?(0|[1-9]\d*)", lex) is not None and lex != "-0"
                elif dt == "double":
                    ok = canonical_double(lex)
                else:
                    ok = re.fullmatch(r"-?(0|[1-9]\d*)\.(0|\d*[1-9])", lex) is not None
                if ok:
                    can[dt] = can.get(dt, 0) + 1
        for dt in sorted(tot):
            print(f"xsd:{dt}\tliterals\t{tot[dt]}\tcanonical\t{can.get(dt, 0)}\tdistinct_lexical\t{len(distinct[dt])}")


if __name__ == "__main__":
    main()
