#!/usr/bin/env python3
"""Write a DLOG (the delta log of an SBM11 generation) of a given number of
entries, in one DLB1 batch, without the Lean writer.

    gen_dlog.py OUT.dlog ENTRIES [--kind rename|insert]

The bytes are the version 1 format of `Storage/DeltaLog.lean` (the module
header there and `docs/designissues/2026-10-12-sbm11-stage5.md` section 2.1):

    DLOG header   'DLOG' u32 version = 1
    DLB1 frame    'DLB1' u32 version = 1, u32 body length, body, u32 checksum
    body          u64 seq, u64 epoch, u32 entry count, then the entries
    DLE1 frame    'DLE1' u32 version = 1, u32 payload length, payload, u32 checksum
    payload       u8 tag (0 add, 1 remove), a triple, a graph (u8 0: default)
    triple        subject (u8 0 IRI, string), predicate (string), object
    object        u8 2 literal, lexical (string), datatype (string), u8 0
    string        u32 byte length, UTF-8 bytes
    checksum      the sum of the bytes it covers, modulo 2^32

Everything is little-endian. The writer does not use the Lean encoder, so a log
made here tests the reader alone, at any size, and a log that the Lean writer
cannot make in the memory of a test machine (issue 857) can still be read.

Kinds. Both are made for a generation packed from N-Triples of the form

    <http://example.org/s{i}> <http://example.org/p> "v{i}" .

* rename: for i = 0, 1, ... ENTRIES/2 - 1, a remove of (s{i}, p, "v{i}") and an
  add of (s{i}, q, "v{i}"). The update `DELETE { ?s ex:p ?o } INSERT { ?s ex:q ?o }
  WHERE { ?s ex:p ?o }` writes the same entries. Every term but `q` is in the
  dictionary of the generation (a lookup that finds the term). ENTRIES must be
  even, and ENTRIES/2 at most the number of statements of the generation.
* insert: ENTRIES adds of (n{i}, p, "w{i}"): no term but `p` is in the
  dictionary (a lookup that finds nothing, and a new overlay term for each).
"""
import struct
import sys

EX = "http://example.org/"
XSD_STRING = "http://www.w3.org/2001/XMLSchema#string"


def lstr(s: str) -> bytes:
    b = s.encode("utf-8")
    return struct.pack("<I", len(b)) + b


def literal(lexical: str) -> bytes:
    return b"\x02" + lstr(lexical) + lstr(XSD_STRING) + b"\x00"


def triple(s: str, p: str, o: bytes) -> bytes:
    return b"\x00" + lstr(s) + lstr(p) + o


def frame(magic: bytes, body: bytes) -> bytes:
    return (magic + struct.pack("<I", 1) + struct.pack("<I", len(body)) + body
            + struct.pack("<I", sum(body) & 0xFFFFFFFF))


def entry(tag: int, s: str, p: str, o: bytes) -> bytes:
    return frame(b"DLE1", bytes([tag]) + triple(s, p, o) + b"\x00")


def entries(kind: str, n: int):
    if kind == "rename":
        if n % 2:
            raise SystemExit("rename needs an even number of entries")
        for i in range(n // 2):
            yield entry(1, f"{EX}s{i}", f"{EX}p", literal(f"v{i}"))
            yield entry(0, f"{EX}s{i}", f"{EX}q", literal(f"v{i}"))
    elif kind == "insert":
        for i in range(n):
            yield entry(0, f"{EX}n{i}", f"{EX}p", literal(f"w{i}"))
    else:
        raise SystemExit("kind is rename or insert")


def main() -> int:
    args = sys.argv[1:]
    kind = "rename"
    if "--kind" in args:
        i = args.index("--kind")
        kind = args[i + 1]
        del args[i:i + 2]
    if len(args) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    out, n = args[0], int(args[1])
    body = struct.pack("<QQI", 1, 1, n) + b"".join(entries(kind, n))
    with open(out, "wb") as f:
        f.write(b"DLOG" + struct.pack("<I", 1) + frame(b"DLB1", body))
    return 0


if __name__ == "__main__":
    sys.exit(main())
