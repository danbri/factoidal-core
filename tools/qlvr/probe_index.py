#!/usr/bin/env python3
"""Probe a QLever index directory and print what its files contain.

This is a format probe for the Factoidal/qlvr format record
(docs/designissues/2026-10-11-qlever-index-format.md,
https://github.com/danbri/factoidal/issues/778). It is not part of the engine:
the Lean reader is the implementation. The probe exists so that every
"confirmed by the instance" claim in the record can be rerun.

Usage:
  python3 -I tools/qlvr/probe_index.py <index-dir> <basename> [--scan PRED_IRI]
  python3 -I tools/qlvr/probe_index.py <index-dir> <basename> --dump-block0 index.pso

Needs the `zstandard` Python package (pip install zstandard).

With --scan, it decodes the PSO permutation for one bound predicate and
prints the (subject, object) pairs as N-Triples terms, in PSO order.
"""
import json
import os
import struct
import sys

import zstandard

U64 = struct.Struct("<Q")
I64 = struct.Struct("<q")

DATATYPES = ["Undefined", "Bool", "Int", "Double", "VocabIndex",
             "LocalVocabIndex", "SecondaryVocabIndex", "TextRecordIndex",
             "Date", "GeoPoint", "WordVocabIndex", "BlankNodeIndex",
             "EncodedVal"]


class Reader:
    def __init__(self, buf, pos=0):
        self.buf, self.pos = buf, pos

    def u64(self):
        v = U64.unpack_from(self.buf, self.pos)[0]
        self.pos += 8
        return v

    def i64(self):
        v = I64.unpack_from(self.buf, self.pos)[0]
        self.pos += 8
        return v

    def u8(self):
        v = self.buf[self.pos]
        self.pos += 1
        return v

    def f32(self):
        v = struct.unpack_from("<f", self.buf, self.pos)[0]
        self.pos += 4
        return v

    def bytes(self, n):
        v = self.buf[self.pos:self.pos + n]
        self.pos += n
        return v


# --- Id ----------------------------------------------------------------------
def id_split(bits):
    return bits >> 60, bits & ((1 << 60) - 1)


def id_int(payload):
    # NBitInteger<60>: two's complement in the low 60 bits.
    return payload - (1 << 60) if payload & (1 << 59) else payload


def id_double(bits):
    return struct.unpack("<d", U64.pack((bits << 4) & ((1 << 64) - 1)))[0]


# --- FSST --------------------------------------------------------------------
DECODER_BYTES = 8 + 1 + 255 + 255 * 8  # 2304 with the struct's alignment


def read_fsst_decoder(r):
    start = r.pos
    version = r.u64()
    zero_terminated = r.u8()
    lens = r.bytes(255)
    r.pos = start + 264  # 8 + 1 + 255 = 264, already 8-aligned
    symbols = [r.bytes(8) for _ in range(255)]
    assert r.pos - start == 2304
    return {"version": version, "zero": zero_terminated,
            "len": lens, "sym": symbols}


def fsst_decode(dec, data):
    out = bytearray()
    i = 0
    n = len(data)
    while i < n:
        c = data[i]
        i += 1
        if c < 255:
            out += dec["sym"][c][:dec["len"][c]]
        else:
            out.append(data[i])
            i += 1
    return bytes(out)


class Vocabulary:
    """CompressedVocabulary<VocabularyInternalExternal>, FSST applied twice."""

    def __init__(self, d, base):
        p = os.path.join(d, base + ".vocabulary")
        with open(p + ".codebooks", "rb") as f:
            r = Reader(f.read())
        ndec = r.u64()
        self.decoders = []
        for _ in range(ndec):
            self.decoders.append((read_fsst_decoder(r), read_fsst_decoder(r)))
        with open(p + ".words.external.offsets", "rb") as f:
            off = f.read()
        tr = Reader(off, len(off) - 32)
        self.num_offsets, _cap, nbytes = tr.u64(), tr.u64(), tr.u64()
        magic = struct.unpack_from("<II", off, len(off) - 8)
        assert magic == (7601577, 0), magic
        self.offsets = off[:nbytes]
        self.size = self.num_offsets - 1
        self.ext = open(p + ".words.external", "rb")

    def compressed(self, i):
        a, b = struct.unpack_from("<QQ", self.offsets, 8 * i)
        self.ext.seek(a)
        return self.ext.read(b - a)

    def word(self, i):
        d1, d2 = self.decoders[i >> 20]
        # Compressed with d1 then d2; decompress with d2 first.
        return fsst_decode(d1, fsst_decode(d2, self.compressed(i))).decode("utf-8")


def internal_vocab(d, base):
    p = os.path.join(d, base + ".vocabulary.words.internal")
    with open(p, "rb") as f:
        r = Reader(f.read())
    data_size = r.u64()
    r.bytes(data_size)
    noff = r.u64()
    offsets = [r.u64() for _ in range(noff)]
    with open(p + ".ids", "rb") as f:
        r2 = Reader(f.read())
    nid = r2.u64()
    ids = [r2.u64() for _ in range(nid)]
    return data_size, len(offsets) - 1, ids


def term(vocab, bits):
    t, payload = id_split(bits)
    name = DATATYPES[t]
    if name == "VocabIndex":
        return vocab.word(payload)
    if name == "Int":
        return '"%d"^^<http://www.w3.org/2001/XMLSchema#int>' % id_int(payload)
    if name == "Double":
        return '"%r"^^<http://www.w3.org/2001/XMLSchema#double>' % id_double(bits)
    if name == "Bool":
        return '"%s"^^<http://www.w3.org/2001/XMLSchema#boolean>' % (
            "true" if payload & 1 else "false")
    if name == "BlankNodeIndex":
        return "_:bn%d" % payload
    return "%s:%d" % (name, payload)


# --- permutations ------------------------------------------------------------
def read_block_meta(r):
    ncol = r.u64()
    cols = [(r.i64(), r.u64()) for _ in range(ncol)]
    num_rows = r.u64()
    first = [r.u64() for _ in range(4)]
    last = [r.u64() for _ in range(4)]
    has_graphs = r.u8()
    graphs = None
    if has_graphs:
        graphs = [r.u64() for _ in range(r.u64())]
    dup = r.u8()
    block_index = r.u64()
    return {"cols": cols, "rows": num_rows, "first": first, "last": last,
            "graphs": graphs, "dup": dup, "index": block_index}


def read_permutation(path):
    with open(path, "rb") as f:
        buf = f.read()
    start = I64.unpack_from(buf, len(buf) - 8)[0]
    r = Reader(buf, start)
    magic, version = r.u64(), r.u64()
    assert magic == (1 << 64) - 3 and version == 2, (magic, version)
    name = r.bytes(r.u64()).decode()
    blocks = [read_block_meta(r) for _ in range(r.u64())]
    _offset_after = r.i64()
    total, ndistinct = r.u64(), r.u64()
    assert r.pos == len(buf) - 8
    rels = []
    with open(path + ".meta", "rb") as f:
        mbuf = f.read()
    mt = Reader(mbuf, len(mbuf) - 32)
    nrel = mt.u64()
    mr = Reader(mbuf, 0)
    for _ in range(nrel):
        rels.append({"col0": mr.u64(), "rows": mr.u64(), "m1": mr.f32(),
                     "m2": mr.f32(), "offsetInBlock": mr.u64()})
    return {"buf": buf, "name": name, "blocks": blocks, "total": total,
            "distinct": ndistinct, "meta_start": start, "relations": rels}


def decode_column(buf, offset, size, rows):
    raw = zstandard.ZstdDecompressor().decompress(buf[offset:offset + size])
    assert len(raw) == 8 * rows, (len(raw), rows)
    return list(struct.unpack("<%dQ" % rows, raw))


def scan(perm, col0):
    """All rows with first column == col0, from every block whose range covers it."""
    out = []
    for b in perm["blocks"]:
        if not (b["first"][0] <= col0 <= b["last"][0]):
            continue
        cols = [decode_column(perm["buf"], o, s, b["rows"]) for o, s in b["cols"]]
        for i in range(b["rows"]):
            if cols[0][i] == col0:
                out.append(tuple(c[i] for c in cols))
    return out


def dump_block0(path):
    """Print the trailing metadata up to the end of block 0, field by field,
    with the file offset and the raw bytes of each field."""
    with open(path, "rb") as f:
        buf = f.read()
    start = I64.unpack_from(buf, len(buf) - 8)[0]
    r = Reader(buf, start)

    def show(label, n):
        print("%10d  %-30s %s" % (r.pos, label, buf[r.pos:r.pos + n].hex(" ")))

    print("%10d  %-30s %s" % (len(buf) - 8, "start of metadata (i64)",
                              buf[-8:].hex(" ")))
    show("magic", 8); r.u64()
    show("version", 8); r.u64()
    show("name length", 8); n = r.u64()
    print("%10d  %-30s %r" % (r.pos, "name", bytes(r.bytes(n))))
    show("number of blocks", 8); r.u64()
    show("block 0: number of columns", 8); nc = r.u64()
    for c in range(nc):
        show("column %d offsetInFile" % c, 8); r.i64()
        show("column %d compressedSize" % c, 8); r.u64()
    show("numRows", 8); r.u64()
    for k in ("firstTriple", "lastTriple"):
        for c in ("col0", "col1", "col2", "graph"):
            show("%s.%s" % (k, c), 8); v = r.u64()
            print("%10s  %-30s tag %d payload %d" % ("", "", v >> 60,
                                                     v & ((1 << 60) - 1)))
    show("graphInfo present", 1); present = r.u8()
    if present:
        show("graphInfo count", 8); g = r.u64()
        for _ in range(g):
            show("graph Id", 8); r.u64()
    show("containsDuplicates", 1); r.u8()
    show("blockIndex", 8); r.u64()


def main():
    d, base = sys.argv[1], sys.argv[2]
    if "--dump-block0" in sys.argv:
        dump_block0(os.path.join(d, base + "." + sys.argv[sys.argv.index("--dump-block0") + 1]))
        return
    vocab = Vocabulary(d, base)
    print("vocabulary words:", vocab.size, "decoder blocks:", len(vocab.decoders))
    for i in (0, 1, vocab.size - 1):
        print("  word[%d] = %r" % (i, vocab.word(i)))
    dsize, nwords, ids = internal_vocab(d, base)
    print("internal vocabulary: %d words, %d data bytes, first ids %s"
          % (nwords, dsize, ids[:4]))
    for p in ("pso", "pos", "spo", "sop", "osp", "ops"):
        for kind in ("index", "internal.index"):
            path = os.path.join(d, "%s.%s.%s" % (base, kind, p))
            if not os.path.exists(path):
                continue
            perm = read_permutation(path)
            blocks = perm["blocks"]
            ncols = {len(b["cols"]) for b in blocks}
            indices_ok = [b["index"] for b in blocks] == list(range(len(blocks)))
            keys = [tuple(b["first"][:3]) for b in blocks]
            sorted_ok = keys == sorted(keys)
            col_offsets = [o for b in blocks for o, _ in b["cols"]]
            in_file_order = col_offsets == sorted(col_offsets)
            print("%s: name=%r blocks=%d triples=%d distinctCol0=%d columns/block=%s "
                  "relations-in-.meta=%d metadata-at=%d blockIndex=0..n-1:%s "
                  "sorted-by-first-triple:%s column-offsets-ascending:%s"
                  % (os.path.basename(path), perm["name"], len(blocks),
                     perm["total"], perm["distinct"], sorted(ncols),
                     len(perm["relations"]), perm["meta_start"], indices_ok,
                     sorted_ok, in_file_order))
    if "--scan" in sys.argv:
        iri = sys.argv[sys.argv.index("--scan") + 1]
        target = "<%s>" % iri
        # Linear search over the vocabulary; the sort order is ICU collation,
        # so a byte-wise binary search is not valid.
        idx = next(i for i in range(vocab.size) if vocab.word(i) == target)
        col0 = (4 << 60) | idx
        perm = read_permutation(os.path.join(d, base + ".index.pso"))
        rows = scan(perm, col0)
        print("scan %s (VocabIndex %d): %d rows" % (target, idx, len(rows)))
        for row in rows:
            print("%s %s %s ." % (term(vocab, row[1]), target, term(vocab, row[2])))


if __name__ == "__main__":
    main()
