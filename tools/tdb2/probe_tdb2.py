#!/usr/bin/env python3
"""Format probe for an Apache Jena TDB2 database directory (read only).

The byte layout is recorded in docs/designissues/2026-10-13-tdb2-format.md,
with the Jena 6.2.0 source file for each rule. This probe is the second,
independent reader of that record: the Lean decoder
(formal/lean4/L4Factoidal/Tdb2/*.lean) is tested against Jena's own
`tdb2.tdbdump`, and this probe against the same dump.

Usage:
  probe_tdb2.py stats DB          generation, state files, tree shapes, counts
  probe_tdb2.py dump DB           N-Quads of every quad (default graph from
                                  SPO, named graphs from GSPO), Jena's term
                                  forms, in index order
  probe_tdb2.py node DB OFFSET    the RDF term at one node-table offset

DB is the database directory (it holds Data-NNNN) or a Data-NNNN directory.
"""
import struct, sys
from decimal import Decimal
from pathlib import Path

BLOCK = 8192
PTR_LEN = 4  # BPlusTreeParams.SizeOfPointer


def generation(db):
    db = Path(db)
    if db.name.startswith("Data-"):
        return db
    gens = sorted(p for p in db.iterdir() if p.is_dir() and p.name.startswith("Data-"))
    if not gens:
        sys.exit(f"{db}: no Data-NNNN directory")
    return gens[-1]


def bpt_state(path):
    """BPTStateMgr: three big-endian longs: root id, node-blocks limit,
    records-blocks limit."""
    b = path.read_bytes()
    return struct.unpack(">qqq", b[:24])


def order(record_len):
    """BPlusTreeParams.calcOrder(8192, recordLength); Gap = 0."""
    x = (BLOCK - 4 - record_len) // (record_len + PTR_LEN)
    return (x + 1) // 2


def tree_records(gen, name, record_len):
    """Every record of the B+tree NAME, in key order, by an explicit-stack
    depth-first walk from the root in NAME.bpt (TDB2 trees are copy on
    write, so the walk follows pointers from the committed root; record-block
    links are not used)."""
    root, _, _ = bpt_state(gen / f"{name}.bpt")
    idn = (gen / f"{name}.idn").read_bytes()
    dat = (gen / f"{name}.dat").read_bytes()
    n = order(record_len)
    max_rec = 2 * n - 1
    out = []
    stack = [("node", root)]
    while stack:
        kind, bid = stack.pop()
        if kind == "node":
            base = bid * BLOCK
            head = struct.unpack(">i", idn[base:base + 4])[0]
            btype, count = (head >> 24) & 0xFF, head & 0x00FFFFFF
            if btype not in (6, 7):
                sys.exit(f"{name}.idn block {bid}: block type {btype}, expected 6 or 7")
            pstart = base + 4 + max_rec * record_len
            ptrs = [struct.unpack(">i", idn[pstart + 4 * i: pstart + 4 * i + 4])[0]
                    for i in range(count + 1)]
            child = "records" if btype == 7 else "node"
            for p in reversed(ptrs):
                stack.append((child, p))
        else:
            base = bid * BLOCK
            count, _link = struct.unpack(">ii", dat[base:base + 8])
            for i in range(count):
                s = base + 8 + i * record_len
                out.append(dat[s:s + record_len])
    return out


# ---------------------------------------------------------------------------
# Thrift compact protocol, the subset RDF_Term uses
# ---------------------------------------------------------------------------
class Reader:
    def __init__(self, b, pos):
        self.b, self.pos = b, pos

    def byte(self):
        v = self.b[self.pos]
        self.pos += 1
        return v

    def varint(self):
        shift = v = 0
        while True:
            x = self.byte()
            v |= (x & 0x7F) << shift
            shift += 7
            if not x & 0x80:
                return v

    def zigzag(self):
        v = self.varint()
        return (v >> 1) ^ -(v & 1)

    def string(self):
        n = self.varint()
        s = self.b[self.pos:self.pos + n].decode("utf-8")
        self.pos += n
        return s

    def double(self):
        v = struct.unpack("<d", self.b[self.pos:self.pos + 8])[0]
        self.pos += 8
        return v

    def struct_(self):
        """{field id: value}; nested structs are dicts."""
        fields, last = {}, 0
        while True:
            h = self.byte()
            if h == 0:
                return fields
            delta, ty = h >> 4, h & 0x0F
            fid = last + delta if delta else self.zigzag()
            last = fid
            if ty in (1, 2):
                v = ty == 1
            elif ty == 3:
                v = self.byte()
            elif ty in (4, 5, 6):
                v = self.zigzag()
            elif ty == 7:
                v = self.double()
            elif ty == 8:
                v = self.string()
            elif ty == 12:
                v = self.struct_()
            else:
                raise ValueError(f"thrift type {ty} not used by RDF_Term")
            fields[fid] = v


XSD = "http://www.w3.org/2001/XMLSchema#"


def esc(s):
    return (s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
            .replace("\r", "\\r"))


def lit(lex, dt=None, lang=None):
    if lang:
        return f'"{esc(lex)}"@{lang}'
    if dt is None or dt == XSD + "string":
        return f'"{esc(lex)}"'
    return f'"{esc(lex)}"^^<{dt}>'


def shortest_digits(a, single):
    """Shortest decimal digits and exponent that read back to a (a > 0):
    (digits, e) with a = 0.digits * 10^e. Java 19+ Double.toString and
    Float.toString choose the shortest such digits (JDK-4511638); Python's
    repr does the same for doubles."""
    r = repr(a)
    if single:
        for prec in range(1, 10):
            r = f"{a:.{prec - 1}e}"
            if struct.unpack("<f", struct.pack("<f", float(r)))[0] == a:
                break
    t = Decimal(r).as_tuple()
    e = len(t.digits) + t.exponent
    return "".join(map(str, t.digits)).rstrip("0") or "0", e


def java_float_string(d, single=False):
    """Double.toString / Float.toString layout: plain for 1e-3 <= |d| < 1e7,
    else d.dddE<n>; at least one digit after the point."""
    if d != d:
        return "NaN"
    if d in (float("inf"), float("-inf")):
        return "Infinity" if d > 0 else "-Infinity"
    sign = "-" if str(d).startswith("-") else ""
    a = abs(d)
    if a == 0:
        return sign + "0.0"
    digits, e = shortest_digits(a, single)
    if 1e-3 <= a < 1e7:
        if e <= 0:
            return sign + "0." + "0" * (-e) + digits
        if len(digits) <= e:
            return sign + digits + "0" * (e - len(digits)) + ".0"
        return sign + digits[:e] + "." + digits[e:]
    return sign + digits[0] + "." + (digits[1:] or "0") + "E" + str(e - 1)


def java_double(d):
    return java_float_string(d)


def xsd_double(d):
    """XSDNumUtils.stringForm(double): INF, -INF, NaN, else Double.toString
    with "e0" appended when it has no exponent."""
    if d != d:
        return "NaN"
    if d in (float("inf"), float("-inf")):
        return "INF" if d > 0 else "-INF"
    x = java_float_string(d)
    return x if "E" in x else x + "e0"


def xsd_float(f):
    if f != f:
        return "NaN"
    if f in (float("inf"), float("-inf")):
        return "INF" if f > 0 else "-INF"
    return java_float_string(f, single=True)


def date_time(v, with_time):
    """DateTimeNode.unpack."""
    bits = lambda lo, n: (v >> lo) & ((1 << n) - 1)
    year, month, day = bits(36, 13), bits(32, 4), bits(27, 5)
    hour, minute, milli = bits(22, 5), bits(16, 6), bits(0, 16)
    tz = (v >> 49) & 0x7F
    s = f"{year:04d}-{month:02d}-{day:02d}"
    if with_time:
        sec, frac = divmod(milli, 1000)
        s += f"T{hour:02d}:{minute:02d}:{sec:02d}"
        if frac:
            if frac % 100 == 0:
                s += f".{frac // 100}"
            elif frac % 10 == 0:
                s += f".{frac // 10:02d}"
            else:
                s += f".{frac:03d}"
    if tz == 0x7F:
        return s + "Z"
    if tz == 0x7E:
        return s
    if tz & 0x40:
        tz -= 0x80
    sign = "-" if tz < 0 else "+"
    tz = abs(tz)
    return s + f"{sign}{tz // 4:02d}:{(tz % 4) * 15:02d}"


def term_of_thrift(t):
    if 1 in t:
        return f"<{t[1][1]}>"
    if 2 in t:
        return f"_:B{t[2][1]}"
    if 3 in t:
        f = t[3]
        return lit(f[1], f.get(3), f.get(2))
    if 10 in t:
        return lit(str(t[10]), XSD + "integer")
    if 11 in t:
        return lit(java_double(t[11]), XSD + "double")
    if 12 in t:
        value, scale = t[12][1], t[12].get(2, 0)
        return lit(plain_decimal(value, scale), XSD + "decimal")
    raise ValueError(f"RDF_Term field {sorted(t)} not decoded")


def plain_decimal(value, scale):
    """BigDecimal.valueOf(value, scale).toPlainString()."""
    neg = value < 0
    digits = str(abs(value))
    if scale <= 0:
        s = digits + "0" * (-scale)
    else:
        digits = digits.rjust(scale + 1, "0")
        s = digits[:-scale] + "." + digits[-scale:]
    return ("-" if neg else "") + s


def canonical_decimal_with_dot(value, scale):
    """XSDNumUtils.canonicalDecimalStrWithDot(BigDecimal.valueOf(value, scale))."""
    if value == 0:
        return "0.0"
    if scale <= 0:
        return plain_decimal(value, scale) + ".0"
    while scale > 0 and value % 10 == 0:
        value //= 10
        scale -= 1
    s = plain_decimal(value, scale)
    return s if "." in s else s + ".0"


DERIVED = {1: "integer", 10: "positiveInteger", 11: "negativeInteger",
           12: "nonNegativeInteger", 13: "nonPositiveInteger", 14: "long", 15: "int",
           16: "short", 17: "byte", 18: "unsignedLong", 19: "unsignedInt",
           20: "unsignedShort", 21: "unsignedByte"}


def sign_extend(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def node_of(nid, obj):
    """NodeIdFactory.create64 + NodeIdInline.extract / NodeTableTRDF."""
    if not nid >> 63:
        return term_of_thrift(Reader(obj, nid).struct_())
    if (nid >> 62) & 1:
        x = nid & ((1 << 62) - 1)
        sign, exp9, sig = (x >> 61) & 1, (x >> 52) & 0x1FF, x & ((1 << 52) - 1)
        exp11 = 0 if exp9 == 0 else 0x7FF if exp9 == 0x1FF else exp9 - 255 + 1023
        d = struct.unpack(">d", struct.pack(">Q", (sign << 63) | (exp11 << 52) | sig))[0]
        return lit(xsd_double(d), XSD + "double")
    ty = (nid >> 56) & 0x7F
    v = nid & ((1 << 56) - 1)
    if ty in DERIVED:
        return lit(str(sign_extend(v, 56)), XSD + DERIVED[ty])
    if ty == 2:
        scale = (v >> 48) & 0xFF
        value = sign_extend(v & ((1 << 48) - 1), 48)
        return lit(canonical_decimal_with_dot(value, scale), XSD + "decimal")
    if ty == 8:
        return lit("true" if v == 1 else "false", XSD + "boolean")
    if ty == 3:
        f = struct.unpack(">f", struct.pack(">I", v & 0xFFFFFFFF))[0]
        return lit(xsd_float(f), XSD + "float")
    if ty in (5, 6):
        return lit(date_time(v, True), XSD + ("dateTime" if ty == 5 else "dateTimeStamp"))
    if ty == 7:
        return lit(date_time(v, False), XSD + "date")
    raise ValueError(f"inline NodeId type {ty} not decoded by the probe")


def quads(gen):
    obj = (gen / "nodes-data.obj").read_bytes()
    cache = {}

    def n(raw):
        nid = struct.unpack(">Q", raw)[0]
        if nid not in cache:
            cache[nid] = node_of(nid, obj)
        return cache[nid]

    for r in tree_records(gen, "SPO", 24):
        yield n(r[0:8]), n(r[8:16]), n(r[16:24]), None
    for r in tree_records(gen, "GSPO", 32):
        yield n(r[8:16]), n(r[16:24]), n(r[24:32]), n(r[0:8])


def main(argv):
    if len(argv) < 2:
        sys.exit(__doc__)
    cmd, gen = argv[0], generation(argv[1])
    jrnl = gen / "journal.jrnl"
    if jrnl.exists() and jrnl.stat().st_size:
        sys.exit(f"{jrnl}: journal not empty ({jrnl.stat().st_size} bytes); recover with Jena first")
    if cmd == "stats":
        print(f"generation {gen.name}")
        for name, rl in (("SPO", 24), ("POS", 24), ("OSP", 24), ("GSPO", 32), ("GPOS", 32),
                         ("GOSP", 32), ("SPOG", 32), ("POSG", 32), ("OSPG", 32), ("nodes", 24)):
            st = bpt_state(gen / f"{name}.bpt")
            print(f"{name}: root={st[0]} node-blocks={st[1]} record-blocks={st[2]} "
                  f"order={order(rl)} records={len(tree_records(gen, name, rl))}")
        print(f"nodes-data.obj bytes={(gen / 'nodes-data.obj').stat().st_size}")
    elif cmd == "dump":
        for s, p, o, g in quads(gen):
            print(f"{s} {p} {o} {g} ." if g else f"{s} {p} {o} .")
    elif cmd == "node":
        print(term_of_thrift(Reader((gen / "nodes-data.obj").read_bytes(), int(argv[2])).struct_()))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
