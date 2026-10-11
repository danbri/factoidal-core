#!/usr/bin/env python3
"""Canonicalise N-Triples lines for the Factoidal/qlvr dump comparison.

https://github.com/danbri/factoidal/issues/778. Reads lines on stdin, writes
one canonical line per input line on stdout (streaming; nothing is held in
memory). Used by tests/qlvr/run.sh on the lines where the input N-Triples and
the `l4qlvr dump` output differ byte for byte.

Canonical form, both sides:
  * IRIs and literal contents have their N-Triples escapes (ECHAR, UCHAR)
    decoded, then the literal content is escaped as QLever prints it:
    backslash, LF, CR and double quote only (rdfTypes/RdfEscaping.cpp:217-236).

--side input also applies QLever's documented normalisations of numbers
(format record, docs/designissues/2026-10-11-qlever-index-format.md,
section 1):
  * the 12 integer datatypes become xsd:int with the decimal value;
  * xsd:decimal, xsd:double and xsd:float become the binary64 value with
    the 4 lowest mantissa bits cleared, printed with %.1f when integral and
    %.13g otherwise (".0" added when there is no "." or "e"), as xsd:decimal;
    NaN and the infinities as xsd:double.
--side dump leaves numbers as printed (the Lean reader prints QLever's form),
so a normalised match also checks the Lean %.13g formatter.

--classes prints, instead of lines, the count of input lines per rule that
changed them (escape, int-datatype, double).
"""
import math
import re
import struct
import sys
from collections import Counter

XSD = "http://www.w3.org/2001/XMLSchema#"
INT_TYPES = {XSD + t for t in (
    "int", "integer", "nonPositiveInteger", "negativeInteger", "long", "short",
    "byte", "nonNegativeInteger", "unsignedLong", "unsignedInt", "unsignedShort",
    "positiveInteger")}
DOUBLE_TYPES = {XSD + t for t in ("decimal", "double", "float")}

ECHAR = {"t": "\t", "b": "\b", "n": "\n", "r": "\r", "f": "\f", '"': '"', "'": "'", "\\": "\\"}
ESC_RE = re.compile(r'\\(?:u([0-9A-Fa-f]{4})|U([0-9A-Fa-f]{8})|(.))')


def unescape(s):
    def rep(m):
        if m.group(1):
            return chr(int(m.group(1), 16))
        if m.group(2):
            return chr(int(m.group(2), 16))
        return ECHAR.get(m.group(3), "\\" + m.group(3))
    return ESC_RE.sub(rep, s)


def escape(s):
    return s.replace("\\", "\\\\").replace("\n", "\\n").replace("\r", "\\r").replace('"', '\\"')


def qlever_double(v):
    b = struct.unpack("<Q", struct.pack("<d", v))[0] & ~0xF
    v = struct.unpack("<d", struct.pack("<Q", b))[0]
    if math.isnan(v):
        return "NaN", XSD + "double"
    if math.isinf(v):
        return ("INF" if v > 0 else "-INF"), XSD + "double"
    if math.modf(v)[0] == 0.0:
        return "%.1f" % v, XSD + "decimal"
    s = "%.13g" % v
    if "." not in s and "e" not in s:
        s += ".0"
    return s, XSD + "decimal"


TERM_RE = re.compile(r'\s*(<[^>]*>|_:\S+|"(?:[^"\\]|\\.)*"(?:@[A-Za-z0-9-]+|\^\^<[^>]*>)?)')


def terms(line):
    out, pos = [], 0
    for _ in range(3):
        m = TERM_RE.match(line, pos)
        if not m:
            raise ValueError("cannot parse: " + line)
        out.append(m.group(1))
        pos = m.end()
    if line[pos:].strip() != ".":
        raise ValueError("no final dot: " + line)
    return out


def canon_term(t, side, classes):
    if t.startswith("<"):
        u = "<" + unescape(t[1:-1]) + ">"
        if u != t:
            classes.add("escape")
        return u
    if not t.startswith('"'):
        return t
    end = t.rfind('"')
    lex, suffix = unescape(t[1:end]), t[end + 1:]
    if escape(lex) != t[1:end]:
        classes.add("escape")
    if side == "input" and suffix.startswith("^^<"):
        dt = suffix[3:-1]
        if dt in INT_TYPES:
            v = int(lex.strip())
            if dt != XSD + "int" or str(v) != lex:
                classes.add("int-datatype")
            return '"%d"^^<%sint>' % (v, XSD)
        if dt in DOUBLE_TYPES:
            s, ndt = qlever_double(float(lex.strip()))
            if s != lex or ndt != dt:
                classes.add("double")
            return '"%s"^^<%s>' % (s, ndt)
    return '"' + escape(lex) + '"' + suffix


def main():
    side = "dump"
    if "--side" in sys.argv:
        side = sys.argv[sys.argv.index("--side") + 1]
    count_classes = "--classes" in sys.argv
    counts = Counter()
    out = sys.stdout
    for line in sys.stdin:
        line = line.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        classes = set()
        c = " ".join(canon_term(t, side, classes) for t in terms(line)) + " ."
        if count_classes:
            counts["+".join(sorted(classes)) or "unchanged"] += 1
        else:
            out.write(c + "\n")
    if count_classes:
        for k, v in sorted(counts.items()):
            print("%s\t%d" % (k, v))


if __name__ == "__main__":
    main()
