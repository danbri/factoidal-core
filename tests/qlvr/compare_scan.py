#!/usr/bin/env python3
"""Compare `l4qlvr scan` output with a QLever SPARQL JSON answer.

https://github.com/danbri/factoidal/issues/778.

Usage: compare_scan.py ORACLE.srj SCAN.nt SUBJVAR OBJVAR

The oracle answers `SELECT ?SUBJVAR ?OBJVAR WHERE { ?SUBJVAR <p> ?OBJVAR }`;
the scan prints `s <p> o .` lines. Both become multisets of (subject, object)
RDF terms. Numeric literals (xsd:int and the other integer types, xsd:decimal,
xsd:double, xsd:float) compare by value: (integer or float, value). Other
terms compare as N-Triples text with QLever's escaping. Exit 0 when the two
multisets are equal; otherwise print up to 5 differences each way and exit 1.
"""
import json
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import canon_nt  # noqa: E402

XSD = canon_nt.XSD


def value_key(term):
    if term.startswith('"') and "^^<" in term:
        end = term.rfind('"')
        lex, dt = canon_nt.unescape(term[1:end]), term[end + 3:-1]
        if dt in canon_nt.INT_TYPES:
            return ("int", int(lex))
        if dt in canon_nt.DOUBLE_TYPES:
            return ("num", float(lex))
    if term.startswith("<"):
        return ("iri", canon_nt.unescape(term[1:-1]))
    return ("term", canon_nt.canon_term(term, "dump", set()))


def srj_term(b):
    t, v = b["type"], b["value"]
    if t == "uri":
        return "<" + v + ">"
    if t == "bnode":
        return "_:" + v
    s = '"' + canon_nt.escape(v) + '"'
    if "xml:lang" in b:
        return s + "@" + b["xml:lang"]
    if "datatype" in b:
        return s + "^^<" + b["datatype"] + ">"
    return s


def main():
    srj, scan, sv, ov = sys.argv[1:5]
    rows = json.load(open(srj))["results"]["bindings"]
    want = Counter((value_key(srj_term(r[sv])), value_key(srj_term(r[ov]))) for r in rows)
    got = Counter()
    with open(scan) as f:
        for line in f:
            if line.strip():
                s, _p, o = canon_nt.terms(line.rstrip("\n"))
                got[(value_key(s), value_key(o))] += 1
    if want == got:
        print("equal: %d rows" % sum(got.values()))
        return 0
    print("DIFFERENT: oracle %d rows, scan %d rows" % (sum(want.values()), sum(got.values())))
    for k in list((want - got).keys())[:5]:
        print("  only in oracle:", k)
    for k in list((got - want).keys())[:5]:
        print("  only in scan:", k)
    return 1


if __name__ == "__main__":
    sys.exit(main())
