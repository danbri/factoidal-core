#!/usr/bin/env python3
"""Compare an `l4qlvr query` answer with a QLever SPARQL JSON answer.

https://github.com/danbri/factoidal/issues/778.

Usage: compare_query.py ORACLE.srj ANSWER.json QUERY.rq

Both answers become multisets of solutions. A solution is the set of its
(variable, term) pairs; numeric literals (the integer types, xsd:decimal,
xsd:double, xsd:float) compare by value, other literals by lexical form and
language tag or datatype, IRIs and blank nodes by their value. When the query
has ORDER BY, the sequence of the ORDER BY keys of the rows must also be
equal (rows whose keys are equal may come in any order). Exit 0 when equal;
otherwise print up to 5 differences each way and exit 1.
"""
import json
import re
import sys
from collections import Counter

XSD = "http://www.w3.org/2001/XMLSchema#"
INT_TYPES = {XSD + t for t in (
    "int", "integer", "nonPositiveInteger", "negativeInteger", "long", "short", "byte",
    "nonNegativeInteger", "unsignedLong", "unsignedInt", "unsignedShort", "positiveInteger")}
DOUBLE_TYPES = {XSD + t for t in ("decimal", "double", "float")}


def term_key(b):
    if b is None:
        return ("unbound",)
    t, v = b["type"], b["value"]
    if t == "uri":
        return ("iri", v)
    if t == "bnode":
        return ("bnode", v)
    if "xml:lang" in b:
        return ("lang", v, b["xml:lang"].lower())
    dt = b.get("datatype", XSD + "string")
    if dt in INT_TYPES:
        return ("num", float(int(v)))
    if dt in DOUBLE_TYPES:
        return ("num", float(v))
    return ("typed", v, dt)


def order_vars(query):
    text = " ".join(l for l in query.splitlines() if not l.lstrip().startswith("#"))
    m = re.search(r"ORDER\s+BY\s+(.*?)(LIMIT|OFFSET|$)", text, re.I | re.S)
    if not m:
        return []
    return re.findall(r"\?(\w+)", m.group(1))


def main():
    oracle, answer, query = sys.argv[1:4]
    want_rows = json.load(open(oracle))["results"]["bindings"]
    try:
        got_rows = json.load(open(answer))["results"]["bindings"]
    except (ValueError, KeyError) as e:
        print("answer is not SPARQL JSON: %s" % e)
        return 1

    def sol(r):
        return frozenset((k, term_key(v)) for k, v in r.items())

    want = Counter(sol(r) for r in want_rows)
    got = Counter(sol(r) for r in got_rows)
    ok = True
    detail = []
    if want != got:
        ok = False
        detail.append("DIFFERENT: oracle %d rows, answer %d rows" % (len(want_rows), len(got_rows)))
        for k in list((want - got).keys())[:5]:
            detail.append("  only in oracle: %s" % sorted(k))
        for k in list((got - want).keys())[:5]:
            detail.append("  only in answer: %s" % sorted(k))
    ov = order_vars(open(query).read())
    if ov and ok:
        wk = [tuple(term_key(r.get(v)) for v in ov) for r in want_rows]
        gk = [tuple(term_key(r.get(v)) for v in ov) for r in got_rows]
        if wk != gk:
            ok = False
            first = next(i for i in range(min(len(wk), len(gk))) if wk[i] != gk[i]) \
                if any(a != b for a, b in zip(wk, gk)) else min(len(wk), len(gk))
            detail.append("ORDER DIFFERENT (ORDER BY %s) at row %d: oracle %s, answer %s" % (
                " ".join("?" + v for v in ov), first,
                wk[first] if first < len(wk) else None, gk[first] if first < len(gk) else None))
    if ok:
        print("equal: %d rows%s" % (len(got_rows), ", ORDER BY keys in order" if ov else ""))
        return 0
    print("\n".join(detail))
    return 1


if __name__ == "__main__":
    sys.exit(main())
