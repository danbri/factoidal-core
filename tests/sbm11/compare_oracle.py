#!/usr/bin/env python3
"""Compare an `l4sbm11 query` answer with the QLever oracle answer.

SBM11 stage 4, https://github.com/danbri/factoidal/issues/790. Record:
docs/designissues/2026-10-12-sbm11-stage4.md section 5.

Usage: compare_oracle.py ORACLE.srj ANSWER.srj QUERY.rq NAME

Both answers become multisets of solutions. A solution is the set of its
(variable, term) pairs; integer, decimal, double and float literals compare
by value, other literals by lexical form and language tag or datatype, IRIs
and blank nodes by their value.

When the query has ORDER BY, the answer's rows must be in SPARQL 1.1 section
15.1 order of the ORDER BY keys (`sparql_key` below: blank nodes, then IRIs by
code point, then literals; numbers by value; other literals by datatype, then
lexical form by code point, then language tag), and the sequence of keys must
equal the oracle's.

The differences of the comparison record
(docs/designissues/2026-10-11-shardborough-vs-qlever.md section 3.3), handled
as that section says:

  q07  QLever orders words by ICU collation of en_US; SPARQL by code point.
       The key sequence is not compared with the oracle's; the answer must be
       in section 15.1 order and equal to the oracle as a multiset.
  q15  QLever folds `1936` (xsd:integer) and "1936"^^xsd:int to one value;
       under RDF term equality the pattern matches nothing. The answer must
       have 0 rows.
  q20  QLever drops 4 mantissa bits and prints %.13g. Doubles are compared
       after rounding to 12 significant digits (all differences are within
       1e-11 relative).

Exit 0 when equal; otherwise print up to 5 differences each way and exit 1.
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

ROUND12 = False


def num(v, dt):
    x = float(int(v)) if dt in INT_TYPES else float(v)
    if ROUND12 and dt in DOUBLE_TYPES:
        x = float("%.11e" % x)
    return x


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
    if dt in INT_TYPES or dt in DOUBLE_TYPES:
        return ("num", num(v, dt))
    return ("typed", v, dt)


def sparql_key(b):
    """Section 15.1 order as a Python sort key."""
    if b is None:
        return (0,)
    t, v = b["type"], b["value"]
    if t == "bnode":
        return (1, v)
    if t == "uri":
        return (2, v)
    dt = b.get("datatype", XSD + "string")
    if "xml:lang" not in b and (dt in INT_TYPES or dt in DOUBLE_TYPES):
        return (4, num(v, dt))
    if "xml:lang" in b:
        dt = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
    return (7, dt, v, b.get("xml:lang", ""))


def order_conds(query):
    text = " ".join(l for l in query.splitlines() if not l.lstrip().startswith("#"))
    m = re.search(r"ORDER\s+BY\s+(.*?)(LIMIT|OFFSET|$)", text, re.I | re.S)
    if not m:
        return []
    out = []
    for desc, var in re.findall(r"(DESC\s*\(\s*)?\?(\w+)", m.group(1), re.I):
        out.append((var, bool(desc)))
    return out


def main():
    global ROUND12
    oracle, answer, query, name = sys.argv[1:5]
    ROUND12 = name.startswith("q20")
    want_rows = json.load(open(oracle))["results"]["bindings"]
    try:
        got_rows = json.load(open(answer))["results"]["bindings"]
    except (ValueError, KeyError) as e:
        print("answer is not SPARQL JSON: %s" % e)
        return 1
    if name.startswith("q15"):
        if len(got_rows) == 0:
            print("expected difference (record 3.3): 0 rows under RDF term equality; QLever %d" % len(want_rows))
            return 0
        print("q15: expected 0 rows, got %d" % len(got_rows))
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
    conds = order_conds(open(query).read())
    if conds and ok:
        # the answer is in section 15.1 order
        def okey(r):
            return [sparql_key(r.get(v)) for v, _ in conds]
        for i in range(1, len(got_rows)):
            a, b = okey(got_rows[i - 1]), okey(got_rows[i])
            for (ka, kb, (_, desc)) in zip(a, b, conds):
                if ka == kb:
                    continue
                if (ka > kb) != desc:
                    ok = False
                    detail.append("NOT IN SECTION 15.1 ORDER at row %d: %s then %s" % (i, a, b))
                break
            if not ok:
                break
        if ok and not name.startswith("q07"):
            wk = [tuple(term_key(r.get(v)) for v, _ in conds) for r in want_rows]
            gk = [tuple(term_key(r.get(v)) for v, _ in conds) for r in got_rows]
            if wk != gk:
                ok = False
                first = next((i for i in range(min(len(wk), len(gk))) if wk[i] != gk[i]), min(len(wk), len(gk)))
                detail.append("ORDER BY keys differ from the oracle at row %d" % first)
    if ok:
        extra = ""
        if conds:
            extra = ", in section 15.1 order" + ("" if name.startswith("q07") else ", keys equal to the oracle's")
        if name.startswith("q07"):
            extra += " (expected difference, record 3.3: QLever's ICU order not compared)"
        if name.startswith("q20"):
            extra += " (doubles to 12 significant digits, record 3.3)"
        print("equal: %d rows%s" % (len(got_rows), extra))
        return 0
    print("\n".join(detail))
    return 1


if __name__ == "__main__":
    sys.exit(main())
