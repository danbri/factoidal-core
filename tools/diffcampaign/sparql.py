#!/usr/bin/env python3
"""Random differential campaign: Factoidal against Oxigraph on SPARQL 1.1 SELECT
and ASK (https://github.com/danbri/factoidal-core/issues/1184, P7).

Reason: https://www.anthropic.com/research/formal-verification compared an
interpreter with its reference on 1.7 million random programs and stated the
agreement rate. Here a seeded generator writes small graphs (no blank nodes)
and queries (BGP, OPTIONAL, UNION, FILTER, DISTINCT, GROUP BY with COUNT,
MINUS, BIND, ORDER BY with LIMIT on a total order); each engine answers in the
SPARQL 1.1 Query Results JSON Format; the comparer reports "agrees on N of M"
and writes each disagreement as a case to keep.

Comparison: SELECT answers are compared as multisets of rows (variable to
term); with ORDER BY each engine's row order must also be one that SPARQL 1.1
section 15.1 allows (the order of, for example, a simple literal and a
language-tagged literal is left to the implementation, so two different orders
can both be right). ASK answers compare as booleans. Terms compare by type, value, datatype and language tag. Numeric
literals (xsd:integer, decimal, double, float) compare by value, because an
aggregate may be written `2.5` or `2.50`; other literals compare as written.
CONSTRUCT answers (profile ext) compare as sets of N-Triples lines; the
generated data has no blank nodes, so no relabelling is needed. A case where
both engines refuse the query counts apart, not as agreement.

Commands:
  gen --seed S --n N --out cases.jsonl [--profile base|ext]
    ext: property paths, VALUES, subqueries, EXISTS, aggregates with HAVING, CONSTRUCT
  oxigraph cases.jsonl --out ox.jsonl         (needs pyoxigraph)
  compare cases.jsonl ox.jsonl fd.jsonl [--keep DIR] [--json FILE]
The Factoidal side is tools/diffcampaign/sparql-factoidal.mjs.
"""
import json
import os
import random
import sys
from collections import Counter

EX = "http://example.org/"
XSD = "http://www.w3.org/2001/XMLSchema#"
SUBJECTS = [f"{EX}s{i}" for i in range(6)]
PREDICATES = [f"{EX}p{i}" for i in range(4)]
VARS = ["?a", "?b", "?c", "?d"]


def literal(rng):
    k = rng.randrange(4)
    if k == 0:
        return f'"{rng.randrange(6)}"^^<{XSD}integer>', ("num", None)
    if k == 1:
        return f'"w{rng.randrange(4)}"', ("str", None)
    if k == 2:
        return f'"w{rng.randrange(4)}"@{rng.choice(["en", "fr"])}', ("str", None)
    return f'"{rng.randrange(3)}.5"^^<{XSD}decimal>', ("num", None)


def graph(rng):
    triples = set()
    for _ in range(rng.randrange(5, 31)):
        s = rng.choice(SUBJECTS)
        p = rng.choice(PREDICATES)
        o = f"<{rng.choice(SUBJECTS)}>" if rng.random() < 0.5 else literal(rng)[0]
        triples.add(f"<{s}> <{p}> {o} .")
    return "\n".join(sorted(triples)) + "\n"


def term(rng, pos):
    r = rng.random()
    if r < 0.6:
        return rng.choice(VARS)
    if pos == "p":
        return f"<{rng.choice(PREDICATES)}>"
    if pos == "o" and r < 0.75:
        return literal(rng)[0]
    return f"<{rng.choice(SUBJECTS)}>"


def tp(rng):
    p = f"<{rng.choice(PREDICATES)}>" if rng.random() < 0.8 else rng.choice(VARS)
    return f"{term(rng, 's')} {p} {term(rng, 'o')} ."


def bgp(rng, k=None):
    return " ".join(tp(rng) for _ in range(k or rng.randrange(1, 4)))


def filter_expr(rng):
    v = rng.choice(VARS)
    w = rng.choice(VARS)
    return rng.choice([
        f"BOUND({v})", f"!BOUND({v})", f"isIRI({v})", f"isLiteral({v})",
        f"({v} > {rng.randrange(5)})", f"({v} = {w})", f"({v} != {w})",
        f'(STR({v}) = "w{rng.randrange(4)}")', f'(LANG({v}) = "en")',
        f"(DATATYPE({v}) = <{XSD}integer>)", f'REGEX(STR({v}), "^w[0-1]")',
        f"(isNumeric({v}) && {v} >= 2)",
    ])


def group(rng, depth=0, binds=None):
    binds = binds if binds is not None else [0]
    parts = [bgp(rng)]
    for _ in range(rng.randrange(0, 3)):
        r = rng.random()
        if r < 0.3:
            parts.append(f"OPTIONAL {{ {bgp(rng, 1)} }}")
        elif r < 0.45 and depth == 0:
            parts = [f"{{ {' '.join(parts)} }} UNION {{ {group(rng, depth + 1, binds)} }}"]
        elif r < 0.6:
            parts.append(f"MINUS {{ {bgp(rng, 1)} }}")
        elif r < 0.75:
            binds[0] += 1  # a fresh variable each time: BIND to a variable in scope is a syntax error
            parts.append(f"BIND(STR({rng.choice(VARS)}) AS ?z{binds[0]})")
        else:
            parts.append(f"FILTER ({filter_expr(rng)})")  # a Constraint must be bracketed or a call
    return " ".join(parts)


def query(rng):
    where = group(rng)
    r = rng.random()
    if r < 0.12:
        return f"ASK {{ {where} }}", False
    if r < 0.27:
        v = rng.choice(VARS)
        return f"SELECT {v} (COUNT(*) AS ?n) WHERE {{ {where} }} GROUP BY {v}", False
    distinct = "DISTINCT " if rng.random() < 0.3 else ""
    if rng.random() < 0.15:
        return f"SELECT {distinct}?a ?b WHERE {{ {where} }} ORDER BY ?a ?b", True
    return f"SELECT {distinct}* WHERE {{ {where} }}", False


PATHS = ["<{a}>/<{b}>", "<{a}>|<{b}>", "<{a}>*", "<{a}>+", "^<{a}>", "<{a}>?", "(<{a}>/<{b}>)*",
         "!(<{a}>)", "!(<{a}>|^<{b}>)", "<{a}>/^<{b}>", "(<{a}>|<{b}>)+"]


def tp_ext(rng):
    """A triple pattern whose predicate may be a property path (SPARQL 1.1 section 9)."""
    if rng.random() < 0.45:
        a, b = rng.sample(PREDICATES, 2)
        p = rng.choice(PATHS).format(a=a, b=b)
    else:
        p = f"<{rng.choice(PREDICATES)}>" if rng.random() < 0.8 else rng.choice(VARS)
    return f"{term(rng, 's')} {p} {term(rng, 'o')} ."


def group_ext(rng, depth=0):
    parts = [" ".join(tp_ext(rng) for _ in range(rng.randrange(1, 3)))]
    for _ in range(rng.randrange(0, 3)):
        r = rng.random()
        if r < 0.2:
            vals = " ".join(rng.choice([f"<{x}>" for x in SUBJECTS] + ["UNDEF", f'"{rng.randrange(6)}"^^<{XSD}integer>'])
                            for _ in range(rng.randrange(1, 4)))
            parts.append(f"VALUES {rng.choice(VARS)} {{ {vals} }}")
        elif r < 0.35 and depth == 0:
            v = rng.choice(VARS)
            parts.append(f"{{ SELECT {v} (COUNT(*) AS ?k) WHERE {{ {bgp(rng, 1)} }} GROUP BY {v} }}")
        elif r < 0.5:
            parts.append(f"OPTIONAL {{ {tp_ext(rng)} }}")
        elif r < 0.65:
            parts.append(f"FILTER ({filter_expr(rng)})")
        elif r < 0.75:
            parts.append(f"FILTER NOT EXISTS {{ {tp_ext(rng)} }}")
        else:
            parts.append(f"FILTER EXISTS {{ {tp(rng)} }}")
    return " ".join(parts)


def query_ext(rng):
    """Returns (query, ordered, kind); kind is "rows" or "graph" (CONSTRUCT)."""
    where = group_ext(rng)
    r = rng.random()
    if r < 0.15:
        a, b = rng.sample(VARS, 2)
        return f"CONSTRUCT {{ {a} <{EX}q> {b} }} WHERE {{ {where} }}", False, "graph"
    if r < 0.45:
        v, w = rng.sample(VARS, 2)
        agg = rng.choice([f"COUNT(DISTINCT {w})", f"SUM({w})", f"MIN({w})", f"MAX({w})", f"AVG({w})", f"COUNT({w})"])
        having = f" HAVING (COUNT(*) > {rng.randrange(1, 3)})" if rng.random() < 0.3 else ""
        return f"SELECT {v} ({agg} AS ?x) WHERE {{ {where} }} GROUP BY {v}{having}", False, "rows"
    if r < 0.55:
        return f"ASK {{ {where} }}", False, "rows"
    distinct = "DISTINCT " if rng.random() < 0.4 else ""
    return f"SELECT {distinct}* WHERE {{ {where} }}", False, "rows"


def gen(seed, n, out, profile="base"):
    rng = random.Random(seed)
    if profile == "ext":
        with open(out, "w") as fh:
            for i in range(n):
                q, ordered, kind = query_ext(rng)
                fh.write(json.dumps({"id": f"e{seed}-{i}", "data": graph(rng), "query": q, "ordered": ordered, "kind": kind}) + "\n")
        print(f"generated {n} cases, profile ext, seed {seed}")
        return
    with open(out, "w") as fh:
        for i in range(n):
            q, ordered = query(rng)
            fh.write(json.dumps({"id": f"{seed}-{i}", "data": graph(rng), "query": q, "ordered": ordered}) + "\n")
    print(f"generated {n} cases, seed {seed}")


def run_oxigraph(cases, out):
    import pyoxigraph as ox
    with open(cases) as fin, open(out, "w") as fout:
        for line in fin:
            c = json.loads(line)
            try:
                store = ox.Store()
                store.load(c["data"].encode(), format=ox.RdfFormat.N_TRIPLES)
                res = store.query(c["query"])
                if c.get("kind") == "graph":
                    text = ox.serialize(list(res), format=ox.RdfFormat.N_TRIPLES).decode()
                    fout.write(json.dumps({"id": c["id"], "ok": True, "nt": text}, ensure_ascii=False) + "\n")
                    continue
                text = res.serialize(format=ox.QueryResultsFormat.JSON).decode()
                fout.write(json.dumps({"id": c["id"], "ok": True, "json": text}) + "\n")
            except Exception as e:  # a refusal is an answer of the engine
                fout.write(json.dumps({"id": c["id"], "ok": False, "error": str(e)[:300]}) + "\n")
    print(f"oxigraph {ox.__version__}: answered {cases}")


def norm_term(t):
    if t is None:
        return None
    if t.get("type") in ("literal", "typed-literal") and t.get("datatype") in NUMERIC:
        try:  # aggregates: the same value may be written as "2.5" or "2.50"
            return ("literal", round(float(t["value"]), 9), t["datatype"], "")
        except ValueError:
            pass
    if t.get("type") == "literal" and "datatype" not in t and "xml:lang" not in t:
        return ("literal", t["value"], XSD + "string", "")
    return (t.get("type").replace("typed-literal", "literal"), t.get("value"), t.get("datatype", XSD + "string" if t.get("type") == "literal" and "xml:lang" not in t else ""), t.get("xml:lang", "").lower())


NUMERIC = {XSD + t for t in ("integer", "decimal", "double", "float")}


def term_lt(x, y):
    """SPARQL 1.1 section 15.1 order of two terms: True, False, or None when the
    specification leaves the order to the implementation (for example a simple
    literal against a language-tagged literal)."""
    rank = lambda t: 0 if t is None else {"bnode": 1, "uri": 2, "literal": 3}[t[0]]
    rx, ry = rank(x), rank(y)
    if rx != ry:
        return rx < ry
    if x is None or x[0] == "bnode":
        return None if x != y else False
    if x[0] == "uri":
        return x[1] < y[1]
    if x[2] in NUMERIC and y[2] in NUMERIC:
        return float(x[1]) < float(y[1])
    if x[2] == y[2] == XSD + "string" and not x[3] and not y[3]:
        return x[1] < y[1]
    return None if x != y else False


def order_ok(rows, keys):
    """True when no later row sorts strictly before an earlier one, by the
    ORDER BY keys, in the order SPARQL defines."""
    for i in range(len(rows)):
        for j in range(i + 1, len(rows)):
            a, b = dict(rows[i]), dict(rows[j])
            for k in keys:
                if term_lt(b.get(k), a.get(k)):
                    return False
                lt = term_lt(a.get(k), b.get(k))
                if lt is None or lt:
                    break  # undefined, or decided in the right order
    return True


def norm(text, ordered):
    """The answer as a value to compare, and whether its row order is one that
    SPARQL allows for the ORDER BY of the generator (?a then ?b)."""
    d = json.loads(text)
    if "boolean" in d:
        return ("ask", d["boolean"]), True
    vars_ = sorted(d.get("head", {}).get("vars", []))
    rows = [tuple((v, norm_term(b.get(v))) for v in vars_ if b.get(v) is not None)
            for b in d["results"]["bindings"]]
    ok = order_ok(rows, ["a", "b"]) if ordered else True
    return ("select", tuple(vars_), tuple(sorted(Counter(rows).items(), key=repr))), ok


def compare(cases, oxf, fdf, keep=None, out_json=None):
    cs = {json.loads(l)["id"]: json.loads(l) for l in open(cases)}
    ox = {json.loads(l)["id"]: json.loads(l) for l in open(oxf)}
    fd = {json.loads(l)["id"]: json.loads(l) for l in open(fdf)}
    tally = Counter()
    kept = []
    refused = []  # a sample, to find generator defects
    for cid, c in cs.items():
        a, b = ox.get(cid), fd.get(cid)
        if a is None or b is None:
            tally["missing"] += 1
            continue
        if not a["ok"] and not b["ok"]:
            tally["both refuse"] += 1
            if tally["both refuse"] <= 25:
                refused.append((c, a, b))
            continue
        if a["ok"] != b["ok"]:
            tally["one refuses"] += 1
            kept.append((c, a, b, "one refuses"))
            continue
        if c.get("kind") == "graph":
            la = sorted(set(l.strip() for l in a.get("nt", "").splitlines() if l.strip()))
            lb = sorted(set(l.strip() for l in b.get("nt", "").splitlines() if l.strip()))
            if la == lb:
                tally["agree"] += 1
            else:
                tally["differ"] += 1
                kept.append((c, a, b, "differ"))
            continue
        try:
            (va, oka), (vb, okb) = norm(a["json"], c["ordered"]), norm(b["json"], c["ordered"])
        except Exception as e:
            va, oka, vb, okb = 0, True, 1, True
            b = dict(b, error=f"cannot read answer: {e}")
        if va == vb and oka and okb:
            tally["agree"] += 1
        else:
            why = "differ" if va != vb else ("order not allowed: " + ("factoidal" if not okb else "oxigraph"))
            tally["differ"] += 1
            kept.append((c, a, b, why))
    m = len(cs)
    print(f"sparql differential: agrees on {tally['agree']} of {m} cases; "
          f"{tally['differ']} differ, {tally['one refuses']} refused by one engine, "
          f"{tally['both refuse']} refused by both, {tally['missing']} missing")
    if keep:
        os.makedirs(keep, exist_ok=True)
        for c, a, b, why in kept:
            with open(os.path.join(keep, f"{c['id']}.json"), "w") as fh:
                json.dump({"why": why, "case": c, "oxigraph": a, "factoidal": b}, fh, indent=1)
    if keep:
        rdir = os.path.join(os.path.dirname(os.path.abspath(keep)), "both-refused")
        os.makedirs(rdir, exist_ok=True)
        for c, a, b in refused:
            with open(os.path.join(rdir, f"{c['id']}.json"), "w") as fh:
                json.dump({"query": c["query"], "oxigraph": a.get("error"), "factoidal": b.get("error")}, fh, indent=1)
    if out_json:
        json.dump({"cases": m, **tally}, open(out_json, "w"))
    return 0


def main(argv):
    if not argv:
        print(__doc__); return 2
    cmd = argv[0]
    opt = lambda k, d=None: argv[argv.index(k) + 1] if k in argv else d
    if cmd == "gen":
        gen(int(opt("--seed", "1")), int(opt("--n", "1000")), opt("--out", "cases.jsonl"), opt("--profile", "base")); return 0
    if cmd == "oxigraph":
        run_oxigraph(argv[1], opt("--out", "ox.jsonl")); return 0
    if cmd == "compare":
        return compare(argv[1], argv[2], argv[3], opt("--keep"), opt("--json"))
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
