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
term), except with ORDER BY, where the sequence is compared; ASK answers as
booleans. Terms compare by type, value, datatype and language tag. Literal
values are compared as written (no value-space equality), so `"01"^^xsd:integer`
and `"1"^^xsd:integer` differ, as they do in RDF term equality. A case where
both engines refuse the query counts apart, not as agreement.

Commands:
  gen --seed S --n N --out cases.jsonl
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


def group(rng, depth=0):
    parts = [bgp(rng)]
    for _ in range(rng.randrange(0, 3)):
        r = rng.random()
        if r < 0.3:
            parts.append(f"OPTIONAL {{ {bgp(rng, 1)} }}")
        elif r < 0.45 and depth == 0:
            parts = [f"{{ {' '.join(parts)} }} UNION {{ {group(rng, depth + 1)} }}"]
        elif r < 0.6:
            parts.append(f"MINUS {{ {bgp(rng, 1)} }}")
        elif r < 0.75:
            parts.append(f"BIND(STR({rng.choice(VARS)}) AS ?z)")
        else:
            parts.append(f"FILTER {filter_expr(rng)}")
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


def gen(seed, n, out):
    rng = random.Random(seed)
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
                text = res.serialize(format=ox.QueryResultsFormat.JSON).decode()
                fout.write(json.dumps({"id": c["id"], "ok": True, "json": text}) + "\n")
            except Exception as e:  # a refusal is an answer of the engine
                fout.write(json.dumps({"id": c["id"], "ok": False, "error": str(e)[:300]}) + "\n")
    print(f"oxigraph {ox.__version__}: answered {cases}")


def norm_term(t):
    if t is None:
        return None
    if t.get("type") == "literal" and "datatype" not in t and "xml:lang" not in t:
        return ("literal", t["value"], XSD + "string", "")
    return (t.get("type").replace("typed-literal", "literal"), t.get("value"), t.get("datatype", XSD + "string" if t.get("type") == "literal" and "xml:lang" not in t else ""), t.get("xml:lang", "").lower())


def norm(text, ordered):
    d = json.loads(text)
    if "boolean" in d:
        return ("ask", d["boolean"])
    vars_ = sorted(d.get("head", {}).get("vars", []))
    rows = [tuple((v, norm_term(b.get(v))) for v in vars_ if b.get(v) is not None)
            for b in d["results"]["bindings"]]
    return ("select", tuple(vars_), tuple(rows) if ordered else tuple(sorted(Counter(rows).items(), key=repr)))


def compare(cases, oxf, fdf, keep=None, out_json=None):
    cs = {json.loads(l)["id"]: json.loads(l) for l in open(cases)}
    ox = {json.loads(l)["id"]: json.loads(l) for l in open(oxf)}
    fd = {json.loads(l)["id"]: json.loads(l) for l in open(fdf)}
    tally = Counter()
    kept = []
    for cid, c in cs.items():
        a, b = ox.get(cid), fd.get(cid)
        if a is None or b is None:
            tally["missing"] += 1
            continue
        if not a["ok"] and not b["ok"]:
            tally["both refuse"] += 1
            continue
        if a["ok"] != b["ok"]:
            tally["one refuses"] += 1
            kept.append((c, a, b, "one refuses"))
            continue
        try:
            same = norm(a["json"], c["ordered"]) == norm(b["json"], c["ordered"])
        except Exception as e:
            same = False
            b = dict(b, error=f"cannot read answer: {e}")
        if same:
            tally["agree"] += 1
        else:
            tally["differ"] += 1
            kept.append((c, a, b, "differ"))
    m = len(cs)
    print(f"sparql differential: agrees on {tally['agree']} of {m} cases; "
          f"{tally['differ']} differ, {tally['one refuses']} refused by one engine, "
          f"{tally['both refuse']} refused by both, {tally['missing']} missing")
    if keep:
        os.makedirs(keep, exist_ok=True)
        for c, a, b, why in kept:
            with open(os.path.join(keep, f"{c['id']}.json"), "w") as fh:
                json.dump({"why": why, "case": c, "oxigraph": a, "factoidal": b}, fh, indent=1)
    if out_json:
        json.dump({"cases": m, **tally}, open(out_json, "w"))
    return 0


def main(argv):
    if not argv:
        print(__doc__); return 2
    cmd = argv[0]
    opt = lambda k, d=None: argv[argv.index(k) + 1] if k in argv else d
    if cmd == "gen":
        gen(int(opt("--seed", "1")), int(opt("--n", "1000")), opt("--out", "cases.jsonl")); return 0
    if cmd == "oxigraph":
        run_oxigraph(argv[1], opt("--out", "ox.jsonl")); return 0
    if cmd == "compare":
        return compare(argv[1], argv[2], argv[3], opt("--keep"), opt("--json"))
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
