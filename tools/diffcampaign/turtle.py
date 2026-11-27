#!/usr/bin/env python3
"""Random differential campaign: the Turtle reader of Factoidal against Oxigraph's
(https://github.com/danbri/factoidal-core/issues/1184, P7).

A seeded generator writes Turtle 1.1 documents that use the grammar's harder
parts: @prefix and PREFIX, @base and BASE with relative IRI references, prefixed
names with `.`, `-`, `_`, percent and backslash escapes in the local part,
every string form (" ' \"\"\" ''') with escapes including \\u and \\U,
language tags, numeric and boolean shorthand, `a`, predicate and object lists,
blank node labels, blank node property lists (also as subject), and
collections (also empty and nested). Oxigraph reads each document and writes
N-Quads; tools/diffcampaign/turtle-factoidal.mjs reads the same document with
Factoidal, canonicalises both datasets with RDFC-1.0 (Factoidal's
`canonicalize`) and compares the canonical forms. So a difference is a
difference of the readers, up to blank node labels.

Limits: the comparison uses Factoidal's N-Quads reader and canonicaliser on
Oxigraph's output, so a defect shared by those and the Turtle reader is not
seen. A document both readers refuse counts apart.

Commands:
  gen --seed S --n N --out cases.jsonl [--format turtle|trig]
  oxigraph cases.jsonl --out ox.jsonl                 (needs pyoxigraph)
Then: node tools/diffcampaign/turtle-factoidal.mjs cases.jsonl ox.jsonl [module] [--keep DIR]
"""
import json
import random
import sys

XSD = "http://www.w3.org/2001/XMLSchema#"


def local(rng):
    head = rng.choice(["s", "p", "o", "_x", "a1", "Z"])
    tail = rng.choice(["", "1", "-b", ".c", "_d", "%20e", "\\~f", "\\.g", "x.y-z", "é", "a:b"])
    return head + tail


def iri(rng, prefixes):
    r = rng.random()
    if r < 0.45:
        return f"{rng.choice(prefixes)}:{local(rng)}"
    if r < 0.6:
        return rng.choice(["<a>", "<#frag>", "<../up>", "<sub/x?q=1>", "<>"])
    if r < 0.7:
        return f"{rng.choice(prefixes)}:"
    return f"<http://example.org/{local(rng).replace(chr(92), '').replace('%20', '_')}>"


ESC = ["\\t", "\\n", "\\\"", "\\'", "\\\\", "\\u00E9", "\\U0001F600", "\\r", "\\b", "\\f"]


def string(rng):
    body = "".join(rng.choice(["w", "x y", "é", "😀"] + ESC) for _ in range(rng.randrange(0, 4)))
    form = rng.randrange(4)
    if form == 0:
        return f'"{body}"'
    if form == 1:
        return "'" + body + "'"
    if form == 2:
        return '"""' + body + "\nline" + '"""'
    return "'''" + body + " 'q' " + "'''"


def literal(rng, prefixes):
    r = rng.random()
    if r < 0.35:
        s = string(rng)
        k = rng.random()
        if k < 0.3:
            return s + "@" + rng.choice(["en", "en-GB", "fr", "zh-Hant-TW"])
        if k < 0.5:
            return s + f"^^<{XSD}string>"
        return s
    if r < 0.6:
        return rng.choice(["1", "-2", "+3", "0", "2.5", "-0.5", ".5", "1e3", "1.5E-2", "-1e+2", "007"])
    if r < 0.7:
        return rng.choice(["true", "false"])
    return f'"{rng.randrange(100)}"^^{rng.choice(["xsd:integer", f"<{XSD}decimal>", "xsd:boolean"])}'


def obj(rng, prefixes, depth):
    r = rng.random()
    if r < 0.35:
        return iri(rng, prefixes)
    if r < 0.65:
        return literal(rng, prefixes)
    if r < 0.75:
        return f"_:b{rng.randrange(4)}"
    if r < 0.85 and depth < 2:
        return "[ " + predicate_list(rng, prefixes, depth + 1) + " ]"
    if depth < 2:
        items = " ".join(obj(rng, prefixes, depth + 1) for _ in range(rng.randrange(0, 4)))
        return f"( {items} )"
    return "[]"


def predicate_list(rng, prefixes, depth):
    parts = []
    for _ in range(rng.randrange(1, 4)):
        p = "a" if rng.random() < 0.15 else iri(rng, prefixes)
        objs = " , ".join(obj(rng, prefixes, depth) for _ in range(rng.randrange(1, 3)))
        parts.append(f"{p} {objs}")
    sep = rng.choice([" ; ", " ;\n  ", " ; ; "])
    return sep.join(parts) + (" ;" if rng.random() < 0.2 else "")


def document_parts(rng):
    """The prologue lines and the statements (each a whole statement, which may
    span lines, ending with ` .`)."""
    prefixes = ["ex", "e2", ""]
    prologue = [
        rng.choice(["@base <http://example.org/base/> .", "BASE <http://example.org/base/>"]),
        rng.choice(["@prefix ex: <http://example.org/ns#> .", "PREFIX ex: <http://example.org/ns#>"]),
        "@prefix e2: <ns2/> .",
        "@prefix : <http://example.org/default/> .",
        f"@prefix xsd: <{XSD}> .",
    ]
    stmts = []
    for _ in range(rng.randrange(1, 6)):
        r = rng.random()
        if r < 0.15:
            subj = "[ " + predicate_list(rng, prefixes, 1) + " ]"
            if rng.random() < 0.5:
                stmts.append(subj + " .")
                continue
        elif r < 0.3:
            subj = f"_:b{rng.randrange(4)}"
        elif r < 0.38:
            subj = "( " + " ".join(obj(rng, prefixes, 1) for _ in range(rng.randrange(1, 3))) + " )"
        else:
            subj = iri(rng, prefixes)
        stmts.append(f"{subj} {predicate_list(rng, prefixes, 0)} .")
    return prologue, stmts


def document(rng):
    prologue, stmts = document_parts(rng)
    return "\n".join(prologue + stmts) + "\n"


def trig_document(rng):
    """A TriG 1.1 document: the Turtle prologue, then statements in the default
    graph, in `{ }` blocks, and in named graph blocks (`GRAPH g { }` and
    `g { }`, with an IRI or blank node graph name)."""
    prologue, body = document_parts(rng)
    prefixes = ["ex", "e2", ""]
    out, i = list(prologue), 0
    while i < len(body):
        k = rng.randrange(1, 3)
        chunk = body[i:i + k]
        i += k
        r = rng.random()
        if r < 0.25:
            out.extend(chunk)
            continue
        inner = "\n".join(chunk)
        if rng.random() < 0.3 and inner.endswith(" ."):
            inner = inner[:-2]  # the last triple of a block may omit its '.'
        name = iri(rng, prefixes) if rng.random() < 0.8 else f"_:g{rng.randrange(3)}"
        if r < 0.45:
            out.append("{ " + inner + " }")
        elif r < 0.7:
            out.append(f"GRAPH {name} {{ {inner} }}")
        else:
            out.append(f"{name} {{ {inner} }}")
    return "\n".join(out) + "\n"


def gen(seed, n, out, fmt="turtle"):
    rng = random.Random(seed)
    make = trig_document if fmt == "trig" else document
    with open(out, "w") as fh:
        for i in range(n):
            fh.write(json.dumps({"id": f"{fmt[0]}{seed}-{i}", "format": fmt, "data": make(rng)}, ensure_ascii=False) + "\n")
    print(f"generated {n} {fmt} documents, seed {seed}")


def run_oxigraph(cases, out):
    import pyoxigraph as ox
    with open(cases) as fin, open(out, "w") as fout:
        for line in fin:
            c = json.loads(line)
            try:
                fmt = {"trig": ox.RdfFormat.TRIG, "rdfxml": ox.RdfFormat.RDF_XML}.get(c.get("format"), ox.RdfFormat.TURTLE)
                quads = list(ox.parse(c["data"].encode(), format=fmt,
                                      base_iri="http://example.org/base/"))
                nq = ox.serialize(quads, format=ox.RdfFormat.N_QUADS).decode()
                fout.write(json.dumps({"id": c["id"], "ok": True, "nquads": nq}, ensure_ascii=False) + "\n")
            except Exception as e:
                fout.write(json.dumps({"id": c["id"], "ok": False, "error": str(e)[:300]}) + "\n")
    print(f"oxigraph {ox.__version__}: read {cases}")


def main(argv):
    if not argv:
        print(__doc__); return 2
    opt = lambda k, d=None: argv[argv.index(k) + 1] if k in argv else d
    if argv[0] == "gen":
        gen(int(opt("--seed", "1")), int(opt("--n", "1000")), opt("--out", "cases.jsonl"), opt("--format", "turtle")); return 0
    if argv[0] == "oxigraph":
        run_oxigraph(argv[1], opt("--out", "ox.jsonl")); return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
