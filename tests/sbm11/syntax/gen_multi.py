#!/usr/bin/env python3
"""Write one dataset in four syntaxes, big enough to cross many 64 KiB chunks.

Usage: gen_multi.py OUTDIR [SUBJECTS]    (default 1500)

Writes OUTDIR/multi.nt, multi.ttl (the default graph only) and
OUTDIR/multi.nq, multi.trig (the same triples, with named graphs). No blank
nodes: the packs of the four files must be byte-identical in pairs
(multi.nt = multi.ttl, multi.nq = multi.trig), apart from the manifest. The
text has two-byte and three-byte UTF-8 characters in every subject, so chunk
boundaries of the readers fall inside code points and inside tokens.
Deterministic."""
import sys

out = sys.argv[1]
n = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
EX = "http://example.org/"
XSD = "http://www.w3.org/2001/XMLSchema#"
GRAPHS = 4


def triples(i):
    s = f"{EX}s/{i}"
    k = (i * 7 + 3) % n
    # The language-tagged literals come last. Until 2026-10-14 an RDF/XML parser
    # let the language of one property element reach the next (issue 841) and
    # would have read the note of a subject as French if it followed the labels.
    # The order is kept so that the generated datasets, and the numbers measured
    # on them, do not change. The RDF/XML export of this dataset
    # (tests/sbm11/export_roundtrip.sh) writes the properties in key order, so the
    # note does follow the labels there.
    return [
        (f"<{s}>", f"<{EX}name>", f'"Name {i} café 中文 \\"quoted\\""'),
        (f"<{s}>", f"<{EX}age>", f'"{18 + i % 60}"^^<{XSD}integer>'),
        (f"<{s}>", f"<{EX}knows>", f"<{EX}s/{k}>"),
        (f"<{s}>", f"<{EX}born>", f'"19{50 + i % 50}-0{1 + i % 9}-1{i % 10}"^^<{XSD}date>'),
        (f"<{s}>", f"<{EX}score>", f'"{i}.{i % 100:02d}"^^<{XSD}decimal>'),
        (f"<{s}>", f"<{EX}note>", f'"line one\\nline {i}. # not a comment { {i} }"'),
        (f"<{s}>", f"<{EX}label>", f'"hello {i}"@en'),
        (f"<{s}>", f"<{EX}label>", f'"bonjour {i}"@fr'),
    ]


def short(term):
    # <http://example.org/xyz> -> ex:xyz, only where the Turtle name is plain
    if term.startswith(f"<{EX}") and term.endswith(">"):
        rest = term[len(EX) + 1:-1]
        if all(c.isalnum() or c in "_-" for c in rest) and rest and not rest[0].isdigit():
            return "ex:" + rest
        if rest.startswith("s/") and rest[2:].isdigit():
            return f"<{term[1:-1]}>"
    return term.replace(f"^^<{XSD}", "^^xsd:").replace(">", "", 0) if "^^<" in term else term


def ttl_term(t):
    if t.startswith("\"") and "^^<" in t:
        head, dt = t.split("^^<", 1)
        return f"{head}^^xsd:{dt[len(XSD):-1]}"
    return short(t)


graph_of = lambda i: (i * GRAPHS) // n if i % 5 != 0 else None  # every fifth subject: default graph
with open(f"{out}/multi.nt", "w", encoding="utf-8") as nt, \
     open(f"{out}/multi.ttl", "w", encoding="utf-8") as ttl, \
     open(f"{out}/multi.nq", "w", encoding="utf-8") as nq, \
     open(f"{out}/multi.trig", "w", encoding="utf-8") as trig:
    pre = f"@prefix ex: <{EX}> .\n@prefix xsd: <{XSD}> .\n"
    ttl.write(pre)
    trig.write(pre)
    for i in range(n):
        ts = triples(i)
        for s, p, o in ts:
            nt.write(f"{s} {p} {o} .\n")
        body = " ;\n    ".join(f"{ttl_term(p)} {ttl_term(o)}" for _, p, o in ts)
        ttl.write(f"{ttl_term(ts[0][0])} {body} .\n")
    # N-Quads and TriG: graph g holds the subjects whose graph_of is g, in
    # subject order; each graph is one contiguous block, default graph first.
    order = [None] + list(range(GRAPHS))
    for g in order:
        members = [i for i in range(n) if graph_of(i) == g]
        if g is None:
            trig.write("{\n")
        else:
            trig.write(f"GRAPH <{EX}g/{g}> {{\n")
        for i in members:
            ts = triples(i)
            for s, p, o in ts:
                nq.write(f"{s} {p} {o}" + ("" if g is None else f" <{EX}g/{g}>") + " .\n")
            body = " ;\n      ".join(f"{ttl_term(p)} {ttl_term(o)}" for _, p, o in ts)
            trig.write(f"  {ttl_term(ts[0][0])} {body} .\n")
        trig.write("}\n")
