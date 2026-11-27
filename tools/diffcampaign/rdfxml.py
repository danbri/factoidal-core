#!/usr/bin/env python3
"""Random RDF/XML documents for the reader campaign
(https://github.com/danbri/factoidal-core/issues/1184, P7). Same case format as
tools/diffcampaign/turtle.py (`format` = "rdfxml"); Oxigraph reads them with
`turtle.py oxigraph`, and turtle-factoidal.mjs compares.

The generator covers RDF 1.1 XML Syntax: rdf:about, rdf:nodeID, rdf:ID with
xml:base, typed node elements, property attributes, rdf:resource,
rdf:datatype, xml:lang (inherited and overridden), nested node elements,
rdf:parseType "Resource", "Collection" and "Literal", rdf:li, and the
reification of a statement by rdf:ID on a property element.

Usage: python3 tools/diffcampaign/rdfxml.py --seed S --n N --out cases.jsonl
"""
import json
import random
import sys
from xml.sax.saxutils import escape, quoteattr

RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
XSD = "http://www.w3.org/2001/XMLSchema#"


def ident(rng):
    return rng.choice(["s", "p", "o", "a1", "x_y", "Thing", "n-1"]) + rng.choice(["", "1", "2"])


def subject_attrs(rng, ids):
    r = rng.random()
    if r < 0.45:
        return f' rdf:about={quoteattr(rng.choice(["http://example.org/" + ident(rng), ident(rng), "#" + ident(rng), ""]))}'
    if r < 0.65:
        return f' rdf:nodeID="b{rng.randrange(3)}"'
    if r < 0.75:
        i = f"i{len(ids)}"
        ids.append(i)
        return f' rdf:ID="{i}"'
    return ""


def text(rng):
    return escape(rng.choice(["w", "x y", "é", "a < b & c", "", "  sp  ", "line\nbreak", "😀"]))


def prop_name(rng):
    return rng.choice(["ex:p", "ex:q", "ex2:r", "ex:p1"])


def node(rng, depth, ids, indent=""):
    tag = rng.choice(["rdf:Description", "rdf:Description", "ex:Thing", "ex2:Kind"])
    attrs = subject_attrs(rng, ids)
    if rng.random() < 0.3:
        attrs += f' ex:attr={quoteattr(rng.choice(["v", "é", "1"]))}'
    if rng.random() < 0.15:
        # Not xml:lang="" (valid RDF/XML, it removes the language in scope):
        # pyoxigraph 0.5.13 refuses it, so it would hide every other difference.
        attrs += f' xml:lang="{rng.choice(["en", "fr"])}"'
    props = [prop(rng, depth, ids, indent + "  ") for _ in range(rng.randrange(0, 4))]
    if not props:
        return f"{indent}<{tag}{attrs}/>"
    return f"{indent}<{tag}{attrs}>\n" + "\n".join(props) + f"\n{indent}</{tag}>"


def prop(rng, depth, ids, indent):
    name = prop_name(rng)
    extra = ""
    if rng.random() < 0.1:
        i = f"r{len(ids)}"
        ids.append(i)
        extra = f' rdf:ID="{i}"'
    r = rng.random()
    if r < 0.3:
        lang = f' xml:lang="{rng.choice(["en", "en-GB", "de"])}"' if rng.random() < 0.3 else ""
        return f"{indent}<{name}{extra}{lang}>{text(rng)}</{name}>"
    if r < 0.4:
        dt = rng.choice([XSD + "integer", XSD + "string", XSD + "decimal", "http://example.org/dt"])
        return f'{indent}<{name}{extra} rdf:datatype="{dt}">{rng.randrange(20)}</{name}>'
    if r < 0.55:
        ref = rng.choice(["http://example.org/" + ident(rng), "#" + ident(rng), ident(rng)])
        return f"{indent}<{name}{extra} rdf:resource={quoteattr(ref)}/>"
    if r < 0.6:
        return f'{indent}<{name}{extra} rdf:nodeID="b{rng.randrange(3)}"/>'
    if r < 0.7 and depth < 2:
        return f"{indent}<{name}{extra}>\n{node(rng, depth + 1, ids, indent + '  ')}\n{indent}</{name}>"
    if r < 0.78 and depth < 2:
        inner = [prop(rng, depth + 1, ids, indent + "  ") for _ in range(rng.randrange(1, 3))]
        return f'{indent}<{name}{extra} rdf:parseType="Resource">\n' + "\n".join(inner) + f"\n{indent}</{name}>"
    if r < 0.86 and depth < 2:
        items = [node(rng, depth + 1, ids, indent + "  ") for _ in range(rng.randrange(0, 3))]
        return f'{indent}<{name}{extra} rdf:parseType="Collection">\n' + "\n".join(items) + f"\n{indent}</{name}>"
    if r < 0.92:
        xml = rng.choice(["<b>x</b>", "a <i xmlns='http://www.w3.org/1999/xhtml'>b</i> c", "plain", "<ex:e ex:a='1'/>"])
        return f'{indent}<{name}{extra} rdf:parseType="Literal">{xml}</{name}>'
    if r < 0.96:
        return f'{indent}<{name}{extra} ex:a="1" ex:b="2"/>'
    return f"{indent}<rdf:li>{text(rng)}</rdf:li>"


def document(rng):
    ids = []
    base = ' xml:base="http://example.org/base/doc"' if rng.random() < 0.7 else ""
    lang = f' xml:lang="{rng.choice(["en", "fr"])}"' if rng.random() < 0.2 else ""
    nodes = [node(rng, 0, ids, "  ") for _ in range(rng.randrange(1, 4))]
    if rng.random() < 0.15:
        nodes.append('  <rdf:Bag rdf:about="http://example.org/bag">\n    <rdf:li>one</rdf:li>\n    <rdf:li rdf:resource="http://example.org/two"/>\n  </rdf:Bag>')
    return ('<?xml version="1.0"?>\n'
            f'<rdf:RDF xmlns:rdf="{RDF}" xmlns:ex="http://example.org/ns#" xmlns:ex2="http://example.org/ns2/"{base}{lang}>\n'
            + "\n".join(nodes) + "\n</rdf:RDF>\n")


def main(argv):
    opt = lambda k, d=None: argv[argv.index(k) + 1] if k in argv else d
    seed, n, out = int(opt("--seed", "1")), int(opt("--n", "1000")), opt("--out", "cases.jsonl")
    rng = random.Random(seed)
    with open(out, "w") as fh:
        for i in range(n):
            fh.write(json.dumps({"id": f"x{seed}-{i}", "format": "rdfxml", "data": document(rng)}, ensure_ascii=False) + "\n")
    print(f"generated {n} rdfxml documents, seed {seed}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
