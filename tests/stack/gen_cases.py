#!/usr/bin/env python3
"""Generate the deep-input fixtures for tests/stack.

Every case is an input whose SIZE OR NESTING the caller of a shipped
surface controls.  None of them is unusual RDF; each is only large in the
one dimension that a non-tail recursion turns into stack frames.

Written to the directory given as argv[1].  A case file is regenerated
only when it is missing, so a rerun after a fix is cheap.
"""
import json, os, struct, sys, hashlib

OUT = sys.argv[1]
os.makedirs(OUT, exist_ok=True)


def write(name, text):
    path = os.path.join(OUT, name)
    if not os.path.exists(path):
        with open(path, "w") as fh:
            fh.write(text)
    return path


def write_bytes(name, data):
    path = os.path.join(OUT, name)
    if not os.path.exists(path):
        with open(path, "wb") as fh:
            fh.write(data)
    return path


def args(name, *values):
    path = os.path.join(OUT, name)
    with open(path, "w") as fh:
        json.dump(list(values), fh)
    return path


# ---------------------------------------------------------------- RDF/XML
# 10,000 sequential entity references in one element's content.  Sequential,
# not nested: the depth this can reach is set by the DOCUMENT, and the
# XML declaration itself is legal.
N_ENT = int(os.environ.get("STACK_ENTITIES", "10000"))
ents = "\n".join('<!ENTITY e%d "x">' % i for i in range(8))
refs = "".join("&e%d;" % (i % 8) for i in range(N_ENT))
write("xml-entities.rdf",
      '<?xml version="1.0"?>\n'
      '<!DOCTYPE rdf:RDF [\n%s\n]>\n'
      '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
      '         xmlns:ex="http://example.org/">\n'
      '  <rdf:Description rdf:about="http://example.org/s">\n'
      '    <ex:p>%s</ex:p>\n'
      '  </rdf:Description>\n'
      '</rdf:RDF>\n' % (ents, refs))

# The same references in one attribute value (the scan of a start tag), and
# in the literals of the DTD: an entity value of 10,000 character references
# and an attribute default of 10,000 entity references.  Until 2026-10-10 the
# attribute case overflowed where the content case did (issue 673); the DTD
# case ran.
write("xml-entities-attr.rdf",
      '<?xml version="1.0"?>\n'
      '<!DOCTYPE rdf:RDF [\n%s\n]>\n'
      '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
      '         xmlns:ex="http://example.org/">\n'
      '  <rdf:Description rdf:about="http://example.org/s" ex:p="%s"/>\n'
      '</rdf:RDF>\n' % (ents, refs))
charrefs = "".join("&#%d;" % (120 + i % 3) for i in range(N_ENT))
write("xml-entities-dtd.rdf",
      '<?xml version="1.0"?>\n'
      '<!DOCTYPE rdf:RDF [\n%s\n<!ENTITY big "%s">\n'
      '<!ATTLIST rdf:Description ex:q CDATA "%s">\n]>\n'
      '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
      '         xmlns:ex="http://example.org/">\n'
      '  <rdf:Description rdf:about="http://example.org/s">\n'
      '    <ex:p>&big;</ex:p>\n'
      '  </rdf:Description>\n'
      '</rdf:RDF>\n' % (ents, charrefs, refs))

# NESTED entity expansion (https://github.com/danbri/factoidal/issues/755): a
# chain in which the replacement text of entity N references entity N-1, so
# expanding the last entity goes through every level.  XML 1.0 section 4.1,
# WFC: No Recursion, makes the chain finite, but the document chooses its
# length.  The text chain ends in a literal of N_TEXT_CHAIN characters.  Each
# level of the markup chain holds one property element and the reference to
# the level below, so the ELEMENT nesting stays at one level and only the
# entity nesting grows; the parse gives N_MARKUP_CHAIN triples.
N_TEXT_CHAIN = int(os.environ.get("STACK_TEXT_CHAIN", "10000"))
text_decls = "\n".join(['<!ENTITY t0 "x">'] +
                       ['<!ENTITY t%d "&t%d;y">' % (i, i - 1) for i in range(1, N_TEXT_CHAIN)])
write("xml-text-chain.rdf",
      '<?xml version="1.0"?>\n'
      '<!DOCTYPE rdf:RDF [\n%s\n]>\n'
      '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
      '         xmlns:ex="http://example.org/">\n'
      '  <rdf:Description rdf:about="http://example.org/s">\n'
      '    <ex:p>&t%d;</ex:p>\n'
      '  </rdf:Description>\n'
      '</rdf:RDF>\n' % (text_decls, N_TEXT_CHAIN - 1))
N_MARKUP_CHAIN = int(os.environ.get("STACK_MARKUP_CHAIN", "3000"))
markup_decls = "\n".join(['<!ENTITY m0 "<ex:p>0</ex:p>">'] +
                         ['<!ENTITY m%d "<ex:p>%d</ex:p>&m%d;">' % (i, i, i - 1)
                          for i in range(1, N_MARKUP_CHAIN)])
write("xml-markup-chain.rdf",
      '<?xml version="1.0"?>\n'
      '<!DOCTYPE rdf:RDF [\n%s\n]>\n'
      '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
      '         xmlns:ex="http://example.org/">\n'
      '  <rdf:Description rdf:about="http://example.org/s">&m%d;</rdf:Description>\n'
      '</rdf:RDF>\n' % (markup_decls, N_MARKUP_CHAIN - 1))

# ------------------------------------------------------------------ Turtle
# One literal of 1 MB on one line.
LIT = int(os.environ.get("STACK_LITERAL_BYTES", str(1 << 20)))
write("turtle-literal.ttl",
      '<http://example.org/s> <http://example.org/p> "%s" .\n' % ("a" * LIT))

# A collection of 100,000 elements -- one `( ... )` the parser must close.
N_COLL = int(os.environ.get("STACK_COLLECTION", "100000"))
write("turtle-collection.ttl",
      "@prefix ex: <http://example.org/> .\n"
      "ex:s ex:p ( %s ) .\n" % " ".join("%d" % i for i in range(N_COLL)))

# One statement with 10,000 predicates: `ex:s ex:p0 0 ; ex:p1 1 ; ...`, one
# `;` group per predicate (https://github.com/danbri/factoidal/issues/754).
N_PRED = int(os.environ.get("STACK_PREDICATES", "10000"))
write("turtle-predicates.ttl",
      "@prefix ex: <http://example.org/> .\n"
      "ex:s %s .\n" % " ;\n  ".join("ex:p%d %d" % (i, i) for i in range(N_PRED)))

# ----------------------------------------------------------------- N-Quads
N_Q = int(os.environ.get("STACK_QUADS", "50000"))
write("nquads-one-subject.nq",
      "".join('<http://example.org/s> <http://example.org/p%d> "%d" .\n' % (i, i)
              for i in range(N_Q)))

# ------------------------------------------------------------------ SPARQL
N_UNION = int(os.environ.get("STACK_UNION", "1000"))
arms = " UNION ".join("{ ?s <http://example.org/p%d> ?o }" % i for i in range(N_UNION))
write("sparql-union.rq", "SELECT ?s ?o WHERE { %s }\n" % arms)

N_NEST = int(os.environ.get("STACK_NEST", "1000"))
write("sparql-nested.rq",
      "SELECT ?s WHERE %s{ ?s ?p ?o }%s\n" % ("{ " * N_NEST, " }" * N_NEST))

# -------------------------------------------------------------- JSON-LD
# The nesting is written as text. json.dumps recurses once per nesting level
# and raises RecursionError at 5000 levels on Python 3.13 (issue 749), so no
# nested dict is built and no recursion limit is raised. The text is
# byte-identical to what json.dumps produced for the same nested dict
# (separators ", " and ": "; "@context" is the last key of the outermost
# object); compared at depths 0, 1, 2, 3 and 10 on 2026-10-10.
N_JSONLD = int(os.environ.get("STACK_JSONLD", "5000"))
JSONLD_LEAF = '{"@id": "http://example.org/leaf"}'
JSONLD_ARM = '{"http://example.org/p": ['
if N_JSONLD == 0:
    jsonld_text = JSONLD_LEAF[:-1] + ', "@context": {}}'
else:
    jsonld_text = (JSONLD_ARM * N_JSONLD + JSONLD_LEAF + "]}" * (N_JSONLD - 1)
                   + '], "@context": {}}')
write("jsonld-nested.jsonld", jsonld_text)

# ---------------------------------------------------------------- SHACL
N_SHAPES = int(os.environ.get("STACK_SHAPES", "5000"))
lines = ["@prefix sh: <http://www.w3.org/ns/shacl#> .",
         "@prefix ex: <http://example.org/> .",
         "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> ."]
for i in range(N_SHAPES):
    lines.append("ex:S%d a sh:NodeShape ; sh:targetClass ex:C%d ; "
                 "sh:property [ sh:path ex:p%d ; sh:minCount 1 ; "
                 "sh:datatype xsd:string ] ." % (i, i, i))
write("shacl-shapes.ttl", "\n".join(lines) + "\n")

# --------------------------------------------------------------- manifest
# A synthetic SBM0 manifest of N entries, assembled from the wire format
# in L4Factoidal/Storage/ShardManifest.lean (magic "SBM0", u8 version,
# u32+bytes source identity, then two length-prefixed strings, then a u32
# entry count and that many entries).  Building it from the codec's own
# BYTES rather than through the packer keeps this fixture cheap: the
# packer would need N real blocks on disk.
N_MAN = int(os.environ.get("STACK_MANIFEST", "40000"))


def u32(n):
    return struct.pack("<I", n)


def s(text):
    b = text.encode()
    return u32(len(b)) + b


def manifest(n):
    out = bytearray()
    out += b"SBM0"          # magic
    out += bytes([0])       # wire version 0
    out += s("stack-suite")  # source identity (u32 length + bytes)
    out += s("terms-v0")     # term registry version
    out += s("predicate-ibk2-v0")  # layout
    out += u32(n)
    for i in range(n):
        key = "blocks/p%d.ibk2" % i
        out += s("https://example.test/p%d" % i)   # predicate IRI
        out += s(key)                              # artifact key
        out += u32(4096)                           # artifact bytes
        out += hashlib.sha256(key.encode()).digest()  # sha256, 32 bytes
        out += u32(1)                              # rows
        out += u32(i)                              # ordinal
    return bytes(out)


man = manifest(N_MAN)
write_bytes("manifest-%d.sbm" % N_MAN, man)
args("manifest-args.json", man.hex())

# ------------------------------------------------------ dispatch arg files
args("args-xml.json", open(os.path.join(OUT, "xml-entities.rdf")).read(),
     "rdfxml", "http://example.org/")
args("args-xml-attr.json", open(os.path.join(OUT, "xml-entities-attr.rdf")).read(),
     "rdfxml", "http://example.org/")
args("args-xml-dtd.json", open(os.path.join(OUT, "xml-entities-dtd.rdf")).read(),
     "rdfxml", "http://example.org/")
args("args-xml-text-chain.json",
     open(os.path.join(OUT, "xml-text-chain.rdf")).read(), "rdfxml",
     "http://example.org/")
args("args-xml-markup-chain.json",
     open(os.path.join(OUT, "xml-markup-chain.rdf")).read(), "rdfxml",
     "http://example.org/")
args("args-turtle-literal.json",
     open(os.path.join(OUT, "turtle-literal.ttl")).read(), "turtle",
     "http://example.org/")
args("args-turtle-collection.json",
     open(os.path.join(OUT, "turtle-collection.ttl")).read(), "turtle",
     "http://example.org/")
args("args-turtle-predicates.json",
     open(os.path.join(OUT, "turtle-predicates.ttl")).read(), "turtle",
     "http://example.org/")
args("args-nquads.json", open(os.path.join(OUT, "nquads-one-subject.nq")).read(),
     "nquads", "http://example.org/")
args("args-sparql-union.json",
     "<http://example.org/s> <http://example.org/p0> <http://example.org/o> .",
     open(os.path.join(OUT, "sparql-union.rq")).read())
args("args-sparql-nested.json",
     "<http://example.org/s> <http://example.org/p> <http://example.org/o> .",
     open(os.path.join(OUT, "sparql-nested.rq")).read())

print(json.dumps({
    "dir": OUT, "entities": N_ENT, "literalBytes": LIT, "collection": N_COLL, "predicates": N_PRED,
    "quads": N_Q, "unionArms": N_UNION, "nestDepth": N_NEST,
    "jsonldDepth": N_JSONLD, "shapes": N_SHAPES, "manifestEntries": N_MAN,
    "manifestBytes": len(man)}))
