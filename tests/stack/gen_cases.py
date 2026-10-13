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

# N-Quads with named graphs and long literals and IRIs. The STRING_LITERAL_QUOTED
# and IRIREF body readers (Syntax/Lexing.lean, readStringLiteralBody and
# readIriRefBody) used one native frame per character until 2026-10-11; a
# 23 MB file with ~6,000-character geo:asWKT literals then exhausted the wasm
# stack in `parse(text, {format: 'nquads'})`. Every 1,000th quad here carries
# a LONG_LIT-character WKT literal; every 10,000th has a LONG_LIT-character
# object IRI.
N_QL = int(os.environ.get("STACK_QUADS_LONG", "120000"))
LONG_LIT = int(os.environ.get("STACK_LONG_LITERAL", "20000"))
def nq_long_line(i):
    g = "<http://example.org/g%d>" % (i % 7)
    s = "<http://example.org/s%d>" % (i // 4)
    if i % 1000 == 0:
        pts = ", ".join("%d.%d %d.%d" % (i % 90, k, k % 180, i % 97)
                        for k in range(LONG_LIT // 12))
        wkt = ("POLYGON((%s))" % pts)[:LONG_LIT]
        return ('%s <http://www.opengis.net/ont/geosparql#asWKT> "%s"'
                '^^<http://www.opengis.net/ont/geosparql#wktLiteral> %s .\n'
                % (s, wkt, g))
    if i % 10000 == 5:
        return '%s <http://example.org/link> <http://example.org/%s> %s .\n' % (
            s, "x" * LONG_LIT, g)
    return '%s <http://example.org/p%d> "v%d" %s .\n' % (s, i % 13, i, g)
write("nquads-long-literal.nq", "".join(nq_long_line(i) for i in range(N_QL)))

# ------------------------------------------------------------------ SPARQL
N_UNION = int(os.environ.get("STACK_UNION", "1000"))
arms = " UNION ".join("{ ?s <http://example.org/p%d> ?o }" % i for i in range(N_UNION))
write("sparql-union.rq", "SELECT ?s ?o WHERE { %s }\n" % arms)

N_NEST = int(os.environ.get("STACK_NEST", "1000"))
write("sparql-nested.rq",
      "SELECT ?s WHERE %s{ ?s ?p ?o }%s\n" % ("{ " * N_NEST, " }" * N_NEST))

# ORDER BY with LIMIT over many solution rows: the ordered-prefix merge
# sort (SPARQL/OrderedPrefix.lean, mergeSortPrefix) recurses ceil(log2 n)
# deep and its merge is a loop; a frame per row would overflow here.
N_ORDER = int(os.environ.get("STACK_ORDER_ROWS", "100000"))
write("sparql-order-limit.nq",
      "".join('<http://example.org/s%d> <http://example.org/p> "%d" .\n' % (i, (i * 7919) % N_ORDER)
              for i in range(N_ORDER)))
write("sparql-order-limit.rq",
      "SELECT ?s ?o WHERE { ?s <http://example.org/p> ?o } ORDER BY DESC(?o) LIMIT 3\n")

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
args("args-nquads-long-literal.json",
     open(os.path.join(OUT, "nquads-long-literal.nq")).read(),
     "nquads", "http://example.org/")
args("args-sparql-union.json",
     "<http://example.org/s> <http://example.org/p0> <http://example.org/o> .",
     open(os.path.join(OUT, "sparql-union.rq")).read())
args("args-sparql-nested.json",
     "<http://example.org/s> <http://example.org/p> <http://example.org/o> .",
     open(os.path.join(OUT, "sparql-nested.rq")).read())
args("args-sparql-order-limit.json",
     open(os.path.join(OUT, "sparql-order-limit.nq")).read(),
     open(os.path.join(OUT, "sparql-order-limit.rq")).read())

# ------------------------------------- issue 752 (OKR batch 1 KR 2.6) cases
# Each is above the depth at which the readable recursion overflowed under
# LEAN_STACK_SIZE_KB=512 (measured 2026-10-13 on base 7d314f43, native):
#   rdfxml-collection   rdf:parseType="Collection": 2,000 members ran,
#                       5,000 overflowed (collectionList); case 20,000
#   sparql-collection   INSERT DATA with one collection: 2,000 members ran,
#                       5,000 overflowed (pCollection); case 8,000. The
#                       parser's fuel (topFuel, 10,000) falls by one per
#                       member, so about 10,000 members are a parse error
#                       with or without the loop:
#                       https://github.com/danbri/factoidal/issues/818
#   sparql-replace-long REPLACE over one literal: 5,000 characters ran,
#                       20,000 overflowed (replaceLoop, one frame per
#                       character); case 100,000
# Two cases are expected failures (xfail_issue in run.sh):
#   regex-replace-groups  REPLACE with "$1" over "(a)+": the capture matcher
#                         cmatch recurses once per repetition (4,000 ran,
#                         5,000 overflowed), issue 816; case 5,000
#   rdfc-bnode-chain      two chains of 2,000 blank nodes, each node with its
#                         own literal: RDFC-1.0 Hash N-Degree Quads recurses
#                         once per node of one chain (2,000 overflowed),
#                         issue 817
NQ1 = "<http://example.org/s> <http://example.org/p> <http://example.org/o> ."
N_RX_COLL = int(os.environ.get("STACK_RDFXML_COLLECTION", "20000"))
args("args-rdfxml-collection.json",
     '<?xml version="1.0"?>\n'
     '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
     '         xmlns:ex="http://example.org/">\n'
     '  <rdf:Description rdf:about="http://example.org/s">\n'
     '    <ex:p rdf:parseType="Collection">%s</ex:p>\n'
     '  </rdf:Description>\n'
     '</rdf:RDF>\n' % "".join('<rdf:Description rdf:about="http://example.org/m%d"/>' % i
                              for i in range(N_RX_COLL)),
     "rdfxml", "http://example.org/")
N_SP_COLL = int(os.environ.get("STACK_SPARQL_COLLECTION", "8000"))
args("args-sparql-collection.json", NQ1,
     "INSERT DATA { <http://example.org/s> <http://example.org/q> ( %s ) }"
     % " ".join(str(i) for i in range(N_SP_COLL)))
N_REPL = int(os.environ.get("STACK_REPLACE_CHARS", "100000"))
args("args-sparql-replace-long.json", NQ1,
     'SELECT (STRLEN(REPLACE("%s", "b", "c")) AS ?n) WHERE {}' % ("a" * N_REPL))
N_REPL_G = int(os.environ.get("STACK_REPLACE_GROUP_REPS", "5000"))
args("args-regex-replace-groups.json", NQ1,
     'SELECT (STRLEN(REPLACE("%s", "(a)+", "$1")) AS ?n) WHERE {}' % ("a" * N_REPL_G))
N_RDFC_CHAIN = int(os.environ.get("STACK_RDFC_CHAIN", "2000"))
_chain = []
for _c in "ab":
    for _i in range(N_RDFC_CHAIN):
        _chain.append('_:%s%d <http://example.org/v> "%d" .' % (_c, _i, _i))
        if _i + 1 < N_RDFC_CHAIN:
            _chain.append("_:%s%d <http://example.org/p> _:%s%d ." % (_c, _i, _c, _i + 1))
args("args-rdfc-bnode-chain.json", "\n".join(_chain) + "\n")

# ------------------------------------------------- zstd (Factoidal/qlvr)
# One zstd frame of 1,200,000 QLever-like 8-byte Ids (9,600,000 bytes of
# output, above 8 MiB), level 3 with a content checksum, for
# `l4qlvr-zstd-check frame` (https://github.com/danbri/factoidal/issues/778).
# The expected sha256 is written beside it. Needs the `zstandard` package;
# without it no file is written and run.sh records a failure.
N_ZSTD_IDS = 1200000
try:
    import random
    import zstandard
    zpath = os.path.join(OUT, "zstd-ids.zst")
    if not os.path.exists(zpath) or not os.path.exists(zpath + ".sha256"):
        rnd = random.Random(8878)
        v = (4 << 60) | 137024
        raw = bytearray()
        for _ in range(N_ZSTD_IDS):
            v += rnd.choice((0, 0, 1, 1, 2, 7, 300))
            raw += struct.pack("<Q", v)
        with open(zpath, "wb") as fh:
            fh.write(zstandard.ZstdCompressor(level=3, write_checksum=True).compress(bytes(raw)))
        with open(zpath + ".sha256", "w") as fh:
            fh.write(hashlib.sha256(raw).hexdigest())
except ImportError:
    pass

# ------------------------------------------- SBM11 dictionary (issue 788)
# `l4sbm11-dict-pack` phases 1 and 2 on 150,000 subjects with a run size of
# 20,000 terms (so the external sort writes and merges 15 or more runs), one
# literal of 300,000 bytes (the largest page decode: a front-coded key far
# above any per-byte stack budget), language tags in upper case (folded),
# canonical and non-canonical integers and blank nodes.
N_SBM11 = 150000
SBM11_LIT = 300000
sbm11_path = os.path.join(OUT, "sbm11-dict.nt")
if not os.path.exists(sbm11_path):
    with open(sbm11_path, "w") as fh:
        for i in range(N_SBM11):
            s = "<http://example.org/sbm11/s%07d>" % i
            fh.write('%s <http://example.org/p/label> "label %d"@EN-GB .\n' % (s, i))
            fh.write('%s <http://example.org/p/n> "%d"^^<http://www.w3.org/2001/XMLSchema#int> .\n' % (s, i))
            fh.write('%s <http://example.org/p/m> "0%d"^^<http://www.w3.org/2001/XMLSchema#integer> .\n' % (s, i % 1000))
            fh.write('%s <http://example.org/p/b> _:b%d .\n' % (s, i % 5000))
        fh.write('<http://example.org/sbm11/big> <http://example.org/p/text> "%s" .\n' % ("x" * SBM11_LIT))

# ------------------------------------------- SBM11 delta overlay (issue 791)
# Two SPARQL Update requests over sbm11-dict.nt: DELETE DATA of the p:n quads
# of the first 4,000 subjects, then INSERT DATA of a new p:n value for each
# of them (inside the base blocks: each touched 65,536-row block is merged
# whole) and 4,000 quads of new subjects with new labels (overlay terms,
# sorted after every base id: one chunk after the last block). The merge of
# a 65,536-row block and the compaction scans run over input-proportional
# data. The INSERT DATA request has 8,000 quads. Until 2026-10-13 the case
# used 1,000 and 2,000 quads, because the SPARQL tokenizer was quadratic in
# the request length (stage 5 record section 4: 4,000 quads took 62 s to
# parse; https://github.com/danbri/factoidal/issues/802, repaired by
# `tokenizeLoop_eq_fast` in formal/lean4/L4Factoidal/SPARQL/Tokenizer.lean).
N_DELTA = int(os.environ.get("STACK_SBM11_DELTA", "4000"))
ddel = os.path.join(OUT, "sbm11-delta-del-%d.ru" % N_DELTA)
dins = os.path.join(OUT, "sbm11-delta-ins-%d.ru" % N_DELTA)
if not os.path.exists(dins):
    with open(ddel, "w") as fh:
        fh.write("DELETE DATA {\n")
        for i in range(N_DELTA):
            fh.write('<http://example.org/sbm11/s%07d> <http://example.org/p/n> "%d"^^<http://www.w3.org/2001/XMLSchema#int> .\n' % (i, i))
        fh.write("}\n")
    with open(dins, "w") as fh:
        fh.write("INSERT DATA {\n")
        for i in range(N_DELTA):
            fh.write('<http://example.org/sbm11/s%07d> <http://example.org/p/n> "%d"^^<http://www.w3.org/2001/XMLSchema#int> .\n' % (i, 1000000 + i))
            fh.write('<http://example.org/sbm11/new%07d> <http://example.org/p/label> "new %d"@en .\n' % (i, i))
        fh.write("}\n")

# ------------------------------- browser update log (issue 728, post 18)
# A log of 100,000 records for the ops deltaLogDecode and deltaLogMerge
# (formal/lean4/Wasm/Ops/DeltaLog.lean): one DLB1 record per committed
# update, each one batch of one entry that adds <http://e/s> <http://e/p>
# <http://e/o> to the default graph, seq 0 to 99,999. The decoders over the
# log are loops (one record, one entry per iteration); a frame per record
# would overflow here. The bytes are written here, from the format of
# L4Factoidal/Storage/BrowserLog.lean (DLB1 around DLE1 frames, additive
# mod-2^32 checksums), so the fixture costs no engine run. A wrong byte
# would show as a torn log: run.sh checks that the engine decodes all
# 100,000 batches and reports the log clean.
N_DLOG = int(os.environ.get("STACK_DELTA_RECORDS", "100000"))


def dl_u32(n):
    return struct.pack("<I", n)


def dl_lstring(text):
    b = text.encode()
    return dl_u32(len(b)) + b


def dl_frame(magic, body):
    return dl_u32(magic) + dl_u32(1) + dl_u32(len(body)) + body + dl_u32(sum(body) % 4294967296)


DL_PAYLOAD = (bytes([0])                                   # entry tag: add
              + bytes([0]) + dl_lstring("http://e/s")      # subject: IRI
              + dl_lstring("http://e/p")                   # predicate
              + bytes([0]) + dl_lstring("http://e/o")      # object: IRI
              + bytes([0]))                                # graph: default
DL_ENTRY = dl_frame(0x31454C44, DL_PAYLOAD)               # 'DLE1'


def dl_record(seq):
    body = struct.pack("<QQ", seq, 0) + dl_u32(1) + DL_ENTRY
    return dl_frame(0x31424C44, body)                     # 'DLB1'


dl_hex = "\n".join(dl_record(i).hex() for i in range(N_DLOG))
args("args-delta-log-decode.json", dl_hex)
args("args-delta-log-merge.json", "", dl_hex)

print(json.dumps({
    "dir": OUT, "zstdIds": N_ZSTD_IDS, "entities": N_ENT, "literalBytes": LIT, "collection": N_COLL, "predicates": N_PRED,
    "quads": N_Q, "unionArms": N_UNION, "nestDepth": N_NEST, "orderRows": N_ORDER,
    "jsonldDepth": N_JSONLD, "sbm11Delta": N_DELTA, "shapes": N_SHAPES, "manifestEntries": N_MAN,
    "manifestBytes": len(man), "deltaLogRecords": N_DLOG}))
