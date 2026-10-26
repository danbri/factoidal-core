#!/usr/bin/env python3
"""Differential test of the Turtle writer operations: an OLD and a NEW l4wasm-cli on random cases.

usage: tools/turtle-writer-differential.py OLD_CLI NEW_CLI CASES SEED [WORKDIR]

OLD_CLI is a copy of `formal/lean4/.lake/build/bin/l4wasm-cli` made before a change to the
Turtle writer (`L4Factoidal/Syntax/TurtleSerialize.lean`) or to `declarationOrderPrefixes`
(`Wasm/Ops/Parse.lean`); NEW_CLI is the build after it. The exit code and standard output of
the two must be the same bytes for every case. Exit status 0 when they are, 1 when one case
differs (the case is kept in WORKDIR, default ./diff, as a `callseq` file).

A case is a `l4wasm-cli callseq` file: `datasetOpen` of an N-Triples 1.2 text (triple terms
nested up to 5 deep in the object position) or of a Turtle document with `@prefix` lines (some
labels bound twice); `datasetSerialize`; `datasetSerializeWith` with a random prefix table of
0 to 200 rows (the same namespace in two rows, namespaces inside one another, the empty
namespace, non-ASCII namespaces, labels equal to the derived ones `ns1`, `rdf`, `xsd`) and with
`literalShorthand` false and with `{}`; `serializeTurtleWith` and `serializeTurtle` on the
text when it has no triple term. In half of the cases the table also has 1,100 to 2,100 rows
under `http://pad.example/`, and the graph has a triple for each, so that every row is used and
the writer indexes the table (`Abbreviator`, `prefixIndexRatio`).

Written for https://github.com/danbri/factoidal/issues/864 (2026-10-15). Seeds 101 and 102,
1,500 cases each: 3,568 comparisons, 0 differences, between 6607b7f5 and the change. The
generator is deterministic for a SEED."""
import json, os, random, subprocess, sys, hashlib
if len(sys.argv) < 5:
    sys.exit(__doc__)
old, new, n, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
work = sys.argv[5] if len(sys.argv) > 5 else "diff"
os.makedirs(work, exist_ok=True)
rnd = random.Random(seed)
NS = ["http://e/", "http://e/a/", "http://e/a/b/", "http://e/ab/", "http://e#", "http://e#x/",
      "http://f/", "urn:x:", "urn:x:y:", "http://é.example/", "http://é.example/ü/",
      "", "http://e", "http://e/a", "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
      "http://www.w3.org/2001/XMLSchema#", "http://xmlns.com/foaf/0.1/", "http://schema.org/"]
NS += ["http://g/n%d/" % k for k in range(40)]
LOC = ["x", "y1", "a", "b/c", "d#e", "é", "", "1x", "-x", "x.y", "x.", "%41", "type", "integer", "name"]
LABELS = ["ns1", "ns2", "ns3", "rdf", "xsd", "e", "f", "foaf", "schema", "a", "b", "c", "dcterms"]
XSD = "http://www.w3.org/2001/XMLSchema#"
RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

PAD = 1000
def pad_ns(k): return "http://pad.example/%05d/" % k
def iri():
    r = rnd.random()
    if r < 0.05: return "mailto:a@b"
    if r < 0.12: return pad_ns(rnd.randrange(PAD)) + rnd.choice(LOC)
    return rnd.choice([n for n in NS if n != ""]) + rnd.choice(LOC)
def esc_iri(s):
    return "<" + s.replace(" ", "%20") + ">"
def esc_lit(v):
    return v.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
def lit():
    k = rnd.randrange(8)
    v = esc_lit(rnd.choice(["t", "a b", 'q"uote', "line\nx", "back\\slash", "\u00e9", "5", "-7", "1.5", "1e3", "true", "x.y"]))
    if k == 0: return '"%s"' % v
    if k == 1: return '"%s"@en' % v
    if k == 2: return '"%s"@en-GB' % v
    if k == 3: return '"%s"^^<%sinteger>' % (rnd.choice(["5", "-7", "007"]), XSD)
    if k == 4: return '"%s"^^<%sdecimal>' % (rnd.choice(["1.5", ".5", "5."]), XSD)
    if k == 5: return '"%s"^^<%sboolean>' % (rnd.choice(["true", "false", "1"]), XSD)
    if k == 6: return '"%s"^^%s' % (v, esc_iri(iri()))
    return '"%s"^^<%sdouble>' % (rnd.choice(["1e3", "1.5E-3", "INF"]), XSD)
bn_n = [0]
def bnode():
    return "_:b%d" % rnd.randrange(6)
def subj():
    return esc_iri(iri()) if rnd.random() < 0.8 else bnode()
def pred():
    return "<%s>" % RDF_TYPE if rnd.random() < 0.15 else esc_iri(iri())
def obj(depth):
    r = rnd.random()
    if depth > 0 and r < 0.25:
        return "<<( %s %s %s )>>" % (subj(), pred(), obj(depth - 1))
    if r < 0.55: return esc_iri(iri())
    if r < 0.65: return bnode()
    return lit()
def triples(k):
    return "".join("%s %s %s .\n" % (subj(), pred(), obj(rnd.choice([0, 0, 1, 3, 5]))) for _ in range(k))
def table(size):
    pool = rnd.sample(NS, min(size, len(NS))) if size <= len(NS) else [rnd.choice(NS) for _ in range(size)]
    rows = []
    used = set()
    for i, ns in enumerate(pool):
        lab = rnd.choice(LABELS) + ("" if rnd.random() < 0.5 else str(i)) if rnd.random() < 0.3 else "p%d" % i
        if lab in used: lab = "q%d" % i
        used.add(lab)
        rows.append((lab, ns))
    # duplicates of a namespace under another label, in a random place
    for _ in range(rnd.choice([0, 0, 1, 3])):
        if rows:
            lab, ns = rnd.choice(rows)
            nl = "dup%d" % rnd.randrange(1000)
            if nl not in used:
                used.add(nl); rows.insert(rnd.randrange(len(rows) + 1), (nl, ns))
    return rows
def distinct_lengths(rows):
    return len(set(len(ns) for _, ns in rows))
def pad_rows(rows):
    # grow the table until the writer indexes it: more than 64 rows for each distinct length
    rows = list(rows)
    k = 0
    pads = []
    while len(rows) + len(pads) <= 64 * (distinct_lengths(rows) + 1 + 17) + 8:
        pads.append(("pad%d" % k, pad_ns(k))); k += 1
    cut = rnd.randrange(len(rows) + 1) if rows else 0
    mode = rnd.randrange(3)
    if mode == 0: return rows + pads, len(pads)
    if mode == 1: return pads + rows, len(pads)
    return rows[:cut] + pads + rows[cut:], len(pads)
def pad_triples(npad):
    # one triple for each padding namespace, so the writer keeps every row of the table
    out = []
    for k in range(npad):
        out.append("%s %s %s .\n" % (esc_iri(pad_ns(k) + rnd.choice(LOC)), pred(),
                                     esc_iri(pad_ns((k * 7 + 3) % npad) + rnd.choice(LOC)) if rnd.random() < 0.8 else lit()))
    return "".join(out)
def options(rows, shorthand=True):
    d = {"prefixes": {lab: ns for lab, ns in rows}}
    if not shorthand: d["literalShorthand"] = False
    return json.dumps(d, ensure_ascii=rnd.random() < 0.5)
def ttl_doc():
    # a Turtle document with prefixes declared (some rebound), full-IRI triples
    lines = []
    for _ in range(rnd.choice([0, 1, 5, 17, 40])):
        lab = rnd.choice(LABELS + ["p%d" % rnd.randrange(30)])
        lines.append("@prefix %s: <%s> .\n" % (lab, rnd.choice(NS).replace(" ", "")))
    return "".join(lines) + triples(rnd.randrange(1, 25))

def run(cli, seqfile):
    p = subprocess.run([cli, "callseq", seqfile], capture_output=True, timeout=120)
    return (p.returncode, p.stdout)
def run1(cli, op, argsfile):
    p = subprocess.run([cli, "call", op, argsfile], capture_output=True, timeout=120)
    return (p.returncode, p.stdout)

same = diff = 0
bytes_cmp = 0
stats = {"open_ok": 0, "open_err": 0, "has_tt": 0, "big_table_used": 0, "big_table": 0, "dupes_used": 0}
diffs = []
tsizes = [0, 1, 2, 8, 15, 16, 17, 18, 31, 32, 33, 64, 200]
for i in range(n):
    kind = rnd.choice(["nt", "nt", "ttl"])
    if kind == "nt":
        text = triples(rnd.randrange(1, 40)); fmt = "nt12"
    else:
        text = ttl_doc(); fmt = "turtle12"
    rows = table(rnd.choice(tsizes))
    padded = rnd.random() < 0.5
    if padded:
        rows, npad = pad_rows(rows)
        text += pad_triples(npad)
    stats["padded"] = stats.get("padded", 0) + (1 if padded else 0)
    if padded:
        stats["rows_min"] = min(stats.get("rows_min", 10**9), len(rows))
        stats["rows_max"] = max(stats.get("rows_max", 0), len(rows))
    seq = [["datasetOpen", [text, fmt, ""]],
           ["datasetSerialize", ["h1", "turtle"]],
           ["datasetSerializeWith", ["h1", "turtle", options(rows)]],
           ["datasetSerializeWith", ["h1", "turtle", options(rows, False)]],
           ["datasetSerializeWith", ["h1", "turtle", "{}"]]]
    sf = os.path.join(work, "case.seq.json")
    json.dump(seq, open(sf, "w"))
    a = run(old, sf); b = run(new, sf)
    results = [("callseq", a, b)]
    outl = a[1].decode("utf-8", "replace").split("\n")
    if outl and '"ok":true' in outl[0]: stats["open_ok"] += 1
    else:
        stats["open_err"] += 1
        if stats["open_err"] <= 5: print("open error:", outl[0][:200], "| text starts:", repr(text[:200]))
    if "<<(" in a[1].decode("utf-8", "replace"): stats["has_tt"] += 1
    if len(rows) > 16:
        stats["big_table"] += 1
        if len(outl) > 2 and outl[2].count("@prefix") >= 1: stats["big_table_used"] += 1
    if "<<(" not in text and kind == "nt":
        af = os.path.join(work, "case.args.json")
        json.dump([text, options(rows)], open(af, "w"))
        results.append(("serializeTurtleWith", run1(old, "serializeTurtleWith", af), run1(new, "serializeTurtleWith", af)))
        json.dump([text], open(af, "w"))
        results.append(("serializeTurtle", run1(old, "serializeTurtle", af), run1(new, "serializeTurtle", af)))
    for name, x, y in results:
        if x == y:
            same += 1; bytes_cmp += len(x[1])
        else:
            diff += 1
            diffs.append((i, name, x[0], y[0], hashlib.sha256(x[1]).hexdigest()[:12], hashlib.sha256(y[1]).hexdigest()[:12]))
            keep = os.path.join(work, "diff-%d-%s.seq.json" % (i, name))
            json.dump(seq, open(keep, "w"))
print(stats)
print("cases=%d comparisons=%d identical=%d different=%d stdout_bytes_compared=%d" % (n, same + diff, same, diff, bytes_cmp))
for d in diffs[:20]: print(d)
sys.exit(1 if diff else 0)
