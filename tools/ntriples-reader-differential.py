#!/usr/bin/env python3
"""Differential test of the N-Triples and N-Quads readers and writers: an OLD and a NEW l4factoidal on random documents.

usage: tools/ntriples-reader-differential.py OLD_L4FACTOIDAL NEW_L4FACTOIDAL CASES SEED [WORKDIR]

OLD_L4FACTOIDAL is a copy of `formal/lean4/.lake/build/bin/l4factoidal` made before a change to
the object reader of RDF 1.2 N-Triples and N-Quads (`readObject12` in `L4Factoidal/Syntax/NTriples.lean`),
to the hash or the join key of a term (`L4Factoidal/RDF/Core.lean`) or to the text of a term
(`Term.toNTriples`); NEW_L4FACTOIDAL is the build after it. For every document the two must give
the same exit code, the same standard output and the same standard error, byte for byte, in each of
the ways the command reads and writes a document:

  parse F --format nt12|nq12                  the count (the streamed reader)
  parse F --format nt12|nq12 --out nquads     the canonical N-Quads (streamed)
  parse F --format nt12|nq12 --out ntriples   the N-Triples text, written by `Term.toNTriples`
  parse F --format nt12|nq12 --out turtle     the Turtle writer
  parse F --format nt12|nq12 --out trig       the TriG writer
  parse F --format nt12|nq12 --lenient        the lenient reader (recovers after an error)
  parse F --format ntriples|nquads            the RDF 1.1 reader, the count

Exit status 0 when every comparison agrees, 1 when one differs (the document is kept in WORKDIR,
default ./diff).

A document is N-Triples or N-Quads of RDF 1.2. Its lines have a subject and a predicate that are IRIs
or blank nodes, with the white space of the grammar (spaces and tabs, a different amount at each place),
an object that is an IRI, a blank node, a literal of every form (language tags in capitals, a base
direction, a datatype, escapes, `\\uXXXX` and `\\UXXXXXXXX`) or a triple term nested up to 10 deep with
every kind of term at the bottom and inside, a graph name for N-Quads, comments and blank lines. In 40
percent of the cases the document is then damaged (a character deleted, doubled, replaced by one of
`<>()"._:@^#-` and a space, or the text cut short), so that the reader stops with an error whose
message and offset are compared. The generator is deterministic for a SEED.

Written for https://github.com/danbri/factoidal/issues/867 (2026-10-15): the open triple terms of a
nesting are a list in `readObject12`, the hash and the join key of a term and the text of a term are
loops."""
import os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

if len(sys.argv) < 5:
    sys.exit(__doc__)
old, new, ncases, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
work = sys.argv[5] if len(sys.argv) > 5 else "diff"
os.makedirs(work, exist_ok=True)

NS = ["http://e/", "http://e/a/", "http://e#", "http://f/", "urn:x:", "http://\\u00e9.example/",
      "http://www.w3.org/1999/02/22-rdf-syntax-ns#", "http://www.w3.org/2001/XMLSchema#"]
LOC = ["s", "p", "o", "x1", "y-z", "a.b", "\\u00e9", "%41", "_u", "1", "q:r", "", "T"]
STR = ["t", "a b", "q\\\"uote", "line\\nx", "tab\\tx", "\\u00e9", "\\U0001F600", "x.y", "", "it's", "b\\\\s", "<a/>"]
XSD = "http://www.w3.org/2001/XMLSchema#"
DAMAGE = list('<>()"._:@^#- \t\n')
WS = [" ", " ", " ", "  ", "\t", " \t"]


class Gen:
    def __init__(self, rnd):
        self.r = rnd

    def ws(self):
        return self.r.choice(WS)

    def iri(self):
        r = self.r
        return "<" + r.choice(NS) + r.choice(LOC) + ">"

    def bnode(self):
        return "_:b%d" % self.r.randrange(6)

    def subject(self):
        return self.iri() if self.r.random() < 0.7 else self.bnode()

    def lit(self):
        r = self.r
        k = r.randrange(9)
        v = r.choice(STR)
        if k == 0:
            return '"%s"' % v
        if k == 1:
            return '"%s"@%s' % (v, r.choice(["en", "EN", "en-GB", "fr--ltr", "ar--rtl", "AR--RTL", "de-DE--ltr"]))
        if k == 2:
            return '"%s"^^%s' % (v, self.iri())
        if k == 3:
            return '"%s"^^<%sinteger>' % (r.choice(["5", "-7", "007", "x"]), XSD)
        if k == 4:
            return '"%s"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>' % r.choice(
                ["<a  b='1'/>", "<a/>", "<b>x</b>", "<a b=\\\"2\\\" c='1'></a>"])
        if k == 5:
            return '"%s"^^<%sstring>' % (v, XSD)
        return '"%s"' % v

    def leaf(self):
        k = self.r.randrange(6)
        if k <= 1:
            return self.iri()
        if k == 2:
            return self.bnode()
        return self.lit()

    def term_object(self, depth):
        r = self.r
        if depth < 10 and r.random() < 0.45:
            return self.triple_term(depth + 1)
        return self.leaf()

    def triple_term(self, depth=0):
        r = self.r
        s, p, o = self.subject(), self.iri(), self.term_object(depth)
        if r.random() < 0.15:
            w = self.ws
            return "<<(%s%s%s%s%s%s%s)>>" % (w(), s, w(), p, w(), o, w())
        return "<<( %s %s %s )>>" % (s, p, o)

    def object(self):
        r = self.r
        k = r.randrange(10)
        if k <= 3:
            return self.triple_term()
        return self.leaf()

    def line(self, quads):
        r = self.r
        parts = [self.subject(), self.iri(), self.object()]
        if quads and r.random() < 0.6:
            parts.append(self.iri() if r.random() < 0.8 else self.bnode())
        text = parts[0]
        for p in parts[1:]:
            text += self.ws() + p
        text += r.choice(["", " ", "\t"]) + "."
        if r.random() < 0.1:
            text += " # comment"
        return text

    def document(self, quads):
        r = self.r
        lines = []
        for _ in range(r.randrange(1, 12)):
            k = r.random()
            if k < 0.08:
                lines.append("# a comment")
            elif k < 0.14:
                lines.append("")
            else:
                lines.append(self.line(quads))
        sep = r.choice(["\n", "\n", "\r\n"])
        return sep.join(lines) + r.choice(["\n", "", "\n\n"])

    def damage(self, text):
        r = self.r
        for _ in range(r.randrange(1, 3)):
            if not text:
                break
            i = r.randrange(len(text))
            k = r.randrange(5)
            if k == 0:
                text = text[:i] + text[i + 1:]
            elif k == 1:
                text = text[:i] + text[i] + text[i:]
            elif k == 2:
                text = text[:i] + r.choice(DAMAGE) + text[i + 1:]
            elif k == 3:
                text = text[:i]
            else:
                text = text[:i] + r.choice(DAMAGE) + text[i:]
        return text


def run(binary, path, fmt, mode):
    cmd = [binary, "parse", path, "--format", fmt]
    if mode == "lenient":
        cmd.append("--lenient")
    elif mode != "count":
        cmd += ["--out", mode]
    p = subprocess.run(cmd, capture_output=True, timeout=300)
    return (p.returncode, p.stdout, p.stderr)


MODES12 = ("count", "nquads", "ntriples", "turtle", "trig", "lenient")


def one(i):
    rnd = random.Random(seed * 1000003 + i)
    g = Gen(rnd)
    quads = rnd.random() < 0.5
    text = g.document(quads)
    if rnd.random() < 0.4:
        text = g.damage(text)
    path = os.path.join(work, "c%d.%s" % (i, "nq" if quads else "nt"))
    with open(path, "w", encoding="utf-8", newline="") as fh:
        fh.write(text)
    diffs = []
    ok = err = 0
    runs = [("nq12" if quads else "nt12", m) for m in MODES12] + [("nquads" if quads else "ntriples", "count")]
    for fmt, mode in runs:
        a = run(old, path, fmt, mode)
        b = run(new, path, fmt, mode)
        if a == b:
            if a[0] == 0:
                ok += 1
            else:
                err += 1
        else:
            diffs.append((fmt, mode, a[0], b[0]))
    if not diffs:
        os.remove(path)
    return (i, path, diffs, ok, err)


results = []
with ThreadPoolExecutor(max_workers=4) as ex:
    for r in ex.map(one, range(ncases)):
        results.append(r)
same_ok = sum(r[3] for r in results)
same_err = sum(r[4] for r in results)
bad = [r for r in results if r[2]]
total = (len(MODES12) + 1) * ncases
print("documents=%d comparisons=%d identical=%d (exit 0: %d, same error: %d) different=%d" % (
    ncases, total, same_ok + same_err, same_ok, same_err, sum(len(r[2]) for r in bad)))
for r in bad[:20]:
    print("DIFF", r[1], r[2])
sys.exit(1 if bad else 0)
