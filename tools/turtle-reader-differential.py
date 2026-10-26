#!/usr/bin/env python3
"""Differential test of the Turtle and TriG readers: an OLD and a NEW l4factoidal on random documents.

usage: tools/turtle-reader-differential.py OLD_L4FACTOIDAL NEW_L4FACTOIDAL CASES SEED [WORKDIR]

OLD_L4FACTOIDAL is a copy of `formal/lean4/.lake/build/bin/l4factoidal` made before a change to
the Turtle reader (`L4Factoidal/Syntax/Turtle.lean`, `TriG.lean`, the chunk walks and the lenient
reader); NEW_L4FACTOIDAL is the build after it. For every document the two must give the same exit
code, the same standard output and the same standard error, byte for byte, in each of the ways the
command reads a document:

  parse F --format turtle12|trig12            the count (the chunk walk, streamed)
  parse F --format turtle12|trig12 --out nquads
                                              the canonical N-Quads (streamed)
  parse F --format turtle12|trig12 --out turtle
                                              the whole-text reader (a text with `<<` is read by
                                              `parseTurtle` and not by the chunk walk) and the writer
  parse F --format turtle12|trig12 --lenient  the lenient reader (recovers after an error)

Exit status 0 when every comparison agrees, 1 when one differs (the document is kept in WORKDIR,
default ./diff).

A document is Turtle or TriG. It has directives (`@prefix` and `PREFIX`, some labels bound again,
`@base` and `BASE`, `@version`), statements with prefixed names, IRIs, blank nodes, `[]`, property
lists, collections, literals of every form, object lists, predicate lists, reified triples and
annotations, and triple terms nested up to 10 deep with every kind of term at the bottom and
inside. In some documents the prefix table has 100 to 600 labels. In 40 percent of the cases the
document is then damaged (a character deleted, doubled, replaced by one of `<>()";,.[]{}#~`, or the
text cut short), so that the reader stops with an error whose message and offset are compared.
The generator is deterministic for a SEED.

Written for https://github.com/danbri/factoidal/issues/865 (2026-10-15): the open triple terms of a
nesting are a list and the latest binding of a prefix label is read from a tree. Seeds 11, 12 and 13,
4,000 documents each: 48,000 comparisons, 0 differences, between 3e832dfe and the change (20,209 with
exit 0, 27,791 the same error)."""
import os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

if len(sys.argv) < 5:
    sys.exit(__doc__)
old, new, ncases, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
work = sys.argv[5] if len(sys.argv) > 5 else "diff"
os.makedirs(work, exist_ok=True)

NS = ["http://e/", "http://e/a/", "http://e#", "http://f/", "urn:x:", "http://é.example/",
      "http://www.w3.org/1999/02/22-rdf-syntax-ns#", "http://www.w3.org/2001/XMLSchema#", "rel/", "../up/", ""]
LABELS = ["a", "b", "c", "", "p1", "p2", "ex", "x-y", "é", "t.u", "rdf", "xsd"]
LOC = ["s", "p", "o", "x1", "y-z", "a.b", "é", "%41", "\\~x", "_u", "1", "q:r", ""]
STR = ["t", "a b", "q\\\"uote", "line\\nx", "\\u00e9", "x.y", "", "it's"]
XSD = "http://www.w3.org/2001/XMLSchema#"
DAMAGE = list('<>()";,.[]{}#~:@_ \n')


class Gen:
    def __init__(self, rnd):
        self.r = rnd
        self.many = rnd.random() < 0.15
        self.labels = list(LABELS)
        if self.many:
            self.labels += ["m%d" % i for i in range(rnd.randrange(100, 600))]
        self.declared = {}

    def pick_label(self):
        return self.r.choice(self.labels) if not self.many or self.r.random() < 0.3 else self.r.choice(self.labels[len(LABELS):])

    def iri(self):
        r = self.r
        base = r.choice(NS)
        return "<" + base + r.choice(["s", "p", "o", "x1", "y-z", "é", "a/b", "#f", ""]) + ">"

    def pname(self):
        r = self.r
        pool = list(self.declared) or LABELS
        lab = r.choice(pool) if r.random() < 0.985 else r.choice(self.labels)
        return lab + ":" + r.choice(LOC)

    def node(self):
        r = self.r
        k = r.randrange(10)
        if k <= 3 and self.declared:
            return self.pname()
        if k <= 5:
            return self.iri()
        if k == 6:
            return "_:b%d" % r.randrange(6)
        if k == 7:
            return "[]"
        return self.pname() if self.declared else self.iri()

    def lit(self):
        r = self.r
        k = r.randrange(10)
        v = r.choice(STR)
        if k == 0:
            return '"%s"' % v
        if k == 1:
            return "'%s'" % v
        if k == 2:
            return '"%s"@%s' % (v, r.choice(["en", "en-GB", "fr--ltr", "ar--rtl"]))
        if k == 3:
            return '"%s"^^%s' % (v, self.iri())
        if k == 4:
            return '"%s"^^<%sinteger>' % (r.choice(["5", "-7", "007", "x"]), XSD)
        if k == 5:
            return r.choice(["5", "-7", "+1", "1.5", ".5", "1e3", "-2.5E-3", "true", "false"])
        if k == 6:
            return '"""%s\nmore"""' % v
        if k == 7:
            return "'''%s'''" % v
        return '"%s"' % v

    def tt_object(self, depth):
        r = self.r
        k = r.randrange(8)
        if k <= 1 and depth < 10:
            return self.triple_term(depth + 1)
        if k == 2:
            return self.lit()
        if k == 3:
            return "_:b%d" % r.randrange(6)
        return self.node() if r.random() < 0.7 else self.iri()

    def triple_term(self, depth=0):
        r = self.r
        subj = self.iri() if r.random() < 0.5 or not self.declared else self.pname()
        if r.random() < 0.1:
            subj = "_:t%d" % r.randrange(3)
        verb = r.choice(["a", self.iri(), self.pname() if self.declared else self.iri()])
        return "<<( %s %s %s )>>" % (subj, verb, self.tt_object(depth))

    def object(self, depth=0):
        r = self.r
        k = r.randrange(14)
        if k <= 2:
            return self.node()
        if k <= 4:
            return self.lit()
        if k <= 7:
            return self.triple_term()
        if k == 8 and depth < 2:
            return "[ %s ]" % self.pred_obj_list(depth + 1)
        if k == 9 and depth < 2:
            return "( %s )" % " ".join(self.object(depth + 1) for _ in range(r.randrange(0, 4)))
        if k == 10:
            return "<< %s %s %s >>" % (self.iri(), self.iri(), self.node())
        return self.node()

    def pred_obj_list(self, depth=0):
        r = self.r
        groups = []
        for _ in range(r.randrange(1, 3)):
            verb = r.choice(["a", self.iri(), self.pname() if self.declared else self.iri()])
            objs = []
            for _ in range(r.randrange(1, 4)):
                o = self.object(depth)
                if r.random() < 0.1:
                    o += " ~ " + self.iri()
                if r.random() < 0.05:
                    o += " {| %s %s |}" % (self.iri(), self.node())
                objs.append(o)
            groups.append(verb + " " + " , ".join(objs))
        return " ; ".join(groups)

    def directive(self):
        r = self.r
        k = r.randrange(8)
        if k <= 4:
            lab = self.pick_label()
            ns = r.choice(NS)
            self.declared[lab] = ns
            return ("@prefix %s: <%s> ." if k < 3 else "PREFIX %s: <%s>") % (lab, ns)
        if k == 5:
            return r.choice(["@base <http://b/%s/> .", "BASE <http://b/%s/>"]) % r.choice(["x", "y", "z/w"])
        if k == 6:
            return r.choice(['@version "1.2" .', 'VERSION "1.2"'])
        lab = self.pick_label()
        self.declared[lab] = r.choice(NS)
        return "@prefix %s: <%s> ." % (lab, self.declared[lab])

    def statement(self):
        r = self.r
        subj = self.node()
        if subj == "[]" and r.random() < 0.3:
            subj = "[ %s ]" % self.pred_obj_list(1)
        elif r.random() < 0.05:
            subj = "<< %s %s %s >>" % (self.iri(), self.iri(), self.node())
        return "%s %s ." % (subj, self.pred_obj_list())

    def document(self, trig):
        r = self.r
        lines = []
        if r.random() < 0.95:
            lines.append("@base <http://base.example/dir/> .")
        if self.many:
            for lab in self.labels[len(LABELS):]:
                ns = r.choice(NS[:6]) + lab + "/"
                self.declared[lab] = ns
                lines.append("@prefix %s: <%s> ." % (lab, ns))
        for _ in range(r.randrange(1, 6)):
            lines.append(self.directive())
        for _ in range(r.randrange(1, 12)):
            k = r.random()
            if k < 0.15:
                lines.append(self.directive())
            elif trig and k < 0.5:
                name = self.node() if r.random() < 0.7 else self.iri()
                if name == "[]":
                    name = "_:g"
                body = " ".join(self.statement() for _ in range(r.randrange(0, 4)))
                lines.append(("GRAPH %s { %s }" if r.random() < 0.3 else "%s { %s }") % (name, body))
            else:
                lines.append(self.statement())
        return "\n".join(lines) + "\n"

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


def one(i):
    rnd = random.Random(seed * 1000003 + i)
    g = Gen(rnd)
    trig = rnd.random() < 0.35
    text = g.document(trig)
    if rnd.random() < 0.4:
        text = g.damage(text)
    fmt = "trig12" if trig else "turtle12"
    path = os.path.join(work, "c%d.%s" % (i, "trig" if trig else "ttl"))
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    diffs = []
    ok = err = 0
    for mode in ("count", "nquads", "turtle", "lenient"):
        a = run(old, path, fmt, mode)
        b = run(new, path, fmt, mode)
        if a == b:
            if a[0] == 0:
                ok += 1
            else:
                err += 1
        else:
            diffs.append((mode, a[0], b[0]))
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
print("documents=%d comparisons=%d identical=%d (exit 0: %d, same error: %d) different=%d" % (
    ncases, 4 * ncases, same_ok + same_err, same_ok, same_err, sum(len(r[2]) for r in bad)))
for r in bad[:20]:
    print("DIFF", r[1], r[2])
sys.exit(1 if bad else 0)
