#!/usr/bin/env python3
"""Compare an `l4sbm11 query` answer with an `l4factoidal query` answer.

SBM11 stage 4, https://github.com/danbri/factoidal/issues/790.

Usage: compare_answers.py GOT WANT WANT_EXIT_CODE

SPARQL JSON SELECT answers: multisets of solutions; a blank node compares
equal to any blank node (labels are not compared: the two engines may name
them differently), a language tag in lower case (the SBM11 packer folds
language tags to lower case, RDF 1.1 Concepts section 3.3). SPARQL JSON ASK
answers: the boolean (the reference CLI prints `true` or `false`). Other
answers (CONSTRUCT, DESCRIBE): N-Triples lines as multisets, each blank node
label replaced by `_:` and each language tag in lower case (issue 823: the
id path instantiates CONSTRUCT templates; until then only the number of
lines was compared).

Prints `equal ...`, `different ...` or `uncompared ...` on the first line.
"""
import json
import re
import sys
from collections import Counter

BNODE = re.compile(r'_:[^\s<>"]+')
LANGTAG = re.compile(r'(?<!\\)"@([A-Za-z0-9-]+)')


def norm_line(line):
    """An N-Triples line with blank node labels and language-tag case masked."""
    line = BNODE.sub("_:", line.strip())
    return LANGTAG.sub(lambda m: '"@' + m.group(1).lower(), line)


def term_key(b):
    t = b.get("type")
    if t == "bnode":
        return ("bnode",)
    if t == "uri":
        return ("uri", b["value"])
    if t == "triple":
        v = b["value"]
        return ("triple", term_key(v["subject"]), term_key(v["predicate"]), term_key(v["object"]))
    lang = b.get("xml:lang")
    if lang is not None:
        return ("lang", b["value"], lang.lower(), b.get("its:dir"))
    return ("lit", b["value"], b.get("datatype", "http://www.w3.org/2001/XMLSchema#string"))


def load_json(path):
    try:
        with open(path) as fh:
            return json.load(fh)
    except Exception:
        return None


def main():
    got_p, want_p, want_rc = sys.argv[1:4]
    if want_rc not in ("0", "1"):
        print("uncompared: the reference engine exited %s" % want_rc)
        return 0
    got = load_json(got_p)
    want_text = open(want_p).read()
    want = load_json(want_p)
    if isinstance(got, dict) and "boolean" in got:
        if isinstance(want, dict):
            w = str(want.get("boolean", "")).lower()
        elif isinstance(want, bool):
            w = "true" if want else "false"
        else:
            w = want_text.strip().split("\n")[0].strip()
        if w in ("true", "false"):
            if str(got["boolean"]).lower() == w:
                print("equal: boolean %s" % w)
            else:
                print("different: boolean %s, reference %s" % (got["boolean"], w))
        else:
            print("uncompared: reference answer is not a boolean")
        return 0
    if isinstance(got, dict) and "results" in got:
        if not isinstance(want, dict) or "results" not in want:
            print("uncompared: reference answer is not SPARQL JSON")
            return 0
        g = Counter(frozenset((k, term_key(v)) for k, v in r.items()) for r in got["results"]["bindings"])
        w = Counter(frozenset((k, term_key(v)) for k, v in r.items()) for r in want["results"]["bindings"])
        if g == w:
            print("equal: %d rows" % sum(g.values()))
        else:
            print("different: %d rows, reference %d rows; only here %s; only in reference %s" % (
                sum(g.values()), sum(w.values()), sorted(map(sorted, (g - w).keys()))[:1],
                sorted(map(sorted, (w - g).keys()))[:1]))
        return 0
    gl = [l for l in open(got_p).read().split("\n") if l.strip()]
    wl = [l for l in want_text.split("\n") if l.strip()]
    g = Counter(norm_line(l) for l in gl)
    w = Counter(norm_line(l) for l in wl)
    if g == w:
        print("equal: %d triples" % len(gl))
    else:
        print("different: %d triples, reference %d; only here %s; only in reference %s" % (
            len(gl), len(wl), sorted((g - w).keys())[:1], sorted((w - g).keys())[:1]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
