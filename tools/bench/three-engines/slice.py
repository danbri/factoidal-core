#!/usr/bin/env python3
"""Write the DBpedia benchmark slice as N-Triples.

Usage: slice.py OBJECTS.ttl.bz2 LITERALS.ttl.bz2 OUT.nt OUT-STATS.json

Input: DBpedia 2016-10 core-i18n/en mappingbased_objects_en.ttl.bz2 and
mappingbased_literals_en.ttl.bz2 (one N-Triples statement per line).

Slice rule (fixed; record: docs/designissues/2026-10-12-three-engine-benchmark.md):
  - every statement of mappingbased_objects_en;
  - the statements of mappingbased_literals_en whose predicate is one of
    LITERAL_PREDICATES below;
  - a statement is dropped when one of its IRIs is not an N-Triples IRIREF
    (RDF 1.1 N-Triples production [8]: no U+0000..U+0020, < > " { } | ^ `
    or backslash other than \\u and \\U escapes) or is not absolute (no
    scheme).
The output keeps input order. Counts go to OUT-STATS.json.
"""
import bz2
import json
import re
import sys

LITERAL_PREDICATES = {
    "<http://xmlns.com/foaf/0.1/name>",
    "<http://dbpedia.org/ontology/birthDate>",
    "<http://dbpedia.org/ontology/deathDate>",
    "<http://dbpedia.org/ontology/populationTotal>",
}
IRI = re.compile(r'<((?:[^\x00-\x20<>"{}|^`\\]|\\u[0-9A-Fa-f]{4}|\\U[0-9A-Fa-f]{8})*)>')
SCHEME = re.compile(r'[A-Za-z][A-Za-z0-9+.-]*:')


def iri_ok(tok):
    m = IRI.fullmatch(tok)
    return bool(m) and bool(SCHEME.match(m.group(1)))


def main():
    objects, literals, out, stats_path = sys.argv[1:5]
    stats = {"objects_in": 0, "literals_in": 0, "literals_selected": 0,
             "dropped_bad_iri": 0, "written": 0}
    with open(out, "w", encoding="utf-8", newline="\n") as w:
        for path, kind in ((objects, "objects"), (literals, "literals")):
            with bz2.open(path, "rt", encoding="utf-8", newline="\n") as f:
                for line in f:
                    if line.startswith("#") or not line.strip():
                        continue
                    stats[kind + "_in"] += 1
                    s, rest = line.split(" ", 1)
                    p, o = rest.split(" ", 1)
                    if kind == "literals":
                        if p not in LITERAL_PREDICATES:
                            continue
                        stats["literals_selected"] += 1
                    ok = iri_ok(s) and iri_ok(p)
                    if ok and o.startswith("<"):
                        ok = ">" in o and iri_ok(o[: o.index(">") + 1])
                    if not ok:
                        stats["dropped_bad_iri"] += 1
                        continue
                    w.write(line if line.endswith("\n") else line + "\n")
                    stats["written"] += 1
    with open(stats_path, "w") as f:
        json.dump(stats, f, indent=1)
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
