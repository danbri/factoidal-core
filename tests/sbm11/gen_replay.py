#!/usr/bin/env python3
"""Write a base dataset and five SPARQL Update requests for the replay test of
tests/sbm11/update_where.sh (group `replay`,
https://github.com/danbri/factoidal/issues/858).

    gen_replay.py OUTDIR

OUTDIR gets base.nq (20,000 quads) and r1.ru .. r5.ru. The dictionary of the
packed base has more than 600 pages of 64 keys, and the requests give a log
whose terms meet every case of the walk in dictionary order
(`Dict.lookupNextM`, `L4Factoidal/Storage/Sbm11/DictFinger.lean`):

* terms in the dictionary that are close to each other (the same page, the next
  page) and far from each other;
* terms that the dictionary does not hold, in a gap between two pages, between two
  keys of a page, before the first key and after the last key;
* terms in the log that are the same as an earlier term (a term twice);
* terms with an inline code (integers, booleans), never in the dictionary;
* a language tag in upper case, which `normalizeTerm` folds to lower case;
* blank nodes, named graphs that exist, graphs that do not exist;
* a request whose second operation reads the store, so that the entries of the
  first are applied to the overlay by `Run.sync` before it runs.

The generator is deterministic (no random numbers). The expected state is the
state the reference engine (`l4factoidal update`) gives.
"""
import os
import sys

EX = "http://example.org/"
XSD = "http://www.w3.org/2001/XMLSchema#"
N = 20000


def iri(local: str) -> str:
    return f"<{EX}{local}>"


def obj(i: int) -> str:
    """The object of base quad i."""
    k = i % 6
    if k == 0:
        return iri(f"o{i % 3000}")
    if k == 1:
        return f'"v{i}"'
    if k == 2:
        return f'"x{i}"@en'
    if k == 3:
        return f'"{i}"^^<{XSD}integer>'
    if k == 4:
        return f'"{i}.5"^^<{XSD}decimal>'
    return f"_:b{i % 2000}"


def graph(i: int):
    """The graph name of base quad i, or None for the default graph."""
    return iri(f"g{i % 4}") if i % 5 == 0 else None


def quad(i: int) -> tuple:
    return (iri(f"s{i}"), iri(f"p{i % 7}"), obj(i), graph(i))


def nquad(q: tuple) -> str:
    s, p, o, g = q
    return f"{s} {p} {o} {g} ." if g else f"{s} {p} {o} ."


def block(quads) -> str:
    """Quads as the body of INSERT DATA or DELETE DATA: bare triples for the default
    graph, a GRAPH block for each quad of a named graph."""
    out = []
    for s, p, o, g in quads:
        out.append(f"GRAPH {g} {{ {s} {p} {o} }}" if g else f"{s} {p} {o} .")
    return "\n".join(out)


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    d = sys.argv[1]
    os.makedirs(d, exist_ok=True)
    with open(f"{d}/base.nq", "w") as f:
        for i in range(N):
            f.write(nquad(quad(i)) + "\n")

    # r1: remove 1,000 quads of the base: every 20th, so that the terms are far apart,
    # and a run of 100 in a row, so that they are in the same pages
    # (a blank node in DELETE DATA is a syntax error: the quads with a blank node are left out)
    removed = [quad(i) for i in list(range(0, N, 20)) + list(range(9000, 9100)) if i % 6 != 5]
    with open(f"{d}/r1.ru", "w") as f:
        f.write("DELETE DATA {\n" + block(removed) + "\n}\n")

    # r2: add quads with terms the dictionary holds and terms it does not hold
    added = []
    for i in range(1000):
        s = iri(f"s{i * 17 % N}x") if i % 3 == 0 else iri(f"s{i * 13 % N}")
        p = iri(f"q{i % 5}") if i % 4 == 0 else iri(f"p{i % 7}")
        k = i % 8
        if k == 0:
            o = f'"N{i}"@EN-gb'
        elif k == 1:
            o = f"_:nb{i % 40}"
        elif k == 2:
            o = iri(f"o{i % 3000}")
        elif k == 3:
            o = f'"{i}"^^<{XSD}integer>'
        elif k == 4:
            o = "true"
        elif k == 5:
            o = f'"w{i}"'
        elif k == 6:
            o = f'"{i}"^^<{XSD}double>'
        else:
            o = iri(f"zz{i}")
        added.append((s, p, o, iri("g9") if i % 11 == 0 else None))
    added.append(("<a:first>", "<a:first>", '"first"', None))
    added.append(("<zzz:last>", "<zzz:last>", '"last"', None))
    added.append(("<zzz:last>", iri("p1"), "<zzz:last>", iri("g1")))
    with open(f"{d}/r2.ru", "w") as f:
        f.write("INSERT DATA {\n" + block(added) + "\n}\n")

    # r3: remove quads that are not there (terms the dictionary holds in a new
    # combination, and terms it does not hold), and put 300 of r1's quads back
    absent = [(iri(f"s{i}"), iri(f"p{(i + 1) % 7}"), obj(i + 1), None) for i in range(5000, 5500) if (i + 1) % 6 != 5]
    absent += [(iri(f"nothere{i}"), iri("p1"), '"nothing"', None) for i in range(200)]
    absent += [(iri("s1"), iri("p1"), iri(f"nothere{i}"), iri(f"g{i % 4}")) for i in range(100)]
    back = [quad(i) for i in range(0, N, 20) if i % 6 != 5][:300]
    with open(f"{d}/r3.ru", "w") as f:
        f.write("DELETE DATA {\n" + block(absent) + "\n} ;\nINSERT DATA {\n" + block(back) + "\n}\n")

    # r4: graph management: one graph cleared, one dropped, one created, and graphs
    # that do not exist (SILENT)
    with open(f"{d}/r4.ru", "w") as f:
        f.write(f"CLEAR GRAPH {iri('g1')} ;\nDROP GRAPH {iri('g2')} ;\nCREATE GRAPH {iri('g7')} ;\n"
                f"CLEAR SILENT GRAPH {iri('gX')} ;\nDROP SILENT GRAPH {iri('gY')}\n")

    # r5: two operations. The first adds 300 quads (new subjects and literals, and subjects of the
    # base); the second reads the store, so the entries of the first are applied to the overlay
    # before it runs (`Run.sync`) and its WHERE clause finds them: the literals of one predicate
    # move to another.
    ins = [(iri(f"s{i * 7 % N}y") if i % 2 else iri(f"s{i * 11 % N}"), iri("p3"), f'"m{i}"', None)
           for i in range(300)]
    with open(f"{d}/r5.ru", "w") as f:
        f.write("INSERT DATA {\n" + block(ins) + "\n} ;\n"
                f"DELETE {{ ?s {iri('p3')} ?o }} INSERT {{ ?s {iri('q1')} ?o }} "
                f"WHERE {{ ?s {iri('p3')} ?o FILTER(isLiteral(?o)) }}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
