#!/usr/bin/env python3
"""Generate a TriG corpus of at least N bytes (default 100 MB) for the shard
packer (https://github.com/danbri/factoidal/issues/769).

Usage: gen_trig.py OUT.trig [BYTES] [--interleaved]

Deterministic (fixed seed). Mixes the forms the chunk walk must split:
prefix and SPARQL-style directives, `GRAPH <g> {`, `<g> {`, `ex:g {`,
blank-node graph labels, a default-graph block, collections, blank-node
property lists, language tags, typed and long-string literals containing
braces and dots, escaped local names, comments, and final statements of a
block with no dot. By default each named graph is ONE contiguous block and the
default graph comes first, so the quad order equals the whole-source route's
order and the two routes must pack byte-identical generations. With
--interleaved graphs recur in random order, which the whole-source route
regroups (https://github.com/danbri/factoidal/issues/836)."""
import random, sys

args = [a for a in sys.argv[1:] if not a.startswith('--')]
interleaved = '--interleaved' in sys.argv
out, size = args[0], int(args[1]) if len(args) > 1 else 100_000_000
GRAPHS = 60
rnd = random.Random(769)
P = "http://example.org/"
with open(out, "w", encoding="utf-8") as f:
    f.write(f"@prefix ex: <{P}> .\nPREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n@base <{P}base/> .\n")
    n = 0
    written = 0
    # default graph first
    f.write("{ ex:d0 ex:p ex:o0 . ex:d1 ex:p \"x\" }\n")
    def stmt(n):
        s = f"ex:s{n}"
        k = rnd.randrange(8)
        if k == 0: return f"  {s} ex:name \"name {n}\"@en , \"nom {n}\"@fr ."
        if k == 1: return f"  {s} ex:val {n} ; ex:dec {n}.5 ; ex:typed \"{n}\"^^xsd:integer ."
        if k == 2: return f"  {s} ex:list ( ex:a{n} \"b{n}\" {n} ) ."
        if k == 3: return f"  {s} ex:p [ ex:q ex:o{n} ; ex:r \"r\" ] ."
        if k == 4: return f"  {s} ex:text \"\"\"line {{ one }}.\nline two. # not a comment\n\"\"\" ."
        if k == 5: return f"  {s} ex:esc ex:a\\~b\\.{n} . # trailing comment {{ }}"
        if k == 6: return f"  <{P}s{n}> <{P}p> <{P}o{rnd.randrange(1000)}> ."
        return f"  _:n{n} ex:link {s} ."
    def block(g, limit):
        global n
        form = rnd.randrange(5)
        head = [f"GRAPH <{P}g{g}> {{", f"<{P}g{g}> {{", f"ex:g{g} {{", f"_:b{g} {{", f"GRAPH ex:g{g} {{"][form]
        lines, size_b = [head], 0
        while size_b < limit:
            n += 1
            lines.append(stmt(n)); size_b += len(lines[-1]) + 1
        if rnd.randrange(2) == 0 and lines[-1].endswith(" ."):
            lines[-1] = lines[-1][:-2]  # last statement of the block without a dot
        lines.append("}\n")
        f.write("\n".join(lines))
        return size_b
    if interleaved:
        while written < size:
            written += block(rnd.randrange(GRAPHS), rnd.randrange(70, 4000))
    else:
        for g in range(GRAPHS):
            block(g, size // GRAPHS)
