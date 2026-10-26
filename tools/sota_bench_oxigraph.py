#!/usr/bin/env python3
"""tools/sota_bench_oxigraph.py: the Oxigraph (pyoxigraph) side of
tools/sota-bench.py (https://github.com/danbri/factoidal/issues/811).

Each verb does one workload of the state-of-the-art table and writes its
answer to standard output, so that tools/sota-bench.py counts and compares
the answers of every engine in the same way. Python start-up and the import
of pyoxigraph are part of the measured time; the row `start` of the table
measures them alone.

  parse FILE FORMAT [BASE]   parse, write N-Quads (one line per quad read)
  query FILE FORMAT QUERY.rq load into an in-memory Store, run the query,
                             write the solutions as SPARQL TSV
  convert FILE FORMAT OUT    parse, write in the syntax OUT (writer rows)
  canonicalize FILE          RDFC-1.0 of an N-Quads file; the canonical
                             N-Quads, sorted in code point order
  start                      import pyoxigraph and exit

FORMAT: ntriples | nquads | turtle | trig | rdfxml | jsonld.
pyoxigraph is not vendored; tools/sota-bench.py installs it into a venv
under its download directory.
"""

import sys

import pyoxigraph as ox

FORMATS = {
    "ntriples": ox.RdfFormat.N_TRIPLES,
    "nquads": ox.RdfFormat.N_QUADS,
    "turtle": ox.RdfFormat.TURTLE,
    "trig": ox.RdfFormat.TRIG,
    "rdfxml": ox.RdfFormat.RDF_XML,
    "jsonld": ox.RdfFormat.JSON_LD,
}


def main(argv):
    verb = argv[1]
    if verb == "start":
        return 0
    if verb == "parse":
        path, fmt = argv[2], FORMATS[argv[3]]
        base = argv[4] if len(argv) > 4 else None
        ox.serialize(ox.parse(path=path, format=fmt, base_iri=base),
                     sys.stdout.buffer, ox.RdfFormat.N_QUADS)
        return 0
    if verb == "convert":
        # read FILE in FORMAT, write it in OUT (a writer row)
        path, fmt, out = argv[2], FORMATS[argv[3]], FORMATS[argv[4]]
        ox.serialize(ox.parse(path=path, format=fmt), sys.stdout.buffer, out)
        return 0
    if verb == "query":
        path, fmt = argv[2], FORMATS[argv[3]]
        with open(argv[4], encoding="utf-8") as f:
            text = f.read()
        store = ox.Store()
        store.load(path=path, format=fmt)
        res = store.query(text)
        res.serialize(sys.stdout.buffer, ox.QueryResultsFormat.TSV)
        return 0
    if verb == "canonicalize":
        ds = ox.Dataset(ox.parse(path=argv[2], format=ox.RdfFormat.N_QUADS))
        ds.canonicalize(ox.CanonicalizationAlgorithm.RDFC_1_0)
        lines = sorted(str(q) + " .\n" for q in ds)
        sys.stdout.write("".join(lines))
        return 0
    print(f"unknown verb {verb}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
