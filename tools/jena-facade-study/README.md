# Jena-style facade feasibility study: scripts

The scripts behind `docs/designissues/2026-10-25-jena-style-facade-feasibility.md`.
They read a clone of Apache Jena (the study used commit
`a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98`) and the npm package in
`npm/factoidal/`. Clone Jena first:

    git clone --depth 1 https://github.com/apache/jena <dir>

- `count.sh <jena root> <module>`, `tcount.py`: count test classes and methods.
- `api.py`: count public types and methods.
- `classify.py`: group test methods by package path (coarse, a judgement).
- `extract.py`, `run-expr.mjs`: convert the one-line ARQ expression tests to
  SPARQL ASK queries and run them on `@factoidal/core`.
- `ops.mjs`, `probe.mjs`: list the wasm ops and probe a few behaviours.
- `sample-port.test.mjs`: 11 Jena test methods ported by hand against the
  hypothetical facade `@factoidal/echochamber`. It does not run (the facade
  does not exist).

Licence: `sample-port.test.mjs` and the expression cases that `extract.py`
reads are derived from Apache Jena, Apache License 2.0. Apache Jena:
Copyright The Apache Software Foundation. This product includes software
developed at The Apache Software Foundation (https://www.apache.org/).
