# Jena-style facade feasibility study: scripts

The scripts behind `docs/designissues/2026-10-25-jena-style-facade-feasibility.md`.
They read a clone of Apache Jena (the study used commit
`a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98`) and the npm package in
`npm/factoidal/`. Clone Jena first:

    git clone --depth 1 https://github.com/apache/jena <dir>

- `count.sh <jena root> <module>`, `tcount.py`: count test classes and methods.
- `api.py`: count public types and methods.
- `classify.py`: group test methods by package path (coarse, a judgement).
- `extract.py`: convert every one-line ARQ expression test
  (`jena-arq/src/test/java/org/apache/jena/sparql/expr`) to a SPARQL
  expression and a check kind, into
  `npm/factoidal/test/fixtures/jena-arq-expr/cases.json`
  (`python3 -I extract.py <jena root> <out.json>`). The suite that runs them
  is `npm/factoidal/test/jena-arq-expr.test.mjs` (stage 0; it replaces the
  study's `run-expr.mjs`). Verdicts: `fixtures/jena-arq-expr/verdicts.json`.
- `run-manifests.sh <jena root> [out dir]`: run Jena's `ARQ` and
  `SPARQL-CDTs` manifests with `l4w3c` (stage 0b).
- `ops.mjs`, `probe.mjs`: list the wasm ops and probe a few behaviours.
- `sample-port.test.mjs`: 11 Jena test methods ported by hand against the
  hypothetical facade `@factoidal/echochamber`. It does not run (the facade
  does not exist).

Licence: `sample-port.test.mjs` and the expression cases that `extract.py`
reads are derived from Apache Jena, Apache License 2.0. Apache Jena:
Copyright The Apache Software Foundation. This product includes software
developed at The Apache Software Foundation (https://www.apache.org/).
