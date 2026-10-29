# RDF Data Cube in Lean: normalization and integrity constraints

Date: 2026-10-28. Tracking: https://github.com/danbri/factoidal/issues/1165
(RDF Data Cube item of the spec-coverage issue).

Specification: The RDF Data Cube Vocabulary, W3C Recommendation 16 January
2014, https://www.w3.org/TR/2014/REC-vocab-data-cube-20140116/. Lean namespace
`L4Factoidal.DataCube.QB2014`.

## What runs

- `DataCube/Queries.lean`: the SPARQL texts of sections 10.1 and 11.1,
  generated from the vendored files in `tests/datacube/spec/` by
  `tools/datacube-gen-queries.py` (the test fails on drift).
- `DataCube/Normalize.lean`: section 10.1 two ways. `normalizeSparql` runs the
  two update requests through the SPARQL 1.1 Update evaluator
  (`SPARQL/Update.lean`). `normalize` is one graph function per INSERT
  operation, applied in request order.
- `DataCube/Constraints.lean`: section 11.1 two ways. `checkSparql` runs the
  ASK queries through the SPARQL engine (IC-20 and IC-21: the instantiation
  SELECT, then one template instance per IRI). `checkDirect` is one graph
  function per constraint. IC-0 has no query; it reuses the D-entailment
  inconsistency test of `RDF/Entailment.lean`.
- `lake exe l4datacube MANIFEST`: normalizes each case both ways (the results
  must have the same triples), checks both ways (the verdicts must agree), and
  compares the violated constraints with the manifest.

## Theorems (`DataCube/NormalizeTheorems.lean`)

- `normalize_extensive`: normalization keeps every input triple.
- `phase1_rdfs_sound`: every triple of phase 1's result has a derivation by the
  RDF 1.1 Semantics section 9.2 rules (`RDFS.Derives`) from the input and ten
  declarations of the Data Cube vocabulary (`qbPhase1Schema`). This is the
  Recommendation's statement "These closure operations are implied by the RDFS
  semantics of the Data Cube vocabulary". `l4datacube --check-schema` checks
  the ten triples against the vendored vocabulary `cube.ttl`.

Not proved: that `checkSparql` and `checkDirect` (and the two normalizations)
agree on every graph. They agree on every fixture; the direct functions compare
terms by RDF term equality, and five queries use SPARQL `=` / `!=`, which
compare literals by value.

## Decisions

1. IC-17 as written is false on every graph: its HAVING clause names `?count`,
   the alias of a SELECT expression, and SPARQL 1.1 Query section 18.2.4.1
   applies HAVING before section 18.2.4.4 binds SELECT expressions. The W3C
   aggregate tests repeat the aggregate in HAVING (`agg03.rq`). The checker
   uses `tests/datacube/local/ic-17-sparql11.rq` (the aggregate repeated); the
   harness reports STALE if the query as written is ever true.
2. The IC-20 and IC-21 templates do not tie `?list` to the code list whose
   parent-child property is `$p`; both formulations keep that.
3. Example 13 of the Recommendation is not valid Turtle (the subject repeated
   after `;`); the fixture that uses it writes those lines as statements.
4. No W3C test suite exists. The cases are project-local: one passing cube,
   one failing cube per constraint, and Appendix C (which violates IC-4 alone,
   because it uses `sdmx-dimension:sex` without declaring it).
