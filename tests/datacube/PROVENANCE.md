# Provenance of tests/datacube/

## spec/ (vendored, unmodified text)

Source: The RDF Data Cube Vocabulary, W3C Recommendation 16 January 2014,
https://www.w3.org/TR/2014/REC-vocab-data-cube-20140116/ , fetched 2026-10-28,
HTML sha256 `f5584310c20472992d8994870502f65358ca1a0b8fa4c1f15351860d4c0b8369`.

Each file is the text of one `<pre>` block of that document, with the HTML
tags removed and the HTML entities decoded:

- `prefixes.rq`: section 11.1, the prefix bindings every constraint query assumes.
- `ic-1.rq` to `ic-18.rq`, `ic-19a.rq`, `ic-19b.rq` (the two queries of IC-19):
  section 11.1.
- `ic-20-instantiation.rq`, `ic-20-template.rq`, `ic-21-instantiation.rq`,
  `ic-21-template.rq`: section 11.1, IC-20 and IC-21.
- `normalize-phase1.ru`, `normalize-phase2.ru`: section 10.1.
- `appendix-c-example.ttl`: Appendix C, the complete example Data Cube.

`cube.ttl`: the Data Cube vocabulary, http://purl.org/linked-data/cube
(Accept: text/turtle), fetched 2026-10-28, sha256
`f2d67d3811762fa7796008d225c9b1f891e8a9af8fdeeb3736188fe1bcdb7235`.

Licence: the W3C Document License; code extracts (the SPARQL and Turtle texts)
under the W3C Software and Document License
(https://www.w3.org/copyright/software-license-2023/).

## local/ (changed from the Recommendation)

- `ic-17-sparql11.rq`: `spec/ic-17.rq` with `HAVING (?count != ?numMeasures)`
  replaced by `HAVING (COUNT(?obs2) != ?numMeasures)`. Reason: SPARQL 1.1
  Query section 18.2.4.1 evaluates HAVING before the SELECT expressions bind
  `?count` (section 18.2.4.4), so the query as written is false on every graph.
  `l4datacube` fails with STALE if the query as written is ever true.

## cases/ (project-local)

The Recommendation has no test suite. The cases are project-local: one graph
that passes every constraint (`base-pass.ttl`, `measure-dimension-pass.ttl`
for a cube with a measure dimension), one graph per constraint that violates
that constraint only (`ic-N-fail.ttl`), passing and failing graphs for the
skos:Collection form of IC-19 and for the hierarchies of IC-20 and IC-21, and an
abbreviated cube (`normalize-dataset-attachment-pass.ttl`) that is well formed
only after normalization.

`appendix-c-with-sdmx-sex.ttl` is Appendix C plus the declaration of
`sdmx-dimension:sex` (the shape of example 14) and the SDMX sex code list of
example 13. Example 13 repeats the subject `sdmx-code:sex` after `;` on two
lines, which the Turtle grammar does not allow; those two lines are written as
separate statements. Appendix C alone (`spec/appendix-c-example.ttl`) violates
IC-4, because it uses `sdmx-dimension:sex` and does not declare it.
