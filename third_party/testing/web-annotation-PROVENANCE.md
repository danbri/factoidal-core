# Web Annotation test suite: provenance

Vendored into `third_party/testing/web-annotation/` on 2026-10-29 for
https://github.com/danbri/factoidal/issues/1165 (spec track A, Web Annotation).

## From web-platform-tests

- Source: https://github.com/web-platform-tests/wpt, branch `master`, commit
  `ce5ca39646886a9349fc42913f843ec6e1c8a36f` (2026-10-28).
- Copied: `annotation-model/` without `scripts/` (the harness JavaScript and
  the bundled ajv 4.0.4, showdown), `tools/` (the page generator and its 20
  samples, which are Examples 1 to 20 of the Recommendation) and `examples/`
  (the README says they are not for conformance testing);
  `annotation-protocol/` without `tools/` (the Python reference server);
  `annotation-vocab/` (six manual pages).
- Licence: `LICENSE.md` (3-Clause BSD, web-platform-tests contributors), copied
  from the same commit. The W3C test suite licence also applies to tests
  contributed by W3C groups.
- The harness procedure that the Lean runner follows is
  `annotation-model/scripts/JSONtest.js` of the same commit (`runTests`,
  `determineResult`, `determineAction`), and the format checks are those of
  the bundled ajv 4.0.4 in its default "fast" mode. Neither file is copied;
  `L4Factoidal/WebAnnotation/JsonTest.lean` and
  `L4Factoidal/JSONSchema/Validate.lean` (`draft04Ajv4`) cite them.

## From www.w3.org

Retrieved 2026-10-29 with `curl -L`:

| File | URL | sha256 |
|---|---|---|
| `w3c-ns/anno.jsonld` | https://www.w3.org/ns/anno.jsonld | `c10fd886c5c726fbfd51747b8677eb8f7d02c039357269622de7382e5c20d410` |
| `w3c-ns/ldp.jsonld` | https://www.w3.org/ns/ldp.jsonld | `f29f5e88b353ceca2c9b00b1f957e47f69ccdf4a990133c95d8bc3540f59a620` |
| `w3c-ns/oa.ttl` | https://www.w3.org/ns/oa.ttl | `f661e37d33bf29176390101687711734a7e33a716bdecfb66b90c732373d7af5` |
| `w3c-ns/oa.rdf` | https://www.w3.org/ns/oa.rdf | `f63a5c543e7094dccb8bea29e649554eb70b9c3926bb4f1279dd87f3c994fb2e` |
| `w3c-ns/oa.jsonld` | https://www.w3.org/ns/oa.jsonld | `6e5f08af133f74201a62b28199d986a6beff298004c2144cb89e7ccc8dd5a58c` |

`recommendation-examples/exampleNN.json`: the 44 JSON examples of Web
Annotation Data Model, W3C Recommendation 2017-02-23
(https://www.w3.org/TR/annotation-model/), taken from the `pre` element
after each "Example NN" title of the Recommendation's HTML, HTML entities
decoded, markup removed. Each file is the example text unchanged; every one
parses as JSON.

Licence of the W3C documents: W3C Document License
(https://www.w3.org/copyright/document-license-2023/).

## Defective test data

`annotation-model/definitions/choiceSet.json` accepts only `"type": "Choice"`
for a Choice or Set, but Data Model §3.2.7 also defines `Composite`, `List`
and `Independents` (Examples 42 to 44):
https://github.com/danbri/factoidal/issues/1193. The corrected copy is
`tests/webannotation/local/choiceSet.json` (only the two `enum` lists differ).

## Runner

`formal/lean4/Harness/WebAnnotationRun.lean` (`lake exe l4webannotation`),
wrapper `tests/webannotation/run.sh`.
