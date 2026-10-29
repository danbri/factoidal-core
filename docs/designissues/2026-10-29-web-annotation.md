# Web Annotation in Lean (Data Model, Vocabulary, Protocol)

Date: 2026-10-29. Tracking: https://github.com/danbri/factoidal/issues/1165
(spec track A, item 4). Specifications: Web Annotation Data Model, Web
Annotation Vocabulary and Web Annotation Protocol, W3C Recommendations of
2017-02-23.

## Result (stage 1: Data Model and Vocabulary)

📊 `bash tests/webannotation/run.sh` (`lake exe l4webannotation`):

- annotation-model tests (web-platform-tests `ce5ca396`) on the 44
  Recommendation examples and the 41 protocol samples: 246 pass, 0 fail (out
  of 246 document × test runs); 6 excluded (defective test data,
  https://github.com/danbri/factoidal/issues/1193 (choiceSet.json accepts
  only `Choice`)). With the corrected `choiceSet.json`, the 6 runs pass.
- 19 project-local documents that break one MUST each: 19 pass, 0 fail (out
  of 19). Each must fail the named assertion file, not any assertion.
- annotation-vocab checks 01 to 04 on the 85 documents, and 05 and 06 on
  `oa.ttl`: 342 pass, 0 fail (out of 342).

## What the suite is

The W3C suite for the Data Model is a set of JSON Schemas (draft-04), one
per requirement, grouped by `.test` files into "musts" and "optionals". The
suite's pages ask a tester to paste an annotation that a client made; the
JavaScript harness (`scripts/JSONtest.js` with ajv 4.0.4) then runs the
schemas in order. There is no list of documents with expected verdicts. So
the runner gives it two sets of documents:

1. Conforming documents: the Recommendation's own examples and the
   protocol server's samples. Every applicable `.test` must pass.
2. Documents that break one MUST each (`tests/webannotation/negative/`).
   The `.test` must fail, and the failing subtest must be the named
   assertion file.

The vocabulary suite is six manual pages. Each page names one check; the
check is in `L4Factoidal/WebAnnotation/Vocab.lean`.

## Reuse

- JSON Schema: `L4Factoidal/JSONSchema/Validate.lean`, the draft-07 validator
  that the JSON Schema suite measures. It gains a `Dialect` parameter, with
  default values that keep every earlier verdict. `draft04Ajv4` ignores
  unknown keywords (draft-04 §5.4; the suite puts `assertionType` and the
  other test members in every schema, and writes `"$ref "` twice), reads
  boolean `exclusiveMinimum`, and checks `format` as ajv 4.0.4 "fast" mode
  does (`uri`, `date-time`). The two format checks are direct Lean functions:
  the ECMAScript regex profile does not take flag `i` or `(?:`.
- JSON-LD 1.1 (expansion, toRdf, fromRdf, compaction), the N-Triples, Turtle
  and RDF/XML readers and writers, and dataset isomorphism, all unchanged.

## Decisions

- The test procedure is `JSONtest.js` with one change: the validator is
  three-valued, and an `unsupported` verdict is an undetermined subtest,
  never a pass. Comparison objects (`compareWith`) and nested lists are
  undetermined; the vendored suite has neither, and `run.sh` checks this.
- A `.test` file runs on a document of its kind (`type` Annotation,
  AnnotationCollection or AnnotationPage), as the `.test` descriptions say.
- Vocabulary check 04 compares RDF datasets, not JSON texts. Compaction can
  change member order and array form without a change of meaning.
- Vocabulary check 06: every `rdfs:domain` and `rdfs:range` names a class
  that the ontology declares, or (for a range) an RDF 1.1 datatype.

## Findings

- https://github.com/danbri/factoidal/issues/1193: the schema for "Choice or
  Set" accepts only `Choice`, so the Recommendation's Examples 42 to 44
  (`Composite`, `List`, `Independents`) fail a MUST.
- `oa.jsonld` is not isomorphic to `oa.ttl`: the `rdfs:comment` of
  `oa:annotationService` has a different blank line. `oa.rdf` is isomorphic
  to `oa.ttl`. The runner prints this; it is not a test.

## Theorems (`L4Factoidal/WebAnnotation/Theorems.lean`)

- `wa2017_toRdf_eq_jsonld11_toRdf`, `wa2017_expand_eq_jsonld11_expand`,
  `wa2017_text_toRdf`: the RDF of a Web Annotation 2017 document is its
  JSON-LD 1.1 deserialisation; there is no second mapping.
- `wa2017_yamlld10_toRdf`: the same annotation as YAML-LD 1.0 gives the same
  dataset (through `yamlld10_toRdf_eq_jsonld11_toRdf`).
- `runSchema_hidden_only_if_skipped`: a subtest is hidden only for an
  unexpected result at a level listed in `skipFailures`; the `*Musts.test`
  files list none, so every MUST failure is reported.
- `testVerdict_pass_iff`: a document passes a `.test` file exactly when every
  reported subtest passes.

## Stage 2: the Annotation Protocol (not done yet)

The Protocol is LDP (Basic Containers) with the annotation media type and
paging by `AnnotationPage`. The suite's `annotation-protocol/` is one manual
page (`server/server-manual.html`) that runs requests against a server URL,
and a Python reference server (not vendored). The plan:

1. Read the request list of `server-manual.html` into a Lean test table
   (method, headers, expected status and headers), the same way the LWS
   host tests are written.
2. Serve an annotation container on the LWS storage (`L4Factoidal/LWS/`),
   which already has containers, ETags and paging. Read the Protocol's
   rules for container discovery, creation, update and deletion, the
   `Prefer` header, and container representations as `AnnotationPage`
   pages, and write each as a Lean rule with its section number.
3. Check every annotation the server returns with the stage 1 musts.
4. Add `annotation-protocol` to `tests/webannotation/run.sh`.

A new server surface carries the experimental code notice and states the
invariants of https://github.com/danbri/factoidal/issues/1120 it touches.
