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

## Stage 2: the Annotation Protocol

📊 `bash tests/webannotation/run.sh`, section "protocol":

- `server-manual.html` MUST assertions: 35 pass, 0 fail (out of 35).
- `server-manual.html` SHOULD assertions: 10 pass, 0 fail (out of 10).
- Rules of §4.2, §5 and §6 that the page does not test (marked `extra`):
  11 pass, 0 fail (out of 11).
- 1 expected failure, with its open issue: a GET with
  `Accept: text/turtle` gets JSON-LD, not Turtle (§3.1, a SHOULD),
  https://github.com/danbri/factoidal/issues/1197. The run fails if it
  passes.
- The 64 annotations that the server sent (POST and PUT responses, GET
  responses, page items), each through its Data Model tests: 183 pass,
  0 fail (out of 183 runs); 9 excluded (defective test data,
  https://github.com/danbri/factoidal/issues/1193, the samples that use
  `Composite`, `List` and `Independents`).

### How it is built

- `L4Factoidal/WebAnnotation/Protocol.lean`: `step`, a total function
  from a state and a request to a state and a response. The state is an
  `LWS.Store` state and the list of deleted paths. A container is an LWS
  container entry; an annotation is an LWS data resource whose bytes are
  its JSON-LD text. So every backend that satisfies `LWS.StoreLaws` holds
  annotations, and the listing order and the pages are those of LWS
  (`orderedMemberPaths`, `pageAt`). Names of new annotations use
  `LWS.freeName` and `LWS.slugUsable` (the `Slug` header, §5.1). Each rule
  has its section number in the module header.
- `L4Factoidal/WebAnnotation/ProtocolSuite.lean`: the request list and the
  assertion texts of `server-manual.html`, sent to `step` over
  `LWS.MemStore`. The container is first filled with the suite's 41 sample
  annotations by POST (page size 10, so 5 pages).
- `Harness/WebAnnotationRun.lean` prints the scores and runs every
  annotation the server sent through the stage 1 Data Model tests.

### Decisions

- Default preference: PreferContainedDescriptions (§4.2.1: "If no
  preference is given by the client, the server SHOULD default to the
  PreferContainedDescriptions behavior"). The first page is embedded.
- Container IRIs of the two views: `?iris=0` and `?iris=1`, pages
  `?iris=N&page=K` from 0, as in the examples of §4.2. `Content-Location`
  is the IRI of the view and equals the `id`.
- A deleted IRI is not used again, and a GET answers 410 (§5.3, §6).
- A PUT whose `id` is not the annotation's IRI answers 400; a PUT that
  changes a `canonical` or `via` that was set answers 409 (§5.2, §6:
  "set or change a value that the server does not allow").
- A POST or PUT body that is not JSON-LD, or not an annotation in the Web
  Annotation context with a `target`, answers 415 (§6).

### Finding about the W3C page

The page tests on `first`, `last`, `partOf`, `next` and `prev` call
`request(...)` inside a `then` and do not return its promise, so in a
browser these four tests pass whatever the server answers. With the
default preference, `first` is an embedded page object, and the page would
request the URL `[object Object]`. The Lean suite makes each request,
follows `first.id` when `first` is embedded, and decides.

### Theorems (`Protocol.lean`)

- `wap2017_page_eq_lws10_page`: page `i` of a Web Annotation Protocol 2017
  container is page `i + 1` of the LWS 1.0 listing (`LWS.pageItems`).
- `wap2017_pages_concat`: the pages together give the container's
  annotations, each once, in listing order (from `LWS.pageItems_concat`).
- `assignId_id`, `assignId_canonical`: a created annotation has the
  assigned `id`, and its `canonical` is unchanged (§5.1 MUST).
- `newPath_fresh`, `newPath_prefix`: a POST never replaces an annotation,
  never uses the IRI of a deleted one, and the new IRI is the container IRI
  with a component added (§5.1 MUST).

### Not done

- Turtle (§3.1 SHOULD) and a host that serves `step` over HTTP:
  https://github.com/danbri/factoidal/issues/1197. A served surface needs
  the experimental code notice and the invariants of
  https://github.com/danbri/factoidal/issues/1120.
