# Changelog

## Unreleased

## 0.18.0 (2026-10-27)

- XSD constructor functions for datatypes outside the SPARQL 1.1 §17.5 table (`xsd:byte`, `xsd:int`, `xsd:unsignedInt`, `xsd:date`, `xsd:time`, `xsd:gYear` and the other `xsd:g*` types, the duration types, `xsd:token`, …) now cast as XPath F&O 3.1 §19 says. Before, they changed only the datatype and gave ill-typed literals such as `"HaHa"^^xsd:byte`. An invalid value or a cast that F&O does not allow is now an error (the variable is unbound) (https://github.com/danbri/factoidal/issues/1041, https://github.com/danbri/factoidal-core/pull/142).
- SPARQL: STRSTARTS, STRENDS, CONTAINS, STRBEFORE and STRAFTER compare the base direction of `rdf:dirLangString` arguments (SPARQL 1.2 §17.4.3: same language tag and same base direction). `CONTAINS("abc"@en--ltr, "a"@en)` is now an error. STRBEFORE and STRAFTER keep the base direction of the first argument: `STRBEFORE("abc"@en--ltr, "b")` is `"a"@en--ltr` (https://github.com/danbri/factoidal/issues/1042, https://github.com/danbri/factoidal-core/pull/136).
- Store open sends the manifest to the engine as bytes, not as hexadecimal inside the JSON arguments, and decodes it once for the plan and the open (new ops `storeManifestInspectBytes`, `storeQueryPlanBytes`, `storeOpenBytes`; the hexadecimal ops stay). On the londat store (1,046 blocks, 753 kB manifest) a scoped `openStoreHandle` takes 198 ms, not 305 ms with 0.17.0 (median of 9) (https://github.com/danbri/factoidal/issues/1039, https://github.com/danbri/factoidal-core/pull/141).
- Tests: the W3C manifest runner `l4w3c` reads `.n3` expected results when they are Turtle-compatible (else the test is unsupported, with the reason) and runs Jena's `mfx:TestQuery` as a query evaluation test; Jena ARQ manifests: 31 pass (was 13) of 308 (https://github.com/danbri/factoidal-core/pull/138). The Jena ARQ expression suite drops the 62 expected failures these fixes remove. `tools/split-read-differential.sh` runs on macOS and fails when it checks no file (https://github.com/danbri/factoidal-core/pull/133).

## 0.17.0 (2026-10-27)

- **Breaking:** `canonicalHash(graph)` now returns the SHA-256 (64 lowercase hex digits) of the RDFC-1.0 canonical N-Quads, as the RDF Dataset Canonicalization specification uses it. Before, it returned the canonical text. Use `canonicalize()` for the text. The engine computes the digest in Lean (new op `datasetCanonicalHash`) (https://github.com/danbri/factoidal/issues/1040, https://github.com/danbri/factoidal-core/pull/127).
- SPARQL string functions follow SPARQL 1.1 §17.4.3 argument types: STRLEN, SUBSTR, UCASE, LCASE, STRSTARTS, STRENDS, CONTAINS, ENCODE_FOR_URI, MD5 and SHA* give a type error on a number, boolean or IRI argument (MD5/SHA* also on a language-tagged literal). STRSTARTS/STRENDS/CONTAINS check argument compatibility. SUBSTR follows `fn:substring`: `SUBSTR("12345", 0, 3)` is now `"12"` (was `"123"`) (https://github.com/danbri/factoidal/issues/1036, https://github.com/danbri/factoidal-core/pull/126).
- `factoidal pack --layout sbm11` writes an SBM11 generation: the same files as `l4sbm11-pack`, byte for byte (605 of 605 W3C census inputs). This layout also reads RDF/XML and JSON-LD. `factoidal activate`, `inspect` and `query` read SBM11 stores. `activate` checks the length, SHA-256 and Merkle root of every file before it moves `CURRENT`. `serve` does not read SBM11 stores yet. IBK5 stays the default layout. New wasm ops `storeLayout` and `sbm11Verify` (https://github.com/danbri/factoidal/issues/1009, https://github.com/danbri/factoidal-core/pull/131).
- Store open in Node is faster: on the londat store (142,314 quads, 1,046 blocks) `openStoreHandle` takes 562 ms, not 1485 ms (median of 7 runs, Apple M1, Node 22). The engine decodes the hexadecimal manifest over bytes, reads `JSON.stringify` arguments in place, verifies artifacts with HACL* SHA-256 in `storeOpen`, and decodes the arguments once per call. What remains is the manifest parse, which grows with the number of blocks; an SBM11 store opens in about 5 ms (https://github.com/danbri/factoidal/issues/1039, https://github.com/danbri/factoidal-core/pull/135).
- The chunked Turtle reader (the default `l4sbm11-pack` path and the source layer's split read) reads a subject such as `prefix:Atto`, `base:x` or `version:v` as a prefixed name. Before, it took the name for a `PREFIX`/`BASE`/`VERSION` directive and refused the document (QUDT-all-in-one-OWL.ttl) (https://github.com/danbri/factoidal/issues/1028, https://github.com/danbri/factoidal-core/pull/128).
- RML: a reference to a SPARQL result binding (`formats:SPARQL_Results_CSV`) keeps the literal's datatype when the term map states none. `"5"^^xsd:integer` gives `"5"^^xsd:integer`, not `"5"` (https://github.com/danbri/factoidal/issues/1034, https://github.com/danbri/factoidal-core/pull/129).
- Tests: 996 Apache Jena ARQ expression tests run as SPARQL on the package (`test/jena-arq-expr.test.mjs`). Each case that differs from Jena has a verdict: a Factoidal defect with an open issue (https://github.com/danbri/factoidal/issues/1041, https://github.com/danbri/factoidal/issues/1042, https://github.com/danbri/factoidal/issues/573), or a Jena extension or difference from the SPARQL specification (https://github.com/danbri/factoidal-core/pull/132). Graph names that are blank nodes: `test/graph-names-876.test.mjs` (https://github.com/danbri/factoidal/issues/876 part 2, fixed in 0.16.0 by https://github.com/danbri/factoidal-core/pull/75; https://github.com/danbri/factoidal-core/pull/130).
- Tests and release process: no npm test skips when the wasm lacks an op; each test file asserts the ops it needs, so a wasm without an op fails. The `serve --tdb2` test, which needs Apache Jena, moved to `npm run test:jena`. Core PR CI runs `tests/dataflow/run.sh` and `npm test`. `tools/npm-release-check.mjs` checks the version in package.json, package-lock.json and lib/version.mjs, and a dated changelog heading; the publish workflow runs it. `tools/fetch-builds.sh` warns when the installed release was built from a commit whose source differs from HEAD; `--strict` fails (https://github.com/danbri/factoidal/issues/1038, https://github.com/danbri/factoidal-core/pull/124, https://github.com/danbri/factoidal-core/pull/125).
- LWS: `factoidal lws-serve DIR --authz ASDIR` serves the storage and an authorization server on one port, the issuer the storage root without its trailing slash. The token endpoint and the JWK Set are under the storage root's `.well-known/` (`lws-token`, `lws-jwks`), so no storage resource name is taken from clients; the RFC 8414 metadata is at `/.well-known/lws-configuration` + the issuer's path. The engine decides which requests are the authorization server's (new op `authzOwns`, Lean `L4Factoidal/Authz/Mount.lean`, theorem `endpointOf?_mem`); the storage trusts the issuer with the JWK Set the engine publishes. JS: `listen({ authz: { dir, ... } })` from `@factoidal/core/lws/server`. `authzOpen` takes `mountedOn`, `tokenPath` and `jwksPath`, and answers `resources` and `jwks`.
- LWS and the authorization server read both forms of their well-known paths: the whole path (a client that reaches the server directly) and the path with the storage root's or issuer's path removed (a reverse proxy that serves the server at a path prefix and removes the prefix, as the router of Touchstone's `targetservers` does). Up to 0.16.0 the protected resource metadata named the wrong resource behind such a proxy (`L4Factoidal.LWS.resourceOfMetadataPath`). Test: `tests/authz/mounted.mjs`. Docker target for third-party testing: `deploy/lws-target/`.

## 0.16.0 (2026-10-26)

- Node settings in the evidence (https://github.com/danbri/factoidal/issues/975). The params of `node()` are the node's settings. With a wasm module that has the new op `pipelineCheckNodes` (Lean `Wasm/Ops/PipelineNodes.lean`, `Dataflow/NodeSettings.lean`), each evidence record carries `settings` (canonical: keys sorted, defaults of absent settings that narrow the contract such as `lenient: false` and `entail: 'none'`, a Dataset value as `{nquadsSha256}`) and `settingsDigest` (`sha256:` and the hex SHA-256 of the canonical text). A setting outside the proved domain of a proved stage (a lenient reader, an evaluator with `entail` other than `none` or with `output`, a key the stage's settings table does not name) makes the node's status `unproved`, with `registryStatus` and `outside` (each setting and the reason) in the record, so `run()` reports `proved: false`. A reader's `format` must name the stage's syntax (`ttl12` selects RDF 1.2 mode, reported as `derived.mode`); an evaluator's query must parse, else `node()` rejects. Design record: `docs/designissues/2026-10-25-pipeline-settings-and-provenance.md`.
- The output wire of a `shippedEvaluator` node follows its query form: SELECT gives `Table`, ASK `Answer`, CONSTRUCT and DESCRIBE `Dataset` (owner, 2026-10-25: "select give table? Sure"). So reader, CONSTRUCT, CONSTRUCT is well typed, and reader, SELECT, CONSTRUCT is not. Proved: every answer that meets the evaluator contract has the wire of its query form (`Dataflow.evalContract_wire`) (https://github.com/danbri/factoidal/issues/1026). The Lean wire enumeration has a new wire `table`.
- CSVW is a registered, bound stage: `node('CSVW (tabular data to RDF)', { metadata, mode, base, url })` runs `csvwToRdf` on CSV text and gives a Dataset and an evidence record with status `tested` (the W3C csv2rdf suite; no Lean contract, so `checked: false`) (https://github.com/danbri/factoidal/issues/975). `stages()` marks a stage `bound` only when the engine also reports it runnable.
- With the wasm of 0.15.0 or older (for example a mismatched local install), records have no settings, the evaluator's wire is the registry's `Answer`, and the CSVW stage stays `missing` and unbound.

- `packSbm11(text, { syntax, base })` packs an RDF document into the files of one SBM11 generation in memory and resolves to a `Map` from file name to bytes (data files, `.merkle` sidecars, `manifest.sbm11`; no `CURRENT`); `mapReader(files)` is a reader over such files for `openSbm11(source, { reader })`. The wasm op is `sbm11PackFiles` (Lean `Storage/Sbm11/PackBytes.lean`), one call per file. The files are byte for byte those of the native `l4sbm11-pack` for the same quads: 23 of 23 files for `test/fixtures/sbm11-tiny`, and all files of 605 of 605 W3C SPARQL 1.0 and 1.1 inputs (`SBM11_PACKFILES=1 tests/sbm11/census.sh`) (https://github.com/danbri/factoidal/issues/1009 stage 2). On the wasm of 0.15.0 or older, `packSbm11` rejects with `code: 'SBM11_NO_PACK_OP'`. The whole document and every file are in memory at once. Not yet: `factoidal pack` on SBM11, and a pack that streams its input.
- SPARQL: the inverse path `^p` keeps a pair whose object is a literal. SPARQL 1.1 §9.3 and §18.4 make `?x ^p ?y` the same as `?y p ?x`, so `?x` can bind a literal; up to 0.15.0 both evaluators (the in-memory one and the SBM11 id path) dropped those pairs, and `SELECT ?x ?y WHERE { ?x ^<http://e/p> ?y }` over `<http://e/s> <http://e/p> "v" .` gave no row. Apache Jena ARQ 5.6.0 gives the same rows as the fix (https://github.com/danbri/factoidal/issues/1023). Tests: `test/inverse-path-literal-1023.test.mjs` and the `#guard`s in `SPARQL/QueryTests.lean`. The F* tree has the same fix.
- SPARQL: a `FROM` or `FROM NAMED` IRI that names no graph of the dataset gives a warning of class `dataset-iri-not-found` in the `warnings` member of the query envelope (`class`, `clause` (`FROM` or `FROM NAMED`), `iri`, `message`), and on standard error in the native `l4factoidal query` command. The rows do not change: the clause adds no graph, as before (https://github.com/danbri/factoidal/issues/1032). Lean: `SPARQL.datasetWarnings` beside `applyDataset`, whose merge theorem is unchanged; `#guard`s in `SPARQL/QueryTests.lean` and `Wasm/Ops/Query.lean`. Tests: `test/from-iri-not-found.test.mjs` (plain assertions; https://github.com/danbri/factoidal/issues/1038 records why an expected failure that waits for a rebuild blocked the build of this release).
- Tests, no engine change: GeoSPARQL `geo:wktLiteral` values made with `STRDT(CONCAT("POINT(", STR(?lon), " ", STR(?lat), ")"), geo:wktLiteral)` in SELECT, in a sub-SELECT that feeds `geof:sfWithin`, and by an INSERT whose stored literal `geof:sfWithin` then tests; from a CSVW column whose datatype object is `{"@id": "http://www.opengis.net/ont/geosparql#wktLiteral", "base": "string"}`; and from an RML object map with `rml:datatype` or a `rml:datatypeMap` with `rml:constant`. `test/wkt-generation.test.mjs` (6 pass on the 0.15.0 wasm) and `#guard`s in `Wasm/Ops/Query.lean` and `Wasm/Ops/Formats.lean`.

- Tests, no engine change: `test/sparql-string-arg-types.test.mjs` holds 6 expected failures for SPARQL 1.1 string functions that accept arguments the specification makes type errors, and for SUBSTR rounding (https://github.com/danbri/factoidal/issues/1036), found by porting Apache Jena ARQ expression tests (`docs/designissues/2026-10-25-jena-style-facade-feasibility.md`).

## 0.15.0

- `openSbm11(source)` and `registerSbm11Source(source, reader)` are back, with the wasm ops `sbm11Open`, `sbm11Query`, `sbm11Close`: SPARQL over an SBM11 generation (the Shardborough store) in Node and in the browser, reading each file at an offset through a host reader (https://github.com/danbri/factoidal/issues/1009, https://github.com/danbri/factoidal-core/pull/93). Fix: in 0.14.0 `sbm11Open` trapped (wasm `unreachable`) because the C host-read functions had a signature that differs from the generated one; the wasm build now fails on any such mismatch. Not yet: the Merkle check of each read, a generation with a delta log (refused at open), packing SBM11 from npm.
- `lwsSbm11Reader(url, { auth, headers, transport })`: a reader for `openSbm11` of an SBM11 generation held as Linked Web Storage resources, by HTTP `Range` GETs when the server answers `206` with a matching `Content-Range`, else by whole GETs kept in memory; a changed `ETag` refuses the read, and `store.evidence` lists each resource read with its `ETag` (https://github.com/danbri/factoidal/issues/1010, https://github.com/danbri/factoidal-core/pull/90). In Lean every reader is now a storage `Medium`. `browser.d.ts` now types `openSbm11` and `registerSbm11Source`.
- The native `l4factoidal query` command keeps a named graph with no triple (RDF 1.1 Concepts §4); before, the dataset went through an N-Quads round trip, which cannot state an empty graph (https://github.com/danbri/factoidal/issues/876 part 1, https://github.com/danbri/factoidal-core/pull/94).
- SPARQL: a property-path alternative of IRIs (`?s p|q ?o`) is planned as the UNION of its triple patterns, so the store planners use their indexes for it; a theorem proves the two forms give the same solutions in the same order and multiplicity, and a test checks that both give the same plan and rows (https://github.com/danbri/factoidal/issues/1008, https://github.com/danbri/factoidal-core/pull/96).
- `pipe()` and `run()` take the type check and the union of the named assumptions from the engine's op `pipelineCheck`, computed from the Lean stage registry; one theorem (`Pipeline.guarantee_sound`) gives the guarantee of every well-typed pipeline (https://github.com/danbri/factoidal/issues/1002 step 1, https://github.com/danbri/factoidal-core/pull/82). `pipe()` adds `wellTyped` and `check`; `run()` adds `wellTyped` and refuses a pipeline that is not well typed unless `{unchecked: true}`, then reports `proved: false`. `stages()` adds `params`. With a wasm build that has no op `pipelineCheck`, `wellTyped` is null and the union is computed from the nodes as before.

## 0.14.0

**Checked pipelines.** Each component (reader, store, query evaluator, writer, reasoner, validator, proof checker) has one interface type whose contract against the W3C specifications is part of the type. A component cannot be added without a contract; a contract that is not proved yet is a named assumption, listed and counted in CI. A theorem states that the SPARQL answer agrees with the SPARQL 1.1 semantics for data from any source (a parsed document, a Dataset after edits, an update, a reasoner's output, a union of stores), given the listed assumptions. Status and gaps: https://github.com/danbri/factoidal/issues/975.

- `explain(sources, description, { profile: "rdfs" })`: whether the sources RDFS-entail a description graph (its blank nodes are variables), with a checked derivation (`bundle`) when it does and the reason (`rejection`) when not (https://github.com/danbri/factoidal/issues/1002).
- `run(pipeline, input, { unchecked: true })`: runs nodes whose stage is not proved; each evidence record has `checked`, and the result has `proved` and `uncheckedSteps`. Without the option a stage with no contract does not run.
- `Dataset.warnings`: a language tag that is not well-formed BCP 47 is kept and reported with its line, column and offset; the writers write it unchanged (https://github.com/danbri/factoidal/issues/1004).
- SPARQL `SELECT *` on the store path returns the variables in query order, the same header as the in-memory path (https://github.com/danbri/factoidal/issues/1014).
- SBM11 in npm (`openSbm11`) is **not** in this release. Its wasm op `sbm11Open` traps (`unreachable`) in the release build, so the ops are not dispatched and the functions are not exported; the native `l4sbm11` commands are unchanged (https://github.com/danbri/factoidal/issues/1009).
- `factoidal pack`, `factoidal sample-store` and `sampleStorePath()` write the IBK5 layout (wire version 10, manifest layout `quad-ibk5-ptd2-lgi4-gbi1-merkle-v0`) when no `--layout` is given; the default was IBK3. Owner, 2026-10-25: "yes IBK5 not IBK3 as default sounds sensible, assuming no major downside" (https://github.com/danbri/factoidal/issues/1009). `factoidal serve` over such a store takes changes to every graph; over an IBK3 store a change to a named graph answered 501. `--layout ibk3` still writes IBK3. `sampleStoreFacts.layout` is now `'ibk5'`.
- `stages()`, `node()`, `pipe()`, `run()`: the registered Lean stages as nodes (https://github.com/danbri/factoidal/issues/1002, step 2). `stages()` is the engine's op `stageList`, read from the Lean stage registry: name, interface type, wire types, status, contract and named assumptions of each stage. A value on a wire is `{graph, evidence}`; each node adds one evidence record `{stage, status, contract, assumptions, artefact}`, and `run()` reports the union of the named assumptions of the nodes. A stage with status `missing` does not run. Needs a wasm build with the op `stageList`.
- `factoidal pack` writes a set of rows in every layout (https://github.com/danbri/factoidal/issues/1006). Correction to 0.13.0: its entry says that the stores keep one copy of a repeated triple, but in 0.13.0 that was true for the IBK4 and IBK5 layouts only, and only on read. The default layout (IBK3) kept a repeated triple, and kept `"a"@en` and `"a"@EN` as two rows, so `COUNT(*)` counted both; the IBK4 and IBK5 packers also wrote the repeated rows. Now each packer keeps the distinct triples it has written and writes a triple only once (per graph on the quad layouts). A source with no repeated triple gives the same generation as before. The packer's memory now grows with the number of distinct triples of the source. Proved: `Dataflow.packedRows_keyNodup`; tests: `test/pack-is-a-set-1006.test.mjs`.
- The N-Triples, N-Quads, Turtle and TriG writers give a fresh valid label to a blank-node label outside BLANK_NODE_LABEL (the same label for each occurrence, never a label of another blank node), and refuse a language tag outside LANGTAG with an error that names the tag (https://github.com/danbri/factoidal/issues/986).
- A language tag is kept in lower case (RDF 1.2 Concepts §3.4: `"x"@en` and `"x"@EN` are one RDF term). Every reader, `STRLANG`, `STRLANGDIR` and the term constructors write the tag in lower case, so `LANG()` returns it in lower case, and a SPARQL answer no longer depends on the order of the triple patterns when the data spells one tag in two ways (https://github.com/danbri/factoidal/issues/1001).

## 0.13.0

**A parsed document is a set of quads** (RDF 1.1 Concepts §3 and §4;
https://github.com/danbri/factoidal/issues/972). Up to 0.12.0 a document
that stated the same triple twice gave a graph with two copies: `size`
counted 2 and `SELECT (COUNT(*) AS ?n)` answered 2. Every parser, the
streamed parse, the command's `query` and the stores now keep one copy.
Language tags compare case-insensitively (RDF 1.2 Concepts §3.4), so
`"a"@en` and `"a"@EN` are one term in a graph and in a store dictionary
(https://github.com/danbri/factoidal/issues/977).

SPARQL and RDF semantics fixes:

- `=` and `!=` follow RDFterm-equal (SPARQL 1.1 §17.4.1.7). Terms of
  different kinds (IRI, blank node, literal, triple term) give `=` false.
  Two literals that are different terms give a type error, except where
  the §17.3.1 extension of the W3C tests gives false: `rdf:langString`
  against another datatype, and `xsd:dateTime` against `xsd:date`. The
  SPARQL 1.0 open-world tests: 18 pass, 0 fail (out of 18); were 13 pass,
  5 fail.
- `rdf:XMLLiteral` values compare by RDF term equality; SPARQL `=` on two
  different XMLLiteral terms is a type error
  (https://github.com/danbri/factoidal/issues/963). The RDF/XML parser's
  exclusive XML canonicalization is repaired.
- A query with `FROM` clauses queries the RDF merge of those graphs
  (SPARQL 1.1 §13.2.1): blank nodes from different `FROM` graphs are no
  longer joined (https://github.com/danbri/factoidal/issues/979).
- RDFS closure rule rdfs9 accepts a blank node as the sub-class
  (RDF 1.1 Semantics §9.2; https://github.com/danbri/factoidal/issues/982).
- The RDF/XML writer keeps the base direction of a directional language
  string (`its:dir` with `rdf:version="1.2"`). The JSON-LD writer still
  drops it: https://github.com/danbri/factoidal/issues/984.
- Opening a dataset renames blank nodes inside triple terms as well as at
  the top level.
- `factoidal sample-store` under Deno printed its path three times: the
  pack and the activate each re-executed the whole command. It now
  re-executes once, before any work.

**`proofCheck` no longer joins blank nodes across artifacts**
(https://github.com/danbri/factoidal/issues/976). Up to 0.12.0 a bundle
could take `:A rdfs:subClassOf _:x` from one graph artifact and
`_:x rdfs:subClassOf :C` from another with the same RDFC-1.0 digest, and
conclude `:A rdfs:subClassOf :C` with `valid: true`. Blank nodes are now
scoped to the artifact or assumption they come from (RDF 1.1 Semantics
section 5.2), so that bundle is refused. A chain inside one artifact, and
a chain across artifacts through triples with no blank node, are still
accepted. The report has a new member `rejection`: `null` for a valid
bundle, else the first failed check in words. The bundle format and the
profile `fpp0/1` are unchanged.

**XMPP server from wasm.** `factoidal xmpp-serve DIR` and
`@factoidal/core/xmpp/server` run the Lean XMPP server
(`L4Factoidal.XMPP.Server` — RFC 6120 negotiation, SASL PLAIN and
SCRAM-SHA-256, binding, RFC 6121 roster/presence/messages) in the
WebAssembly engine, one engine session per TCP or direct-TLS (XEP-0368)
connection. New engine ops `xmppOpen`, `xmppSessionOpen`,
`xmppSessionFeed`, `xmppSessionDeliver`, `xmppSessionClose`,
`xmppRosterGet`, `xmppRosterSet`, `xmppClose`
(`formal/lean4/Wasm/Ops/XmppSession.lean`). The state directory is the
native carrier's layout (`accounts`, `roster/`, `spool/`), so a stanza
written as a file under `spool/<bare jid>/` is delivered to that
account. See `xmpp/README.md`.

Linked Web Storage kept in files, stage 2 (https://github.com/danbri/factoidal/issues/918;
design record `docs/designissues/2026-10-22-lws-storage-on-disk.md`):

- Stage 2 (`L4Factoidal/LWS/Bodies.lean`): with `--storage files` the bodies
  stay in their body files. An entry keeps its length, its FNV-1a and SHA-256
  digests and the types of a Turtle body, and no bytes (ACL resources keep
  theirs). A step that needs bytes (GET body or range, JSON Patch, a PUT a
  subscription may hear of, a move of a Turtle resource) answers
  `read: [PATH, ...]`; the host reads those files and gives them to the new op
  `lwsRead` (byte-region entry only), which checks them, and steps again. A
  start reads no body file unless the metadata lacks a fact; the peak RSS of a
  start and one GET of 1,000 and 4,000 resources of 16 KiB is 230 and 211 MiB
  (stage 1: 258 and 515 MiB). A changed body file is refused when it is read
  (the request answers 500), no longer at start.
- The LWS handles run a tree store (`TreeStore`, theorem `treeStoreLaws`) and
  a type index in persistent trees: the engine's step and persist of a PUT
  take 0.30, 0.27, 0.28 and 0.29 ms in a storage of 1,000, 2,000, 4,000 and
  16,000 resources (stage 1: 0.21 ms at 1,000, about 3 ms at 16,000). A POST
  no longer lists every path; a DELETE lists paths only for a container.
- The order of the entries of a snapshot and of `lws-files.json`, and of the
  activities of a recursive DELETE in one notification, is path order (was
  newest first). `lwsSnapshot` of a storage kept in files is refused.
- `solid-serve` keeps the snapshot: an expected failure naming issue 918.

An authorization server as a component (https://github.com/danbri/factoidal/issues/916;
design record `docs/designissues/2026-10-22-authorization-server.md`; skill
`skills/authz-server/SKILL.md`), decided in Lean (`L4Factoidal/Authz/`):

- `factoidal authz-serve DIR --resource IRI[,IRI...]` and
  `import { listen } from '@factoidal/core/authz'`: RFC 8414 metadata at
  `/.well-known/lws-configuration` (and `/.well-known/oauth-authorization-server`),
  a JWK Set, and an RFC 8693 token endpoint that exchanges a subject token for
  an RFC 9068 access token whose `aud` is exactly the requested resource
  (lws10-core "Authorization"). `lws-serve --issuer <its issuer>` accepts its
  tokens with no other setting. `factoidal authz-keys DIR` prints the JWK Set.
- Subject tokens: OpenID Connect ID tokens (lws10-authn-openid) and
  self-issued JWTs for https and did:key subjects (lws10-authn-ssi-cid; P-256
  and Ed25519 did:keys). SAML 2.0 is refused and not advertised: there is no
  XML Signature verifier (https://github.com/danbri/factoidal/issues/926).
  solid-serve does not accept these tokens yet
  (https://github.com/danbri/factoidal/issues/928).
- Documents the server fetches for a subject token: `https` only (`--allow-http`
  for tests), never from a loopback, link-local or private address
  (`--allow-private-fetch` for tests), from the address the engine checked,
  with no redirect.
- Keys: ES256 by default (`--alg EdDSA`), signed by HACL\* through three new
  P-256 externs (sign, secret-to-public, point decompression; RFC 6979 and
  Wycheproof vectors in `lake exe l4crypto-probe`); `kid` is the RFC 7638
  thumbprint; `--rotate-after` rotates and keeps the old key published until
  its tokens expire; `DIR/authz-keys.json` (mode 0600) is sealed under
  `FACTOIDAL_LWS_KEY` when it is set.
- New ops `authzOpen`, `authzStep`, `authzFetched`, `authzKeys`, `authzRotate`,
  `authzClose`.
- Theorems: `issueToken_verifies_published` and `issueToken_audience_exact`
  hold because of a run-time check of every issued token (the proof that
  removes the check: https://github.com/danbri/factoidal/issues/927);
  `exchange_refused_no_token` (a subject token that fails validation never
  yields an access token), `cid_valid_verified`, `didKey_valid_verified`,
  `oidc_valid_named_provider`, `chooseAddress_refuses_private` and others.
- Touchstone with this server in place of its reference one
  (`tools/lws-touchstone.sh --config auth --authz factoidal`, 2026-10-22):
  212 passed, 0 failed, 9 inapplicable (out of 221); of these
  core/authorization_server 9 pass, 0 fail (out of 9), auth/oidc 6 pass,
  0 fail (out of 6), auth/cid 22 pass, 0 fail (out of 22), auth/saml 3
  inapplicable (issue 926).

CORS in the LWS HTTP binding (https://github.com/danbri/factoidal/issues/923),
decided in Lean (`L4Factoidal/HTTP/Cors.lean`, `L4Factoidal/LWS/Cors.lean`), so
a page on another origin (for example GitHub Pages) can call `lws-serve`:

- A CORS-preflight request (`OPTIONS` with `Access-Control-Request-Method`
  and `Origin`) is answered 204 before any other decision, with no token and
  no access check: `Access-Control-Allow-Methods` (with `QUERY` and `PATCH`),
  `-Allow-Headers` (`Authorization`, `Content-Type`, `If-Match`,
  `If-None-Match`, `If-Modified-Since`, `If-Unmodified-Since`, `Link`,
  `Prefer`, `Slug`, `Range`, `DPoP`, `Accept`), `-Max-Age` 7200. An `OPTIONS`
  without `Access-Control-Request-Method` is answered as before.
- Every answer carries `Vary: Origin` (one `Vary` field with the answer's
  own), and, for an answered origin, `Access-Control-Allow-Origin` and
  `Access-Control-Expose-Headers` (`ETag`, `Link`, `Location`, `Allow`,
  `Accept-Patch`, `Accept-Post`, `Accept-Put`, `Accept-Query`,
  `Accept-Ranges`, `Content-Location`, `Content-Range`, `WWW-Authenticate`,
  `Preference-Applied`, `Repr-Digest`, `Last-Modified`,
  `Factoidal-Merkle-Root`). No `Access-Control-Allow-Credentials`: the token
  goes in `Authorization`.
- Default: echo a valid request `Origin` (Solid Protocol §8.1), never `null`.
  `lws-serve --cors-origin ORIGIN` (repeatable) answers only those origins;
  `--no-cors` sends no CORS field; config member `cors` (`false` or a list).
  A malformed origin stops the start.
- `authz-serve` gets the same (`Authz.stepCors`; methods `GET, HEAD, OPTIONS,
  POST`), with the same flags. `solid-serve` keeps its own Solid §8.1 CORS;
  its preflight is now answered before Web Access Control (it was 401 for a
  resource that is not public).

An LWS client (https://github.com/danbri/factoidal/issues/917; design record
`docs/designissues/2026-10-22-lws-client.md`):

- `@factoidal/core/lws/client`: `createLwsClient({ fetch, subjectToken,
  subjectTokenType })` with `discover`, `read`, `head`, `create`, `update`,
  `patch`, `delete`, `readLinkset`, `updateLinkset`, `move`, `list`,
  `typeIndex`, `search`, `subscribe`, `unsubscribe`, `requestAccess`,
  `grantAccess`, `getAccess`, `revokeAccess`, `verifyNotification`; and
  `createNotificationReceiver`, a webhook receiver that answers each delivery
  with the engine's verdict. `fetch` is injected (Node, a browser, or a
  transport such as XMPP).
- Every decision is in Lean (`L4Factoidal/LWS/Client/`, wasm ops
  `lwsClientStart` and `lwsClientStep`): the 401 flow with the three checks of
  lws10-core "Discovery Validation by a Client", RFC 8414 metadata and RFC 8693
  token exchange; conditional writes (the current ETag by default for
  `update`, `patch`, `updateLinkset`, `move`); no repeat after 405 or 415, no
  POST again after a 5xx or a lost answer; paging by `rel="next"` only;
  linkset writes only in advertised methods and formats; the RFC 9421 check of
  a notification. Theorems: `walk_concat`, `walk_members_once`,
  `step_write_precondition`, `step_no_token_request_without_validation`,
  `step_no_blind_create_retry`, `step_no_repeat_after_refusal`.
- CLI `factoidal lws-client <op> URL`.
- Self-issued credentials (lws10-authn-ssi-cid): `createLwsClient({ selfIssued:
  { subject, keyId, jwk } })`; the engine signs the ES256 JWT with HACL*.
- Expected failure: OpenID sign-in is not built (row names issue 917).

## 0.12.0 — 2026-10-22

One error model for the whole package
(https://github.com/danbri/factoidal/issues/882 item 4,
https://github.com/danbri/factoidal/issues/901 KR 3.1). Every op error
envelope of the engine carries a stable `code`, the input `position` where
the input defines one, and the `spec` section where one applies; the engine
decides all three (`formal/lean4/Wasm/Ops/ErrorModel.lean`). The package
copies them into one class, `FactoidalError`. The README "Errors" table is
generated from the engine's list.

### Breaking changes

- `DatasetHandle`, the name of `Dataset` before 0.10.0, is removed. Use
  `Dataset`.

- `ParseError` is removed. Every function rejects with `FactoidalError`
  (`code`, `position`, `spec`, `cause`); a parse error has
  `code: 'parse.syntax'` (or `parse.rdf12-required`, `term.invalid-iri`,
  `term.invalid-langtag`) and `err.position.{line, column, offset}` in place
  of `err.line`, `err.column`, `err.offset`. `position.byteOffset` is new.
- Error messages are the engine's text, with no `<function>: l4factoidal:`
  prefix. A parse with an inferred format no longer appends "(format inferred
  as ...)" to the message; `err.formatInferred` and `err.format` say it.
- An unknown option key, an unknown format name, an `entail`, `output`,
  `version`, `owlClosure` mode, `rmlMap` source kind or `Dataset.closure`
  regime outside the engine's tables, and options that cannot be combined
  were a `TypeError`; each is now a `FactoidalError` (`option.unknown`,
  `format.unknown`, `option.invalid-value`, `regime.refused`,
  `option.conflict`) decided by the new engine op `apiCheck`. A `TypeError`
  stays only for an argument of the wrong JavaScript type.
- A method of a disposed `Dataset` was a `TypeError`; it is now the engine's
  `FactoidalError` with code `handle.disposed`. A closed `Store` is the same.
- `queryRaw` rejected with an `Error` whose message began "SPARQL query
  failed:" and which had `stderr`; it now rejects with the engine's
  `FactoidalError` (`query.syntax` with a position, or `query.failed`).
- File-system and IndexedDB failures (`openStore`, the delta log) are
  `FactoidalError` with code `host.io` and the original error as `cause`.
- `@factoidal/core/fn` `entail()` with an `x-ikl-*` regime rejects with code
  `regime.refused` and the message names `query`, the function that refuses.

Linked Web Storage kept in files, stage 1 (https://github.com/danbri/factoidal/issues/918;
design record `docs/designissues/2026-10-22-lws-storage-on-disk.md`), decided in
Lean (`L4Factoidal/LWS/Journal.lean`, `FileLayout.lean`):

- `factoidal lws-serve DIR --storage files` (config member `storage: "files"`,
  `listen({ storage: 'files' })`; the default stays `snapshot`): DIR holds one
  file per resource body under `bodies/`, a journal `lws-journal` with one
  record per change, and a metadata file `lws-files.json` that the journal is
  folded into when it passes max(1 MiB, the size of the metadata file). A
  write no longer rewrites the whole storage: a PUT into a storage of 1,000,
  2,000 and 4,000 resources took 2.70, 2.40 and 2.89 ms, against 42.6, 83.9 and
  170.4 ms with the snapshot (`tests/lws/scaling.mjs`, rows "storage").
- A journal record is valid only when it is complete and its SHA-256 matches;
  a torn last record is ignored at start (theorem `decodeFrames_torn`).
  Replaying the records of a sequence of steps gives the metadata of the store
  after them (`replay_records`, `persist_replay`).
- With `FACTOIDAL_LWS_KEY` every body file and journal record is sealed with
  ChaCha20-Poly1305 (HACL*), the file's own name in the associated data, and
  `lws-files.json` as the snapshot is.
- An existing `lws-state.json` is migrated at the first start in files mode and
  renamed to `lws-state.json.migrated`.
- New ops `lwsLoad` and `lwsPersist` (byte-region entry only): the engine names
  the files to read and gives every file operation and byte; the host
  (`lws/persist.mjs`) performs them. `tools/lws-touchstone.sh --storage files`.
- Stage 1 still holds the whole storage in memory; stage 2 (bodies read on GET,
  the metadata in an on-disk index) is an expected failure in
  `tests/lws/scaling.mjs` naming issue 918.

Linked Web Storage Search and Type Index Services (`lws10-index`, w3c/lws-protocol
`9a08ff65`; https://github.com/danbri/factoidal/issues/912), decided in Lean
(`L4Factoidal/LWS/TypeIndex.lean`, `Search.lean`):

- The storage description advertises a `TypeIndexService`
  (`GET /.well-known/lws-type-index`, a paged `TypeIndex`) and a
  `TypeSearchService` (`QUERY /.well-known/lws-type-search` with an
  `application/lws-query+json` filter in conjunctive normal form over `type`
  and indexed relations such as `describedby`; a paged ContainerPage).
  Option `typeIndex: false` of `listen`/`openLwsStorage` turns both off.
- Types come from the native class, from `Link: <T>; rel="type"` on POST and
  on `Prefer: set-linkset` PUT and PATCH, and from `rdf:type` in Turtle
  content up to 1 MiB. Such a `type` link was refused with 409 before; it is
  now a declared type and appears in the linkset document. A `type` link
  that names an LWS or LDP class is still refused with 409. A PUT or PATCH
  that applies `Prefer: set-linkset` answers `Preference-Applied: set-linkset`.
- The index is kept by the store on every write and rebuilt in one pass when
  a snapshot is opened. Answers, `totalItems` and the type index hold only
  what the requesting agent may read now. Theorems `ixSearch_eq_specSearch`
  and `searchAnswer_authorized`.

Linked Web Storage Access Requests and Grants (LWS core §Access Requests
and Grants, w3c/lws-protocol `9a08ff65`;
https://github.com/danbri/factoidal/issues/913), decided in Lean
(`L4Factoidal/LWS/AccessPolicy.lean`, `AccessGrants.lean`):

- The storage description advertises an `AccessRequestService`
  (`/.well-known/lws-access-requests/`) and an `AccessGrantService`
  (`/.well-known/lws-access-grants/`), each with `conformsTo`
  `https://www.w3.org/ns/lws#AccessProfile`. Both endpoints are LWS
  containers: GET lists (paged), POST of an `application/lws+json` document
  answers 201 with `Location`, GET and DELETE act on one member. Option
  `accessGrants: false` of `listen`/`openLwsStorage` turns both off.
- Any authenticated agent creates an access request; only the storage
  controller (`acl:Control` on the storage root) creates or revokes a grant.
  A document without `type`, `storage` (this storage), `access`, a policy
  `type` with `AccessPolicy`, `action` (`read`, `modify`, `create`,
  `delete`), `assignee`, or with a bad `inbox`, `target` or constraint,
  answers 400.
- A grant is part of the access policy beside Web Access Control: it permits
  exactly its actions on exactly its targets (a container grant does not
  reach the members) to its assignee (`foaf:Agent` for the public), when
  every constraint holds: `dateTime` (`eq`, `gt`, `gteq`, `lt`, `lteq`),
  `format` and `type` of the resource, `client` (the token's `client_id`)
  with `eq` or `isAnyOf`; `purpose` is accepted and no request satisfies it.
  A move needs `delete` of the resource and `create` in the destination.
  Notification subscriptions and deliveries, and the type index answers,
  see the same access. Theorems `grantsPermit_sound`,
  `policyPermits_excluded`, `recordPermits_expired`, `grantsPermit_revoke`,
  `grantAllows_acl`.
- A new grant is announced (one `Create` notification) to its `inbox` and
  to the inbox of each access request naming one of its assignees. Grants
  and requests are kept in the storage snapshot (member `access`).
- The storage controller hears of a new access request
  (https://github.com/danbri/factoidal/issues/920). Core §Access Requests and
  Grants: "When a new access request is submitted, the storage controller
  SHOULD be notified." The draft names no inbox for the controller, so this
  server's is configuration: `listen({ controllerInbox: URL })` or
  `factoidal lws-serve --controller-inbox URL`. When it is set, each new
  access request gives one `Create` notification there (signed, retried, as
  every delivery); when it is not set, nothing is sent. An inbox that is not
  `http` or `https` stops the start.

Linked Web Storage moves and notifications, three more rules
(w3c/lws-protocol `9a08ff65`), decided in Lean:

- 301 at the previous identifiers of a moved resource
  (https://github.com/danbri/factoidal/issues/914;
  `L4Factoidal/LWS/MoveRedirect.lean`). §Moving Resources: "Such a server
  SHOULD respond to subsequent requests on the previous identifiers of the
  resource and of its auxiliary resources with 301 Moved Permanently,
  including a `Location` header field pointing at the new identifier." After
  a move, a request to the old path of the resource, of each descendant of a
  moved container, of its `.acl` and `.meta` and of its `?linkset` answers
  301 with the new IRI, when the same request at the new path would be
  authorized (§Privacy Considerations, "Redirects": "Servers SHOULD apply the
  same access control to such responses as to the moved resource itself");
  otherwise the old path answers as before. A chain of moves answers the
  current path. The table holds at most `redirectsMax` pairs (default 256,
  `lws-serve --redirects-max N`), is kept in the snapshot (member `moved`),
  and loses a pair when a new resource is created at its old path or the
  moved resource is deleted. Theorems `redirect_current`, `after_ok`,
  `redirect_after_move`.
- A webhook inbox that names this server under another host name, an IP
  address or `localhost`, at its port, is refused with 400
  (https://github.com/danbri/factoidal/issues/915;
  `L4Factoidal/LWS/InboxGuard.lean`). The engine compares the inbox
  authority with the base IRI, the bound address and the interface
  addresses; for a host name it answers `lwsStep` with `resolve: {host}`, the
  host resolves the name and steps the request again with `resolved`. The
  host passes `listen: {address, port, addresses}` to `lwsOpen`.
- A delivery rate limit per subscription (issue 915; the webhook suite:
  "Rate limiting and endpoint verification are suggested to prevent abuse of
  the subscription mechanism"): at most `deliveryLimit` deliveries (default
  10) in a window of `deliveryWindow` seconds (default 60;
  `lws-serve --delivery-limit N --delivery-window S`; `deliveryLimit: 0`
  turns it off). The activities over the limit wait and go, when the window
  ends, in one envelope with an `activity` array (core §Batching
  Notifications). An answer may carry `wake: SECONDS`; the host then calls
  the new op `lwsFlush`. Theorem `admits_le`: at most `deliveryLimit`
  deliveries per subscription in one window. Endpoint verification: the
  drafts define no procedure (no request, no challenge, no expected answer),
  so there is no behaviour to implement.

Linked Web Storage, three rules of the editor's draft (w3c/lws-protocol
`9a08ff65`, 2026-10-19), all decided in Lean:

- Container pagination (§LWS Media Type, Pagination;
  https://github.com/danbri/factoidal/issues/887). A container with more
  than `pageSize` members (option of `listen`/`openLwsStorage`, default 100,
  0 turns it off) answers in pages: `Link` relations `first`, `last`, `next`
  (not on the last page) and `prev` (not on the first page), page URIs
  `CONTAINER?page=N`, `totalItems` over the full membership, one `ETag` per
  page. Members are listed in increasing path order, each once (theorem
  `pageItems_concat`).
- Client-managed links (§Metadata, §Update Resource;
  https://github.com/danbri/factoidal/issues/888): `Link` with
  `Prefer: set-linkset` on PUT (replace) and PATCH (add), `Link` on POST, and
  JSON Patch or PUT of `application/linkset+json` on `PATH?linkset`.
  Server-managed relations (`linkset`, `type`, `format`, `size`, `modified`,
  `up`, `items`, `lws#storage`) answer 409; a malformed link answers 400.
  Client links are kept in the storage snapshot.
- Notifications (§Notifications and the webhook notification suite
  `lws10-notifications-webhook`;
  https://github.com/danbri/factoidal/issues/890). The storage description
  advertises a `NotificationService` (`subscriptionType`
  `["WebhookSubscription"]`, endpoint `/.well-known/lws-subscriptions/`) and
  an Ed25519 `JsonWebKey` verification method. An authenticated POST of a
  `WebhookSubscription` (`topic`, `inbox`, optional `expires`) answers 201;
  each topic must be readable by the agent (403 otherwise). Every successful
  write gives Activity Streams 2.0 `Create` (with `target`), `Update` or
  `Delete` (with `origin`) activities, sent only to subscribers who may read
  the resource at that time, as an `application/lws+json` POST to the inbox,
  signed with HTTP Message Signatures (RFC 9421) and `Content-Digest`
  (RFC 9530). The endpoint lists the agent's subscriptions; GET and DELETE
  manage one. A delivery answered 5xx, 408, 425, 429 or not at all is tried
  up to three times; 410 or three failed deliveries deactivate the
  subscription. Subscriptions and the signing key are kept in the storage
  snapshot. The host makes the requests the engine names and reports each
  status to the new op `lwsDelivered`; `listen`/`openLwsStorage` take
  `notifications: false` to turn it off.
- Moving resources (§Moving Resources;
  https://github.com/danbri/factoidal/issues/914). The storage description
  describes a `MoveResource` capability (`appliesTo` DataResource and
  Container, `preservesIdentifier` false). A JSON Patch (or PUT) of a
  resource's linkset that changes its `up` link moves it to that container,
  with its descendants when it is a container, in one step: the answer is
  200 with the new linkset and `Content-Location`, both containers get a new
  ETag, and a subscriber hears one `Move` activity (`origin`, `target`). A
  destination that is missing or not a container, a cycle, the storage
  root, a name already taken, another storage or a removed `up` link is
  409. The agent needs the delete of every moved resource and the create in
  the destination. `listen`/`openLwsStorage` take `moves: false` to turn it
  off. Theorem `move_tree`: a move keeps the containment hierarchy a tree.
- Three server options, each off by default and decided in Lean
  configuration, so that every Touchstone test that one of our
  configurations can satisfy runs (`tools/lws-touchstone.sh --config all`):
  `lws-serve --moves all|data|off` (`moves: "data"` describes `appliesTo`
  `[DataResource]` and answers a change of a container's `up` link with 409;
  `"off"` describes no `MoveResource`), `--no-linkset-put` (`linksetPut:
  false`: a linkset's `Allow` leaves out PUT and a PUT answers 405 with
  `Allow`, as lws10-core §Metadata requires when PUT is not advertised) and
  `--paginate-always` (`paginateAlways: true`: a container listing that fits
  on one page is still one paginated page, with `rel="first"` and
  `rel="last"` and no `rel="next"` or `rel="prev"`). An unknown `moves`
  value stops the start.
- Fixed: on a paginated container, `If-Match` with the `ETag` of its first
  page (which a GET of the container URI answers) failed with 412; the
  first page's tags are now current tags of the container.

Encryption at rest of the LWS and Solid storage snapshot, off by default
(https://github.com/danbri/factoidal/issues/921; owner, 2026-10-21: "Yes env
var please. Again off by default but good to show we can."):

- When the environment variable `FACTOIDAL_LWS_KEY` holds a 32-byte key (64
  hex digits or base64url), `lws-serve` and `solid-serve` write
  `DIR/lws-state.json` as format `lws-snapshot-sealed-1`: format id, cipher
  id `chacha20-poly1305`, key id (first 8 bytes of SHA-256 of the key), a
  12-byte nonce new for every write, and the ChaCha20-Poly1305 (RFC 8439,
  HACL*) ciphertext of the snapshot, with the header as associated data.
  `listen`/`openLwsStorage`/`openSolidStorage` take `storageKey` (text, or
  `null` to read no key).
- At start the file is authenticated before use. A wrong key, a changed or
  truncated file, a clear-text file with the variable set and a sealed file
  without it each stop the start with a one-line message (exit 1). With the
  variable unset, behaviour is unchanged.
- It protects the file on disk only: not the memory of a running server, not
  the key in its environment, not the answers to clients.
- Decided in Lean (`L4Factoidal/LWS/SnapshotSeal.lean`), with theorems over
  any AEAD with RFC 8439 correctness (`unsealDoc_sealDoc`,
  `unsealDoc_authenticated`, `unsealDoc_wrongKey`, ...). `lwsSnapshot` and
  `solidSnapshot` take an optional second argument `{"nonce":…}`.
- Cost with a key (2026-10-21, about 1,050 resources): a write takes about
  2.7 times as long (133 to 143 ms against 49 to 54 ms), the file is 1.33
  times larger, a restart about 2.1 times as long.

### Breaking changes

- The storage description has a second service, `NotificationService`, and
  `verificationMethod` and `authentication` members; its `ETag` is a digest
  of the document.
- A container listing is in increasing path order. Before, it was in the
  order of the store (newest write first).
- A container with more than 100 members returns only its first 100 members
  unless `pageSize` is set; follow `rel="next"`.
- PUT on a linkset resource replaces the client links. Before, it answered
  405.

### Unstable

- ANTICIPATORY AND UNSTABLE, off by default: a type search results resource
  (https://github.com/danbri/factoidal/issues/922). With
  `listen({ searchResults: true })` or `factoidal lws-serve
  --unstable-search-results`, a QUERY answer of the Type Search Service by an
  authenticated agent carries `Content-Location` naming
  `/.well-known/lws-type-search/results/<id>` (RFC 10008 section 2.3).
  lws10-index defines no such resource; its path, lifetime, snapshot member
  and behaviour are likely to change. A GET by the same agent and client lists
  the QUERY's results that a new QUERY would still answer (paged, filtered by
  current read access); anyone else gets 404; after `searchResultsTtl`
  (600 s) 410. The storage description marks it with the extension member
  `https://github.com/danbri/factoidal/issues/922#unstableResultsResource`.
  `lwsStep` request documents may carry `random` (16 bytes, base64); the LWS
  host sends it with every request. Decided in Lean
  (`L4Factoidal/LWS/SearchResults.lean`).
- Off by default: Merkle hashes of the LWS storage
  (https://github.com/danbri/factoidal/issues/919; owner, 2026-10-21: "As an
  optional, probably default off until we settle on stronger motivating
  usecase but good to have the fundamentals there"). With
  `listen({ merkle: true })` or `factoidal lws-serve --merkle`: a GET or HEAD
  of a resource carries `Repr-Digest: sha-256=:<base64>:` (RFC 9530, SHA-256
  of the stored bytes, HACL*); a container listing carries
  `Factoidal-Merkle-Root` and the member
  `https://github.com/danbri/factoidal/issues/919#merkleRoot` (a Merkle digest
  over its members and their digests); the storage description carries
  `https://github.com/danbri/factoidal/issues/919#storageMerkleRoot`. Under
  authorization the roots go to the storage controller only. Entity tags do
  not change. The hashes are kept by the store on every write, delete and
  move (only the containers above the change are recomputed) and rebuilt when
  a storage is opened; no hash is in the snapshot. Decided in Lean
  (`L4Factoidal/LWS/Merkle.lean`, `MerkleHttp.lean`), with theorems
  `MkState.dig_eq_recompute` (the kept digests equal a recomputation from the
  store) and `change_reaches_ancestor` (a change reaches every container
  above it, with collision-freedom of SHA-256 as a stated hypothesis).
  Cost (2026-10-21, wasm in Node): a write into a container of 2,000 members
  takes about 6.3 ms with the option on against 0.9 ms off (linear in the
  members of each container above the write); a reopen of 2,000 resources
  with the hashes rebuilt takes 246 ms.

### Performance

- LWS and Solid PUT and GET of a large body
  (https://github.com/danbri/factoidal/issues/903): one 100,000-triple
  N-Triples body (7.7 MB) took about 17 s to PUT and the GET stopped the
  engine with out of memory; now the PUT takes 85 ms and the GET 40 ms
  (`npm run test:costs`). The cause was the FNV-1a digest of the entity tag,
  computed in `Nat`: on wasm32 each byte made heap numbers. It now runs in
  `UInt32` (theorem `fnv1a32_eq_spec`: same value as the `Nat` definition).
  Peak memory of the 100,000-triple PUT and GET fell from 2,640 MiB to
  288 MiB. Scaling check: `node tests/lws/scaling.mjs`.

### Fixed

Seven defects of `lws-serve` that the Touchstone LWS conformance harness found
(https://github.com/danbri/factoidal/issues/911; record:
`docs/designissues/2026-10-21-lws-touchstone-run.md`). All are decided in
Lean (`formal/lean4/L4Factoidal/LWS/`):

- A POST or PUT with no content and no `Content-Type` is accepted
  (`Operations.writeMediaType`). Before, it answered 400, so the draft's own
  container-creation example (`POST`, `Content-Length: 0`, the
  `lws#Container` type link) failed. An empty data resource made this way
  has type `application/octet-stream`. Content without `Content-Type` still
  answers 400.
- The Turtle form of a container uses `http://schema.org/size`, as the
  `application/lws+json` context and the core draft's examples do. Before,
  it used `https://schema.org/size`, so the two forms were not RDF
  isomorphic. The WG's `lws10-vocab/vocabulary.yml` declares
  `https://schema.org/`; the conflict is recorded in `Binding.containerTurtle`.
- A container's `ETag` carries the FNV-1a digest of its listing in the
  negotiated media type (`Binding.containerTag`). Before, it was the
  container's clock only, and a host with a real clock sets the clock to
  the current second, so two changes in one second gave one strong tag.
  `Last-Modified` is unchanged.
- The `lws#storage` link of a 401 and the default token audience are the
  storage description IRI `<base>.well-known/lws-storage`, the IRI every
  other response links and the description's `id` (`Authorization.storageIri`).
  Before, both were the storage root `<base>`.
- `If-Unmodified-Since` is evaluated for every method (412 when the resource
  changed after the date), and `If-Modified-Since` and `If-Unmodified-Since`
  are compared as instants in all three HTTP-date formats of RFC 9110
  §5.6.7 (`HttpDate.parseHttpDate`; theorem `unixOfCivil_civilOfUnix`).
  Before, `If-Unmodified-Since` was ignored and `If-Modified-Since` matched
  only the exact `Last-Modified` text.
- A POST names its new resource with the first free name of the hint (or
  `res<clock>`), `-1`, `-2`, ... (`Operations.childPathFor`, theorem
  `childPathFor_fresh`). Before, a clash got the clock as its one suffix,
  and under a real clock the third POST to one container in one second
  REPLACED the second resource.
- The Turtle form of a container gives a contained container no
  `dcterms:modified`: the `application/lws+json` context defines
  `modified` for a DataResource only, so the JSON item's `modified` of a
  container is no triple, and the two forms must be RDF isomorphic.
- `factoidal lws-serve --page-size N` passes `N` to the engine's
  `pageSize`.
- Result: Touchstone (221 tests) runs with no failure, open 70 pass, 0
  fail, 151 inapplicable; with authorization 146 pass, 0 fail, 75
  inapplicable.

Breaking: an LWS access token must name the storage description IRI in
`aud` (or the `--audience` given). A token for the storage root IRI is now
refused with 401 `invalid_token`.

## 0.11.0 — 2026-10-21

No RDF, SPARQL, datatype or IRI decision is made in JavaScript any more
(https://github.com/danbri/factoidal/issues/894; owner, 2026-10-21: "The ja
leak fix is p0"). The engine parses, writes, escapes, compares and chooses
datatypes; the JavaScript copies term components and calls ops.
`tools/host-purity-lint.sh` group 3 scans the npm and hub JavaScript for RDF
syntax and runs in `npm test`.

### Breaking changes

These shapes could not be kept:

- `shexValidate` and `Dataset.validateShex`: a focus or shape given as a
  string is read as one RDF 1.2 N-Triples term (`'<http://…>'` or `'_:b'`);
  a bare IRI string is refused. Every API that takes a term as a string
  now reads it through one engine reader (`TermJson.readTermString`), so
  `_:x` is always a blank node and `<…>` always an IRI.
- `graphs()` returns `[NamedNode|BlankNode, Dataset]` pairs, not
  `[string, Dataset]`, so an IRI graph and a blank-node graph with the same
  text are never confused.
- A literal with a language and a direction has datatype
  `rdf:dirLangString` (RDF 1.2 Concepts; RDF/JS Data Model); before, the
  RDF/JS default gave `rdf:langString`.

- `factoidal lws-serve` and `@factoidal/core/lws` enforce storage-server
  authorization from the LWS editor's draft (401 with
  `WWW-Authenticate: Bearer resource_metadata`, the RFC 9728 metadata
  document, Bearer JWT access tokens checked for signature, `iss`, `aud`,
  `exp`, `nbf` and `iat`, then Web Access Control). `lws-serve` needs
  `--issuer IRI`, `--auth-config FILE` or, for development only,
  `--insecure-no-auth`; `listen()` with neither `auth` nor
  `insecureNoAuth` serves only what the ACLs give to the public. New op
  `lwsFetched`. https://github.com/danbri/factoidal/issues/886

- The N-Quads text functions of `@factoidal/core/rdfjs` (`nquadsToQuads`,
  `nquadsLineToQuad`, `quadsToNQuads`, `quadToNQuads`, `termToNQuads`,
  `DatasetCore.fromNQuads`, `DatasetCore.prototype.toNQuads`) call the engine.
  They throw until the engine is loaded: `await ready()` (new) or any other
  `@factoidal/core` call first. `nquadsToQuads` now rejects a line the
  N-Quads grammar rejects (before, `<http://e/a b>` was read as an IRI), and
  the writers escape as the engine's canonical N-Triples form does (before,
  `\b`, `\f` and other control characters were written raw).
- A JavaScript number answered by a registered extension function becomes
  `xsd:integer` only for an integer within ±(2^53 − 1); every other number is
  an `xsd:double` in the XSD 1.1 canonical form (`1e21` is `"1.0E21"`, before
  `"1e+21"^^xsd:integer`; `0.1` is `"1.0E-1"`, before `"0.1"`). `NaN`,
  `Infinity` and `-Infinity` answer `"NaN"`, `"INF"`, `"-INF"`; before they
  were the §17.6 error. A `bigint` answers `xsd:integer`
  (`L4Factoidal.XSD.JsValue.jsLiteral`).
- `queryHdt` answers a Dataset for CONSTRUCT and DESCRIBE; before it threw a
  TypeError chosen by a regular expression over the query text.
- `Literal` has a `direction` member (`''`, `'ltr'`, `'rtl'`), and a
  directional language-tagged string from the engine keeps its direction and
  its `rdf:dirLangString` datatype; `equals` compares it.

### New

- `isomorphic(a, b)`: dataset isomorphism by the engine
  (`Dataset.isomorphicOutcome`, blank nodes in triple terms included).
  `@factoidal/core/fn`'s `equals` uses it.
- `fromQuads(quads)`: a Dataset from RDF/JS quads, sent as term components.
- `ready()`: load the engine. `engineTables()`: the engine's format,
  regime, query-output and pack-syntax name tables.
- Ops (formal/lean4/Wasm/Ops/Handles.lean): `datasetQuadsJson`,
  `datasetAddQuadsJson`, `datasetDeleteQuadsJson`, `datasetFromQuadsJson`,
  `datasetGraphNames`, `datasetGraphAsDefault`, `datasetIsomorphic`,
  `parseQuadsJson`, `quadsToNQuads`, `termsToNTriples`, `resolveIri`,
  `queryForm`, `engineTables`; `datasetMatch`/`datasetMatchCount` take term
  objects. Theorems: `TermJson.decodeTerm_encodeTerm`,
  `TermJson.decodeQuad_encodeQuad`, `TermJson.mem_quadList_default`,
  `TermJson.mem_quadList_named`, `TermJson.toCanonicalNQuads_eq_quadList`,
  `TermJson.quadPage_append`, `XSD.JsValue.doubleLexical_inLexicalSpace`,
  `XSD.JsValue.integerLexical_inLexicalSpace`,
  `XSD.JsValue.jsLiteral_number_double`, `XSD.JsValue.jsLiteral_number_integer`.

### Added

- An extension function may answer an exact term: an RDF/JS term
  (Literal, NamedNode, BlankNode, or a Quad as an RDF 1.2 triple term), or
  `{value, datatype}`, or `{value, language, direction?}`. The lexical form
  and the datatype IRI are kept as given, ill-typed literals included (RDF
  1.1 Concepts §3.3). The engine checks only what RDF requires: absolute
  IRIs, a well-formed BCP 47 language tag, direction `ltr` or `rtl`; a term
  that fails is the §17.6 error for that call. A plain JS number still gets
  its datatype from `jsLiteral`. Theorem `TermJson.extAnswerJson_encodeTerm`:
  an app-supplied term is the answer, unchanged.

### Performance

- Dataset iteration reads the quads from the engine as one byte region (op
  `datasetQuadsBin`: a term table in the delta-log v2 term codec and four
  u32 indices per quad), decoded in JavaScript with `DataView` and
  `TextDecoder`. 60,000 quads: 178–205 ms under load, against 214–280 ms in
  0.10.0 and about the time of the N-Quads writer op in the same run.
  Theorems `decodeBin_quadsBin` and `quadsBin_binSpec`
  (`formal/lean4/L4Factoidal/RDF/QuadsBinTheorems.lean`) prove the region
  reads back as exactly the dataset's quads, so no run-time check is made.
  https://github.com/danbri/factoidal/issues/900

### Fixed

- `graphs()` (both APIs) no longer merges an IRI graph and a blank-node graph
  whose strings are equal.
- `Dataset` iteration builds its quads from the engine's term objects; it no
  longer parses N-Quads text in JavaScript.
- The Solid client resolves a relative target against `baseIri` by RFC 3986
  §5.2 (op `resolveIri`); before it concatenated strings.
- `factoidal query` table cells and `factoidal inspect` graph names are the
  engine's canonical N-Triples forms (escaped); `factoidal pack` reads its
  suffix table from the engine and detects the syntax of a file with an
  unknown suffix from its content.

## 0.10.0 — 2026-10-21

### Breaking changes

One wasm carries every capability (owner, 2026-10-20: "all this stuff goes
into a single mod we call Factoidal/core and a dingle wasm"):

- The duplicate smaller wasm (`l4-assets/l4factoidal-core.{wasm,mjs,js}`) and
  its `./core` and `./core-browser` subpaths are gone. `l4factoidal.wasm`
  serves every function of the package; import `@factoidal/core`.
  `l4-assets/version.json` has no `coreWasmSha256`/`coreWasmBytes`.
- No demonstration triples ship (owner: "All the CLIs are still bundled i
  just didn't want any actual demo triples cluttering the file"): the
  4,434-triple `sample-store/` directory is gone. `factoidal sample-store
  [DIR]` and `sampleStorePath([dir])` now pack 15 triples held in
  `sample-store.mjs` into a store under DIR or the temporary directory and
  return its path; `sampleStoreFacts` describes that store.
- The demonstration functions `matrixDeterminant`, `matrixScalarProduct`,
  `matrixVectorProduct`, `matrixOuterProduct`, `sigmoidPoints` and
  `sigmoidFormulaMathml` (and `capabilities().matrix`/`.sigmoid`) left the
  JavaScript API, `@factoidal/core/fn` and the types. The Lean ops stay and
  answer through `loadEngine().call(op, args)`.

One `Dataset` class whose data stays in the engine
(https://github.com/danbri/factoidal/issues/882 item 1):

- `Dataset` is a handle into the engine's dataset store; it no longer holds
  N-Quads text. `new Dataset(...)` and `Dataset.fromNQuads(...)` are gone:
  make one with `parse`, `openDataset` or another producer. It still implements RDF/JS DatasetCore:
  `add`, `delete`, `has` and `match` run in the engine (`match` and `has` use
  its indexes; `match` answers a new Dataset). The in-memory RDF/JS DatasetCore is
  `DatasetCore` in `@factoidal/core/rdfjs` (that subpath no longer exports
  `Dataset`).
- `DatasetHandle` is a deprecated alias of `Dataset` (removed in 0.11.0).
  `handle.close()`, `handle.closed` and `handle.toDataset()` are replaced by
  `dispose()`, `disposed` and the Dataset itself. Using a disposed Dataset
  throws a `TypeError`.
- `openDataset` answers a `Dataset` (a Dataset argument is cloned).
- `coreRdfsClosure`/`rhoDfClosure` and `rdfsPlusClosure` answer a `Dataset`
  (before: `{ok, ntriples}` and `{ok, ntriples, rounds}`; `rounds` is gone).
  `fn.coreRdfsClosure` and `fn.rdfsPlusClosure` drop `rounds` too.
- Text input with no `format` is no longer read as Turtle: the engine infers
  the format (op `detectFormat`: JSON-LD, RDF/XML, TriG or Turtle, in RDF
  1.2 mode) and reports it in `dataset.format` / `dataset.formatInferred`, or
  in the error message. N-Quads is never inferred; name it.
- Every function throws a `TypeError` for an unknown option key.
- `update(dataset, text)` answers a new Dataset and leaves its argument
  unchanged (as before); `dataset.update(text)` changes it in place.
- `fn.toDataset` answers a DatasetCore; `fn.fromDataset` takes a `Dataset`
  or a DatasetCore.

### New

- `Dataset` methods: `query` (with `entail` and `output`: SPARQL results
  JSON, XML, CSV, TSV), `update`, `validateShacl`, `validateShex`,
  `closure(regime)`, `canonicalize`, `serialize({format, version})`,
  `toString(format)`, `clone`, `has`, `match`, lazy RDF/JS quad iteration,
  `dispose`, `[Symbol.dispose]`; a `FinalizationRegistry` releases a
  collected Dataset.
- `serialize` writes every writer the engine has: N-Quads, N-Triples,
  Turtle, TriG, RDF/XML, JSON-LD, RDFC-1.0 canonical N-Quads, each with
  `version: '1.1'` (refuses RDF 1.2 terms) or `'1.2'`. `formats()` gives the
  engine's list; the README table is generated from it. Writers the engine
  lacks: https://github.com/danbri/factoidal/issues/883.
- `closure(data, regime)`.
- Engine ops (Lean, `Wasm/Ops/Handles.lean`, `Wasm/Ops/DatasetFull.lean`):
  `datasetClone`, `datasetCanonicalize`, `datasetClosure`,
  `datasetShaclValidate`, `datasetQueryRaw`, `datasetFormats`,
  `detectFormat`, `datasetFromCsvw`, `datasetFromRml`, `datasetFromJsonLd`,
  `datasetToJsonLd`, `datasetShexValidate`, `datasetRifEval`; and
  `datasetSerialize` writes N-Triples, TriG, RDF/XML and RDFC-1.0.
- Every example in README.md and API.md is executed by
  `test/doc-examples.test.mjs`.

### Other changes

- The README is a short summary: what the package is, a usage example, the
  JavaScript API and command list, the specifications covered with test
  scores and their sources, and measured strengths and gaps. The previous
  README is `API.md` in the repository (not in the tarball).
- New pure functions over engine ops that had no JavaScript function:
  `aeadSeal`, `aeadOpen` (ChaCha20-Poly1305, RFC 8439), `hpkeSeal`,
  `hpkeOpen` (RFC 9180 base mode), `proofCheck`, `proofInspect` (FPP0 proof
  bundles), `canonicalizeNQuads` and `normalizeNQuads` (N-Quads text in, text
  out). Tests: `test/pure-and-serve.test.mjs`.
- New `serveStore(root, {port, host})`: the `factoidal serve` SPARQL 1.1
  Protocol server as a function, `{url, port, close()}`. Node only.
- `factoidal serve --file DATA /ds`, the `fuseki-server --file` form, and
  the Fuseki service names `/ds/query`, `/ds/update` and `/ds/get` beside
  `/ds/sparql` (decided in `StoreEndpoint.lean`). Record and gaps:
  `docs/fuseki-replacement.md`; tests `test/fuseki-compat.test.mjs`. W3C live
  protocol run: 50 pass, 0 fail (out of 50).
- The wasm is rebuilt from `main`; the package carries the Lean 4 engine only.
  Package suite: 432 pass, 0 fail (out of 432); 4 of them are expected
  failures naming issues 829, 830 and 831.
- Removed: the 0.9.x subpath aliases `@factoidal/core/l4` and
  `@factoidal/core/l4-core` (files `l4.js`, `l4.d.ts`, `l4-core.js`,
  `l4-core.d.ts`), as announced in 0.9.0. Import `@factoidal/core`; the
  low-level engine handle is `loadEngine()`.
- `l4-assets/version.json` is written at release from the
  `danbri/factoidal-builds` release that built the wasm
  (`tools/fetch-builds.sh --set web`): source commit, build time, sha256 and
  size of both wasm files, and the engine's own version. The committed file
  is a placeholder. `factoidal version` prints the stamp and the loaded
  engine's `version()`, and exits 1 when the stamped sha256 differs from the
  installed wasm.
- RDF 1.2 format tags `turtle12`, `ntriples12`, `nquads12`, `trig12` are in
  the `DataFormat` type.
- Includes the entries listed under "Unreleased" below.

## Unreleased (included in 0.10.0)

- **The durable update log in the browser, on the Lean engine**
  ([issue 728](https://github.com/danbri/factoidal/issues/728); hub post 18).
  `deltaLogOpen`, `deltaLogAppend`, `deltaLogReadAllHex`, `deltaLogMerge`,
  `deltaLogDestroy` and `_deltaLogCorruptLastForTest` are back, with the names
  and result shapes of the F\* browser entry before 0.9.0, and
  `deltaLogInspect` and the capability `deltaLog` are new. One record per
  update, in the DLB1 format of the store's delta log; the engine ops
  `deltaLogEncode`, `deltaLogDecode` and `deltaLogMerge` make every decision
  about the bytes (checksums, a torn last record, merge on read), with
  theorems in `formal/lean4/L4Factoidal/Storage/BrowserLogTheorems.lean`.
  The browser entries keep the records in IndexedDB; the Node entries keep
  them in the memory of the process. A record that does not verify, and
  every record after it, is not applied.

- **SPARQL `SERVICE` failures inside `EXISTS` and under an outer `SILENT`**
  ([issue 735](https://github.com/danbri/factoidal/issues/735); SPARQL 1.1
  Federated Query §2.3 and §3.2). A failed `SERVICE` call without `SILENT`
  inside `EXISTS` or `NOT EXISTS` (in `FILTER`, `BIND`, an `OPTIONAL`
  condition, `HAVING`, `ORDER BY` or a `SELECT` expression) now fails the
  query, as the same call in a graph pattern does. A failed `SERVICE` call
  nested in the body of an outer `SERVICE SILENT` is a failure of the outer
  call, so the outer call gives one solution with no bindings; without
  `SILENT` on the outer call the query fails. The two expected-failure cases
  in `test/l4-parity.test.js` are now assertions.

- **`factoidal serve STORE --port N`: a SPARQL 1.1 endpoint over an activated
  store** ([issue 669](https://github.com/danbri/factoidal/issues/669), step
  1). SPARQL 1.1 Protocol query and update at `/sparql`, the Service
  Description on a GET there with no query string, and the Graph Store HTTP
  Protocol at `/data`. An update or a Graph Store write is appended to the
  generation's delta log as one batch, synced, before it is answered. The
  request framing, routing, status codes, negotiation and the delta-log batch
  are decided by the engine (`storeServeKeys`, `storeServeOpen`,
  `storeServeRequest`, `storeServeCommit`, `storeServeClose`); `bin/serve.mjs`
  moves bytes. W3C protocol, graph-store and service-description tests over
  a live socket: 50 pass, 0 fail (out of 50). Open gap: a quad generation's
  delta log is not replayed by the native quad reader
  ([issue 770](https://github.com/danbri/factoidal/issues/770)).
- **`@factoidal/core/core`: the core engine** ([issue 713](https://github.com/danbri/factoidal/issues/713),
  stage 4). `l4factoidal-core.wasm` (5.68 MB, 1.07 MB with gzip; the full
  engine is 10.54 MB, 2.07 MB) serves parse and serialize (Turtle, TriG,
  N-Triples, N-Quads, RDF/XML, lenient), SPARQL 1.1 and 1.2 query and update
  over text and dataset handles, canonicalization, the RDFS and OWL 2 RL
  closures and SHACL. The entry has the same exports as `.`; a function
  outside that subset rejects naming `@factoidal/core`, and
  `capabilities().profile` is `'core'` (`'full'` on the other entries).
  Files: `core.mjs`, `core.js`, `core-browser.js`, `core.d.ts`,
  `core-browser.d.ts`, `l4-assets/l4factoidal-core.{js,mjs,wasm}`.
- A SELECT of more than about 11,000 solutions, and `canonicalize()` of more
  than about 20,000 blank-node quads, no longer fail under Node's default
  stack with "Maximum call stack size exceeded". Four functions of the Lean
  library recursed once per row or per quad (`SPARQL.numberRows`,
  `SPARQL.rowsJoined`, `RDF.Canonical.collapseKeyedQQuads`, `dedupAdj`);
  each now compiles to an accumulator form proved equal to it. The Results
  JSON writer had also copied the rest of the document once per row.
- `NOW()` is bound ([issue 743](https://github.com/danbri/factoidal/issues/743)).
  Through `query()`, `update()`, dataset handles, the entailment path,
  `queryHdt()` and the store queries, SPARQL `NOW()` answered an error and left
  its variable unbound (W3C `functions/now01.rq` answered `false`). The engine
  now reads the system clock once per query or update and gives every `NOW()` of
  that execution the same `xsd:dateTime` value in UTC (SPARQL 1.1 §17.4.5.1).
  The wasm modules grow by about 82 KB (full) and 89 KB (core).
- The pure dispatch entries take the instant of `NOW()` as an optional last
  argument ([issue 748](https://github.com/danbri/factoidal/issues/748)).
  `call` and `callBlob` read no clock, so a host that uses them got an error
  for `NOW()`. `queryDataset` and `updateDataset` (fourth, after the base IRI),
  `queryRaw` and `storeQuery` (fourth) and `queryHdt` (second) now accept an
  `xsd:dateTime` lexical form such as `2026-10-10T12:34:56Z`; an empty string
  means none, and a text that is not a dateTime lexical form is an error. Hosts
  that pass fewer arguments do not change. `callIO` and `callBlobIO` still read
  the clock themselves.
- `Dataset` (`./rdfjs`) adds and looks up a quad in constant time. It
  scanned every quad it held, so `parse()` of 12,000 quads spent 3.1 s
  building the result; it now takes 0.35 s.

## 0.9.0 — 2026-10-10

**One engine: the Lean 4 build.** ([issue 713](https://github.com/danbri/factoidal/issues/713),
stage 3.) Owner, 2026-10-10: "We should make the main module Lean4-based.
Private builds might compare this with F\* (or indeed different wasms from
different toolchains)." The main entry (`.`: `index.js`, `index.mjs`),
`./api`, `./fn` and `./browser` now load the Lean 4 library `L4Factoidal`
compiled to WebAssembly (`l4-assets/`). Every function is a dispatch op of
that module behind the typed wrapper the F\* engine had, with the same
signatures and result shapes except where the list below says otherwise.

Removed, with no replacement shim (there are no users):

- the F\* bundles (`factoidal.js`, `factoidal.wasm.js`,
  `factoidal-npm-entry*.js` and their wasm assets) and the entry points
  that loaded them: `./wasm`, `./lite`, `./browser-wasm`, `./select`, and the
  `./factoidal*.js` subpaths. The F\* bundles stay build artifacts of
  `danbri/factoidal-builds`, for private comparison builds:
  `tests/engine-compare/run.sh PATH/TO/factoidal-npm-entry.js`.
- `hacl-wasm/` and `hacl-init.js`: Ed25519 is HACL\*'s C code compiled into
  the Lean wasm module, SHA-256 is the Lean hash, and there is no
  initialisation step.
- the COTTAS functions `openCottas`, `queryCottas`, `closeCottas` and
  `toCottas` (on the main entry and on `./fn`), and the browser delta log
  (`deltaLogOpen` ... `deltaLogDestroy`), which wrote COTTAS batches. The
  owner ruled the F\* COTTAS store essentially unused
  ([issue 566](https://github.com/danbri/factoidal/issues/566)). The
  Lean persisted store replaces them (below); its update path in JavaScript
  is [issue 641](https://github.com/danbri/factoidal/issues/641).
- the F\* `version.json` with its claims block. `l4-assets/version.json` is
  the engine's provenance.

New:

- **The persisted store on the main entry**: `openStore(source, options)`
  answers a `Store` (a store handle inside the engine: every artifact
  verified against its manifest's SHA-256 once, then queried from the
  retained blocks), `queryStore(source, sparql)`, `listStores()`, and
  `sampleStorePath()` / `sampleStoreFacts`. `source` is a collection root
  path (Node) or a reader function `(path) => bytes`, which is how a page
  reads a store over `fetch()`.
- `shaclValidate` and `shexValidate` on the Lean engine (ops of
  `formal/lean4/Wasm/Ops/Validate.lean`): SHACL Core, SHACL-SPARQL and SHACL
  1.2 node expressions; ShExJ or ShExC schemas. `shexValidate` answers a
  boolean (the F\* engine answered `null` outside its decidable fragment).
- SPARQL 1.2 queries: `query(data, q, {sparql12: true})` and
  `handle.query(q, {sparql12: true})` (ops `queryDataset12`,
  `datasetQuery12`): triple-term patterns, reified triples, annotations,
  `TRIPLE`/`isTRIPLE`/`SUBJECT`/`PREDICATE`/`OBJECT`.
- `query(data, q, {entail})` with `RDFS`, `OWL-RL`, `x-rdfscore` or
  `x-rdfsplus` runs in the engine (op `queryRaw`): the default graph is
  closed under the regime, then the query is answered. SELECT, ASK,
  CONSTRUCT and DESCRIBE.
- `loadEngine()`: the low-level engine handle (`call(op, args)`), for the
  dispatch ops the typed layer does not wrap.
- Common Logic: `clParse`, `clSerialize`, `clAlphaNorm`, `clNormalize` on the
  main entry (they were on `./l4-core` only).
- `browser.js` loads the wasm with `fetch` and
  `WebAssembly.instantiateStreaming`; `setAssetsUrl()` names another
  directory for the engine's three files.
- `parse(text, {lenient: true})` (op `parseDocument`,
  [issue 716](https://github.com/danbri/factoidal/issues/716)): the Turtle,
  TriG, N-Triples and N-Quads parsers skip each bad statement, keep the good
  ones and list one diagnostic per skipped statement in
  `dataset.diagnostics`: `message`, `line`, `column`, `offset` (a UTF-16
  index, as `ParseError.offset`) and a stable `class` (for example
  `undefined-prefix`, `bad-escape`, `unexpected-token`). The new option
  `maxErrors` stops the parse after that many diagnostics with one
  `too-many-errors` diagnostic. `capabilities().parseDiagnostics` is `true`.
  A document with no error gives the strict result and no diagnostics (a
  theorem in the Lean source). RDF/XML and JSON-LD parse strictly.

Changed:

- **`ParseError.offset` is a UTF-16 code-unit index into the input string**,
  so `text.slice(err.offset)` starts at the error. The F\* engine counted
  UTF-8 bytes; the Lean engine counts Unicode scalar values and the wrapper
  converts. (`line` is 1-based; `column` counts Unicode scalar values.) This
  unit is a coordinator default, recorded in
  `docs/designissues/2026-10-10-npm-lean-only.md`.
- Each SELECT solution `Map` iterates in the order of the SELECT clause
  (`head.vars`); it followed the member order of the engine's JSON binding
  objects, which carries no meaning.
- DESCRIBE answers the Concise Bounded Description of each named resource
  (the F\* engine answered the empty graph,
  [issue 702](https://github.com/danbri/factoidal/issues/702)).
- `serialize(data, {format: 'ntriples'})` answers the engine's N-Quads text
  and refuses data with a named graph (N-Triples has no graph term).
- `xmlWellformed` reads a DOCTYPE with an internal subset (the F\* parser
  answered `false` for any DOCTYPE); `xpathEval` is the full XPath 1.0
  evaluator and its node kinds include `root` and `namespace`;
  `mathmlEval` also evaluates `vector` and `matrix`; `rifEval`'s envelope
  has no `rounds`/`engineMs`; `tableauMaterialise` adds `budgetHit`;
  `rmlMap` reads the iteration format from the mapping's
  `rml:referenceFormulation`. Record:
  `docs/designissues/2026-10-10-npm-lean-only.md` section 6.
- `capabilities()` reports what the loaded wasm serves: new members
  `entailment`, `hdt`, `sparql12`, `store`; `cottasBytesStore` is gone.
- `engines.node` is `>=22.12`: `index.js` hands the ES module `index.mjs`
  to `require()`, so CommonJS and ES module callers share one engine and
  one `Dataset` class. (Node 20 reached end of life on 2026-04-30.)

Open, each with an expected-failure test:

- A failed `SERVICE` call without `SILENT` inside `EXISTS`, and a failed
  nested `SERVICE` under an outer `SILENT`
  ([issue 735](https://github.com/danbri/factoidal/issues/735)). A failed
  `SERVICE` call without `SILENT` elsewhere now fails the query
  ([issue 717](https://github.com/danbri/factoidal/issues/717), fixed).

Deprecated: `./l4` and `./l4-core` are aliases of `.` in 0.9.x and go in
0.10.0. (`./l4` was the low-level loader; `loadEngine()` replaces it.)

### Earlier in 0.9.0 (before the switch; `./l4-core` was the Lean entry then)

**Lean engine (`factoidal/l4-core`): 26 more functions of the main
entry** ([issue 713](https://github.com/danbri/factoidal/issues/713),
stage 1 of making the package Lean-only). `jsonldToRdf`,
`jsonldFromRdf`, `rmlMap`, `csvwToRdf`, `xmlWellformed`, `xpathEval`,
`xsltTransform`, `schematronValidate`, `jsonSchemaValidate`,
`mathmlEval`, `xformsRecalc`, `rifEval`, `queryHdt`,
`tableauMaterialise`, `tableauDlInconsistent`, `queryRaw`, the three
extension-function and two SERVICE-endpoint registry functions, and the
five `toan*` functions now run over the Lean wasm. Signatures and
result shapes are the F\* engine's. `parse(text, {format: 'jsonld'})`
now works on this engine. `tableauMaterialise` also returns `budgetHit`
on the Lean engine. The main entry (`index.js`) is unchanged.

**`factoidal/l4-core` serves the maths, VC and DID functions, and matches the
F\* engine's envelopes** (stage 2 of
[issue 713](https://github.com/danbri/factoidal/issues/713)). New on the Lean
engine, with the signatures and result shapes `index.d.ts` declares:
`matrixDeterminant`, `matrixScalarProduct`, `matrixVectorProduct`,
`matrixOuterProduct`, `sigmoidPoints`, `sigmoidFormulaMathml`, `vcSha256Hex`,
`vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`,
`vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical`, `vcCheckCredential`,
`vcCheckCredentialSubject`, `vcCheckNoDataLoss`,
`vcCheckRelatedResourceDigests` and `didKeyResolve`. The Ed25519 operations run
HACL\* compiled into the wasm module; they need no `initHacl()` call. Envelope
parity ([issue 685](https://github.com/danbri/factoidal/issues/685)): a Turtle,
TriG, N-Triples or N-Quads syntax error rejects with a `ParseError` carrying
`line`, `column`, `offset` and `format` (the Lean `offset` counts Unicode scalar
values, the F\* `offset` counts UTF-8 bytes); `parse()` and `openDataset()`
record the prefixes of a Turtle or TriG document; Turtle output accepts the
`prefixes` and `literalShorthand` options and prints bare numeric and boolean
literals by default; and each document that is parsed gets its own blank-node
scope, so merging two documents that both write `_:b0` keeps two nodes. The
Lean engine still has no `{lenient: true}` parse and no SPARQL 1.2 handle
query.

**Store format: the literal index is renamed LGI3 and LGI4; re-pack older
generations.** The literal search index folds each lexical form before it takes
character 3-grams. On 2026-10-10 the fold changed from ASCII-only to the Unicode
case mapping that SPARQL `LCASE` uses
([issue 706](https://github.com/danbri/factoidal/issues/706)), so the grams of a
non-ASCII literal differ and an index written under the old fold lacks rows the
Unicode `LCASE` keeps. The two layouts are now named LGI3 (was LGI1, sidecar
`.lgi3`) and LGI4 (was LGI2, sidecar `.lgi4`), and the manifest layout labels
changed with them. A generation packed earlier names LGI1 or LGI2; `storeOpen`,
`storeManifestInspect`, `storeQueryPlan`, `storeQuery`, `l4block-shard-activate`
and `l4block-quad-query` refuse it with the cause and ask for a re-pack.
`storeOpen` and `storeHandleList` also report `literalIndexes` and
`geoIndexes`, the number of retained blocks that hold a decoded index of each
kind. Record: `docs/designissues/2026-10-10-literal-index-lgi3.md`.

## 0.8.0 — 2026-09-16

**Behaviour change: parsing is strict by default.** `parse()` (and
every function that parses text input) now rejects on a syntax error,
an undeclared prefix, or a relative IRI with no `baseIRI` in effect,
instead of silently dropping the affected statements. The error is a
new `class ParseError extends Error` (`name`, `line`, `column`,
`offset`, `format` — position fields present for Turtle/TriG/
N-Triples/N-Quads, absent for RDF/XML and JSON-LD, which carry a
message only), exported from every entry point (`index.js`/`.mjs`,
`wasm.js`, `l4-core.js`, `api.js`/`.mjs`, `lite.js`/`.mjs`, and
`browser.js`, which declares its own copy since it has no imports).
Pass `{lenient: true}` to `parse()` to recover instead: the returned
Dataset holds whatever the parser recovered, and the new
`dataset.diagnostics` array lists what was skipped (needs the
npm-entry engine bundle's `parseDocument` export). Issues
[344](https://github.com/danbri/factoidal/issues/344),
[680](https://github.com/danbri/factoidal/issues/680),
[681](https://github.com/danbri/factoidal/issues/681).

**Dataset handles.** `openDataset(data, {format?, baseIRI?})` parses
once and keeps the result indexed in the engine, so repeated
`query()`/`update()`/`serialize()` calls against the returned
`DatasetHandle` skip both the re-parse and the SPARQL-index rebuild a
fresh `query(ds, ...)` call pays every time (measured ~2x faster per
call on a 2,000-triple two-pattern join in this session — see
`tests/perf/npm_handle_vs_stateless.mjs`). `query(data, sparql,
options)`, `serialize(data, options)` and `canonicalize(data)` also
accept a `DatasetHandle` directly; `update(handle, ...)` rejects with
a `TypeError`, since `update()` always returns a fresh Dataset while
`handle.update()` mutates the handle in place. `select.js` (the F*/
Lean backend selector) deliberately does not route `openDataset()` —
a handle is opened against one engine's own entry object, so there is
no "same handle on the other engine" to fall through to.

**Prefixes and Turtle literal shorthand.** `Dataset` gains `.prefixes`
(the declared map from parsing, `{}` for N-Triples/N-Quads) and
`.diagnostics` (own, non-enumerable properties, so `JSON.stringify()`/
`toArray()` are unaffected either way). `serialize(data, {format:
'turtle', prefixes?, literalShorthand?})` uses caller prefix pairs
(dropping unused caller namespaces, skipping caller labels when
auto-generating `nsN:` ones) when given, or automatically when `data`
is a Dataset with non-empty `.prefixes`; `literalShorthand` (default
`true`) controls whether `xsd:integer`/`decimal`/`double`/`boolean`
literals with a Turtle-grammar-matching lexical form print bare.
`DatasetHandle.serialize()` has the same options.

**New entry point `@factoidal/core/lite`** (`lite.js`/`.mjs`/`.d.ts`):
a smaller npm-entry ABI bundle (`factoidal-npm-entry-lite.js`, about
half the gzip size of the full bundle — see README.md's "Choosing a
bundle: full or lite") implementing the core surface (`parse`,
`query`, `update`, `serialize`, `canonicalize`, `graphs`,
`canonicalHash`, `openDataset`/`DatasetHandle`, the extension-function
and SERVICE-endpoint registration functions, `capabilities`) with no
SHACL, ShEx, OWL closure, JSON-LD, RDF/XML, CSVW, RML, RIF, XML,
XPath, VC crypto, COTTAS, or CLI bundle (no entailment regimes, no
`queryHdt`). `capabilities()` gains `profile` (`'full'` | `'lite'`),
`abiVersion`, `datasetHandles`, `parseDiagnostics`, `turtlePrefixes`.
Issue [684](https://github.com/danbri/factoidal/issues/684).

**`browser.js`: `query()` and `toRdf()` route through the npm-entry
ABI.** Whenever the persistent ABI bundle is available (already on
`globalThis`, or fetched by `loadNpmEntry()`), `query()` with `entail:
'none'` and `output: 'json'` (both defaults), and every `toRdf()`
call, now go through it instead of the eval-per-call CLI bundle —
falling back to the CLI bundle only when loading the ABI fails. This
makes the classic-`<script>` route (README.md's "Bundlers and Content
Security Policy" §b) CSP-safe for parsing and SELECT/ASK too, not only
for the operations already ABI-routed. New `openDataset(text,
{format?, baseIRI?})` on `browser.js` returns a handle with `query`/
`update`/`serialize`/`close` over the same ABI. Issue
[682](https://github.com/danbri/factoidal/issues/682) (second half).

Three new entry points, for two storage protocols:

* `@factoidal/core/lws` — a Node `http` server for the
  [Linked Web Storage Protocol 1.0 core](https://w3c.github.io/lws-protocol/lws10-core/);
* `@factoidal/core/solid/server` — the same shape for the
  [Solid Protocol v0.11.0](https://solidproject.org/TR/protocol) server
  conformance class, including the CORS preflight and the storage root;
* `@factoidal/core/solid/client` — the client conformance class over
  `fetch`, whose every request is built by the engine and whose every
  response is read by it.

Three commands: `factoidal lws-serve DIR`, `factoidal solid-serve DIR`
and `factoidal solid-client <get|put|post|delete|discover> URL`.

Every protocol decision is the Lean engine's; the hosts move bytes. The
operations are `lwsOpen`/`lwsStep`/`lwsClose`,
`solidOpen`/`solidStep`/`solidClose` and
`solidClientRequest`/`solidClientResponse` on the WebAssembly dispatch
ABI. **A module built before they landed answers `unknown op`**: the
entry points report it through their `…OpsAvailable(engine)` probe and
the commands exit 3. `DIR` is not read or written yet — the resource tree
lives in the engine handle — and Solid-OIDC token verification is not
built, so the first slice serves public resources and unauthenticated
writes. Issue
[659](https://github.com/danbri/factoidal/issues/659).

New entry point `@factoidal/core/api`: `createApi(entry, options?)`
wires the typed `parse`/`query`/`serialize`/... surface around an
already-loaded npm-entry ABI object, with no `fetch` and no `new
Function(src)` eval — the route for a bundler (esbuild, webpack,
Rollup) or a page under `Content-Security-Policy: script-src 'self'`.
`entry` accepts the `factoidalNpmEntry` object itself, a Promise of
it, or a zero-argument function returning either. `browser.js`'s
`loadNpmEntry()` now checks `globalThis.factoidalNpmEntry` before
fetching anything, so a classic `<script src="factoidal-npm-entry.js">`
tag (or the new `setNpmEntry(abi)`) makes every `browser.js` operation
already routed through that ABI CSP-safe too. `package.json`'s
`exports` map gains `./api` and direct subpaths for
`factoidal-npm-entry.js`/`.wasm.js`/`.wasm.assets/*` (already shipped
in `files`, not previously importable as package subpaths). Every
typed entry point (`factoidal`, `factoidal/wasm`, `factoidal/api`,
`factoidal/l4-core`) now reports `version` and `engine`. See
README.md's "Bundlers and Content Security Policy" section. Proved
against a real headless-Chromium page under that CSP header
(`tests/web-demos/bundler_csp_smoke.sh`) and against esbuild's bundler
(`test/bundler-esbuild.test.mjs`). Issue
[682](https://github.com/danbri/factoidal/issues/682).

README.md documents `parse()`'s output order (canonical/sorted
N-Quads, not document order) and the blank-node label scheme
(`_anonN` in document order for anonymous nodes, `p<k>_d<n>_` scope
prefixes, no RDF meaning beyond within-dataset identity), pinned by
`test/parse-order.test.js`. No behavior changed. Issue
[683](https://github.com/danbri/factoidal/issues/683).

A bare string where `parse`, `query`, `update`, `openDataset`,
`serialize`, `canonicalize` or `DatasetHandle.serialize` take an
options object now means `{ format: <string> }`, so
`serialize(ds, 'turtle')` is `serialize(ds, { format: 'turtle' })`.
Until now the string was read as an empty options object and
`serialize(ds, 'turtle')` returned N-Quads with no error (found by the
0.8.0 release probe). Any other non-object value throws a `TypeError`
naming the function. Pinned by `test/options-format-string.test.js`.

The shipped bundles are built from a fresh extraction of the F\* OWL
closure source. The committed OCaml for `OWL.Closure` and
`OWL.DirectMapping.Filter` had lagged the `.fst` files since the
2026-09-07 OWL soundness audit (commit 709f3c4; the "Check F\* Extraction"
workflow was red on `claude/main` from that date, runs 200 and 201),
so 0.7.1 was built from the pre-audit rules. Observable in this
release: the rule that derived `owl:sameAs` between named classes
from `owl:equivalentClass` is removed, datatype-range clashes are
decided by XSD value-space disjointness (`xsd_value_spaces_disjoint`),
and the direct-mapping filter also excludes the built-in OWL annotation
properties, not only declared ones. The npm-publish workflow re-extracts and refuses drift,
so this correction is a precondition of the release.

## 0.7.1 — 2026-09-06

`factoidal pack --batch-bytes N` was documented in 0.7.0 and refused by the
option parser ("usage" exit 2): the value-option table for `pack` did not
list it. It is accepted now, and `tests/store-host/cli.mjs` packs with it.
No engine change; the wasm module is 0.7.0's.

## 0.7.0 — 2026-09-05

**Wire version 10.** The command and `bin/store.mjs` read a generation
packed at `--layout ibk5`: out-of-line literals, RDF 1.2 triple terms and
directional literals, and per-entry zone maps.

### The packer

`factoidal pack --layout ibk5` writes wire version 10. Blocks are now
published DURING the ingest pass, every `--batch-bytes` of source (default
64 MiB in the module, 256 MiB in the native tool), so peak memory is bounded
by a batch and not by the source: the native packer's peak on the
1,543,478,120-byte skosdex corpus fell from 5,951,730,560 to 396,869,632
bytes, and the module's 128 MiB source cap is gone for N-Quads, Turtle and
N-Triples (TriG still buffers). Rows are bucketed by predicate AND graph, so
an N-Quads file whose graphs interleave line by line packs to the same
block set as the same statements in graph order (measured: 11,636 blocks
became 483). The literal search index is LGI2, whose LEB128 gaps are 23% of
a `skos:prefLabel` block against LGI1's 54%; a version-10 generation of the
210 MB skosdex prefix is 14.5% smaller than version 9.

### Out-of-line literals

A literal above 65,536 UTF-8 bytes is stored as one `blob-<sha256
hex>.lit` file beside the block, committed by the manifest blob table.
The block holds only the byte extent and the digest, so a host must fetch
the blob as well as the block:

- `storeQueryPlan` lists them under `blobKeys`, after `keys` and
  `sidecarKeys`, and counts their bytes in `bytes`;
- `queryStore` and `openStoreHandle` fetch them without a flag;
- a blob that is absent or whose bytes hash differently REFUSES the
  query by name. Nothing is answered with a shortened literal.

A store handle resolves every blob ONCE, at `storeOpen`, and the open
envelope reports how many. The two candidate-filter indexes keep an
out-of-line literal in every candidate set, so `CONTAINS` over a
70,000-byte literal and `geof:sfIntersects` over a polygon above the
ceiling both answer their rows.

### RDF 1.2 terms

A triple term and a directional language literal are stored and read
back. Wire version 9 refuses both.

### Zone maps

Each manifest entry carries the first 64 bytes of the smallest and the
largest subject key and object key of its block. A query with a constant
subject or object skips every block whose range cannot hold it, from the
manifest alone. `storeQueryPlan` reports the count as `zoneExcluded`, and
`factoidal inspect` prints the bounds beside each entry.

### Unchanged

Wire version 9 and earlier answer exactly what they answered before: no
manifest below version 10 carries a blob table or a zone map, so
`blobKeys` is empty and `zoneExcluded` is zero for them.

## 0.6.0 — 2026-09-05

**A full-text index, a geometry index, extension functions from
JavaScript, and a planner that no longer reads the whole store for a
`REGEX`.** Measured end to end on the largest corpus we have: 7,315,251
quads over 204 named graphs, 3,286 blocks, a 1.0 GB generation, queried
through a store handle on plain `node` with no flags.

| search | rows | time |
|---|---|---|
| `water` | 5 | 645 ms |
| `glacier` | **0** | 670 ms |
| `bicycle` | 2 | 617 ms |

A miss costs what a hit costs, because both are index lookups.

### The planner stopped reading the whole store

`REGEX`, `REPLACE`, `IRI()`, `NOW()`, the digest functions, aggregates in
a filter position, the triple-term accessors and every SPARQL 1.1
section 17.6 extension call each made the planner abandon predicate
selection and take every block in the manifest. On a 119-block store a
`REGEX` filter selected 119 artifacts where the same query with
`CONTAINS` selected 1.

The test was `Expr.backendLocal`, which answers a different question: may
the backend evaluate this expression, or must it materialise and
delegate. The right test is `Expr.existsFree` — `Expr.existsPat` and
`Expr.notExistsPat` are the only constructors carrying a pattern, so an
exists-free expression reads no triple whatever functions it calls. A
FILTER may narrow a plan or leave it alone; it must never widen it.
`EXISTS` and `NOT EXISTS` still widen, correctly.

### LGI1, a character-gram literal index

The packer writes a `.lgi1` sidecar beside each block and the planner
uses it where the query shape allows. It holds character 3-grams of the
case-folded lexical form and is a CANDIDATE FILTER, never a decider: it
answers a superset and the engine re-evaluates the original `FILTER`, so
the rows are the scan's rows. Tokens would not do, because `CONTAINS` is
a substring test and "underwater" contains "water" without being the
token "water".

Falls back to a scan, silently and correctly: a needle under 3
characters, a variable needle, `REGEX`, `UCASE`, `!CONTAINS`, `CONTAINS`
under `||`, a filter on a variable not bound in object position, and any
generation without the sidecar. Costs about 55% of the block bytes.

### GBI1, a geometry bounding-box index

The same construction for `geof:`. Five of the six topological functions
are filtered by a box — `sfIntersects`, `sfWithin`, `sfContains`,
`sfTouches`, `sfEquals` — at 74 to 94 times a scan, with a miss at 82
times. **`sfDisjoint` is refused** and falls back: it accepts exactly the
rows a box can exclude, so a box test inverts and would drop answers.

### Extension functions, from JavaScript, on the Lean engine

`registerExtensionFunction` reaches the Lean engine and the persisted
store, not only the in-memory F* path. Section 17.6 semantics are gated:
an unregistered IRI is unbound in SELECT and drops the row in FILTER, a
registration never overrides a built-in family, and `geof:` still
answers from the built-in table. Synchronous only; async is designed and
deferred.

### A handle is bounded by retained bytes

`storeOpen` was capped at 64 artifacts, inherited from the stateless path
where every query re-read and re-decoded its blocks. A handle pays that
once, so a count was the wrong shape — 257 small blocks may cost less
than 4 large ones. The cap is now 134,217,728 retained bytes, derived
from a measured 16.2 bytes resident per retained byte against half the
wasm32 address space, and the check runs BEFORE the read rather than
after hashing and decoding the whole set. A corpus-wide handle over 257
blocks and 741,179 rows now opens.

### Named graphs pack at scale

Blocks cut at graph boundaries, so `GRAPH <iri>` with a constant
predicate reads one block and the graph filter is exact rather than
conservative. Packer peak memory fell 32.6% and dictionary duplication
is 2.57%. No new wire version was needed: SBM7 already admitted several
entries per predicate.

**A large store no longer needs `node --stack-size`.** Several engine
paths recurse once per manifest entry and once per row, and on a
7,315,251-quad collection of 3,286 blocks `storeQueryPlan` alone
overflowed the default call stack of Node, before an artifact byte was
read ([issue 653](https://github.com/danbri/factoidal/issues/653)).

- New `@factoidal/core/store-worker`: `openStoreHandleOnWorker` holds the
  engine and the handle on a `worker_threads` thread with a raised stack.
  A handle is state inside the wasm instance and an instance does not
  cross a thread boundary, so the handle lives there and `query()` and
  `close()` are messages to it. One thread per session, many handles per
  thread. Every call is asynchronous; the synchronous `openStoreHandle`
  is unchanged.
- `factoidal query` still runs IN PROCESS, so a one-shot query pays
  nothing for a worker it would drop. It runs again on a worker only when
  the runtime runs out of frames — under Deno by re-executing itself with
  a raised V8 stack, which needs `--allow-run` and `--allow-env`.
  `--no-worker` turns the retry off.
- Measured: the worker costs about 110 ms once (thread start plus a
  second engine load) and under a millisecond per query after that.
  Deno's `worker_threads` shim does not raise the stack (10,835 frames
  by default, 13,837 at `stackSizeMb` 64, against Node's 41,195 and
  696,555), so a Deno library caller gets an in-process handle behind the
  same interface and starts its process with
  `--v8-flags=--stack-size=65536`.

### Fixed

- `openStoreHandle` with no options failed on any IBK3 generation with
  `artifact 'predicate-0.ibk3.sri2' is not declared by this manifest`.
  Two engine operations disagreed: `storeManifestInspect` reports
  `subjectIndex`, `termIndex` and `objectIndex`, while the handle's
  admission accepted only the block, `literalIndex` and `geoIndex`. One
  list now serves both.
- The README named GeoSPARQL functions that do not exist and said a text
  index was "separate work". Both corrected, with the shapes that fall
  back to a scan listed.

### Known limits, measured

- Ingest is about 2,180 quads per second and peak memory is 2.07 times
  the source, so a 142 GB corpus is not importable at that ratio. Making
  memory flat is a wire change and is not done.
- The quad packer streams N-Quads only; Turtle and TriG are buffered.
- `ORDER BY ... LIMIT n` still overflows above about 14,576 materialised
  rows. https://github.com/danbri/factoidal/issues/653
- The manifest is at version 9. Older generations still read.

## 0.5.1 — 2026-09-04

**A store can be opened once and queried many times.** `storeQuery` is
stateless: it re-reads, re-verifies and re-decodes the block on every
call, so a chat bot or a server paid the full cost for every question.
The new handle pays it once.

Measured on a 141-graph store, `skos:prefLabel` block of 5,571,302 bytes
and 45,806 rows, a DIFFERENT search string every query, load 10:

| | stateless | handle |
|---|---|---|
| first query (open + query) | 1,376 ms | 1,363 ms |
| second query, different string | 1,376 ms | **95 ms** |
| tenth query, all different | 1,382 ms | 103 ms |
| ten queries, total | 13,962 ms | **2,277 ms** |

```js
import { openStoreHandle } from '@factoidal/core/store'
import { loadEngine } from '@factoidal/core/engine'
const engine = await loadEngine()
const store  = await openStoreHandle(engine, '/path/to/store')
const a = store.query('PREFIX skos: … SELECT … ')   //  95 ms
const b = store.query('PREFIX skos: … SELECT … ')   //  95 ms
store.close()
```

**What it buys**: the per-query SHA-256 verification, block decode,
dataset build and index build all happen once. **What it does not buy**:
`CONTAINS` still scans every retained row, so cost stays proportional to
row count. This is not a search fix. There is still no inverted index.

⚠️ **Memory.** A held-open handle is about 170 MiB resident, of which
roughly 94 MiB is the decoded form of that 5.5 MB packed block — about
17 times the packed size. Query evaluation peaks at 346 MiB. A process
holding several stores should watch this; `storeHandleList` reports each
handle's retained bytes and rows.

**For a long-lived process**: several stores may be open at once, keyed
independently. `storeOpen` REFUSES at its cap and never evicts another
caller's handle — an eviction policy is a host decision and is not
implemented. The WebAssembly module is single-threaded, so a host must
queue overlapping calls; use one module instance per worker thread for
concurrency. A server would still need a re-open path when a generation
is replaced on disk, and delta-log overlay support: this path serves the
manifest's committed artifacts only.

Handle answers are gated against the stateless path by comparing ROWS,
not row counts, in `tools/wasm-store-query-smoke.sh` and
`Wasm/native-smoke.sh` (85 pass, 0 fail, out of 85; was 79).

## 0.5.0 — 2026-09-04

**Queries against a persisted store are about six times faster.** Measured
end to end the way a caller runs them — process start, engine load,
digest verification, block decode and scan — on a 141-graph store with a
5,571,302-byte `skos:prefLabel` block of 45,806 rows, at the same machine
load:

| query | 0.4.0 | 0.5.0 |
|---|---|---|
| `CONTAINS` over labels, `LIMIT 8` | 12.03 s | **2.06 s** |
| the same for a second word | 12.18 s | **2.04 s** |
| the same for a third | 11.96 s | **2.02 s** |

Two causes, both fixed.

- **A quadratic byte copy in SHA-256.** `Crypto.processBlocks256` copied
  the whole remaining message once per 64-byte block, so verifying an
  artifact was quadratic in its size. Fitting `t = c*n^k` to the
  admission step gave k = 2.08 before and **k = 0.98 after**. On the
  three blocks of that store, admission went 1,179 / 2,150 / 11,069 ms to
  303 / 413 / 872 ms. Decode and evaluation were linear throughout.
- **`LIMIT` was not pushed down through `GRAPH`.** A `LIMIT 8` cost what
  a full count cost, because `GRAPH ?g { ... }` fell through to the
  reference evaluator over the whole materialised dataset. The push-down
  now takes one `GRAPH` layer with a constant IRI or a variable.
  `ORDER BY`, `OFFSET`, `DISTINCT`, `REDUCED`, `GROUP BY`, `HAVING`,
  `VALUES` and aggregates still reject, two of them pinned by theorems.
- A `RangeError: Maximum call stack size exceeded` on `SELECT ... LIMIT 8`
  is gone with it, because the query no longer materialises 45,806 rows
  to return eight.

**A correctness fix found while measuring.** The pre-existing bare-BGP
`LIMIT` push-down could answer SHORT: a repeated variable (`?x ?p ?x`) or
an RDF-star triple term let the backend stop early on rows the match then
rejected. It now refuses both shapes.

**New exports.** `@factoidal/core/store`, `/pack` and `/engine`. A caller
can drive the store in process instead of spawning the command:

```js
import { openStore, queryStore } from '@factoidal/core/store'
import { loadEngine } from '@factoidal/core/engine'
const engine = await loadEngine()
const store  = openStore('/path/to/store', null)
const { result } = queryStore(engine, store, 'PREFIX skos: ... SELECT ...')
```

**The engine carries a day of OWL work**: OWL RL 1,181 pass, 266 fail
(out of 1,457) and OWL DL about 1,326 pass, 121 fail (out of 1,457), both
against a conclusion check corrected to require one functional blank-node
mapping (RDF 1.1 Semantics §1.5 and the interpolation lemma). A false
clash was removed — the materialiser had minted one existential witness
for several obligations, so the engine denied three consistent
ontologies; ConsistencyTest went 758 pass, 4 fail to 761 pass, 1 fail.

**Named graphs now pack at scale.** The IBK4 quad path read the whole
source file and a 553 MB, 194-graph corpus could not be packed at all. It
streams now, and a quadratic term that only named graphs paid — a hash
map copied per quad in `addQuadFast` — is gone. Peak memory per source
byte fell from 37 and 20 to between 7.4 and 11.4; a 316,816,934-byte,
194-graph input that used to fail now packs in 750 s at 2.34 GB. Byte
identity with the previous packer holds by theorem, not only by diff.

**Documentation corrected.** The GeoSPARQL section named functions that
do not exist. Six topological functions are implemented — `geof:sfEquals`,
`sfDisjoint`, `sfIntersects`, `sfTouches`, `sfWithin`, `sfContains` — and
they work against a persisted store, verified. There is no
`geof:distance`, `buffer`, `envelope`, `boundary`, `convexHull`, no
`relate` with a DE-9IM matrix, no CRS handling beyond the WKT literal and
no GML. Full text is SPARQL 1.1's own `CONTAINS` / `STRSTARTS` / `REGEX`,
evaluated per row after a block decodes: **there is no inverted index**.

Known limits, measured:

- A query is still O(rows) per search string, and nothing is retained
  between queries: `storeQuery` re-reads, re-verifies and re-decodes the
  block every call. A store handle that decodes once is the next step.
- `ORDER BY ... LIMIT n` still overflows the call stack above about
  14,576 materialised rows.
  https://github.com/danbri/factoidal/issues/653
- `update` and `compact` still exit 3.
  https://github.com/danbri/factoidal/issues/641
- A query plan is refused above 64 artifacts, 8,388,608 blob bytes or
  100,000 rows. https://github.com/danbri/factoidal/issues/648
- The two SHA-256 folds are checked equal by the FIPS 180-4 build-time
  guards and the HACL* differential, not proved.

## 0.4.0 — 2026-09-04

The package builds a store of its own. `pack` and `activate` join
`inspect` and `query`, so `npm install @factoidal/core` gives a complete
RDF store — import, activate, query — with no native binary on the
machine. https://github.com/danbri/factoidal/issues/641

- **`factoidal pack INPUT OUTPUT`** builds one immutable Shardborough
  generation from a Turtle, TriG, N-Triples or N-Quads file, streaming
  it in 65,536-byte chunks through the Lean engine's WebAssembly module.
  The generation is BYTE-IDENTICAL to what the native
  `l4block-shard-pack` writes: `diff -r` is empty for the `ibk3` triple
  layout and for the `ibk4` quad layout, on inputs up to 888,949
  triples. `--layout ibk3|ibk4`, `--syntax`, `--base`.
- **`factoidal activate STORE GENERATION`** verifies every artifact
  against the SHA-256 the manifest commits, and every cross-artifact
  relation, then replaces `CURRENT` atomically. A generation that fails
  verification never becomes current.
- **`factoidal sample-store`** prints the path of a store this package
  now carries, so a fresh install answers a SPARQL query with nothing
  else to download: 4,434 triples in 13 predicate blocks, five IPTC
  NewsCodes vocabularies under CC BY 4.0. Also exported as
  `@factoidal/core/sample-store`. See NOTICE.
- The engine gained a raw byte path out of the module
  (`l4_call_blob_io`), so artifact bytes cross the boundary with no
  encoding. Hexadecimal doubled them; base64 was refused. Measured on
  the read path: 242,416 bytes and 96 ms hexadecimal against 4,893 bytes
  and 70 ms raw.
- The pack hashes with HACL* SHA-256, the same primitive the native
  packer uses. It hashed with the pure Lean SHA-256 in development,
  which cost 3.3 times: 104 s against 31 s on 888,949 triples. Now at
  parity, 29.24 s against the native packer's 29.38 s.
- `packBegin` takes a base IRI, defaulted by the command to
  `file://<input>` so relative IRIs resolve exactly as the native packer
  resolves them. `--base ''` asks for no base, which makes a relative
  IRI a parse error rather than a silently different term.
- `pack` on a syntax the streaming fold cannot read now says so by name
  rather than raising an unhandled error.
- `store-host` gained `readChunk` (a short read means end of file, not
  an error), `writeNew` (create and fsync, refusing an existing file so
  a name collision in a generation is reported) and `makeDirectory`, on
  Node and on Deno both.
- `factoidal activate` runs on the raised stack too. Verification decodes
  the same blocks the pack encoded, so it recurses as deep; the worker was
  given to `pack` alone at first, and a 112,742-row generation packed
  successfully and then failed to activate with `Maximum call stack size
  exceeded`, leaving a store that could be built and not opened. Found by
  installing the tarball and running the command, which is why that step
  is in the release procedure. `tests/store-host/cli.mjs` now gates
  pack-then-activate on both runtimes.
- `factoidal pack` no longer needs a runtime flag. The pack fold recurses
  deeper than either runtime's default call stack allows, so an input
  above roughly 0.5 MB ended with `Maximum call stack size exceeded`
  (https://github.com/danbri/factoidal/issues/649). Under Node the pack
  now runs on a `worker_threads` worker with a 64 MiB stack; under Deno
  the command re-executes itself once with
  `--v8-flags=--stack-size=65536`, which needs `--allow-run` and
  `--allow-env` in addition to `--allow-read` and `--allow-write`.
  `gene.ttl`, 17,363,312 bytes and 888,949 triples, packs on the default
  stack of both runtimes, byte-identical to `l4block-shard-pack`.
  `--no-worker` forces the in-process path, which still reports the
  frame budget and the flag that raises it rather than crashing. A
  browser tab has a fixed frame budget and no flag, so this does not
  make an in-page packer possible.

Known limits, measured:

- `update` and `compact` still exit 3. The delta-log operations are
  stage 4 of https://github.com/danbri/factoidal/issues/641.
- The `ibk4` quad layout reads the whole source rather than streaming,
  because a quad block commits a graph-set summary over the entire
  input. The wasm packer refuses a quad file above 128 MiB.
  https://github.com/danbri/factoidal/issues/650
- A query plan is refused above 64 artifacts, 8,388,608 blob bytes or
  100,000 rows. https://github.com/danbri/factoidal/issues/648
- Packing in a browser tab is limited to about 7,800 distinct terms in
  one block, whatever the file size, and no host flag raises it.
  https://github.com/danbri/factoidal/issues/647

## 0.3.0 — 2026-09-03

- The `factoidal` command answers SPARQL against a persisted
  Shardborough store with no native binary. `factoidal inspect STORE`
  decodes the manifest through the engine's `storeManifestInspect`
  operation and prints the wire version, layout, blank-node profile and
  the entry table; `factoidal query STORE 'SELECT ...'` asks the engine
  which artifacts the query needs, reads exactly those, and hands their
  bytes to `storeQuery` through one WebAssembly heap buffer with no
  encoding. Every artifact is verified against the SHA-256 the manifest
  commits before an answer is given. Formats: `table`, `json`,
  `nquads`, `turtle`; `--explain` prints the artifact plan. Runs under
  Node and under Deno (`--allow-read`).
- The three caps of the store query operation — 64 artifacts, 8388608
  artifact bytes, 100000 rows — are reported with the cap, the value
  and a next step, and are decided before a single file is read.
  Nothing is truncated.
- `pack`, `activate`, `update` and `compact` still exit 3; they need
  operations that do not exist yet
  (https://github.com/danbri/factoidal/issues/641).
- A large piped result is no longer truncated: the command sets
  `process.exitCode` instead of calling `process.exit()`, which dropped
  everything past the 64 KiB pipe boundary.

## 0.3.0 — Lean block-worker preview

- The bundled Lean-derived WASM artifact exports
  `scanIBK2Predicate(ibk2Hex, predicateIri)` through `factoidal/l4`.
  It validates a canonical IBK2 block and executes its selective predicate
  scan, returning N-Triples plus a row count.  This is a narrow physical
  helper for the Shardborough work, not full SPARQL execution inside a storage
  backend and not a high-throughput buffer ABI (the current hex transport is
  intentionally diagnostic).
- The regenerated Lean artifact is synchronized across the package's
  `l4-assets/` and the Hub build, and is exercised against the music IBK2
  fixture by `tools/wasm-ibk2-smoke.mjs` in the repository.
- The current-format companion
  `scanIBK3Predicate(ibk3Hex, predicateIri, blankNodeScope)` validates and
  scans complete predicate-local IBK3 artifacts. Its mandatory source/dataset
  scope preserves one blank node across blocks from the same RDF import while
  keeping same-spelled labels in unrelated inputs apart. Hub post 51 composes
  three real IBK3 scans into an editable Lean-WASM SPARQL query.

## 0.2.0 — both engines in one package, with a backend selector

- The Lean 4 engine (`L4Factoidal`, wasm) now ships INSIDE
  `@factoidal/core` as `l4-assets/`, alongside the F\*-extracted
  engine. One install gets both. `require('factoidal/l4')` and
  `factoidal/l4-core` are unchanged; the resolver checks in-package
  assets first, then falls through to the old order (companion
  package, `$FACTOIDAL_L4_ASSETS`, repo checkout).
- `@factoidal/lean` is superseded and was never published.
- New subpath `factoidal/select`: a backend selector, per-instance
  with per-call override. Values `lean`, `fstar`, `lean1st`,
  `fstar1st`, `slowcompareboth`. A request naming exactly one engine
  never gets an answer from the other -- `lean` and `fstar` throw on a
  function that engine does not implement; `lean1st` / `fstar1st` fall
  through, and `lean1st` also takes a list of functions to route to
  F\* regardless. Every result carries the answering engine.
  `slowcompareboth` runs both and REPORTS disagreement rather than
  throwing; comparison is RDFC-1.0 isomorphism for Dataset-shaped
  results and bag equality (blank nodes relabelled per side) for
  SELECT bindings.
- Measured on the typed API surface at this release: 15 functions both
  engines answer, 38 F\*-only, 4 Lean-only (out of 57). This measures
  the typed wrapper surface, not the Lean engine's total capability --
  `l4-core.js` wires 16 of the engine's 21 dispatch ops.
- `clParse` (Common Logic Interchange Format text, ISO/IEC 24707:2018,
  with the IKL `that`-operator extension) is now wired into the typed
  API -- `l4-core.js`/`lib/api.js`/`select.js`, with `.d.ts` types and
  tests. It reads CLIF text and reports its shape (sentence count,
  `pureCL` dialect flag, canonical re-serialisation); it never produces
  RDF. `pureCL` is a DIALECT flag, not a validity or quality signal:
  true while the text stays inside ISO/IEC 24707 Common Logic, false
  once it uses IKL's `that` operator. It is the first Lean-only entry
  on the typed capability table -- formal/fstar has no CL/IKL parser at
  all, so `index.js`/`wasm.js` never export it, `factoidal/select`'s
  `backend:'fstar'` throws for it (never falls back to Lean), and
  `backend:'slowcompareboth'` fails the capability precondition rather
  than comparing one side against nothing.
- `clSerialize`, `clAlphaNorm` and `clNormalize` join `clParse` on the
  same Lean-only typed surface (owner instruction, 2026-08-26 -- "wire
  into js functional api"), same `.d.ts`-typed, test-covered pattern:
  `clSerialize` reads CLIF text and writes it back in canonical
  spacing, surfacing `roundTripProved: false` unmodified (the
  round-trip lemma `clif_roundTrip`, `CL/ClifAdequacy.lean`, is OPEN --
  the fragment boundary `marksLexable` is measured, not proved).
  `clAlphaNorm` gives each sentence's bound-variable-renaming canonical
  form (IKL GUIDE Appendix B condition (1)). `clNormalize` is Hayes's
  satisfiability-preserving reduction of IKL to Common Logic
  ([#625](https://github.com/danbri/factoidal/issues/625)): it
  surfaces `preserves: "satisfiability"` (not equivalence -- suited to
  entailment/consistency testing, not to transforming data you intend
  to keep) and `noIntrusion` (the proof hypothesis `CL.noIntrSs [] []`
  decides, not a paraphrase of it). `clFiniteSat`, the fifth CL/IKL op,
  is DEFERRED rather than wired: it takes a caller-supplied finite-
  interpretation JSON encoding with no user yet, and a typed wrapper
  would freeze that shape before it is known to be right; it stays
  reachable through the raw dispatch ABI.
- The IKL-to-RDF projection ops (`clToDataset`, `queryWithIklService`)
  are DELETED from the engine source (danbri/factoidal#626), along with
  the content-addressed proposition graph names they minted. They were
  never exposed through the npm API. `x-ikl-*` entailment regimes are
  still rejected at the JS layer, and the engine no longer defines the
  family either. The two ops remain present in the compiled wasm
  artifact until it is rebuilt (danbri/factoidal#627) -- the artifact
  is ahead of its source. `clParse` is a different op (it never
  produces RDF) and is unaffected.

## 0.2.0 — Lean 4 engine subpath

- New `factoidal/l4-core` subpath: the same typed API served by the
  Lean 4-extracted wasm engine instead of the F\*-extracted one
  ([#476](https://github.com/danbri/factoidal/issues/476)). Engine
  assets resolve from the `@factoidal/lean` companion package, the
  `FACTOIDAL_L4_ASSETS` environment variable, or the repository
  checkout, in that order. `capabilities()` reports the Lean engine's
  actual surface; `shaclValidate`/`owlIsConsistent`/`owlEntails`
  raise pinned errors rather than returning wrong answers
  ([#586](https://github.com/danbri/factoidal/issues/586) tracks the
  OWL verdicts).
- `serialize({ format: "nquads" })` now normalizes through the entry
  ABI instead of the CLI path.


## 0.1.0 — First published release (as `@factoidal/core`)

- SPARQL 1.1 §17.6 extension functions
  ([#463](https://github.com/danbri/factoidal/issues/463)),
  Comunica-style: `registerExtensionFunction(iri, fn)` /
  `unregisterExtensionFunction(iri)` / `clearExtensionFunctions()`.
  `fn` may be sync or async; it receives the evaluated arguments as
  SRJ-style term objects and returns a term object, a JS primitive,
  or a Promise of either. Dispatch semantics are F*-specified
  (SPARQL11.Algebra.fst's E_FunctionCall arm consults the registry
  LAST; an unregistered IRI is the spec-required error — unbound in
  SELECT/BIND position, row dropped in FILTER position). Async
  functions run over the synchronous extracted engine via a bounded
  memoised re-evaluation trampoline in `lib/api.js`.

- Final name: `@factoidal/core`, published under the `@factoidal` npm
  org (owner decision, 2026-08-22). Everything under "Unreleased"
  below ships in this first cut. The `private` flag and the
  publish-blocking `prepublishOnly` guard are removed; `prepublishOnly`
  now runs the package test suite instead.
- The wasm bundle (`factoidal.wasm.js` + assets) is rebuilt in sync
  with the js bundle. The previous in-tree wasm build predated the
  2026-08-15 COTTAS UTF-8 writer fix (issue #445) and its
  format-compatibility gate rejected stores written by the current js
  bundle (caught by the wasm/js parity test in `test/`).

## Between 0.1.0-alpha.0 and 0.1.0 — unpublished

- Package renamed from the placeholder `@danbri/foafos` to `factoidal`
  (issue #403). The package was never published under the old name, so
  there is no npm-registry alias or deprecation notice to add -- this
  is a rename of unpublished scaffolding, not a breaking change to a
  released package.
- `coreRdfsClosure`/`coreRdfsCheck`/`rhoDfClosure`/`rhoDfFragmentCheck`/
  `rdfsPlusClosure`/`owlIsConsistent`/`owlEntails` now exported from
  `factoidal/wasm` (previously js_of_ocaml-only); `coreRdfsClosure`/
  `coreRdfsCheck`/`rhoDfClosure`/`rhoDfFragmentCheck`/`rdfsPlusClosure`
  added to `factoidal/fn` (FnDataset-returning wrappers around the
  certified ρdf closure family; `owlIsConsistent`/`owlEntails` were
  already there). No new engine logic -- these functions were already
  wired into the npm-entry ABI (`bin/npm-entry/entry_jsoo.ml`) and
  `lib/api.js`'s `buildApi()`; this closes a wrapper-surface gap
  between `index.js`/`browser.js` (which had them) and `wasm.js`/
  `fn.js` (which didn't). See docs/theorem-registry.md for
  `rho_df_closure`'s decides-iff guarantee.
- `version.json` gains a machine-readable `claims` block (issue #403's
  G2 item): a summary of theorem-backed guarantees, each entry naming
  the exact F* theorem, its file, and the docs/theorem-registry.md
  section to check it against -- never a bare assertion. `build-
  ocaml.sh npm` now preserves this block across rebuilds.
- Browser-side durable-UPDATE persistence (issue #282): `browser.js`
  gains `deltaLogOpen`/`deltaLogAppend`/`deltaLogReadAllHex`/
  `deltaLogMerge`/`deltaLogDestroy` (IndexedDB-backed, survives page
  reloads and browser restarts), plus `deltaBatchToHex`/
  `deltaMergeApplyBrowser` on the npm-entry ABI. Every byte moved is
  produced/consumed by the F*-verified `RDF_Store_Columnar_DeltaLog`/
  `RDF_Store_Columnar_DeltaMerge` modules the native on-disk delta log
  (`factoidal serve --rw --delta-log`) uses -- see
  `docs/designissues/2026-07-06-browser-persistence.md` for the v1
  architecture decision (IndexedDB vs. OPFS), the crash/reload
  guarantee mapping, and the quota/eviction honesty section. Prototype
  scope: no compaction, no `navigator.storage.persist()` wiring yet
  (both named as staged next steps); supported update ops are
  `INSERT DATA`/`DELETE DATA`/`CLEAR`/`DROP`/`CREATE`, same subset the
  native `--rw` path accepts.
- CSVW csv2rdf (`csvwToRdf`) added to the npm-entry ABI, the typed API
  (`index.js`/`wasm.js`), and the functional API (`factoidal/fn`:
  `fromCsvw`): raw CSV text + an optional CSVW metadata document
  (tabular-metadata JSON; omitted = schema inferred from the header
  row) to a Dataset, in `standard` (csvw:TableGroup/Table/Row wrapper)
  or `minimal` (bare cell triples) mode. `capabilities()` gained a
  matching `csvw` probe. Engine modules: `CSVW.Metadata.fst` /
  `CSVW.URITemplate.fst` / `CSVW.Conversion.fst` (measured against the
  vendored W3C csv2rdf suite -- see the CSVW program plan's stage
  table for coverage and known gaps: datatype `format` facets,
  list-valued cells, and full inherited-property propagation are not
  yet implemented).
- SHACL Core (`shaclValidate`), ShEx (`shexValidate`), RDFS/OWL-RL
  closure (`owlClosure`), RML (`rmlMap`), and RIF Core
  (`rifEval`) added to the npm-entry ABI and the typed API
  (`index.js`/`wasm.js`) and the functional API (`factoidal/fn`:
  `validate`/`shex`/`fromMapping`/`rif`). `jsonldToRdf` exposes
  JSON-LD-specific options (`base`/`rdfDirection`/`expandContext`/
  `processingMode`); plain `parse(text, {format:'jsonld'})` through
  the npm-entry bundle also now works (previously an unhandled
  format-dispatch case). `capabilities()` gained matching
  `shacl`/`shex`/`owlClosure`/`rml`/`jsonld`/`rif` probes.
- Typed public API: `parse` -> RDF/JS `Dataset`, `query` ->
  `Bindings[]` (Maps of variable -> RDF/JS term) | boolean | Dataset,
  `update`, `serialize`, `canonicalize` (RDFC-1.0), `capabilities`.
- RDF/JS data model (`rdfjs.js`): spec-compliant DataFactory + terms
  with `.equals()`, DatasetCore `Dataset`, converters to/from the
  engine's N-Quads interchange text. Exported as `factoidal/rdfjs`.
- `factoidal/wasm`: same API on the wasm_of_ocaml engine (Node >= 22).
- npm-entry ABI consumer (`bin/npm-entry/entry_jsoo.ml` in the repo):
  persistent string/JSON ABI enabling CONSTRUCT, UPDATE and
  canonicalize; the API falls back to argv-driving the CLI bundle
  until that bundle is built and staged.
- Rewritten `index.d.ts` with self-contained RDF/JS typings; the old
  SRJ-shaped `query()` lives on as `queryRaw()`.
- `node:test` unit suite (`npm test`); entry-dependent tests skip with
  reason "pending npm-entry build".

## 0.1.0-alpha.0 — Initial scaffold, unpublished

Directory layout committed to the main repo under `npm/factoidal/`.
Not yet published to the npm registry.

- `package.json` with dual CJS (`index.js`) / ESM (`index.mjs`)
  entry points, a `browser` condition, and a TypeScript declaration
  file (`index.d.ts`).
- `index.js` wraps the js_of_ocaml-compiled `factoidal.js` bundle in
  an `async` `query(data, query, options)` API with `dataFormat`,
  `entail`, and `output` options.
- `browser.js` mirrors the same API for browsers, fetching
  `factoidal.js` via `fetch()` relative to the module URL.
- `build-ocaml.sh npm` target (in the repo root's
  `formal/fstar/build-ocaml.sh`) populates this directory from the
  existing extraction output.
