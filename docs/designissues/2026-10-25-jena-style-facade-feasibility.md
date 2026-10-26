# Feasibility: a Jena-style JavaScript API over the Factoidal wasm ("@factoidal/echochamber")

Date: 2026-10-25. Status: feasibility study, for owner review. No facade code exists.
Tracking: https://github.com/danbri/factoidal/issues/1036 (SPARQL string-function defects found by this study).

Request (owner, 2026-10-25, verbatim): "Have a subagent assess feasibility of
creating a js reflection of eg Jena's APIs and then ai-manually converting their
test suite to see if we can create a Jena experience over WASM. The NPM ideally
would be different eg @Factoidal/echochamber".

Inputs:

- Apache Jena at commit `a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98`
  (2026-10-25), shallow clone (`git clone --depth 1 https://github.com/apache/jena`).
- factoidal-core at `3af3a4753` (2026-10-25), with the wasm in
  `npm/factoidal/l4-assets/` (16,918,397 bytes; `@factoidal/core` 0.15.0).
- Scripts and raw outputs:
  `tools/jena-facade-study/` (`count.sh`, `tcount.py`, `classify.py`, `api.py`, `ops.mjs`, `probe.mjs`,
  `conv/extract.py`, `conv/run-expr.mjs`, `conv/sample-port.test.mjs`, and the
  `.txt`/`.json` results, which the scripts regenerate and which are not committed).

## 1. Result

1. Feasible for the core of Jena (Model, Graph, Statement, RIOT read and write,
   ARQ query and update, SHACL, ShEx). The engine has most of the semantics now.
   The wasm (measured) lists 183 ops. The dataset-handle ops (`datasetOpen`,
   `datasetMatch`, `datasetAddQuads`, `datasetDeleteQuads`, `datasetQuery`,
   `datasetUpdate`, `datasetIsomorphic`, `datasetSerializeWith`, ...) are
   synchronous calls after load, so a synchronous Java-shaped API is possible.
2. A Jena "experience" is not a renaming of `@factoidal/core`. Jena's Model API
   carries semantics that Factoidal does not have today. Each needs a Lean op
   first (iron rules 1, 2, 7; anti-pattern 36). The largest: value-based
   matching in `Model.contains`, the Java-value-to-literal mapping
   (`createTypedLiteral(99)`), literal value accessors (`getInt`, `getValue`),
   query substitution, syntax-from-file-name, and the Jena rule language.
3. The test conversion found engine defects in the first hour. A mechanical
   port of 477 one-line ARQ expression tests to SPARQL ASK queries gave 274
   pass, 157 fail, 46 parse error (out of 477), measured. About 42 of the fails
   are Factoidal accepting arguments that SPARQL 1.1 §17.4.3.1.4 (argument
   compatibility) and §17.4.6 (hash functions) require to raise a type error,
   for example `md5(1234)` and `contains('abc', 'a'@en)`, and
   `substr('12345', 0, 3)` gives `"123"` where `fn:substring` gives `"12"`.
   No W3C manifest test caught these. This alone justifies porting the
   expression tests, independent of the facade.
4. Of 11,334 Jena test method declarations in jena-core, jena-arq, jena-shacl
   and jena-shex (measured), about 6,842 are API-level tests a conversion would
   port, 2,884 test JVM or engine internals, and 460 are manifest runners whose
   W3C suites Factoidal already runs directly. Classification is by package
   path (coarse, Claude-inferred).
5. No wasm rebuild is needed to start stage 1 with a reduced API. Every new
   Lean op listed in section 6 needs a rebuild by `danbri/factoidal-builds`.
6. Licence: possible under Apache-2.0 with NOTICE and per-file change notes.
   The name "Jena" must not be in the package name or product branding (ASF
   trademark policy). "echochamber" is acceptable.

## 2. Jena API surface (question 1)

### 2.1 Per module (measured)

Method: `count.sh` — files under `src/main/java`; "public types" counts lines
that start `public class|interface|enum|record`; "public methods" counts
indented lines `public ... (` (a regular-expression count, so it includes
constructors and misses methods in interfaces that omit `public`; read it as
an order of magnitude).

| Module | main files | public types | public methods (regex) | Factoidal relation |
|---|---|---|---|---|
| jena-core | 797 | 754 | 6,105 | Model/Graph: partly covered (handles); reasoners: partly |
| jena-arq | 1,752 | 1,667 | 13,821 | query/update/RIOT: covered; Java expression API: no |
| jena-shacl | 160 | 159 | 826 | covered (`shaclValidate`, `datasetShaclValidate`); SHACL compact syntax: no |
| jena-shex | 88 | 81 | 567 | covered (`shexValidate`, `datasetShexValidate`) |
| jena-text | 55 | 55 | 246 | Lucene index: out of scope; `text:query` exists in the Lean tree |
| jena-tdb2 | 133 | 123 | 872 | read only TDB2 exists (`tdb2ServeOpen`, `serveStore({tdb2:true})`); writing: out of scope |
| jena-fuseki2 | 264 | 249 | 1,218 | protocol served by `serveStore`; Fuseki admin/config: out of scope |
| jena-ontapi | 121 | 91 | 1,444 | not covered (OWL 2 object API) |
| jena-rdfconnection | 28 | 26 | 443 | local: maps to handles; remote: needs HTTP host |
| jena-querybuilder | 47 | 40 | 909 | not covered (needs a query AST op) |
| jena-geosparql | 225 | 221 | 826 | partly (GeoSPARQL 37 pass, 0 fail per using-factoidal) |

### 2.2 The user-facing types (measured)

Method: `api.py` — methods declared in the one file of each type (interfaces:
every declaration; classes: `public` ones), comments removed. Inherited
methods are not counted. 26 jena-core types: 678 declarations, 467 distinct
names. 28 jena-arq types: 707 declarations, 458 distinct names. SHACL 4 types:
80/50. ShEx 4 types: 50/38. Full list: regenerate with `tools/jena-facade-study/api.py`.

| Jena type (declared methods) | Factoidal today | Gap (new Lean op unless stated) |
|---|---|---|
| Model 36 + ModelCon 83 + ModelGraphInterface 4 | `Dataset` handle: `add`, `delete`, `has`, `match`, `size`, `query`, `serialize` | value-based `contains`/`listStatements` (2.3); typed-literal creation from JS values |
| Resource 40, Property 5, RDFNode 14, Statement 34 | RDF/JS terms (`rdfjs.mjs`, `lib/nodes.mjs`) | none for structure (JS objects); `Statement.getInt` etc. need value accessors |
| Literal 18 | term components only | `getValue`, `getInt`, `getLexicalForm` of canonical form, `sameValueAs`: lexical-to-value mapping op |
| Graph 16, Node 32, Triple 19 | handle + terms | `Node.sameValueAs`, `Node.matches` are JS on terms except value equality |
| ExtendedIterator 10, StmtIterator 2 | `match` returns a handle; quads iterable | JS only |
| PrefixMapping 19 | prefixes kept on handles; `datasetSerializeWith` | `expandPrefix`/`qnameFor` touch IRI syntax: op (resolveIri exists; qname split does not) |
| RDFList 34, Container 24, Seq 44 | none | collection walk is RDF vocabulary semantics: op |
| ModelFactory 19, ResourceFactory 33 | `openDataset`, `dataFactory` | blank node label supply must be the engine's |
| InfModel 10, Reasoner 8, ReasonerRegistry 15 | `datasetClosure`, `owlClosure`, `rdfsPlusClosure`, `rhoDfClosure`, `tableau*` | Jena rule language (GenericRuleReasoner) parser and engine; Jena's OWL Micro/Mini rule sets differ from OWL 2 RL |
| OntModel 120 | none | large; defer |
| Query 97, QueryFactory 15 | `queryForm` (kind only) | query parse to a JSON AST and back (Query object model, `Query.serialize`) |
| QueryExecution 30, QueryExec 28, ResultSet 14, QuerySolution 6 | `datasetQuery`, `datasetQuery12`, `datasetQueryRaw` | `substitution`/initial bindings; timeouts (JS host) |
| ResultSetFormatter 50 | SRJ/SRX/CSV/TSV output from `datasetQueryRaw` | text table format: op |
| UpdateFactory 23, UpdateExecution 7, UpdateRequest 9 | `datasetUpdate` | UpdateRequest object model: same AST op as Query |
| Dataset 28, DatasetGraph 32, DatasetFactory 20 | handles with graph names (`datasetGraphNames`, `datasetGraphAsDefault`) | union default graph option |
| RDFDataMgr 58, RDFParser 16, RDFParserBuilder 37, RDFWriter 11, RDFWriterBuilder 17 | `parseDocument`, `datasetOpen`, `datasetSerializeWith`, `detectFormat` (content only) | syntax from file name / media type; error-handler levels (warnings exist for language tags only) |
| FunctionRegistry 15, FunctionBase 4 | `extRegister` + host callback | property functions (PropertyFunctionRegistry 14): no |
| NodeValue 109 | none (internal) | not a facade target; port its tests as SPARQL (section 3.3) |
| Txn 10, StreamRDF 8 | none | Txn: JS over clone/swap; StreamRDF: pack ops exist for SBM11 only |
| ShaclValidator 14, Shapes 18, ValidationReport 17, ReportEntry 31 | report graph from `shaclValidate` | report as objects: JS reads the report graph by term match (no semantics) |
| ShexValidator 6, ShexSchema 14, ShexReport 17, Shex 13 | `shexValidate` | ShapeMap object model |

Out of scope: JVM-only classes (Lock, ModelChangedListener event threads,
assemblers as Java object factories, Thrift/Protobuf RDF, HTTP auth, TDB1/TDB2
storage internals, Fuseki server modules).

### 2.3 Semantics that differ (measured unless marked)

Probe: `probe.mjs`, `conv/probe2.mjs`; Jena behaviour read from source.

| Behaviour | Jena | Factoidal (measured) | Effect on ported tests |
|---|---|---|---|
| `Model.contains` | `ModelFactory.createDefaultModel()` uses `GraphMemFactory.createDefaultGraphSameValue()` (value-based: `"01"^^xsd:integer` matches `"1"^^xsd:integer`). `GraphMemFactory.createDefaultGraph()` is same-term since Jena 5. | `has` and `datasetMatch` are term-based: `has("1"^^xsd:integer)` on stored `"01"` gives false | Model tests need a value-matching op; Graph tests port unchanged |
| SPARQL on a Model | ARQ over a same-value graph can match `1` against `"01"` (estimate: not run) | `ASK { <urn:s> <urn:p> 1 }` gives false (term matching, SPARQL 1.1 §18.3) | document as divergence; Factoidal follows the specification |
| Language tag case | `NodeFactory.createLiteralLang` formats per BCP 47 (`en-GB`); `sameValueAs` ignores case | `"x"@EN-gb` is written `"x"@en-gb` | `getLanguage()` assertions differ; documented divergence or a formatting op |
| `'2' = 2`, `1 = true` | false (TestExpressions expects false) | error (unbound), per SPARQL 1.1 §17.4.1.7 RDFterm-equal | Jena differs from the specification; mark tests as divergence |
| `REPLACE('abc', '.?', 'Z')` | `'ZZZ'` (Java regex) | error | XPath 3.1 `fn:replace` raises FORX0003 on a pattern that matches "": Jena differs |
| `YEAR`/`MONTH`/`DAY` on `xsd:date`, `xsd:gYearMonth`, `xsd:duration` | values | unbound | Jena extension beyond SPARQL 1.1 §17.4.5 (not checked against SPARQL 1.2 drafts) |
| `MOD`, `IDIV`, `ADJUST`, `afn:*`, `lfn:*`, `math:*` | built in | parse error or unbound | Jena extensions; port only if wanted, as Lean ops |
| Blank nodes | fresh labels per parse | fresh labels per parse (`_:a` read as `_:d4_a`) | same; tests that assert label text are rare |
| Lenient parsing | RIOT warns on some bad IRIs and keeps the triple | refuses a space in an IRIREF (same as RIOT); keeps an ill-formed language tag with a warning (owner ruling 2026-10-24) | per case; RIOT checking levels have no Factoidal equivalent |
| Duplicate triples | set semantics | set semantics (size 1 for `"x", "x"`) | same |

## 3. Jena test suites (question 2)

### 3.1 Counts per module (measured)

Method: `tcount.py` — per file under `src/test/java`, the number of
`@Test|@ParameterizedTest|@RepeatedTest|@TestFactory` annotations, or, when a
file has none, the number of JUnit 3 `public void test*()` methods. These are
declarations. Parameterized classes and abstract base classes run each
declaration more than once, so executed counts are higher.

| Module | test methods | test classes |
|---|---|---|
| jena-core | 2,953 | 258 |
| jena-arq | 7,168 | 360 |
| jena-shacl | 49 | 9 |
| jena-shex | 16 | 2 |
| jena-text | 191 | 39 |
| jena-tdb2 | 383 | 40 |
| jena-tdb1 | 544 | 56 |
| jena-db | 302 | 38 |
| jena-fuseki2 | 648 | 64 |
| jena-ontapi | 467 | 45 |
| jena-rdfconnection | 137 | 8 |
| jena-querybuilder | 328 | 22 |
| jena-geosparql | 1,441 | 164 |
| jena-base | 773 | 46 |
| jena-iri3986 | 949 | 17 |
| jena-langtag | 188 | 4 |
| jena-integration-tests | 345 | 43 |

Manifest data in the Jena tree (count of `mf:action`): `rdf-tests-cg` copy
2,722; `SPARQL-CDTs` (Jena composite datatypes) 654; `ARQ` (Jena's own SPARQL
manifest tests) 312; `RIOT` 67; jena-shacl 128; jena-shex 1,116; jena-core 35;
jena-tdb2 38. The `ARQ` and `SPARQL-CDTs` manifests are Jena-specific but in
W3C manifest form, so Factoidal's existing manifest runner can read them with
no Java port (estimate: not run).

### 3.2 Classification (measured counts; classification Claude-inferred)

Method: `classify.py`, by package path. (a) manifest runners; (b) API tests a
conversion would port; (c) JVM or engine internals (memory graph stores,
`sparql/algebra` and `sse` optimiser transforms, tokenizer, Thrift, Protobuf,
transactions, timeouts, HTTP, `sparql/util`).

| Group | jena-core | jena-arq | shacl + shex |
|---|---|---|---|
| (a) manifest | 164 (12 classes) | 231 (18) | 65 (11) |
| (b) stage 1: Model, Graph, RIOT, IRI | 1,464 (129) | 1,548 (98) | – |
| (b) stage 2: ARQ API (`query`, `sparql/*`) | – | 1,431 (88) | – |
| (b) stage 2: ARQ expressions (`sparql/expr`) | – | 1,670 (26) | – |
| (b) stage 3: reasoners, ontology, rdfs | 617 (47) | 112 (8) | – |
| (c) internals | 708 (70) | 2,176 (122) | – |

Total (b): 6,842. Total (c): 2,884. Total (a): 460. jena-shacl also has API
tests (compact syntax, report) inside the 65; SHACL compact syntax has no Lean
reader (searched `formal/lean4` for SHACLC: none).

### 3.3 Measured conversion: ARQ expression tests

`conv/extract.py` took every one-line test of the forms
`testBoolean("E", b)`, `testNumeric("E", n)`, `testString("E", s)`,
`testEvalException("E")`, `test("E", "EXPECTED")` and
`test("E", NodeValue.makeX(v))` from `jena-arq/.../sparql/expr`: 477 cases (of
918 one-line test declarations there). `conv/run-expr.mjs` wrote each as one
SPARQL ASK query (`BIND(E AS ?a) BIND(EXPECTED AS ?b)`, then datatype, language
and value equality, or `!BOUND(?a)` for an expected error) and ran it on
`@factoidal/core` 0.15.0 in SPARQL 1.2 mode with a base IRI. The comparison is
done by the engine; JS only reads the boolean.

Result: 274 pass, 157 fail, 46 error (out of 477); 234 ms total.

| Cause of fail/error | count | Whose defect |
|---|---|---|
| expected type error, Factoidal returns a value (CONTAINS, STRSTARTS, STRENDS, STRBEFORE, STRAFTER, SUBSTR, ENCODE_FOR_URI, MD5, SHA*) | 42 | Factoidal, against SPARQL 1.1 §17.4.3.1.4 and §17.4.6 |
| SUBSTR with start ≤ 0 or non-integer arguments, e.g. `substr('12345',0,3)` gives `"123"`; `substr(1,1,3)` gives `"1"^^xsd:integer` | 7 + 2 | Factoidal, against `fn:substring` |
| YEAR/MONTH/DAY/HOURS/MINUTES/SECONDS/TIMEZONE on non-dateTime types | 46 | Jena extension |
| `math:*` (pow, exp, log, sqrt) | 22 | not implemented in Factoidal (XPath 3.1 math functions); or harness issue with `'INF'^^xsd:double`: not separated |
| `afn:*`, `lfn:*`, `MOD`, `IDIV`, `ADJUST`, `fn:numeric-*`, `sparql:*` IRIs | 46 | Jena extensions |
| `'2' = 2`, `1 != true`, `'a'+'b'`, REPLACE on empty match | about 14 | Jena differs from the specification |
| RDF 1.2 functions (`isTriple`, `subject`, ...) | 5 | parse error: harness used Jena's names; not separated |
| other | rest | not analysed |

The first two rows are candidate Factoidal issues. They are not filed (research
only). Each needs a failing test plus an open issue (owner rule, 2026-09-07).

### 3.4 Sample hand port

`conv/sample-port.test.mjs` ports 11 methods from three classes:
`TestLiteralsInModel` (7 methods in the class), `TestAPI` (34),
`TestRDFParser` (31). What the port needed from the engine:

- `TestLiteralsInModel`: Java overloads `addLiteral(X,P,99)` (xsd:int) and
  `99L` (xsd:long), `14.0f` (xsd:float), `'x'` (char). A JS number cannot carry
  the type. The facade needs explicit typed values (BigInt, `XSD.int(99)`), and
  the datatype choice must be an engine table. The assertions depend on
  value-based `contains`.
- `TestAPI`: CONSTRUCT, isomorphism and RDF 1.2 CONSTRUCT filtering exist.
  `substitution(QuerySolutionMap)` needs a new op. A result `Resource` keeps a
  link to its model (JS only).
- `TestRDFParser`: string and file sources exist. Syntax from file name
  (`data.ttl`) needs an op; a JS suffix table fails host-purity lint group 3.

## 4. Design (question 3)

- Package `npm/echochamber/` (`@factoidal/echochamber`), dependency on
  `@factoidal/core`, same wasm, loaded through `loadEngine()`. No second wasm.
- Java names in camelCase (`createResource`, `listStatements`). Java
  iterators implement `hasNext/next/close/toList` and `[Symbol.iterator]`.
  try-with-resources maps to `using` (Node 24) or try/finally.
- Synchronous API after `await ready()`: handle ops are synchronous wasm calls.
  Only engine load is asynchronous.
- Exceptions: map the `{"ok":false,"error":...}` envelope to Jena-named
  classes (`RiotException`, `QueryParseException`, `DatatypeFormatException`)
  as subclasses of `FactoidalError`. The class choice must come from an error
  code in the envelope, not from matching message text. Today the envelope has
  messages only: add a `code` member (new op work).
- JS may do: names, argument order, iteration, builder objects, handle
  lifetime, wrapping terms. JS may not do: datatype choice for JS values,
  literal value comparison, IRI or qname splitting, file-name-to-syntax, RDF
  list walking, error classification by text, vocabulary IRI tables. Jena's
  vocabulary classes (`RDF.type`, `XSD.xint`, `OWL.Class`) contain namespace
  IRIs, which lint group 3 forbids in JS; serve them from an op
  (`vocabularyTable`) generated from the Lean vocabulary modules.
- Entrypoint gate: `tools/entrypoint-gate.py` reads only
  `npm/factoidal/package.json`. A second package would be outside the gate.
  Extend it to every `npm/*/package.json`, then map each echochamber export
  to the core op's stage or declare it `[[nonstage]]`. Most facade methods
  are thin calls of already-mapped ops, so "covers = part" entries suffice.
- Host-purity lint: add `npm/echochamber/**/*.mjs` to group 3.
- Prior art: RDF/JS (DataFactory, DatasetCore; Factoidal's `rdfjs.mjs` and
  `Dataset` already follow it); rdflib.js (`IndexedFormula.statementsMatching`,
  `any`, `each` — the nearest JS shape to Jena's Model); N3.js `Store` (RDF/JS
  store); Comunica (query engine over RDF/JS sources); Oxigraph JS (Rust to
  wasm, `Store.match/query/update/load/dump`, the nearest architecture). None
  copies Jena's API. echochamber sits above RDF/JS: a Jena object API whose
  `Graph` is a Factoidal handle and whose `Node`s are RDF/JS terms.

## 5. Licence and name (question 4)

- Jena is Apache-2.0; Factoidal npm is Apache-2.0. Ported test files are
  derivative works. Apache-2.0 §4 requires: keep the copyright and licence
  notices (keep the ASF header in each ported file), add a prominent notice of
  change in each changed file, and include Jena's NOTICE text (ASF copyright
  2011-2026; HP, Epimorphics, Talis grants; PluggedIn; Xerces; OGC) in the
  package NOTICE. Copied fixtures (`testing/RIOT/Parser/*`) carry the same.
- API shape (names and signatures) copied from Apache-2.0 code is licensed for
  reuse by that licence; no extra step.
- Trademark (ASF policy, https://www.apache.org/foundation/marks/, read
  2026-10-25): "In general you may not use ASF trademarks in any software
  product branding." "Powered By" naming applies only to products that use the
  Apache software, which echochamber would not. Nominative use in text is
  allowed: "an API modelled on Apache Jena's" with first-use "Apache Jena" and
  a trademark attribution line. Do not use "jena" in the package name, scope,
  binary or domain. `@factoidal/echochamber` is acceptable.

## 6. Plan, effort and risk (question 5)

Effort figures are estimates; test counts are measured (section 3.2).

| Stage | Scope | Tests to port (b) | Works with current wasm | New Lean ops (wasm rebuild) |
|---|---|---|---|---|
| 0 | Port the 918 one-line ARQ expression tests as SPARQL ASK; file issues for the type-error and SUBSTR defects | 918 declarations (477 extracted now: 274 pass) | yes, today | fixes only |
| 0b | Run Jena's `ARQ` (312) and `SPARQL-CDTs` (654) manifests with the existing runner | 966 manifest actions | yes (estimate) | CDT datatypes if wanted |
| 1 | Graph, Node, Triple, Model (term-equality), Statement, Resource, PrefixMapping, RDFDataMgr/RDFParser/RDFWriter on strings | 1,464 core + 1,548 arq | Graph and term-level Model: yes | value matching mode; JS-value-to-literal table; literal value accessors; file-name/media-type to syntax; qname split; vocabulary table; error codes; RDF list/container walk |
| 2 | Query, QueryExecution, ResultSet, Update, Dataset, FunctionRegistry | 1,431 arq (+ expression tests from stage 0) | execution: yes | query/update AST to JSON and back; substitution; text result format; property functions |
| 3 | InfModel (RDFS, OWL), SHACL and ShEx objects | 617 core + 112 arq + 65 | RDFS/OWL 2 RL closure, SHACL, ShEx: yes | Jena rule-language parser and engine (or declare out of scope); Jena OWL Micro/Mini rule sets; SHACL compact syntax reader |

Estimate of facade size: about 900 distinct method names for the types in 2.2
(measured 467 + 458 distinct, before overlap). Estimate of porting rate: a
model-driven conversion of a JUnit class into node:test is minutes per class;
the cost is in the engine gaps and in deciding each divergence, not in the
translation.

Risks:

- Jena's Model is value-based and Java-typed; a port that keeps tests unchanged
  needs a value-matching handle mode in Lean. Without it, about the
  `rdf/model` tests (360 declarations) need divergence notes.
- Each divergence must be a failing test with an open issue, or a documented
  Jena-differs-from-specification case. The divergence list grows with the port.
- Jena's rule language and OWL rule reasoners are a second inference system;
  `rulesys` alone is 289 test declarations.
- The entrypoint gate does not see a second package today (section 4).
- Synchronous API depends on handle ops staying synchronous; `query` in
  `lib/dataset.mjs` is declared `async` today but calls a synchronous op.
