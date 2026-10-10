# npm `@factoidal/core`: the Lean 4 engine only

Date: 2026-10-10. Tracking issue: https://github.com/danbri/factoidal/issues/713.
Related: https://github.com/danbri/factoidal/issues/476 (dual-engine
packaging), https://github.com/danbri/factoidal/issues/578 (Lean crypto/VC
off-native), https://github.com/danbri/factoidal/issues/585 (dataset handles
at the ABI), https://github.com/danbri/factoidal/issues/685 (envelope parity),
https://github.com/danbri/factoidal/issues/679 (usability defects).

## 1. Decision

Owner, 2026-10-10, verbatim:

> "I understand our NPM module Factoidal/core is currently a mix of components
> derrived from the F* and/or Lean4 trees here. This looks potentially bloated
> and bug-prone. We should make the main module Lean4-based. Private builds
> might compare this with F* (or indeed different wasms from different
> toolchains). Are we in a position to go 100% to the Lean4 build? If not, why
> not?"

So: the published package carries one engine, the Lean 4 build
(`L4Factoidal` compiled through Lean → C → wasm). The F\* bundles, and any
other build of the same functions (another toolchain, another wasm), are for
private comparison builds, not for the published package.

## 2. State on 2026-10-10 (measured in danbri/factoidal-core 685326b2)

Package `@factoidal/core` 0.8.0, `npm/factoidal/`.

Which engine each entry point loads, before stage 3 (0.8.0) and after it
(0.9.0):

| Entry | 0.8.0 | 0.9.0 (stage 3) |
|---|---|---|
| `.` (`index.js`, `index.mjs`), `./api`, `./fn`, `./browser` | F\* (js_of_ocaml / wasm_of_ocaml bundles; `hacl-wasm/` for VC crypto) | Lean 4 |
| `./lite`, `./wasm`, `./browser-wasm` | F\* | removed |
| `./l4`, `./l4-core` | Lean 4 (wasm, dispatch ABI) | Lean 4 (aliases of `.`; go in 0.10.0) |
| `./select` | both | removed |
| `bin/factoidal.mjs`, `lws/`, `solid/` (Node hosts) | Lean 4 | Lean 4 |
| `./rdfjs`, `store-host`, `sample-store`, `xmpp` | engine-neutral wrappers | engine-neutral wrappers |

The main entry exports 72 names; `l4-core` exports 30. 42 main-entry names
have no Lean path in the package:

| Group | Names | Lean library | Lean wasm dispatch op and `l4-core` wrapper |
|---|---|---|---|
| Formats and transforms | `jsonldToRdf`, `jsonldFromRdf`, `rmlMap`, `csvwToRdf`, `xmlWellformed`, `xpathEval`, `xsltTransform`, `schematronValidate`, `jsonSchemaValidate`, `mathmlEval`, `xformsRecalc`, `rifEval` | yes (W3C suites pass, see issue 698) | **yes since stage 1**: `Wasm/Ops/Formats.lean`; wrapped in `l4-core.js` |
| Stores | `queryHdt`; `openCottas`, `queryCottas`, `closeCottas`, `toCottas` | HDT: yes. COTTAS: no; the owner ruled F\* COTTAS essentially unused (issue 566); the Lean store (IBK3 generations, `storeOpen`/`storeQuery` ops) is the replacement, with a different format | HDT: **yes since stage 1** (`queryHdt` in `Wasm/Ops/QueryExtras.lean`; the file travels as the ABI's byte region). COTTAS: no, by the ruling; store: yes |
| Reasoning | `tableauMaterialise`, `tableauDlInconsistent` | yes (OWL refuter / tableau) | **yes since stage 1**: `Wasm/Ops/Reasoning.lean` |
| Query plumbing | `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions`, `registerServiceEndpoint`, `clearServiceEndpoints`, `queryRaw` | yes | **yes since stage 1**: extension functions (`extRegister` ... already existed; `l4-core.js` now wraps them and installs the JavaScript call-out), SERVICE endpoints (`Wasm/Ops/ServiceReg.lean`), `queryRaw` (`Wasm/Ops/QueryExtras.lean`) |
| Maths | `toanSummation`, `toanProduct`, `toanSimplify`, `toanDiff`, `toanSubst`, `matrixDeterminant`, `matrixScalarProduct`, `matrixVectorProduct`, `matrixOuterProduct`, `sigmoidPoints`, `sigmoidFormulaMathml` | yes (`L4Factoidal/Math`) | ToaN: **wrapped in `l4-core.js` since stage 1** (the ops existed); matrix, sigmoid: yes since stage 2 (`Wasm/Ops/Maths.lean`) |
| VC and DID | `vcSha256Hex`, `vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical`, `vcCheckCredential`, `vcCheckCredentialSubject`, `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests`, `didKeyResolve` | yes; `vcCheckNoDataLoss` and `vcCheckRelatedResourceDigests` landed in stage 2 (`L4Factoidal/VC/Credential.lean`, namespace `Doc`) | yes since stage 2 (`Wasm/Ops/Vc.lean`) |

The table is the state on 2026-10-10 before stage 1 and stage 2, with each
cell updated by the stage that changed it.

**After stage 1 and stage 2** (measured in danbri/factoidal-core, 2026-10-10):
`l4-core` exports 73 names (30 before). Of the main entry's 72 names, 4 have no
`l4-core` function: `openCottas`, `queryCottas`, `closeCottas` and `toCottas`,
which the issue 566 ruling replaces by the Lean store functions in stage 3.
`shaclValidate` and `shexValidate` are exported by `l4-core` as functions that
reject with the engine-capability error: the Lean library has SHACL and ShEx and
the dispatch table does not serve them yet. Stage 3 is the switch.

Behaviour differences of the Lean engine through the npm wrapper, already
recorded on 2026-10-10:
- envelope parity: parse-error position, prefixes on a dataset handle,
  `serializeTurtleWith`, literal shorthand in Turtle output (issue 685,
  expected-failure cases in `npm/factoidal/test/`);
- blank-node labels are not salted per document when documents are merged
  (`test/l4-core.test.js` header);
- N-Quads line order differs (content is compared sorted).

State after stage 2 (2026-10-10): the first two are closed; see § 5. The
N-Quads line order still differs. Three differences remain, each stated here
so the stage 3 switch does not hide them:
- the Lean `offset` of a parse error counts Unicode scalar values, the F\*
  `offset` counts UTF-8 bytes (`line` and `column` agree);
- the Lean parser has no `{lenient: true}` mode, so `parse()` with that option
  and `capabilities().parseDiagnostics` stay unserved on the Lean engine;
- `datasetQuery12` (SPARQL 1.2 over a handle) is unserved on the Lean engine.

State after stage 3 (§ 7): the wrapper converts `offset` to a UTF-16
code-unit index, so `text.slice(err.offset)` starts at the error;
`datasetQuery12` is served. `{lenient: true}` was still unserved at the
stage 3 merge (issue 716); the issue-716 merge serves it (op `parseDocument`,
`formal/lean4/Wasm/Ops/Lenient.lean`), its two expected-failure cases are now
assertions, and diagnostic offsets get the same UTF-16 conversion as
`ParseError.offset`. One difference from the F\* engine remains, by the
issue's specification: Turtle recovery resumes at the next statement boundary
(a `.` in normal mode followed by white space or `#`), where the F\* engine
resumed at the next line.

Size, measured on the 2026-09-08 Lean wasm (6,359,842 bytes) and the F\*
bundles of factoidal-builds run 11:

| Artifact | Raw | gzip -9 |
|---|---|---|
| Lean `l4factoidal.wasm` (whole library) | 6.36 MB | 1.20 MB |
| F\* `factoidal-npm-entry.js` (full) | 1.18 MB | 0.35 MB |
| F\* `factoidal-npm-entry-lite.js` | 0.60 MB | 0.17 MB |

The Lean module is about 3.4 times the F\* full bundle after compression,
because one dispatch table reaches the whole library, so the linker can drop
nothing.

After stage 3 (§ 7) the wasm of 0.9.0 is 10,402,990 bytes raw and 2,042,240
bytes with gzip -9; every JavaScript file `browser.js` loads is 67,446 bytes
with gzip -9 together.

Speed: the 2026-08-22 benchmark (issue 476) measured the Lean query path as
quadratic (2,891 ms against 205 ms for F\* wasm at 8,000 triples). The Lean
evaluator has changed a lot since then; the Lean vs F\* survey of 2026-10-10
(branch claude/wt-perf-survey) re-measures it.

## 3. Answer to "are we in a position to go 100% Lean?"

Not on 2026-10-10, for four reasons, none of them a missing specification
implementation:
1. Plumbing: 42 of 72 main-entry functions are not exported through the Lean
   wasm dispatch ABI or not wrapped in JavaScript. 38 of them are already in
   the Lean library with their W3C suites passing.
2. Two Lean library gaps: the VCDM data-loss and related-resource-digest
   checks (issue 578 gap 3; closed by stage 2), and SPARQL SERVICE endpoint
   registration from the host.
3. Recorded behaviour differences (issue 685 and blank-node salting, both
   closed by stage 2; N-Quads order and the three differences listed above
   remain).
4. Download size (about 3.4 times larger compressed) and query speed are not
   yet measured to be acceptable for a browser default.

COTTAS is not a reason: the owner's ruling on issue 566 lets the package drop
the F\* COTTAS functions in favour of the Lean store.

## 4. Plan (one commit-sized stage each)

1. [x] Formats, transforms, stores, reasoning, query plumbing: dispatch ops and
   `l4-core` wrappers for the first four groups of the table, each tested by
   running the existing F\*-engine npm tests for that function against the
   Lean engine (same inputs, same expected results). Landed on the branch
   `claude/wt-npm-lean-1` of danbri/factoidal-core (2026-10-10):
   `npm/factoidal/test/l4-parity.test.js`, and a case pair per op in
   `formal/lean4/Wasm/native-smoke.sh`. Differences from the F\* engine that
   the parity run found are in § 6.
2. Maths, VC and DID (issue 578 items 2-4), and the envelope parity of
   issue 685 and blank-node salting. **Done 2026-10-10** (branch
   `claude/wt-npm-lean-2`); the record is § 5.
3. [x] Switch: `.`, `./api`, `./fn`, `./browser` load the Lean engine; the F\*
   bundles, `hacl-wasm/`, `./wasm`, `./browser-wasm` and `./lite` leave the
   package. The F\* bundles stay as factoidal-builds artifacts for private
   comparison builds (and the differential harness `l4diff`). The COTTAS
   functions are replaced by the Lean store functions. Version 0.9.0.
   **Done 2026-10-10** (branch `claude/wt-npm-lean-3`); the record is § 7.
4. Size profile: a smaller Lean wasm for the browser, from a dispatch table
   that reaches a subset of the library (the role `./lite` had), measured
   against the F\* lite bundle.
5. Speed: the npm benchmark (`tests/perf/l4_vs_fstar_wasm_bench.mjs`) re-run;
   any row where the Lean engine is more than 2 times slower becomes an
   issue before the switch is published.

## 7. Stage 3: what landed (2026-10-10)

Everything below is in `danbri/factoidal-core`, branch `claude/wt-npm-lean-3`,
merged with `claude/core-split` at c8dbe2ab (the OWL DL merge and the
performance merge). Package version 0.9.0.

### Entry points

`.` (`index.js`, `index.mjs`), `./api`, `./fn` and `./browser` load the Lean
wasm. `./l4` and `./l4-core` are aliases of `.` for 0.9.x and go in 0.10.0
(`CHANGELOG.md`). These files left the package and git: `wasm.js`,
`wasm.d.ts`, `lite.js`, `lite.mjs`, `lite.d.ts`, `browser-wasm.js`,
`hacl-init.js`, `hacl-wasm/`, `parquet_zstd_stubs.js`, `vendor/fzstd.umd.js`,
`select.js`, `select.d.ts`, `lib/engine-js.js`, `lib/engine-wasm.js` and the
F\* `version.json`. The F\* bundles are no longer copied into the package.

The JavaScript is one ES module core with CommonJS shims:

| File | Role |
|---|---|
| `lib/api.mjs` | the typed wrappers (`buildApi`): argument shaping, envelope decoding, RDF/JS conversion, `ParseError`, `DatasetHandle`, `Store`. No RDF or SPARQL semantics |
| `lib/lean-entry.mjs` | one method per op, built from the engine's `ops` reflection; the byte-region adapters (`queryHdt`, `storeOpen`) and the extension-function call-out |
| `lib/store.mjs` | the store reader plumbing: read `CURRENT`, a manifest and the artifact files the engine names |
| `index.mjs` | Node: loads `bin/engine.mjs`, reads a store from the file system |
| `browser.js` | browser: fetches `l4-assets/l4factoidal.wasm` and compiles it with `WebAssembly.instantiateStreaming` (falls back to `WebAssembly.instantiate` over the bytes when the server sends another media type); `setAssetsUrl` moves the assets |
| `api.mjs` | `createApi(engine)` over an engine handle the caller loaded |
| `index.js`, `api.js`, `rdfjs.js`, `l4.js`, `l4-core.js` | CommonJS: `module.exports = require('./….mjs')` (Node `require(esm)`, so `engines.node` is `>=22.12`) |

`capabilities()` is computed from the ops the loaded wasm lists, so an older
wasm reports what it serves. A function the wasm does not serve rejects with
the capability error; there is no command-line fallback.

### Lean operations added

| Op | Module | What it does |
|---|---|---|
| `queryDataset12` (`callIO`) | `Wasm/Ops/Query.lean` | `queryDataset` with the SPARQL 1.2 grammar (`SparqlVersion.v12`), so a triple term pattern parses |
| `datasetQuery12` (`callIO`) | `Wasm/Ops/Handles.lean` | the same over a dataset handle; `DatasetHandle.query(q, {sparql12: true})` |
| `shaclValidate` (`call`) | `Wasm/Ops/Validate.lean` | `SHACL.decodeShapesGraph`, `SHACL.validateFull`, report as N-Triples of `SHACL.reportToGraph`. A shapes graph with a feature the decoder does not read, and a validation failure (SHACL § 5.3.2), are refusals |
| `shexValidate` (`call`) | `Wasm/Ops/Validate.lean` | ShExJ when the schema text starts with `{`, ShExC otherwise; `ShEx.validateStart` for an empty shape, `ShEx.validateNode` otherwise. `verdict` is always a boolean (the F\* function answered `null` outside its fragment) |
| `queryRaw` entailment `x-rdfscore`, `x-rdfsplus` | `Wasm/Ops/QueryExtras.lean` | `RDFS.closureFix` and `RDFS.rdfsPlusClosureFix` before the query, beside the existing `none`, `RDFS` and `OWL-RL` |

Each has positive and negative `#guard` cases in its module and cases in
`Wasm/native-smoke.sh`.

### The store

The COTTAS functions (`openCottas`, `queryCottas`, `closeCottas`, `toCottas`)
are removed; the issue 566 ruling replaces them with the Lean store.
`openStore(source, {generation, sparql, keys})` takes a collection root path
(Node) or a reader function `path => bytes` (any host) and answers a `Store`
(`query`, `inspect`, `close`, and `generation`, `activated`, `identity`,
`layout`, `wireVersion`, `artifacts`, `bytes`, `rows`). `queryStore(source,
sparql)` opens, queries and closes. `listStores()` lists the open handles. The
manifest is checked, the artifacts are chosen and their digests are verified
by the ops `storeManifestInspect`, `storeQueryPlan` and `storeOpen`; the
JavaScript reads the files they name. With `{sparql}`, only the artifacts that
query's plan needs are read, and the handle refuses a query that needs more.
`sampleStorePath` and `sampleStoreFacts` are exported from `.` for tests and
examples. Cases: `npm/factoidal/test/store.test.js`.

### `ParseError.offset`

`offset` is a UTF-16 code-unit index into the input string
(`text.slice(err.offset)` starts at the error); `column` stays a count of
Unicode scalar values, as the engine reports it. The engine counts Unicode
scalar values; `utf16OffsetOf` in `lib/api.mjs` converts. The F\* engine
counted UTF-8 bytes. This unit is a coordinator default for issue 713 stage 3,
not an owner decision. Cases with U+1F600 in `test/parse-errors.test.js`.

### SELECT solution order of variables

The Lean engine writes the members of each SPARQL Results JSON binding
object in name order; `head.vars` is in SELECT order. The wrapper built each
solution `Map` from the binding object, so the Map iterated in name order.
A JSON object is unordered (RFC 8259 § 4), so `bindingsFromSrj` in
`lib/api.mjs` now takes the order from `head.vars` (SPARQL 1.1 Query Results
JSON Format § 3.1). Case: "query: each solution Map iterates in the SELECT
projection order" in `test/api.test.js` (fails without the change). Hub
posts 19, 21 and 31 pinned the SELECT order and pass again.

### Tests

All tests that load `.`, `./api`, `./fn` or `./browser` run on the Lean
engine. Tests that only checked the F\* engine, or a removed entry point, are
deleted (`lite`, `select`, `wasm-parity`, `vc-crypto`, `browser-wasm-cottas`,
`cottas-bytes-store`, `cottas-bytes-store-wasm`, `delta-log`,
`delta-log-typed`, `delta-log-wasm`, `smoke-wasm.mjs`, `smoke.js`). Assertions
of F\*-specific output (blank-node labels, statement order) became the
spec-level property (graph isomorphism, RDF 1.1 Concepts § 3.6; equal
statement sets). A capability probe that skipped a test is now an assertion,
so a function the wasm does not serve fails the suite. The F\* cross-checks
moved to `tests/engine-compare/` (`run.sh PATH/TO/factoidal-npm-entry.js`,
exit 2 when the bundle is absent).

Expected failures in `npm test`, each with an open issue (the issue-716
merge turned its 2 cases, `{lenient: true}` parse, into assertions):
- issue 717, `SERVICE` without `SILENT` to an unregistered endpoint: 1 case (fixed in ffbce3c0; issue 735 has the two remaining cases);
- issue 691, unused `@prefix xsd:` in Turtle output with literal shorthand: 1
  case (the Lean writer has the defect the issue names for F\*);
- issue 676, PRECIS for XMPP JIDs: 2 cases.

### The hub

`docs/web/hub/hub.njk` and three demos imported `npm/factoidal/browser.js`,
which was the F\* API. That driver is kept at
`docs/fstar-extracted/browser.js`, beside the F\* bundles that
`tools/fetch-builds.sh` installs, and the hub template, the demos, the
service-worker precache list and the hub browser checks point at it. The hub
node harness (`tests/hub/`) binds `npm/factoidal`, which is now the Lean
engine, so the node harness and the hub pages test different engines.
On the stage 3 tree with no F\* bundle and no F\* native binary installed,
the hub node suite is 353 pass, 34 fail (out of 387). Before stage 3 it was
203 pass, 184 fail (out of 387), measured in another checkout of the same
container (`/home/user/work/core-main`) which had the F\* native binary but no
F\* web bundle; the node harness then bound the F\* bundles, which were not
installed. Two of the hub checks read the browser driver: they now read
`docs/fstar-extracted/browser.js`, the file `hub.njk` imports. The 34
failures are of four kinds:
- Lean output that differs from the F\* output the post pins: the parse-error
  column (post31: the Lean parser reports the position after the token), the
  members of the OWL-RL closure (post03: no `rdfs:Resource` and `owl:Thing`
  types), the MathML `undef` reason (post28), the Schematron location
  `/person[1]` (post27), the `via` member of `owlEntails` (post30);
- functions the Lean package does not have: COTTAS (post42), `text:query`
  (post20), `geof:distance` and `geof:envelope` (post21);
- files and cells that need an F\* build: the npm-entry bundle
  (`FACTOIDAL_NPM_ENTRY`: post07, post10, post13, post18, post23, post25), the
  native binary or the js_of_ocaml bundle (post24), the installed F\*
  `version.json` (post37);
- files this checkout does not have: `docs/test-results/latest.json`
  (post17), and the `.eleventy.js` pass-through line post54 pins.

Which engine the hub uses was decided by the coordinator on 2026-10-10
(https://github.com/danbri/factoidal/issues/726): the published one, Lean.
§ 8 records the move.

### Gates

Measured on the merge with `claude/core-split` c8dbe2ab, with the wasm that
`Wasm/build-wasm.sh` built from that tree (10,402,990 bytes; 10,375,811 before
the merge; 9,622,969 after stages 1 and 2). No F\* bundle is in
`npm/factoidal/` or `docs/npm/` for these runs.

| Gate | Result |
|---|---|
| `lake build` (in `formal/lean4`) | exit 0 (1314 jobs) |
| `formal/lean4/Wasm/native-smoke.sh` | 297 pass, 0 fail (out of 297); 282 before stage 3 |
| `cd npm/factoidal && npm test` | 371 pass, 0 fail, 0 skipped (out of 371), 6 of them the expected-failure cases above. Before stage 3, with no F\* bundle: 227 pass, 98 fail, 108 skipped (out of 433) |
| `tests/lws/server.mjs`, `tests/solid/server/protocol.mjs`, `tests/solid/client/against-own-server.mjs` | 8, 12 and 7 pass, 0 fail |
| `tests/store-host/conformance.mjs`, `tests/store-host/cli.mjs` | 34 and 33 pass, 0 fail |
| `tests/web-demos/npm_browser_smoke.sh` (headless Chromium, static page, local Node HTTP server) | PASS: parse, SELECT, `canonicalize`, `xpathEval`, `openStore` over `fetch`; `instantiateStreaming` called once; wasm served as `application/wasm`; 1776 ms to settle |
| `tests/web-demos/bundler_csp_smoke.sh` | PASS (esbuild bundle under `script-src 'self' 'wasm-unsafe-eval'`) |
| `tests/engine-compare/run.sh` with the F\* bundle of factoidal-builds `build-dba1bdb1d320-web` | 7 pass, 0 fail (out of 7), one of them the issue 702 expected failure; exit 2 with no bundle |
| `npm pack --dry-run` | 161 files, 2,410,574 bytes packed, 12,042,704 unpacked; no F\* bundle, no `hacl-wasm/` |

The Lean changes add no `sorry`, `axiom`, `native_decide` or `partial def`.

## 8. The hub on the Lean engine (issue 726, 2026-10-10)

Branch `claude/wt-hub-lean` of danbri/factoidal-core.

### Bindings

`docs/_includes/hub.njk` imports `/npm/factoidal/browser.js` as `Factoidal`
and binds `fn = Object.assign({}, Factoidal.default, hubHelpers)`: the
package's typed API, plus the hub-only helpers (the Lean dispatch ABI
`loadL4`/`l4Call`/`l4CallBlobIO`/`l4Parse`/`l4Query`/`l4Update`, where
`loadL4()` is the package's own `loadEngine()`, so a page instantiates one
wasm module; `openStoreOverHttp`; `loadWikifunctions`;
`loadRegistryPackage`). The F\* raw-call adapter and its JavaScript N-Quads
parser are removed. `docs/.eleventy.js` passes the package's browser files
through from `npm/factoidal/` (browser.js, api.mjs, rdfjs.mjs, lib/,
l4-assets/, store-host/, store-http/); the generated mirror `docs/npm/`
is no longer read (the factoidal-builds `web` release still writes it; it
can stop). The service worker precaches the engine's JavaScript and the
two loaders; the 10 MB wasm is warmed on first use (precaching it made the
first-visit install slow enough that post 42 missed the browser sweep's
navigation deadline). `tests/hub/fn_surface_parity_test.mjs` imports
browser.js and checks every `fn.*` and `Factoidal.*` name a post calls
against its exports and the helpers.

### The 34 node-harness failures

Kind 1, Lean output against an F\* pin; each pin is now what the
specification fixes:
- post03: the OWL 2 RL/RDF rules (OWL 2 Profiles § 4.3, Tables 4-9) give
  `foaf:Person` (cax-eqc1) and type no individual as `owl:Thing` (cls-thing,
  Table 6, types `owl:Thing` itself as a class); `rdfs:Resource` comes from
  rdfs4a/rdfs4b, RDFS entailment. The Lean closure is right; the F\*
  answer came from extension tables. Pin and prose changed.
- post27: SVRL `location` is an XPath that selects the context node; the
  test evaluates the reported path on the instance.
- post28: the undefined value is pinned, not the wording of its reason.
- post30: the someValuesFrom conclusion is in the RL closure (cls-svf1,
  Table 6; cax-eqc2, Table 7), so `via` is `closure`; a union example (no RL
  row) shows the `refutation` path.
- post31: column 10 is where the text stops being a prefix of any Turtle
  1.1 document (`PNAME_NS ::= PN_PREFIX? ':'`); the F\* parser reported the
  token start. The test also checks that `text.slice(err.offset)` starts
  there.

Kind 2, functions only F\* had:
- post42 packs its TriG corpus in the page into one Shardborough generation
  (layout ibk4, the quad layout; ops packBegin/packFeed/packNext/packEndPass/
  packFinish) held in a Map, opens it with `openStore(reader, {generation})`
  and queries the `Store`; the store and in-memory answers agree.
- post20 (`text:query`) and post21 (`geof:distance`, `geof:envelope`):
  expected failures naming https://github.com/danbri/factoidal/issues/727,
  with a note in each post.
- post18 (the browser durable update log): opened as
  https://github.com/danbri/factoidal/issues/728; the three lifecycle cells
  and the browser.js exports are expected failures naming it, and a note in
  the post says steps 2-4 answer `{available: false}` on the Lean engine.

Kind 3, cells that needed an F\* build: posts 06, 07, 09, 10, 13, 23, 25,
45, 48 and 49 call the typed functions (`shexValidate`, `jsonldToRdf`,
`jsonldFromRdf`, `rmlMap`, `rifEval`, `csvwToRdf`, `didKeyResolve`,
`xmlWellformed`, `xpathEval`, `queryRaw`), and their tests bind the
package instead of F\* ABI shims. post10's `rounds` member is gone (the
Lean saturation reports no round count). post24 uses the package's
`queryHdt`. post37 maps the 0.1.0 tarball's `gitSha` (a danbri/factoidal
commit) through `tools/repo-split/commit-map.tsv` before the ancestry check.
post12's `factoidal/wasm` capability check had no subject after 0.9.0; it
is replaced by a check that the entry is gone, and the post's section says
the package has one engine.

Kind 4, checkout files:
- post17 reads the committed Lean conformance baseline
  (`docs/designissues/2026-10-09-lean-conformance-baseline.md`: SPARQL 1.1
  manifest-all, which includes the 13 Update manifests, 631 pass, 0 fail
  (out of 631)) instead of `docs/test-results/latest.json`, a build
  artifact the checkout does not have; the prose says both figures.
- post54 pins the new package pass-through instead of the removed
  `"../npm/factoidal/store-http"` line.
- post18's C demo transcript is checked against the committed KaRaMeL C
  source (`delta_log_demo.c` prints both quoted lines); the demo binary is
  an F\* native build product. Two checks of the F\* npm-entry bundles'
  contents were removed: their subject is not in a hub checkout.

### Tools that loaded files 0.9.0 removed

`tests/perf/l4_vs_fstar_wasm_bench.mjs` runs the Lean engine through the
package and the two F\* npm-entry bundles by path from
`docs/fstar-extracted/` through the same `buildApi` wrappers (an absent
bundle is reported as that engine's error); `tools/deltalog-bench/
bench-js-wasm.mjs` loads the F\* wasm npm-entry bundle by path;
`tools/bundle-sizes.sh` measures the package files as required rows and
the F\* bundles as optional comparison rows; `tests/hub/post12_test.mjs`
no longer requires `npm/factoidal/wasm.js`.

### Gates (2026-10-10)

No Lean source changed, so the wasm was not rebuilt: the runs use the
module the issue-716 merge built from the same Lean tree (10,510,450
bytes, sha256 `5da96d60…`), installed in `npm/factoidal/l4-assets/`. The
newest factoidal-builds `web` release (`build-19c2f705e3e8-web`) predates
stage 3 and lacks its operations. No F\* bundle or binary was installed.

| Gate | Before | After |
|---|---|---|
| `node --test tests/hub/*_test.mjs` | 353 pass, 34 fail (out of 387) | 445 pass, 0 fail (out of 445), 18 of them expected failures: issue 727 (7), issue 728 (10), issue 690 (1, older) |
| `tests/web-demos/hub_browser_all.sh` (headless Chromium) | not run on the Lean engine | 54 pass, 0 fail (out of 54 posts) |
| `cd npm/factoidal && npm test` | 372 pass (coordinator) | 371 pass, 0 fail, 1 skipped (out of 372); the skip is the esbuild bundler case, esbuild not installed in this worktree; 4 expected failures |

### Not done

The three F\* gallery demos under `docs/fstar-extracted/` (`demo-cottas`,
`demo-jsonld-playground`, `demo-rif`) still import the F\* driver
`./browser.js` and its `runFactoidalCli`; they are not hub pages and need
the F\* web bundles.

## 5. Stage 2: what landed (2026-10-10)

Everything below is in `danbri/factoidal-core`, branch `claude/wt-npm-lean-2`.
Each name has a dispatch op of the same name, takes string arguments, and answers
the envelope `bin/npm-entry/entry_extras.ml` answers. `npm/factoidal/lib/api.js`
already held the typed wrappers, so `l4-core.js` lists the op names (`STAGE2_OPS`)
and re-exports the wrappers.

**Maths** (`Wasm/Ops/Maths.lean`): `matrixDeterminant`, `matrixScalarProduct`,
`matrixVectorProduct`, `matrixOuterProduct`, `sigmoidPoints`,
`sigmoidFormulaMathml`. The Lean matrix entry has no reason on an undefined
entry; a scalar `undef` result reports `division-by-zero`, which is the only way
these operations produce one. `sigmoidPoints` refuses a count above 1,000,000
(the F\* entry has no cap).

**VC and DID** (`Wasm/Ops/Vc.lean`): the six crypto functions, the four checks
and `didKeyResolve`.
- Ed25519 goes through the `@[extern]` HACL\* binding of
  `L4Factoidal/Crypto/Ed25519.lean`. `build-wasm.sh` compiles that C into the
  wasm module, so these ops do not use the `hacl-wasm` npm artifact and need no
  `initHacl()` call. SHA-256 is the pure Lean `hashHex`, as
  `skills/crypto-policy/SKILL.md` allows for hashes over public data.
- `L4Factoidal/VC/Credential.lean` namespace `Doc` ports the rest of
  `VC.Credential.fst`: `checkFromString` (`vc_check_from_string`),
  `checkCredentialSubjectFromString`, `checkNoDataLossFromString` and
  `checkRelatedResourceDigestsFromString`. `VC/Context.lean` gained the port of
  `VC.Context.fst`'s type-term resolution, and `VC/Multibase.lean` the lenient
  base64 decoder the digest check needs. The earlier strict layer
  (`checkCredential`, issuer required) is unchanged.
- Differences from the F\* module, in the header of `Credential.lean`: a tab is
  not IRI-shaped, `validFrom` and `validUntil` use the XSD 1.1 lexical mapping, and
  a timezone-less value compares with a timezoned one through the ±14:00 window.

**Envelope parity** (issue 685; `Wasm/Ops/Parse.lean`, `Handles.lean`,
`Syntax/TurtleSerialize.lean`):
- a Turtle, TriG, N-Triples or N-Quads failure answers `error` with
  ` at line L, column C`, and `offset`, `line`, `column`, `format`;
- `parseToDatasetJson` and `datasetOpen` answer `prefixes` (each label once, latest
  binding, declaration order) and the handle keeps them;
- `serializeTurtleWith` and `datasetSerializeWith` take
  `{"prefixes":{label:iri},"literalShorthand":bool}`;
- Turtle output prints INTEGER, DECIMAL, DOUBLE and BooleanLiteral bare when the
  lexical form is the terminal. This follows the F\* change of issue 681; the
  Lean module had carried the quoted-only rule, and its guard was replaced;
- ties in the namespace count keep their order (stable sort), as F\*'s
  `sortWith` does.

**Blank-node scope**: the IO entry (`callIO`, which the wasm wire and the native
CLI use) serves `parseToDatasetJson` and `datasetOpen` through a counter and
prefixes every blank-node label with `d<N>_`, as `scope_dataset_bnodes` does in
the F\* entry. The pure `call` keeps the labels as written, because it has no
counter.

**Loader**: `docs/web/hub/assets/l4/l4factoidal.js` throws an `Error` whose
message is unchanged and whose `.envelope` is the whole `{"ok":false,...}`
document. Without it `l4-core.js` could not pass `line` and `column` to
`entryResult`.

Measured on 2026-10-10 (Lean wasm built by `Wasm/build-wasm.sh`: 7,828,865 bytes,
against 6,359,842 bytes on 2026-09-08; the growth has more causes than stage 2,
and stage 4 measures the sizes):

| Gate | Result |
|---|---|
| `lake build` | exit 0 (1292 jobs) |
| `formal/lean4/Wasm/native-smoke.sh` | 223 pass, 0 fail (out of 223); 152 before stage 2 |
| `lake exe l4vc-probe` | 236 pass, 0 fail (out of 236); 119 before. The new section scores the 117 scorable VCDM 2.0 fixtures: 117 pass, 0 fail (out of 117), the F\* runner's score |
| `node --test test/l4-parity-2.test.js test/l4-core.test.js` | 69 pass, 1 fail, 3 skipped (out of 73). The fail is the existing case "l4-core vs F* engine: same join", which needs the F\* bundle; the 3 skips are the new F\* cross-checks |
| full `node --test` in `npm/factoidal`, base JS against the new wasm | 136 pass, 100 fail, 106 skipped (out of 342) |
| full `node --test` in `npm/factoidal`, stage 2 | 171 pass, 98 fail, 108 skipped (out of 377). The failing names are the base set minus two expected-failure cases that now pass; all 98 need the F\* bundle, which this container does not have (no `web` release exists in `danbri/factoidal-builds`) |
| `tests/lws/server.mjs`, `tests/solid/server/protocol.mjs`, `tests/solid/client/against-own-server.mjs`, `tests/store-host/conformance.mjs` | 8, 12, 7 and 34 pass, 0 fail |

Not measured: the F\* cross-checks in `l4-parity-2.test.js` (matrix and sigmoid
results, the 120 VC fixtures) because no F\* bundle was available. They run when
the bundle is present.

`npm/factoidal/test/l4-parity-2.test.js` holds the npm cases, including a
cross-check of the Ed25519 and SHA-256 results against `node:crypto`, of the
sigmoid against `Math.exp`, of the VC fixtures through the wasm, and, when the F\*
bundle is present, of the maths and the VC verdicts against the F\* engine.

## 6. Stage 1: what landed (2026-10-10)

Everything below is in `danbri/factoidal-core`, branch `claude/wt-npm-lean-1`,
merged with stage 2 (§ 5). Each name has a dispatch op, takes string arguments
and answers the envelope `bin/npm-entry/entry_extras.ml` answers, so
`npm/factoidal/lib/api.js` drives both engines through the same wrappers.
`l4-core.js` lists the op names in `OPS`.

| Names | Dispatch op, module | Entry |
|---|---|---|
| `jsonldToRdf`, `jsonldFromRdf`, `rmlMap`, `csvwToRdf`, `xmlWellformed`, `xpathEval`, `xsltTransform`, `schematronValidate`, `jsonSchemaValidate`, `mathmlEval`, `xformsRecalc`, `rifEval` | same names, `Wasm/Ops/Formats.lean` | `call` and `callIO` |
| `tableauMaterialise`, `tableauDlInconsistent` | same names, `Wasm/Ops/Reasoning.lean` | `call` and `callIO` |
| `queryRaw` | `Wasm/Ops/QueryExtras.lean` | `call` and `callIO` |
| `queryHdt` | `Wasm/Ops/QueryExtras.lean`; the `.hdt` file is the byte region (`blobOps`) | `callBlob` |
| `registerServiceEndpoint`, `clearServiceEndpoints` | `Wasm/Ops/ServiceReg.lean`; the registry is an `IO.Ref` and `queryDataset` and `datasetQuery` read a snapshot of it per query | `callIO` only |
| `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions` | the ops `extRegister`, `extUnregister`, `extClear` existed; `l4-core.js` wraps them and installs `globalThis.__factoidalExtCall` | `callIO` |
| `toanSummation`, `toanProduct`, `toanSimplify`, `toanDiff`, `toanSubst` | the ops existed; `l4-core.js` wraps them | `call` |

`parseToDatasetJson` and `datasetOpen` also read JSON-LD now (`format: 'jsonld'`),
so `parse(text, {format: 'jsonld'})` works on the Lean engine.

Data sources are strings, with no host callback and no network, as in the F\*
entry. A remote JSON-LD `@context`, an `xsl:import` and an external XML entity are
therefore unresolved on both engines. `lib/api.js` changed in two places:
`queryHdt` uses the entry's `queryHdt` when it has one (the F\* bundles have none
and keep the command-line path), and `tableauMaterialise` passes on a `budgetHit`
member when the engine sends one.

### Differences from the F\* engine that the parity run found

The cases of `npm/factoidal/test/l4-parity.test.js` use the inputs and the
expected results of the F\*-engine tests. All of them pass on the Lean engine
unchanged. These are the differences in behaviour outside those cases. Where a
specification decides the answer, it is named; no F\* answer was found wrong
against a specification, and the one F\* limit that the Lean side lifts
(DOCTYPE) is a scope limit of the F\* parser.

- `xmlWellformed`: the Lean parser reads a DOCTYPE with an internal subset
  (XML 1.0 § 2.8) and answers `true` for a document that has one; the F\* byte
  parser has no DOCTYPE production and answers `false`. The F\* answer is a
  scope limit of that parser, documented in its README row.
- `xpathEval`: the Lean evaluator is the full XPath 1.0 evaluator; the F\* one is
  its "Stage 1" subset and answers an error envelope for what it does not
  implement. The Lean result adds two node kinds, `root` and `namespace`. A
  number is its XPath string form (`Infinity`, `NaN`).
- `mathmlEval`: the Lean evaluator also evaluates `vector` and `matrix` and
  answers them as `{kind:'vector', value:[[num,den],...]}` and
  `{kind:'matrix', value:[[[num,den],...],...]}`; F\* answers `undef`. For an
  `undef` the Lean `reason` is one fixed sentence (the Lean evaluator returns no
  finer reason), where F\* names division by zero or the type error.
- `rmlMap`: the iteration format is decided by the mapping's
  `rml:referenceFormulation` (RML Core); the `sourceKind` argument is checked
  and not used. F\* parses the source as `sourceKind` says whatever the mapping
  states. With `rml:referenceFormulation` stated, which RML Core requires for a
  JSON or CSV source whose path does not end in `.json` or `.csv`, the two agree.
- `rifEval`: the envelope has `inputNquads`, `saturatedNquads`, `inputCount`,
  `derivedCount` and `fuel`; the F\* members `rounds` and `engineMs` are not sent
  (the Lean function is pure and has no clock). `lib/api.js` reads
  `saturatedNquads` only.
- `tableauMaterialise` sends `budgetHit` (the work budget of
  `OWL.Mat.materialiseWithBudget` ran out); the F\* function had no budget.
  `tableauDlInconsistent` decides a clash with `OWL.RL.detectClashPlus` after
  the OWL RL closure, one materialisation pass and the closure again, the
  pipeline the Lean OWL probe runs under `--dl`.
- `queryRaw`: the output formats `json`, `csv`, `tsv` and `xml` are the W3C
  SPARQL results formats; the CSV and TSV format has no ASK encoding, so an ASK
  query with those outputs is an error. A CONSTRUCT
  answer has no results format and is an error for `json`, `csv`, `tsv` and
  `xml`. The F\* command-line driver wrote `table` and `ntriples` as display
  formats; the Lean op writes the same two shapes with N-Triples term syntax.
- `registerServiceEndpoint`: a query with `SERVICE <iri>` for an IRI nobody
  registered answers no rows without `SILENT`. SPARQL 1.1 Federated Query makes
  a failed `SERVICE` without `SILENT` an error of the query; the Lean evaluator
  has no error channel for it (`EvalEnv.services`, `SPARQL/Expr.lean`). Not
  changed here, because the same evaluator serves the W3C federated-query suite.
  Tracked as https://github.com/danbri/factoidal/issues/717; fixed in
  danbri/factoidal-core ffbce3c0 (the evaluator now reports the failure). Two
  remaining cases (inside `EXISTS`; nested under an outer `SILENT`) are
  https://github.com/danbri/factoidal/issues/735, with expected-failure cases
  in `npm/factoidal/test/l4-parity.test.js`.
- `csvwToRdf`: with `metadataJson == ''` the table is described by its own
  header row (embedded metadata, CSV on the Web tabular data model); the F\* test
  and the Lean engine give the same counts and subjects. A
  `tableSchema` given as a URL is not fetched (no host callback), as in F\*.

### Gates, 2026-10-10

Measured on the merge of stage 1 and stage 2 (`claude/wt-npm-lean-1`), with the
wasm built by `Wasm/build-wasm.sh` from that tree.

| Gate | Result |
|---|---|
| `lake build` | exit 0 (1302 jobs) |
| `formal/lean4/Wasm/native-smoke.sh` | 282 pass, 0 fail (out of 282); 223 on stage 2 alone, 202 on stage 1 alone |
| `node --test test/l4-parity.test.js` | 55 pass, 0 fail (out of 55) |
| `node --test test/l4-parity.test.js test/l4-parity-2.test.js test/l4-core.test.js` | 124 pass, 1 fail, 3 skipped (out of 128). The fail is "l4-core vs F* engine: same join", which needs the F\* bundle; the 3 skips are the F\* cross-checks of stage 2 |
| full `node --test` in `npm/factoidal` | before stage 1 (base JS, no wasm): 73 pass, 122 fail, 147 skipped (out of 342). After the merge: 227 pass, 98 fail, 108 skipped (out of 433). The 98 failing names are a subset of the 122; each needs the F\* bundle, which this container does not have (no `web` release exists in `danbri/factoidal-builds`) |

The wasm is 9,622,969 bytes on the merged tree; 9,315,536 bytes on the stage 1
tree; 6,359,842 bytes on 2026-09-08. Stage 4 measures the size by cause.

`Wasm/build-wasm.sh` now changes into `formal/lean4` before step 3. Run from the
repository root with no `elan default`, step 3 printed `GEN-FAIL` for all 838
core modules and the script went on (record: `skills/lean4-wasm-export/SKILL.md`).
