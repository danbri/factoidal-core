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

After stage 4 (§ 9) the full module is 10.52 MB raw, 2.07 MB with gzip -9,
and the core module `l4factoidal-core.wasm` (`@factoidal/core/core`) is
5.66 MB raw, 1.07 MB with gzip -9: 3.1 times the F\* full bundle after
compression.

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
   yet measured to be acceptable for a browser default. (Stage 4, § 9: the core
   module is 3.1 times the F\* full bundle compressed. Stage 5, § 10: after
   the repairs of § 10, the Lean engine is within 1.72 times the faster F\*
   bundle on every row and size measured, and faster on parse, SHACL and
   canonicalization at 6,000 triples and above; its wasm memory at 48,000
   triples is 1.2 GB, https://github.com/danbri/factoidal/issues/744.)

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
4. [x] Size profile: a smaller Lean wasm for the browser, from a dispatch table
   that reaches a subset of the library (the role `./lite` had), measured
   against the F\* lite bundle. **Done 2026-10-10** (branch
   `claude/wt-npm-lean-45`): `l4factoidal-core.wasm` and the `./core` entry;
   the record, with the bytes per Lean namespace, is § 9.
5. [x] Speed: the npm benchmark (`tests/perf/l4_vs_fstar_wasm_bench.mjs`) re-run;
   any row where the Lean engine is more than 2 times slower becomes an
   issue before the switch is published. **Done 2026-10-10** (same branch):
   eight rows at three sizes, three stack overflows found and two families
   repaired, the speed gate `npm run test:speed`; the record is § 10.

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
- issue 717, `SERVICE` without `SILENT` to an unregistered endpoint: 1 case (fixed in ffbce3c0; issue 735 had the two remaining cases, fixed on 2026-10-12);
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
  expected failures naming https://github.com/danbri/factoidal/issues/727
  until 2026-10-10, when the Lean engine gained the three functions; the
  cases are now assertions (record:
  `docs/designissues/2026-10-10-lean-geo-distance-fulltext.md`).
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

## 9. Stage 4: the size profile and the core module (2026-10-10)

Branch `claude/wt-npm-lean-45` of danbri/factoidal-core. The tables are from
the build of the branch after its merge with `claude/core-split` (b2ee79fb).

### How the bytes were attributed

`Wasm/build-wasm.sh` links with `wasm-ld --Map`, and
`tools/wasm-size-profile.py` reads the map. Each input object is one Lean
module (`L4Factoidal/SPARQL/Query.c` gives `L4Factoidal_SPARQL_Query.o`), one
core-library module (`Init_…`, `Std_…`), one Lean runtime file, one HACL\*
unit or one Emscripten system-library member, so the map gives the bytes of
code (function bodies) and data (initialised memory: string literals,
constant tables) that the linker KEPT for each module, after
`--gc-sections` dropped what no export reaches. The figures are the sizes
before `wasm-opt -O3`, which Emscripten runs after the link: for the full
module, 11.96 MB of linked code became a 9.98 MB code section. The script
also prints the code and data sections of the final file. Every build writes
`$WORK/<module>.size.md` (by namespace) and `$WORK/<module>.size-modules.md`
(by module).

The build is reproducible: the full module built from the branch base
(16a6be6a) with the map flag is byte-identical to the one the issue-716 merge
built (10,510,450 bytes, sha256 `5da96d60…`).

### What makes up the wasm

Bytes kept by the linker (code + data, before `wasm-opt`), per Lean namespace,
for the full module (`l4factoidal.wasm`) and the core module
(`l4factoidal-core.wasm`) of this branch:

| Namespace | Full: code + data | Core: code + data |
|---|---:|---:|
| L4Factoidal.SPARQL | 1,314,729 | 1,312,325 |
| Init (Lean core library) | 1,292,496 | 1,277,413 |
| L4Factoidal.OWL | 1,031,246 | 249,598 |
| L4Factoidal.Storage | 899,215 | 1,190 |
| Wasm (dispatch and ops) | 898,119 | 239,849 |
| L4Factoidal.Syntax | 683,935 | 660,866 |
| L4Factoidal.SHACL | 510,456 | 510,563 |
| L4Factoidal.RML | 460,437 | 271,079 |
| L4Factoidal.JSONLD | 444,214 | 0 |
| L4Factoidal.ShEx | 396,317 | 0 |
| L4Factoidal.RIF | 324,881 | 0 |
| L4Factoidal.XPath | 291,660 | 224,928 |
| L4Factoidal.XML | 285,927 | 285,069 |
| Std (Lean standard library) | 277,700 | 277,700 |
| L4Factoidal.XSD | 277,660 | 170,299 |
| L4Factoidal.CSVW | 260,612 | 0 |
| Lean runtime (C++) and mimalloc | 248,763 | 243,984 |
| L4Factoidal.RDF | 230,799 | 221,273 |
| L4Factoidal.Codec | 201,736 | 13,199 |
| L4Factoidal.XSLT | 200,002 | 0 |
| Emscripten libc / libc++ / compiler-rt | 186,785 | 186,785 |
| L4Factoidal.CL | 168,817 | 0 |
| HACL\* crypto (C) | 157,582 | 0 |
| L4Factoidal.Text | 157,514 | 156,096 |
| L4Factoidal.MathML | 134,139 | 0 |
| L4Factoidal.Regex | 121,913 | 112,543 |
| L4Factoidal.Geo | 120,000 | 116,574 |
| L4Factoidal.Solid | 104,355 | 0 |
| L4Factoidal.JSONSchema | 101,315 | 0 |
| L4Factoidal.VC | 93,230 | 0 |
| L4Factoidal.RDFS | 88,756 | 76,858 |
| L4Factoidal.HDT | 84,615 | 0 |
| L4Factoidal.Math | 84,582 | 0 |
| L4Factoidal.Crypto | 74,916 | 67,930 |
| L4Factoidal.Fn | 58,222 | 8,751 |
| L4Factoidal.JSON | 55,069 | 51,135 |
| L4Factoidal.LWS | 40,224 | 0 |
| L4Factoidal.XMPP | 32,829 | 0 |
| L4Factoidal.JOSE | 27,993 | 0 |
| L4Factoidal.Proof | 27,506 | 0 |
| L4Factoidal.XForms | 24,616 | 0 |
| others (each under 20,000 in both) | 30,627 | 8,775 |
| **linked total** | **12,506,509** | **6,744,782** |

The largest single modules of the full module, code + data: `L4Factoidal.SPARQL.Parser` 442,058, `L4Factoidal.OWL.Refute` 420,815, `L4Factoidal.XML.Parser` 263,897, `Lean runtime (C++) and mimalloc` 248,763, `L4Factoidal.ShEx.Compact` 246,530, `L4Factoidal.Syntax.Turtle` 227,340, `L4Factoidal.Storage.ShardManifest` 209,643, `L4Factoidal.XSLT.Transform` 192,717, `L4Factoidal.SPARQL.Expr` 189,898, `L4Factoidal.JSONLD.Expand` 188,102, `Emscripten libc / libc++ / compiler-rt` 186,785, `L4Factoidal.SPARQL.Query` 185,927, `L4Factoidal.OWL.RLClosureIndexed` 169,525, `L4Factoidal.XSD.Datatypes` 166,182, `Init.Data.Order.PackageFactories` 160,618.

No namespace dominates: the 10.5 MB is the sum of about forty specifications
of 30 to 1,300 KB each, plus 1.3 MB of Lean's core library, 0.28 MB of its
standard library and 0.44 MB of runtime and C libraries that every module
needs.

### The core module

`l4factoidal-core.wasm` is linked from the same objects as the full module,
with `Wasm/CoreExports.lean` in place of `Wasm/Exports.lean`: the same C
symbols over the dispatch table of `Wasm/CoreDispatch.lean`, which imports
only the op modules of the core subset (parse and serialise Turtle, TriG,
N-Triples and N-Quads in RDF 1.1 and 1.2 and RDF/XML; the lenient parse;
SPARQL 1.1 and 1.2 query and update over text and over dataset handles, with
the §17.6 extension-function and SERVICE registries and `queryRaw`;
RDFC-1.0; the RDFS, RDFS-Plus and OWL 2 RL closures; SHACL). The full table
(`Wasm/Dispatch.lean`) delegates those ops to the core table, so each op has
one arm and both modules answer it with the same envelope;
`Wasm/CoreDispatchTests.lean` checks at build time that the core names and
`Core.fullOnlyOpNames` together are exactly the full table's names, and
compares the two tables' envelopes for a positive and a negative case of each
core family.

To keep the rest of the library out of the core closure, five op modules were
split, with no change of behaviour:
- JSON-LD is a parameter of the parse functions (`ExtraReader` in
  `Wasm/Ops/Parse.lean`); `Wasm/Ops/ParseJsonLd.lean` binds the JSON-LD
  reader and keeps the old names for the full table and `Wasm/Cli.lean`. The
  core table refuses the JSON-LD tags by name.
- `owlIsConsistent` and `owlEntails` (the tableau refuter) moved to
  `Wasm/Ops/ReasonDl.lean`, `shexValidate` to `Wasm/Ops/ShExValidate.lean`,
  `queryHdt` to `Wasm/Ops/QueryHdt.lean`.

The RDF/XML parser needs the XML parser, so `L4Factoidal.XML` is in the core
module (0.29 MB); XPath, XSLT, Schematron and the XML ops are not.

**A cost paid during the split.** `OWL.RL.closureFix` is the scanning
specification; the `@[csimp]` theorem `closureFix_eq_indexed` in
`OWL/RLClosureIndexed.lean` makes the compiler emit the indexed closure for
every call, but only in a module where that theorem is imported.
`Wasm/Ops/Reason.lean` had it through `OWL.Refute`; when the OWL DL ops moved
out, the import went with them and `owlClosure` compiled to the scanning
closure (100 to 500 times slower on large inputs, per
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`). The size table
showed it first: `L4Factoidal.OWL.RLClosure` grew by 113,186 bytes, because
the scanning rules were reachable again. `Reason.lean`, `ReasonDl.lean` and
`QueryExtras.lean` now import `OWL.RLClosureIndexed` explicitly, with the
reason beside the import (`skills/lean4-performance/SKILL.md`, "A csimp
replacement needs its import").

**What is still in the core module and is not core function.** 0.27 MB of
`L4Factoidal.RML` and 0.22 MB of `L4Factoidal.XPath` (with 0.01 MB of
`Codec`): `SPARQL.StoreBackend` has a `virtualRml` backend (an RML mapping as
a virtual graph), the SPARQL store dispatch matches on every backend, and
`Wasm/Ops/Query.lean` reaches that dispatch through `SPARQL.StoreDataset`. The
RML evaluator brings its XPath reference formulation. Taking the RML backend
out of the core closure is a change to `L4Factoidal/SPARQL` (the backend set
becomes a parameter, as the parse readers did here); it is issue text in the
stage 5 report, not done here. `L4Factoidal.Geo` (0.12 MB) is the GeoSPARQL
`geof:` functions of the §17.6 table, which the SPARQL ops serve.

### Sizes

`gzip -9` is GNU gzip; brotli is quality 11 (Node `zlib.brotliCompressSync`,
no brotli command is installed in the container).

| Artifact | Raw | gzip -9 | brotli 11 |
|---|---:|---:|---:|
| Lean full `l4factoidal.wasm` (`@factoidal/core`) | 10,539,680 | 2,071,197 | 1,291,982 |
| Lean core `l4factoidal-core.wasm` (`@factoidal/core/core`) | 5,681,117 | 1,071,262 | 691,533 |
| F\* full `factoidal-npm-entry.js` (js_of_ocaml) | 1,187,678 | 348,212 | 281,669 |
| F\* lite `factoidal-npm-entry-lite.js` (js_of_ocaml) | 603,188 | 174,453 | 141,000 |
| F\* full wasm_of_ocaml code (`code-f5f9….wasm`, + 45,244 B loader) | 1,472,107 | 370,352 | 288,326 |
| F\* lite wasm_of_ocaml code (`code-f4c2….wasm`, + 43,180 B loader) | 692,013 | 176,281 | 138,252 |

The F\* bundles are those of factoidal-builds `build-0c834393910d-web`. Each
Lean module also loads 67,928 (full) or 67,991 (core) bytes of JavaScript with
gzip -9 (the entry, `lib/`, `rdfjs.mjs`, the loader and Emscripten's glue).

These are the modules of the branch after its merge with core-split; the
full module of the branch base was 10,510,450 bytes (2,067,201 with gzip).
The core module is 54 percent of the full module raw and 52 percent with gzip.
It is 3.1 times the F\* full js_of_ocaml bundle with gzip and 6.1 times the F\*
lite bundle. The core subset removed the specifications the core does not
serve; what remains is the specifications it serves plus the Lean core
library and runtime (1.8 MB of the 6.7 MB linked), and the stray RML and XPath
above (0.5 MB).

### Which module a page loads

The browser default stays the full module: `.` (its `browser` condition),
`./browser` and the hub load `l4factoidal.wasm`. `./core` loads the core
module, in Node (`core.mjs`, `core.js`) and in the browser (its `browser`
condition, `core-browser.js`). Reasons, measured above: the core module
halves the download (1.07 MB against 2.07 MB with gzip) but is still 3.1
times the F\* bundle the browser default used to load, so making it the
default does not restore the F\* download size; and a core default would make
every function outside the subset (the XML family, JSON-LD, the store, VC,
the maths) reject for every page that does not opt in, the hub's posts
included. A page that needs only the core subset imports
`@factoidal/core/core`. This is a coordinator-level default for issue 713
stage 4, not an owner decision.

### The core entry in npm

| File | Role |
|---|---|
| `core.mjs`, `core.js` | Node: the exports of `index.mjs` over `bin/engine.mjs`'s `loadEngine('l4factoidal-core')` |
| `core-browser.js` | browser: the exports of `browser.js` over `lib/browser-engine.mjs`'s loader of `l4factoidal-core.{js,wasm}` |
| `core.d.ts`, `core-browser.d.ts` | the types of `index.d.ts` and `browser.d.ts` |
| `l4-assets/l4factoidal-core.{js,mjs,wasm}` | the module; the loader is generated by `build-wasm.sh` from `l4factoidal.js` (step 8), stamped with the core module's hash |

The `ops` reflection carries `"engine":"core"` or `"engine":"full"`, and the
core module's also `fullOnlyOps` and `fullOnlyFormats`. `capabilities()`
reports `profile: 'core'` and `false` for every function the core module
does not serve. A function outside the subset rejects with an `Error` whose
message names the entry that has it:
`xpathEval: the op 'xpathEval' is not in the core engine that
'@factoidal/core/core' loads (l4factoidal-core.wasm); import
'@factoidal/core', whose full engine (l4factoidal.wasm) serves it`. The raw
dispatch refusal of the core module has `"servedBy":"full"`.

### A defect the speed rows found in the wrapper

`rdfjs.mjs`'s `Dataset` kept set semantics by scanning: `add()` called
`has()`, which compared the quad with every quad already held, so building a
Dataset of n quads cost n²/2 `equals()` calls on both engines. `parse()` of
12,000 quads spent 3.1 s of its 3.3 s there (the engine call itself was
0.42 s). The Dataset now keeps a `Set` of quad keys, one key per `equals()`
class; the same parse takes 0.35 s. `test/dataset-scaling.test.js` checks the
set semantics and that 4n quads cost at most 9 times n.

### Gates (stages 4 and 5)

Measured on the branch after its merge with core-split (b2ee79fb, then the
documentation commits), with the modules `Wasm/build-wasm.sh` built from that
tree installed in `npm/factoidal/l4-assets/`.

| Gate | Result |
|---|---|
| `lake build` (in `formal/lean4`) | exit 0 (1366 jobs); `Wasm/CoreDispatchTests.lean` and the new `#guard`s and theorems check |
| `formal/lean4/Wasm/native-smoke.sh` | 310 pass, 0 fail (out of 310); 7 of them drive the core table through `l4wasm-cli corecall`; 303 before |
| `cd npm/factoidal && npm ci --ignore-scripts && npm test` | 403 pass, 0 fail, 0 skipped (out of 403), 5 of them expected failures (issues 735 (2), 691 (1), 676 (2)); new: `test/core-entry.test.mjs` 23, `test/dataset-scaling.test.js` 2, `test/large-inputs.test.mjs` 4 |
| `node --test tests/hub/*_test.mjs` | 445 pass, 0 fail (out of 445), 18 of them expected failures |
| `tests/web-demos/npm_browser_smoke.sh` | PASS for both entries: full entry 873 ms to settle, core entry 350 ms |
| `tests/web-demos/bundler_csp_smoke.sh` | PASS |
| `npm run test:speed` | 8 pass, 0 fail, 1 expected failure (out of 9), § 10 |

The Lean changes add no `sorry`, `axiom`, `native_decide`, `unsafe`,
`implemented_by` or `partial def`.

## 10. Stage 5: speed against the F\* bundles (2026-10-10)

### Method

`tests/perf/l4_vs_fstar_wasm_bench.mjs` runs each row through the package's
typed API on three engines: the Lean full module (`@factoidal/core`, from
`npm/factoidal/l4-assets/`), and the F\* npm-entry bundles of factoidal-builds
`build-0c834393910d-web` loaded by path from `docs/fstar-extracted/`,
wasm_of_ocaml (`factoidal-npm-entry.wasm.js`) and js_of_ocaml
(`factoidal-npm-entry.js`), through the same `lib/api.mjs` wrappers. Each
(engine, row, size) runs in its own Node 22.22.0 child process. The time is
the median of 5 runs after one warmup run that also checks the answer (a run
of more than 5 s is measured once); an engine whose run at one size took more
than 10 s is not run at the next size (4 times the input), and the row says
so. Memory: `wasmMemoryBytes` is the Lean module's linear memory at the end of
the child (it only grows, so it is the high-water mark of all six runs);
`maxRssMB` is the child's peak resident set. The 1-minute load average is in
each JSON line: the container's 4 CPUs were shared with two other agents and
the load was 2 to 12 during the run, so wall times carry that noise.

K people, each with an `rdf:type`, a `:name` and an `:age` (3K triples).
Sizes: K = 1,000, 4,000 and 16,000 for the parse and query rows; 500, 2,000
and 8,000 for canonicalize (every person a blank node) and SHACL (a shape
with `sh:targetClass`, `sh:minCount`, `sh:datatype`, `sh:maxInclusive`; one
person in 60 violates the last).

Two defects of the measurement path were found and repaired before the run
below: the `Dataset` of `rdfjs.mjs` was quadratic (§ 9; it cost both engines
3 s at 12,000 quads), and the F\* wasm_of_ocaml bundle cannot load under an ES
module main (it reads `require.main.filename` to find its code file; the
bench and `tools/deltalog-bench/bench-js-wasm.mjs` now name the bundle as the
main module).

### Results

One run of the whole matrix (`node tests/perf/l4_vs_fstar_wasm_bench.mjs`),
all three engines in the same run, Lean full module of this branch before the
stack repairs below (load average 2.0 to 11.6):

| Row | Triples | Lean ms | F\* wasm ms | F\* js ms | Lean / faster F\* | Lean linear memory MB | Lean max RSS MB | F\* js max RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| parse-turtle | 3,000 | 53.3 | 668.1 | 352.0 | 0.15 | 53 | 137 | 132 |
| parse-turtle | 12,000 | 223.7 | 11,304.6 | 1,671.4 | 0.13 | 128 | 250 | 189 |
| parse-turtle | 48,000 | 1,189.3 | not run | 6,645.1 | 0.18 | 1,226 | 609 | 304 |
| parse-nquads | 3,000 | 118.9 | 626.3 | 453.0 | 0.26 | 53 | 146 | 132 |
| parse-nquads | 12,000 | 505.4 | 10,434.8 | 1,670.4 | 0.30 | 132 | 238 | 189 |
| parse-nquads | 48,000 | 2,159.7 | not run | 8,181.1 | 0.26 | 1,224 | 664 | 241 |
| select-join | 3,000 | 135.6 | 112.0 | 222.7 | 1.21 | 53 | 167 | 145 |
| select-join | 12,000 | 525.2 | 563.9 | 1,780.7 | 0.93 | 154 | 271 | 196 |
| select-join | 48,000 | error | 2,536.7 | 6,400.2 | - | - | - | 487 |
| order-by | 3,000 | 165.6 | 76.4 | 317.4 | 2.17 | 53 | 160 | 135 |
| order-by | 12,000 | 592.5 | 538.3 | 1,124.5 | 1.10 | 154 | 266 | 233 |
| order-by | 48,000 | error | 1,764.3 | 6,187.6 | - | - | - | 422 |
| group-by | 3,000 | 157.9 | 77.7 | 240.7 | 2.03 | 53 | 159 | 130 |
| group-by | 12,000 | 408.6 | 377.9 | 874.2 | 1.08 | 154 | 274 | 240 |
| group-by | 48,000 | 2,103.8 | 1,805.4 | 5,359.3 | 1.17 | 1,304 | 680 | 410 |
| count-distinct | 3,000 | 169.9 | 89.3 | 426.2 | 1.90 | 53 | 189 | 128 |
| count-distinct | 12,000 | 512.8 | 367.2 | 1,245.6 | 1.40 | 154 | 270 | 248 |
| count-distinct | 48,000 | 2,460.5 | 2,626.8 | 6,780.7 | 0.94 | 1,304 | 717 | 460 |
| canonicalize | 1,500 | 206.3 | 117.1 | 405.9 | 1.76 | 53 | 134 | 121 |
| canonicalize | 6,000 | 1,819.6 | 5,393.0 | 2,023.0 | 0.90 | 84 | 151 | 183 |
| canonicalize | 24,000 | error | error | error | - | - | - | - |
| shacl | 1,500 | 176.9 | 381.1 | 822.2 | 0.46 | 53 | 136 | 110 |
| shacl | 6,000 | 688.3 | 3,085.4 | 4,277.8 | 0.22 | 106 | 182 | 160 |
| shacl | 24,000 | 1,506.4 | error | error | - | 1,246 | 458 | - |

"not run": the F\* wasm_of_ocaml parse took 11.2 s (Turtle) and 10.2 s
(N-Quads) for one run at 12,000 triples, so the 48,000-triple size was not
run (the bench's 10 s rule; both F\* bundles are quadratic in `parse()`:
js_of_ocaml 1.7 s at 12,000, 6.6 s at 48,000). "error" is explained below.

### Three stack overflows, two repaired here

At 48,000 triples the Lean module failed `select-join` and `order-by` with
`RangeError: Maximum call stack size exceeded`, and all three engines failed
`canonicalize` of 24,000 blank-node quads (the F\* js_of_ocaml bundle with
`Stack overflow`, the F\* wasm_of_ocaml bundle with a `WebAssembly.Exception`).
The native Lean build answers the same SELECT with a 512 KB stack: native
frames are small and the native stack is 8 MB, so a recursion of one frame
per row stays hidden there; under Node's default stack (about 1 MB) the wasm
module overflows at about 11,000 rows. A link with `--profiling-funcs` (a
module that keeps function names) gave each overflow's function:

| Function | Pattern | Repair |
|---|---|---|
| `SPARQL.numberRows` (`SPARQL/Query.lean`), numbering the rows of every SELECT with a projection | `f row :: numberRows rest` | `numberRowsTR` (reverse accumulator), `@[csimp] numberRows_eq_numberRowsTR`, proved by `numberRowsTR_go_eq` |
| `SPARQL.rowsJoined` (`SPARQL/ResultsJson.lean`), the SPARQL Results JSON writer | `rowJson r ++ "," ++ rowsJoined rest`: one frame per row, and the rest of the document copied once per row | `rowsJoinedTR` (one accumulator), `@[csimp] rowsJoined_eq_rowsJoinedTR`, proved by `rowsJoined_cons` and `rowsJoinedTR_go_eq` |
| `RDF.Canonical.collapseKeyedQQuads` and `RDF.Canonical.dedupAdj` (`RDF/Canonical.lean`), duplicate removal before hashing and on the output lines | `q :: collapse rest`, `x :: dedupAdj rest` | `collapseKeyedQQuadsTR`, `dedupAdjTR`, with `@[csimp]` theorems proved the same way |

The specifications are unchanged (the theorems in `ResultsTheorems.lean` and
`CanonicalTheorems.lean` still state their properties of `rowsJoined` and
`dedupAdj`); the `csimp` theorems make the compiler emit the accumulator forms.
`npm/factoidal/test/large-select.test.mjs` runs a SELECT of 20,000 solutions,
stateless and on a dataset handle with ORDER BY, on both entries: 2 fail on
the module built before the repairs, 2 pass after.

After the two `RDF.Canonical` repairs the Lean module canonicalizes 24,000
blank-node quads on Node's default stack, which neither F\* bundle does. It is
slow there: 16.9 s in the bench (one run) and 10.3 s in a gate run, against
0.76 s and 1.03 s at 6,000 quads, 22 and 9.9 times the time for 4 times the
input. That is https://github.com/danbri/factoidal/issues/745, held by the gate until its repair as `SCALING_XFAIL['canonicalize']`
(bound: 9 times). The profile and the repair are in "Issue 745: where
canonicalization spent its time" below.

The Lean module after the repairs (Lean only, same sizes and inputs; load
average 6 to 12, so these times are noisier than the table above; the ratio
divides by the F\* time of the table above):

| Row | Triples | Lean ms | Lean / faster F\* (F\* from the table above) | Lean linear memory MB |
|---|---:|---:|---:|---:|
| select-join | 3,000 | 121.2 | 1.08 | 53 |
| select-join | 12,000 | 551.1 | 0.98 | 154 |
| select-join | 48,000 | 2,934.7 | 1.16 | 1,304 |
| order-by | 3,000 | 169.6 | 2.22 | 53 |
| order-by | 12,000 | 668.0 | 1.24 | 154 |
| order-by | 48,000 | 3,042.9 | 1.72 | 1,304 |
| group-by | 3,000 | 260.6 | 3.35 | 53 |
| group-by | 12,000 | 593.9 | 1.57 | 154 |
| group-by | 48,000 | 2,801.5 | 1.55 | 1,304 |
| count-distinct | 3,000 | 275.9 | 3.09 | 53 |
| count-distinct | 12,000 | 520.9 | 1.42 | 154 |
| count-distinct | 48,000 | 2,192.2 | 0.83 | 1,304 |
| canonicalize | 1,500 | 179.1 | 1.53 | 53 |
| canonicalize | 6,000 | 761.1 | 0.38 | 84 |
| canonicalize | 24,000 | 16,916.7 | - (no F\* answer) | 190 |
| shacl | 1,500 | 113.7 | 0.30 | 53 |
| shacl | 6,000 | 339.1 | 0.11 | 106 |
| shacl | 24,000 | 1,843.6 | - (no F\* answer) | 1,246 |

### Rows where the Lean engine is more than 2 times slower

In the first matrix run, two rows were above the bound: ORDER BY at 3,000
triples (2.17 times the faster F\* bundle) and GROUP BY at 3,000 triples (2.03),
at a load average of 6.5 to 7.7. Both run `query(ds, q)` on a parsed `Dataset`:
the wrapper sends the dataset to the engine as N-Quads text, and the Lean op
parses and indexes it on every call. That is most of the time at this size
(GROUP BY on a dataset handle, which parses once: 10.7 ms; stateless: 127 ms).
After the `rowsJoined` repair above (the Results JSON writer had copied the
rest of the document once per row) the same two rows measure 1.27 and 1.43
(gate run at `--size small`, load average 6.2), and every other row at every
size is at most 1.72 (COUNT(DISTINCT) at 3,000 triples). So no row is more
than 2 times slower and no speed issue is opened. A caller that queries one
dataset repeatedly gets the parse-once path from `openDataset()`.

Two defects that are not speed rows are recorded as issues (https://github.com/danbri/factoidal/issues/745 is the
canonicalization scaling above):

- **https://github.com/danbri/factoidal/issues/744, linear memory.** `parse()` of 48,000 triples raises the Lean
  module's linear memory to 641 MB after one call and to 1,227 MB after six;
  the native build of the same op peaks at 388 MB resident, and the F\* js
  bundle's child process at 304 MB. Linear memory never shrinks and wasm32
  stops at 4 GB; at 13 KB of linear memory per triple for one call, that
  limit is near 300,000 triples (an extrapolation from these sizes, not a
  measurement). The gate holds it as `MEMORY_XFAIL['parse-turtle@large']`
  (bound 256 MB).

### The speed gate

`tests/perf/npm_speed_gate.mjs` (`cd npm/factoidal && npm run test:speed`;
not part of `npm test`) runs each row at its middle size on the three
engines, plus the sizes its expected-failure keys name, and requires the Lean
time to be at most 2 times the faster F\* bundle. `XFAIL` holds
no row (it held `order-by@small` and `group-by@small` until the repairs
above). `MEMORY_XFAIL` holds `parse-turtle@large` with a bound of 256 MB of
linear memory (https://github.com/danbri/factoidal/issues/744). Since 2026-10-12 that key is asserted in `MEMORY` and
`MEMORY_XFAIL` is empty: 184 MB after the six calls (the envelope's string
escape without a character list, and 128 MiB allocator arenas on wasm32;
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md` section 11). `SCALING_XFAIL` held `canonicalize`: the Lean
time at 24,000 quads at most 9 times the time at 6,000 (https://github.com/danbri/factoidal/issues/745); since
the repair below, `SCALING` asserts that bound and `SCALING_XFAIL` is empty. Each
expected failure turns the gate red when it passes. Without the F\* bundles
the gate exits 2. The placeholder issue URLs
`https://github.com/danbri/factoidal/issues/744` and `…/https://github.com/danbri/factoidal/issues/745` are for the
coordinator to replace with the issues it opens.

Final run on the branch after its merge with core-split (b2ee79fb), load
average 9.8 on 4 CPUs:

```
xfail memory parse-turtle@large (48000 triples): Lean linear memory 1227 MB, bound 256 MB
ok    parse-turtle@middle (12000 triples): Lean 306.1 ms, best F* 1621 ms, ratio 0.19
ok    parse-nquads@middle (12000 triples): Lean 599 ms, best F* 1860.4 ms, ratio 0.32
ok    select-join@middle (12000 triples): Lean 611.2 ms, best F* 427.8 ms, ratio 1.43
ok    order-by@middle (12000 triples): Lean 606.6 ms, best F* 343.2 ms, ratio 1.77
ok    group-by@middle (12000 triples): Lean 582 ms, best F* 411.2 ms, ratio 1.42
ok    count-distinct@middle (12000 triples): Lean 456.9 ms, best F* 354.9 ms, ratio 1.29
ok    canonicalize@middle (6000 triples): Lean 941.1 ms, best F* 1833.7 ms, ratio 0.51
ok    shacl@middle (6000 triples): Lean 368.9 ms, best F* 2231.7 ms, ratio 0.17
npm_speed_gate: 8 pass, 0 fail, 1 expected failures (out of 9)
```

The scaling row was added after that run; alone (`--rows canonicalize`,
load average 7.1): `xfail scaling canonicalize: Lean 1033.3 ms at 6000
triples, 10265.9 ms at 24000 triples, bound 9 times`; `canonicalize@middle`
ratio 0.69. ORDER BY at 12,000 triples measured 1.10, 1.24, 1.60 and 1.77 in
four runs at load averages from 5 to 10: it is the row nearest the bound.

### Issue 745: where canonicalization spent its time

Profiled natively first: `l4factoidal canonicalize` runs the same
`RDF.Canonical.canonicalize` as the wasm op `canonicalizeToNQuads` (through
`Ops.canonicalizeOf`). Input: the bench's canonicalize row, k blank-node
persons with an `rdf:type`, a `:name` and an `:age` (3k quads; every
first-degree hash is unique, so §4.4 step 5 has no collision group).
Wall and user time, one run each, load average about 5 on 4 shared CPUs:

| k (blank nodes) | quads | before: wall | before: user | after: wall | after: user |
|---:|---:|---:|---:|---:|---:|
| 1,000 | 3,000 | 0.25 s | 0.13 s | 0.15 s | 0.08 s |
| 2,000 | 6,000 | 0.54 s | 0.45 s | 0.18 s | 0.16 s |
| 4,000 | 12,000 | 2.23 s | 1.88 s | 0.35 s | 0.31 s |
| 8,000 | 24,000 | 9.49 s | 8.82 s | 1.19 s | 0.77 s |

The output is byte-identical before and after at all four sizes (`cmp`).

`valgrind --tool=callgrind`, inclusive instructions in millions:

| phase | 1,000 | 2,000 | 4,000 |
|---|---:|---:|---:|
| whole program, before | 1,433 | 4,043 | 13,809 |
| `hfdqTableOf` (§4.4 step 3: §4.5 for every blank node) | 829 | 2,814 | 10,863 |
| of which the `quadsForBnode` filter | 659 | 2,473 | 10,181 |
| `relabelDataset` (`lookupMap`) | 67 | 186 | 879 |
| `readDataset` (N-Quads parse) | 174 | 348 | 697 |
| command line JSON envelope (`okWith` + `parseEnvelope`) | 219 | 442 | 886 |
| whole program, after | - | 1,436 | 2,862 |
| `hfdqTableOfIx`, after | - | 399 | 810 |

The phase that grew superlinearly was the first-degree hash table: 3.4 and
3.9 times per doubling, 79 percent of the instructions at 4,000 blank nodes.
`hashFirstDegreeQuads` found the quads of its blank node with
`quadsForBnode`, a filter over every quad of the dataset, and `hfdqTableOf`
called it once per blank node: 8,000 blank nodes in 24,000 quads cost 192
million calls of `quadMentionsBnode`. The second was `relabelDataset`: the
label of each blank-node occurrence was found by `lookupMap`, a scan of the
issued list (one entry per blank node). RDFC-1.0 §4.4 step 2 builds a "blank
node to quads map" once; the port had replaced it with a filter per blank
node. The insertion sort that the 2026-10-10 tail-recursion work changed
(`insertSortedBy`) is still quadratic in time, but `sortBy` runs only on
the blank nodes left unissued after fuel exhaustion, which no input reaches:
it is not in the profile.

The repair (`RDF/Canonical.lean`, specification definitions unchanged):

- `bnodeQuadIndex`: the §4.4 step 2 map, a `Std.TreeMap` from a blank node
  to its quads, built in one pass. `quadsForBnodeIx_bnodeQuadIndex` proves
  it returns the list `quadsForBnode` returns, order included, for every
  blank node; `hfdqTableOf_eq_hfdqTableOfIx` follows, and
  `@[csimp] hfdqTableOf_eq_Ix` makes the compiler emit the indexed form.
- `labelTree`: the issued list as a `Std.TreeMap`, inserted last entry
  first so that the first entry of a label wins, as in `lookupMap`
  (`labelTree_get?`). `relabelDatasetBy` is the relabelling walk over any
  lookup function; `relabelDataset_eq_by` and `@[csimp]
  relabelDataset_eq_fast` make the compiler build the tree once per call.
- `CanonicalTests.lean` compares the indexed forms with the scanning
  definitions written out in the test module (a guard on `hfdqTableOf`
  alone would compare one program with itself), on a fixture with a blank
  node twice in one quad, a blank-node graph name and a blank node inside
  an RDF 1.2 triple term.

RDFC-1.0: 86 pass, 0 fail (out of 86) before and after (`l4w3c` on
`third_party/testing/rdf-canon/tests/manifest.ttl`).
`tests/stack/lean_scaling.py` has the input as row `rdfc-bnode-unique`
(2,000 and 8,000 blank nodes, bound 9 times): ratio 13.1 on the binary
before the repair (fail), 4.4 after (pass).

A second shape is still quadratic and is now
https://github.com/danbri/factoidal/issues/751: blank nodes that share one
first-degree hash (`_:p{i} rdf:type ex:Person`), so §4.4 step 5 runs Hash
N-Degree Quads for each. 0.16 s at 2,000 blank nodes, 2.37 s at 8,000,
11.62 s at 16,000 (user time). `hndqRun` does not get the map, so
`buildBucketsFor` filters every quad once per call (761 million
instructions at 2,000, 3,139 million at 4,000), and the issuer's
`lookupIssued` scan and `issued ++ [x]` append grow the same way. The row
`rdfc-bnode-collide` holds it as an expected failure naming that issue.
Repaired on 2026-10-13: see "Issue 751" below.

The wasm module rebuilt from this change (`Wasm/build-wasm.sh`; full module
10,666,063 bytes, core module 5,821,908 bytes), copied into
`npm/factoidal/l4-assets`, two runs of the whole speed gate
(`node tests/perf/npm_speed_gate.mjs`, Node 22.22.0, load average 3.0 and
3.1 on 4 CPUs). Before the change the gate measured 1,033 ms and 10,266 ms
for the same row (above):

| run | Lean, 6,000 quads | Lean, 24,000 quads | ratio (bound 9) | `canonicalize@middle` against the faster F\* bundle |
|---|---:|---:|---:|---:|
| 1 | 271.1 ms | 1,258.9 ms | 4.6 | 291 ms against 969.7 ms, 0.30 |
| 2 | 253.1 ms | 1,122.6 ms | 4.4 | 277.1 ms against 890.1 ms, 0.31 |

Both runs: `npm_speed_gate: 9 pass, 0 fail, 1 expected failures (out of
10)`; the expected failure is `parse-turtle@large` memory
(https://github.com/danbri/factoidal/issues/744). The gate's `SCALING`
list now asserts `canonicalize` (a time above the bound is a failure), and
`SCALING_XFAIL` is empty.

Other gates on the same tree: `Wasm/native-smoke.sh` 347 pass, 0 fail (out
of 347); `npm test` in `npm/factoidal` 402 pass, 0 fail, 1 skipped (out of
403; the skip needs the `esbuild` devDependency); `tests/stack/lean_scaling.sh`
18 pass, 0 fail, 3 expected-fail (out of 21);
`tools/lean-tail-recursion-audit.py --gate` passes (one new allow-list line,
`relabelTermBy`, whose depth is the RDF 1.2 triple-term nesting, as for
`relabelTerm`); `lake build` exit 0 (1382 jobs).

### Issue 751: blank nodes that share one first-degree hash

Input: k quads `_:p{i} rdf:type ex:Person .` (the `rdfc-bnode-collide` row of
`tests/stack/lean_scaling.py`). Every blank node has the same first-degree
hash (§4.5), so §4.4 step 5 puts all k in one collision group and runs Hash
N-Degree Quads (§4.7) once for each. The callgrind table in the issue put
the time in two places, both growing about 4 times per doubling:

1. `hndqRun` gave `buildBucketsFor` (§4.7 step 3) every quad of the
   dataset, and `buildBucketsFor` tested each one with `quadMentionsBnode`,
   once per call: 3,139 of 5,168 million instructions at 4,000 blank nodes.
2. `IssuerState.issued` is a list. `issueIdentifier` (§4.8) scanned it with
   `lookupIssued` and appended with `issued ++ [x]`; the §4.4 step 5.3
   replay (`replayAll`, `replayOne`) does that once per blank node, and
   `filterUnissued`, `exploreMembers` and `lookupIssued2` scan it once per
   blank node or related blank node: 482 million instructions at 4,000.

The repair (`RDF/Canonical.lean`, section "Hash N-Degree Quads through the
map, with an indexed issuer"; every definition above it is unchanged):

- **The map reaches §4.7.** A `csimp` theorem on `buildBucketsFor` alone
  would rebuild the map on every call, because `buildBucketsFor` gets one
  blank node. `buildCanonicalMappingBudgetedFast` builds `bnodeQuadIndex`
  once, uses it for the first-degree hashes (§4.4 step 3, so the map is
  built once and not twice) and passes it down through `walkGroupsF`,
  `processCollisionGroupsF`, `processCollisionMembersF`, `exploreMembersF`
  and `hndqRunF`, which gives `buildBucketsForF` the quads of its blank node
  only (`quadsForBnodeIx`). `buildBucketsFor_filter` proves that
  `buildBucketsFor` gives the same buckets over the quads of its blank node
  alone, and `quadsForBnodeIx_bnodeQuadIndex` (from issue 745) proves the map
  answers that list.
- **The issuer gets a search tree.** `FIssuer` keeps the issued list as
  `front ++ backRev.reverse`: `issueFresh` (§4.4 step 4) adds to the front
  and `issueIdentifier` adds to the back, so the order is not one direction
  and both ends must take a constant-time addition. A `Std.TreeMap` beside
  it answers `lookupIssued`; the field `tree_get` states that agreement for
  every blank node, so each value carries its own proof and no lemma needs a
  hypothesis about the tree. `FIssuer.toSpec` gives the `IssuerState` a value
  stands for. `FIssuer.issue_toSpec` and `FIssuer.issueFresh_toSpec` prove
  that issuing on the fast form gives the same label and the same list.
- **The first-degree hashes get a search tree.** `lookupHfdq` scanned the
  table once per related blank node (§4.6 step 3). The twins read
  `labelTree` of the table (`labelTree_get?`, `lookupHfdq_eq_lookupMap`).
- **Every twin is proved equal through `toSpec`.** The theorems are
  `insertRelatedEntriesF_eq`, `buildBucketsForF_eq`, `buildPathLabelsF_eq`,
  `walkRecursionF_eq`, `walkPermF_eq`, `pickBestF_eq`,
  `bestPermutationF_eq`, `walkBucketsF_eq`, `hndqRunF_eq` (induction on the
  fuel; the closure argument `HndqRec` of each walker becomes a hypothesis
  that the fast closure maps to the slow one), `assignSingletonsF_toSpec`,
  `filterUnissuedF_eq`, `exploreMembersF_eq` (the twin is a loop on a
  reverse accumulator), `replayOneF_toSpec`, `replayAllF_toSpec`,
  `processCollisionMembersF_eq`, `processCollisionGroupsF_eq`,
  `walkGroupsF_eq` and `foldl_issue_toSpec`. They give
  `buildCanonicalMappingBudgeted_eq_fast`, a `csimp` theorem: the compiler
  emits the twin for `buildCanonicalMapping`, `canonicalizeExceedsBudget`,
  `canonicalize` and `Dataset.canonicalLines`. The issued identifiers, in the
  order the definition gives them, are unchanged. `#print axioms`:
  `propext`, `Classical.choice`, `Quot.sound`.
- `CanonicalTests.lean` runs `issueIdentifier`, `issueFresh` and
  `walkGroups` (no `csimp` of their own, so the definitions run) beside the
  twins: on 12 blank nodes with one shared hash, on the two §4.2 examples of
  the Recommendation and on a two-node cycle and chain. The negative guards
  give the twin an empty map and check that the result changes where §4.7
  has buckets to fill, and check that a blank node not yet issued gets a new
  label.

Measured, `l4factoidal canonicalize FILE --format nquads`, linux x86_64,
Lean 4.33.1, 4 CPUs shared with other work (load average 4 to 8), under
`/usr/bin/time` (user CPU seconds, peak resident memory). "Before" is one run
per point (the 64,000 point takes 5.5 minutes); "after" and the two
reference implementations are the minimum of 3 runs (rdf-canonize at 64,000:
one run). The output is byte-identical before and after at every size
(`cmp`), and the outputs of the two reference implementations and of the
wasm module are byte-identical to it at every size:

| blank nodes | Lean before | Lean after | Oxigraph | rdf-canonize | after / Oxigraph |
|---:|---:|---:|---:|---:|---:|
| 2,000 | 0.16 s, 24 MB | 0.07 s, 26 MB | 0.02 s, 27 MB | 0.14 s, 66 MB | 3.5 |
| 4,000 | 0.59 s, 33 MB | 0.14 s, 33 MB | 0.05 s, 32 MB | 0.26 s, 75 MB | 2.8 |
| 8,000 | 2.66 s, 45 MB | 0.27 s, 47 MB | 0.09 s, 41 MB | 0.64 s, 87 MB | 3.0 |
| 16,000 | 10.83 s, 70 MB | 0.54 s, 70 MB | 0.19 s, 59 MB | 2.02 s, 115 MB | 2.8 |
| 64,000 | 327.67 s, 222 MB | 2.66 s, 222 MB | 0.96 s, 167 MB | 37.80 s, 197 MB | 2.8 |

The same inputs through the npm package with the wasm module rebuilt from
this tree (`canonicalize(text, {format: 'nquads'})`, Node 22.22.0, one run,
user CPU seconds and peak resident memory of the whole Node process, module
instantiation included): 0.70 s, 0.89 s, 1.18 s, 1.86 s and 5.73 s; 134 MB,
138 MB, 139 MB, 172 MB and 412 MB. The wasm module from before the change was
not measured.

The reference implementations, installed into `/tmp` only (not vendored):

- Oxigraph: `python3 -m venv /tmp/rc-sota/py/venv; /tmp/rc-sota/py/venv/bin/pip
  install pyoxigraph` (pyoxigraph 0.5.11, the Rust Oxigraph library). The
  script parses the N-Quads file into `pyoxigraph.Dataset`, calls
  `canonicalize(CanonicalizationAlgorithm.RDFC_1_0)` and prints the quads
  sorted in code point order. Its time includes Python start-up (about 0.02 s).
- rdf-canonize: `npm install rdf-canonize` in `/tmp/rc-sota/js` (5.0.0, the
  JavaScript implementation of Digital Bazaar), run on Node 22.22.0 with
  `canonize.NQuads.parse` and `canonize.canonize(dataset, {algorithm:
  'RDFC-1.0', format: 'application/n-quads'})` and the default
  `maxWorkFactor` of 1. On this shape it is itself superlinear: 2.02 s at
  16,000 and 37.80 s at 64,000 blank nodes.

Natively, Lean takes 2.8 to 3.5 times the CPU time of Oxigraph on this
ladder (2.8 to 3.0 from 4,000 blank nodes up), and less than rdf-canonize at every
size. Where the time goes now
(callgrind at 16,000 blank nodes, 5,701 million instructions, exclusive):
the pure-Lean SHA-256 compression loop and its message schedule are about 20
percent (one hash per blank node for §4.5 and one per Hash N-Degree Quads
call for §4.7 step 6), reference counting and the allocator about 20
percent, the N-Quads parse about 19 percent inclusive, and the command
line's JSON envelope about 11 percent inclusive. No step is superlinear.

Two other shapes, before and after, to check that the cost did not move to
the parts of §4.7 that the collide shape does not use (related blank nodes,
permutations and recursion): k pairs `_:a{i} ex:p _:b{i}` (two collision
groups of k), 0.18 s and 2.08 s at 1,000 and 4,000 before, 0.07 s, 0.26 s and
1.18 s at 1,000, 4,000 and 16,000 after; k chains `_:a{i} ex:p _:b{i} .
_:b{i} ex:p _:c{i}` (three groups, recursion one level down), 0.40 s and
7.00 s before, 0.12 s, 0.47 s and 2.26 s after. Output byte-identical.

Gates on this tree:

- RDFC-1.0 (`l4w3c --quiet third_party/testing/rdf-canon/tests/manifest.ttl`):
  86 pass, 0 fail (out of 86), before and after. `l4rdfc-probe`: output
  identical before and after (`rdfc10 eval: 63 of 63`, `sha384 eval: 1 of
  1`, `rdfc10 map eval: 21 of 21`, `negative eval (excessive-calls abort):
  1 of 1`).
- `tests/stack/lean_scaling.sh`: 21 pass, 0 fail, 1 expected-fail (out of
  22). `rdfc-bnode-collide` passes (0.081 s to 0.300 s, ratio 3.7, bound 9)
  and is no longer in `XFAIL`; the one expected failure is
  `query-memory-fstar` (https://github.com/danbri/factoidal/issues/729).
  Every other row passes, as before.
- `tools/lean-tail-recursion-audit.py --gate` passes with one new allow-list
  line, `hndqRunF`, `(a) PENDING` with https://github.com/danbri/factoidal/issues/752
  as `hndqRun`: it is the same Hash N-Degree Quads recursion (one level per
  blank node of one path), now the code that runs. The (a) PENDING count is
  26 (it was 25).
- `tools/lean-hygiene-audit.py --build-log` on the full build: clean (0
  sorry, 0 axiom, 0 native_decide, 0 unsafe, 0 implemented_by, 164 partial
  def, baseline 164; 1,051 `#print axioms` outputs, none outside `propext`,
  `Classical.choice`, `Quot.sound`).
- `Wasm/native-smoke.sh`: 350 pass, 0 fail (out of 350).
- The wasm modules rebuilt (`Wasm/build-wasm.sh`, 2,055 s at load 6 to 29):
  full module 10,990,953 bytes, core module 5,898,200 bytes, copied into
  `npm/factoidal/l4-assets`. `npm test` in `npm/factoidal`: 413 pass, 0 fail,
  1 skipped (out of 414; the skip needs the `esbuild` devDependency).
- `lake build` (no target): exit 0 (1409 jobs).

### What the F\* comparison found on the F\* side

Recorded for the private comparison builds, not issues of the package: both
F\* bundles parse quadratically (wasm_of_ocaml 0.67 s at 3,000 triples, 11.3 s
at 12,000; js_of_ocaml 0.35 s, 1.7 s, 6.6 s at 48,000), both fail
`canonicalize` of 24,000 blank-node quads (stack overflow), and both fail
SHACL validation of 24,000 triples (the bench of that run kept no error
text), which the Lean module answers in 1.5 s.

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
  in `npm/factoidal/test/l4-parity.test.js`; fixed on 2026-10-12 (OKR batch 1
  key result 4.3), and the two cases are now assertions.
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
