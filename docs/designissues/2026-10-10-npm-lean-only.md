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

Which engine each entry point loads:

| Entry | Engine |
|---|---|
| `.` (`index.js`, `index.mjs`), `./api`, `./fn`, `./lite`, `./wasm`, `./browser`, `./browser-wasm` | F\* (js_of_ocaml / wasm_of_ocaml bundles; `hacl-wasm/` for VC crypto) |
| `./l4`, `./l4-core` | Lean 4 (wasm, dispatch ABI) |
| `./select` | both |
| `bin/factoidal.mjs`, `lws/`, `solid/` (Node hosts) | Lean 4 |
| `./rdfjs`, `store-host`, `sample-store`, `xmpp` | engine-neutral wrappers |

The main entry exports 72 names; `l4-core` exports 30. 42 main-entry names
have no Lean path in the package:

| Group | Names | Lean library | Lean wasm dispatch op and `l4-core` wrapper |
|---|---|---|---|
| Formats and transforms | `jsonldToRdf`, `jsonldFromRdf`, `rmlMap`, `csvwToRdf`, `xmlWellformed`, `xpathEval`, `xsltTransform`, `schematronValidate`, `jsonSchemaValidate`, `mathmlEval`, `xformsRecalc`, `rifEval` | yes (W3C suites pass, see issue 698) | **yes since stage 1**: `Wasm/Ops/Formats.lean`; wrapped in `l4-core.js` |
| Stores | `queryHdt`; `openCottas`, `queryCottas`, `closeCottas`, `toCottas` | HDT: yes. COTTAS: no; the owner ruled F\* COTTAS essentially unused (issue 566); the Lean store (IBK3 generations, `storeOpen`/`storeQuery` ops) is the replacement, with a different format | HDT: **yes since stage 1** (`queryHdt` in `Wasm/Ops/QueryExtras.lean`; the file travels as the ABI's byte region). COTTAS: no, by the ruling; store: yes |
| Reasoning | `tableauMaterialise`, `tableauDlInconsistent` | yes (OWL refuter / tableau) | **yes since stage 1**: `Wasm/Ops/Reasoning.lean` |
| Query plumbing | `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions`, `registerServiceEndpoint`, `clearServiceEndpoints`, `queryRaw` | yes | **yes since stage 1**: extension functions (`extRegister` ... already existed; `l4-core.js` now wraps them and installs the JavaScript call-out), SERVICE endpoints (`Wasm/Ops/ServiceReg.lean`), `queryRaw` (`Wasm/Ops/QueryExtras.lean`) |
| Maths | `toanSummation`, `toanProduct`, `toanSimplify`, `toanDiff`, `toanSubst`, `matrixDeterminant`, `matrixScalarProduct`, `matrixVectorProduct`, `matrixOuterProduct`, `sigmoidPoints`, `sigmoidFormulaMathml` | yes (`L4Factoidal/Math`) | ToaN: **wrapped in `l4-core.js` since stage 1** (the ops existed); matrix, sigmoid: no |
| VC and DID | `vcSha256Hex`, `vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical`, `vcCheckCredential`, `vcCheckCredentialSubject`, `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests`, `didKeyResolve` | yes except `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests` (issue 578 gap 3) | no (issue 578 gap 1) |

**After stage 1** (measured in danbri/factoidal-core, 2026-10-10):
`l4-core` exports 56 names (30 before). Of the main entry's 72 names, 21
have no `l4-core` function: `didKeyResolve`, the 4 `matrix*`, the 2
`sigmoid*`, the 10 `vc*`, and the 4 COTTAS functions. Stage 2 takes the
first 17 of them (the COTTAS four are replaced, see issue 566); stage 3
is the switch. `shaclValidate` and `shexValidate` are exported by `l4-core`
as functions that reject with the engine-capability error; the Lean
library has SHACL and ShEx and the dispatch table does not serve them yet.

Behaviour differences of the Lean engine through the npm wrapper, already
recorded:
- envelope parity: parse-error position, prefixes on a dataset handle,
  `serializeTurtleWith`, literal shorthand in Turtle output (issue 685,
  expected-failure cases in `npm/factoidal/test/`);
- blank-node labels are not salted per document when documents are merged
  (`test/l4-core.test.js` header);
- N-Quads line order differs (content is compared sorted).

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
   checks (issue 578 gap 3), and SPARQL SERVICE endpoint registration from
   the host.
3. Recorded behaviour differences (issue 685, blank-node salting, N-Quads
   order).
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
   the parity run found are in section 5.
2. Maths, VC and DID (issue 578 items 2-4), and the envelope parity of
   issue 685 and blank-node salting.
3. Switch: `.`, `./api`, `./fn`, `./browser` load the Lean engine; the F\*
   bundles, `hacl-wasm/`, `./wasm`, `./browser-wasm` and `./lite` leave the
   package. The F\* bundles stay as factoidal-builds artifacts for private
   comparison builds (and the differential harness `l4diff`). The COTTAS
   functions are replaced by the Lean store functions. Version 0.9.0.
4. Size profile: a smaller Lean wasm for the browser, from a dispatch table
   that reaches a subset of the library (the role `./lite` had), measured
   against the F\* lite bundle.
5. Speed: the npm benchmark (`tests/perf/l4_vs_fstar_wasm_bench.mjs`) re-run;
   any row where the Lean engine is more than 2 times slower becomes an
   issue before the switch is published.
