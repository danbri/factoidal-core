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

| Group | Names | Lean library | Lean wasm dispatch op |
|---|---|---|---|
| Formats and transforms | `jsonldToRdf`, `jsonldFromRdf`, `rmlMap`, `csvwToRdf`, `xmlWellformed`, `xpathEval`, `xsltTransform`, `schematronValidate`, `jsonSchemaValidate`, `mathmlEval`, `xformsRecalc`, `rifEval` | yes (W3C suites pass, see issue 698) | no |
| Stores | `queryHdt`; `openCottas`, `queryCottas`, `closeCottas`, `toCottas` | HDT: yes. COTTAS: no; the owner ruled F\* COTTAS essentially unused (issue 566); the Lean store (IBK3 generations, `storeOpen`/`storeQuery` ops) is the replacement, with a different format | HDT: no; store: yes |
| Reasoning | `tableauMaterialise`, `tableauDlInconsistent` | yes (OWL refuter / tableau) | no |
| Query plumbing | `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions`, `registerServiceEndpoint`, `clearServiceEndpoints`, `queryRaw` | yes | extension functions: yes (`extRegister` ...); SERVICE endpoints and raw results: no |
| Maths | `toanSummation`, `toanProduct`, `toanSimplify`, `toanDiff`, `toanSubst`, `matrixDeterminant`, `matrixScalarProduct`, `matrixVectorProduct`, `matrixOuterProduct`, `sigmoidPoints`, `sigmoidFormulaMathml` | yes (`L4Factoidal/Math`) | ToaN: yes; matrix, sigmoid: yes since stage 2 (`Wasm/Ops/Maths.lean`) |
| VC and DID | `vcSha256Hex`, `vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical`, `vcCheckCredential`, `vcCheckCredentialSubject`, `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests`, `didKeyResolve` | yes; `vcCheckNoDataLoss` and `vcCheckRelatedResourceDigests` landed in stage 2 (`L4Factoidal/VC/Credential.lean`, namespace `Doc`) | yes since stage 2 (`Wasm/Ops/Vc.lean`) |

The table above is the state on 2026-10-10 before stage 1 and stage 2. After
stage 2 the Maths row and the VC and DID row have a Lean library and a
dispatch op for every name; stage 1 changes the other rows.

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

1. Formats, transforms, stores, reasoning, query plumbing: dispatch ops and
   `l4-core` wrappers for the first four groups of the table, each tested by
   running the existing F\*-engine npm tests for that function against the
   Lean engine (same inputs, same expected results).
2. Maths, VC and DID (issue 578 items 2-4), and the envelope parity of
   issue 685 and blank-node salting. **Done 2026-10-10** (branch
   `claude/wt-npm-lean-2`); the record is § 5.
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
