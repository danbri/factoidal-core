# Semantic lockdown: status report, 2026-10-24

Issue: [danbri/factoidal#975](https://github.com/danbri/factoidal/issues/975), "Bind every component to the Lean FOUNDATION layer".

Owner steer, 2026-10-24 (verbatim): "We want all our parsers, all and any data access APIs we create, our SPARQL OWL etc tools of any kind, to be bound irreversibly to the Lean we write and declare as our standardized FOUNDATION layer."

## Summary

| | State |
|---|---|
| Lockdown tooling | ✅ Exists and runs in CI on every build of `danbri/factoidal-builds` |
| Coverage | 🟡 Low: 47 of 585 entry points are bound to a stage; 60 foundation imports break the rules |
| Binding by type | 🟡 Readers done (`RdfReader`); data access in progress (`LawfulStore`); five kinds not started |
| Semantics fixed by type | 🟡 First rule: one spelling per RDF term (canonical language tags), PR 57 |
| End-to-end theorem | ❌ Not stated yet; all parts exist |
| Flow-based npm API | ❌ Not started; design in [danbri/factoidal#1002](https://github.com/danbri/factoidal/issues/1002) |

## 1. The tooling (what "lockdown" means in practice)

| Tool | What it fails on | Where |
|---|---|---|
| FOUNDATION manifest | — (the declaration) | [`foundation/manifest.toml`](../foundation/manifest.toml), version 0 |
| Foundation import gate | a foundation module that imports an implementation module; a level that imports a higher level | [`tools/foundation-gate.py`](../tools/foundation-gate.py) |
| Entry-point gate | an npm export, wasm op or CLI command with no registered Lean stage | [`tools/entrypoint-gate.py`](../tools/entrypoint-gate.py) |
| Assumption gate | a named assumption (inventory `IO assumptions`, or a field named `assumed_*`) not listed in `foundation/assumptions.txt`; a pinned `proved` stage that is no longer proved | [`tools/assumption-gate.py`](../tools/assumption-gate.py) |
| Ratchets | either violation list growing, or listing an entry that is gone | `foundation/allow-imports.txt`, `foundation/unbound-entrypoints.txt`, `foundation/assumptions.txt` (4 named assumptions), `foundation/proved-stages.txt` (60 stages) |
| Dataflow inventory | a registry change without the regenerated table | [`docs/dataflow-inventory.md`](dataflow-inventory.md) |

All of them run in `tests/dataflow/run.sh`, which the Linux Lean job of `danbri/factoidal-builds` runs after `lake build` ([factoidal-builds PR 2](https://github.com/danbri/factoidal-builds/pull/2)). A failure stops the release sets.

Foundation levels, version 0 (owner, 2026-10-24: "the details matter less than that we can do it, and that the human experts can refine it later"):

| Level | Content | Modules |
|---|---|---|
| L0 | RDF/RDFS model, named graphs, IRIs, XSD datatypes, RDF Semantics | 31 |
| L1 | SPARQL and its extensions (text, geo, functions), OWL, RIF, SHACL, ShEx, RDFC-1.0, XPath F&O, proof claims (FPP0), `Stage` | 71 |
| L2 | XML, XPath 1.0, JSON, and the RDF, SPARQL, OWL, RIF and ShEx syntaxes | 35 |
| L3 | CSVW, RML, JSON-LD | 15 |

The module choice was made from the code by an agent; it needs expert review.

## 2. Coverage

### Entry points (CI, 2026-10-24)

| Kind | Total | Bound (proved / tested) | No stage | Unbound |
|---|---|---|---|---|
| npm | 390 | 29 | 37 | 324 |
| wasm | 179 | 18 | 4 | 157 |
| CLI | 16 | 0 | 1 | 15 |
| **All** | **585** | **47 (43 / 4)** | **42** | **496** |

"No stage" entries run no computation: version strings, reflection, constants, error classes. Unbound was 504 when the gate landed (PR 54); PR 56 bound npm `parse`, `openDataset` and wasm `datasetOpen`, `parseQuadsJson`, `parseDocument` (−8).

Most used unbound entry points (by the number of test, example and hub files that call them): `fn.query`, `fn.filter`, `loadEngine`, CLI `query`, the server `listen` entries, `engine`, `fn.canonicalize`, `serialize`.

### Foundation imports

60 violations, all on the ratchet list with a reason: 51 foundation modules import an implementation module (for example `SPARQL.Query` imports `ExistsIndex` and `OrderedPrefix`; `RDF.Isomorphism` imports `GraphIndex`; `RDF.DatasetSet` imports the TriG parser; `Allowed` lives in the SBM11 storage tree), and 9 import a higher level.

## 3. Binding by type (issue 975, item 2)

The rule: each kind of component has ONE interface type whose contract against the foundation is a field, so a value cannot exist without its proof. Consumers accept only that type. A proof not yet done is a named assumption field, counted by a ratchet.

| Kind | Interface type | State |
|---|---|---|
| Reader (bytes/text → dataset) | `RdfReader` (`Dataflow/Reader.lean`) | ✅ [PR 56](https://github.com/danbri/factoidal-core/pull/56): fields `set`, `sound` (reader contract, every document scope), `fails` (fails exactly when the parser fails); every wasm op that parses RDF takes its reader from one table |
| Data access (`StoreCaps`) | `LawfulStore` | 🟡 in progress: exact search and exact predicates as fields; HDT and COTTAS reader laws as named assumptions; planner and evaluator accept only this type |
| Writer | — | ❌ (round trips proved for N-Triples and N-Quads, [PR 49](https://github.com/danbri/factoidal-core/pull/49), [PR 51](https://github.com/danbri/factoidal-core/pull/51), as separate theorems) |
| Query evaluator | `LawfulEvaluator` (`Dataflow/Evaluator.lean`) | 🟡 fields `run`, `assumed_contractOn` (named assumption: the backend path outside `NativeFrag`, and the SELECT fast paths), `sound` (every other input: the reference answer, or the modifier layer over an `Allowed` WHERE answer); `queryParsedDatasetWith`, the evaluation of every wasm query op, takes one |
| Reasoner | — | ❌ |
| Validator | — | ❌ |
| Proof checker | — | ❌ (`checkBundle_rdfsEntails` proved, as a separate theorem) |

## 4. Semantics fixed by type

[PR 57](https://github.com/danbri/factoidal-core/pull/57) ([danbri/factoidal#1001](https://github.com/danbri/factoidal/issues/1001)): `RDF.literalWf` requires a lower-case language tag (RDF 1.2 Concepts §3.4: tags compare case-insensitively; an implementation may convert to lower case). A term with a non-canonical tag cannot exist, so `Term.eqb` is structural equality (`Term.eqb_iff_eq`). This is the first foundation rule enforced by the type and not by a theorem beside it. It removed a premise (`GraphFixed`) from the evaluator refinement theorems and fixed a defect: a SPARQL answer depended on the order of two triple patterns when a tag had upper case.

## 5. The flow-based data architecture

| Layer | State |
|---|---|
| Lean: `Stage` (run, contract, sound), `IOStage` (named assumptions), composition | ✅ `Dataflow/Stage.lean` |
| Lean: registry of stages with typed wires | ✅ 105 entries: 60 proved, 24 tested, 4 assumed, 17 missing; 14 of the 17 moved to their own issues ([#987](https://github.com/danbri/factoidal/issues/987) to [#999](https://github.com/danbri/factoidal/issues/999), [#756](https://github.com/danbri/factoidal/issues/756)) |
| Lean: one common dataset target | ✅ `DatasetDen`; block stores, the SBM11 overlay, `MemGen`, dictionaries and `StoreCaps` map into it |
| End-to-end theorem (bytes → reader → store → evaluator → result) | ❌ waits for `LawfulStore` and an evaluator type |
| npm: nodes and evidence wires | ❌ design in [#1002](https://github.com/danbri/factoidal/issues/1002): graphs with evidence as the unit (owner: "Stuffing everything into atomic triples is one of RDF's failure conditions"), RDFS first, `explain(sources, description)` |

## 6. Next steps

1. Merge `LawfulStore` (the assumption-count ratchet, item 4, is `tools/assumption-gate.py`).
2. Interface types for the evaluator, then writers, reasoners, validators, checker.
3. State the end-to-end theorem over `RdfReader`, `LawfulStore` and the evaluator type (item 5).
4. Shrink the two ratchet lists: move index helpers out of foundation modules; bind `fn.query`, `serialize`, CLI `query`.
5. `explain` for RDFS over graph descriptions (#1002).

## Method note

On 2026-10-24 PRs 44 to 52 were merged after a Lean build and the drift test only. PR 51 broke the npm package suite, found by the first CI build of main. The rule since then ([PR 55](https://github.com/danbri/factoidal-core/pull/55), `skills/github-and-prs`): a PR that changes shipped Lean or npm code is built in CI on its head commit and merged only when `web-gates` passes. PR 57 was held by that rule: CI found a CLI smoke case that pinned the old two-spelling behaviour.
