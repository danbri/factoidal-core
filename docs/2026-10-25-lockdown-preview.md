# Semantic lockdown preview, 2026-10-25

Issue: [danbri/factoidal#975](https://github.com/danbri/factoidal/issues/975). Branch `claude/lockdown-preview-975` merges PRs [57](https://github.com/danbri/factoidal-core/pull/57), [59](https://github.com/danbri/factoidal-core/pull/59), [60](https://github.com/danbri/factoidal-core/pull/60), [61](https://github.com/danbri/factoidal-core/pull/61), [62](https://github.com/danbri/factoidal-core/pull/62) and the branch `claude/lockdown-evaluator-975`, and adds the end-to-end theorem (acceptance item 5). It shows all interface types in one tree. Do not merge it; merge the separate PRs.

## 1. Interface types

Each component kind has one interface type. Its contract against the foundation is a field. An unproved part of the contract is a field named `assumed_*`; the assumption gate counts it.

| Kind | Interface type (file) | Instances | Proved fields | `assumed_*` fields |
|---|---|---|---|---|
| Reader | `RdfReader` (`Dataflow/Reader.lean`) | `readers` table: N-Triples, N-Quads, Turtle, TriG, RDF/XML, JSON-LD | `set`, `sound` (reader contract, every document scope), `fails` | none |
| Data access, one graph | `LawfulStore` (`Dataflow/Store.lean`) | proved: `ofList`, `ofIndexed`, `ofCaps`, `overlay`, `union`; with names: `hdt`, `cottasInMemory`, `cottasOnDisk`, `cottasOnDiskDelta`, `virtualRml`, `ofGraph`, `ofIndexedGraph` | `law` (`BackendExact` under the assumptions) | `assumed_contracts` (list of `AssumptionName`: 6 names, 12 uses) |
| Data access, dataset | `LawfulDataset` (`Dataflow/Store.lean`) | proved: `indexed`, `ofDefault`, `ofCertified` (IRI graph names); with names: `ofCertified` (blank-node graph name), `ofDataset` | `law` (`DatasetBackendExact`) | `assumed_contracts` |
| Writer | `RdfWriter` (`Dataflow/Writer.lean`) | `writers` table; proved: N-Triples, N-Quads; assumed: Turtle, TriG, RDF/XML, JSON-LD, canonical N-Quads | `roundTrip` (when nothing is assumed) | `assumed_roundTrip` (5 writers) |
| Query evaluator | `LawfulEvaluator` (`Dataflow/Evaluator.lean`) | `shippedEvaluator` (all wasm query ops) | `sound` (`EvalContract` outside the assumed inputs) | `assumed_contractOn` (backend path outside `NativeFrag`; SELECT fast paths) |
| Reasoner | `SoundReasoner` (`Dataflow/Reasoner.lean`) | `rhoDfReasoner`, `rdfsReasoner D`, `owlRlReasoner` | `sound` (output entailed in the regime) | `assumed_completeness` (3 instances) |
| Validator | `LawfulValidator` (`Dataflow/Validator.lean`) | `shaclValidator` | `sound` (conforming report implies SHACL Core conformance) | `assumed_spec_iff` (1 instance) |
| Proof checker | `SoundChecker` (`Dataflow/Checker.lean`) | `foundationalChecker`, `rdfsChecker` | `sound` (accept implies the claim) | none |

## 2. The end-to-end theorem

Module `formal/lean4/L4Factoidal/Dataflow/EndToEnd.lean`. The pipeline is `pipeline r ev inp env q`: the reader `r` reads the document text; `loadStore` builds the lawful store `LawfulDataset.ofCertified` when every graph name is an IRI (no store when a graph name is a blank node, then the reference evaluator answers); `ev.run` evaluates the query.

`pipeline_sound r ev hev inp env q h`. If the reader accepts (`h : r.run inp = .ok out`), then:

1. the pipeline answers `ev.run x`, with `x = pipelineInput env c q`;
2. the parse of the document gives `raw`, the read dataset is the set of quads of `raw`, and its denotation is `raw.den`;
3. every loaded store has the denotation of the read dataset and a proved law (no named assumption);
4. `EvalContract x (ev.run x)`: the answer is the foundation's SPARQL 1.1 answer over the read dataset (`evalSelect`, `evalAsk`, `evalConstruct`, `evalDescribe`), or, for SELECT and ASK on the backend path, the foundation's modifier layer over a WHERE answer that `Allowed` (SPARQL 1.1 §18.5) admits. The second case is not proved equal to the first.

Premises: `hev : ev.AssumptionHolds` (the named assumption `LawfulEvaluator.assumed_contractOn`) and `h` (the case "the reader accepts"; on a parse error, `pipeline_error` gives the error). The reader and the store add no assumption. `shipped_pipeline_sound` replaces `hev` by the two named statements `BackendOutsideFragmentAgrees` and `SelectFastPathAgrees`. `pipeline_sound_proved` has no assumption, for the inputs outside `assumed_contractOn`. `shipped_pipeline_construct`: a CONSTRUCT answer is exactly `evalConstruct` over the read dataset.

The join of store and evaluator: `LawfulDataset.backendReads_ofCertified` (the store's backend reads the dataset, `BackendReads`) and `pipelineInput_wf` (`EvalInput.Wf`). Anti-pattern 29 check: no premise contains `pipeline`, `SetOf`, `den` or `LawfulDataset`; `hev` contains `EvalContract` only on the assumed inputs. `#print axioms` for all eight theorems: propext, Classical.choice, Quot.sound. No sorry, axiom, `native_decide` or `partial`.

Not covered: a store with a blank-node graph name (the backend record cannot read it pair for pair); the claim that the answer depends only on the denotation; the decode from bytes to text (it is the separate proved stage `decodeStage`).

## 3. Gates (this branch)

| Gate | Result |
|---|---|
| Entry points (`tools/entrypoint-gate.py`) | 60 bound (48 proved, 12 assumed), 42 no stage, 483 unbound (out of 585); main: 47 bound, 496 unbound |
| Foundation imports (`tools/foundation-gate.py`) | 60 violations, all 60 on the allow list (51 implementation imports, 9 level imports) |
| Assumptions (`tools/assumption-gate.py`) | 28 named assumptions: 16 io, 6 field, 6 `AssumptionName` with 12 uses; 78 proved stages pinned, 0 demoted |
| Inventory (`docs/dataflow-inventory.md`) | 78 proved, 24 tested, 17 assumed, 17 missing (out of 136) |
| Gate tests | foundation gate 10 pass, 0 fail (out of 10); entry-point gate 12 pass, 0 fail (out of 12); assumption gate 26 pass, 0 fail (out of 26) |
| Build | full `lake build`: 2290 jobs, exit 0; `tests/dataflow/run.sh`: exit 0 |
| Not run here | W3C suites, npm package suite, wasm build, native smoke (CI on `danbri/factoidal-builds`) |

## 4. Merge notes

- One assumption gate: PR 59 counted io assumptions, `assumed_*` fields and proved stages; PR 60 counted the uses of each `AssumptionName`. The combined gate does all of this. Line kinds in `foundation/assumptions.txt`: `io:`, `field:`, `name:<Ctor> uses=N`, `demoted:`. The field regex no longer counts a value `assumed_x := v` as a declaration.
- PR 57 removed the `Fixed` fields of `GraphRel`. So the Fixed premises of PR 60 (`where_allowed`, `lawfulWhereStage`) and the `GraphFixed` premises of the evaluator branch (`backendReads_indexed`, `EvalInput.wf_indexed`) are removed here.
- `Wasm/Ops/Query.lean`: `queryParsedDatasetWith` takes the `LawfulDataset` of PR 60 and the `LawfulEvaluator` of the evaluator branch.
