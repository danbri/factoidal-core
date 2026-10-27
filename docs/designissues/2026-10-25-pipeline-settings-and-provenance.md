# Pipeline node settings: the API, the evidence record and the proofs

Status: current. Date: 2026-10-25. Landed on `main` in
https://github.com/danbri/factoidal-core/pull/116 (pipeline node settings,
merged 2026-10-25, merge commit a76d8694; branch `claude/pipeline-0.16`).
The engine parts need a wasm module built from a76d8694 or later; npm
0.15.0 does not have them.
Tracking: https://github.com/danbri/factoidal/issues/975 (checked pipelines),
https://github.com/danbri/factoidal/issues/1026 (evaluator output wire).
Companion record: `2026-10-25-tabular-and-source-models.md` (tables and
sources, https://github.com/danbri/factoidal/issues/1033).

Owner, 2026-10-25, verbatim:

> "If parsers and other components take extra args and settings find a way to
> expose that in api and keep it in provenance/pipeline, also consider their
> impact on proofs"

> "select give table? Sure"

## 1. What a setting is

A node is a registry stage (`Dataflow/Registry.lean`) plus its settings: the
inputs it takes when it is made, not values on a wire. In npm the settings are
the second argument of `node(name, params)`; the runner passes them to the
package function of the stage. The Lean module
`L4Factoidal/Dataflow/NodeSettings.lean` decides what each setting does; the
wasm op `pipelineCheckNodes` (`Wasm/Ops/PipelineNodes.lean`) reports it;
`npm/factoidal/lib/nodes.mjs` only marshals (a Dataset value is sent as
`{"$nquads": text}`).

## 2. Settings per stage, and their effect on the contract

Each setting has one role (`SettingRole`):

| Role | Meaning | Effect on status |
|---|---|---|
| `parameter` | the contract theorem quantifies over the value | none |
| `selects-wire` | a parameter that also selects the output wire | none; the wire changes |
| `inert` | the stage's computation does not read it on a node's input | none |
| `narrows` (default `d`) | the contract covers only `d` | another value: `unproved` |
| `unlisted` | a key the stage's table does not name | on a proved stage: `unproved` |

The table (`settingTable`):

| Stage | Setting | Role | Why |
|---|---|---|---|
| readers (`*DocumentReader`) | `format` | parameter | names the stage's syntax and selects the RDF 1.1 or 1.2 mode; `ReaderContract extra fmt mode base` is stated for every mode. The op refuses a format of another syntax and reports `derived.mode` |
| | `baseIRI` | parameter | `ReaderContract` is stated for every base |
| | `lenient` | narrows (`false`) | the lenient parse skips statements that fail; `ReaderContract` states the strict parse `parseDocumentRaw` |
| | `maxErrors` | inert | read only by the lenient parse |
| writers (`*DocumentWriter`) | `format` | parameter | must name the stage's syntax |
| | `version`, `prefixes`, `literalShorthand` | parameter | `RoundTripOn` is stated for each mode and every `TurtleRenderOptions` value |
| | `useNativeTypes`, `useRdfType`, `rdfDirection` | narrows (absent) | JSON-LD render options, not `TurtleRenderOptions` fields |
| `shippedEvaluator` | `query` | selects-wire | `EvalContract` is stated for every parsed query; the form selects the wire (section 3) |
| | `baseIRI`, `sparql12`, `version` | parameter | part of, or the grammar of, the parsed query |
| | `entail` | narrows (`none`) | a regime adds an entailment step that `EvalContract` does not state |
| | `output` | narrows (absent) | the results document rendering has no stage |
| reasoners, `rdfcStage` | `format`, `baseIRI` | inert | read only when the input is text |
| `shaclValidator` | `shapes` | parameter | `CoreConformance` is stated for every shapes graph |
| `rdfsExplainGraphStage` | `description` | parameter | `ExplainGraphContract` is stated for every description |
| CSVW (`tested`) | `metadata`, `mode`, `base`, `url` | parameter | csv2rdf inputs; the stage has no Lean contract, so they are recorded only |

A stage that is not `proved` (`tested`, `assumed`) has no proved domain: its
settings are recorded and its status does not change.

## 3. The output wire that a setting selects

The registry gives `shippedEvaluator` the wire `Answer` (the sum of the three
answer forms). A node knows its query, so `formWire` refines it: SELECT
`Table`, ASK `Answer`, CONSTRUCT and DESCRIBE `Dataset` (the dataset whose
default graph is the answer graph, with no named graph). `table` is a new wire
of `Dataflow/Wire.lean`; until the shared table type of issue 1033 lands it
names the SELECT answer only.

Proof: `evalContract_wire` shows that every answer satisfying `EvalContract`
has the wire `formWire q.form` (the reference answer and the modifier layer
both keep the form), so `LawfulEvaluator.run_wire`: a lawful evaluator, on a
well-formed input outside its assumed class, answers with that wire. The node
signature is `Entry.nodeSig e (formWire q.form)`, and the pipeline check is
the same `pipelineReport Wire.conv` over node signatures. `#guard`s: reader,
CONSTRUCT, CONSTRUCT is well typed; reader, SELECT, CONSTRUCT is not
(mismatch at 1: `Table` to `Dataset`); CSVW then CONSTRUCT is well typed.

## 4. How settings appear in the evidence record

Per node, the op returns and each record carries:

* `settings`: the given settings plus the default of every absent `narrows`
  setting (`lenient: false`, `entail: "none"`), in canonical form
  (`canonJson`: object keys in code point order at every depth, arrays in
  order, number lexical forms as given; `{"$nquads": t}` becomes
  `{"nquadsSha256": hex}`, the N-Quads text as the Dataset gave it, not RDFC);
* `settingsDigest`: `sha256:` and the hex SHA-256 (pure Lean
  `Crypto.sha256Hex`) of the compact canonical text;
* `status`: `unproved` when a proved stage has a setting outside its domain,
  with `registryStatus` and `outside` (setting and reason); else the registry
  status. `checked` is `nodeChecked` (`nodeChecked_iff`: checked exactly when
  the stage is proved and no setting is outside).

`run().proved` is true only when every record is checked and the pipeline is
well typed, so a lenient reader makes a pipeline unproved, and the record
says which setting caused it.

## 5. Impact on proofs

* One theorem per stage, parameterised by the settings, is the form used:
  `ReaderContract` takes `mode` and `base`, `RoundTripOn` quantifies over the
  mode and every `TurtleRenderOptions`, `EvalContract` over every parsed
  query. A theorem per setting value is not written: it would multiply with
  every option and still not cover free text such as a base IRI or a query.
* A setting value outside the domain of the theorem (lenient parsing, an
  entailment regime on the evaluator, a JSON-LD render option on a Turtle
  writer, an unknown key) makes the node `unproved`. The pipeline guarantee
  `Pipeline.guarantee_sound` is unchanged; it applies to the components whose
  contracts hold, and a node outside its domain has no proved contract to
  supply.
* To bring a setting into the domain, state the theorem for it: for example a
  lenient-reader contract (the output is the set of the statements that
  parse, each a sub-document of the input), or an evaluator contract over the
  entailment regimes (`regimeEntails`). Then change its role in
  `settingTable` from `narrows` to `parameter` in the same commit.
* Settings that select a wire need a theorem that ties the wire to the
  setting (`evalContract_wire`); without one the wire stays the registry's.
* The canonical form and the digest are not part of any contract: they
  identify the configuration in the record.

## 6. Not done, with tracking

* The query parser is not proved (the registry row "SPARQL query evaluation
  (reference evaluator)" is `tested`); `EvalContract` starts at the parsed
  query. Same as before this change.
* RML has no materialising stage in the registry (only the virtual RML
  `LawfulStore`, two open assumptions); `rmlMap` is not a node yet. Other
  plain-function importers not registered as stages: `jsonldToRdf` (the
  JSON-LD reader is), `rifEval`, `fromMapping`.
* The wasm op needs a module rebuild (danbri/factoidal-builds). On an older
  module records carry no settings and the evaluator's wire is `Answer`.
