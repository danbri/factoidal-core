/-
L4Factoidal.Dataflow.Registry — the declared list of stages of the system
(https://github.com/danbri/factoidal/issues/975, phase A3).

`tools/dataflow-inventory.py` reads this list (through
`tools/dataflow-inventory.lean`, which elaborates against the built library)
and writes `docs/dataflow-inventory.md`. The inventory is this list, not a
guess from file or declaration names (anti-pattern 31).

Each entry names its Lean declarations with double-backtick name literals, so
a name that does not exist stops the build. The report program also checks,
for each entry: the status agrees with the fields (below), every named
declaration exists, and `#print axioms` of every named declaration is a
subset of propext, Classical.choice, Quot.sound.

Status:

* `proved`: `stage` is a `Stage` value, or a value of an interface type with
  its contract as a field: `RdfReader` (`Dataflow/Reader.lean`), `SoundReasoner`
  (`Reasoner.lean`), `LawfulValidator` (`Validator.lean`), `SoundChecker`
  (`Checker.lean`), `LawfulEvaluator` (`Evaluator.lean`), whose `sound` field is a proof, or an `RdfWriter`
  (`Dataflow/Writer.lean`) whose `assumed_roundTrip` is `none`. Unproved
  contract fields of these types are named assumptions, fields with the prefix
  `assumed_`;
  `contract` names its contract; `theorems` names the component theorems it
  uses.
* `assumed`: `stage` is an `IOStage`, an `RdfWriter` whose `assumed_roundTrip`
  is `some name`, or a data-access interface value (`LawfulStore`,
  `LawfulDataset`, `Dataflow/Store.lean`) whose law rests on a named
  assumption; `ioAssumptions` names the assumption.
* A `LawfulStore` or `LawfulDataset` value with no named assumption is
  `proved` like a `Stage`: its law is a field.
* `tested`: no Lean contract; `tests` names the test suite that checks the
  behaviour against the W3C test files (scores in `skills/test-suites`).
* `missing`: no Lean stage contract and no suite named here. `theorems` may
  list component theorems that a future stage can use.

`wireIn`, `wireOut` are wire types of `Dataflow/Wire.lean`; `params` names
the inputs that a node supplies when it is made (a query, a shapes graph,
render options), which the Lean stage takes as an argument or as the other
component of a pair. The pipeline check (`Dataflow/Pipeline.lean`,
`wellTyped`) compares the wires only.

`dir` is the directory under `formal/lean4/L4Factoidal/` of the area. The
report lists the directories that no entry names.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Instances
import L4Factoidal.Dataflow.PhaseD
import L4Factoidal.Dataflow.PhaseE
import L4Factoidal.Dataflow.PhaseC
import L4Factoidal.Dataflow.Reasoner
import L4Factoidal.Dataflow.Validator
import L4Factoidal.Dataflow.Checker
import L4Factoidal.Dataflow.ExplainGraph
import L4Factoidal.Dataflow.PhaseStorage
import L4Factoidal.Dataflow.PackSetStage
import L4Factoidal.Dataflow.StoreTheorems
import L4Factoidal.Unified.OwlRlAdequacy
import L4Factoidal.Storage.BlockDenotation
import L4Factoidal.SPARQL.FromMergeStage
import L4Factoidal.Storage.SelectedDataset
import L4Factoidal.Storage.BackendRefinement
import L4Factoidal.Dataflow.Evaluator
import L4Factoidal.Storage.StoreDictTheorems
import L4Factoidal.HDT.DictionaryTheorems
import L4Factoidal.Cottas.DictTheorems
import L4Factoidal.Dataflow.Wire
import L4Factoidal.Dataflow.Pipeline

namespace L4Factoidal.Dataflow

inductive Status where
  | proved | tested | assumed | missing
  deriving Repr, DecidableEq, Inhabited

def Status.label : Status → String
  | .proved => "proved"
  | .tested => "tested"
  | .assumed => "assumed"
  | .missing => "missing"

/-- One stage of the inventory. `Name.anonymous` means none. -/
structure Entry where
  area : String
  dir : String
  stage : Lean.Name := .anonymous
  /-- The wire the stage reads (`Dataflow/Wire.lean`). -/
  wireIn : Wire
  /-- The wire the stage writes. -/
  wireOut : Wire
  /-- The inputs a node supplies when it is made, not values on a wire. -/
  params : List String := []
  contract : Lean.Name := .anonymous
  status : Status
  theorems : List Lean.Name := []
  ioAssumptions : List Lean.Name := []
  tests : List String := []
  note : String := ""
  deriving Inhabited

/-- What the `stage` field names, as the report reads it from the environment:
a `Stage` value, an `IOStage` value, nothing, or another declaration. -/
inductive StageKind where
  | stage | writer | ioStage | iface | none | other
  deriving Repr, DecidableEq, Inhabited

/-- `Name.anonymous`: the field names nothing. -/
def isNone : Lean.Name → Bool
  | .anonymous => true
  | _ => false

/-- The status rule of the module header: `none` when the status agrees with
the fields and the kind of the stage, else the reason. The report stops on any
reason (`tools/dataflow-inventory.lean`); `RegistryTests.lean` holds an entry
for each way to disagree. -/
def Entry.statusError (e : Entry) (k : StageKind) : Option String :=
  match e.status with
  | .proved =>
    if isNone e.stage || isNone e.contract || e.theorems.isEmpty then
      some "proved needs a stage, a contract and theorems"
    else if k != .stage && k != .writer && k != .iface then
      some s!"proved: {e.stage} is not a Stage, an RdfWriter or a data-access interface value"
    else Option.none
  | .assumed =>
    if e.ioAssumptions.isEmpty then some "assumed needs a named IO assumption"
    else if k != .ioStage && k != .writer && k != .iface then
      some s!"assumed: {e.stage} is not an IOStage, an RdfWriter or a data-access interface value"
    else Option.none
  | .tested =>
    if e.tests.isEmpty || !isNone e.stage || !isNone e.contract then
      some "tested needs a suite, no stage and no contract"
    else Option.none
  | .missing =>
    if !isNone e.stage || !isNone e.contract || !e.tests.isEmpty || !e.ioAssumptions.isEmpty then
      some "missing has no stage, no contract, no suite and no IO assumption"
    else Option.none

/-- A stage may run as a node (the npm node API, `Wasm/Ops/StageList.lean`)
unless its status is `missing`: a stage with no contract and no suite does not
run (https://github.com/danbri/factoidal/issues/975, item 3). -/
def Entry.runnable (e : Entry) : Bool := e.status != .missing

private def dropPrefix (pre s : String) : Option String :=
  if s.startsWith pre then some (String.ofList (s.toList.drop pre.length)) else none

/-- A declaration name relative to `L4Factoidal.Dataflow` or `L4Factoidal`. -/
def stageShortName (s : String) : String :=
  (dropPrefix "L4Factoidal.Dataflow." s).getD ((dropPrefix "L4Factoidal." s).getD s)

/-- The node name of an entry: its declaration relative to
`L4Factoidal.Dataflow` or `L4Factoidal`, else its area (the `name` of the
wasm op `stageList`). -/
def Entry.nodeName (e : Entry) : String :=
  if isNone e.stage then e.area else stageShortName e.stage.toString

/-- The signature of an entry for the pipeline check (`Dataflow/Pipeline.lean`):
its node name, wires, contract name and named assumptions. -/
def Entry.sig (e : Entry) : StageSig Wire Lean.Name where
  name := e.nodeName
  inW := e.wireIn
  outW := e.wireOut
  contract := if isNone e.contract then none else some e.contract
  assumptions := e.ioAssumptions

/-- The registry. Order: boundary, syntax, stores, query, reasoning,
validation, evidence. -/
def registry : List Entry := [
  { area := "Document decode (UTF-8, media type)", dir := "RDF"
    stage := ``decodeStage, wireIn := .document, wireOut := .formatText
    contract := ``DecodeContract, status := .proved
    theorems := [``fromUTF8?_toUTF8, ``decodeParse_mediaType,
      ``L4Factoidal.RDF.formatOfDocument_of_mediaType, ``L4Factoidal.RDF.formatOfDocument_absent,
      ``L4Factoidal.RDF.formatOfMediaType_params]
    note := "six registered media types (RDF/MediaType.lean); the extension only when the media type is absent; text/n3 has no reader" },
  { area := "RDF readers: N-Triples, Turtle, N-Quads, TriG, RDF/XML, JSON-LD (set contract)"
    dir := "RDF"
    stage := ``parseStage, wireIn := .formatText, wireOut := .dataset
    contract := ``ParseContract, status := .proved
    theorems := [``L4Factoidal.RDF.Source.parseDocument_set, ``L4Factoidal.RDF.Dataset.memQuad_toSet,
      ``L4Factoidal.RDF.Dataset.toSet_isSet, ``SetOf.den_eq]
    note := "labels as written; the document scope is scopedParseStage" },
  { area := "Document blank-node scope (fresh labels per document)", dir := "RDF"
    stage := ``scopeStage, wireIn := .dataset, wireOut := .dataset
    contract := ``ScopeContract, status := .proved
    theorems := [``L4Factoidal.RDF.Dataset.den_iso_scopeDocument,
      ``L4Factoidal.RDF.Dataset.scopeDocument_inScope, ``L4Factoidal.RDF.Dataset.scopeDocument_isSet,
      ``L4Factoidal.RDF.docLabel_inj]
    note := "scope number from a fresh-label supply (Wasm counter, harness file index); the supply is IO, not modelled" },
  { area := "RDF readers with the document scope; two documents combine to a merge", dir := "RDF"
    stage := ``scopedParseStage, wireIn := .formatText, wireOut := .dataset
    contract := ``ScopedParseContract, status := .proved
    theorems := [``scopedParseContract_of, ``scopedParse_combine_isMerge,
      ``L4Factoidal.RDF.scopeDocument_combine_isMerge, ``L4Factoidal.RDF.Dataset.den_combine]
    note := "RDF 1.1 Semantics 5.2 merge (DatasetDen.IsMerge), not the union" },
  { area := "Blank-node relabelling at a store boundary (identity transport)", dir := "RDF"
    stage := ``relabelStage, wireIn := .dataset, wireOut := .dataset
    contract := ``RelabelContract, status := .proved
    theorems := [``L4Factoidal.RDF.Dataset.den_iso_renameBnodes,
      ``L4Factoidal.RDF.Dataset.den_renameBnodes, ``L4Factoidal.RDF.Dataset.renameBnodes_isSet,
      ``L4Factoidal.RDF.Dataset.renameBnodes_invertible, ``L4Factoidal.RDF.DatasetDen.iso_equivalence]
    note := "DatasetDen.Iso: one relabelling over graphs, graph names and triple terms" },
  { area := "W3C harness fixture loading (data and graph files as separate documents)", dir := "RDF"
    wireIn := .files, wireOut := .dataset, status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all (l4w3c)", "Harness/HarnessTests.lean fixture-scope #guards"]
    note := "each file scoped by its index (addDataFile, addGraphFile)" },
  { area := "Reader: N-Triples (batch)", dir := "Syntax"
    stage := ``ntriplesReader, wireIn := .text, wireOut := .dataset
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error; RDF 1.2 mode reads triple terms" },
  { area := "Reader: N-Quads (batch)", dir := "Syntax"
    stage := ``nquadsReader, wireIn := .text, wireOut := .dataset
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error" },
  { area := "Reader: Turtle (batch)", dir := "Syntax"
    stage := ``turtleReader, wireIn := .text, wireOut := .dataset
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error" },
  { area := "Reader: TriG (batch)", dir := "Syntax"
    stage := ``trigReader, wireIn := .text, wireOut := .dataset
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error; empty named graphs kept" },
  { area := "Reader: RDF/XML (batch)", dir := "Syntax"
    stage := ``rdfxmlReader, wireIn := .text, wireOut := .dataset
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error" },
  { area := "Reader: JSON-LD to RDF (batch)", dir := "Syntax"
    stage := ``jsonldReader, wireIn := .text, wireOut := .dataset
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error; Source.withJsonLd" },
  { area := "Reader: RDF/JSON (W3C Note, triples only)", dir := "Syntax"
    stage := ``rdfJsonReader, wireIn := .text, wireOut := .dataset
    contract := ``RdfJsonContract, status := .proved
    theorems := [``L4Factoidal.RDF.Dataset.den_toSet, ``L4Factoidal.RDF.Dataset.den_iso_scopeDocument,
      ``L4Factoidal.RDF.Dataset.den_renameBnodes]
    note := "default graph only; no W3C suite; used by RML targets" },
  { area := "RdfReader: N-Triples (wasm dispatch)", dir := "Syntax"
    stage := ``ntriplesDocumentReader, wireIn := .text, wireOut := .datasetPrefixes, params := ["mode", "base"]
    contract := ``ReaderContract, status := .proved
    theorems := [``documentReader, ``parseDocumentWithPrefixes_map_fst, ``readerContract_of_set,
      ``parseDocument_error_iff, ``RdfReader.isSet, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "RdfReader interface type: the contract (set, document scope n, den, Iso, labels-only change) and error iff parser error are fields; the table readers serves the wasm document ops" },
  { area := "RdfReader: N-Quads (wasm dispatch, dataset handles)", dir := "Syntax"
    stage := ``nquadsDocumentReader, wireIn := .text, wireOut := .datasetPrefixes, params := ["mode", "base"]
    contract := ``ReaderContract, status := .proved
    theorems := [``documentReader, ``parseDocumentWithPrefixes_map_fst, ``readerContract_of_set,
      ``parseDocument_error_iff, ``RdfReader.isSet, ``L4Factoidal.RDF.Source.parseDocument_set, ``readNQuadsText_eq]
    note := "RdfReader interface type: the contract (set, document scope n, den, Iso, labels-only change) and error iff parser error are fields; the table readers serves the wasm document ops; also reads the N-Quads text of a dataset handle (readNQuadsText)" },
  { area := "RdfReader: Turtle (wasm dispatch)", dir := "Syntax"
    stage := ``turtleDocumentReader, wireIn := .text, wireOut := .datasetPrefixes, params := ["mode", "base"]
    contract := ``ReaderContract, status := .proved
    theorems := [``documentReader, ``parseDocumentWithPrefixes_map_fst, ``readerContract_of_set,
      ``parseDocument_error_iff, ``RdfReader.isSet, ``L4Factoidal.RDF.Source.parseDocument_set, ``L4Factoidal.Syntax.parseTurtleTextWithPrefixes_map_fst]
    note := "RdfReader interface type: the contract (set, document scope n, den, Iso, labels-only change) and error iff parser error are fields; the table readers serves the wasm document ops; the prefixes are extra output, pinned by #guards (TurtleChunkFoldTests.lean)" },
  { area := "RdfReader: TriG (wasm dispatch)", dir := "Syntax"
    stage := ``trigDocumentReader, wireIn := .text, wireOut := .datasetPrefixes, params := ["mode", "base"]
    contract := ``ReaderContract, status := .proved
    theorems := [``documentReader, ``parseDocumentWithPrefixes_map_fst, ``readerContract_of_set,
      ``parseDocument_error_iff, ``RdfReader.isSet, ``L4Factoidal.RDF.Source.parseDocument_set, ``L4Factoidal.Syntax.parseTriGWithPrefixes_map_fst]
    note := "RdfReader interface type: the contract (set, document scope n, den, Iso, labels-only change) and error iff parser error are fields; the table readers serves the wasm document ops" },
  { area := "RdfReader: RDF/XML (wasm dispatch)", dir := "Syntax"
    stage := ``rdfxmlDocumentReader, wireIn := .text, wireOut := .datasetPrefixes, params := ["mode", "base"]
    contract := ``ReaderContract, status := .proved
    theorems := [``documentReader, ``parseDocumentWithPrefixes_map_fst, ``readerContract_of_set,
      ``parseDocument_error_iff, ``RdfReader.isSet, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "RdfReader interface type: the contract (set, document scope n, den, Iso, labels-only change) and error iff parser error are fields; the table readers serves the wasm document ops" },
  { area := "RdfReader: JSON-LD to RDF (full wasm dispatch)", dir := "Syntax"
    stage := ``jsonldDocumentReader, wireIn := .text, wireOut := .datasetPrefixes, params := ["mode", "base"]
    contract := ``ReaderContract, status := .proved
    theorems := [``documentReader, ``parseDocumentWithPrefixes_map_fst, ``readerContract_of_set,
      ``parseDocument_error_iff, ``RdfReader.isSet, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "RdfReader interface type: the contract (set, document scope n, den, Iso, labels-only change) and error iff parser error are fields; the table readers serves the wasm document ops; Source.withJsonLd; the core dispatch refuses JSON-LD by name" },
  { area := "Reader grammar: N-Triples", dir := "Syntax"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["W3C RDF 1.1 rdf-n-triples (l4w3c)", "W3C RDF 1.2 rdf-n-triples (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: N-Quads", dir := "Syntax"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["W3C RDF 1.1 rdf-n-quads (l4w3c)", "W3C RDF 1.2 rdf-n-quads (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: Turtle", dir := "Syntax"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["W3C RDF 1.1 rdf-turtle (l4w3c)", "W3C RDF 1.2 rdf-turtle (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: TriG", dir := "Syntax"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["W3C RDF 1.1 rdf-trig (l4w3c)", "W3C RDF 1.2 rdf-trig (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: RDF/XML", dir := "Syntax"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["W3C RDF 1.1 rdf-xml (l4w3c)", "W3C RDF 1.2 rdf-xml (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: JSON-LD to RDF", dir := "JSONLD"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["W3C JSON-LD 1.1 toRdf (l4jsonld-probe)"]
    note := "grammar and algorithm conformance are not proved" },
  { area := "Reader grammar: RDF/JSON", dir := "Syntax"
    wireIn := .text, wireOut := .dataset, status := .tested
    tests := ["Syntax/RdfJson.lean #guards", "Dataflow/PhaseCTests.lean"]
    note := "no W3C suite exists" },
  { area := "Streamed N-Triples and Turtle output as a set (dedup consumer)", dir := "RDF"
    stage := ``streamSetStage, wireIn := .chunks, wireOut := .graph
    contract := ``StreamSetContract, status := .proved
    theorems := [``L4Factoidal.RDF.runChunks_eq_toSet, ``L4Factoidal.RDF.runChunks_keyNodup,
      ``L4Factoidal.RDF.runChunks_written]
    note := "the consumer half; the reader half (chunks = batch parse) is the next entry" },
  { area := "Streamed N-Triples and Turtle reader: chunk cut equals batch parse", dir := "Syntax"
    wireIn := .chunks, wireOut := .triples, status := .tested
    theorems := [``L4Factoidal.RDF.Source.turtleStep_collect]
    tests := ["RDF/Source.lean #guards (every cut position)", "tests/known-defects/run.sh rows SF-1, SF-2, SF-4"]
    note := "not proved: https://github.com/danbri/factoidal/issues/826" },
  { area := "Streamed N-Quads reader, RDF 1.1 (chunks to the batch dataset)", dir := "RDF"
    stage := ``nquads11StreamStage, wireIn := .chunks, wireOut := .dataset
    contract := ``NQuadsStreamContract, status := .proved
    theorems := [``L4Factoidal.RDF.Source.nquads11_readAll_eq_parseNQuadsFast, ``nquads11Stream_reader]
    note := "streamed then scoped = nquadsReader on the joined text" },
  { area := "Streamed N-Quads reader, RDF 1.2", dir := "Syntax"
    wireIn := .chunks, wireOut := .dataset, status := .tested
    tests := ["tests/known-defects/run.sh row SF-3"]
    note := "not proved: https://github.com/danbri/factoidal/issues/826" },
  { area := "Streamed TriG reader (chunk fold)", dir := "Syntax"
    wireIn := .chunks, wireOut := .quads, status := .tested
    tests := ["tests/trig-pack/order_xfail.sh", "tests/trig-pack/compare_w3c.sh"]
    note := "chunk fold vs parseTriG not proved; source order differs for a default block after a named block: https://github.com/danbri/factoidal/issues/836" },
  { area := "Streamed RDF/XML reader (item by item)", dir := "Syntax"
    wireIn := .chunks, wireOut := .quads, status := .tested
    theorems := [``L4Factoidal.RDF.Source.rdfxml_readAll_of_notStreamed]
    tests := ["tests/known-defects/run.sh row RX-1", "l4rdfxml-chunk-diff"]
    note := "fall-back mode proved (rdfxml_readAll_of_notStreamed); item mode measured: https://github.com/danbri/factoidal/issues/936" },
  { area := "Streamed JSON-LD reader (top-level node objects)", dir := "JSONLD"
    wireIn := .chunks, wireOut := .quads, status := .tested
    theorems := [``L4Factoidal.RDF.Source.jsonld_readAll_of_notStreamed, ``L4Factoidal.RDF.Source.jsonld_readAll]
    tests := ["tests/known-defects/run.sh row JS-1", "l4jsonld-chunk-diff"]
    note := "whole-reader mode proved (jsonld_readAll_of_notStreamed); item mode measured: https://github.com/danbri/factoidal/issues/946" },
  { area := "Writer: N-Triples (round trip on the projection)", dir := "Syntax"
    stage := ``ntriplesWriter, wireIn := .dataset, wireOut := .text
    contract := ``WriterContract, status := .proved
    theorems := [``writerContract_nt, ``writerRoundTrip_nt, ``writerProjection_triples_den, ``L4Factoidal.RDF.writeLabelMap_injOn, ``L4Factoidal.RDF.writeLabelMap_valid, ``L4Factoidal.Syntax.NTriplesRoundTrip.Triple.ntLex_renameBnodes, ``L4Factoidal.Syntax.NTriplesRoundTrip.parseNTriples_toNTriples, ``L4Factoidal.Syntax.NTriplesRoundTrip.readTriple11_line, ``L4Factoidal.Syntax.NTriplesRoundTrip.readTriple12_line, ``L4Factoidal.Syntax.NTriplesRoundTrip.readStringLiteralBody_escape, ``L4Factoidal.Syntax.NTriplesRoundTrip.readObject12_safe]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/NTriplesDocRoundTrip.lean counter-example #guards"]
    note := "RDF 1.1 and 1.2 modes; projection: union of all graphs, no graph name (writerProjection_triples_den); domain: IRIREF and LANGTAG lexical spaces (Triple.ntSafe); blank-node labels outside BLANK_NODE_LABEL are relabelled (Dataset.relabelForWrite, writeLabelMap_injOn; isomorphism = the relabelling), language tags outside LANGTAG are an error (https://github.com/danbri/factoidal/issues/986)" },
  { area := "Writer: N-Quads (round trip on the projection)", dir := "Syntax"
    stage := ``nquadsWriter, wireIn := .dataset, wireOut := .text
    contract := ``WriterContract, status := .proved
    theorems := [``writerContract_nquads, ``writerRoundTrip_nquads, ``writerProjection_nquads_den, ``writerProjection_nquads_renameBnodes, ``L4Factoidal.Syntax.NQuadsRoundTrip.Quad.ntLex_renameBnodes, ``L4Factoidal.Syntax.NQuadsRoundTrip.parseNQuads_toNQuads, ``L4Factoidal.Syntax.NQuadsRoundTrip.toNQuads_lines, ``L4Factoidal.Syntax.NQuadsRoundTrip.addAll_quadsOf_memQuad, ``L4Factoidal.Syntax.NQuadsRoundTrip.addAll_quadsOf_names, ``L4Factoidal.Syntax.parseNQuadsFast_eq_parseNQuads]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/NQuadsDocRoundTrip.lean counter-example #guards"]
    note := "RDF 1.1 and 1.2 modes; projection: empty named graphs dropped (writerProjection_nquads_den); domain: Quad.ntSafe (the N-Triples domain and an IRI graphLabel in IRIREF); blank-node labels and graph labels outside BLANK_NODE_LABEL are relabelled (Dataset.relabelForWrite), language tags outside LANGTAG are an error (https://github.com/danbri/factoidal/issues/986)" },
  { area := "Writer: Turtle (round trip on the projection)", dir := "Syntax"
    wireIn := .dataset, wireOut := .text, status := .tested
    theorems := [``writerProjection_triples_den]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)"]
    note := "projection: union of all graphs (writerProjection_triples_den); WriterRoundTrip stated, not proved" },
  { area := "Writer: TriG (round trip, whole dataset)", dir := "Syntax"
    wireIn := .dataset, wireOut := .text, status := .tested
    theorems := [``writerProjection_dataset]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)"]
    note := "no projection: empty named graphs and blank-node graph names kept (writerProjection_dataset); WriterRoundTrip stated, not proved" },
  { area := "Writer: RDF/XML (round trip on the projection)", dir := "Syntax"
    wireIn := .dataset, wireOut := .text, status := .tested
    theorems := [``writerProjection_triples_den]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/RdfXmlWrite.lean #guards"]
    note := "projection: union of all graphs; domain: no triple term (refused with an error); finding fixed in phase C: base direction was dropped" },
  { area := "Writer: JSON-LD fromRdf (round trip, whole dataset)", dir := "JSONLD"
    wireIn := .dataset, wireOut := .text, status := .tested
    theorems := [``writerProjection_dataset]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "W3C JSON-LD 1.1 fromRdf (l4jsonld-api)"]
    note := "domain: no triple term (refused), no directional language string (written as @direction; the JSON-LD 1.1 reader with no rdfDirection drops it, https://github.com/danbri/factoidal/issues/984)" },
  { area := "RdfWriter: N-Triples (wasm dispatch)", dir := "Syntax"
    stage := ``ntriplesDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .proved
    theorems := [``writerContractW_nt, ``serializeWith_default, ``writers_run_default, ``writerProjection_triples_den, ``RdfWriter.claim_of_proved, ``RdfWriter.roundTrip_of_claim]
    note := "RdfWriter interface type: the round trip with the matching RdfReader (domain, projection, Iso) is a field, proved for RDF 1.1 and 1.2; the table writers serves the wasm dataset-handle writers" },
  { area := "RdfWriter: N-Quads (batch)", dir := "Syntax"
    stage := ``nquadsDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .proved
    theorems := [``writerContractW_nquads, ``serializeWith_default, ``writers_run_default, ``writerProjection_nquads_den, ``RdfWriter.claim_of_proved, ``RdfWriter.roundTrip_of_claim]
    note := "RdfWriter interface type: round trip proved, RDF 1.1 and 1.2; empty named graphs are not written (projection)" },
  { area := "RdfWriter: Turtle (wasm dispatch)", dir := "Syntax"
    stage := ``turtleDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .assumed
    theorems := [``serializeWith_default, ``writers_run_default, ``RdfWriter.roundTrip_of_claim, ``writerProjection_triples_den]
    ioAssumptions := [``TurtleWriterRoundTrip]
    note := "round trip with the Turtle reader is the named assumption TurtleWriterRoundTrip, for any Turtle options; tested on seeded datasets" },
  { area := "RdfWriter: TriG (wasm dispatch)", dir := "Syntax"
    stage := ``trigDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .assumed
    theorems := [``serializeWith_default, ``writers_run_default, ``RdfWriter.roundTrip_of_claim, ``writerProjection_dataset]
    ioAssumptions := [``TrigWriterRoundTrip]
    note := "round trip with the TriG reader is the named assumption TrigWriterRoundTrip; tested on seeded datasets" },
  { area := "RdfWriter: RDF/XML (wasm dispatch)", dir := "Syntax"
    stage := ``rdfxmlDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .assumed
    theorems := [``serializeWith_default, ``writers_run_default, ``RdfWriter.roundTrip_of_claim, ``writerProjection_triples_den]
    ioAssumptions := [``RdfXmlWriterRoundTrip]
    note := "round trip with the RDF/XML reader is the named assumption RdfXmlWriterRoundTrip; domain: no triple term" },
  { area := "RdfWriter: JSON-LD (full engine)", dir := "Syntax"
    stage := ``jsonldDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .assumed
    theorems := [``serializeWith_default, ``writers_run_default, ``RdfWriter.roundTrip_of_claim, ``writerProjection_dataset]
    ioAssumptions := [``JsonLdWriterRoundTrip]
    note := "round trip with the JSON-LD reader is the named assumption JsonLdWriterRoundTrip; domain: no triple term, no directional language string (https://github.com/danbri/factoidal/issues/984)" },
  { area := "RdfWriter: canonical N-Quads (dataset handles)", dir := "Syntax"
    stage := ``canonicalNQuadsDocumentWriter, wireIn := .dataset, wireOut := .text, params := ["mode", "render options"]
    contract := ``RoundTripOn, status := .assumed
    theorems := [``serializeWith_default, ``writers_run_default, ``RdfWriter.roundTrip_of_claim, ``writerProjection_nquads_den, ``L4Factoidal.RDF.parseNQuadsFast_toCanonicalNQuads]
    ioAssumptions := [``CanonicalNQuadsWriterRoundTrip]
    note := "round trip is the named assumption CanonicalNQuadsWriterRoundTrip; the parse of the text is normalizeDataset (parseNQuadsFast_toCanonicalNQuads) but its denotation is not yet related to the projection" },
  { area := "Writer: RDF/JSON (round trip, triples only)", dir := "Syntax"
    wireIn := .graph, wireOut := .text, status := .tested
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/RdfJson.lean #guards"]
    note := "the union of the graphs; no graph name; triple terms refused" },
  { area := "Stream writers (Sink.Writer, all syntaxes)", dir := "RDF"
    wireIn := .quads, wireOut := .text, status := .tested
    theorems := [``L4Factoidal.RDF.Sink.runList_rdfxml_eq, ``L4Factoidal.RDF.Sink.runList_jsonld_eq]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2) via streamDataset", "tests/sbm11/export_roundtrip.sh"]
    note := "RDF/XML stream = whole writer for contiguous subjects (runList_rdfxml_eq); JSON-LD elements in order (runList_jsonld_eq); the rest tested" },
  { area := "JSON-LD expansion, compaction, framing", dir := "JSONLD"
    wireIn := .json, wireOut := .json, status := .missing },
  { area := "SBM11 pack (dataset to generation and files)", dir := "Storage"
    stage := ``sbm11PackStage, wireIn := .dataset, wireOut := .generations
    contract := ``PackContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.PackSpec.den_packSpec,
      ``L4Factoidal.Storage.Sbm11.PackSpec.packSpec_written,
      ``L4Factoidal.Storage.Sbm11.PackSpec.packSpec_check,
      ``L4Factoidal.Storage.Sbm11.PackSpec.datasetOf_of_den,
      ``L4Factoidal.Storage.Sbm11.AllowedPerm.allowed_perm, ``packContract_of]
    note := "answer transfer needs Sbm11Folded (finding 3)" },
  { area := "SBM11 disk (write files, positioned reads)", dir := "Storage"
    stage := ``sbm11Disk, wireIn := .fileGen, wireOut := .fileGen, status := .assumed
    ioAssumptions := [``ReadsWritten]
    note := "Session caches not covered" },
  { area := "SBM11 WHERE over the files", dir := "Storage"
    stage := ``sbm11WhereStage, wireIn := .generations, wireOut := .idTable
    contract := ``WhereContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.MemGen.harness_where_allowed_file,
      ``L4Factoidal.Storage.Sbm11.MemGen.store_written]
    note := "the output store decodes the table (sbm11DecodeStage)" },
  { area := "SBM11 id table to solution sequence", dir := "Storage"
    stage := ``sbm11DecodeStage, wireIn := .idTable, wireOut := .solutions
    contract := ``DecodeRowsContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.SubSelect.decodeRowsM_run]
    note := "decodeRowsM, the decoder of the shipped nested path" },
  { area := "End to end: document bytes to SBM11 WHERE answer", dir := "Dataflow"
    stage := ``documentToWhere, wireIn := .document, wireOut := .idTable
    contract := ``documentToWhere_sound, status := .proved
    theorems := [``documentToWhere_sound, ``Stage.comp_ok_contract]
    ioAssumptions := [``ReadsWritten]
    note := "document scope n; raw parse to generation is DatasetDen.Iso; premises: ReadsWritten, plan hypotheses, QHyps, Sbm11Folded, PermOk" },
  { area := "End to end: document bytes to SolutionSeq (SBM11 id path)", dir := "Dataflow"
    stage := ``documentToSolutions, wireIn := .document, wireOut := .solutions
    contract := ``documentToSolutions_sound, status := .proved
    theorems := [``documentToSolutions_sound, ``documentToWhere_sound,
      ``L4Factoidal.Storage.Sbm11.LocalVocab.termOf_withLocal,
      ``L4Factoidal.Storage.Sbm11.MemGen.store_written,
      ``L4Factoidal.Storage.Sbm11.MemGen.mem_htermOf]
    ioAssumptions := [``ReadsWritten]
    note := "decoded solutions = the sequence WhereOk allows, with multiplicity; premises as above" },
  { area := "SBM11 session and its caches", dir := "Storage"
    wireIn := .files, wireOut := .idTable, status := .tested
    tests := ["SBM11 gate (tests/sbm11/run.sh)"] },
  { area := "SBM11 delta overlay (INSERT, DELETE, CREATE)", dir := "Storage"
    stage := ``sbm11OverlayStage, wireIn := .logState, wireOut := .logState, params := ["log entry"]
    contract := ``OverlayStepContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_add,
      ``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_remove,
      ``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_remove_sbm11_vocab,
      ``L4Factoidal.Storage.Sbm11.Overlay.heldFolded_sbm11,
      ``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_create_names,
      ``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_create_graph,
      ``L4Factoidal.Storage.Sbm11.OverlayDict.overlay_dictInjective,
      ``sbm11OverlayStage_add, ``sbm11OverlayStage_remove]
    note := "HeldFolded proved (heldFolded_sbm11); open: that Session.idOrNew computes vocabAddAll, CLEAR and DROP (no denotation theorem), replay of a log" },
  { area := "Block store IBK3 (one graph): write, then read", dir := "Storage"
    stage := ``ibk3RoundTripStage, wireIn := .block, wireOut := .block
    contract := ``BlockDenEq, status := .proved
    theorems := [``L4Factoidal.Storage.IndexedBlockWireV3.den_decode_encode?,
      ``L4Factoidal.Storage.IndexedBlock.Block.den_eq_ofRows,
      ``L4Factoidal.Storage.IndexedBlock.fromParts?_foldedDictInjective, ``ibk3RoundTrip_den]
    note := "den of the block read back = den of the block written; one id per RDF term (issue 977)" },
  { area := "Block store IBK4 (quads): write, then read", dir := "Storage"
    stage := ``ibk4RoundTripStage, wireIn := .quadBlock, wireOut := .quadBlock
    contract := ``Ibk4DenEq, status := .proved
    theorems := [``L4Factoidal.Storage.IndexedBlockWireV4.den_decode_encode?,
      ``L4Factoidal.Storage.StoreDictTheorems.v4_fromParts?_foldedDictInjective, ``ibk4RoundTrip_den]
    note := "den preserved; a quad block cannot hold an empty named graph (den_names_nonempty, issue 880)" },
  { area := "Block store IBK5 (quads, out-of-line literals): write, then read", dir := "Storage"
    stage := ``ibk5RoundTripStage, wireIn := .quadBlock, wireOut := .quadBlock
    contract := ``Ibk5DenEq, status := .proved
    theorems := [``L4Factoidal.Storage.IndexedBlockWireV5.den?_decode_encode?,
      ``L4Factoidal.Storage.IndexedBlockWireV5.den?_decode_encode?_toWire,
      ``L4Factoidal.Storage.StoreDictTheorems.v5_fromParts?_foldedDictInjective, ``ibk5RoundTrip_den]
    note := "den? equal for every hash function and blob lookup" },
  { area := "Block store IBK3: build from a graph (fromGraph), write, then read", dir := "Storage"
    stage := ``ibk3BuildWriteReadStage, wireIn := .graph, wireOut := .block
    contract := ``Ibk3BuildDen, status := .proved
    theorems := [``L4Factoidal.Storage.IndexedBlock.fromGraph_denotes,
      ``L4Factoidal.Storage.IndexedBlock.fromGraph_den,
      ``L4Factoidal.Storage.IndexedBlockWireV3.den_decode_encode?_fromGraph, ``ibk3BuildWriteRead_den]
    note := "den of the block read back = graphDen of the input graph; no Dataset.IsSet hypothesis; the rows decode to the input with terms folded (issue 977); BlockMvp is built by its record constructor (den = graphDen of its rows by definition) and has no wire format" },
  { area := "Block store IBK4: build from quads (fromQuads), write, then read", dir := "Storage"
    stage := ``ibk4BuildWriteReadStage, wireIn := .quads, wireOut := .quadBlock
    contract := ``Ibk4BuildDen, status := .proved
    theorems := [``L4Factoidal.Storage.IndexedBlockWireV4.fromQuads_denotes,
      ``L4Factoidal.Storage.IndexedBlockWireV4.fromQuads_den,
      ``L4Factoidal.Storage.IndexedBlockWireV4.fromQuads_listQuads_den,
      ``L4Factoidal.Storage.IndexedBlockWireV4.den_decode_encode?_fromQuads,
      ``ibk4BuildWriteRead_den, ``ibk4BuildWriteRead_dataset]
    note := "den read back = DatasetDen.ofQuads of the input; for a Dataset, ds.den when no named graph is empty (issue 880)" },
  { area := "Block store IBK5: build from RDF quads (toWire), write, then read", dir := "Storage"
    stage := ``ibk5BuildWriteReadStage, wireIn := .quads, wireOut := .quadBlock
    contract := ``Ibk5BuildDen, status := .proved
    theorems := [``L4Factoidal.Storage.IndexedBlockWireV5.fromQuads_denotes,
      ``L4Factoidal.Storage.TermWireV2.resolve_foldWire,
      ``L4Factoidal.Storage.IndexedBlockWireV5.den?_fromRdfQuads,
      ``L4Factoidal.Storage.IndexedBlockWireV5.den?_decode_encode?_fromRdfQuads, ``ibk5BuildWriteRead_den]
    note := "den? read back = some (ofQuads input) when the blob lookup resolves each object (premise of the contract; TermWireV2.resolve_toWire gives it for the packer's own lookup)" },
  { area := "Streaming packer (pack ops, factoidal pack): the rows written are a set", dir := "Storage"
    stage := ``packSetStage, wireIn := .chunks, wireOut := .graph
    contract := ``PackSetContract, status := .proved
    theorems := [``packedRows_eq, ``packedRows_keyNodup,
      ``L4Factoidal.Storage.PackSet.dedupBatch_written, ``L4Factoidal.Storage.PackSet.dedupBatch_toGraph,
      ``L4Factoidal.Storage.PackSet.addFreshQuad_fresh]
    tests := ["npm/factoidal/test/pack-is-a-set-1006.test.mjs (pack, activate, COUNT(*) for IBK3, IBK4, IBK5)"]
    note := "https://github.com/danbri/factoidal/issues/1006; PackStream.ingestFeed and ingestFinish (IBK2/IBK3) call PackSet.dedupBatch with one seen graph, and addQuadPub (IBK4/IBK5) calls PackSet.addFreshQuad; that the ingest loop is this fold is by construction, not a theorem; block encoding is the block-builder entries" },
  { area := "Store interface StoreCaps (planner)", dir := "SPARQL"
    stage := ``storeSearchStage, wireIn := .patternBound, wireOut := .triples
    contract := ``SearchContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.StoreBackend.capsOfBackend_exact,
      ``L4Factoidal.SPARQL.StoreBackend.backendSearch_exact,
      ``L4Factoidal.SPARQL.StoreBackend.backendSearch_nodupKeys,
      ``L4Factoidal.RDF.capsOfIndexed_default_denotes, ``L4Factoidal.RDF.unionCaps_exact,
      ``L4Factoidal.RDF.overlay_exact, ``backendExact_indexed_default, ``indexedDefaultSearch_sound]
    note := "StoreCapsExact (RDF/StoreCapsDenotation.lean); premise BackendExact: list and index from Dataset.IsSet; HDT and COTTAS readers rest on BackendReadOpsExact, CottasReadOpsExact (not proved); RML on RmlPushdownInvisible (open)" },
  { area := "LawfulStore: list (data-access interface)", dir := "Dataflow"
    stage := ``LawfulStore.ofList, wireIn := .patternBound, wireOut := .triples
    contract := ``L4Factoidal.RDF.StoreCapsExact, status := .proved
    theorems := [``LawfulStore.exact, ``LawfulStore.search_exact, ``LawfulStore.search_nodupKeys, ``L4Factoidal.SPARQL.StoreBackend.capsOfList_exact]
    note := "LawfulStore interface type (Dataflow/Store.lean): backend, graph, named assumptions, law BackendExact as fields; premise g.KeyNodup" },
  { area := "LawfulStore: in-memory index", dir := "Dataflow"
    stage := ``LawfulStore.ofIndexed, wireIn := .patternBound, wireOut := .triples
    contract := ``L4Factoidal.RDF.StoreCapsExact, status := .proved
    theorems := [``LawfulStore.exact, ``LawfulStore.search_exact, ``LawfulStore.search_nodupKeys, ``L4Factoidal.RDF.capsOfIndexed_exact]
    note := "premise g.KeyNodup; the index is Index.ofGraph g" },
  { area := "LawfulStore: any StoreCaps record with its law", dir := "Dataflow"
    stage := ``LawfulStore.ofCaps, wireIn := .patternBound, wireOut := .triples
    contract := ``L4Factoidal.RDF.StoreCapsExact, status := .proved
    theorems := [``LawfulStore.exact, ``LawfulStore.search_exact, ``LawfulStore.search_nodupKeys]
    note := "the GraphBackend arm .caps c; its law is StoreCapsExact G c" },
  { area := "LawfulStore: base plus resolved delta (overlay)", dir := "Dataflow"
    stage := ``LawfulStore.overlay, wireIn := .patternBound, wireOut := .triples
    contract := ``L4Factoidal.RDF.StoreCapsExact, status := .proved
    theorems := [``LawfulStore.exact, ``LawfulStore.search_exact, ``LawfulStore.search_nodupKeys, ``L4Factoidal.RDF.overlay_exact, ``LawfulStore.overlay_caps]
    note := "reads overlayPred of the base graph; keeps the base store's named assumptions" },
  { area := "LawfulStore: union of stores (set union)", dir := "Dataflow"
    stage := ``LawfulStore.union, wireIn := .patternBound, wireOut := .triples
    contract := ``L4Factoidal.RDF.StoreCapsExact, status := .proved
    theorems := [``LawfulStore.exact, ``LawfulStore.search_exact, ``LawfulStore.search_nodupKeys, ``L4Factoidal.RDF.unionCaps_exact, ``LawfulStore.backendsExact_map, ``LawfulStore.union_caps]
    note := "reads unionPred of the members' graphs; the assumptions are those of the members" },
  { area := "LawfulStore: HDT reader", dir := "Dataflow"
    stage := ``LawfulStore.hdt, wireIn := .patternBound, wireOut := .triples, status := .assumed
    ioAssumptions := [``L4Factoidal.SPARQL.StoreBackend.BackendReadOpsExact]
    note := "named assumption backendReadOpsExact (file access); the law follows from it (capsOfReadOps_exact)" },
  { area := "LawfulStore: in-memory COTTAS reader", dir := "Dataflow"
    stage := ``LawfulStore.cottasInMemory, wireIn := .patternBound, wireOut := .triples, status := .assumed
    ioAssumptions := [``L4Factoidal.SPARQL.StoreBackend.BackendReadOpsExact]
    note := "named assumption backendReadOpsExact" },
  { area := "LawfulStore: COTTAS on disk", dir := "Dataflow"
    stage := ``LawfulStore.cottasOnDisk, wireIn := .patternBound, wireOut := .triples, status := .assumed
    ioAssumptions := [``L4Factoidal.RDF.CottasReadOpsExact]
    note := "named assumption cottasReadOpsExact (file access); capsOfCottas_exact" },
  { area := "LawfulStore: COTTAS on disk plus delta", dir := "Dataflow"
    stage := ``LawfulStore.cottasOnDiskDelta, wireIn := .patternBound, wireOut := .triples, status := .assumed
    ioAssumptions := [``L4Factoidal.RDF.CottasReadOpsExact]
    note := "named assumption cottasReadOpsExact; overlay_exact" },
  { area := "LawfulStore: virtual RML source", dir := "Dataflow"
    stage := ``LawfulStore.virtualRml, wireIn := .patternBound, wireOut := .triples, status := .assumed
    ioAssumptions := [``L4Factoidal.SPARQL.StoreBackend.RmlPushdownInvisible, ``L4Factoidal.SPARQL.StoreBackend.RmlVirtualIsMaterialised]
    note := "two open named assumptions (#guards only); capsOfRmlSource_exact" },
  { area := "LawfulStore: list or index without a set proof", dir := "Dataflow"
    stage := ``LawfulStore.ofGraph, wireIn := .patternBound, wireOut := .triples, status := .assumed
    ioAssumptions := [``L4Factoidal.RDF.Graph.KeyNodup]
    note := "named assumption datasetIsSet (g.KeyNodup) at a call site that carries no proof (harness block diff tools); ofIndexedGraph is the same for the index" },
  { area := "LawfulDataset: in-memory dataset record, proved", dir := "Dataflow"
    stage := ``LawfulDataset.indexed, wireIn := .dataset, wireOut := .datasetBackend
    contract := ``L4Factoidal.Storage.PlannerSoundness.DatasetBackendExact, status := .proved
    theorems := [``L4Factoidal.Storage.PlannerSoundness.indexedDatasetBackend_exact]
    note := "premise Dataset.IsSet (the distinctNames premise was removed 2026-10-25: backend names are Subjects, issue 975); SBM11 meets it at the denotation (sbm11_record_denotes)" },
  { area := "LawfulDataset: dataset handle (CertifiedDataset)", dir := "Dataflow"
    stage := ``LawfulDataset.ofCertified, wireIn := .certifiedDataset, wireOut := .datasetBackend
    contract := ``L4Factoidal.Storage.PlannerSoundness.DatasetBackendExact, status := .proved
    theorems := [``LawfulDataset.ofCertified_proved, ``L4Factoidal.Storage.PlannerSoundness.indexedDatasetBackend_exact, ``LawfulDataset.ofCertified_backend]
    note := "no assumption for any graph name, IRI or blank node (ofCertified_proved; graphNameKeysDistinct removed 2026-10-25, issue 975). Used by the dataset handles, the queryDataset ops (readNQuadsCertified) and the end-to-end pipeline (loadStore)" },
  { area := "LawfulDataset: dataset without a set proof", dir := "Dataflow"
    stage := ``LawfulDataset.ofDataset, wireIn := .dataset, wireOut := .datasetBackend, status := .assumed
    ioAssumptions := [``L4Factoidal.RDF.Dataset.IsSet]
    theorems := [``LawfulDataset.ofDataset_backend]
    note := "named assumption datasetIsSet (graphNameKeysDistinct removed 2026-10-25, issue 975); used by storeQuery, storeHandleQuery, the served view (StoreEndpoint.View.of), the CLI and the harness query tools" },
  { area := "LawfulDataset: one store as the default graph", dir := "Dataflow"
    stage := ``LawfulDataset.ofDefault, wireIn := .store, wireOut := .datasetBackend
    contract := ``L4Factoidal.Storage.PlannerSoundness.DatasetBackendExact, status := .proved
    theorems := [``backendExact_congr, ``LawfulDataset.ofDefault_backend]
    note := "keeps the store's named assumptions; the harness block and shard query tools read HDT-arm stores through it" },
  { area := "Backend BGP evaluator over a LawfulStore", dir := "Dataflow"
    stage := ``lawfulBgpStage, wireIn := .store, wireOut := .solutions
    contract := ``LawfulBgpContract, status := .proved
    theorems := [``LawfulStore.evalBgp_kequiv, ``LawfulStore.evalBgp_kequiv_of_list, ``LawfulStore.evalBgp_kequiv_of_graph,
      ``L4Factoidal.Storage.BackendRefinement.evalBgpBackend_kequiv]
    note := "only premise: the store's named assumptions; reference evalBgp over the rows of the unbounded search, up to order and RDF term equality" },
  { area := "Backend WHERE evaluator over a LawfulDataset vs Allowed", dir := "Dataflow"
    stage := ``lawfulWhereStage, wireIn := .lawfulDataset, wireOut := .solutions
    contract := ``LawfulWhereContract, status := .proved
    theorems := [``LawfulDataset.where_allowed, ``LawfulDataset.graphRel_rows, ``LawfulDataset.namedRel_rows,
      ``L4Factoidal.Storage.BackendRefinement.evalPatternBackend_allowed]
    note := "NativeFrag; premise: named assumptions; over the dataset the record enumerates; the IRI-name premise was removed 2026-10-25 (backend names are Subjects, issue 975); the row-object premise was removed with PR 57 (issue 1001)" },
  { area := "COTTAS store", dir := "Cottas"
    wireIn := .dataset, wireOut := .bytes, status := .missing
    theorems := [``L4Factoidal.Cottas.cotd_dictInjective]
    note := "only the .dict term layer is proved (one id per RDF term when termRoundTripsAll holds, issue 977); missing: a theorem that the triples the reader returns from the bytes of serializeCottas denote the dataset written; the StoreCaps reader law CottasReadOpsExact is an assumption" },
  { area := "HDT store", dir := "HDT"
    wireIn := .dataset, wireOut := .bytes, status := .missing
    theorems := [``L4Factoidal.HDT.hdt_dictInjective]
    note := "only the dictionary layer is proved (one id per RDF term when roundTripsAll holds, issue 977); missing: a theorem that the triples read from an HDT file denote a dataset, and a writer; the reader law BackendReadOpsExact is an assumption" },
  { area := "Planner SELECT over the kept entries", dir := "Storage"
    stage := ``plannerSelectStage, wireIn := .dataset, wireOut := .solutions
    contract := ``PlannerSelectContract, status := .proved
    theorems := [``L4Factoidal.Storage.PlannerSoundness.plannerSoundnessSelect]
    note := "on the shipped path as the reference fallback of l4sbm11 query (finding 6)" },
  { area := "SBM11 reference-fallback read (selectedDataset)", dir := "Storage"
    stage := ``sbm11SelectedRead, wireIn := .generations, wireOut := .dataset, status := .assumed
    ioAssumptions := [``SelectedAgrees]
    note := "IO over Session; pure model Storage.SelectedDataset.selectedModel (den_selectedModel), keeps named graphs the selection empties; that the IO read returns the model is not proved" },
  { area := "SBM11 generation to planner SELECT (reference fallback)", dir := "Dataflow"
    stage := ``sbm11PlannerSelect, wireIn := .generations, wireOut := .solutions
    contract := ``sbm11PlannerSelect_sound, status := .proved
    theorems := [``sbm11PlannerSelect_sound,
      ``L4Factoidal.Storage.PlannerSoundness.plannerSoundnessSelect]
    ioAssumptions := [``SelectedAgrees]
    note := "answer = planner answer over G.denote; needs non-empty named graphs" },
  { area := "Reference fallback SELECT over the model of selectedDataset", dir := "Storage"
    stage := ``L4Factoidal.Storage.SelectedDataset.fallbackSelectStage, wireIn := .dataset, wireOut := .solutions
    contract := ``L4Factoidal.Storage.SelectedDataset.FallbackSelectContract, status := .proved
    theorems := [``L4Factoidal.Storage.SelectedDataset.referenceSelect_selected,
      ``L4Factoidal.Storage.SelectedDataset.referenceSelect_selectedModel,
      ``L4Factoidal.Storage.SelectedDataset.referenceSelect_selectedModel_graphs,
      ``L4Factoidal.Storage.SelectedDataset.den_selectedModel,
      ``L4Factoidal.Storage.SelectedDataset.applyDataset_mapRestrict,
      ``L4Factoidal.Storage.SelectedDataset.evalPatternBackend_active,
      ``L4Factoidal.SPARQL.DatasetRestriction.runSelectQueryBackendDataset_restrict]
    note := "answer over queryDataset of selectedModel = answer over queryDataset of the store (FROM merge, FROM NAMED, predicate and graph-name selection, empty named graphs); premises: SELECT form, IRI graph names; one env on both sides (the harness env.dataset differs, read only by EXISTS, which the collectors refuse; not proved); IO read = model not proved (finding 6)" },
  { area := "Backend BGP evaluator vs SPARQL 1.1 section 18.3 (reference evalBgp)", dir := "Storage"
    stage := ``L4Factoidal.Storage.BackendRefinement.backendBgpStage, wireIn := .graphBackend, wireOut := .solutions
    contract := ``L4Factoidal.Storage.BackendRefinement.BackendBgpContract, status := .proved
    theorems := [``L4Factoidal.Storage.BackendRefinement.evalBgpBackend_kequiv,
      ``L4Factoidal.Storage.BackendRefinement.evalBgpFrom_perm,
      ``L4Factoidal.Storage.BackendRefinement.evalSingleTpBackend_kequiv,
      ``L4Factoidal.Storage.BackendRefinement.tpMatch_boundMatches,
      ``L4Factoidal.Storage.BackendRefinement.evalBgpBackend_kequiv_of_den,
      ``L4Factoidal.Storage.BackendRefinement.evalBgpBackend_solEquiv]
    note := "every BGP, triple terms included; premises BackendExact gb G, a list g with G = KeyMem g and g.KeyNodup; the same multiset of solution mappings up to order and RDF term equality (Term.joinKey); structural (SolEquiv) with no further premise, since every term is its own join key (literalWf requires lower-case language tags, issue 1001); no-duplicate-row claim not made (finding 6)" },
  { area := "Reference fallback WHERE answer (evalPatternBackend, indexedDatasetBackend) vs Allowed", dir := "Storage"
    stage := ``L4Factoidal.Storage.BackendRefinement.fallbackWhereStage, wireIn := .dataset, wireOut := .solutions
    contract := ``L4Factoidal.Storage.BackendRefinement.FallbackWhereContract, status := .proved
    theorems := [``L4Factoidal.Storage.BackendRefinement.indexedWhere_allowed,
      ``L4Factoidal.Storage.BackendRefinement.evalPatternBackend_allowed,
      ``L4Factoidal.Storage.BackendRefinement.evalBgpBackend_allowed,
      ``L4Factoidal.Storage.BackendRefinement.filterFn_local]
    note := "NativeFrag: BGP without text:query, FILTER and OPTIONAL with a backendLocal condition, JOIN, UNION, MINUS, GRAPH with an IRI or a variable, VALUES, empty; premise Dataset.IsSet (the IRI-graph-name premise was removed 2026-10-25, issue 975); the GraphFixed premise was removed 2026-10-24 because literalWf requires lower-case language tags, so every graph satisfies it (issue 1001, #guards in the module) (finding 6)" },
  { area := "Reference fallback SELECT answer vs SPARQL 1.1 semantics and the id path", dir := "SPARQL"
    wireIn := .dataset, wireOut := .solutions, params := ["query"], status := .missing
    theorems := [``L4Factoidal.Storage.BackendRefinement.indexedWhere_allowed]
    note := "WHERE part proved for NativeFrag (row above); missing: the SELECT layer of runSelectQueryBackendDataset (streaming COUNT and GROUP BY, ORDER BY, projection, DISTINCT, slices), the arms outside NativeFrag (BIND, LATERAL, paths, sub-SELECT, non-local conditions), and that two Allowed answers of one pattern are one multiset; so id path and fallback are both allowed, not proved equal (finding 6)" },
  { area := "SPARQL query evaluator of the wasm query ops (LawfulEvaluator: backend path, else reference)"
    dir := "Dataflow"
    stage := ``shippedEvaluator, wireIn := .dataset, wireOut := .answer, params := ["env", "backend", "query"]
    contract := ``EvalContract, status := .proved
    theorems := [``shippedRun_sound, ``shippedRun_of_noBackend, ``shippedRun_of_from,
      ``shippedRun_of_construct, ``shippedRun_of_describe, ``evalSelectBackendDataset_plain,
      ``evalAskBackendReference_some, ``backendReads_indexed, ``LawfulEvaluator.contract,
      ``L4Factoidal.Storage.BackendRefinement.evalPatternBackend_allowed]
    note := "answer = reference evaluator (SPARQL.Query), or the modifier layer (selectPost, formHasSolution) over a WHERE answer Allowed admits; premises EvalInput.Wf (env.dataset = ds, ds.IsSet, BackendReads); named assumption field assumed_contractOn = shippedAssumed: backend path with a pattern outside NativeFrag (BackendOutsideFragmentAgrees) or a SELECT fast path (SelectFastPathAgrees); not claimed: two Allowed answers are one multiset, den invariance" },
  { area := "SPARQL query evaluation (reference evaluator)", dir := "SPARQL"
    wireIn := .dataset, wireOut := .results, params := ["query"], status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all (l4w3c)", "W3C SPARQL 1.2 (l4w3c)"] },
  { area := "SPARQL FROM default graph (RDF merge of the FROM graphs)", dir := "SPARQL"
    stage := ``L4Factoidal.SPARQL.FromMerge.fromMergeStage, wireIn := .graphs, wireOut := .graph
    contract := ``L4Factoidal.SPARQL.FromMerge.FromMergeContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.FromMerge.fromMerge_isMergeOf,
      ``L4Factoidal.SPARQL.FromMerge.applyDataset_default_isMergeOf,
      ``L4Factoidal.SPARQL.FromMerge.isMergeOf_pair]
    note := "SPARQL 1.1 section 13.2.1; two or more graphs relabelled by docLabel; one graph kept as it is (issue 979)" },
  { area := "SPARQL Update request on the dataset denotation", dir := "SPARQL"
    stage := ``updateStage, wireIn := .dataset, wireOut := .dataset, params := ["update"]
    contract := ``UpdateContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.applyUpdateIn_den, ``L4Factoidal.SPARQL.applyOp_den,
      ``L4Factoidal.RDF.applyUpdateIn_isSet, ``L4Factoidal.RDF.Dataset.den_insertQuads,
      ``L4Factoidal.RDF.Dataset.den_deleteQuads, ``L4Factoidal.RDF.Dataset.den_setGraph,
      ``L4Factoidal.RDF.Dataset.den_dropGraph, ``L4Factoidal.RDF.Dataset.den_ensureGraph,
      ``L4Factoidal.RDF.Dataset.den_clearAllNamed]
    note := "OpDen per operation: CLEAR keeps graph names, DROP removes them, CREATE adds a name with no triple; delete before insert; the result is a new value; needs IsSet" },
  { area := "SPARQL Update WHERE evaluation and template instantiation", dir := "SPARQL"
    wireIn := .dataset, wireOut := .quads, params := ["pattern"], status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all, update entries (l4w3c)"]
    note := "OpDen takes the quad lists of evalWhere and instQuads as inputs" },
  { area := "SPARQL protocol and graph store", dir := "SPARQL"
    wireIn := .httpRequest, wireOut := .httpResponse, status := .missing },
  { area := "SPARQL results formats (XML, JSON, CSV, TSV)", dir := "SPARQL"
    wireIn := .results, wireOut := .text, status := .missing },
  { area := "Graph selection (dataset to the union of selected graphs)", dir := "Dataflow"
    stage := ``selectStage, wireIn := .dataset, wireOut := .graph
    contract := ``SelectContract, status := .proved
    theorems := [``mem_select]
    note := "default graph and named graphs as a stage parameter; union, one blank-node scope (RDF 1.1 Concepts section 4)" },
  { area := "RDFS closure (soundness)", dir := "RDFS"
    stage := ``rdfsClosureStage, wireIn := .graph, wireOut := .graph
    contract := ``L4Factoidal.RDF.RdfsEntails, status := .proved
    theorems := [``L4Factoidal.RDF.fullClosure_entails] },
  { area := "RDFS closure over a graph selection (soundness)", dir := "Dataflow"
    stage := ``rdfsSelectStage, wireIn := .dataset, wireOut := .graph
    contract := ``rdfsSelect_sound, status := .proved
    theorems := [``rdfsSelect_sound, ``L4Factoidal.RDF.fullClosure_entails, ``mem_select]
    note := "finding 5 closed: the reasoner reads the selected graphs of a dataset" },
  { area := "RDFS entailment completeness, negative tests", dir := "RDFS"
    wireIn := .graph, wireOut := .bool, status := .missing
    theorems := [``L4Factoidal.RDF.rdfsEntails_subclassSelfLoop_iri]
    note := "false without the axiomatic triples (finding C-1); negative rdf-mt tests are evidence without proof" },
  { area := "ρdf closure (soundness; completeness when closed and in the fragment)", dir := "RDFS"
    stage := ``rhoDfClosureStage, wireIn := .graph, wireOut := .graph
    contract := ``RhoDfContract, status := .proved
    theorems := [``L4Factoidal.RDF.closure_rhoDfEntails, ``L4Factoidal.RDF.closure_rhoDf_iff]
    note := "dataset form: rhoDfSelectStage" },
  { area := "Simple entailment over a graph selection (sound and complete)", dir := "RDF"
    stage := ``simpleEntailsSelectStage, wireIn := .dataset, wireOut := .bool, params := ["graph"]
    contract := ``SimpleContract, status := .proved
    theorems := [``L4Factoidal.RDF.SimpleRefinement.simpleEntails_iff_spec,
      ``L4Factoidal.RDF.simpleEntails_iff_mt]
    note := "model-theoretic form for graphs without triple terms" },
  { area := "OWL 2 RL closure (soundness)", dir := "OWL"
    stage := ``owlRlClosureStage, wireIn := .graph, wireOut := .graph
    contract := ``RlContract, status := .proved
    theorems := [``L4Factoidal.OWL.RL.closure_sound, ``L4Factoidal.OWL.RL.rl_derives_holds]
    note := "dataset form: owlRlSelectStage" },
  { area := "OWL 2 RL completeness", dir := "OWL"
    wireIn := .graph, wireOut := .graph, status := .missing
    theorems := [``L4Factoidal.Unified.owlRl_complete_ground]
    note := "ground completeness needs a Derives-closed closure: open obligation closureFix_saturated (https://github.com/danbri/factoidal/issues/756)" },
  { area := "RIF closure (extensivity)", dir := "RIF"
    stage := ``rifClosureStage, wireIn := .facts, wireOut := .facts, params := ["rules"]
    contract := ``RifContract, status := .proved
    theorems := [``L4Factoidal.RIF.closure_extensive]
    note := "dataset form: rifSelectStage" },
  { area := "RIF soundness and the RDF to RIF mapping", dir := "RIF"
    wireIn := .graph, wireOut := .facts, params := ["rules"], status := .missing
    theorems := [``L4Factoidal.RIF.step_licensed]
    note := "per-round licensing is provenance, not truth; no RIF-BLD model theory; factsOfTriple has no contract" },
  { area := "SHACL validation (a conforming report implies Core conformance)", dir := "SHACL"
    stage := ``shaclStage, wireIn := .graph, wireOut := .validationReport, params := ["shapes graph"]
    contract := ``ShaclContract, status := .proved
    theorems := [``L4Factoidal.SHACL.validateWithSparql_sound_core,
      ``L4Factoidal.SHACL.validate_conforms_iff]
    note := "the l4shacl path: decodeShapesGraph, then validateFull; dataset form: shaclSelectStage" },
  { area := "SHACL validation, W3C suite", dir := "SHACL"
    wireIn := .graph, wireOut := .validationReport, params := ["shapes"], status := .tested
    tests := ["W3C SHACL Core (l4shacl)"]
    note := "the report's results list and the shapes-graph decoding (decodeShapesGraph) have no proved contract" },
  { area := "SPARQL basic graph pattern (soundness)", dir := "SPARQL"
    stage := ``bgpSelectStage, wireIn := .graph, wireOut := .solutions
    contract := ``BgpContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.evalBgp_instantiates_into_graph] },
  { area := "SPARQL ASK of a basic graph pattern (true implies a match)", dir := "SPARQL"
    stage := ``bgpAskStage, wireIn := .graph, wireOut := .bool
    contract := ``AskContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.evalBgp_instantiates_into_graph]
    note := "false is not proved to mean no match" },
  { area := "SPARQL basic graph pattern completeness", dir := "SPARQL"
    wireIn := .graph, wireOut := .solutions, status := .missing
    theorems := [``L4Factoidal.SPARQL.rdfsRegime_bgp_complete_conditional]
    note := "the named gap EvalBgpCompleteAt is a hypothesis, not proved" },
  { area := "End to end: document to RDFS closure of a selection to BGP answer", dir := "Dataflow"
    stage := ``documentToRdfsBgp, wireIn := .document, wireOut := .solutions
    contract := ``documentToRdfsBgp_sound, status := .proved
    theorems := [``documentToRdfsBgp_sound, ``rdfsEntails_of_mem, ``mem_select,
      ``L4Factoidal.RDF.fullClosure_entails, ``L4Factoidal.SPARQL.evalBgp_instantiates_into_graph]
    note := "premise hcmps; exactness for the entailment clause; tested only: parser grammar, query text to Bgp, algebra beyond a BGP" },
  { area := "ShEx validation", dir := "ShEx"
    wireIn := .graph, wireOut := .report, params := ["schema"], status := .missing },
  { area := "CSVW (tabular data to RDF)", dir := "CSVW"
    wireIn := .csv, wireOut := .dataset, params := ["metadata", "mode", "base", "url"], status := .tested
    tests := ["W3C CSVW csv2rdf (l4csvw-rdf)", "CSVW/ConversionTests.lean"]
    note := "csv2rdf conversion (CSVW/Conversion.lean); no Lean contract; npm node runs csvwToRdf with the settings recorded (Dataflow/NodeSettings.lean, https://github.com/danbri/factoidal/issues/975)" },
  { area := "RDFC-1.0 canonicalization (canonical N-Quads and SHA-256 hex)", dir := "RDF"
    stage := ``rdfcStage, wireIn := .dataset, wireOut := .canonical
    contract := ``RdfcContract, status := .proved
    theorems := [``L4Factoidal.RDF.Canonical.canonicalLines_sorted, ``canonicalNQuads_join,
      ``L4Factoidal.RDF.Canonical.mkLabel_inj]
    note := "lines in code point order; fails on the section 4.4 work budget; relabelling invariance is the next entry" },
  { area := "RDFC-1.0 relabelling invariance (isomorphic input, same canonical form)", dir := "RDF"
    wireIn := .dataset, wireOut := .text, status := .tested
    theorems := [``L4Factoidal.RDF.Canonical.hashFirstDegreeQuads_rename]
    tests := ["W3C RDFC-1.0 suite (l4rdfc-probe)", "Dataflow/PhaseETests.lean relabelling #guard"]
    note := "stated only (Canonical.RelabellingInvariance); the first-degree hash is proved invariant" },
  { area := "VC Data Integrity sign (eddsa-rdfc-2022 proofValue)", dir := "VC"
    stage := ``vcSignStage, wireIn := .vcSignIn, wireOut := .text
    contract := ``SignContract, status := .proved
    theorems := [``L4Factoidal.VC.DataIntegrity.createProofValue_of_canonical_eq]
    note := "the proofValue depends on the canonical forms only; the signing primitive is a parameter" },
  { area := "VC Data Integrity verify (eddsa-rdfc-2022)", dir := "VC"
    stage := ``vcVerifyStage, wireIn := .vcVerifyIn, wireOut := .bool
    contract := ``VerifyContract, status := .proved
    theorems := [``L4Factoidal.VC.DataIntegrity.verifyProofValue_of_canonical_eq,
      ``L4Factoidal.VC.DataIntegrity.verifyFromCanonical_not_multibase, ``vcSignVerify_roundTrip,
      ``L4Factoidal.VC.DataIntegrity.verifyFromCanonical_createFromCanonical]
    tests := ["VC/Tests.lean vc-di-eddsa vectors", "l4vc-probe (RFC 8032 and vc-di-eddsa)"]
    note := "sign then verify round trip under Ed25519Correct (vcSignVerify_roundTrip); unforgeability is not stated" },
  { area := "XML parser", dir := "XML"
    wireIn := .text, wireOut := .xml, status := .missing },
  { area := "XPath evaluation", dir := "XPath"
    wireIn := .xml, wireOut := .xdmSequence, params := ["expression"], status := .missing },
  { area := "XPath 4.0 evaluation (XDM 4.0, F&O 4.0 subset)", dir := "XPath4"
    wireIn := .xml, wireOut := .xdmSequence, params := ["expression"], status := .tested
    tests := ["qt4tests b39c4bc0 prod op fn map array math (lake exe l4qt4 --isolate 60): 24152 pass, 4327 fail, 10180 unsupported of 38659"]
    note := "XPath4 is not in the library root; its theorems (XPath4/Theorems.lean: parseXml_eq, parseJsonText_eq, Fn.String sharing, document order) are checked by lake build l4qt4; a proved entry would put XPath4 in the library root (docs/20261028-xpath4-stage2.md)" },
  { area := "XSLT transformation", dir := "XSLT"
    wireIn := .xml, wireOut := .xml, params := ["stylesheet"], status := .missing },
  { area := "XSLT 4.0 transformation", dir := "XSLT4"
    wireIn := .xml, wireOut := .xml, params := ["stylesheet"], status := .tested
    tests := ["xslt40-test 91328fbf non-streaming subset (lake exe l4xslt4 --isolate 30): 6766 pass, 1280 fail, 3053 unsupported of 11099",
      "XSLT 1.0 corpora (l4xslt4 --xslt10): xslt 84 of 88 pass, xslt1-xalan 1455 of 1686 pass"]
    note := "XSLT4 is not in the library root; its theorems and #guards (XSLT4/Theorems.lean: parse_eq_parseXPath, patMatch_type, stripDoc_noRules, the identity transform, agreement with the XSLT 1.0 engine) are checked by lake build l4xslt4 (docs/20261028-xslt4-stage1.md)" },
  { area := "Schematron validation", dir := "Schematron"
    wireIn := .xml, wireOut := .report, params := ["schema"], status := .missing },
  { area := "Ed25519 verify primitive (HACL* call-out)", dir := "Crypto"
    stage := ``ed25519VerifyIO, wireIn := .ed25519Input, wireOut := .bool
    status := .assumed, ioAssumptions := [``Ed25519Correct]
    tests := ["l4vc-probe ed25519-rfc8032"]
    note := "RFC 8032 correctness; HACL* proves it for its F* source, this tree does not" },
  { area := "SHA-256 native primitive (HACL* call-out)", dir := "Crypto"
    stage := ``sha256NativeIO, wireIn := .bytes, wireOut := .bytes
    status := .assumed, ioAssumptions := [``Sha256Agrees]
    note := "equal to the pure Lean Crypto.sha256 (FIPS 180-4 vectors at build time); compared by tests, not proved (https://github.com/danbri/factoidal/issues/777)" },
  { area := "Digest collision resistance (body-less artifact references)", dir := "Crypto"
    wireIn := .digest, wireOut := .graph, status := .missing
    note := "no theorem uses it; a reader who resolves a source reference by its digest relies on it" },
  { area := "Proof checker (FPP0 bundles)", dir := "Proof"
    stage := ``proofCheckStage, wireIn := .bundle, wireOut := .claim
    contract := ``CheckContract, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_merge]
    note := "the axiom set is the bundle's own artifact, not the RDFS profile's (next entry)" },
  { area := "Proof checker with the RDFS profile axiom set (RDFS entailment)", dir := "Proof"
    stage := ``proofCheckRdfsStage, wireIn := .bundle, wireOut := .claim
    contract := ``RdfsCheckContract, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_rdfsEntails, ``L4Factoidal.FPP0.mem_mergeOf_profile,
      ``L4Factoidal.FPP0.axiomaticTriples_scoped]
    note := "profileAxiomsOk compares graph values, so no hash assumption" },
  { area := "SoundReasoner: rho-df (RDFS.closureFix; wasm rhoDfClosure, datasetClosure)", dir := "RDFS"
    stage := ``rhoDfReasoner, wireIn := .graph, wireOut := .graph
    contract := ``Regime.Entails, status := .proved
    theorems := [``L4Factoidal.RDF.closure_rhoDfEntails, ``rhoDfReasoner_complete,
      ``L4Factoidal.RDF.closure_rhoDf_iff]
    note := "SoundReasoner interface type: soundness against RhoDfEntails is a field; conditional completeness is the theorem rhoDfReasoner_complete; the unconditional statement is the named assumption assumed_completeness" },
  { area := "SoundReasoner: RDFS (RDFS.fullClosure with the rdf:_n slice; wasm owlClosure RDFS, datasetClosure)", dir := "RDFS"
    stage := ``rdfsReasoner, wireIn := .graph, wireOut := .graph
    contract := ``Regime.Entails, status := .proved
    theorems := [``L4Factoidal.RDF.fullClosure_entails, ``cmpSlice_member]
    note := "SoundReasoner interface type: soundness against RdfsEntails is a field; the rdf:_n slice is proved to be rdf:_n IRIs; completeness is the named assumption assumed_completeness (open, finding C-1)" },
  { area := "SoundReasoner: OWL 2 RL (set of OWL.RL.closureFix; wasm owlClosure OWL-RL, datasetClosure)", dir := "OWL"
    stage := ``owlRlReasoner, wireIn := .graph, wireOut := .graph
    contract := ``Regime.Entails, status := .proved
    theorems := [``L4Factoidal.OWL.RL.closure_sound, ``L4Factoidal.OWL.RL.rl_derives_holds,
      ``L4Factoidal.RDF.Graph.toSet_sublist]
    note := "SoundReasoner interface type: soundness against OwlRlEntails (Derives, and truth in every interpretation meeting the row conditions) is a field; completeness is the named assumption assumed_completeness (closureFix_saturated, https://github.com/danbri/factoidal/issues/756)" },
  { area := "SPARQL 1.2 RL infer (SPARQLRL.RuleSet.infer; wasm datasetSparqlRlInfer)", dir := "SPARQLRL"
    wireIn := .graph, wireOut := .graph, status := .tested
    tests := ["W3C SPARQL 1.2 RL suite (l4shacl-rules)", "SPARQLRL/Tests.lean #guards"]
    note := "the rule-set semantics of the editor's draft is not proved (https://github.com/danbri/factoidal/issues/1099)" },
  { area := "LawfulValidator: SHACL (decodeShapesGraph, validateFull; wasm shaclValidate, datasetShaclValidate)", dir := "SHACL"
    stage := ``shaclValidator, wireIn := .graph, wireOut := .validationReport, params := ["shapes graph"]
    contract := ``CoreConformance, status := .proved
    theorems := [``L4Factoidal.SHACL.validateWithSparql_sound_core,
      ``shaclValidator_conforms_iff_passes, ``L4Factoidal.SHACL.validateWithSparql_conforms_iff]
    note := "LawfulValidator interface type: a conforming report implies SHACL Core conformance is a field; the report is exact against Core plus the two SHACL-SPARQL passes (theorem); exactness against Spec.GraphConformsWithSparql is the named assumption assumed_spec_iff" },
  { area := "SoundChecker: FPP0 kernel, foundational profile", dir := "Proof"
    stage := ``foundationalChecker, wireIn := .bundle, wireOut := .claim
    contract := ``CheckProfile.Holds, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_merge]
    note := "SoundChecker interface type: accept implies the claim is derivable from the merge is a field; no named assumption" },
  { area := "SoundChecker: FPP0 kernel, RDFS profile", dir := "Proof"
    stage := ``rdfsChecker, wireIn := .bundle, wireOut := .claim
    contract := ``CheckProfile.Holds, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_rdfsEntails, ``rdfsChecker_accept]
    note := "SoundChecker interface type: accept implies RDFS entailment from the merge is a field; no named assumption" },
  { area := "RDFS explanation (selection and target to an FPP0 bundle)", dir := "RDFS"
    stage := ``rdfsExplainStage, wireIn := .dataset, wireOut := .bundle, params := ["target triple"]
    contract := ``ExplainContract, status := .proved
    theorems := [``L4Factoidal.RDFS.fullClosureWithProof_graph, ``explainBundle_G,
      ``explainBundle_sources, ``mergeOf_explain, ``select_eq_flatMap]
    tests := ["Dataflow/PhaseETests.lean (empty input, coherence demonstration, blank nodes)"]
    note := "the run calls the kernel; that every emitted bundle is accepted is tested only" },
  { area := "RDFS explanation, then the proof checker", dir := "Proof"
    stage := ``rdfsExplainCheckStage, wireIn := .dataset, wireOut := .claim, params := ["target triple"]
    contract := ``ExplainCheckContract, status := .proved
    theorems := [``rdfsExplainCheck_sound, ``L4Factoidal.FPP0.checkBundle_merge,
      ``L4Factoidal.FPP0.checkBundle_rdfsEntails, ``rdfsEntails_of_closure]
    note := "one graph artifact G (the union of the selection; one blank-node scope) and body-less source references; no wasm op (https://github.com/danbri/factoidal/issues/615)" },
  { area := "SoundChecker: graph bundle, RDFS profile (a description with shared blank nodes)", dir := "Proof"
    stage := ``rdfsGraphChecker, wireIn := .graphBundle, wireOut := .graphClaim
    contract := ``CheckProfile.Holds, status := .proved
    theorems := [``checkGraphRun_sound, ``rdfsEntails_of_derivable_instance,
      ``rdfsGraphChecker_accept, ``L4Factoidal.RDFS.checkDerivation_sound]
    tests := ["Dataflow/ExplainGraphTests.lean (tampered bundles)"]
    note := "SoundChecker interface type: accept implies the sources RDFS-entail the description (RDF 1.1 Semantics 5.3 interpolation lemma over the RDFS derivations, 9.2); the axiom set is computed by the checker; no named assumption (https://github.com/danbri/factoidal/issues/1002)" },
  { area := "RDFS explanation of a description (sources and a graph to a verdict and a graph bundle)", dir := "RDFS"
    stage := ``rdfsExplainGraphStage, wireIn := .dataset, wireOut := .explainGraphResult, params := ["description"]
    contract := ``ExplainGraphContract, status := .proved
    theorems := [``explainGraphOf_spec, ``checkGraphRun_sound, ``findInstance_none,
      ``unmatchedIn_no_instance, ``L4Factoidal.RDFS.fullClosureWithProof_graph]
    tests := ["Dataflow/ExplainGraphTests.lean (entailed description with a shared blank node, noMatch, noJointMapping)"]
    note := "entailed: the graph checker accepts the returned bundle and RdfsEntails holds (proved); not entailed: no instance of the description in the closure (proved), not RDFS-entailed only under closure completeness (named in the result's assumptions); that every emitted bundle is accepted is tested only; wasm explainGraph (https://github.com/danbri/factoidal/issues/1002)" }
]

end L4Factoidal.Dataflow
