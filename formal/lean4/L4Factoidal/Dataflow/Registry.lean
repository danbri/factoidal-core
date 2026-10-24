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

* `proved`: `stage` is a `Stage` value whose `sound` field is a proof;
  `contract` names its contract; `theorems` names the component theorems it
  uses.
* `assumed`: `stage` is an `IOStage`; `ioAssumptions` names the assumption.
* `tested`: no Lean contract; `tests` names the test suite that checks the
  behaviour against the W3C test files (scores in `skills/test-suites`).
* `missing`: no Lean stage contract and no suite named here. `theorems` may
  list component theorems that a future stage can use.

`dir` is the directory under `formal/lean4/L4Factoidal/` of the area. The
report lists the directories that no entry names.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Instances
import L4Factoidal.Dataflow.PhaseD
import L4Factoidal.Dataflow.PhaseE
import L4Factoidal.Dataflow.PhaseC
import L4Factoidal.Unified.OwlRlAdequacy
import L4Factoidal.Storage.BlockDenotation
import L4Factoidal.SPARQL.FromMergeStage
import L4Factoidal.Storage.StoreDictTheorems
import L4Factoidal.HDT.DictionaryTheorems
import L4Factoidal.Cottas.DictTheorems

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
  wireIn : String
  wireOut : String
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
  | stage | ioStage | none | other
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
    else if k != .stage then some s!"proved: {e.stage} is not a Stage"
    else Option.none
  | .assumed =>
    if e.ioAssumptions.isEmpty then some "assumed needs a named IO assumption"
    else if k != .ioStage then some s!"assumed: {e.stage} is not an IOStage"
    else Option.none
  | .tested =>
    if e.tests.isEmpty || !isNone e.stage || !isNone e.contract then
      some "tested needs a suite, no stage and no contract"
    else Option.none
  | .missing =>
    if !isNone e.stage || !isNone e.contract || !e.tests.isEmpty || !e.ioAssumptions.isEmpty then
      some "missing has no stage, no contract, no suite and no IO assumption"
    else Option.none

/-- The registry. Order: boundary, syntax, stores, query, reasoning,
validation, evidence. -/
def registry : List Entry := [
  { area := "Document decode (UTF-8, media type)", dir := "RDF"
    stage := ``decodeStage, wireIn := "Document", wireOut := "RdfFormat × String"
    contract := ``DecodeContract, status := .proved
    theorems := [``fromUTF8?_toUTF8, ``decodeParse_mediaType,
      ``L4Factoidal.RDF.formatOfDocument_of_mediaType, ``L4Factoidal.RDF.formatOfDocument_absent,
      ``L4Factoidal.RDF.formatOfMediaType_params]
    note := "six registered media types (RDF/MediaType.lean); the extension only when the media type is absent; text/n3 has no reader" },
  { area := "RDF readers: N-Triples, Turtle, N-Quads, TriG, RDF/XML, JSON-LD (set contract)"
    dir := "RDF"
    stage := ``parseStage, wireIn := "RdfFormat × String", wireOut := "Dataset"
    contract := ``ParseContract, status := .proved
    theorems := [``L4Factoidal.RDF.Source.parseDocument_set, ``L4Factoidal.RDF.Dataset.memQuad_toSet,
      ``L4Factoidal.RDF.Dataset.toSet_isSet, ``SetOf.den_eq]
    note := "labels as written; the document scope is scopedParseStage" },
  { area := "Document blank-node scope (fresh labels per document)", dir := "RDF"
    stage := ``scopeStage, wireIn := "Dataset", wireOut := "Dataset"
    contract := ``ScopeContract, status := .proved
    theorems := [``L4Factoidal.RDF.Dataset.den_iso_scopeDocument,
      ``L4Factoidal.RDF.Dataset.scopeDocument_inScope, ``L4Factoidal.RDF.Dataset.scopeDocument_isSet,
      ``L4Factoidal.RDF.docLabel_inj]
    note := "scope number from a fresh-label supply (Wasm counter, harness file index); the supply is IO, not modelled" },
  { area := "RDF readers with the document scope; two documents combine to a merge", dir := "RDF"
    stage := ``scopedParseStage, wireIn := "RdfFormat × String", wireOut := "Dataset"
    contract := ``ScopedParseContract, status := .proved
    theorems := [``scopedParseContract_of, ``scopedParse_combine_isMerge,
      ``L4Factoidal.RDF.scopeDocument_combine_isMerge, ``L4Factoidal.RDF.Dataset.den_combine]
    note := "RDF 1.1 Semantics 5.2 merge (DatasetDen.IsMerge), not the union" },
  { area := "Blank-node relabelling at a store boundary (identity transport)", dir := "RDF"
    stage := ``relabelStage, wireIn := "Dataset", wireOut := "Dataset"
    contract := ``RelabelContract, status := .proved
    theorems := [``L4Factoidal.RDF.Dataset.den_iso_renameBnodes,
      ``L4Factoidal.RDF.Dataset.den_renameBnodes, ``L4Factoidal.RDF.Dataset.renameBnodes_isSet,
      ``L4Factoidal.RDF.Dataset.renameBnodes_invertible, ``L4Factoidal.RDF.DatasetDen.iso_equivalence]
    note := "DatasetDen.Iso: one relabelling over graphs, graph names and triple terms" },
  { area := "W3C harness fixture loading (data and graph files as separate documents)", dir := "RDF"
    wireIn := "files", wireOut := "Dataset", status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all (l4w3c)", "Harness/HarnessTests.lean fixture-scope #guards"]
    note := "each file scoped by its index (addDataFile, addGraphFile)" },
  { area := "Reader: N-Triples (batch)", dir := "Syntax"
    stage := ``ntriplesReader, wireIn := "String", wireOut := "Dataset"
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error; RDF 1.2 mode reads triple terms" },
  { area := "Reader: N-Quads (batch)", dir := "Syntax"
    stage := ``nquadsReader, wireIn := "String", wireOut := "Dataset"
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error" },
  { area := "Reader: Turtle (batch)", dir := "Syntax"
    stage := ``turtleReader, wireIn := "String", wireOut := "Dataset"
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error" },
  { area := "Reader: TriG (batch)", dir := "Syntax"
    stage := ``trigReader, wireIn := "String", wireOut := "Dataset"
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error; empty named graphs kept" },
  { area := "Reader: RDF/XML (batch)", dir := "Syntax"
    stage := ``rdfxmlReader, wireIn := "String", wireOut := "Dataset"
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error" },
  { area := "Reader: JSON-LD to RDF (batch)", dir := "Syntax"
    stage := ``jsonldReader, wireIn := "String", wireOut := "Dataset"
    contract := ``ReaderContract, status := .proved
    theorems := [``readerStage_error, ``readerStage_error_of_raw, ``readerStage_ok_of_raw, ``readerStage_eq_scoped, ``eraseLabels_scopeDocument, ``L4Factoidal.RDF.Source.parseDocument_set]
    note := "set, document scope n, den = raw den, Iso, labels-only change; error iff parser error; Source.withJsonLd" },
  { area := "Reader: RDF/JSON (W3C Note, triples only)", dir := "Syntax"
    stage := ``rdfJsonReader, wireIn := "String", wireOut := "Dataset"
    contract := ``RdfJsonContract, status := .proved
    theorems := [``L4Factoidal.RDF.Dataset.den_toSet, ``L4Factoidal.RDF.Dataset.den_iso_scopeDocument,
      ``L4Factoidal.RDF.Dataset.den_renameBnodes]
    note := "default graph only; no W3C suite; used by RML targets" },
  { area := "Reader grammar: N-Triples", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C RDF 1.1 rdf-n-triples (l4w3c)", "W3C RDF 1.2 rdf-n-triples (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: N-Quads", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C RDF 1.1 rdf-n-quads (l4w3c)", "W3C RDF 1.2 rdf-n-quads (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: Turtle", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C RDF 1.1 rdf-turtle (l4w3c)", "W3C RDF 1.2 rdf-turtle (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: TriG", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C RDF 1.1 rdf-trig (l4w3c)", "W3C RDF 1.2 rdf-trig (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: RDF/XML", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C RDF 1.1 rdf-xml (l4w3c)", "W3C RDF 1.2 rdf-xml (l4w3c)"]
    note := "grammar conformance is not proved" },
  { area := "Reader grammar: JSON-LD to RDF", dir := "JSONLD"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C JSON-LD 1.1 toRdf (l4jsonld-probe)"]
    note := "grammar and algorithm conformance are not proved" },
  { area := "Reader grammar: RDF/JSON", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["Syntax/RdfJson.lean #guards", "Dataflow/PhaseCTests.lean"]
    note := "no W3C suite exists" },
  { area := "Streamed N-Triples and Turtle output as a set (dedup consumer)", dir := "RDF"
    stage := ``streamSetStage, wireIn := "triples per chunk", wireOut := "Graph"
    contract := ``StreamSetContract, status := .proved
    theorems := [``L4Factoidal.RDF.runChunks_eq_toSet, ``L4Factoidal.RDF.runChunks_keyNodup,
      ``L4Factoidal.RDF.runChunks_written]
    note := "the consumer half; the reader half (chunks = batch parse) is the next entry" },
  { area := "Streamed N-Triples and Turtle reader: chunk cut equals batch parse", dir := "Syntax"
    wireIn := "chunks", wireOut := "triples", status := .tested
    theorems := [``L4Factoidal.RDF.Source.turtleStep_collect]
    tests := ["RDF/Source.lean #guards (every cut position)", "tests/known-defects/run.sh rows SF-1, SF-2, SF-4"]
    note := "not proved: https://github.com/danbri/factoidal/issues/826" },
  { area := "Streamed N-Quads reader, RDF 1.1 (chunks to the batch dataset)", dir := "RDF"
    stage := ``nquads11StreamStage, wireIn := "chunks", wireOut := "Dataset"
    contract := ``NQuadsStreamContract, status := .proved
    theorems := [``L4Factoidal.RDF.Source.nquads11_readAll_eq_parseNQuadsFast, ``nquads11Stream_reader]
    note := "streamed then scoped = nquadsReader on the joined text" },
  { area := "Streamed N-Quads reader, RDF 1.2", dir := "Syntax"
    wireIn := "chunks", wireOut := "Dataset", status := .tested
    tests := ["tests/known-defects/run.sh row SF-3"]
    note := "not proved: https://github.com/danbri/factoidal/issues/826" },
  { area := "Streamed TriG reader (chunk fold)", dir := "Syntax"
    wireIn := "chunks", wireOut := "quads", status := .tested
    tests := ["tests/trig-pack/order_xfail.sh", "tests/trig-pack/compare_w3c.sh"]
    note := "chunk fold vs parseTriG not proved; source order differs for a default block after a named block: https://github.com/danbri/factoidal/issues/836" },
  { area := "Streamed RDF/XML reader (item by item)", dir := "Syntax"
    wireIn := "chunks", wireOut := "quads", status := .tested
    theorems := [``L4Factoidal.RDF.Source.rdfxml_readAll_of_notStreamed]
    tests := ["tests/known-defects/run.sh row RX-1", "l4rdfxml-chunk-diff"]
    note := "fall-back mode proved (rdfxml_readAll_of_notStreamed); item mode measured: https://github.com/danbri/factoidal/issues/936" },
  { area := "Streamed JSON-LD reader (top-level node objects)", dir := "JSONLD"
    wireIn := "chunks", wireOut := "quads", status := .tested
    theorems := [``L4Factoidal.RDF.Source.jsonld_readAll_of_notStreamed, ``L4Factoidal.RDF.Source.jsonld_readAll]
    tests := ["tests/known-defects/run.sh row JS-1", "l4jsonld-chunk-diff"]
    note := "whole-reader mode proved (jsonld_readAll_of_notStreamed); item mode measured: https://github.com/danbri/factoidal/issues/946" },
  { area := "Writer: N-Triples (round trip on the projection)", dir := "Syntax"
    stage := ``ntriplesWriter, wireIn := "Dataset", wireOut := "String"
    contract := ``WriterContract, status := .proved
    theorems := [``writerContract_nt, ``writerRoundTrip_nt, ``writerProjection_triples_den, ``L4Factoidal.Syntax.NTriplesRoundTrip.parseNTriples_toNTriples, ``L4Factoidal.Syntax.NTriplesRoundTrip.readTriple11_line, ``L4Factoidal.Syntax.NTriplesRoundTrip.readTriple12_line, ``L4Factoidal.Syntax.NTriplesRoundTrip.readStringLiteralBody_escape, ``L4Factoidal.Syntax.NTriplesRoundTrip.readObject12_safe]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/NTriplesDocRoundTrip.lean counter-example #guards"]
    note := "RDF 1.1 and 1.2 modes; projection: union of all graphs, no graph name (writerProjection_triples_den); domain: IRIREF, BLANK_NODE_LABEL and LANGTAG lexical spaces (Triple.ntSafe; the IRI-only domain was false)" },
  { area := "Writer: N-Quads (round trip on the projection)", dir := "Syntax"
    stage := ``nquadsWriter, wireIn := "Dataset", wireOut := "String"
    contract := ``WriterContract, status := .proved
    theorems := [``writerContract_nquads, ``writerRoundTrip_nquads, ``writerProjection_nquads_den, ``L4Factoidal.Syntax.NQuadsRoundTrip.parseNQuads_toNQuads, ``L4Factoidal.Syntax.NQuadsRoundTrip.toNQuads_lines, ``L4Factoidal.Syntax.NQuadsRoundTrip.addAll_quadsOf_memQuad, ``L4Factoidal.Syntax.NQuadsRoundTrip.addAll_quadsOf_names, ``L4Factoidal.Syntax.parseNQuadsFast_eq_parseNQuads]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/NQuadsDocRoundTrip.lean counter-example #guards"]
    note := "RDF 1.1 and 1.2 modes; projection: empty named graphs dropped (writerProjection_nquads_den); domain: Quad.ntSafe (the N-Triples domain and graphLabel); the empty domain restriction was false" },
  { area := "Writer: Turtle (round trip on the projection)", dir := "Syntax"
    wireIn := "Dataset", wireOut := "String", status := .tested
    theorems := [``writerProjection_triples_den]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)"]
    note := "projection: union of all graphs (writerProjection_triples_den); WriterRoundTrip stated, not proved" },
  { area := "Writer: TriG (round trip, whole dataset)", dir := "Syntax"
    wireIn := "Dataset", wireOut := "String", status := .tested
    theorems := [``writerProjection_dataset]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)"]
    note := "no projection: empty named graphs and blank-node graph names kept (writerProjection_dataset); WriterRoundTrip stated, not proved" },
  { area := "Writer: RDF/XML (round trip on the projection)", dir := "Syntax"
    wireIn := "Dataset", wireOut := "String", status := .tested
    theorems := [``writerProjection_triples_den]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/RdfXmlWrite.lean #guards"]
    note := "projection: union of all graphs; domain: no triple term (refused with an error); finding fixed in phase C: base direction was dropped" },
  { area := "Writer: JSON-LD fromRdf (round trip, whole dataset)", dir := "JSONLD"
    wireIn := "Dataset", wireOut := "String", status := .tested
    theorems := [``writerProjection_dataset]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "W3C JSON-LD 1.1 fromRdf (l4jsonld-api)"]
    note := "domain: no triple term (refused), no directional language string (finding: direction dropped with no error, https://github.com/danbri/factoidal/issues/984)" },
  { area := "Writer: RDF/JSON (round trip, triples only)", dir := "Syntax"
    wireIn := "Graph", wireOut := "String", status := .tested
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2)", "Syntax/RdfJson.lean #guards"]
    note := "the union of the graphs; no graph name; triple terms refused" },
  { area := "Stream writers (Sink.Writer, all syntaxes)", dir := "RDF"
    wireIn := "quads", wireOut := "String", status := .tested
    theorems := [``L4Factoidal.RDF.Sink.runList_rdfxml_eq, ``L4Factoidal.RDF.Sink.runList_jsonld_eq]
    tests := ["Dataflow/PhaseCTests.lean round trip #guards (30 seeded datasets, RDF 1.1 and 1.2) via streamDataset", "tests/sbm11/export_roundtrip.sh"]
    note := "RDF/XML stream = whole writer for contiguous subjects (runList_rdfxml_eq); JSON-LD elements in order (runList_jsonld_eq); the rest tested" },
  { area := "JSON-LD expansion, compaction, framing", dir := "JSONLD"
    wireIn := "JSON", wireOut := "JSON / Dataset", status := .missing },
  { area := "SBM11 pack (dataset to generation and files)", dir := "Storage"
    stage := ``sbm11PackStage, wireIn := "Dataset", wireOut := "MemGen × FileGen"
    contract := ``PackContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.PackSpec.den_packSpec,
      ``L4Factoidal.Storage.Sbm11.PackSpec.packSpec_written,
      ``L4Factoidal.Storage.Sbm11.PackSpec.packSpec_check,
      ``L4Factoidal.Storage.Sbm11.PackSpec.datasetOf_of_den,
      ``L4Factoidal.Storage.Sbm11.AllowedPerm.allowed_perm, ``packContract_of]
    note := "answer transfer needs Sbm11Folded (finding 3)" },
  { area := "SBM11 disk (write files, positioned reads)", dir := "Storage"
    stage := ``sbm11Disk, wireIn := "FileGen", wireOut := "FileGen", status := .assumed
    ioAssumptions := [``ReadsWritten]
    note := "Session caches not covered" },
  { area := "SBM11 WHERE over the files", dir := "Storage"
    stage := ``sbm11WhereStage, wireIn := "MemGen × FileGen", wireOut := "id table (WhereOut)"
    contract := ``WhereContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.MemGen.harness_where_allowed_file,
      ``L4Factoidal.Storage.Sbm11.MemGen.store_written]
    note := "the output store decodes the table (sbm11DecodeStage)" },
  { area := "SBM11 id table to solution sequence", dir := "Storage"
    stage := ``sbm11DecodeStage, wireIn := "id table (WhereOut)", wireOut := "SolutionSeq"
    contract := ``DecodeRowsContract, status := .proved
    theorems := [``L4Factoidal.Storage.Sbm11.SubSelect.decodeRowsM_run]
    note := "decodeRowsM, the decoder of the shipped nested path" },
  { area := "End to end: document bytes to SBM11 WHERE answer", dir := "Dataflow"
    stage := ``documentToWhere, wireIn := "Document", wireOut := "id table (WhereOut)"
    contract := ``documentToWhere_sound, status := .proved
    theorems := [``documentToWhere_sound, ``Stage.comp_ok_contract]
    ioAssumptions := [``ReadsWritten]
    note := "document scope n; raw parse to generation is DatasetDen.Iso; premises: ReadsWritten, plan hypotheses, QHyps, Sbm11Folded, PermOk" },
  { area := "End to end: document bytes to SolutionSeq (SBM11 id path)", dir := "Dataflow"
    stage := ``documentToSolutions, wireIn := "Document", wireOut := "SolutionSeq"
    contract := ``documentToSolutions_sound, status := .proved
    theorems := [``documentToSolutions_sound, ``documentToWhere_sound,
      ``L4Factoidal.Storage.Sbm11.LocalVocab.termOf_withLocal,
      ``L4Factoidal.Storage.Sbm11.MemGen.store_written,
      ``L4Factoidal.Storage.Sbm11.MemGen.mem_htermOf]
    ioAssumptions := [``ReadsWritten]
    note := "decoded solutions = the sequence WhereOk allows, with multiplicity; premises as above" },
  { area := "SBM11 session and its caches", dir := "Storage"
    wireIn := "files", wireOut := "id table", status := .tested
    tests := ["SBM11 gate (tests/sbm11/run.sh)"] },
  { area := "SBM11 delta overlay (INSERT, DELETE, CREATE)", dir := "Storage"
    wireIn := "update log", wireOut := "Dataset", status := .missing
    theorems := [``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_add,
      ``L4Factoidal.Storage.Sbm11.Overlay.overlayDen_remove,
      ``L4Factoidal.Storage.Sbm11.OverlayDict.overlay_dictInjective]
    note := "denotation theorems exist; no stage; HeldFolded open" },
  { area := "Block stores (BlockMvp, IndexedBlock, IBK4, IBK5)", dir := "Storage"
    wireIn := "Dataset", wireOut := "bytes", status := .missing
    theorems := [``L4Factoidal.Storage.IndexedBlock.Block.den_eq_ofRows,
      ``L4Factoidal.Storage.IndexedBlockWireV4.den_decode_encode?,
      ``L4Factoidal.Storage.IndexedBlock.fromParts?_foldedDictInjective,
      ``L4Factoidal.Storage.StoreDictTheorems.v4_fromParts?_foldedDictInjective,
      ``L4Factoidal.Storage.StoreDictTheorems.v5_fromParts?_foldedDictInjective]
    note := "one id per RDF term: tags folded at pack and at read (issue 977)" },
  { area := "Store interface StoreCaps (planner)", dir := "SPARQL"
    wireIn := "PatternBound", wireOut := "List Triple", status := .missing
    note := "no denotation (phase B1)" },
  { area := "COTTAS store", dir := "Cottas"
    wireIn := "Dataset", wireOut := "bytes", status := .missing
    theorems := [``L4Factoidal.Cottas.cotd_dictInjective]
    note := ".dict term layer: one id per RDF term when termRoundTripsAll holds (issue 977)" },
  { area := "HDT store", dir := "HDT"
    wireIn := "Dataset", wireOut := "bytes", status := .missing
    theorems := [``L4Factoidal.HDT.hdt_dictInjective]
    note := "tags folded at read; one id per RDF term when roundTripsAll holds (issue 977)" },
  { area := "Planner SELECT over the kept entries", dir := "Storage"
    stage := ``plannerSelectStage, wireIn := "Dataset", wireOut := "SolutionSeq"
    contract := ``PlannerSelectContract, status := .proved
    theorems := [``L4Factoidal.Storage.PlannerSoundness.plannerSoundnessSelect]
    note := "on the shipped path as the reference fallback of l4sbm11 query (finding 6)" },
  { area := "SBM11 reference-fallback read (selectedDataset)", dir := "Storage"
    stage := ``sbm11SelectedRead, wireIn := "MemGen × FileGen", wireOut := "Dataset", status := .assumed
    ioAssumptions := [``SelectedAgrees]
    note := "IO over Session, no Lean model; keeps named graphs the selection empties" },
  { area := "SBM11 generation to planner SELECT (reference fallback)", dir := "Dataflow"
    stage := ``sbm11PlannerSelect, wireIn := "MemGen × FileGen", wireOut := "SolutionSeq"
    contract := ``sbm11PlannerSelect_sound, status := .proved
    theorems := [``sbm11PlannerSelect_sound,
      ``L4Factoidal.Storage.PlannerSoundness.plannerSoundnessSelect]
    ioAssumptions := [``SelectedAgrees]
    note := "answer = planner answer over G.denote; needs non-empty named graphs" },
  { area := "Reference fallback answer vs id path answer and parsed dataset", dir := "SPARQL"
    wireIn := "Query × MemGen", wireOut := "SolutionSeq", status := .missing
    note := "no theorem relates runSelectQueryBackendDataset over G.denote to WhereOk or to the dataset parsed; pure model of selectedDataset missing (finding 6)" },
  { area := "SPARQL query evaluation (reference evaluator)", dir := "SPARQL"
    wireIn := "Query × Dataset", wireOut := "QueryResult", status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all (l4w3c)", "W3C SPARQL 1.2 (l4w3c)"] },
  { area := "SPARQL FROM default graph (RDF merge of the FROM graphs)", dir := "SPARQL"
    stage := ``L4Factoidal.SPARQL.FromMerge.fromMergeStage, wireIn := "List Graph", wireOut := "Graph"
    contract := ``L4Factoidal.SPARQL.FromMerge.FromMergeContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.FromMerge.fromMerge_isMergeOf,
      ``L4Factoidal.SPARQL.FromMerge.applyDataset_default_isMergeOf,
      ``L4Factoidal.SPARQL.FromMerge.isMergeOf_pair]
    note := "SPARQL 1.1 section 13.2.1; two or more graphs relabelled by docLabel; one graph kept as it is (issue 979)" },
  { area := "SPARQL Update request on the dataset denotation", dir := "SPARQL"
    stage := ``updateStage, wireIn := "Dataset × Update", wireOut := "Dataset"
    contract := ``UpdateContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.applyUpdateIn_den, ``L4Factoidal.SPARQL.applyOp_den,
      ``L4Factoidal.RDF.applyUpdateIn_isSet, ``L4Factoidal.RDF.Dataset.den_insertQuads,
      ``L4Factoidal.RDF.Dataset.den_deleteQuads, ``L4Factoidal.RDF.Dataset.den_setGraph,
      ``L4Factoidal.RDF.Dataset.den_dropGraph, ``L4Factoidal.RDF.Dataset.den_ensureGraph,
      ``L4Factoidal.RDF.Dataset.den_clearAllNamed]
    note := "OpDen per operation: CLEAR keeps graph names, DROP removes them, CREATE adds a name with no triple; delete before insert; the result is a new value; needs IsSet" },
  { area := "SPARQL Update WHERE evaluation and template instantiation", dir := "SPARQL"
    wireIn := "Dataset × QueryPattern", wireOut := "List Quad", status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all, update entries (l4w3c)"]
    note := "OpDen takes the quad lists of evalWhere and instQuads as inputs" },
  { area := "SPARQL protocol and graph store", dir := "SPARQL"
    wireIn := "HTTP request", wireOut := "HTTP response", status := .missing },
  { area := "SPARQL results formats (XML, JSON, CSV, TSV)", dir := "SPARQL"
    wireIn := "QueryResult", wireOut := "String", status := .missing },
  { area := "Graph selection (dataset to the union of selected graphs)", dir := "Dataflow"
    stage := ``selectStage, wireIn := "Dataset", wireOut := "Graph"
    contract := ``SelectContract, status := .proved
    theorems := [``mem_select]
    note := "default graph and named graphs as a stage parameter; union, one blank-node scope (RDF 1.1 Concepts section 4)" },
  { area := "RDFS closure (soundness)", dir := "RDFS"
    stage := ``rdfsClosureStage, wireIn := "Graph", wireOut := "Graph"
    contract := ``L4Factoidal.RDF.RdfsEntails, status := .proved
    theorems := [``L4Factoidal.RDF.fullClosure_entails] },
  { area := "RDFS closure over a graph selection (soundness)", dir := "Dataflow"
    stage := ``rdfsSelectStage, wireIn := "Dataset", wireOut := "Graph"
    contract := ``rdfsSelect_sound, status := .proved
    theorems := [``rdfsSelect_sound, ``L4Factoidal.RDF.fullClosure_entails, ``mem_select]
    note := "finding 5 closed: the reasoner reads the selected graphs of a dataset" },
  { area := "RDFS entailment completeness, negative tests", dir := "RDFS"
    wireIn := "Graph", wireOut := "Bool", status := .missing
    theorems := [``L4Factoidal.RDF.rdfsEntails_subclassSelfLoop_iri]
    note := "false without the axiomatic triples (finding C-1); negative rdf-mt tests are evidence without proof" },
  { area := "ρdf closure (soundness; completeness when closed and in the fragment)", dir := "RDFS"
    stage := ``rhoDfClosureStage, wireIn := "Graph", wireOut := "Graph"
    contract := ``RhoDfContract, status := .proved
    theorems := [``L4Factoidal.RDF.closure_rhoDfEntails, ``L4Factoidal.RDF.closure_rhoDf_iff]
    note := "dataset form: rhoDfSelectStage" },
  { area := "Simple entailment over a graph selection (sound and complete)", dir := "RDF"
    stage := ``simpleEntailsSelectStage, wireIn := "Dataset × Graph", wireOut := "Bool"
    contract := ``SimpleContract, status := .proved
    theorems := [``L4Factoidal.RDF.SimpleRefinement.simpleEntails_iff_spec,
      ``L4Factoidal.RDF.simpleEntails_iff_mt]
    note := "model-theoretic form for graphs without triple terms" },
  { area := "OWL 2 RL closure (soundness)", dir := "OWL"
    stage := ``owlRlClosureStage, wireIn := "Graph", wireOut := "Graph"
    contract := ``RlContract, status := .proved
    theorems := [``L4Factoidal.OWL.RL.closure_sound, ``L4Factoidal.OWL.RL.rl_derives_holds]
    note := "dataset form: owlRlSelectStage" },
  { area := "OWL 2 RL completeness", dir := "OWL"
    wireIn := "Graph", wireOut := "Graph", status := .missing
    theorems := [``L4Factoidal.Unified.owlRl_complete_ground]
    note := "ground completeness needs a Derives-closed closure: open obligation closureFix_saturated (https://github.com/danbri/factoidal/issues/756)" },
  { area := "RIF closure (extensivity)", dir := "RIF"
    stage := ``rifClosureStage, wireIn := "Facts × rules", wireOut := "Facts"
    contract := ``RifContract, status := .proved
    theorems := [``L4Factoidal.RIF.closure_extensive]
    note := "dataset form: rifSelectStage" },
  { area := "RIF soundness and the RDF to RIF mapping", dir := "RIF"
    wireIn := "Graph × rules", wireOut := "Facts", status := .missing
    theorems := [``L4Factoidal.RIF.step_licensed]
    note := "per-round licensing is provenance, not truth; no RIF-BLD model theory; factsOfTriple has no contract" },
  { area := "SHACL validation (a conforming report implies Core conformance)", dir := "SHACL"
    stage := ``shaclStage, wireIn := "Graph × Graph", wireOut := "ValidationReport"
    contract := ``ShaclContract, status := .proved
    theorems := [``L4Factoidal.SHACL.validateWithSparql_sound_core,
      ``L4Factoidal.SHACL.validate_conforms_iff]
    note := "the l4shacl path: decodeShapesGraph, then validateFull; dataset form: shaclSelectStage" },
  { area := "SHACL validation, W3C suite", dir := "SHACL"
    wireIn := "Graph × shapes", wireOut := "ValidationReport", status := .tested
    tests := ["W3C SHACL Core (l4shacl)"]
    note := "the report's results list and the shapes-graph decoding (decodeShapesGraph) have no proved contract" },
  { area := "SPARQL basic graph pattern (soundness)", dir := "SPARQL"
    stage := ``bgpSelectStage, wireIn := "Graph", wireOut := "SolutionSeq"
    contract := ``BgpContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.evalBgp_instantiates_into_graph] },
  { area := "SPARQL ASK of a basic graph pattern (true implies a match)", dir := "SPARQL"
    stage := ``bgpAskStage, wireIn := "Graph", wireOut := "Bool"
    contract := ``AskContract, status := .proved
    theorems := [``L4Factoidal.SPARQL.evalBgp_instantiates_into_graph]
    note := "false is not proved to mean no match" },
  { area := "SPARQL basic graph pattern completeness", dir := "SPARQL"
    wireIn := "Graph", wireOut := "SolutionSeq", status := .missing
    theorems := [``L4Factoidal.SPARQL.rdfsRegime_bgp_complete_conditional]
    note := "the named gap EvalBgpCompleteAt is a hypothesis, not proved" },
  { area := "End to end: document to RDFS closure of a selection to BGP answer", dir := "Dataflow"
    stage := ``documentToRdfsBgp, wireIn := "Document", wireOut := "SolutionSeq"
    contract := ``documentToRdfsBgp_sound, status := .proved
    theorems := [``documentToRdfsBgp_sound, ``rdfsEntails_of_mem, ``mem_select,
      ``L4Factoidal.RDF.fullClosure_entails, ``L4Factoidal.SPARQL.evalBgp_instantiates_into_graph]
    note := "premise hcmps; exactness for the entailment clause; tested only: parser grammar, query text to Bgp, algebra beyond a BGP" },
  { area := "ShEx validation", dir := "ShEx"
    wireIn := "Graph × schema", wireOut := "report", status := .missing },
  { area := "CSVW (tabular data to RDF)", dir := "CSVW"
    wireIn := "CSV × metadata", wireOut := "Dataset", status := .missing },
  { area := "RDFC-1.0 canonicalization (canonical N-Quads and SHA-256 hex)", dir := "RDF"
    stage := ``rdfcStage, wireIn := "Dataset", wireOut := "String × String"
    contract := ``RdfcContract, status := .proved
    theorems := [``L4Factoidal.RDF.Canonical.canonicalLines_sorted, ``canonicalNQuads_join,
      ``L4Factoidal.RDF.Canonical.mkLabel_inj]
    note := "lines in code point order; fails on the section 4.4 work budget; relabelling invariance is the next entry" },
  { area := "RDFC-1.0 relabelling invariance (isomorphic input, same canonical form)", dir := "RDF"
    wireIn := "Dataset", wireOut := "String", status := .tested
    theorems := [``L4Factoidal.RDF.Canonical.hashFirstDegreeQuads_rename]
    tests := ["W3C RDFC-1.0 suite (l4rdfc-probe)", "Dataflow/PhaseETests.lean relabelling #guard"]
    note := "stated only (Canonical.RelabellingInvariance); the first-degree hash is proved invariant" },
  { area := "VC Data Integrity sign (eddsa-rdfc-2022 proofValue)", dir := "VC"
    stage := ``vcSignStage, wireIn := "SignIn (key, document, proof config)", wireOut := "String"
    contract := ``SignContract, status := .proved
    theorems := [``L4Factoidal.VC.DataIntegrity.createProofValue_of_canonical_eq]
    note := "the proofValue depends on the canonical forms only; the signing primitive is a parameter" },
  { area := "VC Data Integrity verify (eddsa-rdfc-2022)", dir := "VC"
    stage := ``vcVerifyStage, wireIn := "VerifyIn (key, document, proof config, proofValue)", wireOut := "Bool"
    contract := ``VerifyContract, status := .proved
    theorems := [``L4Factoidal.VC.DataIntegrity.verifyProofValue_of_canonical_eq,
      ``L4Factoidal.VC.DataIntegrity.verifyFromCanonical_not_multibase, ``vcSignVerify_roundTrip,
      ``L4Factoidal.VC.DataIntegrity.verifyFromCanonical_createFromCanonical]
    tests := ["VC/Tests.lean vc-di-eddsa vectors", "l4vc-probe (RFC 8032 and vc-di-eddsa)"]
    note := "sign then verify round trip under Ed25519Correct (vcSignVerify_roundTrip); unforgeability is not stated" },
  { area := "XML parser", dir := "XML"
    wireIn := "String", wireOut := "XML document", status := .missing },
  { area := "XPath evaluation", dir := "XPath"
    wireIn := "XML document × expression", wireOut := "sequence", status := .missing },
  { area := "XSLT transformation", dir := "XSLT"
    wireIn := "XML document × stylesheet", wireOut := "XML document", status := .missing },
  { area := "Schematron validation", dir := "Schematron"
    wireIn := "XML document × schema", wireOut := "report", status := .missing },
  { area := "Ed25519 verify primitive (HACL* call-out)", dir := "Crypto"
    stage := ``ed25519VerifyIO, wireIn := "pk × message × signature", wireOut := "Bool"
    status := .assumed, ioAssumptions := [``Ed25519Correct]
    tests := ["l4vc-probe ed25519-rfc8032"]
    note := "RFC 8032 correctness; HACL* proves it for its F* source, this tree does not" },
  { area := "SHA-256 native primitive (HACL* call-out)", dir := "Crypto"
    stage := ``sha256NativeIO, wireIn := "bytes", wireOut := "bytes"
    status := .assumed, ioAssumptions := [``Sha256Agrees]
    note := "equal to the pure Lean Crypto.sha256 (FIPS 180-4 vectors at build time); compared by tests, not proved (https://github.com/danbri/factoidal/issues/777)" },
  { area := "Digest collision resistance (body-less artifact references)", dir := "Crypto"
    wireIn := "digest", wireOut := "Graph", status := .missing
    note := "no theorem uses it; a reader who resolves a source reference by its digest relies on it" },
  { area := "Proof checker (FPP0 bundles)", dir := "Proof"
    stage := ``proofCheckStage, wireIn := "Bundle", wireOut := "Claim"
    contract := ``CheckContract, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_merge]
    note := "the axiom set is the bundle's own artifact, not the RDFS profile's (next entry)" },
  { area := "Proof checker with the RDFS profile axiom set (RDFS entailment)", dir := "Proof"
    stage := ``proofCheckRdfsStage, wireIn := "Bundle", wireOut := "Claim"
    contract := ``RdfsCheckContract, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_rdfsEntails, ``L4Factoidal.FPP0.mem_mergeOf_profile,
      ``L4Factoidal.FPP0.axiomaticTriples_scoped]
    note := "profileAxiomsOk compares graph values, so no hash assumption" },
  { area := "RDFS explanation (selection and target to an FPP0 bundle)", dir := "RDFS"
    stage := ``rdfsExplainStage, wireIn := "Dataset × Triple", wireOut := "Bundle"
    contract := ``ExplainContract, status := .proved
    theorems := [``L4Factoidal.RDFS.fullClosureWithProof_graph, ``explainBundle_G,
      ``explainBundle_sources, ``mergeOf_explain, ``select_eq_flatMap]
    tests := ["Dataflow/PhaseETests.lean (empty input, coherence demonstration, blank nodes)"]
    note := "the run calls the kernel; that every emitted bundle is accepted is tested only" },
  { area := "RDFS explanation, then the proof checker", dir := "Proof"
    stage := ``rdfsExplainCheckStage, wireIn := "Dataset × Triple", wireOut := "Claim"
    contract := ``ExplainCheckContract, status := .proved
    theorems := [``rdfsExplainCheck_sound, ``L4Factoidal.FPP0.checkBundle_merge,
      ``L4Factoidal.FPP0.checkBundle_rdfsEntails, ``rdfsEntails_of_closure]
    note := "one graph artifact G (the union of the selection; one blank-node scope) and body-less source references; no wasm op (https://github.com/danbri/factoidal/issues/615)" }
]

end L4Factoidal.Dataflow
