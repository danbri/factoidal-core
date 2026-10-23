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
import L4Factoidal.Storage.BlockDenotation

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

/-- The registry. Order: boundary, syntax, stores, query, reasoning,
validation, evidence. -/
def registry : List Entry := [
  { area := "Document decode (UTF-8, format label)", dir := "RDF"
    stage := ``decodeStage, wireIn := "Document", wireOut := "RdfFormat × String"
    contract := ``DecodeContract, status := .proved
    theorems := [``fromUTF8?_toUTF8]
    note := "media types other than application/ld+json give no format (finding 1)" },
  { area := "RDF readers: N-Triples, Turtle, N-Quads, TriG, RDF/XML, JSON-LD (set contract)"
    dir := "RDF"
    stage := ``parseStage, wireIn := "RdfFormat × String", wireOut := "Dataset"
    contract := ``ParseContract, status := .proved
    theorems := [``L4Factoidal.RDF.Source.parseDocument_set, ``L4Factoidal.RDF.Dataset.memQuad_toSet,
      ``L4Factoidal.RDF.Dataset.toSet_isSet, ``SetOf.den_eq]
    note := "blank nodes not scoped by Document.source (finding 2)" },
  { area := "RDF readers: grammar conformance", dir := "Syntax"
    wireIn := "String", wireOut := "Dataset", status := .tested
    tests := ["W3C RDF 1.1 syntax suites (l4w3c)", "W3C RDF 1.2 syntax suites (l4w3c)"] },
  { area := "RDF writers (N-Triples, Turtle, N-Quads, TriG, RDF/XML, JSON-LD)", dir := "Syntax"
    wireIn := "Dataset", wireOut := "String", status := .missing
    note := "round trip against Dataset.den not stated (phase C)" },
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
    note := "decoding to SolutionSeq uses a state the run does not return (finding 4)" },
  { area := "End to end: document bytes to SBM11 WHERE answer", dir := "Dataflow"
    stage := ``documentToWhere, wireIn := "Document", wireOut := "id table (WhereOut)"
    contract := ``documentToWhere_sound, status := .proved
    theorems := [``documentToWhere_sound, ``Stage.comp_ok_contract]
    ioAssumptions := [``ReadsWritten]
    note := "premises: ReadsWritten, plan hypotheses, QHyps, Sbm11Folded, PermOk" },
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
      ``L4Factoidal.Storage.IndexedBlockWireV4.den_decode_encode?]
    note := "one id per structural term (issue 977)" },
  { area := "Store interface StoreCaps (planner)", dir := "SPARQL"
    wireIn := "PatternBound", wireOut := "List Triple", status := .missing
    note := "no denotation (phase B1)" },
  { area := "COTTAS store", dir := "Cottas"
    wireIn := "Dataset", wireOut := "bytes", status := .missing },
  { area := "HDT store", dir := "HDT"
    wireIn := "Dataset", wireOut := "bytes", status := .missing },
  { area := "Planner SELECT over the kept entries", dir := "Storage"
    stage := ``plannerSelectStage, wireIn := "Dataset", wireOut := "SolutionSeq"
    contract := ``PlannerSelectContract, status := .proved
    theorems := [``L4Factoidal.Storage.PlannerSoundness.plannerSoundnessSelect]
    note := "input is an in-memory Dataset; no stage from SBM11 files (finding 6)" },
  { area := "SPARQL query evaluation (reference evaluator)", dir := "SPARQL"
    wireIn := "Query × Dataset", wireOut := "QueryResult", status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all (l4w3c)", "W3C SPARQL 1.2 (l4w3c)"] },
  { area := "SPARQL update", dir := "SPARQL"
    wireIn := "Update × Dataset", wireOut := "Dataset", status := .tested
    tests := ["W3C SPARQL 1.1 manifest-all, update entries (l4w3c)"] },
  { area := "SPARQL protocol and graph store", dir := "SPARQL"
    wireIn := "HTTP request", wireOut := "HTTP response", status := .missing },
  { area := "SPARQL results formats (XML, JSON, CSV, TSV)", dir := "SPARQL"
    wireIn := "QueryResult", wireOut := "String", status := .missing },
  { area := "RDFS closure (soundness)", dir := "RDFS"
    stage := ``rdfsClosureStage, wireIn := "Graph", wireOut := "Graph"
    contract := ``L4Factoidal.RDF.RdfsEntails, status := .proved
    theorems := [``L4Factoidal.RDF.fullClosure_entails]
    note := "one graph, not a dataset (finding 5)" },
  { area := "RDFS entailment completeness, negative tests", dir := "RDFS"
    wireIn := "Graph", wireOut := "Bool", status := .missing },
  { area := "OWL 2 RL reasoner", dir := "OWL"
    wireIn := "Graph", wireOut := "Graph", status := .missing },
  { area := "RIF reasoner", dir := "RIF"
    wireIn := "Graph × rules", wireOut := "Graph", status := .missing },
  { area := "SHACL validation", dir := "SHACL"
    wireIn := "Graph × shapes", wireOut := "ValidationReport", status := .tested
    tests := ["W3C SHACL Core (l4shacl)"] },
  { area := "ShEx validation", dir := "ShEx"
    wireIn := "Graph × schema", wireOut := "report", status := .missing },
  { area := "CSVW (tabular data to RDF)", dir := "CSVW"
    wireIn := "CSV × metadata", wireOut := "Dataset", status := .missing },
  { area := "RDFC-1.0 canonicalization", dir := "RDF"
    wireIn := "Dataset", wireOut := "String", status := .missing },
  { area := "VC Data Integrity (sign, verify)", dir := "VC"
    wireIn := "Dataset × key", wireOut := "Bool", status := .missing
    note := "crypto assumptions not yet named (phase E)" },
  { area := "XML parser", dir := "XML"
    wireIn := "String", wireOut := "XML document", status := .missing },
  { area := "XPath evaluation", dir := "XPath"
    wireIn := "XML document × expression", wireOut := "sequence", status := .missing },
  { area := "XSLT transformation", dir := "XSLT"
    wireIn := "XML document × stylesheet", wireOut := "XML document", status := .missing },
  { area := "Schematron validation", dir := "Schematron"
    wireIn := "XML document × schema", wireOut := "report", status := .missing },
  { area := "Hash and signature primitives (HACL* call-outs)", dir := "Crypto"
    wireIn := "bytes", wireOut := "bytes", status := .missing
    note := "native and pure Lean compared by tests, not proved (https://github.com/danbri/factoidal/issues/777)" },
  { area := "Proof checker (FPP0 bundles)", dir := "Proof"
    stage := ``proofCheckStage, wireIn := "Bundle", wireOut := "Claim"
    contract := ``CheckContract, status := .proved
    theorems := [``L4Factoidal.FPP0.checkBundle_merge] }
]

end L4Factoidal.Dataflow
