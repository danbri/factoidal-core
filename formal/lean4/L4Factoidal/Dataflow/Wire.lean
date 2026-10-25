/-
L4Factoidal.Dataflow.Wire — the wire types of the stage registry as a finite
enumeration (https://github.com/danbri/factoidal/issues/1002, step 1).

Each registry entry (`Dataflow/Registry.lean`) names the wire it reads
(`wireIn`), the wire it writes (`wireOut`) and its parameters (`params`): the
inputs a node supplies when it is made (a SPARQL query, a shapes graph, render
options), not values that travel on a wire. Before this module the two wires
were free text, and the same type had several spellings ("Graph",
"Graph (rows written)"; "id table", "id table (WhereOut)"), so no function
could check that one stage's output is the next stage's input.

`Wire.label` is the text that `docs/dataflow-inventory.md` and the wasm op
`stageList` show.

## Conversions

`Wire.conv a b` is true for the four pairs where a value of `a` becomes a
value of `b` by a fixed total function, which the composed contract of a
pipeline names (`Dataflow/Pipeline.lean`, `arrive`):

* `datasetPrefixes` to `dataset`: the dataset (the prefixes are dropped);
* `datasetPrefixes` to `graph`, `dataset` to `graph`: the default graph;
* `graph` to `dataset`: the dataset with this default graph and no named
  graph.

No other pair converts. A pipeline whose stage output is neither the next
stage's input nor converts to it is not well typed (`wellTyped`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.Dataflow

/-- The wire types of the registry. -/
inductive Wire where
  | text | document | formatText
  | dataset | datasetPrefixes | graph | graphs | triples | quads | chunks
  | patternBound | datasetBackend | graphBackend | certifiedDataset | store | lawfulDataset
  | solutions | results | answer | bool
  | validationReport | report
  | bundle | claim | graphBundle | graphClaim | explainGraphResult
  | canonical | bytes | digest
  | generations | fileGen | idTable | quadBlock | block | files | logState
  | json | xml | xdmSequence | facts | csv | httpRequest | httpResponse
  | vcSignIn | vcVerifyIn | ed25519Input
  deriving Repr, DecidableEq, Inhabited

/-- The text of a wire in the inventory and in the `stageList` op. -/
def Wire.label : Wire → String
  | .text => "String"
  | .document => "Document"
  | .formatText => "RdfFormat × String"
  | .dataset => "Dataset"
  | .datasetPrefixes => "Dataset × PrefixList"
  | .graph => "Graph"
  | .graphs => "List Graph"
  | .triples => "List Triple"
  | .quads => "List Quad"
  | .chunks => "chunks"
  | .patternBound => "PatternBound"
  | .datasetBackend => "DatasetBackend"
  | .graphBackend => "GraphBackend"
  | .certifiedDataset => "CertifiedDataset"
  | .store => "LawfulStore"
  | .lawfulDataset => "LawfulDataset"
  | .solutions => "SolutionSeq"
  | .results => "QueryResult"
  | .answer => "Answer"
  | .bool => "Bool"
  | .validationReport => "ValidationReport"
  | .report => "report"
  | .bundle => "Bundle"
  | .claim => "Claim"
  | .graphBundle => "GraphBundle"
  | .graphClaim => "GraphClaim"
  | .explainGraphResult => "ExplainGraphResult"
  | .canonical => "String × String"
  | .bytes => "bytes"
  | .digest => "digest"
  | .generations => "MemGen × FileGen"
  | .fileGen => "FileGen"
  | .idTable => "id table (WhereOut)"
  | .quadBlock => "QuadBlock"
  | .block => "IndexedBlock.Block"
  | .files => "files"
  | .logState => "State"
  | .json => "JSON"
  | .xml => "XML document"
  | .xdmSequence => "sequence"
  | .facts => "Facts"
  | .csv => "CSV"
  | .httpRequest => "HTTP request"
  | .httpResponse => "HTTP response"
  | .vcSignIn => "SignIn (key, document, proof config)"
  | .vcVerifyIn => "VerifyIn (key, document, proof config, proofValue)"
  | .ed25519Input => "pk × message × signature"

/-- Every wire, in declaration order. -/
def Wire.all : List Wire :=
  [ .text, .document, .formatText
  , .dataset, .datasetPrefixes, .graph, .graphs, .triples, .quads, .chunks
  , .patternBound, .datasetBackend, .graphBackend, .certifiedDataset, .store, .lawfulDataset
  , .solutions, .results, .answer, .bool
  , .validationReport, .report
  , .bundle, .claim, .graphBundle, .graphClaim, .explainGraphResult
  , .canonical, .bytes, .digest
  , .generations, .fileGen, .idTable, .quadBlock, .block, .files, .logState
  , .json, .xml, .xdmSequence, .facts, .csv, .httpRequest, .httpResponse
  , .vcSignIn, .vcVerifyIn, .ed25519Input ]

theorem Wire.mem_all (w : Wire) : w ∈ Wire.all := by
  cases w <;> simp [Wire.all]

/-- The conversions between distinct wires (module header). -/
def Wire.conv : Wire → Wire → Bool
  | .datasetPrefixes, .dataset => true
  | .datasetPrefixes, .graph => true
  | .dataset, .graph => true
  | .graph, .dataset => true
  | _, _ => false

/-- The four conversions, and no other. -/
theorem Wire.conv_cases {a b : Wire} (h : Wire.conv a b = true) :
    (a = .datasetPrefixes ∧ b = .dataset) ∨ (a = .datasetPrefixes ∧ b = .graph) ∨
    (a = .dataset ∧ b = .graph) ∨ (a = .graph ∧ b = .dataset) := by
  cases a <;> cases b <;> simp_all [Wire.conv]

-- labels are distinct, so a label names one wire
#guard (Wire.all.map Wire.label).eraseDups.length == Wire.all.length
#guard Wire.all.length == 47
#guard (Wire.all.filter fun a => (Wire.all.filter fun b => Wire.conv a b).length > 0).length == 3

end L4Factoidal.Dataflow
