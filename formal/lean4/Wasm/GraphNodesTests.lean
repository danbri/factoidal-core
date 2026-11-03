/-
Wasm.GraphNodesTests — build-time checks of the ops `graphCheckNodes` and
`datasetMerge` (`Wasm/Ops/GraphNodes.lean`,
https://github.com/danbri/factoidal/issues/1130, stage 1b).

* Two N-Quads readers, `datasetMerge`, and a SELECT evaluator node: no issue,
  output wire `Table`, no named assumption, every node `proved` and checked.
* Each issue kind with its node, port and port name: `unknownInput`,
  `forwardRef` (a node that reads itself: a cycle), `portCount`,
  `wireMismatch`.
* Refusals: an unknown stage, an empty node list, a `from` element that is
  neither form, a node with no `from`, an unknown input wire label, JSON that
  does not parse.
* Fan-out: one reader feeds two writers.
* A setting on the merge node makes it `unproved`.
* The two tables: the full table serves both ops through `callIO` and lists
  them in its `ops` reflection; `graphCheckNodes` also through the pure `call`.
* `mergeDatasets` (the dataset the op `datasetMerge` stores) on two one-quad
  N-Quads documents that both use `_:b`: 2 quads, 2 blank nodes, and a SELECT
  over the merge gives 2 solutions. The plain union of the same two documents
  has 1 quad. The IO op itself (handles, the scope counter) is run by the npm
  tests (`npm/factoidal/test/pipeline-graph-1130.test.mjs`).

No executable imports this module.
-/
import Wasm.Dispatch

namespace L4Wasm.GraphNodesTests

open L4Wasm.Ops
open L4Factoidal.JSON
open L4Factoidal.RDF

private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def reader : String := "{\"stage\":\"nquadsDocumentReader\",\"from\":[{\"input\":0}]}"
private def reader1 : String := "{\"stage\":\"nquadsDocumentReader\",\"from\":[{\"input\":1}]}"
private def merge (a b : Nat) : String :=
  s!"\{\"stage\":\"datasetMerge\",\"from\":[\{\"node\":{a}},\{\"node\":{b}}]}"
private def select (j : Nat) : String :=
  s!"\{\"stage\":\"shippedEvaluator\",\"settings\":\{\"query\":\"SELECT ?s WHERE \{ ?s ?p ?o }\"},\"from\":[\{\"node\":{j}}]}"
private def graph (inputs : String) (nodes : List String) : String :=
  s!"\{\"inputs\":{inputs},\"nodes\":[{",".intercalate nodes}]}"
private def two : String := "[\"String\",\"String\"]"

/-- Two readers, the merge, a SELECT. -/
def mergeGraph : String := graph two [reader, reader1, merge 0 1, select 2]

#guard has (graphCheckNodes mergeGraph) "\"ok\":true,\"issues\":[],\"wireOut\":\"Table\",\"assumptions\":[]"
#guard has (graphCheckNodes mergeGraph)
  "\"contract\":{\"theorem\":\"L4Factoidal.Dataflow.Graph.guarantee_sound\",\"staticCheck\":\"L4Factoidal.Dataflow.Graph.run_stage_error_only\"}"
-- the merge node: two named ports on Dataset, proved, checked, its contract
#guard has (graphCheckNodes mergeGraph)
  "\"name\":\"datasetMerge\",\"kind\":\"PortComponent\",\"status\":\"proved\",\"registryStatus\":null,\"checked\":true,\"contract\":\"L4Factoidal.RDF.DatasetDen.IsMerge\""
#guard has (graphCheckNodes mergeGraph)
  "\"ports\":[{\"name\":\"left\",\"wire\":\"Dataset\"},{\"name\":\"right\",\"wire\":\"Dataset\"}],\"wireOut\":\"Dataset\""
-- a registry node: one port named in, the fields of pipelineCheckNodes
#guard has (graphCheckNodes mergeGraph)
  "\"name\":\"nquadsDocumentReader\",\"kind\":\"RdfReader\",\"status\":\"proved\",\"registryStatus\":\"proved\",\"checked\":true"
#guard has (graphCheckNodes mergeGraph) "\"ports\":[{\"name\":\"in\",\"wire\":\"String\"}],\"wireOut\":\"Dataset × PrefixList\""
#guard has (graphCheckNodes mergeGraph) "\"derived\":{\"form\":\"SELECT\"}"
#guard has (graphCheckNodes mergeGraph) "\"settingsDigest\":\"sha256:"
#guard has (graphCheckNodes mergeGraph) "\"L4Wasm.Ops.mergeDatasets_isMerge\""
-- the option table of the npm function datasetMerge
#guard apiCheck "datasetMerge" "{\"format\":\"nquads\"}" == "{\"ok\":true}"
#guard has (apiCheck "datasetMerge" "{\"bogus\":\"1\"}") "\"code\":\"option.unknown\""

-- an assumed writer's assumption is in the union
#guard has (graphCheckNodes (graph "[\"String\"]"
    [reader, "{\"stage\":\"turtleDocumentWriter\",\"from\":[{\"node\":0}]}"]))
  "\"issues\":[],\"wireOut\":\"String\",\"assumptions\":[\"L4Factoidal.Dataflow.TurtleWriterRoundTrip\"]"
-- fan-out: one reader feeds two writers
#guard has (graphCheckNodes (graph "[\"String\"]"
    [reader, "{\"stage\":\"nquadsDocumentWriter\",\"from\":[{\"node\":0}]}",
     "{\"stage\":\"ntriplesDocumentWriter\",\"from\":[{\"node\":0}]}"]))
  "\"issues\":[]"

/-! ## Each issue kind -/

-- graph input 5 does not exist
#guard has (graphCheckNodes (graph two
    [reader, "{\"stage\":\"nquadsDocumentReader\",\"from\":[{\"input\":5}]}", merge 0 1]))
  "\"issues\":[{\"kind\":\"unknownInput\",\"node\":1,\"port\":0,\"portName\":\"in\",\"input\":5}]"
-- node 2 reads itself: a cycle
#guard has (graphCheckNodes (graph two [reader, reader1, merge 0 2]))
  "\"issues\":[{\"kind\":\"forwardRef\",\"node\":2,\"port\":1,\"portName\":\"right\",\"ref\":2}]"
-- the merge node has two ports and one source
#guard has (graphCheckNodes (graph two
    [reader, reader1, "{\"stage\":\"datasetMerge\",\"from\":[{\"node\":0}]}"]))
  "\"issues\":[{\"kind\":\"portCount\",\"node\":2,\"ports\":2,\"sources\":1}]"
-- a SELECT table into the merge node's right port
#guard has (graphCheckNodes (graph two [reader, reader1, merge 0 1, select 2, merge 0 3]))
  "\"issues\":[{\"kind\":\"wireMismatch\",\"node\":4,\"port\":1,\"portName\":\"right\",\"source\":\"Table\",\"portWire\":\"Dataset\"}]"
-- an input on a wire that is not text: the reader's port
#guard has (graphCheckNodes (graph "[\"Graph\",\"String\"]" [reader, reader1, merge 0 1]))
  "\"issues\":[{\"kind\":\"wireMismatch\",\"node\":0,\"port\":0,\"portName\":\"in\",\"source\":\"Graph\",\"portWire\":\"String\"}]"
-- the issues are those of graphIssues, in its order
#guard has (graphCheckNodes (graph two [reader, "{\"stage\":\"nquadsDocumentReader\",\"from\":[{\"node\":3}]}",
    "{\"stage\":\"datasetMerge\",\"from\":[{\"node\":0}]}"]))
  "\"issues\":[{\"kind\":\"forwardRef\",\"node\":1,\"port\":0,\"portName\":\"in\",\"ref\":3},{\"kind\":\"portCount\",\"node\":2,\"ports\":2,\"sources\":1}]"

/-! ## Refusals -/

#guard has (graphCheckNodes (graph two [reader, "{\"stage\":\"noSuchStage\",\"from\":[]}"]))
  "\"ok\":false,\"error\":\"graphCheckNodes: no registered stage named 'noSuchStage'\""
#guard has (graphCheckNodes (graph two [])) "\"ok\":false,\"error\":\"graphCheckNodes: no nodes\""
#guard has (graphCheckNodes (graph two ["{\"stage\":\"nquadsDocumentReader\",\"from\":[{\"inp\":0}]}"]))
  "\"ok\":false,\"error\":\"graphCheckNodes: node 0, source 0 is neither"
#guard has (graphCheckNodes (graph two ["{\"stage\":\"nquadsDocumentReader\",\"from\":[{\"input\":0,\"node\":1}]}"]))
  "\"ok\":false"
#guard has (graphCheckNodes (graph two ["{\"stage\":\"nquadsDocumentReader\"}"]))
  "\"ok\":false,\"error\":\"graphCheckNodes: node 0 has no array member from\""
#guard has (graphCheckNodes (graph "[\"Text\"]" [reader]))
  "\"ok\":false,\"error\":\"graphCheckNodes: input 0: 'Text' is not a wire label"
#guard has (graphCheckNodes "{") "\"ok\":false"
#guard has (graphCheckNodes "[]") "\"ok\":false,\"error\":\"graphCheckNodes: graphJson must be a JSON object\""
-- a registry node's settings are checked as pipelineCheckNodes checks them
#guard has (graphCheckNodes (graph "[\"String\"]"
    ["{\"stage\":\"turtleDocumentReader\",\"settings\":{\"format\":\"nt\"},\"from\":[{\"input\":0}]}"]))
  "\"ok\":false"
-- a setting on the merge node: outside the proved domain, unproved
#guard has (graphCheckNodes (graph two [reader, reader1,
    "{\"stage\":\"datasetMerge\",\"settings\":{\"x\":1},\"from\":[{\"node\":0},{\"node\":1}]}"]))
  "\"name\":\"datasetMerge\",\"kind\":\"PortComponent\",\"status\":\"unproved\",\"registryStatus\":null,\"checked\":false"

/-! ## The dispatch tables -/

private def argsOf (xs : List String) : String := (Json.array (xs.map Json.string)).toString

#guard L4Wasm.call "graphCheckNodes" (argsOf [mergeGraph]) == graphCheckNodes mergeGraph
#guard has (L4Wasm.call "graphCheckNodes" (argsOf [])) "expects 1 argument"
#guard has L4Wasm.opsReflectionIO "\"graphCheckNodes\""
#guard has L4Wasm.opsReflectionIO "\"datasetMerge\""

/-! ## The merge of two documents that both use `_:b` -/

private def doc : String := "_:b <http://example.org/p> <http://example.org/o> .\n"

private def parsed (t : String) : Option Dataset :=
  (parseDocumentOutcome t "nquads" "").toOption.map (·.ds)

private def merged : Option Dataset := do
  let a ← parsed doc
  let c ← parsed doc
  pure (mergeDatasets 7 a c)

-- two quads, two blank nodes
#guard merged.map datasetQuadCount == some 2
#guard merged.map (fun ds => (ds.default.map (·.s)).eraseDups.length) == some 2
-- a SELECT over the merge: two solutions
#guard merged.map (fun ds =>
  ((queryParsedDataset ds "SELECT ?s WHERE { ?s ?p ?o }").splitOn "\"type\":\"bnode\"").length - 1) ==
  some 2
-- the union of the same documents, with no scope, is one quad
#guard ((parsed doc).bind fun a => (parsed doc).map fun c =>
  datasetQuadCount (a.combine c).certify.val) == some 1
-- the prefixes of a merge: the first dataset's, then the second's new labels
#guard mergePrefixes [("ex", "http://e/")] [("ex", "http://x/"), ("foaf", "http://f/")] ==
  [("ex", "http://e/"), ("foaf", "http://f/")]

end L4Wasm.GraphNodesTests
