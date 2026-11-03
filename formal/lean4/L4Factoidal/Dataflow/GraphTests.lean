/-
L4Factoidal.Dataflow.GraphTests — checks of `Dataflow/Graph.lean` and
`Dataflow/GraphStages.lean`, evaluated during `lake build`
(https://github.com/danbri/factoidal/issues/1130).

* Two N-Triples documents, each read by its own reader node, merged by the
  two-port merge node, then the default graph and a BGP SELECT: a graph
  pipeline with five nodes and a join of two branches. Both documents use the
  blank-node label `_:b`; after the merge they are two blank nodes, so the
  SELECT gives two solutions (RDF 1.1 Semantics section 5.2).
* `Graph.guarantee_sound` gives the graph's contract with no premise: no node
  has a named assumption.
* Fan-out: one reader node feeds two nodes.
* The static check: a forward reference (a cycle), an unknown graph input, a
  wrong number of sources, a wire mismatch; each is found with its node and
  port, and a run of each stops before any stage runs on bad input.
* Registry signatures as port signatures: the check on a reader, a reasoner
  and two writers, with a conversion on one edge.

No executable imports this module.
-/
import L4Factoidal.Dataflow.GraphStages
import L4Factoidal.Dataflow.PipelineTests

namespace L4Factoidal.Dataflow.GraphTests

open L4Factoidal.Dataflow
open L4Factoidal.Dataflow.PipelineTests
open L4Factoidal.RDF
open L4Factoidal.SPARQL

private def mw : MergeWires testWires := { dataset := .dataset, carrier_eq := rfl }

private def reader : PortComponent testWires testAssumption :=
  .ofComponent (Component.ofStage "ntriplesReader" .text .dataset (some ``ReaderContract)
    (ntriplesReader .rdf11 0))

private def select : PortComponent testWires testAssumption :=
  .ofComponent (Component.ofStage "selectStage" .dataset .graph (some ``SelectContract)
    (selectStage { default := true, named := [] }))

private def bgp : PortComponent testWires testAssumption :=
  .ofComponent (Component.ofStage "bgpSelectStage" .graph .solutions (some ``BgpContract)
    (bgpSelectStage [{ s := .var "s", p := .var "p", o := .var "o" }]))

private def merge : PortComponent testWires testAssumption := datasetMergeStage mw none

/-- Read two documents, merge, select the default graph, query. -/
def twoDocs : Graph testWires testAssumption :=
  { nodes := [ { comp := reader, srcs := [.input 0] },
               { comp := reader, srcs := [.input 1] },
               { comp := merge, srcs := [.node 0, .node 1] },
               { comp := select, srcs := [.node 2] },
               { comp := bgp, srcs := [.node 3] } ] }

private def ex : String := "http://example.org/"
private def docA : String := s!"_:b <{ex}p> <{ex}o> .\n"
private def docB : String := s!"_:b <{ex}p> <{ex}o> .\n"

private def lastCount : Except GraphError (List (Packed testWires)) → Option Nat
  | .ok env => match env.getLast? with
    | some ⟨.solutions, sols⟩ => some (List.length (α := Binding) sols)
    | _ => none
  | _ => none

-- the static check finds nothing; the output wire is `solutions`
#guard graphIssues testWires.conv [.text, .text] twoDocs.sigs == []
#guard graphOutWire twoDocs.sigs == some .solutions
-- one `_:b` per document: two blank nodes after the merge, two solutions
#guard lastCount (twoDocs.run [⟨.text, docA⟩, ⟨.text, docB⟩]) == some 2
-- the same document twice is still two blank nodes
#guard lastCount (twoDocs.run [⟨.text, docA⟩, ⟨.text, docA⟩]) == some 2
-- a syntax error in the second document stops at node 1
#guard match twoDocs.run [⟨.text, docA⟩, ⟨.text, "<a> ."⟩] with
  | .error (.stage "ntriplesReader" _) => true
  | _ => false
-- the merge node's ports
#guard merge.sig.ins.map (·.1) == ["left", "right"]

/-- No node has a named assumption: the graph's contract holds of every
successful run with no premise. -/
theorem twoDocs_sound (inputs env : List (Packed testWires)) (h : twoDocs.run inputs = .ok env) :
    twoDocs.contract inputs env :=
  Graph.guarantee_sound twoDocs (fun m hm => by
    simp [Graph.assumptions, twoDocs, reader, select, bgp, merge, datasetMergeStage,
      PortComponent.ofComponent, Component.ofStage, StageSig.toPortSig] at hm) inputs env h

/-- Fan-out: one reader feeds two selections. -/
def fanOut : Graph testWires testAssumption :=
  { nodes := [ { comp := reader, srcs := [.input 0] },
               { comp := select, srcs := [.node 0] },
               { comp := select, srcs := [.node 0] } ] }

#guard graphIssues testWires.conv [.text] fanOut.sigs == []
#guard match fanOut.run [⟨.text, s!"<{ex}a> <{ex}p> <{ex}b> .\n"⟩] with
  | .ok env => env.length == 3
  | _ => false

/-! ## The static check -/

private def withSrcs (g : Graph testWires testAssumption) (i : Nat) (srcs : List Src) :
    Graph testWires testAssumption :=
  { nodes := g.nodes.zipIdx.map fun (n, j) => if j == i then { n with srcs } else n }

-- node 2 reads itself: a cycle
#guard graphIssues testWires.conv [.text, .text] (withSrcs twoDocs 2 [.node 0, .node 2]).sigs ==
  [.forwardRef 2 1 2]
-- node 1 reads a later node
#guard graphIssues testWires.conv [.text, .text] (withSrcs twoDocs 1 [.node 3]).sigs ==
  [.forwardRef 1 0 3]
-- graph input 5 does not exist
#guard graphIssues testWires.conv [.text, .text] (withSrcs twoDocs 1 [.input 5]).sigs ==
  [.unknownInput 1 0 5]
-- the merge node has two ports and one source
#guard graphIssues testWires.conv [.text, .text] (withSrcs twoDocs 2 [.node 0]).sigs ==
  [.portCount 2 2 1]
-- the query's solutions into the merge node's right port
#guard graphIssues testWires.conv [.text, .text]
    { nodes := twoDocs.nodes ++ [{ comp := merge, srcs := [.node 0, .node 4] }] : Graph testWires testAssumption }.sigs ==
  [.wireMismatch 5 1 .solutions .dataset]
-- the run of a graph with a forward reference stops at a source, before the stage runs
#guard match (withSrcs twoDocs 1 [.node 3]).run [⟨.text, docA⟩, ⟨.text, docB⟩] with
  | .error (.source "ntriplesReader") => true
  | _ => false
-- an input on the wrong wire: the check sees it, the run stops with a wire error
#guard graphIssues testWires.conv [.graph, .text] twoDocs.sigs ==
  [.wireMismatch 0 0 .graph .text]
#guard match twoDocs.run [⟨.graph, ([] : L4Factoidal.RDF.Graph)⟩, ⟨.text, docB⟩] with
  | .error (.wire "ntriplesReader") => true
  | _ => false

/-! ## Registry signatures as port signatures -/

private def entrySig (n : String) : Option (PortSig Wire Lean.Name) :=
  (registry.find? (·.nodeName == n)).map fun e => e.sig.toPortSig

private def regGraph (nodes : List (String × List Src)) : List (PortSig Wire Lean.Name × List Src) :=
  nodes.filterMap fun (n, srcs) => (entrySig n).map (·, srcs)

-- a Turtle reader feeding a Turtle writer and a TriG writer (fan-out), each
-- through the datasetPrefixes-to-dataset conversion
#guard (regGraph [("turtleDocumentReader", [.input 0]), ("turtleDocumentWriter", [.node 0]),
    ("trigDocumentWriter", [.node 0])]).length == 3
#guard graphIssues Wire.conv [.text] (regGraph [("turtleDocumentReader", [.input 0]),
    ("turtleDocumentWriter", [.node 0]), ("trigDocumentWriter", [.node 0])]) == []
-- a writer's text into a reasoner's graph port
#guard graphIssues Wire.conv [.text] (regGraph [("turtleDocumentReader", [.input 0]),
    ("turtleDocumentWriter", [.node 0]), ("rdfsReasoner", [.node 1])]) ==
  [.wireMismatch 2 0 .text .graph]

#print axioms twoDocs_sound

end L4Factoidal.Dataflow.GraphTests
