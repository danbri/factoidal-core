/-
L4Factoidal.Dataflow.PipelineTests — checks of `Dataflow/Pipeline.lean`,
evaluated during `lake build` (https://github.com/danbri/factoidal/issues/1002,
step 1).

Registry signatures (`Entry.sig`, wires of `Dataflow/Wire.lean`):

* A well-typed three-stage path (Turtle writer, Turtle reader, TriG
  writer): `wellTyped` accepts it, and the guarantee's assumptions are the
  union of the three stages' named assumptions, written out.
* An ill-typed path (a writer's text into a reasoner's graph) is rejected,
  with the first mismatch at stage 0; the same check on hand-made signatures
  is decided by the kernel (`example`).
* A path with a conversion reports where it converts.

Components with real stages (a test wire system `testWires` that gives
carriers to the wires the components use; every other wire carries `Unit`):

* The N-Triples reader, the graph selection, and a BGP SELECT, as one
  pipeline: `Pipeline.guarantee_sound` gives its composed contract with no
  premise (no stage has a named assumption), and a run on a document returns
  solutions (`#guard`).
* The native SHA-256 IO stage with the pure Lean SHA-256 as its model: the
  guarantee's one assumption is `Sha256Agrees`, and `guarantee_sound` needs
  exactly that premise.

No executable imports this module.
-/
import L4Factoidal.Dataflow.Pipeline
import L4Factoidal.Dataflow.Registry

namespace L4Factoidal.Dataflow.PipelineTests

open L4Factoidal.Dataflow
open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Registry signatures -/

private def sigsOf (names : List String) : List (StageSig Wire Lean.Name) :=
  names.filterMap fun n => (registry.find? (·.nodeName == n)).map Entry.sig

private def assumptionsOf (n : String) : List Lean.Name :=
  ((registry.find? (·.nodeName == n)).map (·.ioAssumptions)).getD []

private def path3 : List String :=
  ["turtleDocumentWriter", "turtleDocumentReader", "trigDocumentWriter"]

-- all three names are registered
#guard (sigsOf path3).length == 3
-- well typed: Dataset → String, String → Dataset × PrefixList → (convert) Dataset → String
#guard wellTyped Wire.conv (sigsOf path3)
-- the guarantee's assumptions are the union of the stages' named assumptions
#guard (pipelineReport Wire.conv (sigsOf path3)).assumptions ==
  [``TurtleWriterRoundTrip, ``TrigWriterRoundTrip]
#guard (pipelineReport Wire.conv (sigsOf path3)).assumptions ==
  (assumptionsOf "turtleDocumentWriter" ++ assumptionsOf "turtleDocumentReader" ++
    assumptionsOf "trigDocumentWriter").eraseDups
-- the reader adds no assumption; each writer adds one
#guard assumptionsOf "turtleDocumentReader" == []
-- the conversion between the reader and the second writer is reported
#guard (pipelineReport Wire.conv (sigsOf path3)).conversions == [(1, .datasetPrefixes, .dataset)]
#guard (pipelineReport Wire.conv (sigsOf path3)).mismatch == none
-- a repeated stage adds its assumption once
#guard (pipelineReport Wire.conv (sigsOf (path3 ++ ["turtleDocumentReader", "turtleDocumentWriter"]))).assumptions ==
  [``TurtleWriterRoundTrip, ``TrigWriterRoundTrip]

-- ill typed: the writer's text is not the reasoner's graph
#guard !wellTyped Wire.conv (sigsOf ["turtleDocumentWriter", "rdfsReasoner"])
#guard (pipelineReport Wire.conv (sigsOf ["turtleDocumentWriter", "rdfsReasoner"])).mismatch == some 0
#guard (pipelineReport Wire.conv (sigsOf ["turtleDocumentReader", "rdfsReasoner", "turtleDocumentWriter",
  "rdfsReasoner"])).mismatch == some 2
-- the empty pipeline is not well typed
#guard !wellTyped Wire.conv ([] : List (StageSig Wire Lean.Name))

private def sig (i o : Wire) : StageSig Wire Lean.Name :=
  { name := "s", inW := i, outW := o, contract := none, assumptions := [] }

/-- The check rejects text into a graph input, and `wellTyped_iff` turns the
rejection into the negation of `WellTyped`. -/
example : ¬ WellTyped Wire.conv [sig .dataset .text, sig .graph .graph] := by
  rw [← wellTyped_iff]
  decide

example : WellTyped Wire.conv [sig .text .datasetPrefixes, sig .graph .graph, sig .dataset .text] := by
  rw [← wellTyped_iff]
  decide

/-! ## Components with real stages -/

/-- The carriers of the test wire system. -/
abbrev testCarrier : Wire → Type
  | .text => String
  | .bytes => ByteArray
  | .dataset => Dataset
  | .datasetPrefixes => Dataset × PrefixList
  | .graph => Graph
  | .solutions => SolutionSeq
  | _ => Unit

/-- The conversions of `Wire.conv` on the test carriers. -/
def testCoe : (a b : Wire) → testCarrier a → Option (testCarrier b)
  | .datasetPrefixes, .dataset, x => some x.1
  | .datasetPrefixes, .graph, x => some x.1.default
  | .dataset, .graph, x => some x.default
  | .graph, .dataset, x => some { default := x, named := [] }
  | _, _, _ => none

/-- The test wire system: `Wire.conv` with the carriers above. -/
def testWires : WireSystem Wire where
  Carrier := testCarrier
  conv := Wire.conv
  coe := testCoe
  coe_some a b h x := by
    rcases Wire.conv_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The statement of each assumption name in these tests: `Sha256Agrees` is
the realisation of the native SHA-256 IO stage by the pure Lean SHA-256;
no other name is used. -/
def testAssumption (n : Lean.Name) : Prop :=
  n = ``Sha256Agrees → sha256NativeIO.Realised (fun b => .ok (L4Factoidal.Crypto.sha256 b))

private def ex : String := "http://example.org/"

private def sel : GraphSelection := { default := true, named := [] }

private def q : Bgp := [{ s := .var "s", p := .var "p", o := .var "o" }]

/-- Reader, selection, BGP SELECT: three registered stages as components. -/
def readSelectQuery : Pipeline testWires testAssumption :=
  [ Component.ofStage "ntriplesReader" .text .dataset (some ``ReaderContract) (ntriplesReader .rdf11 0),
    Component.ofStage "selectStage" .dataset .graph (some ``SelectContract) (selectStage sel),
    Component.ofStage "bgpSelectStage" .graph .solutions (some ``BgpContract) (bgpSelectStage q) ]

-- the component signatures agree with the registry's on the wires
#guard (readSelectQuery.sigs.map fun s => (s.name, s.inW, s.outW)) ==
  ((sigsOf ["ntriplesReader", "selectStage", "bgpSelectStage"]).map fun s => (s.name, s.inW, s.outW))
#guard wellTyped Wire.conv readSelectQuery.sigs
#guard readSelectQuery.guarantee.assumptions == []

/-- No stage has a named assumption, so the composed contract holds of every
successful run with no premise. -/
theorem readSelectQuery_sound (x y : Packed testWires) (h : readSelectQuery.run x = .ok y) :
    readSelectQuery.guarantee.contract x y :=
  Pipeline.guarantee_sound readSelectQuery (fun n hn => by simp [Pipeline.guarantee,
    assumptionUnion, Pipeline.sigs, readSelectQuery, Component.ofStage] at hn) x y h

private def doc : String := s!"<{ex}a> <{ex}p> <{ex}b> .\n<{ex}a> <{ex}q> <{ex}c> .\n"

private def solutionCount : Except PipelineError (Packed testWires) → Option Nat
  | .ok ⟨.solutions, sols⟩ => some (List.length (α := Binding) sols)
  | _ => none

-- two triples in the default graph: two solutions
#guard solutionCount (readSelectQuery.run ⟨.text, doc⟩) == some 2
-- a syntax error stops the run at the reader
#guard match readSelectQuery.run ⟨.text, "<a> ."⟩ with
  | .error (.stage "ntriplesReader" _) => true
  | _ => false
-- a value on the wrong wire stops with a wire error at the first stage
#guard match readSelectQuery.run ⟨.graph, ([] : Graph)⟩ with
  | .error (.wire "ntriplesReader") => true
  | _ => false

/-- The native SHA-256, modelled by the pure Lean SHA-256. -/
def nativeHash : Pipeline testWires testAssumption :=
  [ Component.ofIOStage "sha256NativeIO" .bytes .bytes ``Sha256Agrees sha256NativeIO
      (fun b => .ok (L4Factoidal.Crypto.sha256 b)) ⟨fun h => h rfl, fun h _ => h⟩ ]

#guard nativeHash.guarantee.assumptions == [``Sha256Agrees]

/-- The guarantee of the IO pipeline needs exactly its named assumption. -/
theorem nativeHash_sound (hA : sha256NativeIO.Realised (fun b => .ok (L4Factoidal.Crypto.sha256 b)))
    (x y : Packed testWires) (h : nativeHash.run x = .ok y) : nativeHash.guarantee.contract x y :=
  Pipeline.guarantee_sound nativeHash (fun _ _ _ => hA) x y h

#print axioms readSelectQuery_sound
#print axioms nativeHash_sound

end L4Factoidal.Dataflow.PipelineTests
