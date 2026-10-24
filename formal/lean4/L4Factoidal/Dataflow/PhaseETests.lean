/-
L4Factoidal.Dataflow.PhaseETests — checks of `Dataflow/PhaseE.lean`, evaluated
during `lake build` (https://github.com/danbri/factoidal/issues/975, phase E).

1. The empty-input RDFS axiom example: from the empty graph, the explain stage
   gives a bundle for `rdfs:subPropertyOf rdfs:subPropertyOf
   rdfs:subPropertyOf`; its support is rdfs6 ← rdfs2 ← two axioms (four
   foundational steps), so the emitter does not take the rdfD2 route. The
   chain axiom → rdfD2 → rdfs6 of the coherence document is a bundle written
   here by hand over the same artifacts; the kernel and the RDFS profile check
   accept it (three foundational steps).
2. Profile licensing: a bundle whose axiom artifact holds an arbitrary triple
   `ex:a ex:b ex:c` is ACCEPTED by the kernel (finding), fails
   `profileAxiomsOk`, and `proofCheckRdfsStage` refuses it.
3. The corpus-coherence demonstration (TriG: observation graph, schema graph,
   empty named graph): `ex:alice ex:affiliatedWith ex:organisation` by rdfs7;
   the bundle cites exactly the observation graph and the schema graph; the
   empty graph is not cited; with the observation graph only, explain fails.
4. Blank nodes: a class `_:c` shared by two named graphs of one dataset (one
   scope, RDF 1.1 Concepts section 4) gives `ex:Employee rdfs:subClassOf
   ex:Person` by rdfs11; rdfs9 with a blank-node class derives nothing
   (finding); a mutation that reads the schema triple from a second artifact with
   the same body is refused as a blank-node scope conflict. A target with a
   blank node keeps its raw label in the conclusion.
5. RDFC-1.0 stage: the same graph with two blank-node labellings gives the
   same canonical text (a test of relabelling invariance, not a proof).
6. VC: the verify stage refuses a proofValue that is not multibase-z.

No executable imports this module.
-/
import L4Factoidal.Dataflow.PhaseE

namespace L4Factoidal.Dataflow.PhaseETests

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.FPP0
open L4Factoidal.Dataflow

private def okVal? {ε β : Type} : Except ε β → Option β
  | .ok b => some b
  | .error _ => none

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private theorem noCmps : ∀ c ∈ ([] : List WfIri), IsRdfMemberIri c := by
  intro c hc; cases hc

/-- The rule of the step that concludes `u`, and the rules of its premises,
read back to the leaves along the first premise. -/
private def chainOf (b : Bundle) (u : Triple) : List RuleId :=
  let byId (i : String) := b.steps.toList.find? (·.id == i)
  let rec go (fuel : Nat) (st : BundleStep) : List RuleId :=
    match fuel, st.justification with
    | 0, _ => []
    | _, .adapterEvidence _ _ => []
    | n + 1, .rule r _ _ =>
      r :: (match st.premises.head? >>= byId with
            | some p => go n p
            | none => [])
  let concludes (st : BundleStep) : Bool :=
    match st.conclusion with
    | .rdfDerivable _ _ v => v == u
    | .clif _ => false
  match b.steps.toList.find? concludes with
  | some st => go 8 st
  | none => []

/-! ## 1. The empty-input axiom example -/

private def spSpSp : Triple :=
  { s := .iri rdfsSubPropertyOf, p := rdfsSubPropertyOf, o := .iri rdfsSubPropertyOf }

private def defaultOnly : GraphSelection := { default := true }

private def emptyBundle? : Option Bundle :=
  okVal? ((rdfsExplainStage [] [] defaultOnly).run (Dataset.empty, spSpSp))

#guard emptyBundle?.isSome
-- the emitter's witness: rdfs6 from `rdfs:subPropertyOf rdf:type rdf:Property`,
-- which it derives by rdfs2 from two axioms (4 foundational steps), not by rdfD2
#guard match emptyBundle? with
  | some b => (checkBundle b).foundationalOnly && (checkBundle b).counts.foundational == 4
  | none => false
#guard (emptyBundle?.map (chainOf · spSpSp)) == some [.rdfs6, .rdfs2, .axiomatic]

/- The chain of the coherence document, axiom → rdfD2 → rdfs6, as a bundle
written by hand over the same two artifacts: the axiom is
`rdfs:isDefinedBy rdfs:subPropertyOf rdfs:seeAlso` (RDF 1.1 Semantics 9.3). -/
private def isDefAxiom : Triple :=
  { s := .iri rdfsIsDefinedBy, p := rdfsSubPropertyOf, o := .iri rdfsSeeAlso }
private def spTypeProp : Triple :=
  { s := .iri rdfsSubPropertyOf, p := rdfType, o := .iri rdfProperty }

private def chainBundle : Bundle :=
  let ax := axiomaticTriples [] []
  let gd := graphDigest []
  let ad := graphDigest ax
  let step (id : String) (r : RuleId) (ps : List String) (u : Triple) : BundleStep :=
    { id := id, justification := .rule r "G" "AX", premises := ps
      conclusion := .rdfDerivable gd ad u, level := .foundational, profile := fpp0Profile }
  { artifacts := #[ gArtifact [], axArtifact ax ]
    assumptions := #[]
    steps := #[ step "a" .axiomatic [] isDefAxiom, step "d" .rdfD2 ["a"] spTypeProp,
                step "s" .rdfs6 ["d"] spSpSp ]
    conclusion := .rdfDerivable gd ad spSpSp }

#guard (axiomaticTriples [] []).contains isDefAxiom
#guard (checkBundle chainBundle).foundationalOnly
#guard (checkBundle chainBundle).counts.foundational == 3
#guard chainOf chainBundle spSpSp == [.rdfs6, .rdfD2, .axiomatic]
#guard ((proofCheckRdfsStage [] [] noCmps).run chainBundle matches .ok _)
-- the axiom leaf is a triple of the RDFS axiom set, and the axiom set is the profile's
#guard match emptyBundle? with
  | some b => b.steps.toList.any (fun st => match st.justification, st.conclusion with
      | .rule .axiomatic _ _, .rdfDerivable _ _ v =>
          (supportOf b).contains st.id && (axiomaticTriples [] []).contains v
      | _, _ => false) &&
    profileAxiomsOk (axiomaticTriples [] []) b (graphDigest (axiomaticTriples [] []))
  | none => false
-- explain then check, and the checker with the RDFS profile, accept it
#guard ((rdfsExplainCheckStage [] [] noCmps defaultOnly).run (Dataset.empty, spSpSp)) matches .ok _
#guard match emptyBundle? with
  | some b => ((proofCheckRdfsStage [] [] noCmps).run b matches .ok _)
  | none => false

/-! ## 2. An artifact named "axioms" is not the RDFS profile -/

private def exA : WfIri := iri! "http://example.org/a"
private def exB : WfIri := iri! "http://example.org/b"
private def exC : WfIri := iri! "http://example.org/c"
private def fakeAxiom : Triple := { s := .iri exA, p := exB, o := .iri exC }
private def fakeAx : Graph := [fakeAxiom]
private def fakeConcl : Triple := { s := .iri exB, p := rdfType, o := .iri rdfProperty }

private def fakeBundle : Bundle :=
  let gd := graphDigest []
  let ad := graphDigest fakeAx
  { artifacts := #[ { id := "G", kind := .graph, digest := gd, body := some [] },
                    { id := "axioms", kind := .graph, digest := ad, body := some fakeAx } ]
    assumptions := #[]
    steps := #[
      { id := "s1", justification := .rule .axiomatic "G" "axioms", premises := []
        conclusion := .rdfDerivable gd ad fakeAxiom, level := .foundational, profile := fpp0Profile },
      { id := "s2", justification := .rule .rdfD2 "G" "axioms", premises := ["s1"]
        conclusion := .rdfDerivable gd ad fakeConcl, level := .foundational, profile := fpp0Profile } ]
    conclusion := .rdfDerivable gd ad fakeConcl }

-- FINDING: the kernel accepts it with an empty frontier
#guard (checkBundle fakeBundle).foundationalOnly
-- the profile binding refuses it
#guard !profileAxiomsOk (axiomaticTriples [] []) fakeBundle (graphDigest fakeAx)
#guard (proofCheckRdfsStage [] [] noCmps).run fakeBundle matches .error _

/-! ## 3. The corpus-coherence demonstration -/

private def exAlice : WfIri := iri! "http://example.org/alice"
private def exOrg : WfIri := iri! "http://example.org/organisation"
private def exWorksFor : WfIri := iri! "http://example.org/worksFor"
private def exAffiliated : WfIri := iri! "http://example.org/affiliatedWith"
private def gObs : Subject := .iri (iri! "http://example.org/obs")
private def gSchema : Subject := .iri (iri! "http://example.org/schema")
private def gEmpty : Subject := .iri (iri! "http://example.org/empty")

private def trig : String :=
  "@prefix ex: <http://example.org/> .\n" ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n" ++
  "ex:obs { ex:alice ex:worksFor ex:organisation . }\n" ++
  "ex:schema { ex:worksFor rdfs:subPropertyOf ex:affiliatedWith . }\n" ++
  "ex:empty { }\n"

private def parsed? : Option Dataset :=
  okVal? ((decodeStage.comp (parseStage {} .rdf12 none)).run
    { bytes := trig.toUTF8, mediaType := "application/trig", source := "test:coherence" })

private def allThree : GraphSelection := { named := [gObs, gSchema, gEmpty] }
private def obsOnly : GraphSelection := { named := [gObs] }

private def affiliated : Triple := { s := .iri exAlice, p := exAffiliated, o := .iri exOrg }
private def obsGraph : Graph := [{ s := .iri exAlice, p := exWorksFor, o := .iri exOrg }]
private def schemaGraph : Graph :=
  [{ s := .iri exWorksFor, p := rdfsSubPropertyOf, o := .iri exAffiliated }]

private def demo? : Option Bundle :=
  parsed? >>= fun ds => okVal? ((rdfsExplainStage [] [] allThree).run (ds, affiliated))

private def sourceDigests (b : Bundle) : List String :=
  (b.artifacts.toList.filter (fun a => a.body.isNone)).map (·.digest)

#guard demo?.isSome
#guard match demo? with
  | some b => (checkBundle b).foundationalOnly && (checkBundle b).counts.foundational == 3
  | none => false
#guard (demo?.map (chainOf · affiliated)) == some [.rdfs7, .base]
-- both source graphs are cited, the empty named graph is not
#guard match demo? with
  | some b => let d := sourceDigests b
      d.length == 2 && d.contains (graphDigest obsGraph) && d.contains (graphDigest schemaGraph) &&
      !d.contains (graphDigest [])
  | none => false
-- the claim names the selection and the profile axiom set
#guard match parsed? with
  | some ds => (okVal? ((rdfsExplainCheckStage [] [] noCmps allThree).run (ds, affiliated))) ==
      some (.rdfDerivable (graphDigest (ds.select allThree)) (graphDigest (axiomaticTriples [] [])) affiliated)
  | none => false
-- with the observation graph only there is no derivation
#guard match parsed? with
  | some ds => ((rdfsExplainStage [] [] obsOnly).run (ds, affiliated) matches .error _)
  | none => false

/-! ## 4. Blank nodes -/

private def exPerson : WfIri := iri! "http://example.org/Person"
private def exEmployee : WfIri := iri! "http://example.org/Employee"
private def bnodeDs : Dataset :=
  { default := []
    named := [ { name := gObs, graph := [{ s := .iri exEmployee, p := rdfsSubClassOf, o := .bnode "c" }] },
               { name := gSchema, graph := [{ s := .bnode "c", p := rdfsSubClassOf, o := .iri exPerson }] } ] }
private def personTriple : Triple := { s := .iri exEmployee, p := rdfsSubClassOf, o := .iri exPerson }

/- FINDING: `DerivesFull.rdfs9` takes the class `xxx` as an IRI, so
`ex:alice rdf:type _:c . _:c rdfs:subClassOf ex:Person .` does not give
`ex:alice rdf:type ex:Person`. RDF 1.1 Semantics 9.2 rdfs9 has no such
restriction. This test therefore joins on `_:c` with rdfs11. -/
private def rdfs9BnodeDs : Dataset :=
  { default := []
    named := [ { name := gObs, graph := [{ s := .iri exAlice, p := rdfType, o := .bnode "c" }] },
               { name := gSchema, graph := [{ s := .bnode "c", p := rdfsSubClassOf, o := .iri exPerson }] } ] }
#guard !(fullClosure [] [] (rdfs9BnodeDs.select { named := [gObs, gSchema] })).contains
  { s := .iri exAlice, p := rdfType, o := .iri exPerson }
private def schemaBnodeTriple : Triple := { s := .bnode "c", p := rdfsSubClassOf, o := .iri exPerson }
private def twoGraphs : GraphSelection := { named := [gObs, gSchema] }

private def bnodeBundle? : Option Bundle :=
  okVal? ((rdfsExplainStage [] [] twoGraphs).run (bnodeDs, personTriple))

#guard match bnodeBundle? with
  | some b => (checkBundle b).foundationalOnly && (sourceDigests b).length == 2
  | none => false
#guard (bnodeBundle?.map (chainOf · personTriple)) == some [.rdfs11, .base]

/-- Read one `base` triple from a second artifact `G2` with the same body. -/
private def moveBase (b : Bundle) (u : Triple) : Bundle :=
  let g := ((b.artifacts.toList.find? (·.id == "G")).bind (·.body)).getD []
  { b with
    artifacts := b.artifacts.push { id := "G2", kind := .graph, digest := graphDigest g, body := some g }
    steps := b.steps.map (fun st => match st.justification, st.conclusion with
      | .rule .base _ aa, .rdfDerivable _ _ v =>
          if v == u then { st with justification := .rule .base "G2" aa } else st
      | _, _ => st) }

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

-- the two artifacts are two scopes: the join on _:c is refused (PR 33 rule)
#guard match bnodeBundle? with
  | some b => let r := checkBundle (moveBase b schemaBnodeTriple)
      !r.valid && contains (r.rejection.getD "") "different scopes"
  | none => false

-- a target with a blank node: the conclusion keeps the raw label
private def bnodeObs : Dataset :=
  { default := []
    named := [ { name := gObs, graph := [{ s := .bnode "b", p := exWorksFor, o := .iri exOrg }] },
               { name := gSchema, graph := schemaGraph } ] }
private def bnodeAffiliated : Triple := { s := .bnode "b", p := exAffiliated, o := .iri exOrg }

#guard match okVal? ((rdfsExplainCheckStage [] [] noCmps twoGraphs).run (bnodeObs, bnodeAffiliated)) with
  | some (.rdfDerivable _ _ v) => v == bnodeAffiliated
  | _ => false

/-! ## 5. RDFC-1.0 -/

private def relabelled : Dataset :=
  { default := [{ s := .bnode "zz", p := rdfType, o := .iri exPerson },
                { s := .bnode "zz", p := exWorksFor, o := .iri exOrg }], named := [] }
private def labelled : Dataset :=
  { default := [{ s := .bnode "a1", p := exWorksFor, o := .iri exOrg },
                { s := .bnode "a1", p := rdfType, o := .iri exPerson }], named := [] }

#guard match okVal? (rdfcStage.run relabelled), okVal? (rdfcStage.run labelled) with
  | some r1, some r2 => r1 == r2 && r1.2.length == 64
  | _, _ => false

/-! ## 6. VC verify refuses a proofValue that is not multibase-z -/

#guard ((VC.DataIntegrity.verifyProofValue (fun _ _ _ => true) .sha256 ByteArray.empty
  Dataset.empty Dataset.empty "not-multibase") == false)
#guard ((vcVerifyStage (fun _ _ _ => true) .sha256).run
  ⟨ByteArray.empty, Dataset.empty, Dataset.empty, "not-multibase"⟩) matches .ok false

end L4Factoidal.Dataflow.PhaseETests
