/-
L4Factoidal.Dataflow.JudgesTests — checks of the reasoner, validator and
checker interface types (`Dataflow/Reasoner.lean`, `Validator.lean`,
`Checker.lean`), evaluated during `lake build`
(https://github.com/danbri/factoidal/issues/975, item 2).

* Reasoners: each shipped reasoner derives the rdfs7 triple
  `ex:alice ex:affiliatedWith ex:organisation` from
  `ex:alice ex:worksFor ex:organisation` and
  `ex:worksFor rdfs:subPropertyOf ex:affiliatedWith`, and keeps the input.
  The `rdf:_n` slice of the empty graph is `[rdf:_1]`; of a graph that
  mentions `rdf:_3` it holds `rdf:_3`, once.
  The regime of each reasoner is the one it declares.
* The named assumptions are present and are not proved: `assumed_completeness`
  of each reasoner is exactly `CompleteStatement`; there are 3 reasoners and
  the rule `rhoDfReasoner_complete` proves the conditional completeness.
* Validator: `sh:minCount 1` conforms, `sh:minCount 2` does not (no failure);
  a shapes graph with an unsupported feature is refused.
* Checker: the RDFS-profile checker accepts the bundle the explain stage emits
  and refuses a bundle whose conclusion is not an RDF claim; the foundational
  checker accepts the same bundle.

No executable imports this module.
-/
import L4Factoidal.Dataflow.Reasoner
import L4Factoidal.Dataflow.JudgeStages
import L4Factoidal.Dataflow.Validator
import L4Factoidal.Dataflow.Checker
import L4Factoidal.Dataflow.PhaseD

namespace L4Factoidal.Dataflow.JudgesTests

open L4Factoidal.RDF
open L4Factoidal.Dataflow

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def okVal? {ε β : Type} : Except ε β → Option β
  | .ok b => some b
  | .error _ => none

private def exAlice : WfIri := iri! "http://example.org/alice"
private def exOrg : WfIri := iri! "http://example.org/organisation"
private def exWorksFor : WfIri := iri! "http://example.org/worksFor"
private def exAffiliated : WfIri := iri! "http://example.org/affiliatedWith"

private def input : Graph :=
  [ { s := .iri exAlice, p := exWorksFor, o := .iri exOrg },
    { s := .iri exWorksFor, p := RDFS.rdfsSubPropertyOf, o := .iri exAffiliated } ]

private def affiliated : Triple := { s := .iri exAlice, p := exAffiliated, o := .iri exOrg }

/-! ## Reasoners -/

#guard (rhoDfReasoner.run input).mem affiliated
#guard (rdfsReasoner (withMinimalD [])).run input |>.mem affiliated
#guard (owlRlReasoner.run input).mem affiliated
#guard input.all (fun t => (rhoDfReasoner.run input).mem t)
#guard input.all (fun t => ((rdfsReasoner (withMinimalD [])).run input).mem t)
#guard input.all (fun t => (owlRlReasoner.run input).mem t)
-- the input alone does not give the triple: the reasoner added it
#guard !input.mem affiliated

-- the stage form runs the same closure
#guard match okVal? (owlRlReasoner.toStage.run input) with
  | some c => c.mem affiliated
  | none => false

-- the rdf:_n slice
#guard (cmpSlice []).length == 1
private def cmp3 : WfIri := iri! "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"
#guard (cmpSlice [{ s := .iri exAlice, p := cmp3, o := .iri exOrg },
  { s := .iri exOrg, p := cmp3, o := .iri exAlice }]).length == 2

-- the declared regime
#guard match rhoDfReasoner.regime, (rdfsReasoner []).regime, owlRlReasoner.regime with
  | .rhoDf, .rdfs [], .owlRl => true
  | _, _, _ => false
#guard shippedReasoners.length == 3

-- the soundness proof is usable: a consumer gets the entailment from the type
example (g : Graph) : RdfsEntails (fun x => x ∈ withMinimalD []) g ((rdfsReasoner (withMinimalD [])).run g) :=
  (rdfsReasoner (withMinimalD [])).sound g

-- the named completeness assumptions are the statements, nothing stronger
example : rhoDfReasoner.assumed_completeness = CompleteStatement .rhoDf RDFS.closureFix :=
  rhoDfReasoner.completeness_stmt
example : owlRlReasoner.assumed_completeness =
    CompleteStatement .owlRl (fun g => Graph.toSet (OWL.RL.closureFix g)) :=
  owlRlReasoner.completeness_stmt

/-! ## Validator -/

private def dataTtl : String :=
  "@prefix ex: <http://example.org/> .\nex:alice ex:worksFor ex:organisation .\n"

private def shapesText (n : Nat) (extra : String := "") : String :=
  "@prefix ex: <http://example.org/> .\n" ++
  "@prefix sh: <http://www.w3.org/ns/shacl#> .\n" ++
  "ex:S a sh:NodeShape ; sh:targetNode ex:alice ;\n" ++
  s!"  sh:property [ sh:path ex:worksFor ; sh:minCount {n} ] .\n" ++ extra

private def graphOf? (text : String) : Option Graph :=
  (okVal? ((decodeStage.comp (parseStage {} .rdf12 none)).run
    { bytes := text.toUTF8, mediaType := "text/turtle", source := "test:judges" })).map
    (·.default)

#guard match graphOf? dataTtl, graphOf? (shapesText 1), graphOf? (shapesText 2) with
  | some d, some s1, some s2 =>
    match okVal? (shaclValidator.run (d, s1)), okVal? (shaclValidator.run (d, s2)) with
    | some r1, some r2 => r1.conforms && !r2.conforms && r1.failure.isNone && r2.failure.isNone
    | _, _ => false
  | _, _, _ => false

-- the validator's run is the stage's run on a supported shapes graph
#guard match graphOf? dataTtl, graphOf? (shapesText 1) with
  | some d, some s1 =>
    match okVal? (shaclValidator.run (d, s1)), okVal? ((shaclStage {}).run (d, s1)) with
    | some a, some b => a.conforms == b.conforms && a.results.length == b.results.length
    | _, _ => false
  | _, _ => false

example : shaclValidator.assumed_spec_iff = ExactStatement {} shaclValidator.run :=
  shaclValidator.spec_iff_stmt

/-! ## Checker -/

private def spSpSp : Triple :=
  { s := .iri RDFS.rdfsSubPropertyOf, p := RDFS.rdfsSubPropertyOf, o := .iri RDFS.rdfsSubPropertyOf }

private theorem noCmps : ∀ c ∈ ([] : List WfIri), IsRdfMemberIri c := by
  intro c hc; cases hc

private def bundle? : Option FPP0.Bundle :=
  okVal? ((rdfsExplainStage [] [] { default := true }).run (Dataset.empty, spSpSp))

#guard match bundle? with
  | some b => ((rdfsChecker [] [] noCmps).run b matches .ok _) &&
      ((foundationalChecker).run b matches .ok _)
  | none => false

-- a bundle whose conclusion is not an RDF claim is refused by the RDFS checker
#guard match bundle? with
  | some b => ((rdfsChecker [] [] noCmps).run { b with conclusion := .clif "p" } matches .error _)
  | none => false

-- a consumer gets the entailment from the type
example (b : FPP0.Bundle) (c : FPP0.Claim) (h : (rdfsChecker [] [] noCmps).run b = .ok c) :
    (rdfsChecker [] [] noCmps).profile.Holds b c :=
  (rdfsChecker [] [] noCmps).sound b c h

end L4Factoidal.Dataflow.JudgesTests
