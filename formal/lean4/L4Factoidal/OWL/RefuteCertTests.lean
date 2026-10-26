/-
L4Factoidal.OWL.RefuteCertTests — the certificate path end to end on small
graphs: the refuter refutes, `readOntology` reads, `emitCert` emits, and
`checkCert` accepts (or does not).

Every positive case has a negative twin: the same graph with the axiom the
certificate needs removed or made unreadable. A reader that invented
axioms, or a checker that accepted every certificate, fails a negative
guard.

The last guard is an EXPECTED FAILURE: a refutation the checker cannot
certify yet (https://github.com/danbri/factoidal/issues/764). It asserts
the current state, so the build fails when the refutation becomes
certified; then this guard and the issue are updated together.
-/
import L4Factoidal.OWL.RefuteCert

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

private def exC : WfIri := ⟨"http://e/C", rfl⟩
private def exD : WfIri := ⟨"http://e/D", rfl⟩
private def exE : WfIri := ⟨"http://e/E", rfl⟩
private def exP : WfIri := ⟨"http://e/P", rfl⟩
private def exDP : WfIri := ⟨"http://e/dp", rfl⟩
private def exI : WfIri := ⟨"http://e/i", rfl⟩
private def exY : WfIri := ⟨"http://e/y", rfl⟩

private def fuel : Nat := 40

private def proved (g : Graph) : Bool := (certify g fuel).isProved

private def refuted (g : Graph) : Bool := refute g fuel == some false

private def nnInt (v : String) : Term :=
  .literal ⟨{ lexicalForm := v,
              datatype := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩,
              langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff]⟩

private def intLit (v : String) : Term :=
  .literal ⟨{ lexicalForm := v,
              datatype := ⟨"http://www.w3.org/2001/XMLSchema#integer", rfl⟩,
              langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff]⟩

/-! ## `DisjointClasses` (Table 5) -/

private def gDisjoint : Graph :=
  [ ⟨.iri exI, rdfType, .iri exC⟩, ⟨.iri exI, rdfType, .iri exD⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩ ]

#guard refuted gDisjoint
#guard proved gDisjoint

/-- A consistent graph: no refutation, so no certificate. -/
private def gConsistent : Graph :=
  [ ⟨.iri exI, rdfType, .iri exC⟩, ⟨.iri exC, rdfsSubClassOf, .iri exD⟩ ]

#guard !refuted gConsistent
#guard (match certify gConsistent fuel with
        | .notRefuted => true
        | _ => false)
-- A bare `close` on its ontology does not check.
#guard !checkCert (readOntology gConsistent) .close

/-! ## A fresh witness: `i : ∃p.E ⊓ ∀p.¬E` -/

private def witnessGraph (declare : Bool) : Graph :=
  (if declare then [⟨.iri exP, rdfType, .iri owlObjectProperty⟩] else []) ++
  [ ⟨.iri exI, rdfType, .bnode "r1"⟩, ⟨.bnode "r1", rdfType, .iri owlRestriction⟩,
    ⟨.bnode "r1", owlOnProperty, .iri exP⟩, ⟨.bnode "r1", owlSomeValuesFrom, .iri exE⟩,
    ⟨.iri exI, rdfType, .bnode "r2"⟩, ⟨.bnode "r2", rdfType, .iri owlRestriction⟩,
    ⟨.bnode "r2", owlOnProperty, .iri exP⟩, ⟨.bnode "r2", owlAllValuesFrom, .bnode "c"⟩,
    ⟨.bnode "c", owlComplementOf, .iri exE⟩ ]

#guard refuted (witnessGraph true)
#guard proved (witnessGraph true)
-- `p` is not declared an object property: the refuter still refutes,
-- the reader leaves both restrictions out, and nothing is certified.
#guard refuted (witnessGraph false)
#guard !proved (witnessGraph false)

/-! ## Data cardinality restrictions as class names: `≥ 1 dp` and `≤ 0 dp` -/

private def dataCardGraph (lower : Nat) : Graph :=
  [ ⟨.iri exDP, rdfType, .iri owlDatatypeProperty⟩,
    ⟨.iri exI, rdfType, .bnode "m1"⟩, ⟨.bnode "m1", rdfType, .iri owlRestriction⟩,
    ⟨.bnode "m1", owlOnProperty, .iri exDP⟩, ⟨.bnode "m1", owlMinCardinality, nnInt (toString lower)⟩,
    ⟨.iri exI, rdfType, .bnode "m0"⟩, ⟨.bnode "m0", rdfType, .iri owlRestriction⟩,
    ⟨.bnode "m0", owlOnProperty, .iri exDP⟩, ⟨.bnode "m0", owlMaxCardinality, nnInt "0"⟩ ]

#guard refuted (dataCardGraph 1)
#guard proved (dataCardGraph 1)
-- `≥ 0 dp` beside `≤ 0 dp` has a model.
#guard !refuted (dataCardGraph 0)
#guard !checkCert (readOntology (dataCardGraph 0)) .close

/-! ## A nominal read as a class name: `x : ≤ 0 p.{y}` with `x p y`

The shape `OWL/NegationGoals.lean` writes for a negated property
assertion. -/

private def nominalGraph (edge : Bool) : Graph :=
  [ ⟨.iri exP, rdfType, .iri owlObjectProperty⟩,
    ⟨.iri exI, rdfType, .bnode "q"⟩, ⟨.bnode "q", rdfType, .iri owlRestriction⟩,
    ⟨.bnode "q", owlOnProperty, .iri exP⟩, ⟨.bnode "q", owlMaxQualifiedCardinality, nnInt "0"⟩,
    ⟨.bnode "q", owlOnClass, .bnode "o"⟩, ⟨.bnode "o", owlOneOf, .bnode "l"⟩,
    ⟨.bnode "l", rdfFirst, .iri exY⟩, ⟨.bnode "l", rdfRest, .iri rdfNil⟩,
    ⟨.iri exY, rdfType, .bnode "o"⟩ ] ++
  (if edge then [⟨.iri exI, exP, .iri exY⟩] else [])

#guard refuted (nominalGraph true)
#guard proved (nominalGraph true)
#guard !refuted (nominalGraph false)

/-! ## A declared datatype is never read as a class name

`i : D` beside `i : ¬D`. With `D` a class the graph is refuted and
certified; with `D` typed `rdfs:Datatype` the reader leaves both
memberships out (a datatype is no class of the object domain), so the
refutation, if the refuter finds one, is not certified. -/

private def exDT : WfIri := ⟨"http://e/DT", rfl⟩

private def complementGraph (datatype : Bool) : Graph :=
  (if datatype then [⟨.iri exDT, rdfType, .iri rdfsDatatype⟩] else []) ++
  [ ⟨.iri exI, rdfType, .iri exDT⟩, ⟨.iri exI, rdfType, .bnode "n"⟩,
    ⟨.bnode "n", owlComplementOf, .iri exDT⟩ ]

#guard refuted (complementGraph false)
#guard proved (complementGraph false)
#guard !proved (complementGraph true)

/-! ## EXPECTED FAILURE (https://github.com/danbri/factoidal/issues/764)

A functional data property with two different integer values. The refuter
refutes it by literal values (`clashForLabel`, `≤ 1` against provably
distinct successors); the checker has no data domain, so it cannot
certify the refutation. When it can, this guard fails the build: replace
it with `#guard proved gFunctionalData` and update the issue. -/

private def gFunctionalData : Graph :=
  [ ⟨.iri exDP, rdfType, .iri owlDatatypeProperty⟩,
    ⟨.iri exDP, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exI, exDP, intLit "1"⟩, ⟨.iri exI, exDP, intLit "2"⟩ ]

#guard refuted gFunctionalData
#guard !proved gFunctionalData

end L4Factoidal.OWL.Refute
