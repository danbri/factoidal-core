/-
Independent source-model witnesses for the two original RDF boundary probes.
These prove SourceModel on the original Graph values, before any reader or
compiler call. They do not infer consistency from failed certificate search.
-/
import L4Factoidal.OWL.AtomicDirect
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

namespace AtomicDirectModels

open L4Factoidal.RDF L4Factoidal.OWL L4Factoidal.OWL.AtomicDirect

def emptyInterpretation : Interp Unit := ⟨fun _ _ => False, fun _ _ _ => False⟩
def unitAssignment : Ind → Unit := fun _ => ()
def property : WfIri := ⟨"urn:p", rfl⟩
def individual : WfIri := ⟨"urn:a", rfl⟩
def collisionClass : WfIri := ⟨"urn:factoidal:owl-cert:one-of:urn:a", rfl⟩
def note : WfLiteral := ⟨{
  lexicalForm := "note"
  datatype := ⟨"http://www.w3.org/2001/XMLSchema#string", rfl⟩
  langTag := none
  direction := none
}, rfl⟩

def annotationGraph : Graph := [
  ⟨.iri property, rdfType, .iri owlAnnotationProperty⟩,
  ⟨.iri property, domain, .iri owlNothing⟩,
  ⟨.iri individual, property, .literal note⟩
]

def collisionGraph : Graph := [
  ⟨.iri collisionClass, rdfType, .iri owlClass⟩,
  ⟨.iri collisionClass, subClassOf, .iri owlNothing⟩
]

theorem mapsClass_shape {name : WfIri} {className : AtomicClass}
    (mapped : MapsClass name className) :
    (name = owlThing ∧ className = .thing) ∨
    (name = owlNothing ∧ className = .nothing) ∨
    (reserved name = false ∧ className = .named name.val) := by
  cases mapped with
  | thing => exact Or.inl ⟨rfl, rfl⟩
  | nothing => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | named _ ordinary => exact Or.inr (Or.inr ⟨ordinary, rfl⟩)

theorem nonclass_reserved {name : WfIri} {className : AtomicClass}
    (logical : reserved name = true) (notThing : name ≠ owlThing) (notNothing : name ≠ owlNothing)
    (mapped : MapsClass name className) : False := by
  rcases mapsClass_shape mapped with ⟨equal, _⟩ | ⟨equal, _⟩ | ⟨ordinary, _⟩
  · exact notThing equal
  · exact notNothing equal
  · rw [logical] at ordinary; cases ordinary

theorem reserved_of_owl_prefix {name : WfIri}
    (starts : "http://www.w3.org/2002/07/owl#".toList <+: name.val.toList) :
    reserved name = true := by
  have first : name.val.startsWith "http://www.w3.org/2002/07/owl#" = true :=
    String.startsWith_string_iff.mpr starts
  simp [reserved, first]

theorem empty_class_of_ordinary {name : WfIri} {className : AtomicClass}
    (ordinary : reserved name = false) (mapped : MapsClass name className) (element : Unit) :
    ¬ classHolds emptyInterpretation className element := by
  cases mapped with
  | thing =>
      have logical : reserved owlThing = true := reserved_of_owl_prefix (by unfold owlThing; decide)
      rw [logical] at ordinary; cases ordinary
  | nothing =>
      have logical : reserved owlNothing = true := reserved_of_owl_prefix (by unfold owlNothing; decide)
      rw [logical] at ordinary; cases ordinary
  | named _ _ => exact fun impossible => impossible

theorem annotation_source_model : SourceModel emptyInterpretation unitAssignment annotationGraph := by
  have typeDomain : rdfType ≠ domain := by unfold rdfType domain; decide
  have subType : subClassOf ≠ rdfType := by unfold subClassOf rdfType; decide
  have subDomain : subClassOf ≠ domain := by unfold subClassOf domain; decide
  have diffType : differentFrom ≠ rdfType := by unfold differentFrom rdfType; decide
  have diffDomain : differentFrom ≠ domain := by unfold differentFrom domain; decide
  intro triple member clause mapped
  cases mapped <;> simp_all [annotationGraph, axiomHolds]
  exact False.elim (nonclass_reserved
    (reserved_of_owl_prefix (by unfold owlAnnotationProperty; decide))
    (by unfold owlAnnotationProperty owlThing; decide)
    (by unfold owlAnnotationProperty owlNothing; decide) ‹MapsClass owlAnnotationProperty _›)

theorem collision_source_model : SourceModel emptyInterpretation unitAssignment collisionGraph := by
  have typeSub : rdfType ≠ subClassOf := by unfold rdfType subClassOf; decide
  have subType : subClassOf ≠ rdfType := by unfold subClassOf rdfType; decide
  have diffType : differentFrom ≠ rdfType := by unfold differentFrom rdfType; decide
  have diffSub : differentFrom ≠ subClassOf := by unfold differentFrom subClassOf; decide
  intro triple member clause mapped
  cases mapped <;> simp_all [collisionGraph, axiomHolds]
  · intro element impossible
    exact False.elim (empty_class_of_ordinary
      (by
        unfold reserved collisionClass
        simp only [Bool.or_eq_false_iff, String.startsWith_string_eq_false_iff]
        decide)
      ‹MapsClass collisionClass _› element impossible)
  · exact False.elim (nonclass_reserved
      (reserved_of_owl_prefix (by unfold owlClass; decide))
      (by unfold owlClass owlThing; decide)
      (by unfold owlClass owlNothing; decide) ‹MapsClass owlClass _›)

theorem annotation_satisfiable : Satisfiable annotationGraph :=
  ⟨Unit, emptyInterpretation, unitAssignment, annotation_source_model⟩

theorem collision_satisfiable : Satisfiable collisionGraph :=
  ⟨Unit, emptyInterpretation, unitAssignment, collision_source_model⟩

theorem model_prevents_false {graph : Graph} (model : Satisfiable graph) (certificate : Cert) :
    (decide graph certificate).consistent ≠ some false := by
  intro reported
  have meaningful := decide_sound graph certificate
  rw [reported] at meaningful
  exact meaningful.2 model

theorem annotation_ne_inconsistent (certificate : Cert) :
    (decide annotationGraph certificate).consistent ≠ some false :=
  model_prevents_false annotation_satisfiable certificate

theorem collision_ne_inconsistent (certificate : Cert) :
    (decide collisionGraph certificate).consistent ≠ some false :=
  model_prevents_false collision_satisfiable certificate

def equivalentClass : WfIri := ⟨"http://www.w3.org/2002/07/owl#equivalentClass", rfl⟩

/-- Contradictory in full OWL; outside this atomic mapping language. -/
def unsupportedGraph : Graph := [
  ⟨.iri collisionClass, equivalentClass, .iri owlThing⟩,
  ⟨.iri collisionClass, equivalentClass, .iri owlNothing⟩
]

/-- Limited source semantics alone cannot justify verdicts on unsupported syntax. -/
theorem unsupported_source_model : SourceModel emptyInterpretation unitAssignment unsupportedGraph := by
  have typeOther : rdfType ≠ equivalentClass := by unfold rdfType equivalentClass; decide
  have subOther : subClassOf ≠ equivalentClass := by unfold subClassOf equivalentClass; decide
  have diffOther : differentFrom ≠ equivalentClass := by unfold differentFrom equivalentClass; decide
  intro triple member clause mapped
  cases mapped <;> simp_all [unsupportedGraph, axiomHolds]

theorem unsupported_satisfiable_in_limited_semantics : Satisfiable unsupportedGraph :=
  ⟨Unit, emptyInterpretation, unitAssignment, unsupported_source_model⟩

/-- `decide +kernel`: since 2026-10-24 the reader looks up annotation
properties in a hash map and tests `reserved` (String.startsWith), which the
elaborator's `decide` does not reduce; the kernel does. -/
theorem unsupported_read_none : readOntology unsupportedGraph = none := by
  decide +kernel

theorem unsupported_not_admitted : ¬ Accepted unsupportedGraph := by
  intro ⟨ontology, reading⟩
  rw [unsupported_read_none] at reading
  cases reading

theorem unsupported_no_definitive (verdict : CertifiedVerdict unsupportedGraph) (answer : Bool) :
    (erase verdict).consistent ≠ some answer := by
  intro reported
  exact unsupported_not_admitted (definitive_admitted verdict answer reported)

#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict unsupportedGraph from
  .consistent unsupported_satisfiable_in_limited_semantics)

#guard (readOntology annotationGraph).isSome
#guard (readOntology collisionGraph).isSome
#guard (readOntology unsupportedGraph).isNone
#guard decide annotationGraph .close = ⟨none, some .certificateRejected⟩
#guard decide collisionGraph .close = ⟨none, some .certificateRejected⟩
#guard decide unsupportedGraph .close = ⟨none, some .unsupported⟩

#print axioms annotation_source_model
#print axioms collision_source_model
#print axioms annotation_ne_inconsistent
#print axioms collision_ne_inconsistent
#print axioms unsupported_source_model
#print axioms unsupported_read_none
#print axioms unsupported_not_admitted
#print axioms unsupported_no_definitive

end AtomicDirectModels
