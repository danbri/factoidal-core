/-
Finite semantic QA examples, 2026-10-21, against the actual OWL reader,
preprocessing and certificate checker. This is an acceptance gate: both
labelled model-preservation guards MUST reject a certificate for a
contradiction. They intentionally fail on the audited implementation.

The intended DlOntology values are specified independently of readOntology.
Their correspondence to the RDF inputs is a manual W3C mapping judgment
that still needs independent review; the model proofs do not formalize that
mapping. These examples are neither a universal preservation proof nor a
public API conformance claim. They do not establish behavior of an npm
artifact. No product implementation is replaced or patched here.

References:
https://www.w3.org/TR/owl2-direct-semantics/#Introduction
  Annotations have no semantic meaning in OWL 2 Direct Semantics.
https://www.w3.org/TR/owl2-direct-semantics/#Class_Expression_Axioms
  SubClassOf(C owl:Nothing) permits the interpretation of C to be empty.

Run from formal/lean4 with the existing library built:
  lake env lean ../../tests/assurance/OwlModelPreservation.lean
The original exploratory probe and log are retained under .claude-runs/.
-/
import L4Factoidal.OWL.RefuteCert
import L4Factoidal.OWL.CertifiedDecision
import L4Factoidal.Syntax.NQuadsFast
import Lean

namespace OwlModelPreservation

open L4Factoidal.RDF L4Factoidal.OWL L4Factoidal.OWL.RL
open L4Factoidal.Syntax

def annotationInput : String :=
  "<urn:p> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#AnnotationProperty> .\n" ++
  "<urn:p> <http://www.w3.org/2000/01/rdf-schema#domain> <http://www.w3.org/2002/07/owl#Nothing> .\n" ++
  "<urn:a> <urn:p> \"note\" .\n"

def collisionInput : String :=
  "<urn:factoidal:owl-cert:one-of:urn:a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .\n" ++
  "<urn:factoidal:owl-cert:one-of:urn:a> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://www.w3.org/2002/07/owl#Nothing> .\n"

-- An annotation declaration, its domain and its assertion add no logical
-- constraints to this Direct Semantics fragment.
def annotationIntended : DlOntology := {}

-- This ordinary class IRI has no nominal meaning. Its class is empty;
-- no individual is asserted to belong to it.
def collisionIntended : DlOntology :=
  { tbox := [(.atom "urn:factoidal:owl-cert:one-of:urn:a", .bot)] }

def emptyExtensions : Interp Unit :=
  ⟨fun _ _ => False, fun _ _ _ => False⟩

def unitNames : Ind → Unit := fun _ => ()

-- Unit is nonempty. Both proofs model the independently specified
-- ontology, not the output of the translator under test.
theorem annotationIntended_model :
    DirectModel emptyExtensions unitNames annotationIntended := by
  constructor
  · constructor <;> intro q hq <;> cases hq
  constructor
  · intro ax hax; cases hax
  constructor
  · intro q hq; cases hq
  constructor
  · intro q hq; cases hq
  · intro ax hax; cases hax

theorem collisionIntended_model :
    DirectModel emptyExtensions unitNames collisionIntended := by
  constructor
  · constructor <;> intro q hq <;> cases hq
  constructor
  · intro ax hax x hx
    simp only [collisionIntended, List.mem_singleton] at hax
    subst hax
    exact hx
  constructor
  · intro q hq; cases hq
  constructor
  · intro q hq; cases hq
  · intro ax hax; cases hax

-- Universal controls connect the real checker theorem to each independent
-- model. The actual RDF-reader checks below cannot use these without the
-- missing transformation proof: their ontology arguments are different.
theorem annotation_rejects_every_certificate (certificate : Cert) :
    checkCert annotationIntended certificate = false :=
  CertifiedDecision.checkCert_rejects_model
    ⟨Unit, emptyExtensions, unitNames, annotationIntended_model⟩ certificate

theorem collision_rejects_every_certificate (certificate : Cert) :
    checkCert collisionIntended certificate = false :=
  CertifiedDecision.checkCert_rejects_model
    ⟨Unit, emptyExtensions, unitNames, collisionIntended_model⟩ certificate

-- Executable controls: the checker rejects .close on each intended ontology.
#guard checkCert annotationIntended .close == false
#guard checkCert collisionIntended .close == false

-- Parsing controls are separate from the semantic acceptance conditions.
#guard (parseNQuadsFast annotationInput .rdf12).isOk
#guard (parseNQuadsFast annotationInput .rdf12).toOption.map
  (fun ds => ds.default.length) == some 3
#guard (parseNQuadsFast collisionInput .rdf12).isOk
#guard (parseNQuadsFast collisionInput .rdf12).toOption.map
  (fun ds => ds.default.length) == some 2

-- Preserve parse errors: no fallback empty graph can make the gate pass.
def actualClose (input : String) (preprocess : Graph → Graph) : Except ParseError Bool :=
  (parseNQuadsFast input .rdf12).map (fun ds =>
    checkCert (Refute.certOntology (preprocess ds.default)) .close)

-- Labels are named definitions so a failing #guard identifies its case.
def annotationAfterRlClosureRejects : Bool :=
  (actualClose annotationInput closureFix).toOption == some false

def namespaceCollisionRawRejects : Bool :=
  (actualClose collisionInput id).toOption == some false

-- A machine-readable inventory prevents a runner from treating no discovered
-- cases as success. A parse error remains null, never an invented false.
def reportCase (caseId : String) (observed : Except ParseError Bool) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", Lean.toJson caseId),
    ("expectedCheckCert", Lean.toJson false),
    ("actualCheckCert", match observed with
      | .ok accepted => Lean.toJson accepted
      | .error _ => .null)]

#eval IO.println ("OWL_MODEL_PRESERVATION_REPORT=" ++
  (Lean.Json.mkObj [("cases", .arr #[
    reportCase "annotation-domain" (actualClose annotationInput closureFix),
    reportCase "generated-name-collision" (actualClose collisionInput id)
  ])]).compress)

-- MODEL-PRESERVATION: annotation assertions must not acquire logical force.
#guard annotationAfterRlClosureRejects

-- MODEL-PRESERVATION: user class IRIs must not acquire generated members.
#guard namespaceCollisionRawRejects

#print axioms annotationIntended_model
#print axioms collisionIntended_model

end OwlModelPreservation
