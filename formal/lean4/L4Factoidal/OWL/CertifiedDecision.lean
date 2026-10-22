/-
Proof-bearing decisions for the existing DirectCert ontology fragment.

The semantic predicate below is exactly the model existential negated by
DirectCert.checkCert_sound. Its scope is the existing Concept/DlOntology
fragment and DirectModel definitions, not a new transcription of all OWL.

This module does not prove the RDF reader or preprocessing correct. The
source-lifting theorems require the relevant model-preservation direction
as an explicit argument; they do not discharge O1/O2. No public producer
or wire adapter is changed to call this boundary by adding this module.
-/
import L4Factoidal.OWL.DirectCert

namespace L4Factoidal.OWL.CertifiedDecision

/-- The exact model notion used by `DirectCert.checkCert_sound`. -/
def HasModel (ontology : DlOntology) : Prop :=
  ∃ (δ : Type) (interpretation : Interp δ) (assignment : Ind → δ),
    DirectModel interpretation assignment ontology

/-- Every certificate is rejected for an ontology with a model, not just
the sample certificates exercised by the executable controls. -/
theorem checkCert_rejects_model {ontology : DlOntology}
    (model : HasModel ontology) (certificate : Cert) :
    checkCert ontology certificate = false := by
  cases checked : checkCert ontology certificate with
  | false => rfl
  | true => exact False.elim (checkCert_sound checked model)

inductive UnknownReason where
  | certificateRejected
  | budgetExhausted
  | unsupported
  deriving Repr, DecidableEq

/-- Definitive verdicts carry evidence about this specific fragment ontology. -/
inductive CertifiedVerdict (ontology : DlOntology) where
  | consistent (model : HasModel ontology)
  | inconsistent (noModel : ¬ HasModel ontology)
  | unknown (reason : UnknownReason)

structure WireVerdict where
  consistent : Option Bool
  reason : Option UnknownReason
  deriving Repr, DecidableEq

def erase {ontology : DlOntology} : CertifiedVerdict ontology → WireVerdict
  | .consistent _ => ⟨some true, none⟩
  | .inconsistent _ => ⟨some false, none⟩
  | .unknown reason => ⟨none, some reason⟩

def Meaning (ontology : DlOntology) : Option Bool → Prop
  | some true => HasModel ontology
  | some false => ¬ HasModel ontology
  | none => True

/-- Proof erasure preserves the meaning of a fragment verdict. -/
theorem erase_sound {ontology : DlOntology} (verdict : CertifiedVerdict ontology) :
    Meaning ontology (erase verdict).consistent := by
  cases verdict with
  | consistent model => exact model
  | inconsistent noModel => exact noModel
  | unknown _ => exact True.intro

theorem no_contradictory_booleans {ontology : DlOntology}
    (left right : CertifiedVerdict ontology)
    (positive : (erase left).consistent = some true)
    (negative : (erase right).consistent = some false) : False := by
  have model := erase_sound left
  have noModel := erase_sound right
  rw [positive] at model
  rw [negative] at noModel
  exact noModel model

/-- Total certificate validation. Rejected refutations assert neither Boolean. -/
def checkedRefutation (ontology : DlOntology) (certificate : Cert) :
    CertifiedVerdict ontology :=
  if accepted : checkCert ontology certificate = true then
    .inconsistent (checkCert_sound accepted)
  else
    .unknown .certificateRejected

/-- This producer's erased output is sound for the exact ontology it checks. -/
theorem checkedRefutation_sound (ontology : DlOntology) (certificate : Cert) :
    Meaning ontology (erase (checkedRefutation ontology certificate)).consistent :=
  erase_sound (checkedRefutation ontology certificate)

theorem checkedRefutation_ne_consistent (ontology : DlOntology) (certificate : Cert) :
    (erase (checkedRefutation ontology certificate)).consistent ≠ some true := by
  unfold checkedRefutation
  split <;> intro impossible <;> cases impossible

theorem checkedRefutation_rejected {ontology : DlOntology} {certificate : Cert}
    (rejected : checkCert ontology certificate = false) :
    erase (checkedRefutation ontology certificate) = ⟨none, some .certificateRejected⟩ := by
  simp [checkedRefutation, rejected, erase]

/-
Conditional composition with a source language. SatSource must be supplied
from that language's reviewed semantics. These implications do not assert
that any current RDF reader or closure satisfies them. Refutation needs
source-model preservation; a model verdict needs the reverse direction.
-/

theorem lift_no_model {Source : Sort u} (SatSource : Source → Prop)
    (lower : Source → DlOntology)
    (preservesModels : ∀ source, SatSource source → HasModel (lower source))
    (source : Source) (noTargetModel : ¬ HasModel (lower source)) :
    ¬ SatSource source :=
  fun sourceModel => noTargetModel (preservesModels source sourceModel)

theorem lift_model {Source : Sort u} (SatSource : Source → Prop)
    (lower : Source → DlOntology)
    (liftsModels : ∀ source, HasModel (lower source) → SatSource source)
    (source : Source) (targetModel : HasModel (lower source)) :
    SatSource source :=
  liftsModels source targetModel

/-- Lifts this actual checker producer only when its source-model bridge is supplied. -/
theorem checkedRefutation_source_sound {Source : Sort u} (SatSource : Source → Prop)
    (lower : Source → DlOntology)
    (preservesModels : ∀ source, SatSource source → HasModel (lower source))
    (source : Source) (certificate : Cert)
    (reported : (erase (checkedRefutation (lower source) certificate)).consistent = some false) :
    ¬ SatSource source := by
  have noTargetModel := checkedRefutation_sound (lower source) certificate
  rw [reported] at noTargetModel
  exact lift_no_model SatSource lower preservesModels source noTargetModel

/-- A fragment model verdict requires a separate reverse model-lifting bridge. -/
theorem consistent_source_sound {Source : Sort u} (SatSource : Source → Prop)
    (lower : Source → DlOntology)
    (liftsModels : ∀ source, HasModel (lower source) → SatSource source)
    (source : Source) (verdict : CertifiedVerdict (lower source))
    (reported : (erase verdict).consistent = some true) : SatSource source := by
  have targetModel := erase_sound verdict
  rw [reported] at targetModel
  exact lift_model SatSource lower liftsModels source targetModel

namespace Controls

def emptyOntology : DlOntology := {}

/-- An actual Unit-domain model in DirectCert's own definitions. -/
theorem empty_has_model : HasModel emptyOntology := by
  refine ⟨Unit, ⟨fun _ _ => False, fun _ _ _ => False⟩, fun _ => (), ?_, ?_, ?_, ?_, ?_⟩
  · exact respects_empty _
  · intro _ absent; cases absent
  · intro _ absent; cases absent
  · intro _ absent; cases absent
  · intro _ absent; cases absent

def sameDifferentOntology : DlOntology := {
  same := [("a", "b")]
  abox := [.diff "a" "b"]
}

/-- A contradiction derived directly from SameIndividual and DifferentIndividuals. -/
theorem same_different_no_model : ¬ HasModel sameDifferentOntology := by
  intro ⟨_, _, assignment, _, _, _, same, assertions⟩
  have equal : assignment "a" = assignment "b" := same ("a", "b") (List.Mem.head [])
  have distinct : assignment "a" ≠ assignment "b" :=
    assertions (.diff "a" "b") (List.Mem.head [])
  exact distinct equal

-- Checker acceptance, rejection, and erasure use the actual fragment code.
#guard checkCert sameDifferentOntology .close
#guard !checkCert emptyOntology .close
#guard (erase (checkedRefutation sameDifferentOntology .close)).consistent = some false
#guard erase (checkedRefutation emptyOntology .close) = ⟨none, some .certificateRejected⟩
#guard erase (CertifiedVerdict.consistent empty_has_model) = ⟨some true, none⟩
#guard erase (CertifiedVerdict.inconsistent same_different_no_model) = ⟨some false, none⟩

#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict emptyOntology from .inconsistent)
#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict emptyOntology from .inconsistent (fun _ => True.intro))
#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict emptyOntology from
  (CertifiedVerdict.inconsistent same_different_no_model))

end Controls

#print axioms erase_sound
#print axioms checkCert_rejects_model
#print axioms no_contradictory_booleans
#print axioms checkedRefutation
#print axioms checkedRefutation_source_sound
#print axioms consistent_source_sound
#print axioms Controls.empty_has_model
#print axioms Controls.same_different_no_model

end L4Factoidal.OWL.CertifiedDecision
