import Lean

/-
Generic design exemplar, 2026-10-21. This file is outside the product build
and public execution path. It does not formalize W3C semantics or certify
Factoidal's engine. The two finite regimes below are test fixtures only.

The erasure theorem checks an interface: its constructors require semantic
evidence. Supplying an adequate standards model, proving a real certificate
checker sound, and connecting that checker to the shipped adapter are separate
obligations. None is discharged for the actual engine by this example.
-/

namespace CertifiedVerdictContract

universe u v c

/-- Inputs and interpretations can differ between semantic regimes. -/
structure Semantics (Regime : Type u) where
  Input : Regime → Type v
  Interpretation : Regime → Type v
  satisfies : (regime : Regime) → Input regime → Interpretation regime → Prop

def HasModel {Regime : Type u} (semantics : Semantics Regime)
    (regime : Regime) (input : semantics.Input regime) : Prop :=
  ∃ model, semantics.satisfies regime input model

inductive UnknownReason where
  | budgetExhausted
  | unsupported
  | noCandidate
  | rejectedCertificate
  deriving Repr, DecidableEq

/-- Both Boolean conclusions require evidence under the same indexed semantics. -/
inductive CertifiedVerdict {Regime : Type u} (semantics : Semantics Regime)
    (regime : Regime) (input : semantics.Input regime) where
  | consistent (evidence : HasModel semantics regime input)
  | inconsistent (evidence : ¬ HasModel semantics regime input)
  | unknown (reason : UnknownReason)

structure WireVerdict where
  consistent : Option Bool
  reason : Option UnknownReason
  deriving Repr, DecidableEq

/-- The public representation contains no proof terms. -/
def erase {Regime : Type u} {semantics : Semantics Regime} {regime : Regime}
    {input : semantics.Input regime} : CertifiedVerdict semantics regime input → WireVerdict
  | .consistent _ => ⟨some true, none⟩
  | .inconsistent _ => ⟨some false, none⟩
  | .unknown reason => ⟨none, some reason⟩

def Meaning {Regime : Type u} (semantics : Semantics Regime) (regime : Regime)
    (input : semantics.Input regime) : Option Bool → Prop
  | some true => HasModel semantics regime input
  | some false => ¬ HasModel semantics regime input
  | none => True

/-- Universal evidence-erasure safety for this interface, conditional on its semantics. -/
theorem erase_sound {Regime : Type u} {semantics : Semantics Regime} {regime : Regime}
    {input : semantics.Input regime} (verdict : CertifiedVerdict semantics regime input) :
    Meaning semantics regime input (erase verdict).consistent := by
  cases verdict with
  | consistent evidence => exact evidence
  | inconsistent evidence => exact evidence
  | unknown _ => exact True.intro

/-- Two evidence-bearing results for one input and regime cannot contradict each other. -/
theorem no_contradictory_booleans {Regime : Type u} {semantics : Semantics Regime}
    {regime : Regime} {input : semantics.Input regime}
    (left right : CertifiedVerdict semantics regime input)
    (positive : (erase left).consistent = some true)
    (negative : (erase right).consistent = some false) : False := by
  have model := erase_sound left
  have noModel := erase_sound right
  rw [positive] at model
  rw [negative] at noModel
  exact noModel model

/-- Certificate bytes have no semantic authority without the total sound checker. -/
structure CertificateChecker {Regime : Type u} (semantics : Semantics Regime) where
  Certificate : (regime : Regime) → semantics.Input regime → Type c
  check : (regime : Regime) → (input : semantics.Input regime) →
    Certificate regime input → Option Bool
  checker_sound : ∀ regime input certificate,
    Meaning semantics regime input (check regime input certificate)

inductive SearchResult (Certificate : Type c) where
  | proposed (certificate : Certificate)
  | stopped (reason : UnknownReason)

/-- Search supplies an untrusted proposal; only the checker can justify a Boolean. -/
def certify {Regime : Type u} {semantics : Semantics Regime}
    (checker : CertificateChecker semantics) (regime : Regime)
    (input : semantics.Input regime) :
    SearchResult (checker.Certificate regime input) → CertifiedVerdict semantics regime input
  | .stopped reason => .unknown reason
  | .proposed certificate =>
    match observed : checker.check regime input certificate with
    | some true => .consistent (by
        have sound := checker.checker_sound regime input certificate
        rw [observed] at sound
        exact sound)
    | some false => .inconsistent (by
        have sound := checker.checker_sound regime input certificate
        rw [observed] at sound
        exact sound)
    | none => .unknown .rejectedCertificate

/-- No correctness premise is imposed on search; host I/O and liveness are outside this model. -/
def pipeline {Regime : Type u} {semantics : Semantics Regime}
    (checker : CertificateChecker semantics)
    (search : (regime : Regime) → (input : semantics.Input regime) →
      SearchResult (checker.Certificate regime input))
    (regime : Regime) (input : semantics.Input regime) : WireVerdict :=
  erase (certify checker regime input (search regime input))

theorem pipeline_sound {Regime : Type u} {semantics : Semantics Regime}
    (checker : CertificateChecker semantics)
    (search : (regime : Regime) → (input : semantics.Input regime) →
      SearchResult (checker.Certificate regime input))
    (regime : Regime) (input : semantics.Input regime) :
    Meaning semantics regime input (pipeline checker search regime input).consistent :=
  erase_sound (certify checker regime input (search regime input))

namespace FiniteExample

inductive Regime where
  | requiresTrue
  | requiresFalse
  deriving Repr, DecidableEq

def semantics : Semantics Regime where
  Input := fun _ => Bool
  Interpretation := fun _ => Unit
  satisfies := fun regime input _ =>
    match regime with
    | .requiresTrue => input = true
    | .requiresFalse => input = false

inductive Certificate where
  | model
  | refutation
  deriving Repr, DecidableEq

/-- This small total checker validates either proposal against the finite semantics. -/
def check : Regime → Bool → Certificate → Option Bool
  | .requiresTrue, true, .model => some true
  | .requiresFalse, false, .model => some true
  | .requiresTrue, false, .refutation => some false
  | .requiresFalse, true, .refutation => some false
  | _, _, _ => none

def checker : CertificateChecker semantics where
  Certificate := fun _ _ => Certificate
  check := check
  checker_sound := by
    intro regime input certificate
    cases regime <;> cases input <;> cases certificate <;>
      first
      | exact True.intro
      | exact ⟨(), rfl⟩
      | exact fun ⟨_, impossible⟩ => Bool.noConfusion impossible

def modelSearch : (regime : Regime) → (input : semantics.Input regime) →
    SearchResult (checker.Certificate regime input) := fun _ _ => .proposed .model

def refutationSearch : (regime : Regime) → (input : semantics.Input regime) →
    SearchResult (checker.Certificate regime input) := fun _ _ => .proposed .refutation

def stoppedSearch : (regime : Regime) → (input : semantics.Input regime) →
    SearchResult (checker.Certificate regime input) := fun _ _ => .stopped .budgetExhausted

-- Executable controls pin Boolean meaning, regime separation, and rejected proposals.
#guard pipeline checker modelSearch .requiresTrue true = ⟨some true, none⟩
#guard pipeline checker refutationSearch .requiresTrue false = ⟨some false, none⟩
#guard pipeline checker refutationSearch .requiresFalse true = ⟨some false, none⟩
#guard pipeline checker modelSearch .requiresFalse false = ⟨some true, none⟩
#guard pipeline checker refutationSearch .requiresTrue true = ⟨none, some .rejectedCertificate⟩
#guard pipeline checker modelSearch .requiresTrue false = ⟨none, some .rejectedCertificate⟩
#guard pipeline checker stoppedSearch .requiresTrue true = ⟨none, some .budgetExhausted⟩

-- Invalid constructions must remain elaboration failures.
#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict semantics .requiresTrue true from .inconsistent)
#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict semantics .requiresTrue true from
  .inconsistent (fun _ => True.intro))
#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict semantics .requiresTrue false from
  .consistent ⟨(), rfl⟩)
#guard_msgs (drop info) in
#check_failure (show CertificateChecker semantics from {
  Certificate := fun _ _ => Unit
  check := fun _ _ _ => some false
  checker_sound := fun _ _ _ => True.intro
})

-- A proof under another regime cannot be re-labelled as evidence for this one.
def otherRegimeEvidence : CertifiedVerdict semantics .requiresFalse false :=
  .consistent ⟨(), rfl⟩
#guard_msgs (drop info) in
#check_failure (show CertifiedVerdict semantics .requiresTrue false from otherRegimeEvidence)

#eval pipeline checker modelSearch .requiresTrue true
#eval pipeline checker refutationSearch .requiresTrue false
#eval pipeline checker refutationSearch .requiresTrue true

end FiniteExample

#print axioms erase_sound
#print axioms no_contradictory_booleans
#print axioms pipeline_sound
#print axioms FiniteExample.checker

end CertifiedVerdictContract
