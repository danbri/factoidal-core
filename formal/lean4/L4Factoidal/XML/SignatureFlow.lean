/-
Composable XML security admission and a concrete restricted-signature flow.

Versions below describe requested configurations, NOT conformance claims.
The executable signature stages in this module implement only DSig's existing
root/enveloped/RSA-SHA256 profile. A host must derive a plan from the actual
document and bind its installed-feature inventory to actual implementations.
Admission is not a substitute for that reader/dispatcher refinement proof.

Selection and transforms must declare every external capability they need.
The plan checker does no IO. A zero-capability policy rejects requests for
resource access; it does not prove an arbitrary host obeys its capability list.

The concrete coverage gate compares the EXACT canonical bytes verified, not
their hashes. Equality is equality under the chosen canonicalization, not
proof of human intent or semantic preservation by arbitrary XSLT. Crypto is
the existing DSig.RsaVerify parameter; no cryptographic assumption is hidden.
-/
import L4Factoidal.XML.DSig
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.XML.SignatureFlow

open L4Factoidal.Dataflow

inductive SignatureVersion where
  | v10 | v10SecondEdition | v11 | v20Compatibility | v20
  deriving DecidableEq, BEq, Repr

inductive Capability where
  | externalEntity | referenceRead | stylesheetRead | documentRead
  | resultWrite | extensionCall | keyLookup | cipherReferenceRead
  deriving DecidableEq, BEq, Repr

/-- Distinct namespaces prevent a signature algorithm URI being mistaken for
an encryption algorithm or a language edition. Names are inventory keys. -/
inductive Feature where
  | xml (edition : String)
  | xpath (edition : String)
  | xslt (edition : String)
  | signature (version : SignatureVersion)
  | encryption (edition : String)
  | transform (uri : String)
  | canonicalization (uri : String)
  | digest (uri : String)
  | signatureAlgorithm (uri : String)
  | encryptionAlgorithm (uri : String)
  deriving DecidableEq, BEq, Repr

structure Plan where
  features : List Feature
  capabilities : List Capability
  referenceCount : Nat
  transformCount : Nat
  deriving DecidableEq, BEq, Repr

structure Limits where
  maxReferences : Nat
  maxTransforms : Nat
  maxInputBytes : Nat
  maxOutputBytes : Nat
  deriving DecidableEq, BEq, Repr

/-- Bounds are chosen by an application. The lower bounds prevent empty
budgets masquerading as a usable configuration; no universal useful upper
bound is claimed. Runtime stages separately enforce their actual byte bounds. -/
def Limits.valid (l : Limits) : Prop :=
  0 < l.maxReferences ∧ 0 < l.maxTransforms ∧
  0 < l.maxInputBytes ∧ 0 < l.maxOutputBytes

instance (l : Limits) : Decidable l.valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure Policy where
  permitted : List Feature
  capabilities : List Capability
  limits : Limits
  deriving DecidableEq, BEq, Repr

/-- Independent declarative requirements for a plan. Presence in an installed
inventory means claimed implementation availability, never policy permission. -/
def Admissible (installed : List Feature) (policy : Policy) (plan : Plan) : Prop :=
  policy.limits.valid ∧
  (∀ f ∈ plan.features, f ∈ installed) ∧
  (∀ f ∈ plan.features, f ∈ policy.permitted) ∧
  (∀ c ∈ plan.capabilities, c ∈ policy.capabilities) ∧
  0 < plan.referenceCount ∧ plan.referenceCount ≤ policy.limits.maxReferences ∧
  plan.transformCount ≤ policy.limits.maxTransforms

inductive Refusal where
  | invalidLimits
  | unsupported (feature : Feature)
  | forbidden (feature : Feature)
  | capabilityDenied (capability : Capability)
  | referenceLimit
  | transformLimit
  | inputLimit
  | outputLimit
  | signature (message : String)
  | coverageMismatch
  deriving DecidableEq, BEq, Repr

/-- Return the first missing member, retaining a specific diagnostic. -/
def firstMissing {α : Type} [DecidableEq α] (allowed : List α) : List α → Option α
  | [] => none
  | x :: xs => if x ∈ allowed then firstMissing allowed xs else some x

theorem firstMissing_none_iff {α : Type} [DecidableEq α] (allowed xs : List α) :
    firstMissing allowed xs = none ↔ ∀ x ∈ xs, x ∈ allowed := by
  induction xs with
  | nil => simp [firstMissing]
  | cons x xs ih => simp [firstMissing]; split <;> simp_all

/-- Check all three independent questions: implemented, permitted, capable.
No implicit downgrade or retry with another configuration occurs. -/
def admit (installed : List Feature) (policy : Policy) (plan : Plan) : Except Refusal Unit :=
  if ¬ policy.limits.valid then .error .invalidLimits else
  match firstMissing installed plan.features with
  | some f => .error (.unsupported f)
  | none => match firstMissing policy.permitted plan.features with
    | some f => .error (.forbidden f)
    | none => match firstMissing policy.capabilities plan.capabilities with
      | some c => .error (.capabilityDenied c)
      | none =>
          if plan.referenceCount = 0 ∨ policy.limits.maxReferences < plan.referenceCount then
            .error .referenceLimit
          else if policy.limits.maxTransforms < plan.transformCount then
            .error .transformLimit
          else .ok ()

theorem admit_sound {installed : List Feature} {policy : Policy} {plan : Plan}
    (h : admit installed policy plan = .ok ()) : Admissible installed policy plan := by
  unfold admit at h
  split at h
  · cases h
  · rename_i hv
    cases hi : firstMissing installed plan.features with
    | some f => simp [hi] at h
    | none =>
      simp only [hi] at h
      cases hp : firstMissing policy.permitted plan.features with
      | some f => simp [hp] at h
      | none =>
        simp only [hp] at h
        cases hc : firstMissing policy.capabilities plan.capabilities with
        | some c => simp [hc] at h
        | none =>
          simp only [hc] at h
          split at h
          · cases h
          · rename_i hr
            split at h
            · cases h
            · rename_i ht
              exact ⟨by simpa using hv,
                (firstMissing_none_iff _ _).mp hi,
                (firstMissing_none_iff _ _).mp hp,
                (firstMissing_none_iff _ _).mp hc,
                by omega, by omega, by omega⟩

/-- A restrictive caller cannot accidentally grant a capability by installing
more algorithms. The theorem covers the actual admission producer. -/
theorem admit_no_external_capabilities {installed : List Feature} {policy : Policy} {plan : Plan}
    (closed : policy.capabilities = []) (ok : admit installed policy plan = .ok ()) :
    plan.capabilities = [] := by
  have h := (admit_sound ok).2.2.2.1
  cases hp : plan.capabilities with
  | nil => rfl
  | cons c cs => have impossible := h c (by simp [hp]); simp [closed] at impossible

/-- Identity-preserving admission stage: accepted data cannot be substituted
between policy checking and the following dataflow operation. -/
def admissionStage (installed : List Feature) (policy : Policy) : Stage Refusal Plan Plan where
  run plan := (admit installed policy plan).map fun _ => plan
  contract input output := output = input ∧ Admissible installed policy input
  sound := by
    intro input output h
    cases hr : admit installed policy input with
    | error e => simp [hr, Except.map] at h
    | ok u =>
      cases u
      simp only [hr, Except.map, Except.ok.injEq] at h
      exact ⟨h.symm, admit_sound hr⟩

/-- A reusable output-size gate. It checks the actual returned value. This
does not bound the work needed to produce that value; evaluators need fuel. -/
def boundedStage {α β : Type} (size : β → Nat) (maximum : Nat)
    (s : Stage Refusal α β) : Stage Refusal α β where
  run a := match s.run a with
    | .error e => .error e
    | .ok b => if size b ≤ maximum then .ok b else .error .outputLimit
  contract a b := s.contract a b ∧ size b ≤ maximum
  sound := by
    intro a b h
    cases hr : s.run a with
    | error e => simp [hr] at h
    | ok value =>
      simp only [hr] at h
      split at h
      · rename_i bound
        cases h
        exact ⟨s.sound a b hr, bound⟩
      · cases h

/-- The input limit is checked before invoking the wrapped stage. As with the
output gate, the supplied size function must count the intended units. -/
def inputBoundedStage {α β : Type} (size : α → Nat) (maximum : Nat)
    (s : Stage Refusal α β) : Stage Refusal α β where
  run a := if size a ≤ maximum then s.run a else .error .inputLimit
  contract a b := size a ≤ maximum ∧ s.contract a b
  sound := by
    intro a b h
    split at h
    · rename_i bound
      exact ⟨bound, s.sound a b h⟩
    · cases h

def boundedFlow {α β : Type} (inputBytes : α → Nat) (outputBytes : β → Nat)
    (limits : Limits) (s : Stage Refusal α β) : Stage Refusal α β :=
  inputBoundedStage inputBytes limits.maxInputBytes
    (boundedStage outputBytes limits.maxOutputBytes s)

theorem boundedFlow_sound {α β : Type} {inputBytes : α → Nat} {outputBytes : β → Nat}
    {limits : Limits} {s : Stage Refusal α β} {a : α} {b : β}
    (h : (boundedFlow inputBytes outputBytes limits s).run a = .ok b) :
    inputBytes a ≤ limits.maxInputBytes ∧ s.contract a b ∧
      outputBytes b ≤ limits.maxOutputBytes :=
  (boundedFlow inputBytes outputBytes limits s).sound a b h

/-! Concrete restricted-profile operations, reusing the existing verifier. -/

abbrev Selected := DSig.El × DSig.Parts

def selectRoot (idAttribute : String) (d : Document) : Except Refusal Selected :=
  (DSig.signedParts d idAttribute).mapError Refusal.signature

def envelopedTransform (selected : Selected) : Node := DSig.withoutSignature selected.1

structure CanonicalInput where
  selected : Selected
  reference : String
  signedInfo : String

/-- Both canonical values retain the same selected signature parts. -/
def canonicalize (selected : Selected) : Except Refusal CanonicalInput :=
  match DSig.canonForms selected.1 selected.2 with
  | none => .error (.signature "the signed content cannot be canonicalized")
  | some (reference, signedInfo) => .ok ⟨selected, reference, signedInfo⟩

def digestMatches (input : CanonicalInput) : Bool :=
  L4Factoidal.Crypto.sha256 input.reference.toUTF8 == input.selected.2.digest

def signatureMatches (rsa : DSig.RsaVerify) (n e : ByteArray) (input : CanonicalInput) : Bool :=
  rsa n e input.selected.2.sigValue input.signedInfo.toUTF8

def covers (expected : String) (input : CanonicalInput) : Bool := input.reference == expected

/-- Successful output exposes the canonical data actually verified; application
code must consume this value, not reselect another node from the source XML. -/
def verifyCanonical (rsa : DSig.RsaVerify) (n e : ByteArray) (expected : String)
    (input : CanonicalInput) : Except Refusal CanonicalInput :=
  if digestMatches input then
    if signatureMatches rsa n e input then
      if covers expected input then .ok input else .error .coverageMismatch
    else .error (.signature "the signature value does not verify")
  else .error (.signature "the digest of the signed element does not match")

theorem verifyCanonical_sound {rsa : DSig.RsaVerify} {n e : ByteArray} {expected : String}
    {input output : CanonicalInput}
    (h : verifyCanonical rsa n e expected input = .ok output) :
    output = input ∧ digestMatches input = true ∧
      signatureMatches rsa n e input = true ∧ input.reference = expected := by
  unfold verifyCanonical at h
  split at h
  · rename_i hd
    split at h
    · rename_i hs
      split at h
      · rename_i hc
        cases h
        exact ⟨rfl, hd, hs, by simpa [covers] using hc⟩
      · cases h
    · cases h
  · cases h

def verificationStage (rsa : DSig.RsaVerify) (n e : ByteArray) (expected : String) :
    Stage Refusal CanonicalInput CanonicalInput where
  run := verifyCanonical rsa n e expected
  contract input output := output = input ∧ digestMatches input = true ∧
    signatureMatches rsa n e input = true ∧ input.reference = expected
  sound := fun _ _ h => verifyCanonical_sound h

def selectionStage (idAttribute : String) : Stage Refusal Document Selected where
  run := selectRoot idAttribute
  contract document selected := DSig.signedParts document idAttribute = .ok selected
  sound := by
    intro document selected h
    unfold selectRoot at h
    cases hr : DSig.signedParts document idAttribute with
    | error e => simp [hr, Except.mapError] at h
    | ok value => simpa [hr, Except.mapError] using h

def canonicalizationStage : Stage Refusal Selected CanonicalInput where
  run := canonicalize
  contract selected output := output.selected = selected ∧
    DSig.canonForms selected.1 selected.2 = some (output.reference, output.signedInfo)
  sound := by
    intro selected output h
    unfold canonicalize at h
    cases hc : DSig.canonForms selected.1 selected.2 with
    | none => simp [hc] at h
    | some forms =>
      obtain ⟨reference, signedInfo⟩ := forms
      simp only [hc, Except.ok.injEq] at h
      subst output
      exact ⟨rfl, rfl⟩

/-- Actual FP composition of the restricted structural reader, transforms and
canonicalization, digest/signature checking, and exact coverage checking. The
signature's own transform list is checked by selection; callers cannot pass
an unrelated plan in its place. This stage performs no resource IO. -/
def restrictedStage (rsa : DSig.RsaVerify) (n e : ByteArray)
    (expected : String) (idAttribute : String := "ID") : Stage Refusal Document CanonicalInput :=
  ((selectionStage idAttribute).comp canonicalizationStage).comp
    (verificationStage rsa n e expected)

/-- The produced canonical reference and SignedInfo belong to the parts read
from THIS document, and the EXACT returned reference is the expected content.
The external RSA implementation remains a named parameter. -/
theorem restrictedStage_sound {rsa : DSig.RsaVerify} {n e : ByteArray}
    {expected idAttribute : String} {document : Document} {output : CanonicalInput}
    (h : (restrictedStage rsa n e expected idAttribute).run document = .ok output) :
    DSig.signedParts document idAttribute = .ok output.selected ∧
    DSig.canonForms output.selected.1 output.selected.2 =
      some (output.reference, output.signedInfo) ∧
    digestMatches output = true ∧ signatureMatches rsa n e output = true ∧
    output.reference = expected := by
  have hs := (restrictedStage rsa n e expected idAttribute).sound document output h
  obtain ⟨middle, ⟨selected, hselected, hcanon⟩, hverify⟩ := hs
  obtain ⟨same, hd, hv, he⟩ := hverify
  subst output
  obtain ⟨sameSelected, hc⟩ := hcanon
  rw [← sameSelected] at hselected hc
  exact ⟨hselected, hc, hd, hv, he⟩

/-- Stronger than digest equality: an omitted amount cannot be covered merely
because the projected document has its own valid signature. -/
theorem changed_reference_rejected {rsa : DSig.RsaVerify} {n e : ByteArray}
    {expected : String} {input output : CanonicalInput} (changed : input.reference ≠ expected) :
    verifyCanonical rsa n e expected input ≠ .ok output := by
  intro h
  exact changed (verifyCanonical_sound h).2.2.2

#print axioms admit_sound
#print axioms admit_no_external_capabilities
#print axioms verifyCanonical_sound
#print axioms changed_reference_rejected
#print axioms restrictedStage_sound
#print axioms boundedFlow_sound

end L4Factoidal.XML.SignatureFlow
