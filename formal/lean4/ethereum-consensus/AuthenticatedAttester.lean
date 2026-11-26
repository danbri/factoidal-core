import EthereumConsensus.SSZ.ValidatorRegistry
import BLSVerify

namespace EthereumConsensus.SSZ.AuthenticatedAttester
open EthereumConsensus.BLS.Verify

abbrev AttesterEvidence := PreparedAttesterSlashing × AllSignerSelection

inductive AuthError where
  | noEligible
  | preparation (reason : SignerError)
  | firstFailure (reason : VerifyError)
  | secondFailure (reason : VerifyError)
  | firstMismatch
  | secondMismatch

def firstVerdict (e : AttesterEvidence) (sig : ByteArray) : Except VerifyError Bool :=
  verifySigningRoot e.2.firstKeys e.1.firstSigningRoot.bytes sig

def secondVerdict (e : AttesterEvidence) (sig : ByteArray) : Except VerifyError Bool :=
  verifySigningRoot e.2.secondKeys e.1.secondSigningRoot.bytes sig

/-- Both concrete signatures must authenticate the exact prepared evidence. -/
def authenticate (e : AttesterEvidence) (a b : ByteArray) :
    Except AuthError AttesterEvidence :=
  match firstVerdict e a with
  | .error reason => .error (.firstFailure reason)
  | .ok false => .error .firstMismatch
  | .ok true =>
    match secondVerdict e b with
    | .error reason => .error (.secondFailure reason)
    | .ok false => .error .secondMismatch
    | .ok true => if e.2.eligibleCommon.isEmpty then .error .noEligible else .ok e

/-- Conditional on the supplied state commitment. No state mutation. -/
def authenticateState (slot : UInt64) (c : ForkContext) (a b : AttestationData)
    (left right : List UInt64) (lw rw : List SignerWitness) (length : Nat)
    (registryRoot : ByteArray)
    (registrySiblings slotSiblings forkSiblings genesisSiblings : List ByteArray)
    (stateRoot sigA sigB : ByteArray) : Except AuthError AttesterEvidence :=
  match checkAllStateSigners slot c a b left right lw rw length registryRoot
      registrySiblings slotSiblings forkSiblings genesisSiblings stateRoot with
  | .error reason => .error (.preparation reason)
  | .ok e => authenticate e sigA sigB

/-- Kind: linkage. Says: preparation failure prevents authentication.
Does not say: canonical state is established. -/
theorem preparation_error (slot : UInt64) (c : ForkContext) (a b : AttestationData)
    (left right : List UInt64) (lw rw : List SignerWitness) (n : Nat)
    (rr : ByteArray) (rs sl fs gs : List ByteArray) (root sa sb : ByteArray) (e : SignerError)
    (h : checkAllStateSigners slot c a b left right lw rw n rr rs sl fs gs root = .error e) :
    authenticateState slot c a b left right lw rw n rr rs sl fs gs root sa sb =
      .error (.preparation e) := by
  simp only [authenticateState, h]

/-- Kind: linkage. Says: first BLS error is propagated.
Does not say: errors are protocol-invalid verdicts. -/
theorem first_failure (e : AttesterEvidence) (a b : ByteArray) (reason : VerifyError)
    (h : firstVerdict e a = .error reason) :
    authenticate e a b = .error (.firstFailure reason) := by
  simp only [authenticate, h]

/-- Kind: linkage. Says: a false first equation prevents success.
Does not say: the pairing mathematics is refined. -/
theorem first_mismatch (e : AttesterEvidence) (a b : ByteArray)
    (h : firstVerdict e a = .ok false) :
    authenticate e a b = .error .firstMismatch := by
  simp only [authenticate, h]

/-- Kind: linkage. Says: second BLS error remains distinguishable.
Does not say: error is a protocol-invalid verdict. -/
theorem second_failure (e : AttesterEvidence) (a b : ByteArray) (reason : VerifyError)
    (ha : firstVerdict e a = .ok true) (hb : secondVerdict e b = .error reason) :
    authenticate e a b = .error (.secondFailure reason) := by
  simp only [authenticate, ha, hb]

/-- Kind: linkage. Says: a false second equation prevents success.
Does not say: the pairing mathematics is refined. -/
theorem second_mismatch (e : AttesterEvidence) (a b : ByteArray)
    (ha : firstVerdict e a = .ok true) (hb : secondVerdict e b = .ok false) :
    authenticate e a b = .error .secondMismatch := by
  simp only [authenticate, ha, hb]

/-- Kind: linkage. Says: success returns unchanged evidence and requires
both concrete verifier results true. Does not establish canonical state. -/
theorem authenticate_success (e out : AttesterEvidence) (a b : ByteArray)
    (h : authenticate e a b = .ok out) :
    out = e ∧ firstVerdict e a = .ok true ∧ secondVerdict e b = .ok true ∧
    e.2.eligibleCommon.isEmpty = false := by
  cases ha : firstVerdict e a with
  | error reason => simp [authenticate, ha] at h
  | ok x =>
    cases x with
    | false => simp [authenticate, ha] at h
    | true =>
      cases hb : secondVerdict e b with
      | error reason => simp [authenticate, ha, hb] at h
      | ok y =>
        cases y with
        | false => simp [authenticate, ha, hb] at h
        | true =>
          cases hc : e.2.eligibleCommon.isEmpty with
          | true => simp [authenticate, ha, hb, hc] at h
          | false =>
            have he : e = out := by simpa [authenticate, ha, hb, hc] using h
            exact ⟨he.symm, by simp [ha], by simp [hb], by simp [hc]⟩

/-- Kind: linkage. Says: success of the raw state path requires actual
preparation and both concrete verifications on the returned evidence.
Does not say: normative BLS/SSZ refinement or a state mutation. -/
theorem state_success (slot : UInt64) (c : ForkContext) (a b : AttestationData)
    (left right : List UInt64) (lw rw : List SignerWitness) (n : Nat)
    (rr : ByteArray) (rs sl fs gs : List ByteArray) (root sa sb : ByteArray)
    (out : AttesterEvidence)
    (h : authenticateState slot c a b left right lw rw n rr rs sl fs gs root sa sb = .ok out) :
    checkAllStateSigners slot c a b left right lw rw n rr rs sl fs gs root = .ok out ∧
    firstVerdict out sa = .ok true ∧ secondVerdict out sb = .ok true ∧
    out.2.eligibleCommon.isEmpty = false := by
  cases hp : checkAllStateSigners slot c a b left right lw rw n rr rs sl fs gs root with
  | error reason => simp [authenticateState, hp] at h
  | ok e =>
    have hv : authenticate e sa sb = .ok out := by simpa [authenticateState, hp] using h
    obtain ⟨he, ha, hb, hc⟩ := authenticate_success e out sa sb hv
    subst out
    exact ⟨by simp [hp], ha, hb, hc⟩

/-- Kind: linkage. Says: after both signatures pass, an empty eligible
    intersection refuses. Does not say: any state mutation occurs. -/
theorem no_eligible (e : AttesterEvidence) (a b : ByteArray)
    (ha : firstVerdict e a = .ok true) (hb : secondVerdict e b = .ok true)
    (hc : e.2.eligibleCommon.isEmpty = true) :
    authenticate e a b = .error .noEligible := by
  simp only [authenticate, ha, hb, hc, if_true]

#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.no_eligible
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.preparation_error
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.first_failure
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.first_mismatch
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.second_failure
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.second_mismatch
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.authenticate_success
#print axioms EthereumConsensus.SSZ.AuthenticatedAttester.state_success
end EthereumConsensus.SSZ.AuthenticatedAttester
