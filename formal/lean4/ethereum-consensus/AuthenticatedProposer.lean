import EthereumConsensus.SSZ.ProposerSlashing
import BLSVerify

namespace EthereumConsensus.SSZ.AuthenticatedProposer
open EthereumConsensus.BLS.Verify

inductive AuthError where
  | preparation (reason : ProposerEvidenceError)
  | firstFailure (reason : VerifyError)
  | secondFailure (reason : VerifyError)
  | firstMismatch
  | secondMismatch

def firstVerdict (e : ProposerEvidence) (sig : ByteArray) : Except VerifyError Bool :=
  verifySigningRoot [e.publicKey] e.firstSigningRoot.bytes sig

def secondVerdict (e : ProposerEvidence) (sig : ByteArray) : Except VerifyError Bool :=
  verifySigningRoot [e.publicKey] e.secondSigningRoot.bytes sig

/-- Both concrete signatures must authenticate the exact prepared evidence. -/
def authenticate (e : ProposerEvidence) (a b : ByteArray) :
    Except AuthError ProposerEvidence :=
  match firstVerdict e a with
  | .error reason => .error (.firstFailure reason)
  | .ok false => .error .firstMismatch
  | .ok true =>
    match secondVerdict e b with
    | .error reason => .error (.secondFailure reason)
    | .ok false => .error .secondMismatch
    | .ok true => .ok e

/-- Conditional on the supplied state commitment. No state mutation. -/
def authenticateState (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (length : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (registryRoot : ByteArray)
    (registrySiblings slotSiblings forkSiblings genesisSiblings : List ByteArray)
    (stateRoot sigA sigB : ByteArray) : Except AuthError ProposerEvidence :=
  match checkProposerState slot a b c length v siblings registryRoot
      registrySiblings slotSiblings forkSiblings genesisSiblings stateRoot with
  | .error reason => .error (.preparation reason)
  | .ok e => authenticate e sigA sigB

/-- Kind: linkage. Says: preparation failure prevents authentication.
Does not say: canonical state is established. -/
theorem preparation_error (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (n : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray)
    (root sa sb : ByteArray) (e : ProposerEvidenceError)
    (h : checkProposerState slot a b c n v ss rr rs sl fs gs root = .error e) :
    authenticateState slot a b c n v ss rr rs sl fs gs root sa sb =
      .error (.preparation e) := by
  simp only [authenticateState, h]

/-- Kind: linkage. Says: first BLS error is propagated.
Does not say: errors are protocol-invalid verdicts. -/
theorem first_failure (e : ProposerEvidence) (a b : ByteArray) (reason : VerifyError)
    (h : firstVerdict e a = .error reason) :
    authenticate e a b = .error (.firstFailure reason) := by
  simp only [authenticate, h]

/-- Kind: linkage. Says: a false first equation prevents success.
Does not say: the pairing mathematics is refined. -/
theorem first_mismatch (e : ProposerEvidence) (a b : ByteArray)
    (h : firstVerdict e a = .ok false) :
    authenticate e a b = .error .firstMismatch := by
  simp only [authenticate, h]

/-- Kind: linkage. Says: second BLS error remains distinguishable.
Does not say: error is a protocol-invalid verdict. -/
theorem second_failure (e : ProposerEvidence) (a b : ByteArray) (reason : VerifyError)
    (ha : firstVerdict e a = .ok true) (hb : secondVerdict e b = .error reason) :
    authenticate e a b = .error (.secondFailure reason) := by
  simp only [authenticate, ha, hb]

/-- Kind: linkage. Says: a false second equation prevents success.
Does not say: the pairing mathematics is refined. -/
theorem second_mismatch (e : ProposerEvidence) (a b : ByteArray)
    (ha : firstVerdict e a = .ok true) (hb : secondVerdict e b = .ok false) :
    authenticate e a b = .error .secondMismatch := by
  simp only [authenticate, ha, hb]

/-- Kind: linkage. Says: success returns unchanged evidence and requires
both concrete verifier results true. Does not establish canonical state. -/
theorem authenticate_success (e out : ProposerEvidence) (a b : ByteArray)
    (h : authenticate e a b = .ok out) :
    out = e ∧ firstVerdict e a = .ok true ∧ secondVerdict e b = .ok true := by
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
          have he : e = out := by simpa [authenticate, ha, hb] using h
          exact ⟨he.symm, by simp [ha], by simp [hb]⟩

/-- Kind: linkage. Says: success of the raw state path requires actual
preparation and both concrete verifications on the returned evidence.
Does not say: normative BLS/SSZ refinement or a state mutation. -/
theorem state_success (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (n : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray)
    (root sa sb : ByteArray) (out : ProposerEvidence)
    (h : authenticateState slot a b c n v ss rr rs sl fs gs root sa sb = .ok out) :
    checkProposerState slot a b c n v ss rr rs sl fs gs root = .ok out ∧
    firstVerdict out sa = .ok true ∧ secondVerdict out sb = .ok true := by
  cases hp : checkProposerState slot a b c n v ss rr rs sl fs gs root with
  | error reason => simp [authenticateState, hp] at h
  | ok e =>
    have hv : authenticate e sa sb = .ok out := by simpa [authenticateState, hp] using h
    obtain ⟨he, ha, hb⟩ := authenticate_success e out sa sb hv
    subst out
    exact ⟨by simp [hp], ha, hb⟩

#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.preparation_error
#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.first_failure
#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.first_mismatch
#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.second_failure
#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.second_mismatch
#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.authenticate_success
#print axioms EthereumConsensus.SSZ.AuthenticatedProposer.state_success
end EthereumConsensus.SSZ.AuthenticatedProposer
