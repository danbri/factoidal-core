import EthereumConsensus.SSZ.AttesterSlashing

/-! Validator registry membership conditional on a supplied registry root.
    Normative pin: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3,
    specs/phase0/beacon-chain.md, Validator, is_slashable_validator.
    Not BLS validation, state-root authentication or a state transition. -/
namespace EthereumConsensus.SSZ

structure RegistryValidator where
  publicKey : ByteArray
  withdrawalCredentials : ByteArray
  effectiveBalance : UInt64
  slashed : Bool
  activationEligibilityEpoch : UInt64
  activationEpoch : UInt64
  exitEpoch : UInt64
  withdrawableEpoch : UInt64

inductive RegistryError where
  | publicKeyWidth
  | credentialsWidth
  | basicRoot
  | registryLength
  | indexOutside
  | branchLength
  | proof (error : ByteProofError)
  | notCommon
  deriving BEq, DecidableEq, Repr

def validatorPublicKeyRoot (key : ByteArray) : Except RegistryError Chunk := do
  if key.size ≠ 48 then throw .publicKeyWidth
  let left ← (Chunk.ofBytes (key.extract 0 32)).mapError RegistryError.proof
  let right ← (checkedBasicRoot (key.extract 32 48)).mapError (fun _ => .basicRoot)
  return hashPair left right

def validatorTree (key credentials balance slashed eligible activation exit withdrawable : Chunk) : Chunk :=
  hashPair
    (hashPair (hashPair key credentials) (hashPair balance slashed))
    (hashPair (hashPair eligible activation) (hashPair exit withdrawable))

def validatorRoot (v : RegistryValidator) : Except RegistryError Chunk := do
  let key ← validatorPublicKeyRoot v.publicKey
  let credentials ← (Chunk.ofBytes v.withdrawalCredentials).mapError (fun _ => .credentialsWidth)
  let balance ← (uint64Root v.effectiveBalance).mapError (fun _ => .basicRoot)
  let slashed ← (boolRoot v.slashed).mapError (fun _ => .basicRoot)
  let eligible ← (uint64Root v.activationEligibilityEpoch).mapError (fun _ => .basicRoot)
  let activation ← (uint64Root v.activationEpoch).mapError (fun _ => .basicRoot)
  let exit ← (uint64Root v.exitEpoch).mapError (fun _ => .basicRoot)
  let withdrawable ← (uint64Root v.withdrawableEpoch).mapError (fun _ => .basicRoot)
  return validatorTree key credentials balance slashed eligible activation exit withdrawable

def validatorRegistryLimit : Nat := 2 ^ 40

def validatorRegistryGindex (index : Nat) : Nat := 2 ^ 41 + index

def verifyValidatorAt (length index : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (registryRoot : ByteArray) :
    Except RegistryError ByteProofResult :=
  if length > validatorRegistryLimit then .error .registryLength
  else if index ≥ length then .error .indexOutside
  else if siblings.length ≠ 40 then .error .branchLength
  else
    match validatorRoot v with
    | .error e => .error e
    | .ok leaf =>
      match uint64Root (UInt64.ofNat length) with
      | .error _ => .error .basicRoot
      | .ok lengthChunk =>
        (verifyByteBranch 41 (validatorRegistryGindex index) leaf.bytes
          (siblings ++ [lengthChunk.bytes]) registryRoot).mapError RegistryError.proof

def slashableValidatorModel (v : RegistryValidator) (epoch : UInt64) : Prop :=
  v.slashed = false ∧ v.activationEpoch ≤ epoch ∧ epoch < v.withdrawableEpoch

def isSlashableValidator (v : RegistryValidator) (epoch : UInt64) : Bool :=
  !v.slashed && decide (v.activationEpoch ≤ epoch) && decide (epoch < v.withdrawableEpoch)

inductive RegistryCandidateVerdict where
  | rootMismatch
  | notSlashable
  | candidateNotAuthenticated
  deriving BEq, DecidableEq, Repr

/-- Consume the preceding slashing preparation, but never authenticate
    its aggregate signatures or the supplied state/registry root. -/
def checkCommonValidator (prepared : PreparedAttesterSlashing) (epoch index : UInt64)
    (length : Nat) (v : RegistryValidator) (siblings : List ByteArray)
    (registryRoot : ByteArray) : Except RegistryError RegistryCandidateVerdict :=
  if index ∉ prepared.commonIndices then .error .notCommon
  else
    match verifyValidatorAt length index.toNat v siblings registryRoot with
    | .error e => .error e
    | .ok result =>
      if !result.matchesRoot then .ok .rootMismatch
      else if isSlashableValidator v epoch then .ok .candidateNotAuthenticated
      else .ok .notSlashable

/-- Kind: admission. Says: lengths above the protocol list limit refuse.
    Does not say: any admitted length is authentic. -/
theorem verifyValidatorAt_over_length (length index : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray) (h : length > validatorRegistryLimit) :
    verifyValidatorAt length index v siblings root = .error .registryLength := by
  simp only [verifyValidatorAt, if_pos h]

/-- Kind: admission. Says: padded slots cannot be accepted as validators.
    Does not say: the supplied length is authentic. -/
theorem verifyValidatorAt_outside (length index : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray)
    (hl : ¬ length > validatorRegistryLimit) (hi : index ≥ length) :
    verifyValidatorAt length index v siblings root = .error .indexOutside := by
  simp only [verifyValidatorAt, if_neg hl, if_pos hi]

/-- Kind: admission. Says: precisely 40 element siblings are required.
    Does not say: these siblings belong to an authentic registry. -/
theorem verifyValidatorAt_bad_branch (length index : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray)
    (hl : ¬ length > validatorRegistryLimit) (hi : ¬ index ≥ length)
    (hs : siblings.length ≠ 40) :
    verifyValidatorAt length index v siblings root = .error .branchLength := by
  simp only [verifyValidatorAt, if_neg hl, if_neg hi, if_pos hs]

/-- Kind: linkage. Says: the actual verifier appends the locally derived
    length chunk and uses the fixed registry gindex in the byte verifier.
    Does not say: this proves SHA-256 collision resistance or state anchoring. -/
theorem verifyValidatorAt_delegates (length index : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray) (leaf lenChunk : Chunk)
    (hl : ¬ length > validatorRegistryLimit) (hi : ¬ index ≥ length)
    (hs : ¬ siblings.length ≠ 40)
    (hv : validatorRoot v = .ok leaf)
    (hc : uint64Root (UInt64.ofNat length) = .ok lenChunk) :
    verifyValidatorAt length index v siblings root =
      (verifyByteBranch 41 (validatorRegistryGindex index) leaf.bytes
        (siblings ++ [lenChunk.bytes]) root).mapError RegistryError.proof := by
  simp only [verifyValidatorAt, if_neg hl, if_neg hi, if_neg hs, hv, hc]

/-- Kind: refinement. Says: eligibility uses the activation/withdrawable
    interval and slashed flag, not the exit epoch. Does not say: the validator
    or epoch is authentic. -/
theorem isSlashableValidator_iff (v : RegistryValidator) (epoch : UInt64) :
    isSlashableValidator v epoch = true ↔ slashableValidatorModel v epoch := by
  simp [isSlashableValidator, slashableValidatorModel, and_assoc]

/-- Kind: admission. Says: no index absent from the common set can become
    a candidate through this function. Does not say: the set is authenticated. -/
theorem checkCommonValidator_not_common (p : PreparedAttesterSlashing)
    (epoch index : UInt64) (length : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray) (h : index ∉ p.commonIndices) :
    checkCommonValidator p epoch index length v siblings root = .error .notCommon := by
  simp only [checkCommonValidator, if_pos h]

/-- Kind: linkage. Says: a mismatching admitted membership proof cannot
    yield a slashing candidate, even when the validator is eligible.
    Does not say: the supplied root is authentic. -/
theorem checkCommonValidator_mismatch (p : PreparedAttesterSlashing)
    (epoch index : UInt64) (length : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray) (result : ByteProofResult)
    (hm : index ∈ p.commonIndices)
    (hp : verifyValidatorAt length index.toNat v siblings root = .ok result)
    (hb : result.matchesRoot = false) :
    checkCommonValidator p epoch index length v siblings root = .ok .rootMismatch := by
  simp [checkCommonValidator, hm, hp, hb]

/-- Kind: linkage. Says: a common, eligible validator with a matching
    membership proof yields only an unauthenticated candidate.
    Does not say: either signature or the BeaconState has been authenticated. -/
theorem checkCommonValidator_candidate (p : PreparedAttesterSlashing)
    (epoch index : UInt64) (length : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (root : ByteArray) (result : ByteProofResult)
    (hm : index ∈ p.commonIndices)
    (hp : verifyValidatorAt length index.toNat v siblings root = .ok result)
    (hb : result.matchesRoot = true)
    (hv : isSlashableValidator v epoch = true) :
    checkCommonValidator p epoch index length v siblings root = .ok .candidateNotAuthenticated := by
  simp [checkCommonValidator, hm, hp, hb, hv]

#print axioms EthereumConsensus.SSZ.verifyValidatorAt_over_length
#print axioms EthereumConsensus.SSZ.verifyValidatorAt_outside
#print axioms EthereumConsensus.SSZ.verifyValidatorAt_bad_branch
#print axioms EthereumConsensus.SSZ.verifyValidatorAt_delegates
#print axioms EthereumConsensus.SSZ.isSlashableValidator_iff
#print axioms EthereumConsensus.SSZ.checkCommonValidator_not_common

#print axioms EthereumConsensus.SSZ.checkCommonValidator_mismatch
#print axioms EthereumConsensus.SSZ.checkCommonValidator_candidate

end EthereumConsensus.SSZ
