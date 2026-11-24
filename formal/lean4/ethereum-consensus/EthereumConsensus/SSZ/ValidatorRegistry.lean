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


/-- Explicit BeaconState container layouts, not a fork-choice verdict.
    Phase0 through Deneb have 32 field positions; Electra and Fulu have 64.
    The validators field is at zero-based position 11 in both layouts.
    Spec pin: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3. -/
inductive RegistryStateLayout where
  | phase0Deneb
  | electraFulu
  deriving BEq, DecidableEq, Repr

def registryStateDepth : RegistryStateLayout → Nat
  | .phase0Deneb => 5
  | .electraFulu => 6

def registryStateGindex : RegistryStateLayout → Nat
  | .phase0Deneb => 43
  | .electraFulu => 75

def verifyRegistryInState (layout : RegistryStateLayout)
    (registryRoot : ByteArray) (stateSiblings : List ByteArray)
    (stateRoot : ByteArray) : Except RegistryError ByteProofResult :=
  if stateSiblings.length ≠ registryStateDepth layout then .error .branchLength
  else (verifyByteBranch (registryStateDepth layout) (registryStateGindex layout)
    registryRoot stateSiblings stateRoot).mapError RegistryError.proof

inductive StateCandidateVerdict where
  | stateRootMismatch
  | registryVerdict (verdict : RegistryCandidateVerdict)
  deriving BEq, DecidableEq, Repr

/-- Both branches must match before a candidate can be returned. The state
    root, layout, epoch and prepared signatures are not authenticated here. -/
def checkStateCommonValidator (layout : RegistryStateLayout)
    (prepared : PreparedAttesterSlashing) (epoch index : UInt64)
    (length : Nat) (v : RegistryValidator) (siblings : List ByteArray)
    (registryRoot : ByteArray) (stateSiblings : List ByteArray)
    (stateRoot : ByteArray) : Except RegistryError StateCandidateVerdict :=
  match verifyRegistryInState layout registryRoot stateSiblings stateRoot with
  | .error e => .error e
  | .ok result =>
    if result.matchesRoot then
      match checkCommonValidator prepared epoch index length v siblings registryRoot with
      | .error e => .error e
      | .ok verdict => .ok (.registryVerdict verdict)
    else .ok .stateRootMismatch

/-- Kind: layout. Says: the earlier layout uses position 11 at depth 5.
    Does not say: the supplied state uses that fork. -/
theorem registryState_phase0Deneb :
    registryStateDepth .phase0Deneb = 5 ∧ registryStateGindex .phase0Deneb = 43 :=
  ⟨rfl, rfl⟩

/-- Kind: layout. Says: the later layout uses position 11 at depth 6.
    Does not say: the supplied state uses that fork. -/
theorem registryState_electraFulu :
    registryStateDepth .electraFulu = 6 ∧ registryStateGindex .electraFulu = 75 :=
  ⟨rfl, rfl⟩

/-- Kind: admission. Says: a wrong state-branch count is refused.
    Does not say: admitted witnesses have correct byte widths. -/
theorem verifyRegistryInState_bad_branch (layout : RegistryStateLayout)
    (registryRoot : ByteArray) (siblings : List ByteArray) (stateRoot : ByteArray)
    (h : siblings.length ≠ registryStateDepth layout) :
    verifyRegistryInState layout registryRoot siblings stateRoot = .error .branchLength := by
  simp only [verifyRegistryInState, if_pos h]

/-- Kind: linkage. Says: the actual verifier uses the layout's fixed depth
    and index with concrete byte proofs. Does not say: the root is authentic. -/
theorem verifyRegistryInState_delegates (layout : RegistryStateLayout)
    (registryRoot : ByteArray) (siblings : List ByteArray) (stateRoot : ByteArray)
    (h : siblings.length = registryStateDepth layout) :
    verifyRegistryInState layout registryRoot siblings stateRoot =
      (verifyByteBranch (registryStateDepth layout) (registryStateGindex layout)
        registryRoot siblings stateRoot).mapError RegistryError.proof := by
  simp [verifyRegistryInState, h]

/-- Kind: linkage. Says: a mismatching state branch cannot reach a candidate.
    Does not say: the root itself is authentic. -/
theorem checkStateCommonValidator_mismatch (layout : RegistryStateLayout)
    (p : PreparedAttesterSlashing) (epoch index : UInt64) (length : Nat)
    (v : RegistryValidator) (siblings : List ByteArray) (registryRoot : ByteArray)
    (stateSiblings : List ByteArray) (stateRoot : ByteArray) (result : ByteProofResult)
    (hp : verifyRegistryInState layout registryRoot stateSiblings stateRoot = .ok result)
    (hm : result.matchesRoot = false) :
    checkStateCommonValidator layout p epoch index length v siblings registryRoot stateSiblings stateRoot =
      .ok .stateRootMismatch := by
  simp [checkStateCommonValidator, hp, hm]

/-- Kind: linkage. Says: after a matching state proof the existing common
    validator path decides the outcome. Does not say: signatures are valid. -/
theorem checkStateCommonValidator_delegates (layout : RegistryStateLayout)
    (p : PreparedAttesterSlashing) (epoch index : UInt64) (length : Nat)
    (v : RegistryValidator) (siblings : List ByteArray) (registryRoot : ByteArray)
    (stateSiblings : List ByteArray) (stateRoot : ByteArray) (result : ByteProofResult)
    (verdict : RegistryCandidateVerdict)
    (hp : verifyRegistryInState layout registryRoot stateSiblings stateRoot = .ok result)
    (hm : result.matchesRoot = true)
    (hc : checkCommonValidator p epoch index length v siblings registryRoot = .ok verdict) :
    checkStateCommonValidator layout p epoch index length v siblings registryRoot stateSiblings stateRoot =
      .ok (.registryVerdict verdict) := by
  simp [checkStateCommonValidator, hp, hm, hc]

#print axioms EthereumConsensus.SSZ.registryState_phase0Deneb
#print axioms EthereumConsensus.SSZ.registryState_electraFulu
#print axioms EthereumConsensus.SSZ.verifyRegistryInState_bad_branch
#print axioms EthereumConsensus.SSZ.verifyRegistryInState_delegates
#print axioms EthereumConsensus.SSZ.checkStateCommonValidator_mismatch
#print axioms EthereumConsensus.SSZ.checkStateCommonValidator_delegates


/-- Mainnet preset and activation boundary, pinned to the consensus-specs
    revision above (presets/mainnet/phase0.yaml and configs/mainnet.yaml).
    No caller-supplied epoch or fork layout is used by the new entry point. -/
def mainnetRegistryEpoch (slot : UInt64) : UInt64 :=
  UInt64.ofNat (slot.toNat / 32)

def mainnetRegistryLayout (slot : UInt64) : RegistryStateLayout :=
  if mainnetRegistryEpoch slot < 364032 then .phase0Deneb else .electraFulu

def registrySlotGindex : RegistryStateLayout → Nat
  | .phase0Deneb => 34
  | .electraFulu => 66

def verifyMainnetStateSlot (slot : UInt64) (siblings : List ByteArray)
    (stateRoot : ByteArray) : Except RegistryError ByteProofResult :=
  let layout := mainnetRegistryLayout slot
  if siblings.length ≠ registryStateDepth layout then .error .branchLength
  else
    match uint64Root slot with
    | .error _ => .error .basicRoot
    | .ok leaf =>
      (verifyByteBranch (registryStateDepth layout) (registrySlotGindex layout)
        leaf.bytes siblings stateRoot).mapError RegistryError.proof

inductive MainnetSlotCandidateVerdict where
  | slotRootMismatch
  | stateVerdict (verdict : StateCandidateVerdict)
  deriving BEq, DecidableEq, Repr

/-- Check the slot and registry against one supplied state commitment.
    This fixes the epoch used in eligibility and the SSZ layout, conditional
    on that commitment; it does not authenticate the commitment or BLS votes. -/
def checkMainnetSlotCommonValidator (slot : UInt64)
    (prepared : PreparedAttesterSlashing) (index : UInt64)
    (length : Nat) (v : RegistryValidator) (siblings : List ByteArray)
    (registryRoot : ByteArray) (stateSiblings slotSiblings : List ByteArray)
    (stateRoot : ByteArray) : Except RegistryError MainnetSlotCandidateVerdict :=
  match verifyMainnetStateSlot slot slotSiblings stateRoot with
  | .error e => .error e
  | .ok result =>
    if result.matchesRoot then
      match checkStateCommonValidator (mainnetRegistryLayout slot) prepared
          (mainnetRegistryEpoch slot) index length v siblings registryRoot
          stateSiblings stateRoot with
      | .error e => .error e
      | .ok verdict => .ok (.stateVerdict verdict)
    else .ok .slotRootMismatch

/-- Kind: layout. Says: the slot field is at position 2 in each layout.
    Does not say: either supplied state is canonical. -/
theorem registrySlot_gindices :
    registrySlotGindex .phase0Deneb = 34 ∧ registrySlotGindex .electraFulu = 66 :=
  ⟨rfl, rfl⟩

/-- Kind: linkage. Says: the mainnet earlier layout is selected before Electra.
    Does not say: the slot is authenticated. -/
theorem mainnetRegistryLayout_before (slot : UInt64)
    (h : mainnetRegistryEpoch slot < 364032) :
    mainnetRegistryLayout slot = .phase0Deneb := by
  simp only [mainnetRegistryLayout, if_pos h]

/-- Kind: linkage. Says: Electra and the later layout are selected at the boundary.
    Does not say: future layout-changing forks are covered. -/
theorem mainnetRegistryLayout_after (slot : UInt64)
    (h : ¬ mainnetRegistryEpoch slot < 364032) :
    mainnetRegistryLayout slot = .electraFulu := by
  simp only [mainnetRegistryLayout, if_neg h]

/-- Kind: admission. Says: a wrong slot branch count is refused.
    Does not say: an admitted branch is valid. -/
theorem verifyMainnetStateSlot_bad_branch (slot : UInt64)
    (siblings : List ByteArray) (stateRoot : ByteArray)
    (h : siblings.length ≠ registryStateDepth (mainnetRegistryLayout slot)) :
    verifyMainnetStateSlot slot siblings stateRoot = .error .branchLength := by
  simp only [verifyMainnetStateSlot, if_pos h]

/-- Kind: linkage. Says: the slot proof checks the locally derived uint64 leaf
    and mainnet layout with concrete SHA-256. Does not say: the root is canonical. -/
theorem verifyMainnetStateSlot_delegates (slot : UInt64)
    (siblings : List ByteArray) (stateRoot : ByteArray) (leaf : Chunk)
    (h : siblings.length = registryStateDepth (mainnetRegistryLayout slot))
    (hl : uint64Root slot = .ok leaf) :
    verifyMainnetStateSlot slot siblings stateRoot =
      (verifyByteBranch (registryStateDepth (mainnetRegistryLayout slot))
        (registrySlotGindex (mainnetRegistryLayout slot)) leaf.bytes siblings
        stateRoot).mapError RegistryError.proof := by
  simp [verifyMainnetStateSlot, h, hl]

/-- Kind: linkage. Says: a mismatching slot proof prevents candidate admission.
    Does not say: the supplied root is canonical. -/
theorem checkMainnetSlotCommonValidator_mismatch (slot : UInt64)
    (p : PreparedAttesterSlashing) (index : UInt64) (length : Nat)
    (v : RegistryValidator) (siblings : List ByteArray) (registryRoot : ByteArray)
    (stateSiblings slotSiblings : List ByteArray) (stateRoot : ByteArray)
    (result : ByteProofResult)
    (hp : verifyMainnetStateSlot slot slotSiblings stateRoot = .ok result)
    (hm : result.matchesRoot = false) :
    checkMainnetSlotCommonValidator slot p index length v siblings registryRoot
      stateSiblings slotSiblings stateRoot = .ok .slotRootMismatch := by
  simp [checkMainnetSlotCommonValidator, hp, hm]

/-- Kind: linkage. Says: the candidate path receives the derived epoch,
    layout and identical state root only after the slot branch matches.
    Does not say: signatures or canonical chain history are authenticated. -/
theorem checkMainnetSlotCommonValidator_delegates (slot : UInt64)
    (p : PreparedAttesterSlashing) (index : UInt64) (length : Nat)
    (v : RegistryValidator) (siblings : List ByteArray) (registryRoot : ByteArray)
    (stateSiblings slotSiblings : List ByteArray) (stateRoot : ByteArray)
    (result : ByteProofResult) (verdict : StateCandidateVerdict)
    (hp : verifyMainnetStateSlot slot slotSiblings stateRoot = .ok result)
    (hm : result.matchesRoot = true)
    (hc : checkStateCommonValidator (mainnetRegistryLayout slot) p
      (mainnetRegistryEpoch slot) index length v siblings registryRoot
      stateSiblings stateRoot = .ok verdict) :
    checkMainnetSlotCommonValidator slot p index length v siblings registryRoot
      stateSiblings slotSiblings stateRoot = .ok (.stateVerdict verdict) := by
  simp [checkMainnetSlotCommonValidator, hp, hm, hc]

#print axioms EthereumConsensus.SSZ.registrySlot_gindices
#print axioms EthereumConsensus.SSZ.mainnetRegistryLayout_before
#print axioms EthereumConsensus.SSZ.mainnetRegistryLayout_after
#print axioms EthereumConsensus.SSZ.verifyMainnetStateSlot_bad_branch
#print axioms EthereumConsensus.SSZ.verifyMainnetStateSlot_delegates
#print axioms EthereumConsensus.SSZ.checkMainnetSlotCommonValidator_mismatch
#print axioms EthereumConsensus.SSZ.checkMainnetSlotCommonValidator_delegates

end EthereumConsensus.SSZ
