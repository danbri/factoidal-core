import EthereumConsensus.SSZ.ValidatorRegistry

/-! Independent proposer-slashing preparation, conditional on one supplied
BeaconState commitment. Normative target: consensus-specs at
d2021d2719235f0df4726a1d330502cb15aa8ea3, process_proposer_slashing.
This does not verify BLS signatures or mutate state. -/
namespace EthereumConsensus.SSZ

inductive ProposerEvidenceError where
  | differentSlot
  | differentProposer
  | identicalHeaders
  | context (error : StateSigningError)
  | registry (error : RegistryError)
  | slotMismatch
  | registryMismatch
  | validatorMismatch
  | notSlashable
  | signing (error : DomainError)

structure ProposerEvidence where
  publicKey : ByteArray
  firstSigningRoot : Chunk
  secondSigningRoot : Chunk

def prepareProposerRoots (c : ForkContext) (a b : BeaconBlockHeader)
    (key : ByteArray) : Except ProposerEvidenceError ProposerEvidence :=
  match headerProposerSigningRoot c a with
  | .error e => .error (.signing e)
  | .ok first =>
    match headerProposerSigningRoot c b with
    | .error e => .error (.signing e)
    | .ok second => .ok ⟨key, first.signingRoot, second.signingRoot⟩

/-- The current epoch is derived from the proved state slot. The signing
    epoch is derived separately by headerProposerSigningRoot. -/
def checkProposerRegistry (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (length : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (registryRoot : ByteArray)
    (registrySiblings : List ByteArray) (stateRoot : ByteArray) :
    Except ProposerEvidenceError ProposerEvidence :=
  match verifyRegistryInState (mainnetRegistryLayout slot)
      registryRoot registrySiblings stateRoot with
  | .error e => .error (.registry e)
  | .ok registryProof =>
    if registryProof.matchesRoot then
      match verifyValidatorAt length a.proposerIndex.toNat v siblings registryRoot with
      | .error e => .error (.registry e)
      | .ok member =>
        if member.matchesRoot then
          if isSlashableValidator v (mainnetRegistryEpoch slot) then
            prepareProposerRoots c a b v.publicKey
          else .error .notSlashable
        else .error .validatorMismatch
    else .error .registryMismatch

def checkProposerState (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (length : Nat) (v : RegistryValidator)
    (siblings : List ByteArray) (registryRoot : ByteArray)
    (registrySiblings slotSiblings forkSiblings genesisSiblings : List ByteArray)
    (stateRoot : ByteArray) : Except ProposerEvidenceError ProposerEvidence :=
  if a.slot ≠ b.slot then .error .differentSlot
  else if a.proposerIndex ≠ b.proposerIndex then .error .differentProposer
  else if a.parentRoot.bytes == b.parentRoot.bytes &&
    a.stateRoot.bytes == b.stateRoot.bytes && a.bodyRoot.bytes == b.bodyRoot.bytes then
    .error .identicalHeaders
  else
    match verifyStateSigningContext slot c forkSiblings genesisSiblings stateRoot with
    | .error e => .error (.context e)
    | .ok _ =>
      match verifyMainnetStateSlot slot slotSiblings stateRoot with
      | .error e => .error (.registry e)
      | .ok proof =>
        if proof.matchesRoot then
          checkProposerRegistry slot a b c length v siblings registryRoot registrySiblings stateRoot
        else .error .slotMismatch

/-- Kind: admission. Says: unequal slots refuse. Does not say: signatures are valid. -/
theorem checkProposerState_different_slot (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray) (root : ByteArray)
    (h : a.slot ≠ b.slot) :
    checkProposerState slot a b c len v ss rr rs sl fs gs root = .error .differentSlot := by
  simp only [checkProposerState, if_pos h]

/-- Kind: admission. Says: unequal proposers refuse after slot equality.
    Does not say: the proposer was selected by consensus. -/
theorem checkProposerState_different_proposer (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray) (root : ByteArray)
    (hs : a.slot = b.slot) (hi : a.proposerIndex ≠ b.proposerIndex) :
    checkProposerState slot a b c len v ss rr rs sl fs gs root = .error .differentProposer := by
  simp [checkProposerState, hs, hi]

/-- Kind: admission. Says: all three field comparisons being true refuses
    after slot and index equality. Does not assume hash collision resistance. -/
theorem checkProposerState_identical (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray) (root : ByteArray)
    (hs : a.slot = b.slot) (hi : a.proposerIndex = b.proposerIndex)
    (he : (a.parentRoot.bytes == b.parentRoot.bytes &&
      a.stateRoot.bytes == b.stateRoot.bytes && a.bodyRoot.bytes == b.bodyRoot.bytes) = true) :
    checkProposerState slot a b c len v ss rr rs sl fs gs root = .error .identicalHeaders := by
  simp [checkProposerState, hs, hi, he]

/-- Kind: linkage. Says: context errors propagate. Does not authenticate the root. -/
theorem checkProposerState_bad_context (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray) (root : ByteArray)
    (hs : a.slot = b.slot) (hi : a.proposerIndex = b.proposerIndex)
    (he : (a.parentRoot.bytes == b.parentRoot.bytes &&
      a.stateRoot.bytes == b.stateRoot.bytes && a.bodyRoot.bytes == b.bodyRoot.bytes) = false)
    (e : StateSigningError) (hc : verifyStateSigningContext slot c fs gs root = .error e) :
    checkProposerState slot a b c len v ss rr rs sl fs gs root = .error (.context e) := by
  simp [checkProposerState, hs, hi, he, hc]

/-- Kind: linkage. Says: a mismatching slot proof prevents registry use.
    Does not say: the supplied state root is canonical. -/
theorem checkProposerState_slot_mismatch (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray) (root : ByteArray)
    (hs : a.slot = b.slot) (hi : a.proposerIndex = b.proposerIndex)
    (he : (a.parentRoot.bytes == b.parentRoot.bytes &&
      a.stateRoot.bytes == b.stateRoot.bytes && a.bodyRoot.bytes == b.bodyRoot.bytes) = false)
    (hc : verifyStateSigningContext slot c fs gs root = .ok ())
    (proof : ByteProofResult) (hp : verifyMainnetStateSlot slot sl root = .ok proof)
    (hm : proof.matchesRoot = false) :
    checkProposerState slot a b c len v ss rr rs sl fs gs root = .error .slotMismatch := by
  simp [checkProposerState, hs, hi, he, hc, hp, hm]

/-- Kind: linkage. Says: the public state path delegates only with matching
    slot and context. Does not establish signature validity. -/
theorem checkProposerState_delegates (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs sl fs gs : List ByteArray) (root : ByteArray)
    (hs : a.slot = b.slot) (hi : a.proposerIndex = b.proposerIndex)
    (he : (a.parentRoot.bytes == b.parentRoot.bytes &&
      a.stateRoot.bytes == b.stateRoot.bytes && a.bodyRoot.bytes == b.bodyRoot.bytes) = false)
    (hc : verifyStateSigningContext slot c fs gs root = .ok ())
    (proof : ByteProofResult) (hp : verifyMainnetStateSlot slot sl root = .ok proof)
    (hm : proof.matchesRoot = true) :
    checkProposerState slot a b c len v ss rr rs sl fs gs root =
      checkProposerRegistry slot a b c len v ss rr rs root := by
  simp [checkProposerState, hs, hi, he, hc, hp, hm]

/-- Kind: linkage. Says: a mismatching registry root stops the candidate.
    Does not say: any matching commitment is canonical. -/
theorem checkProposerRegistry_mismatch (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs : List ByteArray) (root : ByteArray)
    (proof : ByteProofResult)
    (hp : verifyRegistryInState (mainnetRegistryLayout slot) rr rs root = .ok proof)
    (hm : proof.matchesRoot = false) :
    checkProposerRegistry slot a b c len v ss rr rs root = .error .registryMismatch := by
  simp [checkProposerRegistry, hp, hm]

/-- Kind: linkage. Says: a mismatching proposer membership cannot yield evidence.
    Does not say: membership checks a signature. -/
theorem checkProposerRegistry_member_mismatch (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs : List ByteArray) (root : ByteArray)
    (proof member : ByteProofResult)
    (hp : verifyRegistryInState (mainnetRegistryLayout slot) rr rs root = .ok proof)
    (hm : proof.matchesRoot = true)
    (hv : verifyValidatorAt len a.proposerIndex.toNat v ss rr = .ok member)
    (hn : member.matchesRoot = false) :
    checkProposerRegistry slot a b c len v ss rr rs root = .error .validatorMismatch := by
  simp [checkProposerRegistry, hp, hm, hv, hn]

/-- Kind: linkage. Says: matching membership is insufficient if ineligible
    at the derived current state epoch. Does not prove canonical state. -/
theorem checkProposerRegistry_not_slashable (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs : List ByteArray) (root : ByteArray)
    (proof member : ByteProofResult)
    (hp : verifyRegistryInState (mainnetRegistryLayout slot) rr rs root = .ok proof)
    (hm : proof.matchesRoot = true)
    (hv : verifyValidatorAt len a.proposerIndex.toNat v ss rr = .ok member)
    (hn : member.matchesRoot = true)
    (he : isSlashableValidator v (mainnetRegistryEpoch slot) = false) :
    checkProposerRegistry slot a b c len v ss rr rs root = .error .notSlashable := by
  simp [checkProposerRegistry, hp, hm, hv, hn, he]

/-- Kind: linkage. Says: admitted registry preparation uses the actual
    validator key and both actual signing roots. Does not verify BLS. -/
theorem checkProposerRegistry_delegates (slot : UInt64) (a b : BeaconBlockHeader)
    (c : ForkContext) (len : Nat) (v : RegistryValidator)
    (ss : List ByteArray) (rr : ByteArray) (rs : List ByteArray) (root : ByteArray)
    (proof member : ByteProofResult)
    (hp : verifyRegistryInState (mainnetRegistryLayout slot) rr rs root = .ok proof)
    (hm : proof.matchesRoot = true)
    (hv : verifyValidatorAt len a.proposerIndex.toNat v ss rr = .ok member)
    (hn : member.matchesRoot = true)
    (he : isSlashableValidator v (mainnetRegistryEpoch slot) = true) :
    checkProposerRegistry slot a b c len v ss rr rs root =
      prepareProposerRoots c a b v.publicKey := by
  simp [checkProposerRegistry, hp, hm, hv, hn, he]

/-- Kind: linkage. Says: actual header signing outputs and key are returned
    without substitutions. Does not say: either header signature is valid. -/
theorem prepareProposerRoots_delegates (c : ForkContext) (a b : BeaconBlockHeader)
    (key : ByteArray) (first second : HeaderSigningResult)
    (ha : headerProposerSigningRoot c a = .ok first)
    (hb : headerProposerSigningRoot c b = .ok second) :
    prepareProposerRoots c a b key = .ok ⟨key, first.signingRoot, second.signingRoot⟩ := by
  simp only [prepareProposerRoots, ha, hb]

#print axioms EthereumConsensus.SSZ.checkProposerState_different_slot
#print axioms EthereumConsensus.SSZ.checkProposerState_different_proposer
#print axioms EthereumConsensus.SSZ.checkProposerState_identical
#print axioms EthereumConsensus.SSZ.checkProposerState_bad_context
#print axioms EthereumConsensus.SSZ.checkProposerState_slot_mismatch
#print axioms EthereumConsensus.SSZ.checkProposerState_delegates
#print axioms EthereumConsensus.SSZ.checkProposerRegistry_mismatch
#print axioms EthereumConsensus.SSZ.checkProposerRegistry_member_mismatch
#print axioms EthereumConsensus.SSZ.checkProposerRegistry_not_slashable
#print axioms EthereumConsensus.SSZ.checkProposerRegistry_delegates
#print axioms EthereumConsensus.SSZ.prepareProposerRoots_delegates

end EthereumConsensus.SSZ
