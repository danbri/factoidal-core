import EthereumConsensus.SSZ.ContainerRoots

/-!
# Signature domains and proposer-header signing roots

Normative target: consensus-specs d2021d2719235f0df4726a1d330502cb15aa8ea3,
phase0 beacon-chain.md. Explicit fork context; no implicit chain defaults.
The supplied state context is not authenticated. No BLS operation.
-/
namespace EthereumConsensus.SSZ

inductive DomainError where
  | domainTypeWidth
  | versionWidth
  | container (error : ContainerError)
  deriving BEq, DecidableEq, Repr

structure ForkContext where
  previousVersion : ByteArray
  currentVersion : ByteArray
  activationEpoch : UInt64
  genesisValidatorsRoot : ByteArray

def selectSigningVersion (context : ForkContext) (epoch : UInt64) : ByteArray :=
  if epoch < context.activationEpoch then context.previousVersion
  else context.currentVersion

/-- Assemble the protocol domain from the type and the first 28 bytes of
    the actual checked fork-data Merkle root. -/
def computeSigningDomain (domainType version genesis : ByteArray) :
    Except DomainError Chunk :=
  if domainType.size ≠ 4 then .error .domainTypeWidth
  else
    match checkedForkData version genesis with
    | .error e => .error (.container e)
    | .ok fork =>
      (checkedContainerRoot
        (domainType ++ (forkDataRoot fork).bytes.extract 0 28)).mapError DomainError.container

/-- Both fork versions must have the declared width, even when only one is used. -/
def getSigningDomain (context : ForkContext) (domainType : ByteArray)
    (epoch : UInt64) : Except DomainError Chunk :=
  if context.previousVersion.size ≠ 4 then .error .versionWidth
  else if context.currentVersion.size ≠ 4 then .error .versionWidth
  else computeSigningDomain domainType (selectSigningVersion context epoch)
    context.genesisValidatorsRoot

def proposerDomainType : ByteArray := ByteArray.mk #[0, 0, 0, 0]

structure HeaderSigningResult where
  objectRoot : Chunk
  domain : Chunk
  signingRoot : Chunk

/-- Mainnet profile: 32 slots per epoch. Domain is derived here, not supplied
    by a caller. The header root is the actual fixed-container root. -/
def headerProposerSigningRoot (context : ForkContext) (header : BeaconBlockHeader) :
    Except DomainError HeaderSigningResult :=
  match getSigningDomain context proposerDomainType (header.slot / 32) with
  | .error e => .error e
  | .ok domain =>
    match beaconBlockHeaderRoot header with
    | .error e => .error (.container e)
    | .ok root => .ok ⟨root, domain, signingDataRoot ⟨root, domain⟩⟩

/-- Kind: selection. Says: the previous version is selected strictly before
    activation. Does not say: the context is canonical chain state. -/
theorem selectSigningVersion_before (context : ForkContext) (epoch : UInt64)
    (h : epoch < context.activationEpoch) :
    selectSigningVersion context epoch = context.previousVersion := by
  simp [selectSigningVersion, h]

/-- Kind: selection. Says: at and after activation use the current version.
    Does not say: the supplied activation epoch is authentic. -/
theorem selectSigningVersion_current (context : ForkContext) (epoch : UInt64)
    (h : ¬ epoch < context.activationEpoch) :
    selectSigningVersion context epoch = context.currentVersion := by
  simp [selectSigningVersion, h]

/-- Kind: admission. Says: an invalid domain type width refuses.
    Does not say: every four-byte type is protocol-valid in every context. -/
theorem computeSigningDomain_bad_type (domainType version genesis : ByteArray)
    (h : domainType.size ≠ 4) :
    computeSigningDomain domainType version genesis = .error .domainTypeWidth := by
  simp [computeSigningDomain, h]

/-- Kind: admission. Says: the unselected previous version cannot bypass
    the width check. Does not say: any supplied version is canonical. -/
theorem getSigningDomain_bad_previous (context : ForkContext) (t : ByteArray)
    (epoch : UInt64) (h : context.previousVersion.size ≠ 4) :
    getSigningDomain context t epoch = .error .versionWidth := by
  simp [getSigningDomain, h]

/-- Kind: admission. Says: the current version is checked even before activation.
    Does not say: the transition epoch is authenticated. -/
theorem getSigningDomain_bad_current (context : ForkContext) (t : ByteArray)
    (epoch : UInt64) (hp : context.previousVersion.size = 4)
    (hc : context.currentVersion.size ≠ 4) :
    getSigningDomain context t epoch = .error .versionWidth := by
  simp [getSigningDomain, hp, hc]

/-- Kind: linkage. Says: after successful fork-data admission the domain
    entry uses the exact ordered bytes of the actual Merkle root.
    Does not say: SHA-256 is proved against FIPS or collision-free. -/
theorem computeSigningDomain_delegates (t version genesis : ByteArray) (fork : ForkData)
    (ht : t.size = 4) (hf : checkedForkData version genesis = .ok fork) :
    computeSigningDomain t version genesis =
      (checkedContainerRoot (t ++ (forkDataRoot fork).bytes.extract 0 28)).mapError
        DomainError.container := by
  simp [computeSigningDomain, ht, hf]

/-- Kind: linkage. Says: the header signing entry uses its derived proposer
    domain and actual header root to form SigningData.
    Does not say: a signature was checked or the header accepted by consensus. -/
theorem headerProposerSigningRoot_delegates (context : ForkContext)
    (header : BeaconBlockHeader) (domain root : Chunk)
    (hd : getSigningDomain context proposerDomainType (header.slot / 32) = .ok domain)
    (hr : beaconBlockHeaderRoot header = .ok root) :
    headerProposerSigningRoot context header =
      .ok ⟨root, domain, signingDataRoot ⟨root, domain⟩⟩ := by
  simp [headerProposerSigningRoot, hd, hr]

#print axioms EthereumConsensus.SSZ.selectSigningVersion_before
#print axioms EthereumConsensus.SSZ.selectSigningVersion_current
#print axioms EthereumConsensus.SSZ.computeSigningDomain_bad_type
#print axioms EthereumConsensus.SSZ.getSigningDomain_bad_previous
#print axioms EthereumConsensus.SSZ.getSigningDomain_bad_current
#print axioms EthereumConsensus.SSZ.computeSigningDomain_delegates
#print axioms EthereumConsensus.SSZ.headerProposerSigningRoot_delegates

end EthereumConsensus.SSZ
