import EthereumConsensus.SSZ.SigningDomains

/-! Fixed AttestationData SSZ and attester signing roots.
    Consensus-specs d2021d2719235f0df4726a1d330502cb15aa8ea3,
    phase0/beacon-chain.md. Context and checkpoint provenance are not
    authenticated; this module neither checks BLS nor accepts an attestation. -/
namespace EthereumConsensus.SSZ

structure AttestationData where
  slot : UInt64
  committeeIndex : UInt64
  beaconBlockRoot : Chunk
  source : Checkpoint
  target : Checkpoint

def checkedAttestationData (slot index : UInt64) (beacon : ByteArray)
    (sourceEpoch : UInt64) (sourceRoot : ByteArray)
    (targetEpoch : UInt64) (targetRoot : ByteArray) :
    Except ContainerError AttestationData :=
  match checkedContainerRoot beacon with
  | .error e => .error e
  | .ok beaconRoot =>
    match checkedCheckpoint sourceEpoch sourceRoot with
    | .error e => .error e
    | .ok source =>
      match checkedCheckpoint targetEpoch targetRoot with
      | .error e => .error e
      | .ok target => .ok ⟨slot, index, beaconRoot, source, target⟩

def attestationDataWire (data : AttestationData) : ByteArray :=
  encodeUInt64 data.slot ++ encodeUInt64 data.committeeIndex ++
    data.beaconBlockRoot.bytes ++ checkpointWire data.source ++ checkpointWire data.target

/-- Five field roots, in order, with the source and target represented by
    their own container roots; the remaining three leaves are zeros. -/
def attestationDataRoot (data : AttestationData) : Except ContainerError Chunk :=
  match containerUInt64Root data.slot with
  | .error e => .error e
  | .ok slot =>
    match containerUInt64Root data.committeeIndex with
    | .error e => .error e
    | .ok index =>
      match checkpointRoot data.source with
      | .error e => .error e
      | .ok source =>
        match checkpointRoot data.target with
        | .error e => .error e
        | .ok target =>
          match containerZeroRoot with
          | .error e => .error e
          | .ok zero => .ok (beaconHeaderTree slot index data.beaconBlockRoot source target zero)

def attesterDomainType : ByteArray := ByteArray.mk #[1, 0, 0, 0]

/-- The attester domain is selected by the target checkpoint epoch, not
    by slot or source epoch, as in indexed attestation verification. -/
def attesterSigningRoot (context : ForkContext) (data : AttestationData) :
    Except DomainError HeaderSigningResult :=
  match getSigningDomain context attesterDomainType data.target.epoch with
  | .error e => .error e
  | .ok domain =>
    match attestationDataRoot data with
    | .error e => .error (.container e)
    | .ok root => .ok ⟨root, domain, signingDataRoot ⟨root, domain⟩⟩

/-- Kind: admission. Says: invalid beacon root width refuses at the actual
    constructor. Does not say: well-sized roots are authenticated. -/
theorem checkedAttestationData_bad_beacon (slot index sourceEpoch targetEpoch : UInt64)
    (beacon sourceRoot targetRoot : ByteArray) (h : beacon.size ≠ 32) :
    checkedAttestationData slot index beacon sourceEpoch sourceRoot targetEpoch targetRoot =
      .error .rootWidth := by
  simp only [checkedAttestationData, checkedContainerRoot_wrong_width beacon h]

/-- Kind: structure. Says: wire has the five fixed fields, totalling
    128 bytes. Does not say: the data is a valid vote. -/
theorem attestationDataWire_size (data : AttestationData) :
    (attestationDataWire data).size = 128 := by
  simp only [attestationDataWire, ByteArray.size_append, encodeUInt64_size,
    data.beaconBlockRoot.width, checkpointWire_size] <;> decide

/-- Kind: linkage. Says: the actual root uses these five ordered field roots.
    Does not say: the underlying SHA-256 satisfies full FIPS refinement. -/
theorem attestationDataRoot_delegates (data : AttestationData)
    (slot index source target zero : Chunk)
    (hs : containerUInt64Root data.slot = .ok slot)
    (hi : containerUInt64Root data.committeeIndex = .ok index)
    (hc : checkpointRoot data.source = .ok source)
    (ht : checkpointRoot data.target = .ok target)
    (hz : containerZeroRoot = .ok zero) :
    attestationDataRoot data =
      .ok (beaconHeaderTree slot index data.beaconBlockRoot source target zero) := by
  simp only [attestationDataRoot, hs, hi, hc, ht, hz]

/-- Kind: linkage. Says: target epoch is the domain input of the actual
    signing entry. Does not say: signature verification took place. -/
theorem attesterSigningRoot_delegates (context : ForkContext)
    (data : AttestationData) (domain root : Chunk)
    (hd : getSigningDomain context attesterDomainType data.target.epoch = .ok domain)
    (hr : attestationDataRoot data = .ok root) :
    attesterSigningRoot context data =
      .ok ⟨root, domain, signingDataRoot ⟨root, domain⟩⟩ := by
  simp [attesterSigningRoot, hd, hr]

/-- Kind: refusal. Says: a domain error propagates unchanged.
    Does not say: the caller's context came from an authenticated state. -/
theorem attesterSigningRoot_bad_domain (context : ForkContext)
    (data : AttestationData) (error : DomainError)
    (h : getSigningDomain context attesterDomainType data.target.epoch = .error error) :
    attesterSigningRoot context data = .error error := by
  simp [attesterSigningRoot, h]

#print axioms EthereumConsensus.SSZ.checkedAttestationData_bad_beacon
#print axioms EthereumConsensus.SSZ.attestationDataWire_size
#print axioms EthereumConsensus.SSZ.attestationDataRoot_delegates
#print axioms EthereumConsensus.SSZ.attesterSigningRoot_delegates
#print axioms EthereumConsensus.SSZ.attesterSigningRoot_bad_domain

end EthereumConsensus.SSZ
