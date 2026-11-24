import EthereumConsensus.SSZ.BasicTypes

/-!
# Four fixed-shape beacon consensus SSZ containers

Independent Lean 4.33.1 source for BeaconBlockHeader, Checkpoint, ForkData
and SigningData. Only these four fixed layouts are admitted. The input
validator builds Chunk-typed roots before any container is constructed.
The existing repository-owned SHA-256 is invoked by hashPair.

Normative pin: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/beacon-chain.md; tracking factoidal-core #844 and #725.

These computed roots do not authenticate the caller's parent, state,
proposer, checkpoint or signature. No BLS or fork-choice rule is implied.
-/

namespace EthereumConsensus.SSZ

inductive ContainerError where
  | rootWidth
  | versionWidth
  | basicRoot
  deriving BEq, DecidableEq, Repr

/-- The only way bytes enter a Root field is through the 32-byte constructor. -/
def checkedContainerRoot (bytes : ByteArray) : Except ContainerError Chunk :=
  match Chunk.ofBytes bytes with
  | .ok root => .ok root
  | .error _ => .error .rootWidth

/-- The four-byte fork version is a basic SSZ byte vector. The version's
    field root is its four bytes followed by 28 zeros, not their digest. -/
def checkedVersionRoot (bytes : ByteArray) : Except ContainerError Chunk :=
  if bytes.size ≠ 4 then .error .versionWidth
  else
    match checkedBasicRoot bytes with
    | .ok root => .ok root
    | .error _ => .error .basicRoot

/-- Convert the existing uint64 basic codec to its SSZ Merkle chunk. -/
def containerUInt64Root (value : UInt64) : Except ContainerError Chunk :=
  match uint64Root value with
  | .ok root => .ok root
  | .error _ => .error .basicRoot

/-- The zero Merkle chunk is checked by the same basic-value root path. -/
def containerZeroRoot : Except ContainerError Chunk :=
  match checkedBasicRoot ByteArray.empty with
  | .ok root => .ok root
  | .error _ => .error .basicRoot

structure BeaconBlockHeader where
  slot : UInt64
  proposerIndex : UInt64
  parentRoot : Chunk
  stateRoot : Chunk
  bodyRoot : Chunk

structure Checkpoint where
  epoch : UInt64
  root : Chunk

structure ForkData where
  currentVersion : ByteArray
  versionRoot : Chunk
  genesisValidatorsRoot : Chunk

structure SigningData where
  objectRoot : Chunk
  domain : Chunk

/-- Admit all three 32-byte fields before constructing a typed header. -/
def checkedBeaconBlockHeader (slot proposerIndex : UInt64)
    (parentRoot stateRoot bodyRoot : ByteArray) :
    Except ContainerError BeaconBlockHeader :=
  match checkedContainerRoot parentRoot with
  | .error e => .error e
  | .ok parent =>
    match checkedContainerRoot stateRoot with
    | .error e => .error e
    | .ok state =>
      match checkedContainerRoot bodyRoot with
      | .error e => .error e
      | .ok body => .ok ⟨slot, proposerIndex, parent, state, body⟩

def checkedCheckpoint (epoch : UInt64) (root : ByteArray) :
    Except ContainerError Checkpoint := do
  let checked ← checkedContainerRoot root
  return ⟨epoch, checked⟩

def checkedForkData (version genesisValidatorsRoot : ByteArray) :
    Except ContainerError ForkData := do
  let versionRoot ← checkedVersionRoot version
  let genesis ← checkedContainerRoot genesisValidatorsRoot
  return ⟨version, versionRoot, genesis⟩

def checkedSigningData (objectRoot domain : ByteArray) :
    Except ContainerError SigningData := do
  let object ← checkedContainerRoot objectRoot
  let checkedDomain ← checkedContainerRoot domain
  return ⟨object, checkedDomain⟩

/-- SSZ serialisation of each fixed-shape container is field concatenation;
    no offset words and no length mix-ins are present. -/
def beaconBlockHeaderWire (header : BeaconBlockHeader) : ByteArray :=
  encodeUInt64 header.slot ++ encodeUInt64 header.proposerIndex ++
    header.parentRoot.bytes ++ header.stateRoot.bytes ++ header.bodyRoot.bytes

def checkpointWire (checkpoint : Checkpoint) : ByteArray :=
  encodeUInt64 checkpoint.epoch ++ checkpoint.root.bytes

def forkDataWire (fork : ForkData) : ByteArray :=
  fork.currentVersion ++ fork.genesisValidatorsRoot.bytes

def signingDataWire (signing : SigningData) : ByteArray :=
  signing.objectRoot.bytes ++ signing.domain.bytes

/-- A five-field SSZ container occupies eight leaf slots. In order:
    slot, proposer index, parent, state, body, zero, zero, zero.
    Exactly seven ordered SHA-256 parent hashes produce the root. -/
def beaconHeaderTree (slot proposer parent state body zero : Chunk) : Chunk :=
  hashPair
    (hashPair (hashPair slot proposer) (hashPair parent state))
    (hashPair (hashPair body zero) (hashPair zero zero))

/-- The actual typed header entry calls the existing executable basic-root
    codec and then beaconHeaderTree. The zero leaf cannot be caller-supplied. -/
def beaconBlockHeaderRoot (header : BeaconBlockHeader) :
    Except ContainerError Chunk :=
  match containerUInt64Root header.slot with
  | .error e => .error e
  | .ok slotRoot =>
    match containerUInt64Root header.proposerIndex with
    | .error e => .error e
    | .ok proposerRoot =>
      match containerZeroRoot with
      | .error e => .error e
      | .ok zeroRoot => .ok (beaconHeaderTree slotRoot proposerRoot
          header.parentRoot header.stateRoot header.bodyRoot zeroRoot)

def checkpointRoot (checkpoint : Checkpoint) : Except ContainerError Chunk := do
  let epochRoot ← containerUInt64Root checkpoint.epoch
  return hashPair epochRoot checkpoint.root

def forkDataRoot (fork : ForkData) : Chunk :=
  hashPair fork.versionRoot fork.genesisValidatorsRoot

def signingDataRoot (signing : SigningData) : Chunk :=
  hashPair signing.objectRoot signing.domain

/-- Kind: admission. Says: the actual Root constructor rejects any
    non-32-byte wire value. Does not say: the bytes are authenticated. -/
theorem checkedContainerRoot_wrong_width (bytes : ByteArray)
    (h : bytes.size ≠ 32) :
    checkedContainerRoot bytes = .error .rootWidth := by
  simp [checkedContainerRoot, Chunk.ofBytes, h]

/-- Kind: admission. Says: a four-byte fork version is required before
    its padded field root is built. Does not say: the fork is activated. -/
theorem checkedVersionRoot_wrong_width (bytes : ByteArray)
    (h : bytes.size ≠ 4) :
    checkedVersionRoot bytes = .error .versionWidth := by
  simp only [checkedVersionRoot, if_neg h]

/-- Kind: admission. Says: malformed parent bytes never construct a
    header with a substituted parent. Does not say: a 32-byte parent exists. -/
theorem checkedBeaconBlockHeader_bad_parent
    (slot proposer : UInt64) (parent state body : ByteArray)
    (h : parent.size ≠ 32) :
    checkedBeaconBlockHeader slot proposer parent state body =
      .error .rootWidth := by
  simp only [checkedBeaconBlockHeader, checkedContainerRoot_wrong_width parent h]

/-- Kind: structure. Says: one header byte encoding has precisely the
    five declared field widths and the canonical field order. -/
theorem beaconBlockHeaderWire_size (header : BeaconBlockHeader) :
    (beaconBlockHeaderWire header).size = 112 := by
  simp only [beaconBlockHeaderWire, ByteArray.size_append, encodeUInt64_size,
    header.parentRoot.width, header.stateRoot.width, header.bodyRoot.width] <;> decide

/-- Kind: structure. Says: the root path has exactly the seven ordered
    parent hashes of five field roots and three zeros. Does not say:
    the SHA-256 permutation is independently proved correct. -/
theorem beaconHeaderTree_ordered (slot proposer parent state body zero : Chunk) :
    beaconHeaderTree slot proposer parent state body zero =
      hashPair
        (hashPair (hashPair slot proposer) (hashPair parent state))
        (hashPair (hashPair body zero) (hashPair zero zero)) := by
  rfl

/-- Kind: implementation linkage. Says: when the three actual basic
    root constructors return their checked nodes, the public header
    entry uses the same executable eight-leaf Merkle tree. -/
theorem beaconBlockHeaderRoot_delegates (header : BeaconBlockHeader)
    (slot proposer zero : Chunk)
    (hs : containerUInt64Root header.slot = .ok slot)
    (hp : containerUInt64Root header.proposerIndex = .ok proposer)
    (hz : containerZeroRoot = .ok zero) :
    beaconBlockHeaderRoot header =
      .ok (beaconHeaderTree slot proposer header.parentRoot
        header.stateRoot header.bodyRoot zero) := by
  simp only [beaconBlockHeaderRoot, hs, hp, hz]

/-- Kind: structure. Checkpoint has exactly one uint64 and one Root.
    Does not say: the checkpoint is justified or finalised. -/
theorem checkpointWire_size (checkpoint : Checkpoint) :
    (checkpointWire checkpoint).size = 40 := by
  simp only [checkpointWire, ByteArray.size_append, encodeUInt64_size,
    checkpoint.root.width] <;> decide

/-- Kind: structure. SigningData uses its two 32-byte fields in order.
    Does not say: a BLS signature was checked. -/
theorem signingDataRoot_ordered (value : SigningData) :
    signingDataRoot value = hashPair value.objectRoot value.domain := by
  rfl

/-- Kind: structure. ForkData uses the checked padded version chunk
    and the genesis validators root, in that order. -/
theorem forkDataRoot_ordered (value : ForkData) :
    forkDataRoot value = hashPair value.versionRoot value.genesisValidatorsRoot := by
  rfl

/-- Kind: structure. A signing payload is exactly two SSZ Root fields. -/
theorem signingDataWire_size (value : SigningData) :
    (signingDataWire value).size = 64 := by
  simp only [signingDataWire, ByteArray.size_append,
    value.objectRoot.width, value.domain.width] <;> decide

private def hasError (r : Except ContainerError α) (expected : ContainerError) : Bool :=
  match r with
  | .error error => error == expected
  | .ok _ => false

#guard hasError (checkedContainerRoot ByteArray.empty) .rootWidth
#guard hasError (checkedVersionRoot ByteArray.empty) .versionWidth
#guard hasError (checkedBeaconBlockHeader 0 0 ByteArray.empty
  ByteArray.empty ByteArray.empty) .rootWidth
#guard hasError (checkedCheckpoint 0 ByteArray.empty) .rootWidth
#guard hasError (checkedForkData ByteArray.empty ByteArray.empty) .versionWidth
#guard hasError (checkedSigningData ByteArray.empty ByteArray.empty) .rootWidth
#guard (containerZeroRoot.toOption.map (fun root => root.bytes.size)) == some 32
#guard (containerUInt64Root 18446744073709551615 |>.toOption.map
  (fun root => root.bytes.size)) == some 32

#print axioms EthereumConsensus.SSZ.checkedContainerRoot_wrong_width
#print axioms EthereumConsensus.SSZ.checkedVersionRoot_wrong_width
#print axioms EthereumConsensus.SSZ.checkedBeaconBlockHeader_bad_parent
#print axioms EthereumConsensus.SSZ.beaconBlockHeaderWire_size
#print axioms EthereumConsensus.SSZ.beaconHeaderTree_ordered
#print axioms EthereumConsensus.SSZ.beaconBlockHeaderRoot_delegates
#print axioms EthereumConsensus.SSZ.checkpointWire_size
#print axioms EthereumConsensus.SSZ.signingDataRoot_ordered
#print axioms EthereumConsensus.SSZ.forkDataRoot_ordered
#print axioms EthereumConsensus.SSZ.signingDataWire_size

end EthereumConsensus.SSZ
