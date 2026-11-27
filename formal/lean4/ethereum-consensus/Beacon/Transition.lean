import Beacon.Block

/-!
# Slot processing and the state transition (Fulu)

`process_slot`, `process_slots` and `state_transition` of consensus-specs
v1.6.1. `processSlots` is the iterate of `slotStep`, and the number of
iterations is fixed before the first step (`Beacon/Theorems.lean`).
-/

namespace Beacon

def stateRoot (p : Preset) (s : BeaconState) : ByteArray := BeaconState.codec.root p s

/-- `process_slot`: cache the state root and the block root of the slot. -/
def processSlot (p : Preset) (s : BeaconState) : BeaconState :=
  let root := stateRoot p s
  let position := s.slot % p.slotsPerHistoricalRoot
  let s := { s with stateRoots := s.stateRoots.set! position root }
  let s :=
    if s.latestBlockHeader.stateRoot == zero32 then
      { s with latestBlockHeader := { s.latestBlockHeader with stateRoot := root } }
    else s
  { s with blockRoots := s.blockRoots.set! position (BeaconBlockHeader.codec.root p s.latestBlockHeader) }

/-- One iteration of `process_slots`: the slot's caches, epoch processing
    at the last slot of an epoch, then the slot number. The slot number is
    written from the value read at the start; a step that changed it is
    refused. -/
def slotStep (c : Ctx) (s : BeaconState) : Except String BeaconState :=
  let slot := s.slot
  if slot ≥ uint64Max then .error "process_slots: slot number at the uint64 limit"
  else
    let s := processSlot c.p s
    match (if (slot + 1) % c.p.slotsPerEpoch == 0 then processEpoch c s else .ok s) with
    | .error e => .error e
    | .ok s =>
      if s.slot ≠ slot then .error "process_slots: slot changed inside a slot step"
      else if !s.inRange then .error "process_slots: a uint64 field left its range"
      else .ok { s with slot := slot + 1 }

def iterateSlots (c : Ctx) : Nat → BeaconState → Except String BeaconState
  | 0, s => .ok s
  | n + 1, s =>
    match slotStep c s with
    | .error e => .error e
    | .ok s => iterateSlots c n s

/-- Largest number of slots one call may advance (an implementation
    resource limit, not a consensus rule): 2^24 slots. -/
def maxSlotAdvance : Nat := 16777216

def processSlots (c : Ctx) (s : BeaconState) (slot : Nat) : Except String BeaconState :=
  if s.slot < slot then
    if slot - s.slot > maxSlotAdvance then .error "process_slots: advance above the resource limit"
    else iterateSlots c (slot - s.slot) s
  else .error "process_slots: target slot is not after the state's slot"

def verifyBlockSignature (c : Ctx) (s : BeaconState) (signed : SignedBeaconBlock) : Bool :=
  match s.validators[signed.message.proposerIndex]? with
  | none => false
  | some proposer =>
    let p := c.p
    let root := signingRoot p (BeaconBlock.codec.root p signed.message)
      (getDomain p s domainBeaconProposer (currentEpoch p s))
    blsVerify c proposer.pubkey root signed.signature

def stateTransition (c : Ctx) (s : BeaconState) (signed : SignedBeaconBlock) (validate : Bool := true) :
    Except String BeaconState := do
  let block := signed.message
  let s ← processSlots c s block.slot
  if validate then
    ensure (verifyBlockSignature c s signed) "state transition: invalid block signature"
  let s ← processBlock c s block
  if validate then
    ensure (block.stateRoot == stateRoot c.p s) "state transition: state root mismatch"
  return s

end Beacon
