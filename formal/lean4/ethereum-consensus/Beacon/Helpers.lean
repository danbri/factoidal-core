import Beacon.Types
import BLSVerify
import Std.Data.HashMap

/-!
# Beacon state accessors, predicates and mutators (Fulu)

Written from the helper-function sections of consensus-specs v1.6.1
(`specs/phase0/beacon-chain.md` through `specs/fulu/beacon-chain.md`).
Signature checks call the repository's own BLS12-381 code in `BLSVerify`.

Arithmetic is on `Nat`: sums never wrap. Where the specification's `uint64`
arithmetic would raise on overflow, the transition checks the range
explicitly (`BeaconState.inRange`, used at the end of every block and slot).
-/

namespace Beacon

/-- Run-time context of a transition. -/
structure Ctx where
  p : Preset
  /-- `false` replaces every signature check by `true`; `true` runs the
      built-in BLS verification. -/
  verifyBls : Bool := true
  /-- The vectors' BLS-off mode (`bls_setting: 2`): besides skipping
      signature checks, aggregate public keys are the reference test
      suite's fixed stub value. Never set outside those vectors. -/
  blsOff : Bool := false
  /-- The execution engine's verdict on the payload. The engine link is
      outside this module; the vectors supply the verdict. -/
  executionValid : Bool := true

def uint64Max : Nat := 18446744073709551615

/-! ## BLS -/

/-- The compressed G2 point at infinity. -/
def g2Infinity : ByteArray := ⟨#[0xc0] ++ Array.replicate 95 0⟩

def natBE (n width : Nat) : ByteArray :=
  (List.range width).foldl (fun acc i => acc.push (UInt8.ofNat (n / 256 ^ (width - 1 - i) % 256)))
    (ByteArray.emptyWithCapacity width)

/-- Compressed encoding of a finite G1 point (flags: compressed, sign). -/
def compressG1 (q : EthereumConsensus.BLS.AffinePoint) : ByteArray :=
  natBE (2 ^ 383 + (if EthereumConsensus.BLS.largeY q.y then 2 ^ 381 else 0) + q.x) 48

def chunksOf {α : Type} (n : Nat) (xs : List α) : Nat → List (List α)
  | 0 => []
  | fuel + 1 => if xs.isEmpty then [] else xs.take n :: chunksOf n (xs.drop n) fuel

/-- Sum of public keys as a compressed key; `none` when a key is invalid,
    the list is empty or a partial sum is the point at infinity. Lists
    above the BLS module's limit are summed in groups of that size. -/
def aggregateKeys : Nat → List ByteArray → Option ByteArray
  | 0, _ => none
  | fuel + 1, keys =>
    if keys.length ≤ EthereumConsensus.BLS.maxAggregateKeys then
      match EthereumConsensus.BLS.aggregatePublicKeys keys with
      | .ok q => some (compressG1 q)
      | .error _ => none
    else
      let groups := chunksOf EthereumConsensus.BLS.maxAggregateKeys keys keys.length
      match groups.mapM (aggregateKeys fuel) with
      | some sums => aggregateKeys fuel sums
      | none => none

def blsVerify (c : Ctx) (pubkey root signature : ByteArray) : Bool :=
  if !c.verifyBls || c.blsOff then true
  else match EthereumConsensus.BLS.Verify.verifySigningRoot [pubkey] root signature with
    | .ok true => true
    | _ => false

def blsFastAggregateVerify (c : Ctx) (pubkeys : Array ByteArray) (root signature : ByteArray) : Bool :=
  if !c.verifyBls || c.blsOff then true
  else if pubkeys.size ≤ EthereumConsensus.BLS.maxAggregateKeys then
    match EthereumConsensus.BLS.Verify.verifySigningRoot pubkeys.toList root signature with
    | .ok true => true
    | _ => false
  else match aggregateKeys 4 pubkeys.toList with
    | some key => blsVerify c key root signature
    | none => false

def ethFastAggregateVerify (c : Ctx) (pubkeys : Array ByteArray) (root signature : ByteArray) : Bool :=
  if pubkeys.size == 0 && signature == g2Infinity then true
  else blsFastAggregateVerify c pubkeys root signature

/-! ## Arithmetic -/

def isqrtLoop (n : Nat) : Nat → Nat → Nat
  | 0, r => r
  | bit + 1, r =>
    let candidate := r + 2 ^ bit
    isqrtLoop n bit (if candidate * candidate ≤ n then candidate else r)

/-- Largest `r < 2 ^ 40` with `r * r ≤ n`; the integer square root for
    every `n < 2 ^ 80`. -/
def isqrt (n : Nat) : Nat := isqrtLoop n 40 0

def xorBytes (a b : ByteArray) : ByteArray :=
  ⟨(Array.range a.size).map fun i => a.get! i ^^^ b.get! i⟩

/-! ## Epochs, validators -/

def currentEpoch (p : Preset) (s : BeaconState) : Nat := s.slot / p.slotsPerEpoch

def previousEpoch (p : Preset) (s : BeaconState) : Nat :=
  let c := currentEpoch p s
  if c = 0 then 0 else c - 1

def startSlot (p : Preset) (epoch : Nat) : Nat := epoch * p.slotsPerEpoch

def activationExitEpoch (epoch : Nat) : Nat := epoch + 1 + maxSeedLookahead

def Validator.isActive (v : Validator) (epoch : Nat) : Bool :=
  v.activationEpoch ≤ epoch && epoch < v.exitEpoch

def Validator.isSlashable (v : Validator) (epoch : Nat) : Bool :=
  !v.slashed && v.activationEpoch ≤ epoch && epoch < v.withdrawableEpoch

def Validator.hasEth1Credential (v : Validator) : Bool := v.withdrawalCredentials.get! 0 == 1

def Validator.hasCompoundingCredential (v : Validator) : Bool := v.withdrawalCredentials.get! 0 == 2

def Validator.hasExecutionCredential (v : Validator) : Bool :=
  v.hasEth1Credential || v.hasCompoundingCredential

def Validator.maxEffectiveBalance (v : Validator) : Nat :=
  if v.hasCompoundingCredential then maxEffectiveBalanceElectra else minActivationBalance

def Validator.isEligibleForActivationQueue (v : Validator) : Bool :=
  v.activationEligibilityEpoch == farFutureEpoch && v.effectiveBalance ≥ minActivationBalance

def Validator.isFullyWithdrawable (v : Validator) (balance epoch : Nat) : Bool :=
  v.hasExecutionCredential && v.withdrawableEpoch ≤ epoch && balance > 0

def Validator.isPartiallyWithdrawable (v : Validator) (balance : Nat) : Bool :=
  v.hasExecutionCredential && v.effectiveBalance == v.maxEffectiveBalance && balance > v.maxEffectiveBalance

def activeIndices (s : BeaconState) (epoch : Nat) : Array Nat := Id.run do
  let mut out := Array.mkEmpty s.validators.size
  for i in [0:s.validators.size] do
    if s.validators[i]!.isActive epoch then out := out.push i
  return out

def totalActiveBalance (p : Preset) (s : BeaconState) : Nat :=
  let epoch := currentEpoch p s
  max effectiveBalanceIncrement
    (s.validators.foldl (fun acc v => if v.isActive epoch then acc + v.effectiveBalance else acc) 0)

def randaoMix (p : Preset) (s : BeaconState) (epoch : Nat) : ByteArray :=
  s.randaoMixes[epoch % p.epochsPerHistoricalVector]!

def getSeed (p : Preset) (s : BeaconState) (epoch : Nat) (domainType : ByteArray) : ByteArray :=
  sha (domainType ++ natLE epoch 8 ++
    randaoMix p s (epoch + p.epochsPerHistoricalVector - minSeedLookahead - 1))

def blockRootAtSlot (p : Preset) (s : BeaconState) (slot : Nat) : Except String ByteArray :=
  if slot < s.slot && s.slot ≤ slot + p.slotsPerHistoricalRoot then
    .ok s.blockRoots[slot % p.slotsPerHistoricalRoot]!
  else .error "block root requested for a slot outside the history window"

def blockRoot (p : Preset) (s : BeaconState) (epoch : Nat) : Except String ByteArray :=
  blockRootAtSlot p s (startSlot p epoch)

/-! ## Shuffling and committees -/

/-- `compute_shuffled_index`: the swap-or-not image of one index. -/
def shuffledIndex (p : Preset) (index count : Nat) (seed : ByteArray) : Nat :=
  (List.range p.shuffleRoundCount).foldl
    (fun index round =>
      let rb := seed.push (UInt8.ofNat round)
      let pivot := leNat (sha rb) 0 8 % count
      let flip := (pivot + count - index) % count
      let position := max index flip
      let source := sha (rb ++ natLE (position / 256) 4)
      let byte := (source.get! (position % 256 / 8)).toNat
      if byte / 2 ^ (position % 8) % 2 == 1 then flip else index)
    index

/-- One swap-or-not round applied to a whole array: positions `i` and
    `flip i` exchange their entries when the round's bit for the larger of
    the two is set. One hash per 256 positions. -/
def shuffleRound (seed : ByteArray) (round : Nat) (arr : Array Nat) : Array Nat := Id.run do
  let n := arr.size
  let rb := seed.push (UInt8.ofNat round)
  let pivot := leNat (sha rb) 0 8 % n
  let sources := (Array.range ((n + 255) / 256)).map fun block => sha (rb ++ natLE block 4)
  let mut a := arr
  for i in [0:n] do
    let flip := (pivot + n - i) % n
    if i < flip then
      let byte := (sources[flip / 256]!.get! (flip % 256 / 8)).toNat
      if byte / 2 ^ (flip % 8) % 2 == 1 then
        let x := a[i]!
        let y := a[flip]!
        a := (a.set! i y).set! flip x
  return a

/-- `out[i] = arr[shuffledIndex i]` for every `i`: rounds are applied to the
    array from the last to the first. Tested equal to `shuffledIndex` on the
    vectors; not proved equal. -/
def shuffleList (p : Preset) (seed : ByteArray) (arr : Array Nat) : Array Nat :=
  if arr.size ≤ 1 then arr
  else (List.range p.shuffleRoundCount).foldr (fun round a => shuffleRound seed round a) arr

structure Shuffling where
  shuffled : Array Nat
  committeesPerSlot : Nat

def committeeCountPerSlot (p : Preset) (activeCount : Nat) : Nat :=
  max 1 (min p.maxCommitteesPerSlot (activeCount / p.slotsPerEpoch / p.targetCommitteeSize))

def getShuffling (p : Preset) (s : BeaconState) (epoch : Nat) : Shuffling :=
  let active := activeIndices s epoch
  ⟨shuffleList p (getSeed p s epoch domainBeaconAttester) active, committeeCountPerSlot p active.size⟩

/-- `get_beacon_committee` for a slot of the shuffling's epoch. -/
def Shuffling.committee (p : Preset) (sh : Shuffling) (slot index : Nat) : Array Nat :=
  let count := sh.committeesPerSlot * p.slotsPerEpoch
  let i := (slot % p.slotsPerEpoch) * sh.committeesPerSlot + index
  let n := sh.shuffled.size
  sh.shuffled.extract (n * i / count) (n * (i + 1) / count)

/-- Bound on the candidate loop of `compute_proposer_index`. -/
def proposerSearchLimit : Nat := 1048576

def proposerLoop (p : Preset) (s : BeaconState) (indices : Array Nat) (seed : ByteArray) :
    Nat → Nat → Except String Nat
  | 0, _ => .error "proposer selection: candidate limit reached"
  | fuel + 1, i =>
    let total := indices.size
    let candidate := indices[shuffledIndex p (i % total) total seed]!
    let randomBytes := sha (seed ++ natLE (i / 16) 8)
    let randomValue := leNat randomBytes (i % 16 * 2) 2
    let effective := s.validators[candidate]!.effectiveBalance
    if effective * 65535 ≥ maxEffectiveBalanceElectra * randomValue then .ok candidate
    else proposerLoop p s indices seed fuel (i + 1)

def computeProposerIndex (p : Preset) (s : BeaconState) (indices : Array Nat) (seed : ByteArray) :
    Except String Nat :=
  if indices.size = 0 then .error "proposer selection: no active validators"
  else proposerLoop p s indices seed proposerSearchLimit 0

/-- `get_beacon_proposer_indices`: the proposers of every slot of `epoch`. -/
def beaconProposerIndices (p : Preset) (s : BeaconState) (epoch : Nat) : Except String (Array Nat) :=
  let indices := activeIndices s epoch
  let seed := getSeed p s epoch domainBeaconProposer
  (Array.range p.slotsPerEpoch).mapM fun i =>
    computeProposerIndex p s indices (sha (seed ++ natLE (startSlot p epoch + i) 8))

/-- `get_beacon_proposer_index` (Fulu): read from the lookahead. -/
def beaconProposerIndex (p : Preset) (s : BeaconState) : Nat :=
  s.proposerLookahead[s.slot % p.slotsPerEpoch]!

/-! ## Domains and signing roots -/

def computeDomain (p : Preset) (domainType version genesisValidatorsRoot : ByteArray) : ByteArray :=
  domainType ++ (ForkData.codec.root p ⟨version, genesisValidatorsRoot⟩).extract 0 28

def getDomain (p : Preset) (s : BeaconState) (domainType : ByteArray) (epoch : Nat) : ByteArray :=
  let version := if epoch < s.fork.epoch then s.fork.previousVersion else s.fork.currentVersion
  computeDomain p domainType version s.genesisValidatorsRoot

def signingRoot (p : Preset) (objectRoot domain : ByteArray) : ByteArray :=
  SigningData.codec.root p ⟨objectRoot, domain⟩

/-! ## Rewards -/

def baseRewardPerIncrement (totalActive : Nat) : Nat :=
  effectiveBalanceIncrement * baseRewardFactor / isqrt totalActive

def hasFlag (flags : UInt8) (index : Nat) : Bool := flags.toNat / 2 ^ index % 2 == 1

def addFlag (flags : UInt8) (index : Nat) : UInt8 :=
  if hasFlag flags index then flags else UInt8.ofNat (flags.toNat + 2 ^ index)

def flagWeight (index : Nat) : Nat :=
  if index == timelySourceFlagIndex then timelySourceWeight
  else if index == timelyTargetFlagIndex then timelyTargetWeight
  else timelyHeadWeight

/-- Membership test for `get_unslashed_participating_indices` at the
    previous epoch. -/
def unslashedParticipatingPrevious (p : Preset) (s : BeaconState) (flag i : Nat) : Bool :=
  let v := s.validators[i]!
  v.isActive (previousEpoch p s) && !v.slashed && hasFlag (s.previousEpochParticipation.get! i) flag

def unslashedParticipatingCurrent (p : Preset) (s : BeaconState) (flag i : Nat) : Bool :=
  let v := s.validators[i]!
  v.isActive (currentEpoch p s) && !v.slashed && hasFlag (s.currentEpochParticipation.get! i) flag

def isInInactivityLeak (p : Preset) (s : BeaconState) : Bool :=
  previousEpoch p s - s.finalizedCheckpoint.epoch > minEpochsToInactivityPenalty

def isEligibleValidator (p : Preset) (s : BeaconState) (v : Validator) : Bool :=
  let previous := previousEpoch p s
  v.isActive previous || (v.slashed && previous + 1 < v.withdrawableEpoch)

/-! ## Balances and churn -/

def BeaconState.increaseBalance (s : BeaconState) (index delta : Nat) : BeaconState :=
  { s with balances := s.balances.modify index (· + delta) }

/-- `decrease_balance`: subtraction that stops at zero. -/
def BeaconState.decreaseBalance (s : BeaconState) (index delta : Nat) : BeaconState :=
  { s with balances := s.balances.modify index (· - delta) }

def balanceChurnLimit (p : Preset) (s : BeaconState) : Nat :=
  let churn := max p.minPerEpochChurnLimitElectra (totalActiveBalance p s / p.churnLimitQuotient)
  churn - churn % effectiveBalanceIncrement

def activationExitChurnLimit (p : Preset) (s : BeaconState) : Nat :=
  min p.maxPerEpochActivationExitChurnLimit (balanceChurnLimit p s)

def consolidationChurnLimit (p : Preset) (s : BeaconState) : Nat :=
  balanceChurnLimit p s - activationExitChurnLimit p s

def pendingBalanceToWithdraw (s : BeaconState) (index : Nat) : Nat :=
  s.pendingPartialWithdrawals.foldl (fun acc w => if w.validatorIndex == index then acc + w.amount else acc) 0

/-- `compute_exit_epoch_and_update_churn` with the per-epoch churn supplied
    by the caller (it is constant while effective balances and the active
    set of the current epoch do not change). -/
def exitEpochAndUpdateChurn (p : Preset) (perEpochChurn : Nat) (s : BeaconState) (exitBalance : Nat) :
    BeaconState × Nat :=
  let earliest := max s.earliestExitEpoch (activationExitEpoch (currentEpoch p s))
  let toConsume := if s.earliestExitEpoch < earliest then perEpochChurn else s.exitBalanceToConsume
  let (earliest, toConsume) :=
    if exitBalance > toConsume then
      let additional := (exitBalance - toConsume - 1) / perEpochChurn + 1
      (earliest + additional, toConsume + additional * perEpochChurn)
    else (earliest, toConsume)
  ({ s with exitBalanceToConsume := toConsume - exitBalance, earliestExitEpoch := earliest }, earliest)

def consolidationEpochAndUpdateChurn (p : Preset) (s : BeaconState) (balance : Nat) : BeaconState × Nat :=
  let perEpochChurn := consolidationChurnLimit p s
  let earliest := max s.earliestConsolidationEpoch (activationExitEpoch (currentEpoch p s))
  let toConsume :=
    if s.earliestConsolidationEpoch < earliest then perEpochChurn else s.consolidationBalanceToConsume
  let (earliest, toConsume) :=
    if balance > toConsume then
      let additional := (balance - toConsume - 1) / perEpochChurn + 1
      (earliest + additional, toConsume + additional * perEpochChurn)
    else (earliest, toConsume)
  ({ s with consolidationBalanceToConsume := toConsume - balance, earliestConsolidationEpoch := earliest },
    earliest)

/-- `initiate_validator_exit` with the activation-exit churn supplied. -/
def initiateValidatorExitWith (p : Preset) (perEpochChurn : Nat) (s : BeaconState) (index : Nat) :
    BeaconState :=
  let v := s.validators[index]!
  if v.exitEpoch != farFutureEpoch then s
  else
    let (s, exitEpoch) := exitEpochAndUpdateChurn p perEpochChurn s v.effectiveBalance
    { s with validators := s.validators.modify index fun v =>
        { v with exitEpoch := exitEpoch, withdrawableEpoch := exitEpoch + p.minValidatorWithdrawabilityDelay } }

def initiateValidatorExit (p : Preset) (s : BeaconState) (index : Nat) : BeaconState :=
  initiateValidatorExitWith p (activationExitChurnLimit p s) s index

def queueExcessActiveBalance (s : BeaconState) (index : Nat) : BeaconState :=
  let balance := s.balances[index]!
  if balance > minActivationBalance then
    let v := s.validators[index]!
    { s with
      balances := s.balances.set! index minActivationBalance
      pendingDeposits := s.pendingDeposits.push
        { pubkey := v.pubkey, withdrawalCredentials := v.withdrawalCredentials,
          amount := balance - minActivationBalance, signature := g2Infinity, slot := genesisSlot } }
  else s

def switchToCompounding (s : BeaconState) (index : Nat) : BeaconState :=
  let s := { s with validators := s.validators.modify index fun v =>
    { v with withdrawalCredentials := v.withdrawalCredentials.set! 0 2 } }
  queueExcessActiveBalance s index

/-- `slash_validator`; the whistleblower is the proposer when `none`. -/
def slashValidator (p : Preset) (s : BeaconState) (slashedIndex : Nat) (whistleblower : Option Nat := none) :
    BeaconState :=
  let epoch := currentEpoch p s
  let s := initiateValidatorExit p s slashedIndex
  let s := { s with validators := s.validators.modify slashedIndex fun v =>
    { v with slashed := true, withdrawableEpoch := max v.withdrawableEpoch (epoch + p.epochsPerSlashingsVector) } }
  let effective := s.validators[slashedIndex]!.effectiveBalance
  let s := { s with slashings := s.slashings.modify (epoch % p.epochsPerSlashingsVector) (· + effective) }
  let s := s.decreaseBalance slashedIndex (effective / minSlashingPenaltyQuotientElectra)
  let proposer := beaconProposerIndex p s
  let whistleblowerIndex := whistleblower.getD proposer
  let whistleblowerReward := effective / whistleblowerRewardQuotientElectra
  let proposerReward := whistleblowerReward * proposerWeight / weightDenominator
  let s := s.increaseBalance proposer proposerReward
  s.increaseBalance whistleblowerIndex (whistleblowerReward - proposerReward)

/-- Index of each public key in the registry (first occurrence). -/
def pubkeyIndex (s : BeaconState) : Std.HashMap ByteArray Nat := Id.run do
  let mut m : Std.HashMap ByteArray Nat := Std.HashMap.emptyWithCapacity s.validators.size
  for i in [0:s.validators.size] do
    let key := s.validators[i]!.pubkey
    if !m.contains key then m := m.insert key i
  return m

def findValidator (s : BeaconState) (pubkey : ByteArray) : Option Nat :=
  s.validators.findIdx? (·.pubkey == pubkey)

/-- Every `uint64` field that arithmetic can move is inside the `uint64`
    range. The specification's arithmetic raises outside it. -/
def BeaconState.inRange (s : BeaconState) : Bool :=
  s.slot ≤ uint64Max && s.balances.all (· ≤ uint64Max) && s.slashings.all (· ≤ uint64Max) &&
  s.validators.all (fun v => v.exitEpoch ≤ uint64Max && v.withdrawableEpoch ≤ uint64Max &&
    v.activationEpoch ≤ uint64Max && v.activationEligibilityEpoch ≤ uint64Max) &&
  s.inactivityScores.all (· ≤ uint64Max) && s.earliestExitEpoch ≤ uint64Max &&
  s.earliestConsolidationEpoch ≤ uint64Max && s.nextWithdrawalIndex ≤ uint64Max &&
  s.eth1DepositIndex ≤ uint64Max && s.depositBalanceToConsume ≤ uint64Max &&
  s.pendingPartialWithdrawals.all (fun w => w.withdrawableEpoch ≤ uint64Max && w.amount ≤ uint64Max)

end Beacon
