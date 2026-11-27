import Beacon.Helpers

/-!
# Epoch processing (Fulu)

`process_epoch` and its sub-steps, from consensus-specs v1.6.1
(`specs/altair`, `capella`, `electra` and `fulu` `beacon-chain.md`).
Each step is a function of the state. Loops over the registry visit each
validator once; totals (active balance, participating balances, churn) are
computed once per step, never per validator.
-/

namespace Beacon

def processJustificationAndFinalization (p : Preset) (s : BeaconState) : Except String BeaconState := do
  let current := currentEpoch p s
  if current ≤ genesisEpoch + 1 then return s
  let previous := previousEpoch p s
  let total := totalActiveBalance p s
  let (previousSum, currentSum) := (Array.range s.validators.size).foldl
    (fun (acc : Nat × Nat) i =>
      let e := s.validators[i]!.effectiveBalance
      (if unslashedParticipatingPrevious p s timelyTargetFlagIndex i then acc.1 + e else acc.1,
       if unslashedParticipatingCurrent p s timelyTargetFlagIndex i then acc.2 + e else acc.2))
    (0, 0)
  let previousTarget := max effectiveBalanceIncrement previousSum
  let currentTarget := max effectiveBalanceIncrement currentSum
  let oldPrevious := s.previousJustifiedCheckpoint
  let oldCurrent := s.currentJustifiedCheckpoint
  let b := s.justificationBits
  let mut bits := #[false, b[0]!, b[1]!, b[2]!]
  let mut justified := oldCurrent
  if previousTarget * 3 ≥ total * 2 then
    justified := ⟨previous, ← blockRoot p s previous⟩
    bits := bits.set! 1 true
  if currentTarget * 3 ≥ total * 2 then
    justified := ⟨current, ← blockRoot p s current⟩
    bits := bits.set! 0 true
  let mut finalized := s.finalizedCheckpoint
  if bits[1]! && bits[2]! && bits[3]! && oldPrevious.epoch + 3 == current then finalized := oldPrevious
  if bits[1]! && bits[2]! && oldPrevious.epoch + 2 == current then finalized := oldPrevious
  if bits[0]! && bits[1]! && bits[2]! && oldCurrent.epoch + 2 == current then finalized := oldCurrent
  if bits[0]! && bits[1]! && oldCurrent.epoch + 1 == current then finalized := oldCurrent
  return { s with
    previousJustifiedCheckpoint := oldCurrent
    currentJustifiedCheckpoint := justified
    justificationBits := bits
    finalizedCheckpoint := finalized }

def processInactivityUpdates (p : Preset) (s : BeaconState) : BeaconState :=
  if currentEpoch p s == genesisEpoch then s
  else
    let leak := isInInactivityLeak p s
    let scores := s.inactivityScores.mapIdx fun i score =>
      if !isEligibleValidator p s s.validators[i]! then score
      else
        let score :=
          if unslashedParticipatingPrevious p s timelyTargetFlagIndex i then score - min 1 score
          else score + inactivityScoreBias
        if !leak then score - min inactivityScoreRecoveryRate score else score
    { s with inactivityScores := scores }

/-- New balance of validator `i` after the three flag deltas and the
    inactivity penalty, applied in the specification's order (reward, then
    penalty stopping at zero, for each delta set in turn). -/
def rewardedBalance (p : Preset) (s : BeaconState) (leak : Bool) (perIncrement activeIncrements : Nat)
    (flagIncrements : Array Nat) (i balance : Nat) : Nat :=
  let v := s.validators[i]!
  if !isEligibleValidator p s v then balance
  else
    let base := v.effectiveBalance / effectiveBalanceIncrement * perIncrement
    let balance := (List.range 3).foldl
      (fun balance flag =>
        let weight := flagWeight flag
        if unslashedParticipatingPrevious p s flag i then
          if !leak then balance + base * weight * flagIncrements[flag]! / (activeIncrements * weightDenominator)
          else balance
        else if flag != timelyHeadFlagIndex then balance - base * weight / weightDenominator
        else balance)
      balance
    if !unslashedParticipatingPrevious p s timelyTargetFlagIndex i then
      balance - v.effectiveBalance * s.inactivityScores[i]! / (inactivityScoreBias * inactivityPenaltyQuotientBellatrix)
    else balance

def processRewardsAndPenalties (p : Preset) (s : BeaconState) : BeaconState :=
  if currentEpoch p s == genesisEpoch then s
  else
    let total := totalActiveBalance p s
    let activeIncrements := total / effectiveBalanceIncrement
    let perIncrement := baseRewardPerIncrement total
    let leak := isInInactivityLeak p s
    let flagIncrements := (Array.range 3).map fun flag =>
      max effectiveBalanceIncrement
        ((Array.range s.validators.size).foldl
          (fun acc i =>
            if unslashedParticipatingPrevious p s flag i then acc + s.validators[i]!.effectiveBalance else acc) 0)
        / effectiveBalanceIncrement
    { s with balances := s.balances.mapIdx (rewardedBalance p s leak perIncrement activeIncrements flagIncrements) }

/-- One validator of `process_registry_updates`. -/
def registryStep (p : Preset) (churn current finalized : Nat) (s : BeaconState) (i : Nat) : BeaconState :=
  let v := s.validators[i]!
  if v.isEligibleForActivationQueue then
    { s with validators := s.validators.modify i fun v => { v with activationEligibilityEpoch := current + 1 } }
  else if v.isActive current && v.effectiveBalance ≤ p.ejectionBalance then
    initiateValidatorExitWith p churn s i
  else if v.activationEligibilityEpoch ≤ finalized && v.activationEpoch == farFutureEpoch then
    { s with validators := s.validators.modify i fun v => { v with activationEpoch := activationExitEpoch current } }
  else s

/-- Visit validators `i, i + 1, …` for `count` steps. -/
def registryLoop (p : Preset) (churn current finalized : Nat) : Nat → Nat → BeaconState → BeaconState
  | 0, _, s => s
  | count + 1, i, s => registryLoop p churn current finalized count (i + 1) (registryStep p churn current finalized s i)

def processRegistryUpdates (p : Preset) (s : BeaconState) : BeaconState :=
  registryLoop p (activationExitChurnLimit p s) (currentEpoch p s) s.finalizedCheckpoint.epoch
    s.validators.size 0 s

def processSlashings (p : Preset) (s : BeaconState) : BeaconState :=
  let epoch := currentEpoch p s
  let total := totalActiveBalance p s
  let adjusted := min (s.slashings.foldl (· + ·) 0 * proportionalSlashingMultiplierBellatrix) total
  let perIncrement := adjusted / (total / effectiveBalanceIncrement)
  { s with balances := s.balances.mapIdx fun i balance =>
      let v := s.validators[i]!
      if v.slashed && epoch + p.epochsPerSlashingsVector / 2 == v.withdrawableEpoch then
        balance - perIncrement * (v.effectiveBalance / effectiveBalanceIncrement)
      else balance }

def processEth1DataReset (p : Preset) (s : BeaconState) : BeaconState :=
  if (currentEpoch p s + 1) % p.epochsPerEth1VotingPeriod == 0 then { s with eth1DataVotes := #[] } else s

def isValidDepositSignature (c : Ctx) (pubkey credentials : ByteArray) (amount : Nat) (signature : ByteArray) :
    Bool :=
  let domain := computeDomain c.p domainDeposit c.p.genesisForkVersion zero32
  let root := signingRoot c.p (DepositMessage.codec.root c.p ⟨pubkey, credentials, amount⟩) domain
  blsVerify c pubkey root signature

def addValidatorToRegistry (s : BeaconState) (pubkey credentials : ByteArray) (amount : Nat) : BeaconState :=
  let v : Validator :=
    { pubkey, withdrawalCredentials := credentials, effectiveBalance := 0, slashed := false,
      activationEligibilityEpoch := farFutureEpoch, activationEpoch := farFutureEpoch,
      exitEpoch := farFutureEpoch, withdrawableEpoch := farFutureEpoch }
  let v := { v with effectiveBalance := min (amount - amount % effectiveBalanceIncrement) v.maxEffectiveBalance }
  { s with
    validators := s.validators.push v
    balances := s.balances.push amount
    previousEpochParticipation := s.previousEpochParticipation.push 0
    currentEpochParticipation := s.currentEpochParticipation.push 0
    inactivityScores := s.inactivityScores.push 0 }

def applyPendingDeposit (c : Ctx) (s : BeaconState) (d : PendingDeposit) : BeaconState :=
  match findValidator s d.pubkey with
  | some i => s.increaseBalance i d.amount
  | none =>
    if isValidDepositSignature c d.pubkey d.withdrawalCredentials d.amount d.signature then
      addValidatorToRegistry s d.pubkey d.withdrawalCredentials d.amount
    else s

structure DepositLoop where
  s : BeaconState
  processed : Nat := 0
  next : Nat := 0
  postponed : Array PendingDeposit := #[]
  churnReached : Bool := false

/-- The queue walk of `process_pending_deposits`. It stops at the first
    deposit that may not be processed yet, and never takes more than
    `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits. -/
def pendingDepositsLoop (c : Ctx) (deposits : Array PendingDeposit) (available nextEpoch finalizedSlot : Nat) :
    Nat → DepositLoop → DepositLoop
  | 0, st => st
  | fuel + 1, st =>
    if h : st.next < deposits.size then
      let d := deposits[st.next]
      if d.slot > genesisSlot && st.s.eth1DepositIndex < st.s.depositRequestsStartIndex then st
      else if d.slot > finalizedSlot then st
      else if st.next ≥ maxPendingDepositsPerEpoch then st
      else
        let (exited, withdrawn) :=
          match findValidator st.s d.pubkey with
          | some i =>
            let v := st.s.validators[i]!
            (decide (v.exitEpoch < farFutureEpoch), decide (v.withdrawableEpoch < nextEpoch))
          | none => (false, false)
        if withdrawn then
          pendingDepositsLoop c deposits available nextEpoch finalizedSlot fuel
            { st with s := applyPendingDeposit c st.s d, next := st.next + 1 }
        else if exited then
          pendingDepositsLoop c deposits available nextEpoch finalizedSlot fuel
            { st with postponed := st.postponed.push d, next := st.next + 1 }
        else if st.processed + d.amount > available then { st with churnReached := true }
        else
          pendingDepositsLoop c deposits available nextEpoch finalizedSlot fuel
            { st with s := applyPendingDeposit c st.s d, processed := st.processed + d.amount, next := st.next + 1 }
    else st

def processPendingDeposits (c : Ctx) (s : BeaconState) : BeaconState :=
  let p := c.p
  let nextEpoch := currentEpoch p s + 1
  let available := s.depositBalanceToConsume + activationExitChurnLimit p s
  let finalizedSlot := startSlot p s.finalizedCheckpoint.epoch
  let deposits := s.pendingDeposits
  let st := pendingDepositsLoop c deposits available nextEpoch finalizedSlot (maxPendingDepositsPerEpoch + 1) { s }
  { st.s with
    pendingDeposits := deposits.extract st.next deposits.size ++ st.postponed
    depositBalanceToConsume := if st.churnReached then available - st.processed else 0 }

def consolidationsLoop (nextEpoch : Nat) (queue : Array PendingConsolidation) :
    Nat → Nat → BeaconState → BeaconState × Nat
  | 0, i, s => (s, i)
  | fuel + 1, i, s =>
    if h : i < queue.size then
      let pc := queue[i]
      let source := s.validators[pc.sourceIndex]!
      if source.slashed then consolidationsLoop nextEpoch queue fuel (i + 1) s
      else if source.withdrawableEpoch > nextEpoch then (s, i)
      else
        let amount := min s.balances[pc.sourceIndex]! source.effectiveBalance
        consolidationsLoop nextEpoch queue fuel (i + 1)
          ((s.decreaseBalance pc.sourceIndex amount).increaseBalance pc.targetIndex amount)
    else (s, i)

def processPendingConsolidations (p : Preset) (s : BeaconState) : BeaconState :=
  let queue := s.pendingConsolidations
  let (s, next) := consolidationsLoop (currentEpoch p s + 1) queue queue.size 0 s
  { s with pendingConsolidations := queue.extract next queue.size }

/-- The hysteresis rule of `process_effective_balance_updates` for one
    validator: the new effective balance. -/
def effectiveBalanceUpdate (v : Validator) (balance : Nat) : Nat :=
  let hysteresisIncrement := effectiveBalanceIncrement / hysteresisQuotient
  let downward := hysteresisIncrement * hysteresisDownwardMultiplier
  let upward := hysteresisIncrement * hysteresisUpwardMultiplier
  if balance + downward < v.effectiveBalance ∨ v.effectiveBalance + upward < balance then
    min (balance - balance % effectiveBalanceIncrement) v.maxEffectiveBalance
  else v.effectiveBalance

def processEffectiveBalanceUpdates (s : BeaconState) : BeaconState :=
  { s with validators := s.validators.mapIdx fun i v =>
      let e := effectiveBalanceUpdate v s.balances[i]!
      if e == v.effectiveBalance then v else { v with effectiveBalance := e } }

def processSlashingsReset (p : Preset) (s : BeaconState) : BeaconState :=
  { s with slashings := s.slashings.set! ((currentEpoch p s + 1) % p.epochsPerSlashingsVector) 0 }

def processRandaoMixesReset (p : Preset) (s : BeaconState) : BeaconState :=
  let current := currentEpoch p s
  { s with randaoMixes := s.randaoMixes.set! ((current + 1) % p.epochsPerHistoricalVector) (randaoMix p s current) }

def rootsCodec : Codec (Array ByteArray) := Codec.vec Codec.bytes32 (fun p => p.slotsPerHistoricalRoot)

def processHistoricalSummariesUpdate (p : Preset) (s : BeaconState) : BeaconState :=
  if (currentEpoch p s + 1) % (p.slotsPerHistoricalRoot / p.slotsPerEpoch) == 0 then
    let summary : HistoricalSummary := ⟨rootsCodec.root p s.blockRoots, rootsCodec.root p s.stateRoots⟩
    { s with historicalSummaries := s.historicalSummaries.push summary }
  else s

def processParticipationFlagUpdates (s : BeaconState) : BeaconState :=
  { s with
    previousEpochParticipation := s.currentEpochParticipation
    currentEpochParticipation := zeroBytes s.validators.size }

/-- Bound on the candidate loop of `get_next_sync_committee_indices`. -/
def syncCommitteeSearchLimit : Nat := 4194304

def syncCommitteeLoop (s : BeaconState) (size : Nat) (shuffled : Array Nat) (seed : ByteArray) :
    Nat → Nat → Array Nat → Except String (Array Nat)
  | 0, _, _ => .error "sync committee selection: candidate limit reached"
  | fuel + 1, i, acc =>
    if acc.size ≥ size then .ok acc
    else
      let candidate := shuffled[i % shuffled.size]!
      let randomValue := leNat (sha (seed ++ natLE (i / 16) 8)) (i % 16 * 2) 2
      let effective := s.validators[candidate]!.effectiveBalance
      syncCommitteeLoop s size shuffled seed fuel (i + 1)
        (if effective * 65535 ≥ maxEffectiveBalanceElectra * randomValue then acc.push candidate else acc)

/-- The reference test suite's stand-in aggregate key in BLS-off mode. -/
def stubPubkey : ByteArray := ⟨Array.replicate 48 0x22⟩

def nextSyncCommittee (c : Ctx) (s : BeaconState) : Except String SyncCommittee := do
  let p := c.p
  let epoch := currentEpoch p s + 1
  let active := activeIndices s epoch
  if active.size = 0 then throw "sync committee selection: no active validators"
  let seed := getSeed p s epoch domainSyncCommittee
  let shuffled := shuffleList p seed active
  let indices ← syncCommitteeLoop s p.syncCommitteeSize shuffled seed syncCommitteeSearchLimit 0 #[]
  let pubkeys := indices.map fun i => s.validators[i]!.pubkey
  if c.blsOff then return ⟨pubkeys, stubPubkey⟩
  match aggregateKeys 4 pubkeys.toList with
  | some aggregate => return ⟨pubkeys, aggregate⟩
  | none => throw "sync committee selection: public keys cannot be aggregated"

def processSyncCommitteeUpdates (c : Ctx) (s : BeaconState) : Except String BeaconState := do
  if (currentEpoch c.p s + 1) % c.p.epochsPerSyncCommitteePeriod == 0 then
    let next ← nextSyncCommittee c s
    return { s with currentSyncCommittee := s.nextSyncCommittee, nextSyncCommittee := next }
  else return s

def processProposerLookahead (p : Preset) (s : BeaconState) : Except String BeaconState := do
  let last ← beaconProposerIndices p s (currentEpoch p s + minSeedLookahead + 1)
  return { s with proposerLookahead :=
    s.proposerLookahead.extract p.slotsPerEpoch s.proposerLookahead.size ++ last }

def processEpoch (c : Ctx) (s : BeaconState) : Except String BeaconState := do
  let p := c.p
  let s ← processJustificationAndFinalization p s
  let s := processInactivityUpdates p s
  let s := processRewardsAndPenalties p s
  let s := processRegistryUpdates p s
  let s := processSlashings p s
  let s := processEth1DataReset p s
  let s := processPendingDeposits c s
  let s := processPendingConsolidations p s
  let s := processEffectiveBalanceUpdates s
  let s := processSlashingsReset p s
  let s := processRandaoMixesReset p s
  let s := processHistoricalSummariesUpdate p s
  let s := processParticipationFlagUpdates s
  let s ← processSyncCommitteeUpdates c s
  processProposerLookahead p s

end Beacon
