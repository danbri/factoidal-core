import Beacon.Epoch

/-!
# Block processing (Fulu)

`process_block` and its operations, from consensus-specs v1.6.1. A failed
assertion of the specification is `Except.error` with a reason; the state
is then discarded by the caller. The execution engine is not linked: the
payload's header-level checks are made here and the engine's verdict is an
input (`Ctx.executionValid`).
-/

namespace Beacon

def ensure (condition : Bool) (reason : String) : Except String Unit :=
  if condition then .ok () else .error reason

def processBlockHeader (p : Preset) (s : BeaconState) (block : BeaconBlock) : Except String BeaconState := do
  ensure (block.slot == s.slot) "block header: slot differs from the state's slot"
  ensure (block.slot > s.latestBlockHeader.slot) "block header: not newer than the latest header"
  ensure (block.proposerIndex == beaconProposerIndex p s) "block header: wrong proposer"
  ensure (block.parentRoot == BeaconBlockHeader.codec.root p s.latestBlockHeader)
    "block header: parent root mismatch"
  let some proposer := s.validators[block.proposerIndex]?
    | throw "block header: proposer index outside the registry"
  ensure (!proposer.slashed) "block header: proposer is slashed"
  return { s with latestBlockHeader :=
    { slot := block.slot, proposerIndex := block.proposerIndex, parentRoot := block.parentRoot,
      stateRoot := zero32, bodyRoot := BeaconBlockBody.codec.root p block.body } }

/-! ## Withdrawals -/

def withdrawnSoFar (ws : Array Withdrawal) (index : Nat) : Nat :=
  ws.foldl (fun acc w => if w.validatorIndex == index then acc + w.amount else acc) 0

/-- `get_expected_withdrawals`: the withdrawals and the number of pending
    partial withdrawals consumed. The sweep visits at most
    `min(registry size, MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)` validators. -/
def expectedWithdrawals (p : Preset) (s : BeaconState) : Array Withdrawal × Nat := Id.run do
  let epoch := currentEpoch p s
  let mut nextIndex := s.nextWithdrawalIndex
  let mut ws : Array Withdrawal := #[]
  let mut processed := 0
  for w in s.pendingPartialWithdrawals do
    if w.withdrawableEpoch > epoch || ws.size == p.maxPendingPartialsPerWithdrawalsSweep then break
    let v := s.validators[w.validatorIndex]!
    let balance := s.balances[w.validatorIndex]! - withdrawnSoFar ws w.validatorIndex
    if v.exitEpoch == farFutureEpoch && v.effectiveBalance ≥ minActivationBalance
        && balance > minActivationBalance then
      ws := ws.push ⟨nextIndex, w.validatorIndex, v.withdrawalCredentials.extract 12 32,
        min (balance - minActivationBalance) w.amount⟩
      nextIndex := nextIndex + 1
    processed := processed + 1
  let n := s.validators.size
  let mut vi := s.nextWithdrawalValidatorIndex
  for _ in [0:min n p.maxValidatorsPerWithdrawalsSweep] do
    let v := s.validators[vi]!
    let balance := s.balances[vi]! - withdrawnSoFar ws vi
    if v.isFullyWithdrawable balance epoch then
      ws := ws.push ⟨nextIndex, vi, v.withdrawalCredentials.extract 12 32, balance⟩
      nextIndex := nextIndex + 1
    else if v.isPartiallyWithdrawable balance then
      ws := ws.push ⟨nextIndex, vi, v.withdrawalCredentials.extract 12 32, balance - v.maxEffectiveBalance⟩
      nextIndex := nextIndex + 1
    if ws.size == p.maxWithdrawalsPerPayload then break
    vi := (vi + 1) % n
  return (ws, processed)

def processWithdrawals (p : Preset) (s : BeaconState) (payload : ExecutionPayload) : Except String BeaconState := do
  ensure (s.nextWithdrawalValidatorIndex < s.validators.size) "withdrawals: sweep index outside the registry"
  let (expected, processed) := expectedWithdrawals p s
  ensure (payload.withdrawals == expected) "withdrawals: payload differs from the expected withdrawals"
  let n := s.validators.size
  let s := expected.foldl (fun s w => s.decreaseBalance w.validatorIndex w.amount) s
  let s := { s with pendingPartialWithdrawals :=
    s.pendingPartialWithdrawals.extract processed s.pendingPartialWithdrawals.size }
  let s := match expected.back? with
    | some latest => { s with nextWithdrawalIndex := latest.index + 1 }
    | none => s
  let next :=
    match expected.back? with
    | some latest =>
      if expected.size == p.maxWithdrawalsPerPayload then (latest.validatorIndex + 1) % n
      else (s.nextWithdrawalValidatorIndex + p.maxValidatorsPerWithdrawalsSweep) % n
    | none => (s.nextWithdrawalValidatorIndex + p.maxValidatorsPerWithdrawalsSweep) % n
  return { s with nextWithdrawalValidatorIndex := next }

/-! ## Execution payload (header-level checks) -/

/-- `get_blob_parameters(epoch).max_blobs_per_block`. -/
def maxBlobsPerBlock (p : Preset) (epoch : Nat) : Nat :=
  let applicable := p.blobSchedule.filter (fun entry => epoch ≥ entry.1)
  match applicable.foldl (fun (best : Option (Nat × Nat)) entry =>
      match best with
      | some b => if entry.1 > b.1 then some entry else some b
      | none => some entry) none with
  | some entry => entry.2
  | none => maxBlobsPerBlockElectra

def transactionsCodec : Codec (Array ByteArray) :=
  Codec.list (Codec.byteList (fun _ => maxBytesPerTransaction)) (fun _ => maxTransactionsPerPayload)

def withdrawalsCodec : Codec (Array Withdrawal) :=
  Codec.list Withdrawal.codec (fun p => p.maxWithdrawalsPerPayload)

def processExecutionPayload (c : Ctx) (s : BeaconState) (body : BeaconBlockBody) : Except String BeaconState := do
  let p := c.p
  let payload := body.executionPayload
  ensure (payload.parentHash == s.latestExecutionPayloadHeader.blockHash) "execution payload: parent hash mismatch"
  ensure (payload.prevRandao == randaoMix p s (currentEpoch p s)) "execution payload: prev_randao mismatch"
  ensure (payload.timestamp == s.genesisTime + s.slot * p.secondsPerSlot) "execution payload: timestamp mismatch"
  ensure (body.blobKzgCommitments.size ≤ maxBlobsPerBlock p (currentEpoch p s))
    "execution payload: too many blob commitments"
  ensure c.executionValid "execution payload: rejected by the execution engine"
  return { s with latestExecutionPayloadHeader :=
    { parentHash := payload.parentHash, feeRecipient := payload.feeRecipient, stateRoot := payload.stateRoot,
      receiptsRoot := payload.receiptsRoot, logsBloom := payload.logsBloom, prevRandao := payload.prevRandao,
      blockNumber := payload.blockNumber, gasLimit := payload.gasLimit, gasUsed := payload.gasUsed,
      timestamp := payload.timestamp, extraData := payload.extraData, baseFeePerGas := payload.baseFeePerGas,
      blockHash := payload.blockHash, transactionsRoot := transactionsCodec.root p payload.transactions,
      withdrawalsRoot := withdrawalsCodec.root p payload.withdrawals, blobGasUsed := payload.blobGasUsed,
      excessBlobGas := payload.excessBlobGas } }

/-! ## RANDAO and eth1 data -/

def processRandao (c : Ctx) (s : BeaconState) (body : BeaconBlockBody) : Except String BeaconState := do
  let p := c.p
  let epoch := currentEpoch p s
  let some proposer := s.validators[beaconProposerIndex p s]?
    | throw "randao: proposer index outside the registry"
  let root := signingRoot p (Codec.u64.root p epoch) (getDomain p s domainRandao epoch)
  ensure (blsVerify c proposer.pubkey root body.randaoReveal) "randao: invalid reveal signature"
  let mix := xorBytes (randaoMix p s epoch) (sha body.randaoReveal)
  return { s with randaoMixes := s.randaoMixes.set! (epoch % p.epochsPerHistoricalVector) mix }

def processEth1Data (p : Preset) (s : BeaconState) (body : BeaconBlockBody) : BeaconState :=
  let votes := s.eth1DataVotes.push body.eth1Data
  let count := (votes.filter (· == body.eth1Data)).size
  let s := { s with eth1DataVotes := votes }
  if count * 2 > p.epochsPerEth1VotingPeriod * p.slotsPerEpoch then { s with eth1Data := body.eth1Data } else s

/-! ## Slashings -/

def strictlyIncreasing (xs : Array Nat) : Bool :=
  (Array.range (xs.size - 1)).all fun i => xs[i]! < xs[i + 1]!

def isValidIndexedAttestation (c : Ctx) (s : BeaconState) (a : IndexedAttestation) : Bool :=
  let indices := a.attestingIndices
  if indices.size == 0 || !strictlyIncreasing indices then false
  else if indices.any (· ≥ s.validators.size) then false
  else
    let p := c.p
    let pubkeys := indices.map fun i => s.validators[i]!.pubkey
    let root := signingRoot p (AttestationData.codec.root p a.data)
      (getDomain p s domainBeaconAttester a.data.target.epoch)
    blsFastAggregateVerify c pubkeys root a.signature

def processProposerSlashing (c : Ctx) (s : BeaconState) (slashing : ProposerSlashing) : Except String BeaconState := do
  let p := c.p
  let h1 := slashing.signedHeader1.message
  let h2 := slashing.signedHeader2.message
  ensure (h1.slot == h2.slot) "proposer slashing: slots differ"
  ensure (h1.proposerIndex == h2.proposerIndex) "proposer slashing: proposers differ"
  ensure (h1 != h2) "proposer slashing: headers are identical"
  let some proposer := s.validators[h1.proposerIndex]?
    | throw "proposer slashing: proposer index outside the registry"
  ensure (proposer.isSlashable (currentEpoch p s)) "proposer slashing: proposer is not slashable"
  for signed in [slashing.signedHeader1, slashing.signedHeader2] do
    let domain := getDomain p s domainBeaconProposer (signed.message.slot / p.slotsPerEpoch)
    let root := signingRoot p (BeaconBlockHeader.codec.root p signed.message) domain
    ensure (blsVerify c proposer.pubkey root signed.signature) "proposer slashing: invalid header signature"
  return slashValidator p s h1.proposerIndex

def isSlashableAttestationData (d1 d2 : AttestationData) : Bool :=
  (d1 != d2 && d1.target.epoch == d2.target.epoch) ||
  (d1.source.epoch < d2.source.epoch && d2.target.epoch < d1.target.epoch)

/-- Common elements of two strictly increasing arrays, in order. -/
def sortedIntersection (a b : Array Nat) : Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, acc => acc
  | fuel + 1, i, j, acc =>
    if i < a.size && j < b.size then
      let x := a[i]!
      let y := b[j]!
      if x == y then sortedIntersection a b fuel (i + 1) (j + 1) (acc.push x)
      else if x < y then sortedIntersection a b fuel (i + 1) j acc
      else sortedIntersection a b fuel i (j + 1) acc
    else acc

def processAttesterSlashing (c : Ctx) (s : BeaconState) (slashing : AttesterSlashing) : Except String BeaconState := do
  let p := c.p
  let a1 := slashing.attestation1
  let a2 := slashing.attestation2
  ensure (isSlashableAttestationData a1.data a2.data) "attester slashing: attestations are not slashable"
  ensure (isValidIndexedAttestation c s a1) "attester slashing: first attestation invalid"
  ensure (isValidIndexedAttestation c s a2) "attester slashing: second attestation invalid"
  let common := sortedIntersection a1.attestingIndices a2.attestingIndices
    (a1.attestingIndices.size + a2.attestingIndices.size) 0 0 #[]
  let epoch := currentEpoch p s
  let (s, slashedAny) := common.foldl
    (fun (acc : BeaconState × Bool) index =>
      if acc.1.validators[index]!.isSlashable epoch then (slashValidator p acc.1 index, true) else acc)
    (s, false)
  ensure slashedAny "attester slashing: no validator was slashed"
  return s

/-! ## Attestations -/

def participationFlagIndices (p : Preset) (s : BeaconState) (data : AttestationData) (delay : Nat) :
    Except String (List Nat) := do
  let justified :=
    if data.target.epoch == currentEpoch p s then s.currentJustifiedCheckpoint
    else s.previousJustifiedCheckpoint
  ensure (data.source == justified) "attestation: source is not the justified checkpoint"
  let matchingTarget := data.target.root == (← blockRoot p s data.target.epoch)
  let matchingHead ←
    if matchingTarget then (fun r => data.beaconBlockRoot == r) <$> blockRootAtSlot p s data.slot
    else pure false
  let flags := if delay ≤ isqrt p.slotsPerEpoch then [timelySourceFlagIndex] else []
  let flags := if matchingTarget then flags ++ [timelyTargetFlagIndex] else flags
  return if matchingHead && delay == minAttestationInclusionDelay then flags ++ [timelyHeadFlagIndex] else flags

/-- The attesting indices of an attestation, committee by committee, with
    the specification's checks on committee bits and aggregation bits. -/
def attestingIndices (p : Preset) (sh : Shuffling) (a : Attestation) : Except String (Array Nat) := do
  let mut offset := 0
  let mut attesters : Array Nat := #[]
  for ci in [0:a.committeeBits.size] do
    if a.committeeBits[ci]! then
      ensure (ci < sh.committeesPerSlot) "attestation: committee index out of range"
      let committee := sh.committee p a.data.slot ci
      ensure (offset + committee.size ≤ a.aggregationBits.size) "attestation: aggregation bits too short"
      let mut any := false
      for j in [0:committee.size] do
        if a.aggregationBits[offset + j]! then
          attesters := attesters.push committee[j]!
          any := true
      ensure any "attestation: a selected committee has no attester"
      offset := offset + committee.size
  ensure (a.aggregationBits.size == offset) "attestation: aggregation bits length mismatch"
  return attesters

def processAttestation (c : Ctx) (s : BeaconState) (a : Attestation) : Except String BeaconState := do
  let p := c.p
  let data := a.data
  let current := currentEpoch p s
  ensure (data.target.epoch == previousEpoch p s || data.target.epoch == current)
    "attestation: target epoch is neither current nor previous"
  ensure (data.target.epoch == data.slot / p.slotsPerEpoch) "attestation: target epoch does not match the slot"
  ensure (data.slot + minAttestationInclusionDelay ≤ s.slot) "attestation: included too early"
  ensure (data.index == 0) "attestation: data index must be zero"
  let sh := getShuffling p s data.target.epoch
  let attesters ← attestingIndices p sh a
  let flags ← participationFlagIndices p s data (s.slot - data.slot)
  let sorted := attesters.qsort (· < ·)
  ensure (isValidIndexedAttestation c s ⟨sorted, data, a.signature⟩) "attestation: invalid indexed attestation"
  let isCurrent := data.target.epoch == current
  let perIncrement := baseRewardPerIncrement (totalActiveBalance p s)
  let mut participation := if isCurrent then s.currentEpochParticipation else s.previousEpochParticipation
  let mut numerator := 0
  for index in sorted do
    for flag in flags do
      let old := participation.get! index
      if !hasFlag old flag then
        participation := participation.set! index (addFlag old flag)
        numerator := numerator +
          s.validators[index]!.effectiveBalance / effectiveBalanceIncrement * perIncrement * flagWeight flag
  let denominator := (weightDenominator - proposerWeight) * weightDenominator / proposerWeight
  let s := if isCurrent then { s with currentEpochParticipation := participation }
    else { s with previousEpochParticipation := participation }
  return s.increaseBalance (beaconProposerIndex p s) (numerator / denominator)

/-! ## Deposits -/

def isValidMerkleBranch (leaf : ByteArray) (branch : Array ByteArray) (depth index : Nat) (root : ByteArray) : Bool :=
  let value := (List.range depth).foldl
    (fun value i =>
      if index / 2 ^ i % 2 == 1 then sha (branch[i]! ++ value) else sha (value ++ branch[i]!))
    leaf
  value == root

def applyDeposit (c : Ctx) (s : BeaconState) (pubkey credentials : ByteArray) (amount : Nat)
    (signature : ByteArray) : BeaconState :=
  let pending : PendingDeposit :=
    { pubkey, withdrawalCredentials := credentials, amount, signature, slot := genesisSlot }
  match findValidator s pubkey with
  | some _ => { s with pendingDeposits := s.pendingDeposits.push pending }
  | none =>
    if isValidDepositSignature c pubkey credentials amount signature then
      let s := addValidatorToRegistry s pubkey credentials 0
      { s with pendingDeposits := s.pendingDeposits.push pending }
    else s

def processDeposit (c : Ctx) (s : BeaconState) (deposit : Deposit) : Except String BeaconState := do
  ensure (isValidMerkleBranch (DepositData.codec.root c.p deposit.data) deposit.proof
      (depositContractTreeDepth + 1) s.eth1DepositIndex s.eth1Data.depositRoot)
    "deposit: invalid Merkle branch"
  let s := { s with eth1DepositIndex := s.eth1DepositIndex + 1 }
  return applyDeposit c s deposit.data.pubkey deposit.data.withdrawalCredentials deposit.data.amount
    deposit.data.signature

/-! ## Exits and credential changes -/

def processVoluntaryExit (c : Ctx) (s : BeaconState) (signed : SignedVoluntaryExit) : Except String BeaconState := do
  let p := c.p
  let exit := signed.message
  let current := currentEpoch p s
  let some v := s.validators[exit.validatorIndex]?
    | throw "voluntary exit: validator index outside the registry"
  ensure (v.isActive current) "voluntary exit: validator is not active"
  ensure (v.exitEpoch == farFutureEpoch) "voluntary exit: exit already initiated"
  ensure (current ≥ exit.epoch) "voluntary exit: not yet valid"
  ensure (current ≥ v.activationEpoch + p.shardCommitteePeriod) "voluntary exit: validator too recently activated"
  ensure (pendingBalanceToWithdraw s exit.validatorIndex == 0) "voluntary exit: pending partial withdrawals"
  let domain := computeDomain p domainVoluntaryExit p.capellaForkVersion s.genesisValidatorsRoot
  let root := signingRoot p (VoluntaryExit.codec.root p exit) domain
  ensure (blsVerify c v.pubkey root signed.signature) "voluntary exit: invalid signature"
  return initiateValidatorExit p s exit.validatorIndex

def processBlsToExecutionChange (c : Ctx) (s : BeaconState) (signed : SignedBLSToExecutionChange) :
    Except String BeaconState := do
  let p := c.p
  let change := signed.message
  let some v := s.validators[change.validatorIndex]?
    | throw "bls to execution change: validator index outside the registry"
  ensure (v.withdrawalCredentials.get! 0 == 0) "bls to execution change: not a BLS withdrawal credential"
  ensure (v.withdrawalCredentials.extract 1 32 == (sha change.fromBlsPubkey).extract 1 32)
    "bls to execution change: public key does not match the credential"
  let domain := computeDomain p domainBlsToExecutionChange p.genesisForkVersion s.genesisValidatorsRoot
  let root := signingRoot p (BLSToExecutionChange.codec.root p change) domain
  ensure (blsVerify c change.fromBlsPubkey root signed.signature) "bls to execution change: invalid signature"
  let credentials := (ByteArray.empty.push 1) ++ zeroBytes 11 ++ change.toExecutionAddress
  return { s with validators := s.validators.modify change.validatorIndex fun v =>
    { v with withdrawalCredentials := credentials } }

/-! ## Execution-layer requests (Electra) -/

def processDepositRequest (s : BeaconState) (r : DepositRequest) : BeaconState :=
  let s := if s.depositRequestsStartIndex == unsetDepositRequestsStartIndex then
    { s with depositRequestsStartIndex := r.index } else s
  let pending : PendingDeposit :=
    { pubkey := r.pubkey, withdrawalCredentials := r.withdrawalCredentials, amount := r.amount,
      signature := r.signature, slot := s.slot }
  { s with pendingDeposits := s.pendingDeposits.push pending }

def processWithdrawalRequest (p : Preset) (s : BeaconState) (r : WithdrawalRequest) : BeaconState :=
  let isFullExit := r.amount == fullExitRequestAmount
  if s.pendingPartialWithdrawals.size == p.pendingPartialWithdrawalsLimit && !isFullExit then s
  else match findValidator s r.validatorPubkey with
  | none => s
  | some index =>
    let v := s.validators[index]!
    let current := currentEpoch p s
    if !(v.hasExecutionCredential && v.withdrawalCredentials.extract 12 32 == r.sourceAddress) then s
    else if !v.isActive current then s
    else if v.exitEpoch != farFutureEpoch then s
    else if current < v.activationEpoch + p.shardCommitteePeriod then s
    else
      let pending := pendingBalanceToWithdraw s index
      if isFullExit then
        if pending == 0 then initiateValidatorExit p s index else s
      else
        let balance := s.balances[index]!
        if v.hasCompoundingCredential && v.effectiveBalance ≥ minActivationBalance
            && balance > minActivationBalance + pending then
          let toWithdraw := min (balance - minActivationBalance - pending) r.amount
          let (s, exitEpoch) := exitEpochAndUpdateChurn p (activationExitChurnLimit p s) s toWithdraw
          let entry : PendingPartialWithdrawal :=
            { validatorIndex := index, amount := toWithdraw,
              withdrawableEpoch := exitEpoch + p.minValidatorWithdrawabilityDelay }
          { s with pendingPartialWithdrawals := s.pendingPartialWithdrawals.push entry }
        else s

def isValidSwitchToCompoundingRequest (p : Preset) (s : BeaconState) (r : ConsolidationRequest) : Option Nat :=
  if r.sourcePubkey != r.targetPubkey then none
  else match findValidator s r.sourcePubkey with
  | none => none
  | some index =>
    let v := s.validators[index]!
    if v.withdrawalCredentials.extract 12 32 != r.sourceAddress then none
    else if !v.hasEth1Credential then none
    else if !v.isActive (currentEpoch p s) then none
    else if v.exitEpoch != farFutureEpoch then none
    else some index

def processConsolidationRequest (p : Preset) (s : BeaconState) (r : ConsolidationRequest) : BeaconState :=
  match isValidSwitchToCompoundingRequest p s r with
  | some index => switchToCompounding s index
  | none =>
    if r.sourcePubkey == r.targetPubkey then s
    else if s.pendingConsolidations.size == p.pendingConsolidationsLimit then s
    else if consolidationChurnLimit p s ≤ minActivationBalance then s
    else match findValidator s r.sourcePubkey, findValidator s r.targetPubkey with
    | some sourceIndex, some targetIndex =>
      let source := s.validators[sourceIndex]!
      let target := s.validators[targetIndex]!
      let current := currentEpoch p s
      if !(source.hasExecutionCredential && source.withdrawalCredentials.extract 12 32 == r.sourceAddress) then s
      else if !target.hasCompoundingCredential then s
      else if !source.isActive current then s
      else if !target.isActive current then s
      else if source.exitEpoch != farFutureEpoch then s
      else if target.exitEpoch != farFutureEpoch then s
      else if current < source.activationEpoch + p.shardCommitteePeriod then s
      else if pendingBalanceToWithdraw s sourceIndex > 0 then s
      else
        let (s, exitEpoch) := consolidationEpochAndUpdateChurn p s source.effectiveBalance
        let entry : PendingConsolidation := { sourceIndex, targetIndex }
        { s with
          validators := s.validators.modify sourceIndex fun v =>
            { v with exitEpoch := exitEpoch, withdrawableEpoch := exitEpoch + p.minValidatorWithdrawabilityDelay }
          pendingConsolidations := s.pendingConsolidations.push entry }
    | _, _ => s

/-! ## Sync aggregate -/

def processSyncAggregate (c : Ctx) (s : BeaconState) (aggregate : SyncAggregate) : Except String BeaconState := do
  let p := c.p
  let committee := s.currentSyncCommittee.pubkeys
  let bits := aggregate.syncCommitteeBits
  let participants := (Array.range committee.size).filterMap fun i =>
    if bits.getD i false then some committee[i]! else none
  let previousSlot := max s.slot 1 - 1
  let domain := getDomain p s domainSyncCommittee (previousSlot / p.slotsPerEpoch)
  let root := signingRoot p (← blockRootAtSlot p s previousSlot) domain
  ensure (ethFastAggregateVerify c participants root aggregate.syncCommitteeSignature)
    "sync aggregate: invalid signature"
  let total := totalActiveBalance p s
  let totalBaseRewards := baseRewardPerIncrement total * (total / effectiveBalanceIncrement)
  let maxParticipantRewards := totalBaseRewards * syncRewardWeight / weightDenominator / p.slotsPerEpoch
  let participantReward := maxParticipantRewards / p.syncCommitteeSize
  let proposerReward := participantReward * proposerWeight / (weightDenominator - proposerWeight)
  let lookup := pubkeyIndex s
  let proposer := beaconProposerIndex p s
  let mut s := s
  for i in [0:committee.size] do
    let some index := lookup[committee[i]!]?
      | throw "sync aggregate: committee key is not in the registry"
    if bits.getD i false then
      s := s.increaseBalance index participantReward
      s := s.increaseBalance proposer proposerReward
    else
      s := s.decreaseBalance index participantReward
  return s

/-! ## Operations and the block -/

def forOps {α : Type} (ops : Array α) (f : BeaconState → α → Except String BeaconState) (s : BeaconState) :
    Except String BeaconState :=
  ops.foldlM f s

def processOperations (c : Ctx) (s : BeaconState) (body : BeaconBlockBody) : Except String BeaconState := do
  let p := c.p
  let limit := min s.eth1Data.depositCount s.depositRequestsStartIndex
  if s.eth1DepositIndex < limit then
    ensure (body.deposits.size == min maxDeposits (limit - s.eth1DepositIndex))
      "operations: wrong number of deposits"
  else
    ensure (body.deposits.size == 0) "operations: deposits after the deposit-request transition"
  let s ← forOps body.proposerSlashings (processProposerSlashing c) s
  let s ← forOps body.attesterSlashings (processAttesterSlashing c) s
  let s ← forOps body.attestations (processAttestation c) s
  let s ← forOps body.deposits (processDeposit c) s
  let s ← forOps body.voluntaryExits (processVoluntaryExit c) s
  let s ← forOps body.blsToExecutionChanges (processBlsToExecutionChange c) s
  let s := body.executionRequests.deposits.foldl processDepositRequest s
  let s := body.executionRequests.withdrawals.foldl (processWithdrawalRequest p) s
  return body.executionRequests.consolidations.foldl (processConsolidationRequest p) s

def processBlock (c : Ctx) (s : BeaconState) (block : BeaconBlock) : Except String BeaconState := do
  let p := c.p
  let s ← processBlockHeader p s block
  let s ← processWithdrawals p s block.body.executionPayload
  let s ← processExecutionPayload c s block.body
  let s ← processRandao c s block.body
  let s := processEth1Data p s block.body
  let s ← processOperations c s block.body
  let s ← processSyncAggregate c s block.body.syncAggregate
  ensure s.inRange "block: a uint64 field left its range"
  return s

end Beacon
