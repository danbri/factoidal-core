import Beacon.Harness
import Beacon.Transition

/-!
# Runner for the official consensus test vectors (Fulu)

`beacon-spec-tests --vectors DIR --preset minimal|mainnet [--runner R]
[--handler H] [--case SUBSTRING] [--jobs N (worker threads, default 4)] [--bls-optional verify|skip]
[--json FILE]`

Vectors are a test oracle: the runner compares the built-in state
transition's answers with them and never copies an expected answer into a
result.
-/

open Beacon Beacon.Harness

structure Options where
  vectors : System.FilePath := "."
  preset : Preset := minimal
  fork : String := "fulu"
  runners : List String := []
  handler : Option String := none
  caseFilter : Option String := none
  jobs : Nat := 4
  verifyOptionalBls : Bool := true
  json : Option System.FilePath := none
  benchState : Option System.FilePath := none
  benchValidators : Nat := 0

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--vectors" :: v :: rest, o => parseArgs rest { o with vectors := v }
  | "--preset" :: "minimal" :: rest, o => parseArgs rest { o with preset := minimal }
  | "--preset" :: "mainnet" :: rest, o => parseArgs rest { o with preset := mainnet }
  | "--runner" :: v :: rest, o => parseArgs rest { o with runners := o.runners ++ [v] }
  | "--handler" :: v :: rest, o => parseArgs rest { o with handler := some v }
  | "--case" :: v :: rest, o => parseArgs rest { o with caseFilter := some v }
  | "--jobs" :: v :: rest, o => parseArgs rest { o with jobs := max 1 v.toNat! }
  | "--bls-optional" :: "verify" :: rest, o => parseArgs rest { o with verifyOptionalBls := true }
  | "--bls-optional" :: "skip" :: rest, o => parseArgs rest { o with verifyOptionalBls := false }
  | "--json" :: v :: rest, o => parseArgs rest { o with json := some v }
  | "--bench-epoch" :: v :: rest, o => parseArgs rest { o with benchState := some v }
  | "--validators" :: v :: rest, o => parseArgs rest { o with benchValidators := v.toNat! }
  | arg :: _, _ => .error s!"unknown argument {arg}"

def sszCheck {α : Type} (c : Codec α) (p : Preset) (bytes root : ByteArray) : Except String Unit := do
  let v ← c.decode p bytes
  if c.encode p v != bytes then throw "re-serialisation differs from the vector"
  let r := c.root p v
  if r != root then throw s!"hash_tree_root {toHex r} differs from the vector {toHex root}"

def sszStaticCodec (p : Preset) (name : String) : Option (ByteArray → ByteArray → Except String Unit) :=
  match name with
  | "AggregateAndProof" => some (sszCheck AggregateAndProof.codec p)
  | "Attestation" => some (sszCheck Attestation.codec p)
  | "AttestationData" => some (sszCheck AttestationData.codec p)
  | "AttesterSlashing" => some (sszCheck AttesterSlashing.codec p)
  | "BeaconBlock" => some (sszCheck BeaconBlock.codec p)
  | "BeaconBlockBody" => some (sszCheck BeaconBlockBody.codec p)
  | "BeaconBlockHeader" => some (sszCheck BeaconBlockHeader.codec p)
  | "BeaconState" => some (sszCheck BeaconState.codec p)
  | "BlobIdentifier" => some (sszCheck BlobIdentifier.codec p)
  | "BlobSidecar" => some (sszCheck BlobSidecar.codec p)
  | "BLSToExecutionChange" => some (sszCheck BLSToExecutionChange.codec p)
  | "Checkpoint" => some (sszCheck Checkpoint.codec p)
  | "ConsolidationRequest" => some (sszCheck ConsolidationRequest.codec p)
  | "ContributionAndProof" => some (sszCheck ContributionAndProof.codec p)
  | "DataColumnsByRootIdentifier" => some (sszCheck DataColumnsByRootIdentifier.codec p)
  | "DataColumnSidecar" => some (sszCheck DataColumnSidecar.codec p)
  | "Deposit" => some (sszCheck Deposit.codec p)
  | "DepositData" => some (sszCheck DepositData.codec p)
  | "DepositMessage" => some (sszCheck DepositMessage.codec p)
  | "DepositRequest" => some (sszCheck DepositRequest.codec p)
  | "Eth1Block" => some (sszCheck Eth1Block.codec p)
  | "Eth1Data" => some (sszCheck Eth1Data.codec p)
  | "ExecutionPayload" => some (sszCheck ExecutionPayload.codec p)
  | "ExecutionPayloadHeader" => some (sszCheck ExecutionPayloadHeader.codec p)
  | "ExecutionRequests" => some (sszCheck ExecutionRequests.codec p)
  | "Fork" => some (sszCheck Fork.codec p)
  | "ForkData" => some (sszCheck ForkData.codec p)
  | "HistoricalBatch" => some (sszCheck HistoricalBatch.codec p)
  | "HistoricalSummary" => some (sszCheck HistoricalSummary.codec p)
  | "IndexedAttestation" => some (sszCheck IndexedAttestation.codec p)
  | "LightClientBootstrap" => some (sszCheck LightClientBootstrap.codec p)
  | "LightClientFinalityUpdate" => some (sszCheck LightClientFinalityUpdate.codec p)
  | "LightClientHeader" => some (sszCheck LightClientHeader.codec p)
  | "LightClientOptimisticUpdate" => some (sszCheck LightClientOptimisticUpdate.codec p)
  | "LightClientUpdate" => some (sszCheck LightClientUpdate.codec p)
  | "MatrixEntry" => some (sszCheck MatrixEntry.codec p)
  | "PendingAttestation" => some (sszCheck PendingAttestation.codec p)
  | "PendingConsolidation" => some (sszCheck PendingConsolidation.codec p)
  | "PendingDeposit" => some (sszCheck PendingDeposit.codec p)
  | "PendingPartialWithdrawal" => some (sszCheck PendingPartialWithdrawal.codec p)
  | "PowBlock" => some (sszCheck PowBlock.codec p)
  | "ProposerSlashing" => some (sszCheck ProposerSlashing.codec p)
  | "SignedAggregateAndProof" => some (sszCheck SignedAggregateAndProof.codec p)
  | "SignedBeaconBlock" => some (sszCheck SignedBeaconBlock.codec p)
  | "SignedBeaconBlockHeader" => some (sszCheck SignedBeaconBlockHeader.codec p)
  | "SignedBLSToExecutionChange" => some (sszCheck SignedBLSToExecutionChange.codec p)
  | "SignedContributionAndProof" => some (sszCheck SignedContributionAndProof.codec p)
  | "SignedVoluntaryExit" => some (sszCheck SignedVoluntaryExit.codec p)
  | "SigningData" => some (sszCheck SigningData.codec p)
  | "SingleAttestation" => some (sszCheck SingleAttestation.codec p)
  | "SyncAggregate" => some (sszCheck SyncAggregate.codec p)
  | "SyncAggregatorSelectionData" => some (sszCheck SyncAggregatorSelectionData.codec p)
  | "SyncCommittee" => some (sszCheck SyncCommittee.codec p)
  | "SyncCommitteeContribution" => some (sszCheck SyncCommitteeContribution.codec p)
  | "SyncCommitteeMessage" => some (sszCheck SyncCommitteeMessage.codec p)
  | "Validator" => some (sszCheck Validator.codec p)
  | "VoluntaryExit" => some (sszCheck VoluntaryExit.codec p)
  | "Withdrawal" => some (sszCheck Withdrawal.codec p)
  | "WithdrawalRequest" => some (sszCheck WithdrawalRequest.codec p)
  | _ => none

/-- One case: returns status and detail. -/
abbrev CaseFn := System.FilePath → IO (Status × String × Nat × Bool)

def sszStaticCase (o : Options) (handler : String) : CaseFn := fun dir => do
  match sszStaticCodec o.preset handler with
  | none => return (.unsupported, s!"container {handler} is not implemented", 0, false)
  | some check =>
    let bytes ← readSnappy (dir / "serialized.ssz_snappy")
    let root := hexBytes (← IO.FS.readFile (dir / "roots.yaml"))
    match check bytes root with
    | .ok () => return (.pass, "", 0, false)
    | .error e => return (.fail, e, 0, false)

/-- Names of the top-level state fields whose serialisations differ. -/
def stateDiff (p : Preset) (a b : BeaconState) : List String :=
  let u := Codec.u64
  let cp := Checkpoint.codec
  let fields : List (String × ByteArray × ByteArray) := [
    ("genesis_time", u.encode p a.genesisTime, u.encode p b.genesisTime),
    ("slot", u.encode p a.slot, u.encode p b.slot),
    ("fork", Fork.codec.encode p a.fork, Fork.codec.encode p b.fork),
    ("latest_block_header", BeaconBlockHeader.codec.encode p a.latestBlockHeader, BeaconBlockHeader.codec.encode p b.latestBlockHeader),
    ("block_roots", rootsCodec.encode p a.blockRoots, rootsCodec.encode p b.blockRoots),
    ("state_roots", rootsCodec.encode p a.stateRoots, rootsCodec.encode p b.stateRoots),
    ("eth1_data", Eth1Data.codec.encode p a.eth1Data, Eth1Data.codec.encode p b.eth1Data),
    ("eth1_data_votes", Codec.encodeSeq Eth1Data.codec p a.eth1DataVotes, Codec.encodeSeq Eth1Data.codec p b.eth1DataVotes),
    ("eth1_deposit_index", u.encode p a.eth1DepositIndex, u.encode p b.eth1DepositIndex),
    ("validators", Codec.encodeSeq Validator.codec p a.validators, Codec.encodeSeq Validator.codec p b.validators),
    ("balances", Codec.encodeSeq u p a.balances, Codec.encodeSeq u p b.balances),
    ("randao_mixes", Codec.encodeSeq Codec.bytes32 p a.randaoMixes, Codec.encodeSeq Codec.bytes32 p b.randaoMixes),
    ("slashings", Codec.encodeSeq u p a.slashings, Codec.encodeSeq u p b.slashings),
    ("previous_epoch_participation", a.previousEpochParticipation, b.previousEpochParticipation),
    ("current_epoch_participation", a.currentEpochParticipation, b.currentEpochParticipation),
    ("justification_bits", Codec.packBits a.justificationBits 1, Codec.packBits b.justificationBits 1),
    ("previous_justified_checkpoint", cp.encode p a.previousJustifiedCheckpoint, cp.encode p b.previousJustifiedCheckpoint),
    ("current_justified_checkpoint", cp.encode p a.currentJustifiedCheckpoint, cp.encode p b.currentJustifiedCheckpoint),
    ("finalized_checkpoint", cp.encode p a.finalizedCheckpoint, cp.encode p b.finalizedCheckpoint),
    ("inactivity_scores", Codec.encodeSeq u p a.inactivityScores, Codec.encodeSeq u p b.inactivityScores),
    ("current_sync_committee", SyncCommittee.codec.encode p a.currentSyncCommittee, SyncCommittee.codec.encode p b.currentSyncCommittee),
    ("next_sync_committee", SyncCommittee.codec.encode p a.nextSyncCommittee, SyncCommittee.codec.encode p b.nextSyncCommittee),
    ("latest_execution_payload_header", ExecutionPayloadHeader.codec.encode p a.latestExecutionPayloadHeader, ExecutionPayloadHeader.codec.encode p b.latestExecutionPayloadHeader),
    ("next_withdrawal_index", u.encode p a.nextWithdrawalIndex, u.encode p b.nextWithdrawalIndex),
    ("next_withdrawal_validator_index", u.encode p a.nextWithdrawalValidatorIndex, u.encode p b.nextWithdrawalValidatorIndex),
    ("historical_summaries", Codec.encodeSeq HistoricalSummary.codec p a.historicalSummaries, Codec.encodeSeq HistoricalSummary.codec p b.historicalSummaries),
    ("deposit_requests_start_index", u.encode p a.depositRequestsStartIndex, u.encode p b.depositRequestsStartIndex),
    ("deposit_balance_to_consume", u.encode p a.depositBalanceToConsume, u.encode p b.depositBalanceToConsume),
    ("exit_balance_to_consume", u.encode p a.exitBalanceToConsume, u.encode p b.exitBalanceToConsume),
    ("earliest_exit_epoch", u.encode p a.earliestExitEpoch, u.encode p b.earliestExitEpoch),
    ("consolidation_balance_to_consume", u.encode p a.consolidationBalanceToConsume, u.encode p b.consolidationBalanceToConsume),
    ("earliest_consolidation_epoch", u.encode p a.earliestConsolidationEpoch, u.encode p b.earliestConsolidationEpoch),
    ("pending_deposits", Codec.encodeSeq PendingDeposit.codec p a.pendingDeposits, Codec.encodeSeq PendingDeposit.codec p b.pendingDeposits),
    ("pending_partial_withdrawals", Codec.encodeSeq PendingPartialWithdrawal.codec p a.pendingPartialWithdrawals, Codec.encodeSeq PendingPartialWithdrawal.codec p b.pendingPartialWithdrawals),
    ("pending_consolidations", Codec.encodeSeq PendingConsolidation.codec p a.pendingConsolidations, Codec.encodeSeq PendingConsolidation.codec p b.pendingConsolidations),
    ("proposer_lookahead", Codec.encodeSeq u p a.proposerLookahead, Codec.encodeSeq u p b.proposerLookahead)]
  (fields.filter fun f => f.2.1 != f.2.2).map (·.1)

/-- A transition under test: context, pre-state, case directory contents. -/
abbrev Transition := Ctx → BeaconState → Except String BeaconState

/-- Run `step` on `pre.ssz_snappy` and compare with `post.ssz_snappy`; a
    case without a post-state passes exactly when the step is refused. -/
def transitionCase (o : Options) (dir : System.FilePath) (extraCtx : Ctx → Ctx)
    (load : IO (Except String Transition)) : IO (Status × String × Nat × Bool) := do
  let p := o.preset
  let metaText ← readText (dir / "meta.yaml")
  let bls := (yamlNat metaText "bls_setting").getD 0
  let verify := bls == 1 || (bls == 0 && o.verifyOptionalBls)
  let c := extraCtx { p, verifyBls := verify, blsOff := bls == 2 }
  let pre ← match BeaconState.codec.decode p (← readSnappy (dir / "pre.ssz_snappy")) with
    | .ok s => pure s
    | .error e => return (.fail, s!"pre-state does not decode: {e}", bls, verify)
  let post ← readOptional (dir / "post.ssz_snappy")
  let outcome := match ← load with
    | .error e => Except.error s!"input does not decode: {e}"
    | .ok step => (step c pre).bind fun s =>
        if s.inRange then .ok s else .error "a uint64 field left its range"
  match outcome, post with
  | .error _, none => return (.pass, "", bls, verify)
  | .ok _, none => return (.fail, "accepted an input the vector marks invalid", bls, verify)
  | .error e, some _ => return (.fail, s!"refused a valid input: {e}", bls, verify)
  | .ok s, some expected =>
    if (cachedStateRoot p s {}).1 != BeaconState.codec.root p s then
      return (.fail, "cached state root differs from the plain state root", bls, verify)
    else if BeaconState.codec.encode p s == expected then return (.pass, "", bls, verify)
    else match BeaconState.codec.decode p expected with
      | .ok e => return (.fail, s!"post-state differs in: {stateDiff p s e}", bls, verify)
      | .error e => return (.fail, s!"post-state vector does not decode: {e}", bls, verify)

def withOp {α : Type} (codec : Codec α) (p : Preset) (path : System.FilePath)
    (f : Ctx → BeaconState → α → Except String BeaconState) : IO (Except String Transition) := do
  match codec.decode p (← readSnappy path) with
  | .ok op => return .ok fun c s => f c s op
  | .error e => return .error e

def epochStep (handler : String) : Option Transition :=
  match handler with
  | "justification_and_finalization" => some fun c s => processJustificationAndFinalization c.p s
  | "inactivity_updates" => some fun c s => .ok (processInactivityUpdates c.p s)
  | "rewards_and_penalties" => some fun c s => .ok (processRewardsAndPenalties c.p s)
  | "registry_updates" => some fun c s => .ok (processRegistryUpdates c.p s)
  | "slashings" => some fun c s => .ok (processSlashings c.p s)
  | "eth1_data_reset" => some fun c s => .ok (processEth1DataReset c.p s)
  | "pending_deposits" => some fun c s => .ok (processPendingDeposits c s)
  | "pending_consolidations" => some fun c s => .ok (processPendingConsolidations c.p s)
  | "effective_balance_updates" => some fun _ s => .ok (processEffectiveBalanceUpdates s)
  | "slashings_reset" => some fun c s => .ok (processSlashingsReset c.p s)
  | "randao_mixes_reset" => some fun c s => .ok (processRandaoMixesReset c.p s)
  | "historical_summaries_update" => some fun c s => .ok (processHistoricalSummariesUpdate c.p s)
  | "participation_flag_updates" => some fun _ s => .ok (processParticipationFlagUpdates s)
  | "sync_committee_updates" => some fun c s => processSyncCommitteeUpdates c s
  | "proposer_lookahead" => some fun c s => processProposerLookahead c.p s
  | _ => none

def operationCase (o : Options) (handler : String) : Option CaseFn :=
  let p := o.preset
  let simple {α : Type} (codec : Codec α) (file : String)
      (f : Ctx → BeaconState → α → Except String BeaconState) : Option CaseFn :=
    some fun dir => transitionCase o dir id (withOp codec p (dir / file) f)
  match handler with
  | "attestation" => simple Attestation.codec "attestation.ssz_snappy" processAttestation
  | "attester_slashing" => simple AttesterSlashing.codec "attester_slashing.ssz_snappy" processAttesterSlashing
  | "proposer_slashing" => simple ProposerSlashing.codec "proposer_slashing.ssz_snappy" processProposerSlashing
  | "block_header" => simple BeaconBlock.codec "block.ssz_snappy" fun c s b => processBlockHeader c.p s b
  | "bls_to_execution_change" =>
    simple SignedBLSToExecutionChange.codec "address_change.ssz_snappy" processBlsToExecutionChange
  | "consolidation_request" => simple ConsolidationRequest.codec "consolidation_request.ssz_snappy"
      fun c s r => .ok (processConsolidationRequest c.p s r)
  | "deposit" => simple Deposit.codec "deposit.ssz_snappy" processDeposit
  | "deposit_request" => simple DepositRequest.codec "deposit_request.ssz_snappy"
      fun _ s r => .ok (processDepositRequest s r)
  | "sync_aggregate" => simple SyncAggregate.codec "sync_aggregate.ssz_snappy" processSyncAggregate
  | "voluntary_exit" => simple SignedVoluntaryExit.codec "voluntary_exit.ssz_snappy" processVoluntaryExit
  | "withdrawal_request" => simple WithdrawalRequest.codec "withdrawal_request.ssz_snappy"
      fun c s r => .ok (processWithdrawalRequest c.p s r)
  | "withdrawals" => simple ExecutionPayload.codec "execution_payload.ssz_snappy"
      fun c s payload => processWithdrawals c.p s payload
  | "execution_payload" => some fun dir => do
      let valid := (yamlBool (← readText (dir / "execution.yaml")) "execution_valid").getD true
      transitionCase o dir (fun c => { c with executionValid := valid })
        (withOp BeaconBlockBody.codec p (dir / "body.ssz_snappy") processExecutionPayload)
  | _ => none

def sanityCase (o : Options) (handler : String) : Option CaseFn :=
  let p := o.preset
  match handler with
  | "slots" => some fun dir => do
      let some n := firstNat (← readText (dir / "slots.yaml"))
        | return (.fail, "slots.yaml has no slot count", 0, false)
      transitionCase o dir id (pure (.ok fun c s => processSlots c s (s.slot + n)))
  | "blocks" => some fun dir => do
      let some n := yamlNat (← readText (dir / "meta.yaml")) "blocks_count"
        | return (.fail, "meta.yaml has no blocks_count", 0, false)
      let mut raw : Array ByteArray := #[]
      for i in [0:n] do
        raw := raw.push (← readSnappy (dir / s!"blocks_{i}.ssz_snappy"))
      transitionCase o dir id (pure (.ok fun c s =>
        raw.foldlM (fun s bytes =>
          match SignedBeaconBlock.codec.decode p bytes with
          | .ok block => stateTransition c s block
          | .error e => .error s!"block does not decode: {e}") s))
  | _ => none

def caseFnFor (o : Options) (runner handler : String) : Option CaseFn :=
  match runner with
  | "ssz_static" => some (sszStaticCase o handler)
  | "epoch_processing" => (epochStep handler).map fun step dir => transitionCase o dir id (pure (.ok step))
  | "operations" => operationCase o handler
  | "sanity" => sanityCase o handler
  | _ => none

def runCase (fn : CaseFn) (name : String) (dir : System.FilePath) : IO CaseResult := do
  let t0 ← IO.monoNanosNow
  let outcome ← (fn dir).toBaseIO
  let t1 ← IO.monoNanosNow
  let micros := (t1 - t0) / 1000
  match outcome with
  | .ok (status, detail, bls, verified) =>
    return { name, status, detail, blsSetting := bls, blsVerified := verified, micros }
  | .error e => return { name, status := .fail, detail := s!"harness error: {e}", micros }

def runAll (o : Options) (fn : CaseFn) (cases : Array (String × System.FilePath)) : IO (Array CaseResult) := do
  if o.jobs ≤ 1 then
    cases.mapM fun (name, dir) => runCase fn name dir
  else
    -- `jobs` workers, each running the cases whose index is congruent to its number.
    let workers ← (Array.range o.jobs).mapM fun w => IO.asTask (prio := .dedicated) do
      let mut mine : Array (Nat × CaseResult) := #[]
      for i in [0:cases.size] do
        if i % o.jobs == w then
          let (name, dir) := cases[i]!
          mine := mine.push (i, ← runCase fn name dir)
      return mine
    let mut slots : Array (Option CaseResult) := Array.replicate cases.size none
    for t in workers do
      match ← IO.wait t with
      | .ok mine => for (i, r) in mine do slots := slots.set! i (some r)
      | .error e => IO.eprintln s!"worker error: {e}"
    return (Array.range cases.size).map fun i =>
      match slots[i]! with
      | some r => r
      | none => { name := cases[i]!.1, status := .fail, detail := "worker did not return a result" }

structure HandlerSummary where
  runner : String
  handler : String
  results : Array CaseResult

def count (rs : Array CaseResult) (f : CaseResult → Bool) : Nat := (rs.filter f).size

def HandlerSummary.json (h : HandlerSummary) : String :=
  let rs := h.results
  let times := (rs.map (·.micros)).qsort (· < ·)
  let cnt (s : Status) := count rs (·.status == s)
  let failures := (rs.filter (·.status != .pass)).map fun r =>
    "{\"case\":" ++ jsonString r.name ++ ",\"status\":" ++
      jsonString (if r.status == .fail then "fail" else "unsupported") ++
      ",\"detail\":" ++ jsonString (String.ofList (r.detail.toList.take 300)) ++ "}"
  "{\"runner\":" ++ jsonString h.runner ++ ",\"handler\":" ++ jsonString h.handler ++
  s!",\"total\":{rs.size},\"pass\":{cnt .pass},\"fail\":{cnt .fail},\"unsupported\":{cnt .unsupported}" ++
  s!",\"bls_required\":{count rs (·.blsSetting == 1)},\"bls_required_pass\":{count rs (fun r => r.blsSetting == 1 && r.status == .pass)}" ++
  s!",\"bls_off\":{count rs (·.blsSetting == 2)},\"bls_off_pass\":{count rs (fun r => r.blsSetting == 2 && r.status == .pass)}" ++
  s!",\"bls_optional\":{count rs (·.blsSetting == 0)},\"bls_optional_pass\":{count rs (fun r => r.blsSetting == 0 && r.status == .pass)}" ++
  s!",\"signatures_checked\":{count rs (·.blsVerified)}" ++
  s!",\"p50_us\":{percentile times 50},\"p95_us\":{percentile times 95},\"max_us\":{percentile times 100}" ++
  ",\"not_passing\":[" ++ ",".intercalate failures.toList ++ "]}"

/-- Grow the registry of `s` to `n` validators by repeating its entries,
    each a separate object with its own (not valid) public key bytes;
    enough for the steps timed below, which check no signature. -/
def growRegistry (s : BeaconState) (n : Nat) : BeaconState :=
  let m := s.validators.size
  if n ≤ m || m = 0 then s
  else
    let pick {α : Type} [Inhabited α] (xs : Array α) : Array α := (Array.range n).map fun i => xs[i % m]!
    { s with
      validators := (Array.range n).map fun i =>
        { s.validators[i % m]! with pubkey := natLE (i + 1) 48 }
      balances := pick s.balances
      inactivityScores := pick s.inactivityScores
      previousEpochParticipation := ⟨(Array.range n).map fun i => s.previousEpochParticipation.get! (i % m)⟩
      currentEpochParticipation := ⟨(Array.range n).map fun i => s.currentEpochParticipation.get! (i % m)⟩ }

/-- Time each epoch sub-step once on a state grown to `--validators`
    entries. A scaling measurement, not a conformance test. -/
def benchEpoch (o : Options) (path : System.FilePath) : IO UInt32 := do
  let p := o.preset
  let c : Ctx := { p, verifyBls := false }
  let base ← match BeaconState.codec.decode p (← readSnappy path) with
    | .ok s => pure s
    | .error e => IO.eprintln s!"state does not decode: {e}"; return 2
  let s := growRegistry base o.benchValidators
  IO.println s!"bench-epoch preset {p.name} validators {s.validators.size} slot {s.slot}"
  let steps : List (String × (BeaconState → Except String BeaconState)) := [
    ("justification_and_finalization", processJustificationAndFinalization p),
    ("inactivity_updates", fun s => .ok (processInactivityUpdates p s)),
    ("rewards_and_penalties", fun s => .ok (processRewardsAndPenalties p s)),
    ("registry_updates", fun s => .ok (processRegistryUpdates p s)),
    ("slashings", fun s => .ok (processSlashings p s)),
    ("eth1_data_reset", fun s => .ok (processEth1DataReset p s)),
    ("pending_deposits", fun s => .ok (processPendingDeposits c s)),
    ("pending_consolidations", fun s => .ok (processPendingConsolidations p s)),
    ("effective_balance_updates", fun s => .ok (processEffectiveBalanceUpdates s)),
    ("slashings_reset", fun s => .ok (processSlashingsReset p s)),
    ("randao_mixes_reset", fun s => .ok (processRandaoMixesReset p s)),
    ("historical_summaries_update", fun s => .ok (processHistoricalSummariesUpdate p s)),
    ("participation_flag_updates", fun s => .ok (processParticipationFlagUpdates s)),
    ("proposer_lookahead", processProposerLookahead p)]
  let mut state := s
  let mut total := 0
  for (name, step) in steps do
    let t0 ← IO.monoNanosNow
    match step state with
    | .ok next =>
      -- Force the fields the steps write before reading the clock.
      let witness := next.balances.size + next.validators.size + next.inactivityScores.size +
        next.currentEpochParticipation.size + next.proposerLookahead.foldl (· + ·) 0 +
        (next.balances.foldl (· + ·) 0) % 2 + (next.validators.foldl (fun acc v => acc + v.effectiveBalance) 0) % 2
      let t1 ← IO.monoNanosNow
      IO.println s!"  {name}: {(t1 - t0) / 1000} us (witness {witness % 10})"
      total := total + (t1 - t0) / 1000
      state := next
    | .error e =>
      IO.println s!"  {name}: refused: {e}"
  IO.println s!"  epoch sub-steps total: {total} us"
  let t0 ← IO.monoNanosNow
  IO.println s!"  state root {toHex ((stateRoot p state).extract 0 4)}"
  let t1 ← IO.monoNanosNow
  IO.println s!"  hash_tree_root(state), plain: {(t1 - t0) / 1000} us"
  let (root1, cache) := cachedStateRoot p state {}
  IO.println s!"  state root {toHex (root1.extract 0 4)}"
  let t2 ← IO.monoNanosNow
  IO.println s!"  hash_tree_root(state), cache built from empty: {(t2 - t1) / 1000} us"
  -- A slot's worth of change: one balance, one validator, two history roots.
  let changed := { (state.increaseBalance 7 1) with
    validators := state.validators.modify 11 fun v => { v with effectiveBalance := v.effectiveBalance + 1 }
    stateRoots := state.stateRoots.set! 3 root1
    blockRoots := state.blockRoots.set! 3 root1 }
  let t3 ← IO.monoNanosNow
  let (root2, _) := cachedStateRoot p changed cache
  IO.println s!"  state root {toHex (root2.extract 0 4)}"
  let t4 ← IO.monoNanosNow
  IO.println s!"  hash_tree_root(changed state), from the cache: {(t4 - t3) / 1000} us"
  IO.println s!"  cached root equals plain root: {root2 == stateRoot p changed}"
  return 0

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  if let some path := o.benchState then return ← benchEpoch o path
  let base := o.vectors / "tests" / o.preset.name / o.fork
  let runners := if o.runners.isEmpty then ["ssz_static", "epoch_processing", "operations", "sanity"] else o.runners
  let mut summaries : Array HandlerSummary := #[]
  for runner in runners do
    for handler in ← sortedDir (base / runner) do
      if o.handler.any (· != handler) then continue
      let mut cases : Array (String × System.FilePath) := #[]
      for suite in ← sortedDir (base / runner / handler) do
        for c in ← sortedDir (base / runner / handler / suite) do
          if o.caseFilter.any (fun f => (c.splitOn f).length < 2) then continue
          cases := cases.push (s!"{suite}/{c}", base / runner / handler / suite / c)
      let results ← match caseFnFor o runner handler with
        | some fn => runAll o fn cases
        | none => pure (cases.map fun (name, _) =>
            { name, status := .unsupported, detail := s!"no implementation for {runner}/{handler}" })
      let s : HandlerSummary := { runner, handler, results }
      let times := (results.map (·.micros)).qsort (· < ·)
      IO.println s!"{runner}/{handler}: total {results.size} pass {count results (·.status == .pass)} fail {count results (·.status == .fail)} unsupported {count results (·.status == .unsupported)} | p50 {percentile times 50}us p95 {percentile times 95}us max {percentile times 100}us"
      for r in results do
        if r.status == .fail then IO.println s!"  FAIL {r.name}: {String.ofList (r.detail.toList.take 200)}"
      (← IO.getStdout).flush
      summaries := summaries.push s
  let all := summaries.foldl (fun acc s => acc ++ s.results) #[]
  IO.println s!"TOTAL {o.preset.name}/{o.fork}: total {all.size} pass {count all (·.status == .pass)} fail {count all (·.status == .fail)} unsupported {count all (·.status == .unsupported)}"
  if let some path := o.json then
    IO.FS.writeFile path
      ("{\"preset\":" ++ jsonString o.preset.name ++ ",\"fork\":" ++ jsonString o.fork ++
       s!",\"optional_bls_verified\":{o.verifyOptionalBls}" ++
       ",\"handlers\":[\n" ++ ",\n".intercalate (summaries.map (·.json)).toList ++ "\n]}\n")
  return 0
