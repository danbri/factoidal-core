import Beacon.Harness

/-!
# Runner for the official consensus test vectors (Fulu)

`beacon-spec-tests --vectors DIR --preset minimal|mainnet [--runner R]
[--handler H] [--case SUBSTRING] [--jobs N] [--bls-optional verify|skip]
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

def caseFnFor (o : Options) (runner handler : String) : Option CaseFn :=
  match runner with
  | "ssz_static" => some (sszStaticCase o handler)
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
    let mut out := #[]
    let mut i := 0
    while i < cases.size do
      let batch := cases.extract i (i + o.jobs)
      let tasks ← batch.mapM fun (name, dir) => IO.asTask (runCase fn name dir)
      for t in tasks do
        match ← IO.wait t with
        | .ok r => out := out.push r
        | .error e => out := out.push { name := "?", status := .fail, detail := s!"task error: {e}" }
      i := i + o.jobs
    return out

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

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
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
