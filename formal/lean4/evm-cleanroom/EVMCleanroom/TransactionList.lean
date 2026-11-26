import EVMCleanroom.BlobCall

/-!
# Ordered decoded Cancun call transactions

One initial witness inventory and one checked header pair enter this runner.
Every intermediate state and gas counter is derived inside Lean. This is not
full block validation: signed bytes, trie commitments, beacon-root processing,
withdrawals and chain membership remain outside this transition.
-/
namespace EVMCleanroom.TransactionList

open CallTransaction

structure BlobFields where
  hashes : Array (Array UInt8)
  maxFeePerBlobGas : Nat

structure Entry where
  tx : Envelope
  fuel : Nat
  blob : Option BlobFields := none

structure Input where
  parent : HeaderRLP.Fields
  child : HeaderRLP.Fields
  initialWitnesses : List WitnessAccount
  transactions : List Entry

/-- Local simulation and transport bounds, not Ethereum validity rules. -/
def maxTransactions : Nat := 256
def maxReservedFuel : Nat := CallTransaction.maxFuel
def maxInputBytes : Nat := CallTransaction.maxDataBytes
def maxObservationBytes : Nat := CallTransaction.maxDataBytes
def maxSerializedBytes : Nat := 4 * maxInputBytes

/-- Bounded-prefix inspection refuses before traversing an arbitrary suffix. -/
def countFits {α : Type} : Nat → List α → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, _ :: rest => countFits n rest

def witnessResources (ws : List WitnessAccount) : Bool :=
  !countFits maxAccounts ws ||
  ws.any (fun w => w.code.size > 1048576 || !countFits maxKeysPerAccount w.storage) ||
  ws.foldl (fun n w => n + w.code.size) 0 > maxInputBytes ||
  ws.foldl (fun n w => n + w.storage.length) 0 > 16384

def reservedFuel (entries : List Entry) : Nat :=
  entries.foldl (fun n entry => n + entry.fuel) 0

/-- Called only after the transaction, witness and hash-inventory counts pass.
    Array sizes are inspected without reading every byte. -/
def inputBytes (p : Input) : Nat :=
  p.initialWitnesses.foldl (fun n w => n + w.code.size) 0 +
  p.transactions.foldl (fun n entry => n + entry.tx.data.size +
    (entry.blob.map (fun b => b.hashes.foldl (fun m hash => m + hash.size) 0)).getD 0) 0

inductive Failure where
  | rejected (reason : String)
  | indeterminate (reason : Unavailable)

/-- Validate aggregate resource and initial witness bounds before list execution.
    Individual envelopes retain the ordinary/blob runner's admission checks. -/
def preflight (p : Input) : Except Failure Unit :=
  if !countFits maxTransactions p.transactions then .error (.indeterminate (.frame .resourceLimit))
  else if witnessResources p.initialWitnesses then .error (.indeterminate (.frame .resourceLimit))
  else if p.transactions.any (fun e => e.blob.any (fun b => b.hashes.size > 128)) then
    .error (.indeterminate (.frame .resourceLimit))
  else if reservedFuel p.transactions > maxReservedFuel || inputBytes p > maxInputBytes then
    .error (.indeterminate (.frame .resourceLimit))
  else if !(decide ((p.initialWitnesses.map (·.address)).Nodup) &&
      p.initialWitnesses.all WitnessAccount.valid) then .error (.indeterminate .invalidWitness)
  else .ok ()

/-- Refresh covered values from the actual settled world. The address and slot
    inventory stay fixed; no new state witness is accepted from the host. -/
def refreshWitness (world : World.TxWorld) (w : WitnessAccount) : WitnessAccount :=
  let account := world.accounts w.address
  { address := w.address
    present := CallValue.accountAlive account
    balance := account.balance
    nonce := account.nonce
    code := account.code
    storage := w.storage.map (fun slot => { key := slot.key, value := account.storage slot.key }) }

def refreshWitnesses (world : World.TxWorld) (ws : List WitnessAccount) : List WitnessAccount :=
  ws.map (refreshWitness world)

/-- Only derived prefix counters and the checked common header environment
    enter each request. The next witnessWorld creates fresh transaction state. -/
def requestFor (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (ws : List WitnessAccount) (gasUsed : Nat) (entry : Entry) : Request :=
  { fork := .cancun, fuel := entry.fuel, tx := entry.tx
    block := BlobCall.blockContext p.child gasUsed fees
    witnesses := ws, keccakAcceptance := some a }

structure Transition where
  result : CallTransaction.Result
  blobGasUsed : Nat
  blobFeeBurn : Nat

def fromTransaction (out : CallTransaction.Outcome) (blobGas blobBurn : Nat) : Except Failure Transition :=
  match out with
  | .rejected reason => .error (.rejected reason)
  | .indeterminate reason => .error (.indeterminate reason)
  | .executed result => .ok { result, blobGasUsed := blobGas, blobFeeBurn := blobBurn }

/-- The standalone blob adapter receives a caller-supplied prefix and cannot
    classify an inconsistent position as block invalidity. Here run derives
    that prefix: exceeding a declared total already establishes a mismatch,
    because all subsequent execution/blob charges are nonnegative. Other
    unavailable blob evidence retains its original refusal classification. -/
def fromBlobRefusal : BlobCall.Refusal → Failure
  | .rejected reason => .rejected reason
  | .indeterminate reason =>
    if reason == "inconsistent-block-position" then .rejected "declared-gas-total-exceeded"
    else .indeterminate (.unsupported reason)

/-- Run one entry through the existing transaction paths. Header fees were
    checked once by run, so type 3 reuses prepareWithFees and execute directly.
    A failed receipt remains an executed transition and consumes blob gas. -/
def runEntry (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (ws : List WitnessAccount) (gasUsed blobGasUsed : Nat) (entry : Entry) :
    Except Failure Transition :=
  let request := requestFor a p fees ws gasUsed entry
  if entry.tx.kind > 3 then .error (.indeterminate (.unsupported "unsupported-transaction-type"))
  else if entry.tx.kind = 3 then
    match entry.blob with
    | none => .error (.rejected "missing-blob-fields")
    | some blob =>
      let input : BlobCall.Input := {
        request, parent := p.parent, child := p.child, hashes := blob.hashes
        blobCap := blob.maxFeePerBlobGas, priorBlobGas := blobGasUsed }
      match BlobCall.prepareWithFees input fees with
      | .error reason => .error (fromBlobRefusal reason)
      | .ok ready =>
        match BlobCall.execute ready (HeaderRLP.readNat p.child 10) with
        | .refused reason => .error (fromBlobRefusal reason)
        | .transaction prepared result => fromTransaction result prepared.blobGas prepared.burn
  else if entry.blob.isSome then .error (.rejected "ordinary-blob-fields")
  else fromTransaction (CallTransaction.run request) 0 0

/-- Compact observations retain no intermediate TxWorld. Receipt/trie encoding
    and root verification remain separate from these execution fields. -/
structure Receipt where
  kind : Nat
  frame : FrameStatus
  receiptStatus : Bool
  output : ByteView
  charge : Charge
  cumulativeGasUsed : Nat
  effectiveGasPrice : Nat
  logs : List LogEntry
  blobGasUsed : Nat
  blobFeeBurn : Nat

def receiptOf (entry : Entry) (step : Transition) : Receipt :=
  { kind := entry.tx.kind, frame := step.result.frame, receiptStatus := step.result.receiptStatus
    output := step.result.output, charge := step.result.charge
    cumulativeGasUsed := step.result.cumulativeGasUsed
    effectiveGasPrice := step.result.effectiveGasPrice, logs := step.result.logs
    blobGasUsed := step.blobGasUsed, blobFeeBurn := step.blobFeeBurn }

def observationBytes (step : Transition) : Nat :=
  step.result.logs.foldl (fun n log => n + log.data.size + 32 * log.topics.length + 20)
    step.result.output.size

structure Cursor where
  witnesses : List WitnessAccount
  gasUsed : Nat := 0
  blobGasUsed : Nat := 0
  receiptsRev : List Receipt := []
  observationBytes : Nat := 0
  index : Nat := 0

def initial (p : Input) : Cursor := { witnesses := p.initialWitnesses }

/-- Guard the retained observation budget before extending the receipt list.
    Refresh state from the actual settled world, including status-zero results. -/
def advance (cursor : Cursor) (entry : Entry) (step : Transition) : Except Failure Cursor :=
  let bytes := cursor.observationBytes + observationBytes step
  if bytes > maxObservationBytes then .error (.indeterminate (.frame .resourceLimit))
  else .ok {
    witnesses := refreshWitnesses step.result.world cursor.witnesses
    gasUsed := cursor.gasUsed + step.result.charge.used
    blobGasUsed := cursor.blobGasUsed + step.blobGasUsed
    receiptsRev := receiptOf entry step :: cursor.receiptsRev
    observationBytes := bytes
    index := cursor.index + 1 }

structure IndexedFailure where
  index : Nat
  reason : Failure

/-- Structural recursion visits at most the preflight-bounded transaction list.
    Each entry's instruction allowance is reserved in the aggregate fuel cap. -/
def loop (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat) :
    Cursor → List Entry → Except IndexedFailure Cursor
  | cursor, [] => .ok cursor
  | cursor, entry :: rest =>
    match runEntry a p fees cursor.witnesses cursor.gasUsed cursor.blobGasUsed entry with
    | .error reason => .error { index := cursor.index, reason }
    | .ok result =>
      match advance cursor entry result with
      | .error reason => .error { index := cursor.index, reason }
      | .ok next => loop a p fees next rest

structure Result where
  receipts : List Receipt
  finalWitnesses : List WitnessAccount
  gasUsed : Nat
  blobGasUsed : Nat
  observationBytes : Nat

inductive Outcome where
  | accepted (result : Result)
  | rejected (index : Option Nat) (reason : String)
  | indeterminate (index : Option Nat) (reason : Unavailable)

def refusal (index : Option Nat) : Failure → Outcome
  | .rejected reason => .rejected index reason
  | .indeterminate reason => .indeterminate index reason

/-- Exact totals are checked for the supplied ordered list. This does not
    authenticate that list against the header's transaction commitment. -/
def finish (p : Input) (cursor : Cursor) : Outcome :=
  if cursor.gasUsed != HeaderRLP.readNat p.child 10 then .rejected none "execution-gas-total-mismatch"
  else if cursor.blobGasUsed != HeaderRLP.readNat p.child 17 then .rejected none "blob-gas-total-mismatch"
  else .accepted {
    receipts := cursor.receiptsRev.reverse, finalWitnesses := cursor.witnesses
    gasUsed := cursor.gasUsed, blobGasUsed := cursor.blobGasUsed
    observationBytes := cursor.observationBytes }

/-- One pure transition over the entire supplied list. Failure exposes no
    accepted partial state or receipt list. The fork guard also covers ordinary
    and empty lists, so a later timestamp cannot silently use Cancun settlement. -/
def run (a : Keccak.Acceptance) (p : Input) : Outcome :=
  match preflight p with
  | .error reason => refusal none reason
  | .ok () =>
    let timestamp := HeaderRLP.readNat p.child 11
    if timestamp < HeaderRLP.cancunTime || timestamp ≥ HeaderRLP.pragueTime then
      .indeterminate none (.unsupported "outside-cancun-transaction-rules")
    else
      match HeaderRLP.checkedFeePair a p.parent p.child with
      | .error _ => .indeterminate none (.unsupported "header-pair-refused")
      | .ok fees =>
        match loop a p fees (initial p) p.transactions with
        | .error fail => refusal (some fail.index) fail.reason
        | .ok cursor => finish p cursor

end EVMCleanroom.TransactionList
