import EVMCleanroom.HeaderRLP
import EVMCleanroom.CallTransaction

/-! Cancun decoded blob call transactions. The actual ordinary transaction
runner supplies the EVM, nonce, execution gas, value, refund, tip and
checkpoint. The additional debit occurs before that checkpoint. The
caller still authenticates the envelope, header and account witnesses;
the transaction inventory and KZG sidecars are not verified here.
Prague is deliberately refused (its calldata floor is not in that runner). -/
namespace EVMCleanroom.BlobCall

open CallTransaction

structure Input where
  request : Request
  parent : HeaderRLP.Fields
  child : HeaderRLP.Fields
  hashes : Array (Array UInt8)
  blobCap : Nat
  priorBlobGas : Nat

inductive Refusal where
  | rejected (reason : String)
  | indeterminate (reason : String)

structure Prepared where
  request : Request
  blobGas : Nat
  burn : Nat
  txBlobHashes : Array Word

def gas (hashes : Array (Array UInt8)) : Nat :=
  HeaderRLP.gasPerBlob * hashes.size

def validHash (h : Array UInt8) : Bool :=
  h.size == 32 && (h[0]?).getD 0 == 1

/-- Big-endian hash bytes become one full EVM word. The admitted path invokes
    this only after the one-to-six count and exact 32-byte version checks. -/
def hashWord (h : Array UInt8) : Word :=
  word (h.foldl (fun acc byte => acc * 256 + byte.toNat) 0)

def maximumUpfront (tx : Envelope) (blobGas blobCap : Nat) : Nat :=
  tx.gasLimit * tx.gasPriceCap + tx.value + blobGas * blobCap

def affordable (tx : Envelope) (balance blobGas blobCap : Nat) : Bool :=
  decide (maximumUpfront tx blobGas blobCap ≤ balance)

/-- The fee comes out of the sender witness BEFORE the existing runner
creates its fee-paid, nonce-incremented checkpoint. No refund path can
re-credit this debit. Original witness authenticity remains external. -/
def burnWitness (sender amount : Nat) (w : WitnessAccount) : WitnessAccount :=
  if w.address = sender then { w with balance := w.balance - amount } else w

def blockContext (h : HeaderRLP.Fields) (priorGas : Nat) (fees : Nat × Nat) : BlockContext :=
  { chainId := 1
    coinbase := HeaderRLP.readNat h 2
    number := HeaderRLP.readNat h 8
    timestamp := HeaderRLP.readNat h 11
    gasLimit := HeaderRLP.readNat h 9
    gasUsedBefore := priorGas
    baseFee := fees.1
    prevRandao := HeaderRLP.readNat h 13
    blobBaseFee := fees.2 }

/-- The type-2-shaped input is INTERNAL accounting only: the wire type
was checked as 3 and its blob constraints separately checked. -/
def prepareRequest (p : Input) (fees : Nat × Nat) : Prepared :=
  let b := gas p.hashes
  let burn := b * fees.2
  let request := { p.request with
    fork := .cancun
    tx := { p.request.tx with kind := 2 }
    block := blockContext p.child p.request.block.gasUsedBefore fees
    witnesses := p.request.witnesses.map (burnWitness p.request.tx.sender burn) }
  { request := request, blobGas := b, burn := burn
    txBlobHashes := p.hashes.map hashWord }

def checkFunds (p : Input) (fees : Nat × Nat) (sender : WitnessAccount) :
    Except Refusal Prepared :=
  if !affordable p.request.tx sender.balance (gas p.hashes) p.blobCap then
    .error (.rejected "insufficient-upfront-balance")
  else .ok (prepareRequest p fees)

def prepareWithFees (p : Input) (fees : Nat × Nat) : Except Refusal Prepared :=
  let r := p.request
  if r.tx.kind != 3 then .error (.indeterminate "not-type-3")
  else if r.tx.create then .error (.rejected "blob-creation")
  else if HeaderRLP.readNat p.child 11 >= HeaderRLP.pragueTime then
    .error (.indeterminate "later-transaction-rules")
  else if r.exceedsResources then .error (.indeterminate "resource-limit")
  else if !(decide ((r.witnesses.map (·.address)).Nodup) &&
      r.witnesses.all WitnessAccount.valid) then .error (.indeterminate "invalid-witness")
  else if p.hashes.isEmpty then .error (.rejected "missing-blob")
  else if p.hashes.size > 6 then .error (.rejected "too-many-blobs")
  else if !(p.hashes.all validHash) then .error (.rejected "invalid-versioned-hash")
  else if p.blobCap >= modulus then .error (.rejected "blob-cap-out-of-range")
  else if p.blobCap < fees.2 then .error (.rejected "blob-cap-below-current-fee")
  else if p.priorBlobGas % HeaderRLP.gasPerBlob != 0 ||
      p.priorBlobGas + gas p.hashes > HeaderRLP.readNat p.child 17 ||
      r.block.gasUsedBefore > HeaderRLP.readNat p.child 10 then
    .error (.indeterminate "inconsistent-block-position")
  else match r.witnesses.find? (fun w => w.address == r.tx.sender) with
    | none => .error (.indeterminate "missing-sender-witness")
    | some sender => checkFunds p fees sender

def prepare (a : Keccak.Acceptance) (p : Input) : Except Refusal Prepared :=
  match HeaderRLP.checkedFeePair a p.parent p.child with
  | .error _ => .error (.indeterminate "header-pair-refused")
  | .ok fees => prepareWithFees p fees

inductive Outcome where
  | refused (reason : Refusal)
  | transaction (p : Prepared) (result : CallTransaction.Outcome)

/-- Only the original transaction runner may produce a receipt. The
caller-supplied partial block position cannot exceed the declared total. -/
def execute (p : Prepared) (declaredGas : Nat) : Outcome :=
  match CallTransaction.runWithBlobHashes p.request p.txBlobHashes with
  | .executed result =>
    if result.cumulativeGasUsed > declaredGas then
      .refused (.indeterminate "inconsistent-block-position")
    else .transaction p (.executed result)
  | other => .transaction p other

def run (a : Keccak.Acceptance) (p : Input) : Outcome :=
  match prepare a p with
  | .error reason => .refused reason
  | .ok ready => execute ready (HeaderRLP.readNat p.child 10)

/-- Kind: projection. Says: exact preburn and preserved sender nonce.
Does not say: witness membership or sufficient balance is authenticated. -/
theorem burn_sender (w : WitnessAccount) (amount : Nat) :
    burnWitness w.address amount w = { w with balance := w.balance - amount } := by
  simp [burnWitness]

/-- Kind: projection. Says: other witnesses are unchanged.
Does not say: the inventory is complete. -/
theorem burn_other (w : WitnessAccount) (sender amount : Nat)
    (h : w.address ≠ sender) : burnWitness sender amount w = w := by
  simp [burnWitness, h]

/-- Kind: arithmetic. Says: if funded, debit plus burn equals original balance.
Does not say: the burn price itself is correct. -/
theorem burn_exact (w : WitnessAccount) (amount : Nat) (h : amount ≤ w.balance) :
    (burnWitness w.address amount w).balance + amount = w.balance := by
  rw [burn_sender]
  exact Nat.sub_add_cancel h

/-- Kind: admission. Says: the actual funds gate accepts only full cap
affordability, including value and execution maximum.
Does not say: the caller authenticated the account. -/
theorem funds_refused (p : Input) (fees : Nat × Nat) (w : WitnessAccount)
    (h : w.balance < maximumUpfront p.request.tx (gas p.hashes) p.blobCap) :
    checkFunds p fees w = .error (.rejected "insufficient-upfront-balance") := by
  simp [checkFunds, affordable, Nat.not_le.mpr h]

/-- Kind: composition. Says: the prepared runner uses derived prices,
the declared header coinbase and the exact preburn inventory.
Does not say: the header is a canonical chain member. -/
theorem prepared_exact (p : Input) (fees : Nat × Nat) :
    (prepareRequest p fees).request.block.baseFee = fees.1 ∧
    (prepareRequest p fees).request.block.blobBaseFee = fees.2 ∧
    (prepareRequest p fees).request.block.coinbase = HeaderRLP.readNat p.child 2 ∧
    (prepareRequest p fees).request.witnesses =
      p.request.witnesses.map (burnWitness p.request.tx.sender (gas p.hashes * fees.2)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Kind: composition. Says: a header refusal cannot enter execution.
Does not say: the pair checker is complete. -/
theorem header_refused (a : Keccak.Acceptance) (p : Input) (e : HeaderRLP.Error)
    (h : HeaderRLP.checkedFeePair a p.parent p.child = .error e) :
    run a p = .refused (.indeterminate "header-pair-refused") := by
  simp [run, prepare, h]

/-- Kind: composition. Says: an admitted request with a returned receipt
within the declared gas total exposes exactly the existing runner result.
Does not say: full transaction inventory or receipts-root authentication. -/
theorem execute_exact (p : Prepared) (declaredGas : Nat) (r : CallTransaction.Result)
    (h : CallTransaction.runWithBlobHashes p.request p.txBlobHashes = .executed r)
    (hg : r.cumulativeGasUsed ≤ declaredGas) :
    execute p declaredGas = .transaction p (.executed r) := by
  simp [execute, h, Nat.not_lt.mpr hg]

/-- Kind: executable projection.
    Says: preparation preserves hash order and every complete word through
    the internal accounting-type conversion; it cannot infer an empty context
    from the internal type-2 shape.
    Does not say: that `prepareRequest` alone performs admission checks. -/
theorem prepared_blobHashes (p : Input) (fees : Nat × Nat) :
    (prepareRequest p fees).txBlobHashes = p.hashes.map hashWord := rfl

#print axioms burn_sender
#print axioms burn_other
#print axioms burn_exact
#print axioms funds_refused
#print axioms prepared_exact
#print axioms header_refused
#print axioms execute_exact
#print axioms prepared_blobHashes

end EVMCleanroom.BlobCall
