import EVMCleanroom.CallOpcode
import EVMCleanroom.TxAccounting

/-!
# Witness-limited ordinary Ethereum call transactions

The host authenticates the signed envelope, header context, account and
storage witnesses, and code bytes. Lean validates and executes the admitted
Shanghai and Cancun type-0/1/2 call, including fee escrow and settlement.
Receipt and trie serialisation remain at the host boundary.
-/

namespace EVMCleanroom.CallTransaction

open World

inductive Fork where
  | shanghai
  | cancun
  deriving DecidableEq, Repr

def Fork.profile : Fork → Profile
  | .shanghai => .shanghaiPlus
  | .cancun => .cancunPlus

def Fork.precompileLimit : Fork → Nat
  | .shanghai => 0x09
  | .cancun => 0x0a

structure Access where
  address : Nat
  storageKeys : List Nat

structure Envelope where
  kind : Nat
  signedChainId : Option Nat
  sender : Nat
  to : Nat
  nonce : Nat
  value : Nat
  gasLimit : Nat
  gasPriceCap : Nat
  priorityFeeCap : Nat
  data : Array UInt8
  accessList : List Access

structure BlockContext where
  chainId : Nat
  coinbase : Nat
  number : Nat
  timestamp : Nat
  gasLimit : Nat
  gasUsedBefore : Nat
  baseFee : Nat
  prevRandao : Nat
  blobBaseFee : Nat

structure Slot where
  key : Nat
  value : Nat

/-- Every replay address is explicit, including a proved absence. Each listed
    storage entry can authenticate a present value or a zero word. -/
structure WitnessAccount where
  address : Nat
  present : Bool
  balance : Nat
  nonce : Nat
  code : Array UInt8
  storage : List Slot

def WitnessAccount.account (w : WitnessAccount) : Account :=
  { balance := w.balance, nonce := w.nonce, code := w.code
    storage := fun key => ((w.storage.find? (fun entry => entry.key == key)).map (·.value)).getD 0 }

structure Request where
  fork : Fork
  fuel : Nat
  tx : Envelope
  block : BlockContext
  witnesses : List WitnessAccount
  keccakAcceptance : Option Keccak.Acceptance := none

inductive Unavailable where
  | frame (error : Error)
  | invalidWitness
  | unsupported (reason : String)

inductive FrameStatus where
  | stopped
  | returned
  | reverted
  | exceptional (error : Error)

/-- Simulation resource limits, independent of fork validity. -/
def maxGas : Nat := 100000000
def maxFuel : Nat := 1000000
def maxDataBytes : Nat := 16777216

def maxAccounts : Nat := 1024
def maxAccessEntries : Nat := 4096
def maxKeysPerAccount : Nat := 4096

/-- Test a list bound without traversing an arbitrarily long suffix. -/
private def countFits {α : Type} : Nat → List α → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, _ :: rest => countFits n rest

def Request.exceedsResources (p : Request) : Bool :=
  p.tx.gasLimit > maxGas || p.fuel > maxFuel || p.tx.data.size > maxDataBytes ||
  !countFits maxAccounts p.witnesses || !countFits maxAccessEntries p.tx.accessList ||
  p.witnesses.any (fun w => w.code.size > 1048576 || !countFits maxKeysPerAccount w.storage) ||
  p.tx.accessList.any (fun access => !countFits maxKeysPerAccount access.storageKeys) ||
  p.witnesses.foldl (fun n w => n + w.code.size) 0 > maxDataBytes ||
  p.witnesses.foldl (fun n w => n + w.storage.length) 0 > 16384 ||
  p.tx.accessList.foldl (fun n access => n + access.storageKeys.length) 0 > 16384

def nonceBound : Nat := 2 ^ 64

def BlockContext.bounded (block : BlockContext) (fork : Fork) : Bool :=
  decide (block.chainId < nonceBound ∧ block.coinbase < addressBound ∧
    block.number < nonceBound ∧ block.timestamp < nonceBound ∧ block.gasLimit < nonceBound ∧
    block.gasUsedBefore ≤ block.gasLimit ∧ block.baseFee < modulus ∧
    block.prevRandao < modulus ∧ block.blobBaseFee < modulus) &&
  (if fork = .cancun then block.blobBaseFee != 0 else block.blobBaseFee == 0)

def WitnessAccount.valid (w : WitnessAccount) : Bool :=
  decide (w.address < addressBound ∧ w.balance < modulus ∧ w.nonce < nonceBound ∧
    (w.storage.map (·.key)).Nodup) &&
  w.storage.all (fun entry => decide (entry.key < modulus ∧ entry.value < modulus)) &&
  (if w.present then CallValue.accountAlive w.account
   else w.balance == 0 && w.nonce == 0 && w.code.isEmpty && w.storage.isEmpty)

/-- Input-dependent costs are derived from the envelope itself. Duplicate
    access-list entries are charged individually and warmed only as a set. -/
def accountingInput (tx : Envelope) (block : BlockContext) (sender : Account) : TxAccounting.Input :=
  let zeroBytes := tx.data.foldl (fun n b => if b == 0 then n + 1 else n) 0
  { zeros := zeroBytes, nonzeros := tx.data.size - zeroBytes
    accessAddresses := tx.accessList.length
    accessKeys := tx.accessList.foldl (fun n e => n + e.storageKeys.length) 0
    gasLimit := tx.gasLimit, gasPriceCap := tx.gasPriceCap, priorityCap := tx.priorityFeeCap
    baseFee := block.baseFee, senderBalance := sender.balance, senderNonce := sender.nonce
    executionUsed := 0, feeMarket := tx.kind == 2 }

structure Budget where
  intrinsic : Nat
  gasLimit : Nat
  price : Nat
  baseFee : Nat

def Budget.frameGas (budget : Budget) : Nat := budget.gasLimit - budget.intrinsic

def Budget.escrow (budget : Budget) : Nat := budget.gasLimit * budget.price

/-- Validate the decoded ordinary call before entering any frame. The host
    supplies the recovered sender and the chain identity from signed bytes. -/
def admit (tx : Envelope) (block : BlockContext) (sender : Account) : Except String Budget :=
  let input := accountingInput tx block sender
  let intrinsic := TxAccounting.intrinsicGas input
  let price := TxAccounting.effectivePrice input
  if tx.kind > 2 then .error "unsupported-transaction-type"
  else if tx.sender ≥ addressBound || tx.to ≥ addressBound || tx.value ≥ modulus ||
      tx.gasPriceCap ≥ modulus || tx.priorityFeeCap ≥ modulus then .error "envelope-out-of-range"
  else if tx.signedChainId.isNone && tx.kind != 0 then .error "missing-chain-id"
  else if tx.signedChainId.any (fun id => id != block.chainId) then .error "chain-id-mismatch"
  else if tx.nonce != sender.nonce || tx.nonce ≥ nonceBound - 1 then .error "invalid-sender-nonce"
  else if !sender.code.isEmpty then .error "sender-has-code"
  else if tx.kind == 0 && !tx.accessList.isEmpty then .error "legacy-access-list"
  else if tx.kind != 2 && tx.priorityFeeCap != 0 then .error "legacy-priority-cap"
  else if tx.priorityFeeCap > tx.gasPriceCap then .error "priority-exceeds-fee-cap"
  else if tx.accessList.any (fun entry => entry.address ≥ addressBound || entry.storageKeys.any (· ≥ modulus)) then
    .error "invalid-access-list"
  else if tx.gasLimit > block.gasLimit - block.gasUsedBefore then .error "block-gas-exhausted"
  else if tx.gasLimit < intrinsic then .error "below-intrinsic-gas"
  else if price < block.baseFee then .error "price-below-base-fee"
  else if sender.balance < tx.gasLimit * tx.gasPriceCap + tx.value then .error "insufficient-upfront-balance"
  else .ok ⟨intrinsic, tx.gasLimit, price, block.baseFee⟩

/-- The same input inventory supplies each lookup's coverage check and
    authenticated value. Zeros in the functional map alone prove nothing. -/
def witnessWorld (p : Request) : TxWorld :=
  let find := fun address => p.witnesses.find? (fun item => item.address == address)
  let accounts := fun address => ((find address).map WitnessAccount.account).getD {}
  { beginTransaction accounts with
    witnessed := some {
      account := fun address => (find address).isSome
      slot := fun address key => (find address).any (fun item => item.storage.any (fun slot => slot.key == key)) }
    warmAddresses := fun address => address == p.tx.sender || address == p.tx.to ||
      address == p.block.coinbase || decide (1 ≤ address ∧ address ≤ p.fork.precompileLimit) ||
      p.tx.accessList.any (fun entry => entry.address == address)
    warmSlots := fun address key => p.tx.accessList.any (fun entry =>
      entry.address == address && entry.storageKeys.contains key)
    chainId := p.block.chainId
    blockCoinbase := p.block.coinbase
    blockNumber := p.block.number
    blockTimestamp := p.block.timestamp
    blockPrevRandao := p.block.prevRandao
    blockGasLimit := p.block.gasLimit
    blockBaseFee := p.block.baseFee
    blockBlobBaseFee := p.block.blobBaseFee
    keccakAcceptance := p.keccakAcceptance }

/-- Escrow is outside the execution checkpoint. Storage and the initial log
    journal retain the pre-transaction projection. -/
def debitSender (w : TxWorld) (sender : Nat) (budget : Budget) : TxWorld :=
  let original := w.accounts sender
  { putAccount w sender { original with
      balance := original.balance - budget.escrow, nonce := original.nonce + 1 } with
    effectiveGasPrice := budget.price }

structure Charge where
  beforeRefund : Nat
  refund : Nat
  used : Nat
  returnedWei : Nat
  tip : Nat
  burned : Nat

/-- Shanghai and Cancun cap the SSTORE refund at one fifth of gas consumed,
    including intrinsic gas. Their receipt gas has no Prague calldata floor. -/
def charge (budget : Budget) (frameGasRemaining : Nat) (refundCounter : Int) : Charge :=
  let gross := budget.gasLimit - frameGasRemaining
  let refund := min refundCounter.toNat (gross / 5)
  let used := gross - refund
  { beforeRefund := gross, refund, used
    returnedWei := (budget.gasLimit - used) * budget.price
    tip := used * (budget.price - budget.baseFee)
    burned := used * budget.baseFee }

structure Result where
  world : TxWorld
  frame : FrameStatus
  receiptStatus : Bool
  output : ByteView
  charge : Charge
  cumulativeGasUsed : Nat
  effectiveGasPrice : Nat
  logs : List LogEntry

inductive Outcome where
  | rejected (reason : String)
  | indeterminate (reason : Unavailable)
  | executed (result : Result)

def credit (w : TxWorld) (address amount : Nat) : Except Unavailable TxWorld :=
  let account := w.accounts address
  let balance := account.balance + amount
  if balance ≥ modulus then .error (.unsupported "balance-overflow")
  else .ok (putAccount w address { account with balance })

/-- Fees are applied to the world selected by the execution checkpoint.
    Sequential updates preserve aliases among sender, to and beneficiary. -/
def finish (tx : Envelope) (block : BlockContext) (budget : Budget)
    (w : TxWorld) (frame : FrameStatus) (s : State) (success : Bool) : Outcome :=
  if s.gas > budget.frameGas then .indeterminate (.unsupported "unbounded-frame-gas")
  else
    let bill := charge budget s.gas w.refund
    match credit w tx.sender bill.returnedWei with
    | .error reason => .indeterminate reason
    | .ok refundWorld =>
      match credit refundWorld block.coinbase bill.tip with
      | .error reason => .indeterminate reason
      | .ok world =>
        .executed {
          world, frame, receiptStatus := success, output := s.outputData,
          charge := bill, cumulativeGasUsed := block.gasUsedBefore + bill.used,
          effectiveGasPrice := budget.price, logs := w.logsRev.reverse }

/-- Use the same failure boundary as the ordinary world-aware dispatcher,
    with the fee-paid and nonce-incremented state as its checkpoint. -/
def settleFrame (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (initial : State) (raw : CallOpcode.RawOutcome) : Outcome :=
  match CallOpcode.settle escrow initial raw with
  | .stopped w s => finish tx block budget w .stopped s true
  | .returned w s => finish tx block budget w .returned s true
  | .reverted w s => finish tx block budget w .reverted s false
  | .exceptional w s e => finish tx block budget w (.exceptional e) s false
  | .indeterminate e => .indeterminate (.frame e)

/-- The actual transaction-frame dispatcher. Identity uses the same bounded
    native Lean byte-view executor as nested CALLs and ignores account code.
    A precompile executes no EVM instruction and therefore needs no instruction
    fuel; all ordinary bytecode frames retain `CallOpcode.execute`'s fuel bound.
    Both paths return through `settleFrame`, preserving the fee escrow and the
    transaction value-transfer checkpoint on exceptional failure. -/
def runFrame (fuel : Nat) (entered : TxWorld) (address : Nat) (frame : State) :
    CallOpcode.RawOutcome :=
  if address == 4 then
    match IdentityPrecompile.executeView CallOpcode.maxIdentityCallBytes frame.gas frame.callData with
    | .ok (bytes, remaining) =>
      .returned entered { frame with gas := remaining, outputData := bytes, halted := true }
    | .error .outOfGas => .exceptional .outOfGas
    | .error reason => .indeterminate reason
  else CallOpcode.execute fuel entered address frame

/-- Kind: executable correspondence.
    Says: an admitted, sufficiently funded direct identity frame returns exactly
    its calldata view and the exact unspent gas through the transaction path.
    Does not say: that the supplied envelope or state witness is authenticated. -/
theorem runFrame_identity_exact (fuel : Nat) (entered : TxWorld) (frame : State)
    (hSize : frame.callData.size ≤ CallOpcode.maxIdentityCallBytes)
    (hGas : IdentityPrecompile.gasCost frame.callData.size ≤ frame.gas) :
    runFrame fuel entered 4 frame = .returned entered
      { frame with
        gas := frame.gas - IdentityPrecompile.gasCost frame.callData.size
        outputData := frame.callData
        halted := true } := by
  simp [runFrame, IdentityPrecompile.executeView_exact _ _ _ hSize hGas]

/-- Kind: exceptional boundary.
    Says: underfunded direct identity execution is an EVM out-of-gas result.
    Does not say: that oversized inputs are consensus-invalid; they refuse first. -/
theorem runFrame_identity_outOfGas (fuel : Nat) (entered : TxWorld) (frame : State)
    (hSize : frame.callData.size ≤ CallOpcode.maxIdentityCallBytes)
    (hGas : frame.gas < IdentityPrecompile.gasCost frame.callData.size) :
    runFrame fuel entered 4 frame = .exceptional .outOfGas := by
  simp [runFrame, IdentityPrecompile.executeView, Nat.not_lt_of_ge hSize, hGas]

/-- Kind: resource boundary.
    Says: over-limit direct identity input propagates indeterminate resource
    refusal before gas classification, never a completed failed receipt.
    Does not say: that the local input cap is an Ethereum protocol rule. -/
theorem runFrame_identity_resourceLimit (fuel : Nat) (entered : TxWorld) (frame : State)
    (hSize : CallOpcode.maxIdentityCallBytes < frame.callData.size) :
    runFrame fuel entered 4 frame = .indeterminate .resourceLimit := by
  simp [runFrame, IdentityPrecompile.executeView, hSize]

/-- Kind: effect boundary.
    Says: the real settlement path restores the fee-paid escrow world on
    identity out-of-gas, then applies the existing failure fee accounting.
    Does not say: that signatures, trie witnesses or fee inputs are authentic. -/
theorem settleFrame_identity_outOfGas (tx : Envelope) (block : BlockContext) (budget : Budget)
    (fuel : Nat) (escrow entered : TxWorld) (frame : State)
    (hSize : frame.callData.size ≤ CallOpcode.maxIdentityCallBytes)
    (hGas : frame.gas < IdentityPrecompile.gasCost frame.callData.size) :
    settleFrame tx block budget escrow frame (runFrame fuel entered 4 frame) =
      finish tx block budget escrow (.exceptional .outOfGas)
        { frame with gas := 0, halted := true } false := by
  rw [runFrame_identity_outOfGas fuel entered frame hSize hGas]
  rfl

/-- Kind: executable correspondence.
    Says: direct identity frames are independent of the bytecode step budget.
    Does not say: that native precompile resource bounds are unnecessary. -/
theorem runFrame_identity_fuel (fuel otherFuel : Nat) (entered : TxWorld) (frame : State) :
    runFrame fuel entered 4 frame = runFrame otherFuel entered 4 frame := rfl

/-- Kind: executable correspondence.
    Says: an ordinary transaction still uses the existing bytecode dispatcher
    and its complete fuel and journal semantics without a second implementation.
    Does not say: that all Ethereum instructions or forks are implemented. -/
theorem runFrame_ordinary (fuel : Nat) (entered : TxWorld) (address : Nat) (frame : State)
    (hAddress : address ≠ 4) :
    runFrame fuel entered address frame = CallOpcode.execute fuel entered address frame := by
  simp [runFrame, hAddress]

private def runAdmitted (p : Request) (w : TxWorld) (budget : Budget) : Outcome :=
  let escrow := debitSender w p.tx.sender budget
  match pay escrow p.tx.sender p.tx.to p.tx.value with
  | .error _ => .indeterminate (.unsupported "value-transfer-unavailable")
  | .ok entered =>
    let frame := { frameInput entered p.tx.to budget.frameGas false p.fork.profile p.tx.sender p.tx.sender with
      callData := ByteView.ofArray p.tx.data, callValue := p.tx.value }
    settleFrame p.tx p.block budget escrow frame (runFrame p.fuel entered p.tx.to frame)

/-- Execute a decoded, externally authenticated contract transaction in the
    admitted Shanghai or Cancun slice, or return an explicit refusal. -/
def run (p : Request) : Outcome :=
  if p.tx.kind > 2 then .indeterminate (.unsupported "unsupported-transaction-type")
  else if !p.block.bounded p.fork then .indeterminate (.unsupported "unusable-block-context")
  else if p.exceedsResources then
    .indeterminate (.frame .resourceLimit)
  else if !(decide ((p.witnesses.map (·.address)).Nodup) && p.witnesses.all WitnessAccount.valid) then
    .indeterminate .invalidWitness
  else
    let w := witnessWorld p
    match [p.tx.sender, p.tx.to, p.block.coinbase].find? (fun address => !w.hasAccount address) with
    | some address => .indeterminate (.frame (.incompleteState address none))
    | none =>
      if CallOpcode.unimplementedPrecompile p.fork.profile p.tx.to then .indeterminate (.frame .unsupportedFork)
      else
        match admit p.tx p.block (w.accounts p.tx.sender) with
        | .error reason => .rejected reason
        | .ok budget => runAdmitted p w budget

#print axioms runFrame_identity_exact
#print axioms runFrame_identity_outOfGas
#print axioms runFrame_identity_resourceLimit
#print axioms settleFrame_identity_outOfGas
#print axioms runFrame_identity_fuel
#print axioms runFrame_ordinary

end EVMCleanroom.CallTransaction
