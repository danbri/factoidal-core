import EVMCleanroom.CallTransactionProofs
import EVMCleanroom.BlobCall

/-!
# Contract-creation transactions (destination absent)

Statements about the executable admission, entry and settlement of a creation
transaction in `CallTransaction` (`admit`, `runWithBlobHashes`, `runAdmitted`,
`runCreation`). Normative reference: ethereum/execution-specs `forks/cancun`
and `forks/prague`: `transactions.py` (`validate_transaction`,
`calculate_intrinsic_cost`), `utils/message.py` (`prepare_message`),
`vm/interpreter.py` (`process_message_call`, `process_create_message`) and
`fork.py` (`check_transaction`, `process_transaction`).

Nothing here authenticates an envelope or a witness, and the address
derivation uses the repository's experimental Keccak, which is not proved
equal to Keccak-256. Agreement with EELS is tested, not proved.
-/

namespace EVMCleanroom.CreateTransaction

open World CallTransaction

/-- Kind: executable correspondence (gas schedule).
    Says: the intrinsic gas of a creation envelope is that of the same
    envelope read as a call, plus 32000, plus 2 gas per 32-byte word of
    initcode (EIP-3860).
    Does not say: that the envelope is admitted. -/
theorem intrinsic_creation (tx : Envelope) (block : BlockContext) (sender : Account)
    (h : tx.create = true) :
    TxAccounting.intrinsicGas (accountingInput tx block sender) =
      TxAccounting.intrinsicGas (accountingInput { tx with create := false } block sender) +
        32000 + Create.initCodeCost tx.data.size := by
  simp [TxAccounting.intrinsicGas, TxAccounting.creationGas, accountingInput, h,
    Create.initCodeCost, Create.dataWords]
  omega

/-- Kind: executable correspondence (gas schedule).
    Says: a call envelope pays no creation surcharge: 21000, 4 per zero byte,
    16 per nonzero byte, 2400 per access-list address and 1900 per key.
    Does not say: anything about the Prague calldata floor. -/
theorem intrinsic_call (tx : Envelope) (block : BlockContext) (sender : Account)
    (h : tx.create = false) :
    TxAccounting.intrinsicGas (accountingInput tx block sender) =
      21000 + 4 * (accountingInput tx block sender).zeros +
        16 * (accountingInput tx block sender).nonzeros +
        2400 * tx.accessList.length +
        1900 * tx.accessList.foldl (fun n e => n + e.storageKeys.length) 0 := by
  simp [TxAccounting.intrinsicGas, TxAccounting.creationGas, accountingInput, h]

/-- Kind: admission.
    Says: an admitted creation is of type 0, 1 or 2, its initcode is at most
    49152 bytes, and its budget's intrinsic gas is the creation intrinsic gas,
    which the gas limit covers.
    Does not say: that the initcode then succeeds. -/
theorem admit_creation (tx : Envelope) (block : BlockContext) (account : Account) (budget : Budget)
    (h : admit tx block account = .ok budget) (hCreate : tx.create = true) :
    tx.kind ≤ 2 ∧ tx.data.size ≤ Create.maxInitCodeSize ∧
    budget.intrinsic =
      TxAccounting.intrinsicGas (accountingInput { tx with create := false } block account) +
        32000 + Create.initCodeCost tx.data.size ∧
    budget.intrinsic ≤ tx.gasLimit := by
  obtain ⟨_, _, hIntrinsic, hLimit, _⟩ := admit_checked tx block account budget h
  unfold admit at h
  dsimp only at h
  by_cases hKind : tx.kind > 2
  · simp [hKind] at h
  simp only [hKind, if_false] at h
  by_cases hRange : (decide (tx.sender ≥ addressBound) || decide (tx.to ≥ addressBound) ||
      decide (tx.value ≥ modulus) || decide (tx.gasPriceCap ≥ modulus) || decide (tx.priorityFeeCap ≥ modulus)) = true
  · simp [hRange] at h
  simp only [hRange] at h
  by_cases hInit : (tx.create && decide (tx.data.size > Create.maxInitCodeSize)) = true
  · simp [hInit] at h
  refine ⟨Nat.le_of_not_gt hKind, ?_, ?_, hLimit⟩
  · simp only [hCreate, Bool.true_and, decide_eq_true_eq] at hInit
    exact Nat.le_of_not_gt hInit
  · rw [hIntrinsic, intrinsic_creation tx block account hCreate]

/-- Kind: admission refusal (EIP-3860).
    Says: a creation of type 0, 1 or 2 with in-range fields and more than
    49152 bytes of initcode is rejected as an invalid transaction, whatever
    its gas, nonce and funds.
    Does not say: which of several defects a doubly invalid envelope reports. -/
theorem admit_initcode_too_large (tx : Envelope) (block : BlockContext) (account : Account)
    (hKind : tx.kind ≤ 2)
    (hRange : tx.sender < addressBound ∧ tx.to < addressBound ∧ tx.value < modulus ∧
      tx.gasPriceCap < modulus ∧ tx.priorityFeeCap < modulus)
    (hCreate : tx.create = true) (hSize : Create.maxInitCodeSize < tx.data.size) :
    admit tx block account = .error "initcode-too-large" := by
  obtain ⟨hSender, hTo, hValue, hCap, hPriority⟩ := hRange
  simp [admit, Nat.not_lt.mpr hKind, Nat.not_le.mpr hSender, Nat.not_le.mpr hTo, Nat.not_le.mpr hValue,
    Nat.not_le.mpr hCap, Nat.not_le.mpr hPriority, hCreate, hSize]

/-- Kind: executable inversion.
    Says: a receipt from the shared ordinary/blob entry exists only if the
    creation check passed, the envelope's target is covered by the witness,
    admission succeeded on the sender's witnessed account, and the receipt is
    the admitted run's.
    Does not say: that the witness or envelope is authentic. -/
theorem runWithBlobHashes_executed (p : Request) (hashes : Array Word) (result : Result)
    (h : runWithBlobHashes p hashes = .executed result) :
    p.creationRefusal = none ∧ (witnessWorld p).hasAccount p.tx.to = true ∧
    ∃ budget, admit p.tx p.block ((witnessWorld p).accounts p.tx.sender) = .ok budget ∧
      runAdmitted p { witnessWorld p with txBlobHashes := hashes } budget = .executed result := by
  unfold runWithBlobHashes at h
  dsimp only at h
  by_cases hKind : p.tx.kind > 2
  · simp [hKind] at h
  simp only [hKind, if_false] at h
  by_cases hBlock : (!p.block.bounded p.fork) = true
  · rw [if_pos hBlock] at h
    cases h
  simp only [hBlock] at h
  by_cases hLimit : p.exceedsResources = true
  · rw [if_pos hLimit] at h
    cases h
  simp only [hLimit] at h
  by_cases hCoverage : (!(decide ((p.witnesses.map (·.address)).Nodup) &&
      p.witnesses.all WitnessAccount.valid)) = true
  · rw [if_pos hCoverage] at h
    cases h
  simp only [hCoverage] at h
  cases hCreation : p.creationRefusal with
  | some reason => simp only [hCreation] at h; cases h
  | none =>
    simp only [hCreation] at h
    cases hMissing : [p.tx.sender, p.tx.to, p.block.coinbase].find?
        (fun address => !({ witnessWorld p with txBlobHashes := hashes } : TxWorld).hasAccount address) with
    | some address => simp only [hMissing] at h; cases h
    | none =>
      simp only [hMissing] at h
      by_cases hPrecompile : CallOpcode.unimplementedPrecompile p.fork.profile p.tx.to = true
      · rw [if_pos hPrecompile] at h
        cases h
      simp only [hPrecompile] at h
      cases hAdmit : admit p.tx p.block (({ witnessWorld p with txBlobHashes := hashes } : TxWorld).accounts p.tx.sender) with
      | error reason => simp only [hAdmit] at h; cases h
      | ok budget =>
        simp only [hAdmit] at h
        have hNot : ¬ (!(witnessWorld p).hasAccount p.tx.to) = true :=
          List.find?_eq_none.mp hMissing p.tx.to (by simp)
        exact ⟨rfl, by simpa using hNot, budget, rfl, h⟩

/-- Kind: executable correspondence (address formula of the actual entry).
    Says: every receipt of a creation transaction was produced with the
    Keccak opt-in, and the address the run created at (the envelope's target,
    which the witness must cover) is the low 160 bits of the experimental
    hash of `rlp([sender, nonce])`, where the nonce is the one the sender's
    witnessed account holds before this transaction increments it.
    Does not say: that the experimental hash is Keccak-256 (tested only), or
    that the witness is authentic. -/
theorem run_creation_address (p : Request) (hashes : Array Word) (result : Result)
    (h : runWithBlobHashes p hashes = .executed result) (hCreate : p.tx.create = true) :
    ∃ acceptance, p.keccakAcceptance = some acceptance ∧
      p.tx.to = Create.createAddress acceptance p.tx.sender ((witnessWorld p).accounts p.tx.sender).nonce ∧
      (witnessWorld p).hasAccount p.tx.to = true := by
  obtain ⟨hRefusal, hCovered, budget, hAdmit, _⟩ := runWithBlobHashes_executed p hashes result h
  obtain ⟨hNonce, hBound, _⟩ := admit_checked _ _ _ _ hAdmit
  have hSmall : ¬ p.tx.nonce ≥ nonceBound := by omega
  unfold Request.creationRefusal at hRefusal
  simp only [hCreate, Bool.not_true, Bool.false_or, decide_eq_true_eq, hSmall, if_false] at hRefusal
  cases hAcceptance : p.keccakAcceptance with
  | none => simp [hAcceptance] at hRefusal
  | some acceptance =>
    simp only [hAcceptance] at hRefusal
    by_cases hTarget : (p.tx.to == creationAddress acceptance p.tx) = true
    · refine ⟨acceptance, rfl, ?_, hCovered⟩
      rw [← hNonce]
      simpa [creationAddress] using hTarget
    · simp [hTarget] at hRefusal

/-- Kind: executable refusal.
    Says: a creation envelope run without the Keccak opt-in, with a nonce
    that admission could accept, is refused as indeterminate before any
    witness or admission check; no receipt and no rejection is produced.
    Does not say: that the transaction is invalid. -/
theorem creationRefusal_no_keccak (p : Request) (hCreate : p.tx.create = true)
    (hNonce : p.tx.nonce < nonceBound) (hNone : p.keccakAcceptance = none) :
    p.creationRefusal = some (.frame .unsupportedFork) := by
  simp [Request.creationRefusal, hCreate, Nat.not_le.mpr hNonce, hNone]

/-- Kind: executable refusal.
    Says: a call envelope is never refused by the creation check.
    Does not say: that it is admitted. -/
theorem creationRefusal_call (p : Request) (hCall : p.tx.create = false) :
    p.creationRefusal = none := by
  simp [Request.creationRefusal, hCall]

private theorem credit_code (w result : TxWorld) (address amount : Nat)
    (h : credit w address amount = .ok result) (other : Nat) :
    (result.accounts other).code = (w.accounts other).code := by
  unfold credit at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    by_cases hOther : other = address <;> simp [putAccount, hOther]

/-- Kind: settlement projection.
    Says: an executed fee settlement reports the frame status it was given
    and the charge computed from the frame's remaining gas and the selected
    world's refund counter, and changes no account's code.
    Does not say: which world or status an execution selects. -/
theorem finish_frame_charge (tx : Envelope) (block : BlockContext) (budget : Budget)
    (world : TxWorld) (frame : FrameStatus) (s : State) (success : Bool) (result : Result)
    (h : finish tx block budget world frame s success = .executed result) :
    result.frame = frame ∧ result.charge = charge budget s.gas world.refund ∧
    ∀ address, (result.world.accounts address).code = (world.accounts address).code := by
  unfold finish at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · next refundWorld hRefund =>
      split at h
      · cases h
      · next final hTip =>
        cases h
        exact ⟨rfl, rfl, fun address =>
          (credit_code _ _ _ _ hTip address).trans (credit_code _ _ _ _ hRefund address)⟩

/-- Kind: executable correspondence (collision, EIP-684 and EIP-7610).
    Says: when the target already has a nonce, code or storage, the creation
    settles as an exceptional halt on the escrow world with no gas left; no
    initcode runs and no value moves.
    Does not say: that the host's storage statement is authentic. -/
theorem runCreation_collision (p : Request) (escrow : TxWorld) (budget : Budget)
    (h : Create.collides (escrow.accounts p.tx.to) = true) :
    runCreation p escrow budget =
      finish p.tx p.block budget escrow (.exceptional .addressCollision)
        { creationFrame p escrow budget with gas := 0, halted := true } false := by
  simp [runCreation, h, settleFrame, CallOpcode.settle]

/-- Kind: outcome (collision).
    Says: the receipt of an admitted creation whose target collides has
    status zero, uses the whole gas limit, returns no wei, reports no created
    address, leaves every account's code and storage as before the
    transaction, and leaves the sender's nonce incremented by exactly one.
    Assumes the refund counter is zero at the start, as `witnessWorld` gives.
    Does not say: that the fee credits cannot overflow (then no receipt). -/
theorem runAdmitted_collision (p : Request) (w : TxWorld) (budget : Budget) (result : Result)
    (hCreate : p.tx.create = true) (hRefund : w.refund = 0)
    (hCollides : Create.collides ((debitSender w p.tx.sender budget).accounts p.tx.to) = true)
    (h : runAdmitted p w budget = .executed result) :
    result.receiptStatus = false ∧ result.frame = .exceptional .addressCollision ∧
    result.charge.used = budget.gasLimit ∧ result.charge.returnedWei = 0 ∧
    createdAddress p.tx result = none ∧
    (result.world.accounts p.tx.sender).nonce = (w.accounts p.tx.sender).nonce + 1 ∧
    (∀ address, (result.world.accounts address).code = (w.accounts address).code ∧
      (result.world.accounts address).storage = (w.accounts address).storage) := by
  unfold runAdmitted at h
  simp only [hCreate, if_true] at h
  rw [runCreation_collision p _ budget hCollides] at h
  obtain ⟨hStatus, _, _, hAccounts⟩ := finish_projection _ _ _ _ _ _ _ _ h
  obtain ⟨hFrame, hCharge, hCode⟩ := finish_frame_charge _ _ _ _ _ _ _ _ h
  have hBill : result.charge.used = budget.gasLimit ∧ result.charge.returnedWei = 0 := by
    rw [hCharge]
    have : (debitSender w p.tx.sender budget).refund = 0 := hRefund
    simp [charge, this]
  have hDebit : ∀ address,
      ((debitSender w p.tx.sender budget).accounts address).code = (w.accounts address).code ∧
      ((debitSender w p.tx.sender budget).accounts address).storage = (w.accounts address).storage := by
    intro address
    by_cases hSender : address = p.tx.sender <;> simp [debitSender, putAccount, hSender]
  refine ⟨hStatus, hFrame, hBill.1, hBill.2, by simp [createdAddress, hStatus], ?_, fun address => ?_⟩
  · rw [(hAccounts p.tx.sender).1]
    simp [debitSender, putAccount]
  · exact ⟨(hCode address).trans (hDebit address).1, (hAccounts address).2.trans (hDebit address).2⟩

/-- Kind: executable correspondence (successful creation).
    Says: when the target is free, the endowment is paid and the initcode
    returns output that passes the deposit rules, the creation settles
    through the ordinary success path (fee settlement, then transaction-end
    deletion) on the world in which the new account's code is exactly the
    returned bytes, with 200 gas per byte taken from the gas the initcode
    left; the rest is returned to the sender by the usual settlement.
    Does not say: that the account survives the transaction (initcode that
    self-destructs is deleted at the end), or that the fuel suffices. -/
theorem runCreation_success (p : Request) (escrow entered world : TxWorld) (budget : Budget)
    (s : State) (code : Array UInt8) (remaining : Nat)
    (hFree : Create.collides (escrow.accounts p.tx.to) = false)
    (hEnter : Create.enter escrow p.tx.sender p.tx.to p.tx.value = .ok entered)
    (hRun : CallOpcode.execute p.fuel entered p.tx.to (creationFrame p entered budget) = .returned world s)
    (hDeposit : Create.deposit s.gas s.outputData = some (code, remaining)) :
    runCreation p escrow budget =
      destroyAfter (finish p.tx p.block budget (Create.setCode world p.tx.to code) .returned
        { s with gas := remaining } true) ∧
    ((Create.setCode world p.tx.to code).accounts p.tx.to).code = code ∧
    code = Create.materialize s.outputData ∧ remaining = s.gas - 200 * s.outputData.size := by
  obtain ⟨_, _, _, hRemaining, hCode⟩ := Create.deposit_success _ _ _ _ hDeposit
  refine ⟨?_, (Create.setCode_effect world p.tx.to code).1, hCode, hRemaining⟩
  simp [runCreation, hFree, hEnter, hRun, CallOpcode.depositOutcome, hDeposit, settleFrame, CallOpcode.settle]

/-- Kind: executable correspondence (successful creation, no output).
    Says: initcode that stops without returning (including empty initcode)
    deposits empty code at no cost and settles through the success path
    with all the gas it left.
    Does not say: that the account survives the transaction. -/
theorem runCreation_stopped (p : Request) (escrow entered world : TxWorld) (budget : Budget) (s : State)
    (hFree : Create.collides (escrow.accounts p.tx.to) = false)
    (hEnter : Create.enter escrow p.tx.sender p.tx.to p.tx.value = .ok entered)
    (hRun : CallOpcode.execute p.fuel entered p.tx.to (creationFrame p entered budget) = .stopped world s) :
    runCreation p escrow budget =
      destroyAfter (finish p.tx p.block budget
        (Create.setCode world p.tx.to (Create.materialize {})) .stopped s true) := by
  have hDeposit : Create.deposit s.gas {} = some (Create.materialize {}, s.gas) :=
    Create.deposit_empty s.gas {} rfl
  simp [runCreation, hFree, hEnter, hRun, CallOpcode.depositOutcome, hDeposit, settleFrame, CallOpcode.settle]

/-- Kind: executable correspondence (failed initcode: REVERT).
    Says: reverting initcode settles with status zero on the escrow world,
    keeping the gas the initcode left.
    Does not say: what the revert data means. -/
theorem runCreation_reverted (p : Request) (escrow entered : TxWorld) (budget : Budget) (s : State)
    (hFree : Create.collides (escrow.accounts p.tx.to) = false)
    (hEnter : Create.enter escrow p.tx.sender p.tx.to p.tx.value = .ok entered)
    (hRun : CallOpcode.execute p.fuel entered p.tx.to (creationFrame p entered budget) = .reverted s) :
    ∃ terminal, terminal.gas = s.gas ∧ terminal.outputData = s.outputData ∧
      runCreation p escrow budget = finish p.tx p.block budget escrow .reverted terminal false := by
  refine ⟨_, ?_, ?_, by simp only [runCreation, hFree, hEnter, hRun, CallOpcode.depositOutcome, settleFrame,
    CallOpcode.settle, Bool.false_eq_true, if_false]; rfl⟩ <;> rfl

/-- Kind: executable correspondence (failed initcode: exceptional halt).
    Says: initcode that halts exceptionally settles with status zero on the
    escrow world with no gas left.
    Does not say: that an indeterminate frame produces a receipt (it does not). -/
theorem runCreation_exceptional (p : Request) (escrow entered : TxWorld) (budget : Budget) (e : Error)
    (hFree : Create.collides (escrow.accounts p.tx.to) = false)
    (hEnter : Create.enter escrow p.tx.sender p.tx.to p.tx.value = .ok entered)
    (hRun : CallOpcode.execute p.fuel entered p.tx.to (creationFrame p entered budget) = .exceptional e) :
    runCreation p escrow budget =
      finish p.tx p.block budget escrow (.exceptional e)
        { creationFrame p entered budget with gas := 0, halted := true } false := by
  simp [runCreation, hFree, hEnter, hRun, CallOpcode.depositOutcome, settleFrame, CallOpcode.settle]

/-- Kind: executable correspondence (failed code deposit).
    Says: output that fails a deposit rule (more than 24576 bytes, a 0xEF
    first byte, or fewer than 200 gas per byte left) settles as an
    exceptional halt on the escrow world with no gas left; no code is stored.
    Does not say: which rule failed beyond the reported diagnostic. -/
theorem runCreation_deposit_failure (p : Request) (escrow entered world : TxWorld) (budget : Budget)
    (s : State)
    (hFree : Create.collides (escrow.accounts p.tx.to) = false)
    (hEnter : Create.enter escrow p.tx.sender p.tx.to p.tx.value = .ok entered)
    (hRun : CallOpcode.execute p.fuel entered p.tx.to (creationFrame p entered budget) = .returned world s)
    (hDeposit : Create.deposit s.gas s.outputData = none) :
    runCreation p escrow budget =
      finish p.tx p.block budget escrow (.exceptional (CallOpcode.depositError s.outputData))
        { creationFrame p entered budget with gas := 0, halted := true } false := by
  simp [runCreation, hFree, hEnter, hRun, CallOpcode.depositOutcome, hDeposit, settleFrame, CallOpcode.settle]

/-- Kind: rollback (every failed creation).
    Says: a status-zero settlement on the escrow world, which is what a
    collision, REVERT, exceptional halt and failed deposit all produce, leaves
    each account's nonce, code and storage as in the escrow world (where the
    sender has paid and its nonce is incremented), changes balances only by
    the sender's gas refund and the beneficiary's tip, and reports no created
    address: the value endowment, the new account's nonce and anything the
    initcode did are gone.
    Does not say: how much gas the failure consumed. -/
theorem failed_creation_escrow (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (frame : FrameStatus) (s : State) (result : Result)
    (h : finish tx block budget escrow frame s false = .executed result) :
    result.receiptStatus = false ∧ createdAddress tx result = none ∧
    ∀ address,
      (result.world.accounts address).nonce = (escrow.accounts address).nonce ∧
      (result.world.accounts address).code = (escrow.accounts address).code ∧
      (result.world.accounts address).storage = (escrow.accounts address).storage ∧
      (result.world.accounts address).balance = (escrow.accounts address).balance +
        (if address = tx.sender then result.charge.returnedWei else 0) +
        (if address = block.coinbase then result.charge.tip else 0) := by
  obtain ⟨hStatus, _, _, hAccounts⟩ := finish_projection _ _ _ _ _ _ _ _ h
  obtain ⟨_, _, hCode⟩ := finish_frame_charge _ _ _ _ _ _ _ _ h
  exact ⟨hStatus, by simp [createdAddress, hStatus], fun address =>
    ⟨(hAccounts address).1, hCode address, (hAccounts address).2, finish_balance _ _ _ _ _ _ _ _ address h⟩⟩

/-- Kind: result projection.
    Says: a created address is reported exactly for a creation envelope with
    receipt status one, and it is the envelope's (checked) target.
    Does not say: that the account still exists after transaction-end deletion. -/
theorem createdAddress_iff (tx : Envelope) (result : Result) (new : Nat) :
    createdAddress tx result = some new ↔
      tx.create = true ∧ result.receiptStatus = true ∧ new = tx.to := by
  unfold createdAddress
  by_cases hCreate : tx.create = true <;> by_cases hStatus : result.receiptStatus = true <;>
    simp [hCreate, hStatus, eq_comm]

/-- Kind: admission refusal (EIP-4844).
    Says: a type-3 creation envelope is rejected as invalid by the blob
    preparation, before any resource, witness or fee check.
    Does not say: anything about type 4, which no entry here executes
    (`runWithBlobHashes` refuses every type above 2 as indeterminate). -/
theorem blob_creation_rejected (p : BlobCall.Input) (fees : Nat × Nat)
    (hKind : p.request.tx.kind = 3) (hCreate : p.request.tx.create = true) :
    BlobCall.prepareWithFees p fees = .error (.rejected "blob-creation") := by
  simp [BlobCall.prepareWithFees, hKind, hCreate]

/-- Kind: executable refusal.
    Says: the ordinary entry gives no receipt and no rejection for a type
    above 2, creation or not.
    Does not say: that such a transaction is invalid. -/
theorem run_type_above_two (p : Request) (hashes : Array Word) (hKind : p.tx.kind > 2) :
    runWithBlobHashes p hashes = .indeterminate (.unsupported "unsupported-transaction-type") := by
  simp [runWithBlobHashes, hKind]

#print axioms intrinsic_creation
#print axioms intrinsic_call
#print axioms admit_creation
#print axioms admit_initcode_too_large
#print axioms runWithBlobHashes_executed
#print axioms run_creation_address
#print axioms creationRefusal_no_keccak
#print axioms creationRefusal_call
#print axioms finish_frame_charge
#print axioms runCreation_collision
#print axioms runAdmitted_collision
#print axioms runCreation_success
#print axioms runCreation_stopped
#print axioms runCreation_reverted
#print axioms runCreation_exceptional
#print axioms runCreation_deposit_failure
#print axioms failed_creation_escrow
#print axioms createdAddress_iff
#print axioms blob_creation_rejected
#print axioms run_type_above_two

end EVMCleanroom.CreateTransaction
