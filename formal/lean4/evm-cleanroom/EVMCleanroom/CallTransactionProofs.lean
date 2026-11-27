import EVMCleanroom.CallTransaction

namespace EVMCleanroom.CallTransaction

open World

/-- Kind: admission.
    Says: actual admission enforces the sender nonce, block gas allowance,
    intrinsic gas, base fee, and upfront maximum fees plus value.
    Does not say: how the host recovers the sender or authenticates the header. -/
theorem admit_checked (tx : Envelope) (block : BlockContext) (account : Account) (budget : Budget)
    (h : admit tx block account = .ok budget) :
    tx.nonce = account.nonce ∧ tx.nonce < nonceBound - 1 ∧
    budget.intrinsic = TxAccounting.intrinsicGas (accountingInput tx block account) ∧
    budget.intrinsic ≤ tx.gasLimit ∧ tx.gasLimit ≤ block.gasLimit - block.gasUsedBefore ∧
    budget.price = TxAccounting.effectivePrice (accountingInput tx block account) ∧
    block.baseFee ≤ budget.price ∧ tx.gasLimit * tx.gasPriceCap + tx.value ≤ account.balance := by
  unfold admit at h
  dsimp only at h
  by_cases hKind : tx.kind > 2
  · simp [hKind] at h
  simp only [hKind, if_false] at h
  by_cases hRange : (decide (tx.sender ≥ addressBound) || decide (tx.to ≥ addressBound) ||
      decide (tx.value ≥ modulus) || decide (tx.gasPriceCap ≥ modulus) || decide (tx.priorityFeeCap ≥ modulus)) = true
  · simp [hRange] at h
  simp only [hRange] at h
  by_cases hNoChain : (tx.signedChainId.isNone && tx.kind != 0) = true
  · simp [hNoChain] at h
  simp only [hNoChain] at h
  by_cases hChain : tx.signedChainId.any (fun id => id != block.chainId) = true
  · simp [hChain] at h
  simp only [hChain] at h
  by_cases hNonce : (tx.nonce != account.nonce || decide (tx.nonce ≥ nonceBound - 1)) = true
  · rw [if_pos hNonce] at h
    cases h
  simp only [hNonce] at h
  by_cases hCode : (!account.code.isEmpty) = true
  · simp [hCode] at h
  simp only [hCode] at h
  by_cases hLegacy : (tx.kind == 0 && !tx.accessList.isEmpty) = true
  · simp [hLegacy] at h
  simp only [hLegacy] at h
  by_cases hPriorityType : (tx.kind != 2 && tx.priorityFeeCap != 0) = true
  · simp [hPriorityType] at h
  simp only [hPriorityType] at h
  by_cases hPriority : tx.priorityFeeCap > tx.gasPriceCap
  · simp [hPriority] at h
  simp only [hPriority, if_false] at h
  by_cases hAccess : tx.accessList.any (fun entry =>
      decide (entry.address ≥ addressBound) || entry.storageKeys.any (fun key => decide (key ≥ modulus))) = true
  · simp [hAccess] at h
  simp only [hAccess] at h
  by_cases hBlock : tx.gasLimit > block.gasLimit - block.gasUsedBefore
  · simp [hBlock] at h
  simp only [hBlock, if_false] at h
  by_cases hIntrinsic : tx.gasLimit < TxAccounting.intrinsicGas (accountingInput tx block account)
  · simp [hIntrinsic] at h
  simp only [hIntrinsic, if_false] at h
  by_cases hPrice : TxAccounting.effectivePrice (accountingInput tx block account) < block.baseFee
  · simp [hPrice] at h
  simp only [hPrice, if_false] at h
  by_cases hFunds : account.balance < tx.gasLimit * tx.gasPriceCap + tx.value
  · simp [hFunds] at h
  simp only [hFunds, if_false] at h
  cases h
  simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, not_or] at hNonce
  exact ⟨Classical.byContradiction hNonce.1, Nat.lt_of_not_ge hNonce.2, rfl,
    Nat.le_of_not_gt hIntrinsic, Nat.le_of_not_gt hBlock, rfl,
    Nat.le_of_not_gt hPrice, Nat.le_of_not_gt hFunds⟩

/-- Kind: admission.
    Says: the public execution entry point can produce a receipt only
    after admitting the transaction using the supplied sender account,
    with the checked nonce, intrinsic gas, fee floor and upfront balance.
    Does not say: that the caller has authenticated the input witness. -/
theorem run_executed_admitted (p : Request) (result : Result) (h : run p = .executed result) :
    let account := (witnessWorld p).accounts p.tx.sender
    p.exceedsResources = false ∧
    ∃ budget, admit p.tx p.block account = .ok budget ∧
      p.tx.nonce = account.nonce ∧ budget.intrinsic ≤ p.tx.gasLimit ∧
      p.block.baseFee ≤ budget.price ∧
      p.tx.gasLimit * p.tx.gasPriceCap + p.tx.value ≤ account.balance := by
  unfold run runWithBlobHashes at h
  dsimp only at h
  have hEmptyContext : { witnessWorld p with txBlobHashes := #[] } = witnessWorld p := rfl
  simp only [hEmptyContext] at h
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
  cases hMissing : [p.tx.sender, p.tx.to, p.block.coinbase].find?
      (fun address => !(witnessWorld p).hasAccount address) with
  | some address => simp only [hMissing] at h; cases h
  | none =>
    simp only [hMissing] at h
    by_cases hPrecompile : CallOpcode.unimplementedPrecompile p.fork.profile p.tx.to = true
    · rw [if_pos hPrecompile] at h
      cases h
    simp only [hPrecompile] at h
    cases hAdmit : admit p.tx p.block ((witnessWorld p).accounts p.tx.sender) with
    | error reason => simp only [hAdmit] at h; cases h
    | ok budget =>
      obtain ⟨hNonce, _, _, hIntrinsic, _, _, hPrice, hFunds⟩ :=
        admit_checked p.tx p.block ((witnessWorld p).accounts p.tx.sender) budget hAdmit
      have hWithin : p.exceedsResources = false := by
        cases hSize : p.exceedsResources <;> simp_all
      exact ⟨hWithin, budget, hAdmit, hNonce, hIntrinsic, hPrice, hFunds⟩

/-- Kind: projection.
    Says: the actual escrow operation increments the sender nonce and
    subtracts the prepaid effective fee, keeping sender storage unchanged.
    Does not say: whether a caller supplied a valid underlying budget. -/
theorem debitSender_projection (w : TxWorld) (sender : Nat) (budget : Budget) :
    (debitSender w sender budget).accounts sender =
      { w.accounts sender with
        balance := (w.accounts sender).balance - budget.escrow,
        nonce := (w.accounts sender).nonce + 1 } := by
  simp [debitSender, putAccount]

/-- Kind: gas invariant.
    Says: the actual bill refunds at most both the nonnegative recorded
    refund and a fifth of gas consumed, and charges at most the gas limit.
    Does not say: the correctness of the refund delta from each opcode. -/
theorem charge_bounded (budget : Budget) (remaining : Nat) (counter : Int) :
    (charge budget remaining counter).refund ≤ counter.toNat ∧
    (charge budget remaining counter).refund ≤ (charge budget remaining counter).beforeRefund / 5 ∧
    (charge budget remaining counter).used ≤ budget.gasLimit := by
  unfold charge
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _, Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)⟩

/-- Kind: accounting.
    Says: the amount returned to the sender, the beneficiary tip, and the
    base fee burned account for every wei escrowed at the effective price.
    Does not say: which authenticated account is the beneficiary. -/
theorem charge_escrow_exact (budget : Budget) (remaining : Nat) (counter : Int)
    (hBase : budget.baseFee ≤ budget.price) :
    (charge budget remaining counter).returnedWei + (charge budget remaining counter).tip +
      (charge budget remaining counter).burned = budget.escrow := by
  let used := (charge budget remaining counter).used
  have hUsed : used ≤ budget.gasLimit := (charge_bounded budget remaining counter).2.2
  change (budget.gasLimit - used) * budget.price +
    used * (budget.price - budget.baseFee) + used * budget.baseFee = budget.gasLimit * budget.price
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hBase, ← Nat.add_mul,
    Nat.sub_add_cancel hUsed]

/-- Kind: frame boundary.
    Says: a missing frame result cannot settle fees or produce a receipt.
    Does not say: whether execution at another fuel limit gives a result. -/
theorem settleFrame_indeterminate (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (initial : State) (error : Error) :
    settleFrame tx block budget escrow initial (.indeterminate error) = .indeterminate (.frame error) := rfl

private theorem credit_projection (w result : TxWorld) (address amount : Nat)
    (h : credit w address amount = .ok result) :
    result.logsRev = w.logsRev ∧
    ∀ other, (result.accounts other).nonce = (w.accounts other).nonce ∧
      (result.accounts other).storage = (w.accounts other).storage := by
  unfold credit at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    refine ⟨rfl, fun other => ?_⟩
    by_cases hOther : other = address <;> simp [putAccount, hOther]

/-- Kind: preservation.
    Says: successful fee settlement reports the selected world's logs in
    execution order, preserving storage and every nonce including aliases.
    Does not say: whether a particular frame should select that world. -/
theorem finish_projection (tx : Envelope) (block : BlockContext) (budget : Budget)
    (world : TxWorld) (frame : FrameStatus) (s : State) (success : Bool) (result : Result)
    (h : finish tx block budget world frame s success = .executed result) :
    result.receiptStatus = success ∧ result.logs = world.logsRev.reverse ∧
    result.world.logsRev = world.logsRev ∧
    (∀ address, (result.world.accounts address).nonce = (world.accounts address).nonce ∧
      (result.world.accounts address).storage = (world.accounts address).storage) := by
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
        obtain ⟨hRefundLogs, hRefundAccounts⟩ := credit_projection _ _ _ _ hRefund
        obtain ⟨hTipLogs, hTipAccounts⟩ := credit_projection _ _ _ _ hTip
        exact ⟨rfl, rfl, hTipLogs.trans hRefundLogs, fun addr =>
          ⟨(hTipAccounts addr).1.trans (hRefundAccounts addr).1,
           (hTipAccounts addr).2.trans (hRefundAccounts addr).2⟩⟩

/-- Kind: rollback.
    Says: a reverting transaction uses the execution checkpoint's storage,
    log journal and sender nonce and records receipt status zero.
    Does not say: what its execution gas refund or beneficiary tip is. -/
theorem settleFrame_reverted_checkpoint (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (initial terminal : State) (result : Result)
    (h : settleFrame tx block budget escrow initial (.reverted terminal) = .executed result) :
    result.receiptStatus = false ∧ result.logs = escrow.logsRev.reverse ∧
    (result.world.accounts tx.sender).nonce = (escrow.accounts tx.sender).nonce ∧
    (∀ address, (result.world.accounts address).storage = (escrow.accounts address).storage) := by
  obtain ⟨hStatus, hLogs, _, hAccounts⟩ := finish_projection _ _ _ _ _ _ _ _ h
  exact ⟨hStatus, hLogs, (hAccounts tx.sender).1, fun address => (hAccounts address).2⟩

/-- Kind: rollback.
    Says: an exceptional transaction preserves checkpoint storage, logs
    and sender nonce while settling the exceptional receipt at status zero.
    Does not say: all unsupported opcodes are EVM exceptional halts. -/
theorem settleFrame_exception_checkpoint (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (initial : State) (error : Error) (result : Result)
    (h : settleFrame tx block budget escrow initial (.exceptional error) = .executed result) :
    result.receiptStatus = false ∧ result.logs = escrow.logsRev.reverse ∧
    (result.world.accounts tx.sender).nonce = (escrow.accounts tx.sender).nonce ∧
    (∀ address, (result.world.accounts address).storage = (escrow.accounts address).storage) := by
  obtain ⟨hStatus, hLogs, _, hAccounts⟩ := finish_projection _ _ _ _ _ _ _ _ h
  exact ⟨hStatus, hLogs, (hAccounts tx.sender).1, fun address => (hAccounts address).2⟩

/-- Kind: accounting.
    Says: a successful credit changes the recipient's balance by exactly
    the specified amount and preserves every other balance.
    Does not say: how the amount of the credit was calculated. -/
private theorem credit_balance (w result : TxWorld) (recipient amount address : Nat)
    (h : credit w recipient amount = .ok result) :
    (result.accounts address).balance =
      (w.accounts address).balance + (if address = recipient then amount else 0) := by
  unfold credit at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    by_cases hAddress : address = recipient
    · subst address
      simp [putAccount]
    · simp [putAccount, hAddress]

/-- Kind: accounting.
    Says: every settled balance is exactly the selected frame-world balance
    plus the sender refund and beneficiary tip, applying both when they alias.
    Does not say: which frame world a particular execution selects. -/
theorem finish_balance (tx : Envelope) (block : BlockContext) (budget : Budget)
    (world : TxWorld) (frame : FrameStatus) (s : State) (success : Bool) (result : Result) (address : Nat)
    (h : finish tx block budget world frame s success = .executed result) :
    (result.world.accounts address).balance = (world.accounts address).balance +
      (if address = tx.sender then result.charge.returnedWei else 0) +
      (if address = block.coinbase then result.charge.tip else 0) := by
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
        rw [credit_balance _ _ _ _ _ hTip, credit_balance _ _ _ _ _ hRefund]

/-- Kind: rollback.
    Says: a reverting transaction uses the pre-value-transfer checkpoint
    balance for every address, then applies the exact fee credits.
    Does not say: how much gas the reverted execution consumed. -/
theorem settleFrame_reverted_balance (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (initial terminal : State) (result : Result) (address : Nat)
    (h : settleFrame tx block budget escrow initial (.reverted terminal) = .executed result) :
    (result.world.accounts address).balance = (escrow.accounts address).balance +
      (if address = tx.sender then result.charge.returnedWei else 0) +
      (if address = block.coinbase then result.charge.tip else 0) :=
  finish_balance _ _ _ _ _ _ _ _ _ h

/-- Kind: rollback.
    Says: an exceptional transaction starts fee settlement from the exact
    pre-value-transfer balance at each address, including an aliased beneficiary.
    Does not say: which bytecode halts exceptionally. -/
theorem settleFrame_exception_balance (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow : TxWorld) (initial : State) (error : Error) (result : Result) (address : Nat)
    (h : settleFrame tx block budget escrow initial (.exceptional error) = .executed result) :
    (result.world.accounts address).balance = (escrow.accounts address).balance +
      (if address = tx.sender then result.charge.returnedWei else 0) +
      (if address = block.coinbase then result.charge.tip else 0) :=
  finish_balance _ _ _ _ _ _ _ _ _ h

private theorem credit_toDelete (w result : TxWorld) (address amount : Nat)
    (h : credit w address amount = .ok result) : result.toDelete = w.toDelete := by
  unfold credit at h
  dsimp only at h
  split at h <;> cases h
  rfl

private theorem finish_toDelete (tx : Envelope) (block : BlockContext) (budget : Budget)
    (world : TxWorld) (frame : FrameStatus) (s : State) (success : Bool) (result : Result)
    (h : finish tx block budget world frame s success = .executed result) :
    result.world.toDelete = world.toDelete := by
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
        exact (credit_toDelete _ _ _ _ hTip).trans (credit_toDelete _ _ _ _ hRefund)

/-- Kind: effect (transaction end, EIP-6780).
    Says: a successful transaction frame (stopped or returned) settles to the
    ordinary fee settlement of its world with exactly the registered accounts
    then reset to the absent account, after the sender refund and beneficiary
    tip (so a destroyed fee recipient or sender loses that credit); every
    unregistered account has the fee-settled balance and its own nonce,
    storage and code; the registration list is then empty and the receipt
    fields are those of the fee settlement.
    Does not say: that the frame world registered only created accounts
    (`SelfDestruct.selfDestructStep_registeredCreated` is the per-instruction
    part), or anything about a failed frame (it deletes nothing). -/
theorem settleFrame_success_destroys (tx : Envelope) (block : BlockContext) (budget : Budget)
    (escrow world : TxWorld) (initial terminal : State) (returns : Bool) (result : Result)
    (h : settleFrame tx block budget escrow initial
      (if returns then .returned world terminal else .stopped world terminal) = .executed result) :
    ∃ settled, finish tx block budget world (if returns then .returned else .stopped) terminal true =
        .executed settled ∧
      result = { settled with world := SelfDestruct.destroyRegistered settled.world } ∧
      result.world.toDelete = [] ∧
      (∀ address, address ∈ world.toDelete → result.world.accounts address = {}) ∧
      (∀ address, address ∉ world.toDelete →
        result.world.accounts address = settled.world.accounts address ∧
        (result.world.accounts address).balance = (world.accounts address).balance +
          (if address = tx.sender then result.charge.returnedWei else 0) +
          (if address = block.coinbase then result.charge.tip else 0) ∧
        (result.world.accounts address).nonce = (world.accounts address).nonce ∧
        (result.world.accounts address).storage = (world.accounts address).storage) := by
  have hInner : ∃ settled, finish tx block budget world (if returns then .returned else .stopped) terminal true =
      .executed settled ∧ result = { settled with world := SelfDestruct.destroyRegistered settled.world } := by
    cases returns
    · exact destroyAfter_executed h
    · exact destroyAfter_executed h
  obtain ⟨settled, hFinish, hResult⟩ := hInner
  have hList := finish_toDelete _ _ _ _ _ _ _ _ hFinish
  obtain ⟨_, _, _, hAccounts⟩ := finish_projection _ _ _ _ _ _ _ _ hFinish
  refine ⟨settled, hFinish, hResult, ?_, ?_, ?_⟩
  · rw [hResult]
    exact (SelfDestruct.destroyRegistered_accounts settled.world 0).2
  · intro address hIn
    rw [hResult]
    simp [(SelfDestruct.destroyRegistered_accounts settled.world address).1, hList, hIn]
  · intro address hOut
    have hSame : result.world.accounts address = settled.world.accounts address := by
      rw [hResult]
      simp [(SelfDestruct.destroyRegistered_accounts settled.world address).1, hList, hOut]
    refine ⟨hSame, ?_, ?_, ?_⟩
    · rw [hSame, finish_balance _ _ _ _ _ _ _ _ address hFinish, hResult]
    · rw [hSame]; exact (hAccounts address).1
    · rw [hSame]; exact (hAccounts address).2

#print axioms settleFrame_success_destroys
#print axioms admit_checked
#print axioms run_executed_admitted
#print axioms debitSender_projection
#print axioms charge_bounded
#print axioms charge_escrow_exact
#print axioms settleFrame_indeterminate
#print axioms finish_projection
#print axioms finish_balance
#print axioms settleFrame_reverted_checkpoint
#print axioms settleFrame_exception_checkpoint
#print axioms settleFrame_reverted_balance
#print axioms settleFrame_exception_balance

end EVMCleanroom.CallTransaction
