import EVMCleanroom.ValueCall

/-!
# SELFDESTRUCT (0xff) under EIP-6780, and transaction-end deletion

Normative reference: ethereum/execution-specs, `forks/cancun` and
`forks/prague`, `vm/instructions/system.py` (`selfdestruct`), `fork.py`
(`process_transaction`: the registered accounts are destroyed after the
sender refund and the coinbase fee) and `vm/interpreter.py`
(`process_message_call`: a failed transaction registers nothing).

The instruction pops the beneficiary, charges 5000 gas, plus 2600 if the
beneficiary is cold (it is then warm), plus 25000 if the beneficiary is not
alive and the executing account's balance is nonzero. A static frame fails
after the charge. The whole balance of the executing account moves to the
beneficiary. Only an account created in the same transaction has its balance
set to zero (so a self-beneficiary burns it) and is registered for deletion;
any other account keeps its code, storage and nonce. The frame then halts
like STOP.

The registration list is a field of the transaction world, so every CALL
checkpoint and the entry checkpoint restore it when a frame fails.
`destroyRegistered` is the transaction-end deletion.

Only the `cancunPlus` and `osaka` profiles execute the instruction. The
`shanghaiPlus` profile spans the Cancun boundary (before it SELFDESTRUCT
always deleted), so it refuses, as does `preShanghai`.
-/

namespace EVMCleanroom.SelfDestruct

open EVMCleanroom.World

/-- GAS_SELF_DESTRUCT, GAS_COLD_ACCOUNT_ACCESS and GAS_SELF_DESTRUCT_NEW_ACCOUNT. -/
def gasCost (warm beneficiaryAlive : Bool) (balance : Nat) : Nat :=
  5000 + (if warm then 0 else 2600) + (if !beneficiaryAlive && balance != 0 then 25000 else 0)

/-- Zero the balance of an account created in this transaction and register
    it once for deletion at transaction end. -/
def register (w : TxWorld) (address : Nat) : TxWorld :=
  { putAccount w address { w.accounts address with balance := 0 } with
    toDelete := if w.toDelete.contains address then w.toDelete else address :: w.toDelete }

/-- The world after a funded, non-static SELFDESTRUCT: the frame journal is
    committed, the beneficiary is warmed, the balance moves, and a created
    account is registered. A transfer the bounded model cannot represent
    (an out-of-range address or balance) is a refusal, not an EVM failure. -/
def effects (w : TxWorld) (address beneficiary : Nat) (halted : State) : Except Error TxWorld :=
  match pay (WorldCall.warmTarget (commitFrame w address halted) beneficiary) address beneficiary
      (w.accounts address).balance with
  | .error _ => .error .unsupportedFork
  | .ok moved => .ok (if w.created address then register moved address else moved)

/-- Execute 0xff in the frame of `address`. On success the returned state is
    halted and the returned world is the frame's final world. -/
def selfDestructStep (w : TxWorld) (address : Nat) (s : State) : Except Error (TxWorld × State) :=
  if s.profile = .preShanghai ∨ s.profile = .shanghaiPlus then .error .unsupportedFork
  else
    match s.stack.items with
    | [] => .error .stackUnderflow
    | top :: rest =>
      let beneficiary := top.val % addressBound
      if !w.hasAccount beneficiary then .error (.incompleteState beneficiary none)
      else if !w.hasAccount address then .error (.incompleteState address none)
      else
        match commit s (s.pc + 1) rest
            (gasCost (w.warmAddresses beneficiary) (CallValue.accountAlive (w.accounts beneficiary))
              (w.accounts address).balance) true with
        | .error e => .error e
        | .ok halted =>
          if s.readOnly then .error .writeProtection
          else
            match effects w address beneficiary halted with
            | .error e => .error e
            | .ok final => .ok (final, { halted with selfBalance := (final.accounts address).balance })

/-- Transaction-end deletion (EELS `destroy_account` for every registered
    address): the account reads as absent afterwards. A transaction that
    registered nothing returns the same world without building a new map. -/
def destroyRegistered (w : TxWorld) : TxWorld :=
  if w.toDelete.isEmpty then w
  else
    let doomed := w.toDelete
    { w with
      accounts := fun address => if doomed.contains address then {} else w.accounts address
      toDelete := [] }

/-- The invariant behind "only accounts created in the same transaction are
    deleted": every registered address carries the created flag. -/
def RegisteredCreated (w : TxWorld) : Prop := ∀ address, address ∈ w.toDelete → w.created address = true

/-! ## Gas -/

/-- Kind: gas schedule (four price combinations).
    Says: the charge is 5000 for a warm beneficiary that needs no new account,
    7600 if it is cold, 30000 if it is warm but not alive and the balance is
    nonzero, 32600 if both; a zero balance never pays the 25000 surcharge.
    Does not say: that the frame has that much gas. -/
theorem gasCost_values (balance : Nat) (hFunded : balance ≠ 0) (alive warm : Bool) :
    gasCost true true balance = 5000 ∧ gasCost false true balance = 7600 ∧
    gasCost true false balance = 30000 ∧ gasCost false false balance = 32600 ∧
    gasCost warm alive 0 = 5000 + (if warm then 0 else 2600) := by
  simp [gasCost, hFunded]

private theorem commit_halt {s halted : State} {rest : List Word} {cost : Nat}
    (h : commit s (s.pc + 1) rest cost true = .ok halted) :
    cost ≤ s.gas ∧ halted.gas = s.gas - cost ∧ halted.halted = true ∧ halted.stack.items = rest ∧
    halted.storage = s.storage ∧ halted.logsRev = s.logsRev := by
  unfold commit at h
  split at h
  · split at h
    · next hGas =>
      cases h
      exact ⟨hGas, rfl, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- The decomposition every success theorem below starts from. -/
private theorem step_ok {w w' : TxWorld} {address : Nat} {s s' : State} {top : Word} {rest : List Word}
    (hStack : s.stack.items = top :: rest)
    (h : selfDestructStep w address s = .ok (w', s')) :
    ∃ halted moved,
      commit s (s.pc + 1) rest
        (gasCost (w.warmAddresses (top.val % addressBound))
          (CallValue.accountAlive (w.accounts (top.val % addressBound))) (w.accounts address).balance) true =
        .ok halted ∧
      s.readOnly = false ∧
      pay (WorldCall.warmTarget (commitFrame w address halted) (top.val % addressBound)) address
        (top.val % addressBound) (w.accounts address).balance = .ok moved ∧
      w' = (if w.created address then register moved address else moved) ∧
      s' = { halted with selfBalance := (w'.accounts address).balance } := by
  unfold selfDestructStep at h
  split at h
  · cases h
  · rw [hStack] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next halted hCommit =>
          split at h
          · cases h
          · next hStatic =>
            cases hPay : pay (WorldCall.warmTarget (commitFrame w address halted) (top.val % addressBound))
                address (top.val % addressBound) (w.accounts address).balance with
            | error e => simp [effects, hPay] at h
            | ok moved =>
              simp only [effects, hPay, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hWorld, hState⟩ := h
              refine ⟨halted, moved, hCommit, by simpa using hStatic, hPay, hWorld.symm, ?_⟩
              rw [← hState, ← hWorld]

/-- A checked transfer of the whole balance is the identity for a
    self-beneficiary and the two-account update otherwise. -/
private theorem pay_ok {w out : TxWorld} {sender recipient amount : Nat}
    (h : pay w sender recipient amount = .ok out) :
    out = if sender = recipient then w else payUnchecked w sender recipient amount := by
  unfold pay at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · next hSelf => cases h; simp [hSelf]
  · next hSelf =>
    split at h <;> try contradiction
    cases h
    simp [hSelf]

/-- Kind: executable correspondence (exact gas).
    Says: a successful SELFDESTRUCT leaves exactly the entry gas minus the
    scheduled charge, computed from the beneficiary's warmth and liveness and
    the executing account's balance before the instruction.
    Does not say: that an oracle agrees (that is the differential test). -/
theorem selfDestructStep_gas {w w' : TxWorld} {address : Nat} {s s' : State} {top : Word} {rest : List Word}
    (hStack : s.stack.items = top :: rest) (h : selfDestructStep w address s = .ok (w', s')) :
    gasCost (w.warmAddresses (top.val % addressBound))
      (CallValue.accountAlive (w.accounts (top.val % addressBound))) (w.accounts address).balance ≤ s.gas ∧
    s'.gas = s.gas - gasCost (w.warmAddresses (top.val % addressBound))
      (CallValue.accountAlive (w.accounts (top.val % addressBound))) (w.accounts address).balance := by
  obtain ⟨halted, moved, hCommit, _, _, _, hState⟩ := step_ok hStack h
  obtain ⟨hLe, hGas, _⟩ := commit_halt hCommit
  rw [hState]
  exact ⟨hLe, hGas⟩

/-- Kind: gas boundary.
    Says: with one gas less than the scheduled charge the instruction is out
    of gas, in a static frame too (the charge precedes the static check), and
    returns no world: nothing is warmed, moved or registered.
    Does not say: which later check would fail. -/
theorem selfDestructStep_outOfGas (w : TxWorld) (address : Nat) (s : State) (top : Word) (rest : List Word)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .osaka) (hStack : s.stack.items = top :: rest)
    (hBeneficiary : w.hasAccount (top.val % addressBound) = true) (hSelf : w.hasAccount address = true)
    (hGas : s.gas < gasCost (w.warmAddresses (top.val % addressBound))
      (CallValue.accountAlive (w.accounts (top.val % addressBound))) (w.accounts address).balance) :
    selfDestructStep w address s = .error .outOfGas := by
  have hBound : rest.length ≤ 1024 := by
    have := s.stack.bounded
    rw [hStack] at this
    simp at this
    omega
  have hFork : ¬ (s.profile = .preShanghai ∨ s.profile = .shanghaiPlus) := by
    rcases hProfile with h | h <;> simp [h]
  simp [selfDestructStep, hFork, hStack, hBeneficiary, hSelf, commit, hBound, Nat.not_le.mpr hGas]

/-- Kind: write protection.
    Says: a funded SELFDESTRUCT in a static frame is the write-protection
    failure, an exceptional halt of that frame, and returns no world.
    Does not say: what the caller's checkpoint restores (see `CallOpcode`). -/
theorem selfDestructStep_static (w : TxWorld) (address : Nat) (s : State) (top : Word) (rest : List Word)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .osaka) (hStack : s.stack.items = top :: rest)
    (hBeneficiary : w.hasAccount (top.val % addressBound) = true) (hSelf : w.hasAccount address = true)
    (hStatic : s.readOnly = true)
    (hGas : gasCost (w.warmAddresses (top.val % addressBound))
      (CallValue.accountAlive (w.accounts (top.val % addressBound))) (w.accounts address).balance ≤ s.gas) :
    selfDestructStep w address s = .error .writeProtection := by
  have hBound : rest.length ≤ 1024 := by
    have := s.stack.bounded
    rw [hStack] at this
    simp at this
    omega
  have hFork : ¬ (s.profile = .preShanghai ∨ s.profile = .shanghaiPlus) := by
    rcases hProfile with h | h <;> simp [h]
  simp [selfDestructStep, hFork, hStack, hBeneficiary, hSelf, commit, hBound, hGas, hStatic]

/-- Kind: fork admission.
    Says: the profiles that do not pin EIP-6780 (`preShanghai`, and
    `shanghaiPlus`, which spans the Cancun boundary) refuse the instruction.
    Does not say: the instruction is absent on those forks. -/
theorem selfDestructStep_fork (w : TxWorld) (address : Nat) (s : State)
    (hProfile : s.profile = .preShanghai ∨ s.profile = .shanghaiPlus) :
    selfDestructStep w address s = .error .unsupportedFork := by
  simp [selfDestructStep, hProfile]

/-- Kind: boundary (witness mode).
    Says: a beneficiary outside the supplied coverage is a refusal naming
    it, never a transfer to a defaulted empty account.
    Does not say: the account is absent from the real state. -/
theorem selfDestructStep_uncovered (w : TxWorld) (address : Nat) (s : State) (top : Word) (rest : List Word)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .osaka) (hStack : s.stack.items = top :: rest)
    (hMissing : w.hasAccount (top.val % addressBound) = false) :
    selfDestructStep w address s = .error (.incompleteState (top.val % addressBound) none) := by
  have hFork : ¬ (s.profile = .preShanghai ∨ s.profile = .shanghaiPlus) := by
    rcases hProfile with h | h <;> simp [h]
  simp [selfDestructStep, hFork, hStack, hMissing]

/-! ## Effects -/

/-- Kind: frame result.
    Says: a successful SELFDESTRUCT halts the frame with the beneficiary
    popped, and the frame's output buffer is whatever it was (empty unless
    the caller supplied one), as for STOP.
    Does not say: how the dispatcher resumes a caller. -/
theorem selfDestructStep_halts {w w' : TxWorld} {address : Nat} {s s' : State} {top : Word} {rest : List Word}
    (hStack : s.stack.items = top :: rest) (h : selfDestructStep w address s = .ok (w', s')) :
    s'.halted = true ∧ s'.stack.items = rest ∧ s.readOnly = false := by
  obtain ⟨halted, moved, hCommit, hStatic, _, _, hState⟩ := step_ok hStack h
  obtain ⟨_, _, hHalted, hItems, _⟩ := commit_halt hCommit
  rw [hState]
  exact ⟨hHalted, hItems, hStatic⟩

private theorem register_fields (w : TxWorld) (address : Nat) :
    (register w address).warmAddresses = w.warmAddresses ∧ (register w address).created = w.created :=
  ⟨rfl, rfl⟩

private theorem moved_fields {w moved : TxWorld} {address beneficiary amount : Nat} {halted : State}
    (hPay : pay (WorldCall.warmTarget (commitFrame w address halted) beneficiary) address beneficiary amount =
      .ok moved) :
    moved.warmAddresses beneficiary = true ∧
    (∀ other, other ≠ beneficiary → moved.warmAddresses other = w.warmAddresses other) ∧
    moved.created = w.created ∧ moved.toDelete = w.toDelete := by
  have hOut := pay_ok hPay
  have hBase : (WorldCall.warmTarget (commitFrame w address halted) beneficiary).warmAddresses beneficiary = true ∧
      (∀ other, other ≠ beneficiary →
        (WorldCall.warmTarget (commitFrame w address halted) beneficiary).warmAddresses other =
          w.warmAddresses other) ∧
      (WorldCall.warmTarget (commitFrame w address halted) beneficiary).created = w.created ∧
      (WorldCall.warmTarget (commitFrame w address halted) beneficiary).toDelete = w.toDelete := by
    unfold WorldCall.warmTarget
    split
    · next hWarm => exact ⟨hWarm, fun _ _ => rfl, rfl, rfl⟩
    · exact ⟨by simp, fun other hOther => by simp [hOther, commitFrame], rfl, rfl⟩
  rw [hOut]
  split
  · exact hBase
  · exact hBase

/-- Kind: access list (EIP-2929).
    Says: after a successful SELFDESTRUCT the beneficiary is warm, and no
    other address changed warmth.
    Does not say: that a failed frame keeps the warm-up (its checkpoint drops it). -/
theorem selfDestructStep_warms {w w' : TxWorld} {address : Nat} {s s' : State} {top : Word} {rest : List Word}
    (hStack : s.stack.items = top :: rest) (h : selfDestructStep w address s = .ok (w', s')) :
    w'.warmAddresses (top.val % addressBound) = true ∧
    ∀ other, other ≠ top.val % addressBound → w'.warmAddresses other = w.warmAddresses other := by
  obtain ⟨halted, moved, _, _, hPay, hWorld, _⟩ := step_ok hStack h
  obtain ⟨hWarm, hOthers, _, _⟩ := moved_fields hPay
  rw [hWorld]
  split
  · rw [(register_fields moved address).1]
    exact ⟨hWarm, hOthers⟩
  · exact ⟨hWarm, hOthers⟩

private theorem moved_accounts {w moved : TxWorld} {address beneficiary : Nat} {halted : State}
    (hPay : pay (WorldCall.warmTarget (commitFrame w address halted) beneficiary) address beneficiary
      (w.accounts address).balance = .ok moved) (other : Nat) :
    moved.accounts other =
      if other = address then
        { w.accounts address with
          storage := halted.storage.current
          balance := if address = beneficiary then (w.accounts address).balance else 0 }
      else if other = beneficiary then
        { w.accounts beneficiary with
          balance := (w.accounts beneficiary).balance + (w.accounts address).balance }
      else w.accounts other := by
  have hOut := pay_ok hPay
  have hBase : ∀ a, (WorldCall.warmTarget (commitFrame w address halted) beneficiary).accounts a =
      (commitFrame w address halted).accounts a := fun a => WorldCall.warmTarget_accounts _ _ _
  rw [hOut]
  by_cases hSelf : address = beneficiary
  · subst hSelf
    simp only [if_true]
    rw [WorldCall.warmTarget_accounts]
    by_cases hOther : other = address <;> simp [commitFrame, hOther]
  · simp only [hSelf, if_false, payUnchecked, WorldCall.warmTarget_accounts]
    have hNe : beneficiary ≠ address := fun e => hSelf e.symm
    by_cases hOther : other = address
    · simp [hOther, commitFrame]
    · by_cases hB : other = beneficiary
      · simp [hB, commitFrame, hNe]
      · simp [hOther, hB, commitFrame]

/-- Kind: effect (EIP-6780, account not created in this transaction).
    Says: the executing account keeps its code and nonce, its storage is the
    frame's own journal, nothing is registered for deletion, its balance is
    unchanged for a self-beneficiary and otherwise zero with the beneficiary
    credited by exactly the old balance, and every third account is unchanged.
    Does not say: that the created flag is accurate (CREATE sets it). -/
theorem selfDestructStep_notCreated {w w' : TxWorld} {address : Nat} {s s' : State} {top : Word}
    {rest : List Word} (hStack : s.stack.items = top :: rest)
    (hOld : w.created address = false) (h : selfDestructStep w address s = .ok (w', s')) :
    (w'.accounts address).code = (w.accounts address).code ∧
    (w'.accounts address).nonce = (w.accounts address).nonce ∧
    (w'.accounts address).storage = s.storage.current ∧
    w'.toDelete = w.toDelete ∧
    (w'.accounts address).balance =
      (if address = top.val % addressBound then (w.accounts address).balance else 0) ∧
    (address ≠ top.val % addressBound →
      (w'.accounts (top.val % addressBound)).balance =
        (w.accounts (top.val % addressBound)).balance + (w.accounts address).balance) ∧
    (∀ other, other ≠ address → other ≠ top.val % addressBound → w'.accounts other = w.accounts other) := by
  obtain ⟨halted, moved, hCommit, _, hPay, hWorld, _⟩ := step_ok hStack h
  obtain ⟨_, _, _, _, hStorage, _⟩ := commit_halt hCommit
  have hAccounts := moved_accounts hPay
  obtain ⟨_, _, _, hDelete⟩ := moved_fields hPay
  simp only [hOld, Bool.false_eq_true, if_false] at hWorld
  subst hWorld
  refine ⟨by simp [hAccounts], by simp [hAccounts], by simp [hAccounts, hStorage], hDelete, ?_, ?_, ?_⟩
  · rw [hAccounts]
    by_cases hSelf : address = top.val % addressBound <;> simp [hSelf]
  · intro hSelf
    have hNe : top.val % addressBound ≠ address := fun e => hSelf e.symm
    rw [hAccounts]
    simp [hNe]
  · intro other hOther hB
    rw [hAccounts]
    simp [hOther, hB]

/-- Kind: effect (EIP-6780, account created in this transaction).
    Says: the executing account's balance is zero (so a self-beneficiary
    burns it), it is registered for deletion, a different beneficiary is
    credited by exactly the old balance, the account's code and nonce are
    still present (a later call in the same transaction runs its code), and
    every third account is unchanged.
    Does not say: that the account is already deleted; that is `destroyRegistered`. -/
theorem selfDestructStep_created {w w' : TxWorld} {address : Nat} {s s' : State} {top : Word}
    {rest : List Word} (hStack : s.stack.items = top :: rest)
    (hNew : w.created address = true) (h : selfDestructStep w address s = .ok (w', s')) :
    (w'.accounts address).balance = 0 ∧ address ∈ w'.toDelete ∧
    (address ≠ top.val % addressBound →
      (w'.accounts (top.val % addressBound)).balance =
        (w.accounts (top.val % addressBound)).balance + (w.accounts address).balance) ∧
    (w'.accounts address).code = (w.accounts address).code ∧
    (w'.accounts address).nonce = (w.accounts address).nonce ∧
    (w'.accounts address).storage = s.storage.current ∧
    (∀ other, other ≠ address → other ≠ top.val % addressBound → w'.accounts other = w.accounts other) := by
  obtain ⟨halted, moved, hCommit, _, hPay, hWorld, _⟩ := step_ok hStack h
  obtain ⟨_, _, _, _, hStorage, _⟩ := commit_halt hCommit
  have hAccounts := moved_accounts hPay
  simp only [hNew, if_true] at hWorld
  subst hWorld
  refine ⟨by simp [register, putAccount], ?_, ?_, by simp [register, putAccount, hAccounts],
    by simp [register, putAccount, hAccounts], by simp [register, putAccount, hAccounts, hStorage], ?_⟩
  · unfold register
    dsimp only
    split
    · next hIn => simpa using hIn
    · simp
  · intro hSelf
    have hNe : top.val % addressBound ≠ address := fun e => hSelf e.symm
    simp [register, putAccount, hNe, hAccounts]
  · intro other hOther hB
    simp [register, putAccount, hOther, hAccounts, hB]

/-- Kind: invariant (one instruction).
    Says: SELFDESTRUCT never changes the created flags, registers at most the
    executing account, and only if that account carries the created flag; so
    "every registered address was created in this transaction" is preserved.
    Does not say: that every other dispatcher transition preserves it (they
    do not write either field; `CallOpcode` states what is proved there). -/
theorem selfDestructStep_registeredCreated {w w' : TxWorld} {address : Nat} {s s' : State}
    (h : selfDestructStep w address s = .ok (w', s')) :
    w'.created = w.created ∧
    (∀ other, other ∈ w'.toDelete → other ∈ w.toDelete ∨ (other = address ∧ w.created address = true)) ∧
    (RegisteredCreated w → RegisteredCreated w') := by
  cases hItems : s.stack.items with
  | nil =>
    unfold selfDestructStep at h
    rw [hItems] at h
    split at h <;> cases h
  | cons top rest =>
    obtain ⟨halted, moved, _, _, hPay, hWorld, _⟩ := step_ok hItems h
    obtain ⟨_, _, hCreated, hDelete⟩ := moved_fields hPay
    have hMembers : ∀ other, other ∈ w'.toDelete →
        other ∈ w.toDelete ∨ (other = address ∧ w.created address = true) := by
      intro other hIn
      rw [hWorld] at hIn
      split at hIn
      · next hNew =>
        unfold register at hIn
        dsimp only at hIn
        split at hIn
        · exact .inl (hDelete ▸ hIn)
        · rcases List.mem_cons.mp hIn with hEq | hOld
          · exact .inr ⟨hEq, hNew⟩
          · exact .inl (hDelete ▸ hOld)
      · exact .inl (hDelete ▸ hIn)
    have hSame : w'.created = w.created := by
      rw [hWorld]
      split
      · exact (register_fields moved address).2.trans hCreated
      · exact hCreated
    refine ⟨hSame, hMembers, fun hInv other hIn => ?_⟩
    rw [hSame]
    rcases hMembers other hIn with hOld | ⟨hEq, hNew⟩
    · exact hInv other hOld
    · rw [hEq]; exact hNew

/-! ## Transaction end -/

/-- Kind: effect (transaction end).
    Says: deletion resets exactly the registered accounts to the absent
    account (zero balance and nonce, no code, empty storage), leaves every
    other account as it was, and empties the registration list.
    Does not say: who registered them, or that the list was kept by a
    successful transaction (see `CallTransaction.settleFrame`). -/
theorem destroyRegistered_accounts (w : TxWorld) (address : Nat) :
    (destroyRegistered w).accounts address = (if address ∈ w.toDelete then {} else w.accounts address) ∧
    (destroyRegistered w).toDelete = [] := by
  unfold destroyRegistered
  split
  · next hEmpty =>
    have hNil : w.toDelete = [] := by simpa using hEmpty
    simp [hNil]
  · by_cases hIn : address ∈ w.toDelete <;> simp [hIn]

/-- Kind: invariant consequence.
    Says: if every registered address was created in this transaction, an
    account without the created flag survives transaction-end deletion unchanged.
    Does not say: that the invariant holds for an arbitrary supplied world. -/
theorem destroyRegistered_keeps_old (w : TxWorld) (hInv : RegisteredCreated w) (address : Nat)
    (hOld : w.created address = false) : (destroyRegistered w).accounts address = w.accounts address := by
  rw [(destroyRegistered_accounts w address).1]
  split
  · next hIn => rw [hInv address hIn] at hOld; cases hOld
  · rfl

/-- Kind: projection.
    Says: deletion changes no transaction field other than the accounts and
    the registration list (logs, refund counter, warmth and context stay).
    Does not say: that the next transaction reuses those fields. -/
theorem destroyRegistered_fields (w : TxWorld) :
    (destroyRegistered w).logsRev = w.logsRev ∧ (destroyRegistered w).refund = w.refund ∧
    (destroyRegistered w).warmAddresses = w.warmAddresses ∧ (destroyRegistered w).witnessed = w.witnessed ∧
    (destroyRegistered w).created = w.created := by
  unfold destroyRegistered
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Kind: boundary.
    Says: a world with nothing registered is returned unchanged.
    Does not say: anything about cost; the empty test is one list match. -/
theorem destroyRegistered_none (w : TxWorld) (h : w.toDelete = []) : destroyRegistered w = w := by
  simp [destroyRegistered, h]

#print axioms gasCost_values
#print axioms selfDestructStep_gas
#print axioms selfDestructStep_outOfGas
#print axioms selfDestructStep_static
#print axioms selfDestructStep_fork
#print axioms selfDestructStep_uncovered
#print axioms selfDestructStep_halts
#print axioms selfDestructStep_warms
#print axioms selfDestructStep_notCreated
#print axioms selfDestructStep_created
#print axioms selfDestructStep_registeredCreated
#print axioms destroyRegistered_accounts
#print axioms destroyRegistered_keeps_old
#print axioms destroyRegistered_fields
#print axioms destroyRegistered_none

end EVMCleanroom.SelfDestruct
