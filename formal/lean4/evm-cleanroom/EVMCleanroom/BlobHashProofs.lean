import EVMCleanroom.CallOpcode

/-!
# BLOBHASH at the executable state boundary

The success statements derive an actual `step` result from the gas and stack
conditions. The index remains a full EVM word. Transaction admission owns the
hash list; these statements neither authenticate it nor validate blob sidecars.
-/

namespace EVMCleanroom

/-- Kind: checked-transfer preservation.
    Says: every successful value transfer keeps the world's transaction hash
    list, including a checked self-transfer.
    Does not say: transaction admission authenticated that list. -/
theorem World.pay_txBlobHashes {w out : World.TxWorld} {sender recipient amount : Nat}
    (h : World.pay w sender recipient amount = .ok out) :
    out.txBlobHashes = w.txBlobHashes := by
  unfold World.pay at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  · cases h
    rfl
  · split at h <;> try contradiction
    cases h
    rfl

#print axioms World.pay_txBlobHashes

/-- Kind: successful execution.
    Says: a funded BLOBHASH replaces its index, advances one byte and consumes
    exactly three gas, preserving memory, storage and transaction context.
    This includes static frames and a completely full input stack.
    Does not say: the context was authenticated by a signed transaction. -/
theorem step_blobHash_success (s : State) (index : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x49)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .prague ∨ s.profile = .osaka)
    (hStack : s.stack.items = index :: rest) (hGas : 3 ≤ s.gas) :
    ∃ out, step s = .ok out ∧
      out.stack.items = s.txBlobHashes.getD index.val (word 0) :: rest ∧
      out.gas + 3 = s.gas ∧ out.pc = s.pc + 1 ∧
      out.memory = s.memory ∧ out.storage = s.storage ∧
      out.txBlobHashes = s.txBlobHashes := by
  have hBound : (s.txBlobHashes.getD index.val (word 0) :: rest).length ≤ 1024 := by
    have h := s.stack.bounded
    simpa [hStack] using h
  rw [step_blobHash s index rest hRun hOp hProfile hStack]
  simp only [commit, hBound, hGas, dite_true, Option.getD_none]
  refine ⟨_, rfl, rfl, Nat.sub_add_cancel hGas, rfl, rfl, ?_, rfl⟩
  simp

/-- Kind: in-range opcode correspondence.
    Says: an in-range full-width index makes actual funded BLOBHASH return
    that exact list element, with its stack tail and three-gas charge.
    Does not say: list elements are valid versioned hashes. -/
theorem step_blobHash_in_range (s : State) (index : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x49)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .prague ∨ s.profile = .osaka)
    (hStack : s.stack.items = index :: rest) (hGas : 3 ≤ s.gas)
    (hIndex : index.val < s.txBlobHashes.size) :
    ∃ out, step s = .ok out ∧
      out.stack.items = s.txBlobHashes[index.val] :: rest ∧ out.gas + 3 = s.gas := by
  obtain ⟨out, hStep, hItems, hBill, _⟩ :=
    step_blobHash_success s index rest hRun hOp hProfile hStack hGas
  refine ⟨out, hStep, ?_, hBill⟩
  simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hIndex] using hItems

/-- Kind: out-of-range opcode correspondence.
    Says: every index at least the list length yields zero through actual
    funded BLOBHASH; no truncation to a machine integer precedes the comparison.
    Does not say: out-of-range is a transaction or execution failure. -/
theorem step_blobHash_out_of_range (s : State) (index : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x49)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .prague ∨ s.profile = .osaka)
    (hStack : s.stack.items = index :: rest) (hGas : 3 ≤ s.gas)
    (hIndex : s.txBlobHashes.size ≤ index.val) :
    ∃ out, step s = .ok out ∧
      out.stack.items = word 0 :: rest ∧ out.gas + 3 = s.gas := by
  obtain ⟨out, hStep, hItems, hBill, _⟩ :=
    step_blobHash_success s index rest hRun hOp hProfile hStack hGas
  refine ⟨out, hStep, ?_, hBill⟩
  simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hIndex] using hItems

/-- Kind: executable gas boundary.
    Says: actual admitted BLOBHASH with an index and fewer than three gas
    returns out-of-gas, including when its list is empty or index is large.
    Does not say: the caller's transaction checkpoint has been settled here. -/
theorem step_blobHash_outOfGas (s : State) (index : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x49)
    (hProfile : s.profile = .cancunPlus ∨ s.profile = .prague ∨ s.profile = .osaka)
    (hStack : s.stack.items = index :: rest) (hGas : s.gas < 3) :
    step s = .error .outOfGas := by
  have hBound : (s.txBlobHashes.getD index.val (word 0) :: rest).length ≤ 1024 := by
    have h := s.stack.bounded
    simpa [hStack] using h
  rw [step_blobHash s index rest hRun hOp hProfile hStack]
  simp only [commit, hBound, dite_true, Nat.not_le.mpr hGas, dite_false]

/-- Kind: transaction-context preservation.
    Says: every successful commit retains the supplied hash list regardless
    of the planned memory, storage or log effect.
    Does not say: the input context is consistent with its enclosing world. -/
theorem commit_txBlobHashes {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory}
    {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out) :
    out.txBlobHashes = s.txBlobHashes := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

/-- Kind: opcode-context preservation.
    Says: every successful actual Core.step preserves the transaction list,
    including intervening PUSH instructions before a child executes BLOBHASH.
    Does not say: the CALL-family dispatcher is itself a Core instruction. -/
theorem step_txBlobHashes {s out : State} (h : step s = .ok out) :
    out.txBlobHashes = s.txBlobHashes := by
  cases hp : planStep s with
  | error e => simp [step, hp] at h
  | ok p =>
    exact commit_txBlobHashes (by simpa [step, hp] using h)

#print axioms step_blobHash_success
#print axioms step_blobHash_in_range
#print axioms step_blobHash_out_of_range
#print axioms step_blobHash_outOfGas
#print axioms commit_txBlobHashes
#print axioms step_txBlobHashes

end EVMCleanroom
