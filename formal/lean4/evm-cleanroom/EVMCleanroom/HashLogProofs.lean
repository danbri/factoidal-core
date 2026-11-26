import EVMCleanroom.ByteCopyProofs
import EVMCleanroom.Proofs

/-!
Properties of the executable hash and log dispatch.
Tracking issue: https://github.com/danbri/factoidal-core/issues/796.
-/

namespace EVMCleanroom

/-- Kind: work boundary.
    Says: successful enabled KECCAK256 is both within the host's byte cap
    and bounded in absorbed blocks by the available EVM gas.
    Does not say: either limit bounds the host cost of interpreting a byte view. -/
theorem step_keccak_work_bound (s final : State) (offset length : Word) (rest : List Word)
    (acceptance : Keccak.Acceptance) (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x20)
    (hAccept : s.keccakAcceptance = some acceptance)
    (hStack : s.stack.items = offset :: length :: rest) (hStep : step s = .ok final) :
    length.val ≤ Keccak.maxInputBytes ∧
    Keccak.paddedBlocks length.val ≤ Keccak.maxInputBytes / Keccak.rate + 1 ∧
    Keccak.paddedBlocks length.val ≤ s.gas / 6 + 1 := by
  by_cases hGas : MemoryGas.keccakCost s.memory.words offset.val length.val ≤ s.gas
  · by_cases hSize : length.val ≤ Keccak.maxInputBytes
    · exact ⟨hSize, Nat.add_le_add_right (Nat.div_le_div_right hSize) 1,
        Keccak.paddedBlocks_paid _ _ _ _ hGas⟩
    · rw [step_keccak_resourceLimit s offset length rest acceptance hRun hOp hAccept hStack
        hGas (Nat.lt_of_not_ge hSize)] at hStep
      contradiction
  · rw [step_keccak_outOfGas s offset length rest acceptance hRun hOp hAccept hStack
      (Nat.lt_of_not_ge hGas)] at hStep
    contradiction

/-- Kind: state projection.
    Says: a successful commit adds the planned log in a writable frame and preserves
    the prior journal in a static frame or when the plan has no log.
    Does not say: a later frame outcome keeps the whole journal. -/
theorem commit_log_effect (s final : State) (pc : Nat) (xs : List Word) (gas : Nat)
    (halt : Bool) (memory : Option Memory) (storage : Option Storage) (entry : Option LogEntry)
    (h : commit s pc xs gas halt memory storage entry = .ok final) :
    final.logsRev = s.recordLog entry := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      rfl
    · contradiction
  · contradiction

/-- Kind: invariant.
    Says: any successful core step in a static frame preserves the log journal.
    Does not say: a static frame can execute a LOG opcode. -/
theorem step_static_logs_unchanged (s final : State) (hStatic : s.readOnly = true)
    (hStep : step s = .ok final) : final.logsRev = s.logsRev := by
  cases hp : planStep s with
  | error e => simp [step, hp] at hStep
  | ok plan =>
    have hCommit : commit s plan.nextPC plan.stack plan.gasCost plan.halt plan.nextMemory
        plan.nextStorage plan.nextLog = .ok final := by
      simpa [step, hp] using hStep
    rw [commit_log_effect _ _ _ _ _ _ _ _ _ hCommit]
    cases plan.nextLog <;> simp [State.recordLog, hStatic]

/-- Kind: dispatcher correspondence.
    Says: an actual successful LOG puts one entry ahead of the previous journal,
    using the executing address, exact stack topics and every byte of the paid window.
    Does not say: that an enclosing transaction will keep the entry. -/
theorem step_log_entry (s final : State) (offset length : Word) (topics rest : List Word) (count : Nat)
    (hCount : count ≤ 4) (hRun : s.halted = false) (hOp : byteAt s s.pc = 0xa0 + count)
    (hTopics : topics.length = count) (hStack : s.stack.items = offset :: length :: (topics ++ rest))
    (hGas : MemoryGas.logCost s.memory.words offset.val length.val count ≤ s.gas)
    (hStatic : s.readOnly = false) (hStep : step s = .ok final) :
    ∃ entry : LogEntry, final.logsRev = entry :: s.logsRev ∧ entry.address = s.currentAddress ∧
      entry.topics = topics ∧ entry.data.size = length.val ∧
      final.gas + MemoryGas.logCost s.memory.words offset.val length.val count = s.gas ∧
      ∀ i, i < length.val → entry.data.readByte i =
        (s.memory.expand (MemoryGas.requestedWords offset.val length.val)).readByte (offset.val + i) := by
  rw [step_log s offset length topics rest count hCount hRun hOp hTopics hStack hGas hStatic] at hStep
  let log : LogEntry :=
    ⟨s.currentAddress, topics,
      ByteView.ofMemory (s.memory.expand (MemoryGas.requestedWords offset.val length.val)) offset.val length.val⟩
  refine ⟨log, ?_, rfl, rfl, rfl, commit_gas_exact hStep, ?_⟩
  · simpa [State.recordLog, hStatic, log] using commit_log_effect _ _ _ _ _ _ _ _ _ hStep
  · intro i hi
    exact ByteView.readByte_ofMemory_inside _ _ _ i hi

/-- Kind: context admission.
    Says: the standalone pure-frame policy allows KECCAK256 in its normal zero-value,
    read-only input. The core step still checks the capability.
    Does not say: the policy admits log emission. -/
theorem Frame.zeroValueContextFree_keccak (s : State) :
    Frame.zeroValueContextFree s 0x20 = true ↔ s.readOnly = true ∧ s.callValue = 0 := by
  simp [Frame.zeroValueContextFree]

/-- Kind: context admission.
    Says: the standalone pure-frame policy refuses each LOG opcode.
    Does not say: a writable unrestricted frame must also refuse. -/
theorem Frame.zeroValueContextFree_log (s : State) (count : Nat) (hCount : count ≤ 4) :
    Frame.zeroValueContextFree s (0xa0 + count) = false := by
  have hCases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨ count = 4 := by omega
  rcases hCases with h | h | h | h | h <;> subst count <;> simp [Frame.zeroValueContextFree]

#print axioms step_keccak_work_bound
#print axioms commit_log_effect
#print axioms step_static_logs_unchanged
#print axioms step_log_entry
#print axioms Frame.zeroValueContextFree_keccak
#print axioms Frame.zeroValueContextFree_log

end EVMCleanroom
