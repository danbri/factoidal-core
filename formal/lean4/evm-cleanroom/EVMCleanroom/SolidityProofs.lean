import EVMCleanroom.CalldataProofs
import EVMCleanroom.Frame

/-!
Signed comparison and zero-value frame evidence for Solidity's ABI dispatch.
Tracking issue: https://github.com/danbri/factoidal-core/issues/736.
-/

namespace EVMCleanroom

/-- Mathematical two's-complement interpretation of an EVM word. -/
def Word.signedValue (a : Word) : Int :=
  if a.val < signBit then Int.ofNat a.val else Int.ofNat a.val - Int.ofNat modulus

/-- Kind: representation helper.
    Says: the words one and zero encode true and false respectively.
    Does not say: any other word encodes a Boolean. -/
private theorem boolWord_values (b : Bool) :
    (Word.ofBool b = word 1 ↔ b = true) ∧ (Word.ofBool b = word 0 ↔ b = false) := by
  cases b <;> decide

/-- Kind: semantic correspondence.
    Says: the executable SLT helper returns one exactly for signed strict
    inequality and zero exactly for its complement, over all 256-bit words.
    Does not say: other signed arithmetic is implemented. -/
theorem Word.signedLt_correct (a b : Word) :
    (a.signedLt b = word 1 ↔ a.signedValue < b.signedValue) ∧
    (a.signedLt b = word 0 ↔ b.signedValue ≤ a.signedValue) := by
  have haBound := a.isLt
  have hbBound := b.isLt
  by_cases ha : a.val < signBit <;> by_cases hb : b.val < signBit
  all_goals simp [Word.signedLt, Word.signedValue, ha, hb, (boolWord_values _).1, (boolWord_values _).2] <;> omega

/-- Kind: gas boundary.
    Says: the actual SLT instruction with both operands available cannot
    commit with fewer than three units of gas.
    Does not say: gas failure has priority over an invalid stack. -/
theorem step_slt_outOfGas (s : State) (a b : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x12)
    (hStack : s.stack.items = a :: b :: rest) (hGas : s.gas < 3) :
    step s = .error .outOfGas := by
  have hBound := s.stack.bounded
  rw [hStack] at hBound
  have hNewBound : (a.signedLt b :: rest).length ≤ 1024 := by
    simp only [List.length_cons] at hBound ⊢
    exact Nat.le_trans (Nat.le_succ _) hBound
  rw [step_slt s a b rest hRun hOp hStack, commit, dif_pos hNewBound]
  simp [Nat.not_le_of_gt hGas]

/-- Kind: context admission.
    Says: the pure frame policy allows CALLVALUE exactly in a zero-value,
    read-only state.
    Does not say: the host supplied equivalent context for a remote call. -/
theorem Frame.zeroValueContextFree_callValue (s : State) :
    Frame.zeroValueContextFree s 0x34 = true ↔ s.readOnly = true ∧ s.callValue = 0 := by
  simp [Frame.zeroValueContextFree]

/-- Kind: context invariant.
    Says: every successful core step preserves the zero-value, read-only
    context when started in that context.
    Does not say: an unrelated frame is initialised with the same context. -/
theorem step_preserves_zero_value_context (s final : State)
    (hValue : s.callValue = 0) (hReadOnly : s.readOnly = true)
    (hStep : step s = .ok final) : final.callValue = 0 ∧ final.readOnly = true := by
  unfold step at hStep
  split at hStep
  · contradiction
  · rename_i plan _
    obtain ⟨_, _, hValue', _, hReadOnly', _⟩ :=
      commit_keeps_call_input s final plan.nextPC plan.stack plan.gasCost plan.halt
        plan.nextMemory plan.nextStorage hStep
    exact ⟨hValue'.trans hValue, hReadOnly'.trans hReadOnly⟩

#print axioms Word.signedLt_correct
#print axioms step_slt_outOfGas
#print axioms Frame.zeroValueContextFree_callValue
#print axioms step_preserves_zero_value_context

end EVMCleanroom
