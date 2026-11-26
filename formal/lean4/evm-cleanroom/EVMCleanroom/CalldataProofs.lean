import EVMCleanroom.Core

/-!
Proofs for the executable calldata loader and word predicates.
Tracking issue: https://github.com/danbri/factoidal-core/issues/734.
-/

namespace EVMCleanroom

/-- A byte of the input at its mathematical index, or zero beyond the input. -/
def paddedCallDataByte (data : ByteView) (offset : Nat) : Nat :=
  if offset < data.size then (data.raw offset).toNat else 0

/-- Big-endian semantics by place value. CALLDATALOAD uses width 32. -/
noncomputable def callDataValue (data : ByteView) (offset : Nat) : Nat → Nat
  | 0 => 0
  | remaining + 1 =>
    paddedCallDataByte data offset * 256 ^ remaining + callDataValue data (offset + 1) remaining

private theorem readByte_eq_paddedCallDataByte (data : ByteView) (offset : Nat) :
    (data.readByte offset).toNat = paddedCallDataByte data offset := by
  by_cases h : offset < data.size <;> simp [ByteView.readByte, paddedCallDataByte, h]

private theorem loadCallDataLoop_eq (data : ByteView) (width offset acc : Nat) :
    loadCallDataLoop data offset acc width = acc * 256 ^ width + callDataValue data offset width := by
  induction width generalizing offset acc with
  | zero => simp [loadCallDataLoop, callDataValue]
  | succ remaining ih =>
    simp only [loadCallDataLoop, callDataValue, ih, readByte_eq_paddedCallDataByte]
    simp [Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.add_assoc, Nat.pow_succ]

private theorem callDataValue_lt (data : ByteView) (width offset : Nat) :
    callDataValue data offset width < 256 ^ width := by
  induction width generalizing offset with
  | zero => simp [callDataValue]
  | succ remaining ih =>
    have hByte : paddedCallDataByte data offset < 256 := by
      unfold paddedCallDataByte
      split
      · exact UInt8.toNat_lt _
      · decide
    have hMul := Nat.mul_le_mul_right (256 ^ remaining) (Nat.succ_le_of_lt hByte)
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hMul
    rw [callDataValue, Nat.pow_succ, Nat.mul_comm (256 ^ remaining) 256]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (ih (offset + 1)) _) hMul

private theorem callDataValue_eq_zero (data : ByteView) (width offset : Nat)
    (h : data.size ≤ offset) : callDataValue data offset width = 0 := by
  induction width generalizing offset with
  | zero => rfl
  | succ remaining ih =>
    have hNext : data.size ≤ offset + 1 := by omega
    simp [callDataValue, paddedCallDataByte, Nat.not_lt_of_ge h, ih _ hNext]

/-- Kind: correspondence.
    Says: the executable loader returns the exact natural value of the 32
    zero-padded big-endian bytes; this value is below 2^256.
    Does not say: other calldata or ABI operations are implemented. -/
theorem loadCallDataWord_correct (data : ByteView) (offset : Nat) :
    (loadCallDataWord data offset).val = callDataValue data offset 32 ∧
    callDataValue data offset 32 < modulus := by
  have hBound : callDataValue data offset 32 < modulus := by
    have hWidth : 256 ^ 32 = modulus := by decide
    rw [← hWidth]
    exact callDataValue_lt data 32 offset
  refine ⟨?_, hBound⟩
  simp [loadCallDataWord, loadCallDataLoop_eq, word, Nat.mod_eq_of_lt hBound]

/-- Kind: boundary.
    Says: the executable loader returns zero at every offset at or past the input.
    Does not say: every zero load is outside the input. -/
theorem loadCallDataWord_eq_zero (data : ByteView) (offset : Nat)
    (h : data.size ≤ offset) : (loadCallDataWord data offset).val = 0 := by
  rw [(loadCallDataWord_correct data offset).1, callDataValue_eq_zero data 32 offset h]

/-- Kind: invariant.
    Says: every successful commit preserves the frame input and call context.
    Does not say: a newly constructed child frame inherits its parent's context. -/
theorem commit_keeps_call_input (s final : State) (pc : Nat) (stack : List Word) (cost : Nat)
    (halt : Bool) (memory : Option Memory) (storage : Option Storage)
    {nextLog : Option LogEntry}
    (h : commit s pc stack cost halt memory storage nextLog = .ok final) :
    final.callData = s.callData ∧ final.currentAddress = s.currentAddress ∧
    final.callValue = s.callValue ∧ final.selfBalance = s.selfBalance ∧
    final.readOnly = s.readOnly ∧ final.profile = s.profile := by
  unfold commit at h
  split at h
  next =>
    split at h
    next =>
      cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    next => contradiction
  next => contradiction

private theorem boolWord_cases (b : Bool) :
    Word.ofBool b = word 0 ∨ Word.ofBool b = word 1 := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Kind: range.
    Says: the executable LT, GT, EQ and ISZERO helpers return word 0 or 1.
    Does not say: this range alone proves the predicates compute the required comparisons. -/
theorem Word.comparisons_boolean (a b : Word) :
    (a.lt b = word 0 ∨ a.lt b = word 1) ∧
    (a.gt b = word 0 ∨ a.gt b = word 1) ∧
    (a.eq b = word 0 ∨ a.eq b = word 1) ∧
    (a.isZero = word 0 ∨ a.isZero = word 1) :=
  ⟨boolWord_cases _, boolWord_cases _, boolWord_cases _, boolWord_cases _⟩

/-- Kind: boundary.
    Says: SHL and SHR helpers return zero for any unsigned count of at least 256.
    Does not say: signed right shift has the same boundary result. -/
theorem Word.large_shifts_zero (shift value : Word) (h : 256 ≤ shift.val) :
    shift.shiftLeft value = word 0 ∧ shift.shiftRight value = word 0 := by
  simp [Word.shiftLeft, Word.shiftRight, Nat.not_lt_of_ge h]

-- The coarse pre-Shanghai profile cannot decide whether EIP-145 is active.
#guard ([0x1b, 0x1c] : List UInt8).all fun opcode =>
  match step { code := #[opcode], gas := 3, profile := .preShanghai } with
  | .error .unsupportedFork => true
  | _ => false

-- Calldata itself is available in the pre-Shanghai profile.
#guard
  let input : State := {
    code := #[0x60, 0, 0x35, 0]
    gas := 6
    profile := .preShanghai
    callData := ByteView.ofArray #[0xab]
  }
  match run 3 input with
  | .ok s => s.stack.items.map Word.val == [0xab * 256 ^ 31] && s.gas == 0
  | .error _ => false

#print axioms loadCallDataWord_correct
#print axioms loadCallDataWord_eq_zero
#print axioms commit_keeps_call_input
#print axioms Word.comparisons_boolean
#print axioms Word.large_shifts_zero

end EVMCleanroom
