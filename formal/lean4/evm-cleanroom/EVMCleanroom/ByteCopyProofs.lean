import EVMCleanroom.Frame

/-!
Correctness of bounded byte views and the sparse overlay used by the
calldata, code and returndata copy instructions.
Tracking issue: https://github.com/danbri/factoidal-core/issues/744.
-/

namespace EVMCleanroom

/-- Kind: correspondence.
    Says: an in-bounds read returns the backing byte at that index.
    Does not say: the backing function itself checks the size. -/
theorem ByteView.readByte_inside (view : ByteView) (offset : Nat) (h : offset < view.size) :
    view.readByte offset = view.raw offset := by
  simp [ByteView.readByte, h]

/-- Kind: boundary.
    Says: a read at or beyond the view size is zero, even for a nonzero backing byte.
    Does not say: every zero byte is out of bounds. -/
theorem ByteView.readByte_outside (view : ByteView) (offset : Nat) (h : view.size ≤ offset) :
    view.readByte offset = 0 := by
  simp [ByteView.readByte, Nat.not_lt_of_ge h]

/-- Kind: correspondence.
    Says: the array adapter agrees with zero-padded array indexing at every Nat offset.
    Does not say: an array is materialised for other views. -/
theorem ByteView.readByte_ofArray (bytes : Array UInt8) (offset : Nat) :
    (ByteView.ofArray bytes).readByte offset = bytes.getD offset 0 := by
  by_cases h : offset < bytes.size <;> simp [ByteView.ofArray, ByteView.readByte, h]

/-- Kind: correspondence.
    Says: within a memory window, the adapter reads the original memory at base plus index.
    Does not say: the original memory already paid for every byte of the view. -/
theorem ByteView.readByte_ofMemory_inside (m : Memory) (offset length index : Nat)
    (h : index < length) :
    (ByteView.ofMemory m offset length).readByte index = m.readByte (offset + index) := by
  simp [ByteView.ofMemory, ByteView.readByte, h]

/-- Kind: correspondence.
    Says: when a copy uses the specified expansion, every destination byte reads its
    corresponding source byte for the whole destination range.
    Does not say: the caller can afford the expansion. -/
theorem Memory.readByte_expandedCopy_inside (m : Memory) (source : ByteView)
    (sourceOffset destOffset length address : Nat)
    (hStart : destOffset ≤ address) (hEnd : address < destOffset + length) :
    ((m.expand (MemoryGas.requestedWords destOffset length)).copyFrom source
      sourceOffset destOffset length).readByte address =
      source.readByte (sourceOffset + (address - destOffset)) := by
  have hLength : 0 < length := by omega
  have hCover := MemoryGas.requestedWords_covers destOffset length hLength
  have hGrow : MemoryGas.requestedWords destOffset length ≤
      (m.expand (MemoryGas.requestedWords destOffset length)).words :=
    Nat.le_max_right _ _
  refine Memory.readByte_copyFrom_inside _ _ _ _ _ _ ?_ hStart hEnd
  exact Nat.lt_of_lt_of_le hEnd (Nat.le_trans hCover (Nat.mul_le_mul_left 32 hGrow))

/-- Kind: invariant.
    Says: the common commit path preserves both byte views for return data.
    Does not say: creating or completing a child call leaves both views intact. -/
theorem commit_keeps_return_data (s final : State) (pc : Nat) (stack : List Word) (cost : Nat)
    (halt : Bool) (memory : Option Memory) (storage : Option Storage)
    (h : commit s pc stack cost halt memory storage = .ok final) :
    final.returnData = s.returnData ∧ final.outputData = s.outputData := by
  unfold commit at h
  split at h
  next =>
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · contradiction
  next => contradiction

private theorem commit_sets_memory (s final : State) (pc : Nat) (stack : List Word) (cost : Nat)
    (halt : Bool) (memory : Memory) (storage : Option Storage)
    (h : commit s pc stack cost halt (some memory) storage = .ok final) :
    final.memory = memory := by
  unfold commit at h
  split at h
  next =>
    split at h
    · cases h
      rfl
    · contradiction
  next => contradiction

/-- Kind: dispatcher correspondence.
    Says: a successful RETURNDATACOPY reads each destination byte from the
    matching in-bounds backing byte of the last return-data buffer.
    Does not say: a failed step publishes a memory overlay. -/
theorem step_returnDataCopy_readByte (s final : State)
    (dest source length : Word) (rest : List Word) (address : Nat)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x3e) (hProfile : s.profile ≠ .preShanghai)
    (hStack : s.stack.items = dest :: source :: length :: rest)
    (hGas : MemoryGas.copyCost s.memory.words dest.val length.val ≤ s.gas)
    (hBounds : source.val + length.val ≤ s.returnData.size)
    (hStep : step s = .ok final) (hStart : dest.val ≤ address) (hEnd : address < dest.val + length.val) :
    final.memory.readByte address = s.returnData.raw (source.val + (address - dest.val)) := by
  rw [step_returnDataCopy s dest source length rest hRun hOp hProfile hStack hGas hBounds] at hStep
  rw [commit_sets_memory _ _ _ _ _ _ _ _ hStep]
  rw [Memory.readByte_expandedCopy_inside _ _ _ _ _ _ hStart hEnd]
  exact ByteView.readByte_inside _ _ (by omega)

/-- Kind: correspondence.
    Says: the common RETURN and REVERT handler records its own memory window as output.
    Does not say: this window is the complete output of the most recent child call. -/
theorem Frame.haltWithData_output (s final : State) (offset length : Nat)
    (h : Frame.haltWithData s = .ok (final, offset, length)) :
    final.outputData = ByteView.ofMemory final.memory offset length := by
  unfold Frame.haltWithData at h
  split at h
  next =>
    dsimp only at h
    split at h
    · cases h
      rfl
    · contradiction
  next => contradiction

#print axioms ByteView.readByte_inside
#print axioms ByteView.readByte_outside
#print axioms ByteView.readByte_ofArray
#print axioms ByteView.readByte_ofMemory_inside
#print axioms Memory.readByte_expandedCopy_inside
#print axioms commit_keeps_return_data
#print axioms step_returnDataCopy_readByte
#print axioms Frame.haltWithData_output

end EVMCleanroom
