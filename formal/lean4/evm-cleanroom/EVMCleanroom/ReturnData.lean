import EVMCleanroom.Proofs

/-!
# EIP-211 return-data buffer and RETURNDATACOPY (0x3e)

The return-data buffer belongs to a parent frame, is set by its most recent
CALL and is overwritten by subsequent CALLs. This module implements the
RETURNDATACOPY substep for an existing parent State, independent of CALL
dispatch. It charges 3 + 3*ceil(length/32) plus EVM memory expansion.
Source-offset bounds are checked *even for zero-length copies*. Memory
offsets do not expand memory if length is zero.

For now the caller's return-data buffer is explicitly bounded to 4096 bytes.
An oversized child output must be classified UNSUPPORTED rather than
incorrectly returned, truncated, or mistaken for a protocol error.
-/

namespace EVMCleanroom.ReturnData

def maxObservedBytes : Nat := 4096

/-- Materialize the exact child's return-data bytes, or explicitly refuse
    the current implementation's bounded observation limit. -/
def capture (s : State) (offset length : Nat) : Option (Array UInt8) :=
  if length ≤ maxObservedBytes then
    some ((List.range length).map (fun i => s.memory.readByte (offset + i))).toArray
  else none

/-- The EIP-211 bound is on the return-data SOURCE, not on EVM memory.
    Offset exactly equal to size is allowed only if length is zero. -/
def sourceInBounds (size offset length : Nat) : Bool :=
  decide (offset + length ≤ size)

/-- Plan copying bytes to memory, without mutating state before a gas check. -/
def planCopy (s : State) (buffer : Array UInt8) : Except Error Plan :=
  match s.stack.items with
  | dest :: source :: length :: rest =>
    if !sourceInBounds buffer.size source.val length.val then
      .error (.invalidOpcode 0x3e) -- superseded by specific error in Core
    else
      let words := MemoryGas.requestedWords dest.val length.val
      let expanded := s.memory.expand words
      let written := (List.range length.val).foldl (fun mem i =>
        mem.writeByte (dest.val + i) (buffer.getD (source.val + i) 0)) expanded
      let copyWords := (length.val + 31) / 32
      let charge := 3 + 3 * copyWords +
        MemoryGas.expansion s.memory.words words
      .ok ⟨s.pc + 1, rest, charge, false, some written, none⟩
  | _ => .error .stackUnderflow

def copy (s : State) (buffer : Array UInt8) : Except Error State :=
  match planCopy s buffer with
  | .error e => .error e
  | .ok p => commit s p.nextPC p.stack p.gasCost p.halt
      p.nextMemory p.nextStorage

/-- The observable executable copy cannot invent gas: each accepted
    copy has an exact plan and the sum is the starting gas. -/
theorem copy_has_exact_bill {s out : State} {buffer : Array UInt8}
    (h : copy s buffer = .ok out) :
    ∃ p : Plan, planCopy s buffer = .ok p ∧
      out.gas + p.gasCost = s.gas := by
  cases hp : planCopy s buffer with
  | error e => simp [copy, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt
        p.nextMemory p.nextStorage = .ok out := by
      simpa [copy, hp] using h
    exact ⟨p, rfl, commit_gas_exact hc⟩

/-- RETURN data copies never mutate transaction-original storage. -/
theorem copy_original_unchanged {s out : State} {buffer : Array UInt8}
    (h : copy s buffer = .ok out) (key : Nat) :
    out.storage.original key = s.storage.original key := by
  cases hp : planCopy s buffer with
  | error e => simp [copy, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt
        p.nextMemory p.nextStorage = .ok out := by
      simpa [copy, hp] using h
    exact commit_original_unchanged hc key

#print axioms copy_has_exact_bill
#print axioms copy_original_unchanged

end EVMCleanroom.ReturnData
