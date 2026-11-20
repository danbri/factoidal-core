import EVMCleanroom.Core

/-!
# Top-level EVM frame outcome and atomic REVERT

A scoped extension of the raw bytecode interpreter. It executes RETURN (0xf3)
and REVERT (0xfd), applying the same memory-expansion pricing as EELS Prague,
and records their offset/length without allocating output bytes before the
gas check. All other implemented opcodes go through Core.step.

A successful frame retains storage modifications. REVERT restores the
pre-frame storage snapshot (current values, transaction warmth, refund).
Exceptional halts consume the remaining frame gas and also restore the
snapshot. A finite *fuel budget* or unsupported opcode is NOT counted as an
EVM exceptional halt.

This is one frame, one account. It does NOT implement CALL/CREATE,
nested-call journals, return-data copying into callers, transaction gas
refund caps, receipt/state roots or the full world-state. Unsupported
valid opcodes are not declared to be invalid Ethereum transactions.

References: EIP-140 (REVERT), EIP-2929 (rollback of warm-access sets),
Ethereum execution-specs Prague vm/instructions/control_flow.py.
-/

namespace EVMCleanroom.Frame

inductive RawOutcome where
  | stopped (state : State)
  | returned (state : State) (offset length : Nat)
  | reverted (state : State) (offset length : Nat)
  | exceptional (reason : Error)
  | unsupported (reason : Error)

/-- After rollback, exceptional outcomes carry the restored state and zero
    remaining gas. RawOutcome keeps the pre-checkpoint result separate. -/
inductive Outcome where
  | stopped (state : State)
  | returned (state : State) (offset length : Nat)
  | reverted (state : State) (offset length : Nat)
  | exceptional (state : State) (reason : Error)
  | unsupported (reason : Error)

/-- Implementation cannot safely declare an unimplemented but valid
    instruction to be an Ethereum consensus-invalid opcode. The designated
    INVALID byte 0xfe is the only opcode treated as definitely invalid here. -/
private def errorOutcome (e : Error) : RawOutcome :=
  match e with
  | .unsupportedFork => .unsupported e
  | .stepLimit => .unsupported e
  | .invalidOpcode byte =>
    if byte == 0xfe then .exceptional e
    else .unsupported e
  | _ => .exceptional e

/-- Execute RETURN or REVERT: memory expansion is charged before the
    instruction is committed. No return-byte buffer is allocated here. -/
private def haltWithData (s : State) : Except Error (State × Nat × Nat) :=
  match s.stack.items with
  | offset :: length :: rest =>
    let needed := MemoryGas.requestedWords offset.val length.val
    let expanded := s.memory.expand needed
    let gasCost := MemoryGas.expansion s.memory.words needed
    match commit s (s.pc + 1) rest gasCost true (some expanded) with
    | .ok final => .ok (final, offset.val, length.val)
    | .error e => .error e
  | _ => .error .stackUnderflow

/-- Execute at most fuel instructions, collecting explicit halt outcomes.
    Only supported instructions may be accepted as successful execution. -/
def execute : Nat → State → RawOutcome
  | 0, _ => .unsupported .stepLimit
  | fuel + 1, s =>
    if s.halted then .stopped s
    else if byteAt s s.pc == 0xf3 then
      match haltWithData s with
      | .ok (out, offset, length) => .returned out offset length
      | .error e => errorOutcome e
    else if byteAt s s.pc == 0xfd then
      match haltWithData s with
      | .ok (out, offset, length) => .reverted out offset length
      | .error e => errorOutcome e
    else
      match step s with
      | .error e => errorOutcome e
      | .ok next =>
        if next.halted then .stopped next
        else execute fuel next

/-- Revert all effects that belong to this frame's storage checkpoint.
    Preserve the terminal memory for reading REVERT's return payload. -/
def restore (initial terminal : State) : State :=
  { terminal with storage := initial.storage }

/-- Observable single-frame outcome after the storage checkpoint is settled.
    Exceptional halts consume the frame gas. Unsupported execution yields
    no authoritative protocol result and must not be classified as invalid. -/
def run (fuel : Nat) (initial : State) : Outcome :=
  match execute fuel initial with
  | .stopped out => .stopped out
  | .returned out offset length => .returned out offset length
  | .reverted out offset length =>
      .reverted (restore initial out) offset length
  | .exceptional e =>
      .exceptional { initial with gas := 0, halted := true } e
  | .unsupported e => .unsupported e

/-- Any REVERT restores ALL keys, not just those present in a fixture. -/
theorem restore_current (initial terminal : State) (key : Nat) :
    (restore initial terminal).storage.current key =
      initial.storage.current key := rfl

theorem restore_original (initial terminal : State) (key : Nat) :
    (restore initial terminal).storage.original key =
      initial.storage.original key := rfl

theorem restore_warmth (initial terminal : State) (key : Nat) :
    (restore initial terminal).storage.warm key =
      initial.storage.warm key := rfl

theorem restore_refund (initial terminal : State) :
    (restore initial terminal).storage.refund =
      initial.storage.refund := rfl

/-- An actual interpreter REVERT is atomic for persistent storage, warm
    accesses and refunds, for arbitrary bytecode, gas and execution length. -/
theorem run_revert_atomic (fuel : Nat) (initial final : State)
    (offset length key : Nat)
    (h : run fuel initial = .reverted final offset length) :
    final.storage.current key = initial.storage.current key ∧
    final.storage.original key = initial.storage.original key ∧
    final.storage.warm key = initial.storage.warm key ∧
    final.storage.refund = initial.storage.refund := by
  cases he : execute fuel initial with
  | stopped state => simp [run, he] at h
  | returned state off len => simp [run, he] at h
  | reverted state off len =>
    have hh : Outcome.reverted (restore initial state) off len =
        Outcome.reverted final offset length := by
      simpa [run, he] using h
    injection hh with hs _ _
    subst final
    exact ⟨rfl, rfl, rfl, rfl⟩
  | exceptional e => simp [run, he] at h
  | unsupported e => simp [run, he] at h

/-- Exceptional execution has zero remaining frame gas, and cannot commit
    any frame-local persistent storage effects. This does not apply to an
    unsupported opcode or exhausted *simulation fuel*. -/
theorem run_exception_atomic (fuel : Nat) (initial final : State)
    (reason : Error) (key : Nat)
    (h : run fuel initial = .exceptional final reason) :
    final.gas = 0 ∧
    final.storage.current key = initial.storage.current key ∧
    final.storage.refund = initial.storage.refund := by
  cases he : execute fuel initial with
  | stopped state => simp [run, he] at h
  | returned state off len => simp [run, he] at h
  | reverted state off len => simp [run, he] at h
  | exceptional e =>
    have hh : Outcome.exceptional { initial with gas := 0, halted := true } e =
        Outcome.exceptional final reason := by
      simpa [run, he] using h
    injection hh with hs _
    subst final
    exact ⟨rfl, rfl, rfl⟩
  | unsupported e => simp [run, he] at h

#print axioms restore_current
#print axioms restore_original
#print axioms restore_warmth
#print axioms restore_refund
#print axioms run_revert_atomic
#print axioms run_exception_atomic

end EVMCleanroom.Frame
