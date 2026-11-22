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
  | .framePolicyViolation _ => .unsupported e
  | .stepLimit => .unsupported e
  | .invalidOpcode byte =>
    if byte == 0xfe then .exceptional e
    else .unsupported e
  | _ => .exceptional e

/-- Execute RETURN or REVERT: memory expansion is charged before the
    instruction is committed. No return-byte buffer is allocated here. -/
def haltWithData (s : State) : Except Error (State × Nat × Nat) :=
  match s.stack.items with
  | offset :: length :: rest =>
    let needed := MemoryGas.requestedWords offset.val length.val
    let expanded := s.memory.expand needed
    let gasCost := MemoryGas.expansion s.memory.words needed
    match commit s (s.pc + 1) rest gasCost true (some expanded) with
    | .ok final =>
      .ok ({ final with outputData := ByteView.ofMemory final.memory offset.val length.val },
        offset.val, length.val)
    | .error e => .error e
  | _ => .error .stackUnderflow

/-- Admission predicate for the current frame and its fetched opcode. -/
abbrev OpcodePolicy := State → Nat → Bool

/-- Execute at most fuel instructions. The policy checks the current opcode
    before either frame or core instruction handling. -/
@[specialize] def executeWithPolicy (permits : OpcodePolicy) : Nat → State → RawOutcome
  | 0, _ => .unsupported .stepLimit
  | fuel + 1, s =>
    if s.halted then .stopped s
    else
      let opcode := byteAt s s.pc
      if !permits s opcode then .unsupported (.framePolicyViolation opcode)
      else if opcode == 0xf3 then
        match haltWithData s with
        | .ok (out, offset, length) => .returned out offset length
        | .error e => errorOutcome e
      else if opcode == 0xfd then
        match haltWithData s with
        | .ok (out, offset, length) => .reverted out offset length
        | .error e => errorOutcome e
      else
        match step s with
        | .error e => errorOutcome e
        | .ok next =>
          if next.halted then .stopped next
          else executeWithPolicy permits fuel next

/-- Original frame runner, admitting all opcodes for the interpreter to decide. -/
def execute : Nat → State → RawOutcome :=
  executeWithPolicy (fun _ _ => true)

/-- Context-free instructions plus CALLVALUE in an explicit zero-value,
    read-only frame. Jump decoding still uses the entire runtime bytes. -/
def zeroValueContextFree (s : State) (opcode : Nat) : Bool :=
  s.readOnly && s.callValue == 0 &&
    (match opcode with
    | 0x00 | 0x01 | 0x02 | 0x03 | 0x04 | 0x08 | 0x09
    | 0x10 | 0x11 | 0x12 | 0x14 | 0x15 | 0x16 | 0x17 | 0x18 | 0x19 | 0x1a | 0x1b | 0x1c
    | 0x34 | 0x35 | 0x36 | 0x37 | 0x38 | 0x39 | 0x3d | 0x3e
    | 0x50 | 0x51 | 0x52 | 0x53
    | 0x56 | 0x57 | 0x58 | 0x59 | 0x5b | 0xf3 | 0xfd => true
    | _ => decide (0x5f ≤ opcode ∧ opcode ≤ 0x9f))

/-- Revert all effects that belong to this frame's storage checkpoint.
    Preserve the terminal memory for reading REVERT's return payload. -/
def restore (initial terminal : State) : State :=
  { terminal with storage := initial.storage }

private def settle (initial : State) : RawOutcome → Outcome
  | .stopped out => .stopped out
  | .returned out offset length => .returned out offset length
  | .reverted out offset length =>
      .reverted (restore initial out) offset length
  | .exceptional e =>
      .exceptional { initial with gas := 0, halted := true } e
  | .unsupported e => .unsupported e

/-- Run an instruction-admitted frame with the usual storage checkpoint. -/
def runWithPolicy (permits : OpcodePolicy) (fuel : Nat) (initial : State) : Outcome :=
  settle initial (executeWithPolicy permits fuel initial)

/-- Observable single-frame outcome after the storage checkpoint is settled.
    Exceptional halts consume the frame gas. Unsupported execution yields
    no authoritative protocol result and must not be classified as invalid. -/
def run (fuel : Nat) (initial : State) : Outcome :=
  settle initial (execute fuel initial)

private def RawOutcome.conclusive : RawOutcome → Prop
  | .unsupported _ => False
  | _ => True

/-- A status for which the interpreter reached an EVM outcome. -/
def Outcome.conclusive : Outcome → Prop
  | .unsupported _ => False
  | _ => True

/-- Kind: instruction-admission boundary.
    Says: a rejected instruction at the current PC causes an explicit refusal
    before either frame or core dispatch.
    Does not say: the opcode is invalid on Ethereum. -/
theorem executeWithPolicy_refuses (permits : OpcodePolicy) (fuel : Nat) (s : State)
    (hRunning : s.halted = false) (hRejected : permits s (byteAt s s.pc) = false) :
    executeWithPolicy permits (fuel + 1) s = .unsupported (.framePolicyViolation (byteAt s s.pc)) := by
  simp [executeWithPolicy, hRunning, hRejected]

/-- Kind: refinement helper.
    Says: conclusive raw outcomes agree with unrestricted execution.
    Does not say: an unrestricted opcode satisfies the caller's policy. -/
private theorem executeWithPolicy_refines (permits : OpcodePolicy) (fuel : Nat) (s : State)
    (h : (executeWithPolicy permits fuel s).conclusive) :
    executeWithPolicy permits fuel s = execute fuel s := by
  induction fuel generalizing s with
  | zero => simp [executeWithPolicy, RawOutcome.conclusive] at h
  | succ fuel ih =>
    by_cases hHalted : s.halted = true
    · simp [execute, executeWithPolicy, hHalted]
    · by_cases hPermits : permits s (byteAt s s.pc) = true
      · simp only [execute, executeWithPolicy, hHalted, hPermits, Bool.not_true,
          Bool.false_eq_true, if_false] at h ⊢
        split
        · rfl
        next hReturn =>
          split
          · rfl
          next hRevert =>
            split
            · rfl
            next next hStep =>
              split
              · rfl
              next hNext =>
                exact ih next (by
                  simpa only [hReturn, hRevert, hStep, hNext, Bool.false_eq_true, if_false] using h)
      · have hRejected : permits s (byteAt s s.pc) = false := Bool.eq_false_iff.mpr hPermits
        simp [executeWithPolicy, hHalted, hRejected, RawOutcome.conclusive] at h

/-- Kind: refinement.
    Says: any conclusive outcome from an opcode-guarded frame equals unrestricted
    execution from the same state, with the same fuel, memory and checkpoint.
    Does not say: the unrestricted frame implements every Ethereum opcode. -/
theorem runWithPolicy_refines (permits : OpcodePolicy) (fuel : Nat) (initial : State)
    (h : (runWithPolicy permits fuel initial).conclusive) :
    runWithPolicy permits fuel initial = run fuel initial := by
  have hRaw : (executeWithPolicy permits fuel initial).conclusive := by
    cases hRaw : executeWithPolicy permits fuel initial <;>
      simp [runWithPolicy, hRaw, settle, Outcome.conclusive, RawOutcome.conclusive] at h ⊢
  unfold runWithPolicy run
  rw [executeWithPolicy_refines permits fuel initial hRaw]

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
  | stopped state => simp [run, settle, he] at h
  | returned state off len => simp [run, settle, he] at h
  | reverted state off len =>
    have hh : Outcome.reverted (restore initial state) off len =
        Outcome.reverted final offset length := by
      simpa [run, settle, he] using h
    injection hh with hs _ _
    subst final
    exact ⟨rfl, rfl, rfl, rfl⟩
  | exceptional e => simp [run, settle, he] at h
  | unsupported e => simp [run, settle, he] at h

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
  | stopped state => simp [run, settle, he] at h
  | returned state off len => simp [run, settle, he] at h
  | reverted state off len => simp [run, settle, he] at h
  | exceptional e =>
    have hh : Outcome.exceptional { initial with gas := 0, halted := true } e =
        Outcome.exceptional final reason := by
      simpa [run, settle, he] using h
    injection hh with hs _
    subst final
    exact ⟨rfl, rfl, rfl⟩
  | unsupported e => simp [run, settle, he] at h

#print axioms restore_current
#print axioms restore_original
#print axioms restore_warmth
#print axioms restore_refund
#print axioms run_revert_atomic
#print axioms run_exception_atomic
#print axioms executeWithPolicy_refuses
#print axioms runWithPolicy_refines

end EVMCleanroom.Frame
