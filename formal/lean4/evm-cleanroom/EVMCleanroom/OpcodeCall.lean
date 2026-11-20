import EVMCleanroom.Call

/-!
# First actual bytecode-driven CALL opcode (0xf1) in Lean

A separate depth-1 parent EVM driver that dispatches CALL from *bytecode*.
It executes the existing Core opcode subset plus CALL, uses WorldCall's
EIP-150/EIP-2929 zero-value scheduler, and resumes the real parent stack.

Supported CALL shape: value=0; all calldata/output offsets and lengths=0;
target is a non-precompile (<160-bit) address distinct from the parent;
child executes the existing Frame.run subset and cannot itself CALL.
RETURN/REVERT in the *parent* are not yet dispatched (parent STOP is).
The parent frame is journalled: an exceptional parent outcome rolls back
all intermediate child and parent changes to its entry world. Exceptional
children instead return CALL=0 and do not halt the parent.

No general Solidity contract validity, nested depth, value/gas stipends,
precompile calls, memory copying, returndata, logs or trie roots is claimed.
EIP-150 budgeting is proved separately by CallGas.schedule_conserves and
CallGas.resumed_gas_exact. This file does not prove independent EELS
semantic refinement; compare actual execution to a pinned other client.
-/

namespace EVMCleanroom.OpcodeCall

open EVMCleanroom.World

inductive Advance where
  | ok (world : TxWorld) (parent : State)
  | exceptional (reason : Error)
  | unsupported (why : String)

/-- Commit the gas deducted by the child/target access, then push the
    actual EVM CALL success word and advance PC past opcode 0xf1.
    Child storage is in the world; this parent has a distinct address. -/
private def resumeParent (world : TxWorld) (parentAddress : Nat)
    (s : State) (rest : List Word) (remaining flag : Nat) : Advance :=
  if remaining > s.gas then .unsupported "child-returned-more-than-parent-gas"
  else
    match commit s (s.pc + 1) (word flag :: rest) (s.gas - remaining) with
    | .error e => .exceptional e
    | .ok next =>
      .ok (commitFrame world parentAddress next) next

/-- The seven stack operands are (top first): gas, address, value,
    calldata offset, calldata length, return offset, return length.
    This is a genuine CALL dispatch rather than a preconstructed API call. -/
private def stepCall (working : TxWorld) (parentAddress childFuel : Nat)
    (s : State) : Advance :=
  match s.stack.items with
  | gas :: target :: value :: inOffset :: inLength :: outOffset :: outLength :: rest =>
    if value.val != 0 || inOffset.val != 0 || inLength.val != 0 ||
       outOffset.val != 0 || outLength.val != 0 then
      .unsupported "nonzero-value-or-calldata-or-output"
    else if target.val < 10 || target.val = parentAddress ||
            target.val ≥ addressBound then
      .unsupported "precompile-selfcall-or-out-of-range-address"
    else
      match WorldCall.callZeroValue childFuel working
            target.val s.gas gas.val with
      | .childSuccess out remaining =>
        resumeParent out parentAddress s rest remaining 1
      | .childReverted out remaining =>
        resumeParent out parentAddress s rest remaining 0
      | .childExceptional out remaining _ =>
        resumeParent out parentAddress s rest remaining 0
      | .callerOutOfGas => .exceptional .outOfGas
      | .invalidAddress => .unsupported "invalid-address"
      | .invalidChildGas => .unsupported "untrusted-child-gas"
      | .unsupported _ => .unsupported "unimplemented-child-instruction"
  | _ => .exceptional .stackUnderflow

inductive Outcome where
  | stopped (world : TxWorld) (parent : State)
  | exceptional (world : TxWorld) (reason : Error)
  | unsupported (reason : String)

/-- The complete working-world snapshot is discarded if the parent
    exceptionally halts. Child failure alone does not trigger this. -/
def drive (entry : TxWorld) (parentAddress childFuel : Nat) :
    Nat → TxWorld → State → Outcome
  | 0, _, _ => .unsupported "parent-simulation-fuel-exhausted"
  | fuel + 1, working, s =>
    if s.halted then .stopped working s
    else
      let operation : Advance :=
        if byteAt s s.pc == 0xf1 then
          stepCall working parentAddress childFuel s
        else
          match step s with
          | .ok next =>
            .ok (commitFrame working parentAddress next) next
          | .error e =>
            .exceptional e
      match operation with
      | .ok nextWorld next =>
        if next.halted then .stopped nextWorld next
        else drive entry parentAddress childFuel fuel nextWorld next
      | .exceptional (.invalidOpcode opcode) =>
        if opcode == 0xfe then .exceptional entry (.invalidOpcode opcode)
        else .unsupported "unimplemented-parent-opcode"
      | .exceptional .unsupportedFork => .unsupported "unsupported-parent-fork"
      | .exceptional .stepLimit => .unsupported "parent-step-limit"
      | .exceptional e => .exceptional entry e
      | .unsupported why => .unsupported why

/-- The outermost executable commit barrier. Even if a future driver
    implementation accidentally exposes a partially updated world on an
    exceptional parent outcome, no such world can escape through run. -/
def settleParent (entry : TxWorld) : Outcome → Outcome
  | .exceptional _ reason => .exceptional entry reason
  | other => other

/-- A successful proof of this local property applies to *all* outcomes
    produced by the depth-1 bytecode driver, not just test examples. -/
theorem settleParent_exception_restores {entry result : TxWorld}
    {reason : Error} {out : Outcome}
    (h : settleParent entry out = .exceptional result reason) :
    result = entry := by
  cases out with
  | stopped w s => simp [settleParent] at h
  | unsupported why => simp [settleParent] at h
  | exceptional w error =>
    have hh : Outcome.exceptional entry error =
        Outcome.exceptional result reason := by
      simpa [settleParent] using h
    injection hh with hw _
    exact hw.symm

/-- Frame entry recipient is transaction-warm as required by EIP-2929.
    The target's warmth is still determined by the transaction snapshot. -/
def run (parentFuel childFuel : Nat) (world : TxWorld)
    (parentAddress parentGas : Nat) : Outcome :=
  if parentAddress ≥ addressBound || parentAddress < 10 then
    .unsupported "parent-address-is-not-a-regular-account"
  else
    let entry := WorldCall.warmTarget world parentAddress
    settleParent entry (drive entry parentAddress childFuel parentFuel entry
      (frameInput entry parentAddress parentGas))

/-- Entering the parent transaction cannot mutate any account or
    transaction-original storage simply by warming the parent address. -/
theorem entry_preserves_accounts (w : TxWorld) (parentAddress other : Nat) :
    ((WorldCall.warmTarget w parentAddress).accounts other) =
      w.accounts other := WorldCall.warmTarget_accounts w parentAddress other

theorem entry_preserves_original (w : TxWorld) (parentAddress other key : Nat) :
    ((WorldCall.warmTarget w parentAddress).original other key) =
      w.original other key := WorldCall.warmTarget_original w parentAddress other key

/-- Actual executable parent-level exceptional rollback, even after
    earlier successful child CALL(s). Applies to every address and storage
    slot for all bytecode admitted by the restricted dispatcher. -/
theorem run_exception_world_atomic (parentFuel childFuel : Nat)
    (world result : TxWorld) (parentAddress parentGas addr slot : Nat)
    (reason : Error)
    (h : run parentFuel childFuel world parentAddress parentGas =
        .exceptional result reason) :
    result.accounts addr = world.accounts addr ∧
    result.original addr slot = world.original addr slot ∧
    result.refund = world.refund := by
  unfold run at h
  by_cases hv : parentAddress ≥ addressBound || parentAddress < 10
  · simp [hv] at h
  · simp only [if_neg hv] at h
    have he : result = WorldCall.warmTarget world parentAddress :=
      settleParent_exception_restores h
    subst result
    exact ⟨WorldCall.warmTarget_accounts world parentAddress addr,
      WorldCall.warmTarget_original world parentAddress addr slot,
      WorldCall.warmTarget_refund world parentAddress⟩

#print axioms settleParent_exception_restores
#print axioms run_exception_world_atomic

#print axioms entry_preserves_accounts
#print axioms entry_preserves_original

end EVMCleanroom.OpcodeCall
