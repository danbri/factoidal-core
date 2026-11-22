import EVMCleanroom.Call
import EVMCleanroom.ValueCall
import EVMCleanroom.Proofs

/-!
# Actual EVM CALL instruction (0xf1): transaction-journalled execution slice

This interpreter FETCHES and executes 0xf1 from parent bytecode, POPS the seven
real EVM stack parameters, calls WorldCall.callZeroValue under the proved
EIP-150/2929 scheduler, PUSHES the EVM success bit, and continues executing
the parent machine state. Child effects are committed only if its frame
succeeds; parent REVERT or exceptional failure restores the entire parent
entry world, including any previously successful children.

Exact admitted semantics, deliberately narrow: zero or nonzero value,
input size zero, output size zero, one child frame running existing Frame.run
opcodes (no nested CALL). Nonzero value uses EIP-161 account creation costs,
9000 gas surcharge, 2300 stipend and checked balance transfers, including
rollback; no precompiles, and no parent storage opcodes yet. Arbitrary zero-sized
memory offsets are accepted without allocation. Stack addresses are truncated
to the low 160 bits. Child exceptional outcome does not halt the parent.

An unimplemented but otherwise valid opcode/parameter combination is
INDETERMINATE, never misclassified as a consensus-invalid transaction.
Execution "fuel" bounds simulation, NOT Ethereum gas.

The legacy WorldCall.callZeroValue function is retained as a reusable semantic
component, but this module exercises the real opcode in a parent program.
-/

namespace EVMCleanroom.CallOpcode

open EVMCleanroom.World

inductive CallStep where
  | committed (world : TxWorld) (parent : State)
  | exceptional (reason : Error)
  | indeterminate (reason : Error)

-- Memory expansion of zero-byte ranges is zero, regardless of their offsets;
-- all nonzero lengths are outside this first opcode slice.
/-- One actual CALL instruction with a seven-word stack and checked state commit. -/
/-- A resumed parent with the actual EVM Boolean CALL success bit.
    The charge is validated by Core.commit before committing any persistent
    world-state side effects. -/
private def finishCall (parent : State) (rest : List Word)
    (out : TxWorld) (remaining : Nat) (succeeded : Bool) : CallStep :=
  if remaining ≤ parent.gas then
    match commit parent (parent.pc + 1)
        (word (if succeeded then 1 else 0) :: rest)
        (parent.gas - remaining) with
    | .ok state =>
      .committed out
        { state with storage := { state.storage with refund := out.refund } }
    | .error e => .exceptional e
  else .indeterminate .unsupportedFork

/-- Execute an actual parent CALL instruction with EIP-150/2929 gas and,
    for positive value, EIP-161 new-account cost, 9000 transfer surcharge,
    2300 stipend, checked World.pay and child-frame rollback. -/
def callStep (fuel : Nat) (world : TxWorld)
    (parentAddress : Nat) (parent : State) : CallStep :=
  match parent.stack.items with
  | requested :: target :: value :: _inputOffset :: inputSize ::
      _outputOffset :: outputSize :: rest =>
    if inputSize.val != 0 || outputSize.val != 0 then
      .indeterminate .unsupportedFork
    else if value.val == 0 then
      match WorldCall.callZeroValue fuel world
          (target.val % addressBound) parent.gas requested.val with
      | .childSuccess childWorld remaining =>
        finishCall parent rest childWorld remaining true
      | .childReverted childWorld remaining =>
        finishCall parent rest childWorld remaining false
      | .childExceptional childWorld remaining _ =>
        finishCall parent rest childWorld remaining false
      | .callerOutOfGas => .exceptional .outOfGas
      | .invalidAddress => .indeterminate .unsupportedFork
      | .invalidChildGas => .indeterminate .unsupportedFork
      | .unsupported e => .indeterminate e
    else if parent.readOnly then .exceptional .writeProtection
    else
      match WorldCall.callWithValue fuel world parentAddress
          (target.val % addressBound) parent.gas requested.val value.val with
      | .childSuccess childWorld remaining =>
        finishCall parent rest childWorld remaining true
      | .childReverted childWorld remaining =>
        finishCall parent rest childWorld remaining false
      | .childExceptional childWorld remaining _ =>
        finishCall parent rest childWorld remaining false
      | .insufficientFunds childWorld remaining =>
        finishCall parent rest childWorld remaining false
      | .callerOutOfGas => .exceptional .outOfGas
      | .indeterminate e => .indeterminate e

/-- Intermediate outcomes retain a world on success, but not when an entire
    parent frame must revert or halt exceptionally. That choice forces the
    outer checkpoint to be used when materializing terminal results. -/
inductive RawOutcome where
  | stopped (world : TxWorld) (parent : State)
  | returned (world : TxWorld) (parent : State)
  | reverted (parent : State)
  | exceptional (reason : Error)
  | indeterminate (reason : Error)

/-- Only designated INVALID (0xfe) is classified as definitely exceptional.
    Other unknown opcodes can be valid EVM instructions absent in this slice. -/
def stepError (e : Error) : RawOutcome :=
  match e with
  | .unsupportedFork | .stepLimit => .indeterminate e
  | .invalidOpcode b =>
      if b == 0xfe then .exceptional e else .indeterminate e
  | _ => .exceptional e

/-- Execute the actual parent's instruction stream, entering a child at 0xf1.
    Parent SLOAD/SSTORE is deferred to full world-state integration to avoid
    overwriting the transaction refund delta committed by a previous child. -/
def execute : Nat → TxWorld → Nat → State → RawOutcome
  | 0, _, _, _ => .indeterminate .stepLimit
  | fuel + 1, world, parentAddress, s =>
    if s.halted then .stopped world s
    else if byteAt s s.pc == 0xf1 then
      match callStep fuel world parentAddress s with
      | .committed nextWorld nextParent =>
        execute fuel nextWorld parentAddress nextParent
      | .exceptional e => .exceptional e
      | .indeterminate e => .indeterminate e
    else if byteAt s s.pc == 0xfd || byteAt s s.pc == 0xf3 then
      match Frame.run 1 s with
      | .reverted terminal _ _ => .reverted terminal
      | .returned terminal _ _ =>
        .returned (commitFrame world parentAddress terminal) terminal
      | .exceptional _ e => .exceptional e
      | .unsupported e => .indeterminate e
      | .stopped terminal =>
        .stopped (commitFrame world parentAddress terminal) terminal
    else if byteAt s s.pc == 0x54 || byteAt s s.pc == 0x55 then
      .indeterminate .unsupportedFork
    else
      match step s with
      | .error e => stepError e
      | .ok next =>
        if next.halted then
          .stopped (commitFrame world parentAddress next) next
        else execute fuel world parentAddress next

inductive Outcome where
  | stopped (world : TxWorld) (parent : State)
  | returned (world : TxWorld) (parent : State)
  | reverted (world : TxWorld) (parent : State)
  | exceptional (world : TxWorld) (parent : State) (reason : Error)
  | indeterminate (reason : Error)

/-- The parent entry world is the checkpoint: an unsuccessful parent
    undoes even earlier CHILD frames that had committed within the parent. -/
def settle (entryWorld : TxWorld) (initialParent : State)
    (raw : RawOutcome) : Outcome :=
  match raw with
  | .stopped world s => .stopped world s
  | .returned world s => .returned world s
  | .reverted s => .reverted entryWorld s
  | .exceptional e =>
      .exceptional entryWorld
        { initialParent with gas := 0, halted := true } e
  | .indeterminate e => .indeterminate e

def run (fuel : Nat) (world : TxWorld) (parentAddress gas : Nat) : Outcome :=
  let machine := frameInput world parentAddress gas
  settle world machine (execute fuel world parentAddress machine)

/-- Proven for ALL parent bytecode, ALL worlds, ALL execution fuel: the
    successful execution of a child never survives an eventual parent REVERT.
    This theorem concerns the executable checkpoint, not independent EELS
    semantic refinement. -/
theorem settle_parent_revert_atomic (entry : TxWorld) (initial : State)
    (raw : RawOutcome) (result : TxWorld) (terminal : State)
    (h : settle entry initial raw = .reverted result terminal) :
    result = entry := by
  cases raw <;> simp [settle] at h
  case reverted _ =>
    exact h.1.symm

/-- Exceptional parent execution likewise discards earlier child commits. -/
theorem settle_parent_exception_atomic (entry : TxWorld) (initial : State)
    (raw : RawOutcome) (result : TxWorld) (terminal : State)
    (reason : Error)
    (h : settle entry initial raw = .exceptional result terminal reason) :
    result = entry := by
  cases raw <;> simp [settle] at h
  case exceptional _ =>
    exact h.1.symm

/-- This is the public EXECUTABLE run entry point (not just a constructor
    lemma): any observed parent REVERT returns the precise original
    transaction world, even after one or more successful children. -/
theorem run_parent_revert_atomic (fuel : Nat) (entry result : TxWorld)
    (parentAddress gas : Nat) (terminal : State)
    (h : run fuel entry parentAddress gas = .reverted result terminal) :
    result = entry := by
  dsimp [run] at h
  exact settle_parent_revert_atomic entry
    (frameInput entry parentAddress gas)
    (execute fuel entry parentAddress (frameInput entry parentAddress gas))
    result terminal h

/-- Any exceptional public parent outcome similarly returns the entry world,
    rather than a child-mutated world. The gas is zeroed by settle. -/
theorem run_parent_exception_atomic (fuel : Nat) (entry result : TxWorld)
    (parentAddress gas : Nat) (terminal : State) (reason : Error)
    (h : run fuel entry parentAddress gas = .exceptional result terminal reason) :
    result = entry := by
  dsimp [run] at h
  exact settle_parent_exception_atomic entry
    (frameInput entry parentAddress gas)
    (execute fuel entry parentAddress (frameInput entry parentAddress gas))
    result terminal reason h

#print axioms settle_parent_revert_atomic
#print axioms settle_parent_exception_atomic
#print axioms run_parent_revert_atomic
#print axioms run_parent_exception_atomic

end EVMCleanroom.CallOpcode
