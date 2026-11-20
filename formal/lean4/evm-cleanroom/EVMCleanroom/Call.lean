import EVMCleanroom.CallGas
import EVMCleanroom.Value

/-!
# First transaction-journalled zero-value child-call slice

An explicit parent-to-child *API*, not an implementation of opcode 0xF1.
The caller supplies its remaining gas and the requested forward amount.
CallGas.schedule applies Cancun/Prague's EIP-2929 account access price and
EIP-150 cap, reserving the unforwarded remainder for the caller.

The address is marked warm *before* entering the child checkpoint.
If the child reverts or exceptionally halts, World.runAt restores its account
storage, storage warmth and refunds. The pre-call address warm-up survives
because it belongs to the parent scope, not the child.

This first slice accepts only zero-value calls. It does not implement EVM
CALL stack mutation, calldata, returndata, gas stipend, new-account costs,
cross-contract nested calls, precompiles, depth restriction or value transfer.
The contract is executed by real Frame.run code, which can still explicitly
return unsupported for unimplemented instructions.
-/

namespace EVMCleanroom.WorldCall

open EVMCleanroom.World

/-- EIP-2929 address warming is transaction-scoped but checkpointed. -/
def warmTarget (w : TxWorld) (target : Nat) : TxWorld :=
  { w with warmAddresses := fun a => if a = target then true else w.warmAddresses a }

/-- These results describe what a caller's CALL instruction can observe.
    Child REVERT/exception returns failure, without exceptionally halting
    the caller. Parent out-of-gas at the access cost is different. -/
inductive Outcome where
  | childSuccess (world : TxWorld) (parentGasRemaining : Nat)
  | childReverted (world : TxWorld) (parentGasRemaining : Nat)
  | childExceptional (world : TxWorld) (parentGasRemaining : Nat) (reason : Error)
  | callerOutOfGas
  | invalidAddress
  | invalidChildGas
  | unsupported (reason : Error)

/-- A single zero-value call to the target's code. All unused forwarded
    gas is returned after STOP, RETURN or REVERT, not exceptional halt. -/
def callZeroValue (fuel : Nat) (w : TxWorld)
    (target parentGas requestedGas : Nat) : Outcome :=
  if target ≥ addressBound then .invalidAddress
  else
    match CallGas.schedule parentGas requestedGas (w.warmAddresses target) with
    | .error .outOfGas => .callerOutOfGas
    | .error e => .unsupported e
    | .ok b =>
      let warmed := warmTarget w target
      match runAt fuel warmed target b.forwarded with
      | .stopped out remaining =>
        if remaining ≤ b.forwarded then
          .childSuccess out (b.reserve + remaining)
        else .invalidChildGas
      | .returned out remaining _ _ =>
        if remaining ≤ b.forwarded then
          .childSuccess out (b.reserve + remaining)
        else .invalidChildGas
      | .reverted out remaining _ _ =>
        if remaining ≤ b.forwarded then
          .childReverted out (b.reserve + remaining)
        else .invalidChildGas
      | .exceptional out remaining reason =>
        if remaining ≤ b.forwarded then
          .childExceptional out (b.reserve + remaining) reason
        else .invalidChildGas
      | .unsupported e => .unsupported e

/-- Entering a call cannot itself change accounts (including balance/code),
    storage, refunds or the transaction-original storage snapshot. -/
theorem warmTarget_accounts (w : TxWorld) (target other : Nat) :
    (warmTarget w target).accounts other = w.accounts other := rfl

theorem warmTarget_original (w : TxWorld) (target addr slot : Nat) :
    (warmTarget w target).original addr slot = w.original addr slot := rfl

theorem warmTarget_refund (w : TxWorld) (target : Nat) :
    (warmTarget w target).refund = w.refund := rfl

theorem warmTarget_slotWarmth (w : TxWorld) (target addr slot : Nat) :
    (warmTarget w target).warmSlots addr slot = w.warmSlots addr slot := rfl

/-- A failed child scope must not make its address cold again: address
    warming occurs before the checkpoint and stays in the parent world. -/
theorem warmTarget_own (w : TxWorld) (target : Nat) :
    (warmTarget w target).warmAddresses target = true := by
  simp [warmTarget]

theorem warmTarget_other (w : TxWorld) (target other : Nat)
    (hne : other ≠ target) :
    (warmTarget w target).warmAddresses other = w.warmAddresses other := by
  simp [warmTarget, hne]

#print axioms warmTarget_accounts
#print axioms warmTarget_original
#print axioms warmTarget_refund
#print axioms warmTarget_slotWarmth
#print axioms warmTarget_own
#print axioms warmTarget_other

end EVMCleanroom.WorldCall
