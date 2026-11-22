import EVMCleanroom.Call

/-!
# Real nonzero-value CALL into an existing or newly credited account

This is a *separately fork-scoped* extension of the executable EVM 0xf1
path, not a replacement for the zero-value scheduler. Matches EELS Prague:
- EIP-2929 account access charge (2600 cold / 100 warm);
- 9000 nonzero-value transfer surcharge;
- EIP-161 25000 surcharge when transferring to a not-alive account;
- EIP-150 63/64 cap after those charges;
- 2300 value stipend supplied to the child ABOVE the charged forwarding;
- value transferred at child entry and reverted on failed child frame;
- parent retains unused child gas, even if child REVERTs.

For this slice, the child may execute Frame.run's existing supported opcodes
and storage changes. CALLVALUE/CALLER/ADDRESS in the child, calldata/returndata,
precompiles, and nested calls are handled by later extensions. An unimplemented
path yields an explicit non-consensus 'indeterminate' result.

This module is NOT equivalent to all of EELS CALL by itself. Theorems prove
the exact executable budget arithmetic, and independent EthereumJS differential
tests challenge the parent bytecode path against a real second EVM.
-/

namespace EVMCleanroom.CallValue

open EVMCleanroom
open EVMCleanroom.World

def valueSurcharge : Nat := 9000
def newAccountSurcharge : Nat := 25000
def stipend : Nat := 2300

/-- An account's liveness for the post-EIP-161 CALL new-account surcharge.
    This restricted world models nonce, balance and code; an empty account is
    (nonce=0, balance=0, empty code). -/
def accountAlive (a : Account) : Bool :=
  a.nonce != 0 || a.balance != 0 || a.code.size != 0

def extraCharge (wasWarm isAlive : Bool) : Nat :=
  CallGas.accessCharge wasWarm + valueSurcharge +
    (if isAlive then 0 else newAccountSurcharge)

structure Budget where
  extraCharge : Nat
  forwarded : Nat
  childGas : Nat
  reserve : Nat
  deriving Repr, DecidableEq

/-- The caller is charged only the forwarded gas, not the extra 2300 stipend.
    A child receives the stipend in addition to that forwarded gas. -/
def schedule (available requested : Nat) (wasWarm isAlive : Bool) :
    Except Error Budget :=
  let extra := extraCharge wasWarm isAlive
  if extra ≤ available then
    let remaining := available - extra
    let forwarded := min requested (CallGas.maxForwarded remaining)
    .ok ⟨extra, forwarded, forwarded + stipend, remaining - forwarded⟩
  else .error .outOfGas

/-- No GAS is created in the charged portion of the CALL budget; the
    stipend is tracked explicitly as a distinct child allowance. -/
theorem schedule_charge_exact {available requested : Nat}
    {wasWarm isAlive : Bool} {b : Budget}
    (h : schedule available requested wasWarm isAlive = .ok b) :
    b.reserve + b.forwarded + b.extraCharge = available := by
  dsimp [schedule] at h
  split at h
  · cases h
    dsimp
    have hcap : min requested
        (CallGas.maxForwarded (available - extraCharge wasWarm isAlive)) ≤
        available - extraCharge wasWarm isAlive :=
      Nat.le_trans (Nat.min_le_right _ _) (CallGas.maxForwarded_bounded _)
    omega
  · cases h

theorem schedule_child_stipend {available requested : Nat}
    {wasWarm isAlive : Bool} {b : Budget}
    (h : schedule available requested wasWarm isAlive = .ok b) :
    b.childGas = b.forwarded + stipend := by
  dsimp [schedule] at h
  split at h
  · cases h
    rfl
  · cases h

/-- Parent gas conservation with the stipend explicitly included on the
    right; child gas may be returned even after parent paid no stipend. -/
theorem schedule_resume_exact {available requested : Nat}
    {wasWarm isAlive : Bool} {b : Budget}
    (h : schedule available requested wasWarm isAlive = .ok b)
    (childRemaining : Nat) (hchild : childRemaining ≤ b.childGas) :
    b.reserve + childRemaining + b.extraCharge +
      (b.childGas - childRemaining) = available + stipend := by
  have hc := schedule_charge_exact h
  have hs := schedule_child_stipend h
  omega

theorem extraCharge_covers_stipend (wasWarm isAlive : Bool) :
    stipend ≤ extraCharge wasWarm isAlive := by
  unfold extraCharge valueSurcharge stipend newAccountSurcharge CallGas.accessCharge
  split <;> split <;> omega

/-- The 2300 stipend never yields a net gain in the parent's gas balance
    because the value-transfer surcharge is larger than the stipend. -/
theorem schedule_parent_bounded {available requested : Nat}
    {wasWarm isAlive : Bool} {b : Budget}
    (h : schedule available requested wasWarm isAlive = .ok b)
    (childRemaining : Nat) (hchild : childRemaining ≤ b.childGas) :
    b.reserve + childRemaining ≤ available := by
  have hc := schedule_resume_exact h childRemaining hchild
  have he := extraCharge_covers_stipend wasWarm isAlive
  dsimp [schedule] at h
  split at h
  · cases h
    dsimp at *
    omega
  · cases h

private def budgetMatches (out : Except Error Budget)
    (extra forward child reserve : Nat) : Bool :=
  match out with
  | .ok b => b.extraCharge == extra && b.forwarded == forward &&
      b.childGas == child && b.reserve == reserve
  | _ => false

#guard extraCharge false true == 11600
#guard extraCharge true true == 9100
#guard extraCharge false false == 36600
#guard extraCharge true false == 34100
#guard budgetMatches (schedule 50000 30000 false true) 11600 30000 32300 8400
#guard budgetMatches (schedule 50000 30000 false false) 36600 13191 15491 209
#guard budgetMatches (schedule 50000 0 false true) 11600 0 2300 38400

#print axioms schedule_charge_exact
#print axioms schedule_child_stipend
#print axioms schedule_resume_exact
#print axioms extraCharge_covers_stipend
#print axioms schedule_parent_bounded

end EVMCleanroom.CallValue

namespace EVMCleanroom.WorldCall

open EVMCleanroom.World
open EVMCleanroom.CallValue

/-- CALL failure is not necessarily a REVERT: insufficient balance is a
    distinct failure outcome, with all allotted child gas returned. -/
inductive ValueOutcome where
  | childSuccess (world : TxWorld) (parentGasRemaining : Nat)
  | childReverted (world : TxWorld) (parentGasRemaining : Nat)
  | childExceptional (world : TxWorld) (parentGasRemaining : Nat) (reason : Error)
  | insufficientFunds (world : TxWorld) (parentGasRemaining : Nat)
  | callerOutOfGas
  | indeterminate (reason : Error)

/-- Real nonzero value goes into target's account before child executes.
    REVERT and exceptional child halts restore the parent's warmed checkpoint,
    including both account balances. Child failure does not halt the caller.

    This is one nested level only, with zero calldata/return length handled
    by the actual opcode dispatcher. Unlike an authorization message, the
    value transfer is not a transaction signed by the child. -/
def callWithValue (fuel : Nat) (w : TxWorld)
    (caller target parentGas requestedGas value : Nat) : ValueOutcome :=
  if caller ≥ addressBound || target ≥ addressBound || value = 0 then
    .indeterminate .unsupportedFork
  else
    match CallValue.schedule parentGas requestedGas
      (w.warmAddresses target) (CallValue.accountAlive (w.accounts target)) with
    | .error .outOfGas => .callerOutOfGas
    | .error e => .indeterminate e
    | .ok b =>
      let warmed := warmTarget w target
      match World.pay warmed caller target value with
      | .error .insufficientBalance =>
        .insufficientFunds warmed (b.reserve + b.childGas)
      | .error _ => .indeterminate .unsupportedFork
      | .ok transferred =>
        -- This *actual child execution state* receives the sent wei amount.
        -- World.frameInput reads its SELF balance after the checked transfer.
        -- The general standalone Frame.run path still has callValue=0.
        let child : State :=
          { World.frameInput transferred target b.childGas with callValue := value }
        match Frame.run fuel child with
        | .stopped out =>
          if out.gas ≤ b.childGas then
            .childSuccess (World.commitFrame transferred target out)
              (b.reserve + out.gas)
          else .indeterminate .unsupportedFork
        | .returned out _ _ =>
          if out.gas ≤ b.childGas then
            .childSuccess (World.commitFrame transferred target out)
              (b.reserve + out.gas)
          else .indeterminate .unsupportedFork
        | .reverted out _ _ =>
          if out.gas ≤ b.childGas then
            .childReverted warmed (b.reserve + out.gas)
          else .indeterminate .unsupportedFork
        | .exceptional out reason =>
          if out.gas ≤ b.childGas then
            .childExceptional warmed (b.reserve + out.gas) reason
          else .indeterminate .unsupportedFork
        | .unsupported e => .indeterminate e

/-- Child account liveness depends on nonce, code or balance only. -/
theorem accountAlive_funded (a : Account) (h : (a.balance != 0) = true) :
    CallValue.accountAlive a = true := by
  simp [CallValue.accountAlive, h]

/-- The refund/storage snapshot cannot be affected just by warming the
    value-transfer target in the parent CALL scope. -/
theorem warmTarget_value_refund (w : TxWorld) (target : Nat) :
    (warmTarget w target).refund = w.refund := rfl

#print axioms accountAlive_funded
#print axioms warmTarget_value_refund

end EVMCleanroom.WorldCall
