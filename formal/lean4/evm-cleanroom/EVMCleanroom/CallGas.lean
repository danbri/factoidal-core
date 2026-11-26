import EVMCleanroom.Core

/-!
# Zero-value CALL gas allocation: EIP-150 and EIP-2929 (Berlin–Prague)

For a CALL to an existing account with zero value and no memory expansion,
EIP-2929 charges 2600 on first address access and 100 thereafter, *before*
calculating the EIP-150 63/64 forwarding cap. The caller retains the
unforwarded reserve. The unused portion of a child's gas is returned to
the caller, whether the child succeeds or REVERTs. An exceptional child
returns zero gas.

The pure scheduler below deliberately excludes value stipends, account
creation, memory expansion, per-fork repricings, call-depth checks, calldata,
return-data copying and CALL stack mutation. It is a reusable proved
foundation, NOT yet a CALL opcode dispatcher or semantic refinement to EELS.

Sources: EIP-150 and EIP-2929; execution-specs Prague vm/gas.py.
-/

namespace EVMCleanroom.CallGas

/-- EIP-2929 CALL account access is paid before EIP-150 forwarding. -/
def accessCharge (wasWarm : Bool) : Nat :=
  if wasWarm then 100 else 2600

/-- EIP-150: retain at least floor(available / 64) in the caller. -/
def maxForwarded (available : Nat) : Nat :=
  available - available / 64

structure Budget where
  accessCharge : Nat
  forwarded : Nat
  reserve : Nat
  deriving Repr, DecidableEq

/-- All amounts are gas units, not transaction ETH balances. -/
def schedule (available requested : Nat) (wasWarm : Bool) :
    Except Error Budget :=
  if accessCharge wasWarm ≤ available then
    let remaining := available - accessCharge wasWarm
    let forwarded := min requested (maxForwarded remaining)
    .ok ⟨accessCharge wasWarm, forwarded, remaining - forwarded⟩
  else .error .outOfGas

/-- A pure EIP-150 cap can never exceed available gas. -/
theorem maxForwarded_bounded (available : Nat) :
    maxForwarded available ≤ available := by
  unfold maxForwarded
  exact Nat.sub_le _ _

/-- No requested amount can evade the EIP-150 1/64 reserve.
    The result is stated for any gas amount (including <64). -/
theorem mandatoryReserve (available requested : Nat) :
    available / 64 ≤ available - min requested (maxForwarded available) := by
  have hcap : min requested (maxForwarded available) ≤ maxForwarded available :=
    Nat.min_le_right _ _
  unfold maxForwarded at hcap ⊢
  omega

/-- No gas is created or lost simply by constructing a CALL budget.
    Applies to EVERY successfully admitted parent gas level and request. -/
theorem schedule_conserves {available requested : Nat} {wasWarm : Bool}
    {b : Budget} (h : schedule available requested wasWarm = .ok b) :
    b.reserve + b.forwarded + b.accessCharge = available := by
  unfold schedule at h
  split at h
  · cases h
    dsimp
    have hcap : min requested (maxForwarded (available - accessCharge wasWarm)) ≤
        available - accessCharge wasWarm :=
      Nat.le_trans (Nat.min_le_right _ _)
        (maxForwarded_bounded _)
    omega
  · cases h

/-- Returning unused child gas cannot create gas. Precisely:
    returned parent gas + paid address charge + gas consumed inside child
    equals the parent's starting gas. -/
theorem resumed_gas_exact {available requested : Nat} {wasWarm : Bool}
    {b : Budget} (h : schedule available requested wasWarm = .ok b)
    (childRemaining : Nat) (hchild : childRemaining ≤ b.forwarded) :
    b.reserve + childRemaining + b.accessCharge +
        (b.forwarded - childRemaining) = available := by
  have hc := schedule_conserves h
  omega

/-- The caller cannot gain gas from any admissible child outcome. -/
theorem resumed_gas_bounded {available requested : Nat} {wasWarm : Bool}
    {b : Budget} (h : schedule available requested wasWarm = .ok b)
    (childRemaining : Nat) (hchild : childRemaining ≤ b.forwarded) :
    b.reserve + childRemaining ≤ available := by
  have hc := resumed_gas_exact h childRemaining hchild
  omega

#guard accessCharge false == 2600
#guard accessCharge true == 100
#guard maxForwarded 6400 == 6300
#guard maxForwarded 63 == 63
private def matchesBudget (out : Except Error Budget)
    (charge forwarded reserve : Nat) : Bool :=
  match out with
  | .ok b => b.accessCharge == charge &&
      b.forwarded == forwarded && b.reserve == reserve
  | .error _ => false

private def isOutOfGas (out : Except Error Budget) : Bool :=
  match out with
  | .error .outOfGas => true
  | _ => false

#guard matchesBudget (schedule 10000 10000 false) 2600 7285 115
#guard matchesBudget (schedule 10000 10000 true) 100 9746 154
#guard isOutOfGas (schedule 2599 0 false)
#guard matchesBudget (schedule 10000 500 false) 2600 500 6900

#print axioms maxForwarded_bounded
#print axioms mandatoryReserve
#print axioms schedule_conserves
#print axioms resumed_gas_exact
#print axioms resumed_gas_bounded

end EVMCleanroom.CallGas
