/-!
# EIP-1559 London header fee and gas-limit admission

Independent Lean 4 arithmetic. This module checks the London transition
separately from later London-family blocks; it does not authenticate the
parent header, choose the canonical head, or validate a whole block.
The 64-bit gas and 256-bit fee caps are explicit local admission limits.
-/

namespace EVMCleanroom.HeaderFees

def initialBaseFee : Nat := 1000000000
def elasticity : Nat := 2
def denominator : Nat := 8
def gasLimitDivisor : Nat := 1024
def minGasLimit : Nat := 5000
def maxGasValue : Nat := 2 ^ 64
def maxFeeValue : Nat := 2 ^ 256

structure Input where
  firstLondon : Bool
  parentGasLimit : Nat
  parentGasUsed : Nat
  parentBaseFee : Option Nat
  childGasLimit : Nat
  childGasUsed : Nat
  childBaseFee : Nat
  deriving Repr

inductive Error where
  | resourceLimit
  | parentGasOverLimit
  | childGasOverLimit
  | invalidGasLimit
  | unexpectedParentFee
  | missingParentFee
  | incorrectBaseFee
  deriving Repr, DecidableEq, BEq

def comparisonParentLimit (p : Input) : Nat :=
  if p.firstLondon then p.parentGasLimit * elasticity else p.parentGasLimit

/-- EIP-1559 permits a STRICT change smaller than 1/1024 of the
    comparison parent limit; London activation doubles that limit. -/
def gasLimitValid (p : Input) : Bool :=
  let reference := comparisonParentLimit p
  let bound := reference / gasLimitDivisor
  p.parentGasLimit >= minGasLimit &&
  p.childGasLimit >= minGasLimit &&
  p.childGasLimit < reference + bound &&
  p.childGasLimit > reference - bound

/-- Admission is distinct from the base-fee recurrence, so malformed
    witnesses cannot produce an accepted numeric fee. -/
def checkInputs (p : Input) : Except Error Unit :=
  if p.parentGasLimit >= maxGasValue || p.childGasLimit >= maxGasValue ||
      p.parentGasUsed >= maxGasValue || p.childGasUsed >= maxGasValue ||
      p.childBaseFee >= maxFeeValue ||
      p.parentBaseFee.any (fun v => v >= maxFeeValue) then
    .error .resourceLimit
  else if p.parentGasUsed > p.parentGasLimit then
    .error .parentGasOverLimit
  else if p.childGasUsed > p.childGasLimit then
    .error .childGasOverLimit
  else if !gasLimitValid p then
    .error .invalidGasLimit
  else .ok ()

/-- The two DIV operations must remain separate. Above target,
    even a sub-wei quotient increases by one wei. -/
def nextBaseFee (parentLimit parentUsed parentFee : Nat) : Nat :=
  let target := parentLimit / elasticity
  if parentUsed == target then parentFee
  else if parentUsed > target then
    parentFee + max 1 ((parentFee * (parentUsed - target) / target) / denominator)
  else
    parentFee - ((parentFee * (target - parentUsed) / target) / denominator)

/-- A missing parent fee is never interpreted as zero. An activation
    block has no London parent fee and uses the initial fee instead. -/
def expectedBaseFee (p : Input) : Except Error Nat :=
  match checkInputs p with
  | .error e => .error e
  | .ok _ =>
    if p.firstLondon then
      if p.parentBaseFee.isSome then .error .unexpectedParentFee
      else .ok initialBaseFee
    else
      match p.parentBaseFee with
      | none => .error .missingParentFee
      | some parentFee => .ok (nextBaseFee p.parentGasLimit p.parentGasUsed parentFee)

/-- Compare an actual supplied header base fee to the independently
    calculated value; never report a malformed header as accepted. -/
def checkHeader (p : Input) : Except Error Nat :=
  match expectedBaseFee p with
  | .error e => .error e
  | .ok expected =>
    if p.childBaseFee == expected then .ok expected
    else .error .incorrectBaseFee

/-- Says: a valid parent at its gas target leaves the recurrence unchanged.
    Does not say: the caller supplied a canonical parent block. -/
theorem nextBaseFee_at_target (limit fee : Nat) :
    nextBaseFee limit (limit / elasticity) fee = fee := by
  simp [nextBaseFee]

/-- Says: the above-target recurrence cannot lower the base fee.
    Does not say: a supplied parent gas used value has been authenticated. -/
theorem nextBaseFee_above (limit used fee : Nat)
    (h : limit / elasticity < used) :
    fee ≤ nextBaseFee limit used fee := by
  simp [nextBaseFee, Nat.ne_of_gt h, h]
  
/-- Says: the below-target recurrence cannot raise the base fee.
    Does not say: a supplied parent header has passed other validation. -/
theorem nextBaseFee_below (limit used fee : Nat)
    (h : used < limit / elasticity) :
    nextBaseFee limit used fee ≤ fee := by
  simp [nextBaseFee, Nat.ne_of_lt h, Nat.not_lt.mpr (Nat.le_of_lt h)]

/-- Says: any accepted first-London fee is exactly the initial value.
    Does not say: the London activation height or parent root was checked. -/
theorem expected_firstLondon {p : Input} {fee : Nat}
    (hfirst : p.firstLondon = true)
    (h : expectedBaseFee p = .ok fee) : fee = initialBaseFee := by
  unfold expectedBaseFee at h
  cases hc : checkInputs p with
  | error e => simp [hc] at h
  | ok u =>
    simp [hc, hfirst] at h
    split at h <;> simp_all

/-- Says: acceptance proves equality with the actual computed header fee.
    Does not say: this result validates receipts, trie roots, or consensus. -/
theorem checkHeader_sound {p : Input} {fee : Nat}
    (h : checkHeader p = .ok fee) :
    expectedBaseFee p = .ok fee ∧ p.childBaseFee = fee := by
  unfold checkHeader at h
  cases hc : expectedBaseFee p with
  | error e => simp [hc] at h
  | ok value =>
    simp [hc] at h
    split at h <;> simp_all

/-- Says: post-London without a parent fee can never pass admission.
    Does not say: checking a present fee authenticates its source. -/
theorem missing_parent_refused (p : Input)
    (hfirst : p.firstLondon = false)
    (hparent : p.parentBaseFee = none) :
    ∀ fee, expectedBaseFee p ≠ .ok fee := by
  intro fee
  unfold expectedBaseFee
  cases hc : checkInputs p with
  | error e => simp [hc]
  | ok u => simp [hc, hfirst, hparent]

def neutral : Input :=
  { firstLondon := false, parentGasLimit := 30000000,
    parentGasUsed := 15000000, parentBaseFee := some 1000000000,
    childGasLimit := 30000000, childGasUsed := 1,
    childBaseFee := 1000000000 }

#guard expectedBaseFee neutral == .ok 1000000000
#guard checkHeader neutral == .ok 1000000000
#guard expectedBaseFee { neutral with parentGasUsed := 30000000 } == .ok 1125000000
#guard expectedBaseFee { neutral with parentGasUsed := 0 } == .ok 875000000
#guard expectedBaseFee { neutral with parentGasUsed := 15000001, parentBaseFee := some 1 } == .ok 2
#guard expectedBaseFee { neutral with parentBaseFee := none } == .error .missingParentFee
#guard checkHeader { neutral with childBaseFee := 9 } == .error .incorrectBaseFee
#guard checkHeader { neutral with childGasUsed := 30000001 } == .error .childGasOverLimit
#guard checkHeader { neutral with parentGasUsed := 30000001 } == .error .parentGasOverLimit
#guard checkHeader { neutral with childGasLimit := 30029296 } == .error .invalidGasLimit
#guard checkHeader { neutral with childGasLimit := 29970704 } == .error .invalidGasLimit
#guard checkHeader { neutral with firstLondon := true, parentGasLimit := 15000000,
  parentGasUsed := 14000000, parentBaseFee := none } == .ok 1000000000
#guard checkHeader { neutral with firstLondon := true, parentBaseFee := some 1000000000 } ==
  .error .unexpectedParentFee

#print axioms nextBaseFee_at_target
#print axioms nextBaseFee_above
#print axioms nextBaseFee_below
#print axioms expected_firstLondon
#print axioms checkHeader_sound
#print axioms missing_parent_refused

end EVMCleanroom.HeaderFees
