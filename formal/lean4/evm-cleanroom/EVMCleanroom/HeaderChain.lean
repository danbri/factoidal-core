import EVMCleanroom.HeaderFees

/-! Mainnet London-family header-pair admission. The supplied parent
hash must be authenticated separately; we compare link words, not RLP
or Keccak. Earlier forks are not evaluated by this profile. -/
namespace EVMCleanroom.HeaderChain

def londonHeight : Nat := 12965000

structure Pair where
  parentNumber : Nat
  parentTimestamp : Nat
  parentHash : Nat
  parentGasLimit : Nat
  parentGasUsed : Nat
  parentBaseFee : Option Nat
  childNumber : Nat
  childTimestamp : Nat
  childParentHash : Nat
  childGasLimit : Nat
  childGasUsed : Nat
  childBaseFee : Nat
  deriving Repr

inductive Error where
  | earlierFork
  | resourceLimit
  | numberMismatch
  | timestampMismatch
  | parentHashMismatch
  | fee (reason : HeaderFees.Error)
  deriving Repr

def bounded (p : Pair) : Bool :=
  p.parentNumber < 2^64 && p.childNumber < 2^64 &&
  p.parentTimestamp < 2^64 && p.childTimestamp < 2^64 &&
  p.parentHash < 2^256 && p.childParentHash < 2^256

def feeInput (p : Pair) : HeaderFees.Input :=
  { firstLondon := p.childNumber == londonHeight
    parentGasLimit := p.parentGasLimit
    parentGasUsed := p.parentGasUsed
    parentBaseFee := p.parentBaseFee
    childGasLimit := p.childGasLimit
    childGasUsed := p.childGasUsed
    childBaseFee := p.childBaseFee }

def feeCheck (p : Pair) : Except Error Nat :=
  match HeaderFees.checkHeader (feeInput p) with
  | .error e => .error (.fee e)
  | .ok fee => .ok fee

def check (p : Pair) : Except Error Nat :=
  if !bounded p then .error .resourceLimit
  else if p.childNumber < londonHeight then .error .earlierFork
  else if p.childNumber ≠ p.parentNumber + 1 then .error .numberMismatch
  else if p.childTimestamp ≤ p.parentTimestamp then .error .timestampMismatch
  else if p.childParentHash ≠ p.parentHash then .error .parentHashMismatch
  else feeCheck p

/-- Says: the derived activation flag is true at exactly one height.
Does not say: the supplied block number is authenticated. -/
theorem activation_iff (p : Pair) :
    (feeInput p).firstLondon = true ↔ p.childNumber = londonHeight := by
  simp [feeInput]

/-- Says: the local width cap cannot yield an accepted pair.
Does not say: the caller's allocation is bounded. -/
theorem bounds_refused (p : Pair) (h : bounded p = false) :
    check p = .error .resourceLimit := by
  simp [check, h]

/-- Says: earlier mainnet blocks within the width cap are refused by
this profile. Does not say: those blocks violate Ethereum consensus. -/
theorem earlier_refused (p : Pair) (hb : bounded p = true)
    (h : p.childNumber < londonHeight) :
    check p = .error .earlierFork := by
  simp [check, hb, h]

/-- Says: acceptance enforces adjacency, time order, supplied hash-link
equality and the actual fee checker. Does not say: the supplied parent
hash is authenticated or the block is valid. -/
theorem check_sound {p : Pair} {fee : Nat} (h : check p = .ok fee) :
    bounded p = true ∧ londonHeight ≤ p.childNumber ∧
    p.childNumber = p.parentNumber + 1 ∧
    p.parentTimestamp < p.childTimestamp ∧
    p.childParentHash = p.parentHash ∧
    HeaderFees.checkHeader (feeInput p) = .ok fee := by
  by_cases hb : bounded p = true
  · by_cases hp : p.childNumber < londonHeight
    · simp [check, hb, hp] at h
    · simp [check, hb, hp] at h
      by_cases hn : p.childNumber = p.parentNumber + 1
      · by_cases ht : p.parentTimestamp < p.childTimestamp
        · by_cases hh : p.childParentHash = p.parentHash
          · have hfee : feeCheck p = .ok fee := by
              simpa [hn, Nat.not_le.mpr ht, hh] using h
            refine ⟨hb, Nat.le_of_not_gt hp, hn, ht, hh, ?_⟩
            unfold feeCheck at hfee
            cases he : HeaderFees.checkHeader (feeInput p) with
            | error e => simp [he] at hfee
            | ok v => simp [he] at hfee; simp [hfee]
          · simp [hn, Nat.not_le.mpr ht, hh] at h
        · simp [hn, Nat.le_of_not_gt ht] at h
      · simp [hn] at h
  · have hf : bounded p = false := by cases e : bounded p <;> simp_all
    simp [check, hf] at h

/-- Says: the actual inherited recurrence increases the fee by at least
one wei above target. Does not say: header input is authenticated. -/
theorem above_target_increment (limit used fee : Nat)
    (h : limit / HeaderFees.elasticity < used) :
    fee + 1 ≤ HeaderFees.nextBaseFee limit used fee := by
  simp [HeaderFees.nextBaseFee, Nat.ne_of_gt h, h] <;> omega

#print axioms activation_iff
#print axioms bounds_refused
#print axioms earlier_refused
#print axioms check_sound
#print axioms above_target_increment

end EVMCleanroom.HeaderChain
