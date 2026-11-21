import EVMCleanroom.Core

/-!
# A deliberately narrow transaction-accounting model

Prague, valid no-code, zero-value type-0/1/2 transactions.

The gas floor here is EIP-7623's calldata-floor rule for transactions
without creation, delegation or blob fees. Access-list intrinsic gas and
EIP-1559 effective gas price are handled explicitly.

This module is NOT a transaction parser, a Merkle trie implementation,
or a proof of external Ethereum specification correspondence.
-/

namespace EVMCleanroom.TxAccounting

structure Input where
  zeros : Nat
  nonzeros : Nat
  accessAddresses : Nat
  accessKeys : Nat
  gasLimit : Nat
  gasPriceCap : Nat
  priorityCap : Nat
  baseFee : Nat
  senderBalance : Nat
  senderNonce : Nat
  executionUsed : Nat
  feeMarket : Bool

def intrinsicGas (p : Input) : Nat :=
  21000 + 4 * p.zeros + 16 * p.nonzeros +
    2400 * p.accessAddresses + 1900 * p.accessKeys

def floorGas (p : Input) : Nat :=
  21000 + 10 * (p.zeros + 4 * p.nonzeros)

def effectivePrice (p : Input) : Nat :=
  if p.feeMarket then min p.gasPriceCap (p.baseFee + p.priorityCap)
  else p.gasPriceCap

def chargedGas (p : Input) : Nat :=
  max (intrinsicGas p + p.executionUsed) (floorGas p)

structure Settlement where
  intrinsic : Nat
  floor : Nat
  charged : Nat
  price : Nat
  senderAfterBalance : Nat
  senderAfterNonce : Nat
  minerReward : Nat
  baseFeeBurn : Nat
  deriving Repr

/-- Arithmetic transition, before validation. Its results are used only
    if settle has checked the input validity constraints. -/
def settleUnchecked (p : Input) : Settlement :=
  let charged := chargedGas p
  let price := effectivePrice p
  { intrinsic := intrinsicGas p
    floor := floorGas p
    charged := charged
    price := price
    senderAfterBalance := p.senderBalance - charged * price
    senderAfterNonce := p.senderNonce + 1
    minerReward := charged * (price - p.baseFee)
    baseFeeBurn := charged * p.baseFee }

/-- Reject invalid inputs instead of silently adjusting the fee budget.
    This models only the restricted fee/nonce domain declared above. -/
def settle (p : Input) : Except String Settlement :=
  if p.gasLimit < intrinsicGas p then .error "below-intrinsic-gas"
  else if p.gasLimit < floorGas p then .error "below-calldata-floor"
  else if chargedGas p > p.gasLimit then .error "execution-out-of-gas"
  else if effectivePrice p < p.baseFee then .error "gas-price-below-base-fee"
  else if p.senderBalance < chargedGas p * effectivePrice p then
    .error "insufficient-balance"
  else .ok (settleUnchecked p)

/-- A successful validated settlement cannot charge more than the gas limit. -/
theorem settle_charged_bounded {p : Input} {out : Settlement}
    (h : settle p = .ok out) : out.charged ≤ p.gasLimit := by
  unfold settle at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp [settleUnchecked]
  omega

/-- The sender debit and remaining balance account for exactly the
    charged fee (for validated inputs). -/
theorem sender_balance_conservation (p : Input)
    (h : chargedGas p * effectivePrice p ≤ p.senderBalance) :
    (settleUnchecked p).senderAfterBalance +
      (settleUnchecked p).charged * (settleUnchecked p).price =
      p.senderBalance := by
  simp only [settleUnchecked]
  exact Nat.sub_add_cancel h

/-- The sender nonce advances by exactly one for a successful transaction. -/
theorem sender_nonce_advances (p : Input) :
    (settleUnchecked p).senderAfterNonce = p.senderNonce + 1 := rfl

/-- Paid gas fees split exactly between beneficiary reward and base-fee
    burn, assuming the effective price is at least the block base fee. -/
theorem fee_conservation (p : Input) (h : p.baseFee ≤ effectivePrice p) :
    (settleUnchecked p).minerReward + (settleUnchecked p).baseFeeBurn =
      (settleUnchecked p).charged * (settleUnchecked p).price := by
  simp only [settleUnchecked]
  calc
    chargedGas p * (effectivePrice p - p.baseFee) +
        chargedGas p * p.baseFee =
        chargedGas p * ((effectivePrice p - p.baseFee) + p.baseFee) := by
          rw [Nat.mul_add]
    _ = chargedGas p * effectivePrice p := by
      rw [Nat.sub_add_cancel h]

#print axioms settle_charged_bounded
#print axioms sender_balance_conservation
#print axioms sender_nonce_advances
#print axioms fee_conservation

end EVMCleanroom.TxAccounting
