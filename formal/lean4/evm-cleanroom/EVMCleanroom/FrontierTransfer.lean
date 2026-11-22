import EVMCleanroom.Core

/-!
# Historical Frontier (chainstart) value-transfer transition

The first recorded Ethereum mainnet transaction (block 46147, 7 August
2015) predates EIP-150, EIP-155, EIP-158 and every modern fee-market fork.
This file deliberately uses FRONTIER's intrinsic gas (4/68 per calldata
zero/nonzero byte), 21,000 base gas, and entire gas fee paid to miner.

The executable transition is *conditional* on genuine independently
authenticated pre-transaction account balances, nonces and code. The
accompanying real-chain evidence script verifies actual signed RLP,
transaction hash, transaction-trie and receipt-trie commitments; it DOES
NOT yet provide an authenticated historic prestate witness. Neither
that script nor these local proofs may be represented as full mainnet
state-root replay.
-/

namespace EVMCleanroom.FrontierTransfer

structure Input where
  gasLimit : Nat
  blockGasRemaining : Nat
  gasPrice : Nat
  transferredValue : Nat
  zeros : Nat
  nonzeros : Nat
  senderBalance : Nat
  receiverBalance : Nat
  minerBalance : Nat
  senderNonce : Nat
  signedNonce : Nat
  recipientHasNoCode : Bool
  deriving Repr

def intrinsicGas (p : Input) : Nat :=
  21000 + 4 * p.zeros + 68 * p.nonzeros

def fee (p : Input) : Nat := intrinsicGas p * p.gasPrice

def upfrontRequirement (p : Input) : Nat :=
  p.transferredValue + p.gasLimit * p.gasPrice

def debit (p : Input) : Nat :=
  p.transferredValue + fee p

structure Outcome where
  senderBalance : Nat
  receiverBalance : Nat
  minerBalance : Nat
  senderNonce : Nat
  gasUsed : Nat
  gasRemaining : Nat
  chargedFee : Nat
  valueTransferred : Nat
  deriving Repr

/-- This step is applied ONLY after all validation checks in settle.
    No block subsidy is credited here: Frontier's 5 ETH miner subsidy is
    a distinct BLOCK transition, not the transaction gas reward. -/
def settleUnchecked (p : Input) : Outcome :=
  { senderBalance := p.senderBalance - debit p
    receiverBalance := p.receiverBalance + p.transferredValue
    minerBalance := p.minerBalance + fee p
    senderNonce := p.senderNonce + 1
    gasUsed := intrinsicGas p
    gasRemaining := p.gasLimit - intrinsicGas p
    chargedFee := fee p
    valueTransferred := p.transferredValue }

/-- Reject inputs not admitted by this exact Frontier transfer slice.
    The host verifies 160-bit distinct sender/receiver/miner addresses,
    signed RLP sender recovery, and their actual account code/nonce.
    They must not be taken from untrusted transaction prose. -/
def settle (p : Input) : Except String Outcome :=
  if !p.recipientHasNoCode then .error "recipient-code-execution-not-modelled"
  else if p.senderNonce != p.signedNonce then .error "nonce-mismatch"
  else if p.senderNonce ≥ 2 ^ 64 - 1 then .error "nonce-out-of-range"
  else if p.gasLimit > p.blockGasRemaining then .error "block-gas-exceeded"
  else if p.gasLimit < intrinsicGas p then .error "below-frontier-intrinsic"
  else if p.senderBalance ≥ modulus ||
          p.receiverBalance ≥ modulus || p.minerBalance ≥ modulus then
    .error "account-balance-out-of-range"
  else if p.senderBalance < upfrontRequirement p then
    .error "insufficient-upfront-balance"
  else if p.receiverBalance + p.transferredValue ≥ modulus then
    .error "receiver-overflow"
  else if p.minerBalance + fee p ≥ modulus then
    .error "miner-overflow"
  else .ok (settleUnchecked p)

/-- Frontier transaction fees are all miner reward (zero base fee). -/
theorem settleUnchecked_miner_fee (p : Input) :
    (settleUnchecked p).chargedFee = fee p := rfl

theorem settleUnchecked_nonce (p : Input) :
    (settleUnchecked p).senderNonce = p.senderNonce + 1 := rfl

/-- Fee + value debit is exact provided the initial balance can cover it.
    This is a local arithmetic theorem, not a historic-prestate claim. -/
theorem settleUnchecked_sender_debit (p : Input)
    (h : debit p ≤ p.senderBalance) :
    (settleUnchecked p).senderBalance + debit p =
      p.senderBalance := by
  dsimp [settleUnchecked]
  exact Nat.sub_add_cancel h

/-- Transaction-level conservation across the THREE named participants,
    excluding the separately specified block subsidy / uncle rewards. -/
theorem settleUnchecked_conserves_accounts (p : Input)
    (h : debit p ≤ p.senderBalance) :
    (settleUnchecked p).senderBalance +
      (settleUnchecked p).receiverBalance +
      (settleUnchecked p).minerBalance =
      p.senderBalance + p.receiverBalance + p.minerBalance := by
  dsimp [settleUnchecked, debit]
  have hdebit : p.transferredValue + fee p ≤ p.senderBalance := h
  omega

/-- On validated settlement, no gas above the signed transaction cap
    can be spent. -/
theorem settleUnchecked_gas_bounded (p : Input)
    (h : intrinsicGas p ≤ p.gasLimit) :
    (settleUnchecked p).gasRemaining +
      (settleUnchecked p).gasUsed = p.gasLimit := by
  dsimp [settleUnchecked]
  exact Nat.sub_add_cancel h

/-- The public admitted transition never produces a different nonce. -/
theorem settle_nonce (p : Input) (out : Outcome)
    (h : settle p = .ok out) :
    out.senderNonce = p.senderNonce + 1 := by
  unfold settle at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rfl

private def historicalExample : Input :=
  { gasLimit := 21000
    blockGasRemaining := 21003
    gasPrice := 50000000000000
    transferredValue := 31337
    zeros := 0
    nonzeros := 0
    senderBalance := 2000000000000000000
    receiverBalance := 0
    minerBalance := 0
    senderNonce := 0
    signedNonce := 0
    recipientHasNoCode := true }

/-- Fixture BALANCES ARE ILLUSTRATIVE, NOT AUTHENTICATED MAINNET PRESTATE. -/
#guard intrinsicGas historicalExample == 21000
#guard fee historicalExample == 1050000000000000000
#guard debit historicalExample == 1050000000000031337
#guard (settleUnchecked historicalExample).senderBalance == 949999999999968663
#guard (settleUnchecked historicalExample).receiverBalance == 31337
#guard (settleUnchecked historicalExample).minerBalance == 1050000000000000000
#guard (settleUnchecked historicalExample).senderNonce == 1

#print axioms settleUnchecked_miner_fee
#print axioms settleUnchecked_nonce
#print axioms settleUnchecked_sender_debit
#print axioms settleUnchecked_conserves_accounts
#print axioms settleUnchecked_gas_bounded
#print axioms settle_nonce

end EVMCleanroom.FrontierTransfer
