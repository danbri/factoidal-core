import EVMCleanroom.TxAccounting

/-!
# Prague EIP-4844/EIP-7702 restricted envelope and authority transition

This *executable Lean* model extends the existing empty-code EIP-7623
settlement slice to the two previously excluded genuine official EELS
vectors. It accounts for type 3 blob fees separately from execution gas,
and for type 4's 25,000 intrinsic gas per authorization. It also constructs
the 23-byte EIP-7702 delegation indicator and increments the authority
nonce in Lean, after host-verified secp256k1 signature recovery.

The blob base-fee schedule in this slice accepts EXCESS_BLOB_GAS=0 only,
where EIP-4844's fake_exponential(1,0,3338477) is exactly 1. Higher
excess is explicitly rejected pending a separately validated general
exponential model. This does NOT implement all Prague transactions.
RLP, signature recovery, trie hashing and fixture/host wiring are trusted.
-/

namespace EVMCleanroom.PragueEnvelope

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
  txType : Nat
  blobCount : Nat
  maxFeePerBlobGas : Nat
  excessBlobGas : Nat
  authorizationCount : Nat
  existingAuthorizations : Nat
  deriving Repr

def calldataTokens (p : Input) : Nat :=
  p.zeros + 4 * p.nonzeros

def intrinsicGas (p : Input) : Nat :=
  21000 + 4 * p.zeros + 16 * p.nonzeros +
    2400 * p.accessAddresses + 1900 * p.accessKeys +
    25000 * p.authorizationCount

def floorGas (p : Input) : Nat :=
  21000 + 10 * calldataTokens p

def effectivePrice (p : Input) : Nat :=
  if p.txType ≥ 2 then min p.gasPriceCap (p.baseFee + p.priorityCap)
  else p.gasPriceCap

/-- The refund allowance applies to successful EIP-7702 authorizations on
    already nonempty existing accounts, limited by EIP-3529's 1/5 cap.
    Both selected official EELS fixtures use zero actual refund. -/
def authRefund (p : Input) : Nat :=
  min (12500 * p.existingAuthorizations)
    ((intrinsicGas p + p.executionUsed) / 5)

def chargedGas (p : Input) : Nat :=
  max (intrinsicGas p + p.executionUsed - authRefund p) (floorGas p)

def blobGas (p : Input) : Nat := 131072 * p.blobCount

/-- EIP-4844 at excessBlobGas = 0, where the fake exponential yields 1. -/
def blobBaseFeeAtZero : Nat := 1

def blobBurn (p : Input) : Nat :=
  blobGas p * blobBaseFeeAtZero

def totalChargedWei (p : Input) : Nat :=
  chargedGas p * effectivePrice p + blobBurn p

/-- Check upfront affordability using *caps*, not just actual gas spent.
    A type-3 transaction escrows the max possible blob fee as well. -/
def maximumUpfront (p : Input) : Nat :=
  p.gasLimit * p.gasPriceCap + blobGas p * p.maxFeePerBlobGas

structure Settlement where
  intrinsic : Nat
  floor : Nat
  charged : Nat
  price : Nat
  blobGasUsed : Nat
  blobFeeBurn : Nat
  senderAfterBalance : Nat
  senderAfterNonce : Nat
  minerReward : Nat
  baseFeeBurn : Nat
  authorizationRefundGas : Nat
  deriving Repr

def settleUnchecked (p : Input) : Settlement :=
  { intrinsic := intrinsicGas p
    floor := floorGas p
    charged := chargedGas p
    price := effectivePrice p
    blobGasUsed := blobGas p
    blobFeeBurn := blobBurn p
    senderAfterBalance := p.senderBalance - totalChargedWei p
    senderAfterNonce := p.senderNonce + 1
    minerReward := chargedGas p * (effectivePrice p - p.baseFee)
    baseFeeBurn := chargedGas p * p.baseFee
    authorizationRefundGas := authRefund p }

/-- Exactly the shapes admitted by this scoped replay. ALL failures are
    explicit errors; none is silently treated as a passed state test. -/
def settle (p : Input) : Except String Settlement :=
  if p.txType > 4 then .error "bad-transaction-type"
  else if p.txType = 3 && p.blobCount = 0 then .error "missing-blob"
  else if p.txType != 3 && p.blobCount != 0 then .error "unexpected-blob"
  else if p.txType = 3 && p.excessBlobGas != 0 then
    .error "blob-excess-fee-not-in-this-slice"
  else if p.txType = 3 && p.maxFeePerBlobGas < blobBaseFeeAtZero then
    .error "blob-cap-below-current-fee"
  else if p.txType = 4 && p.authorizationCount = 0 then
    .error "missing-authorization"
  else if p.txType != 4 && p.authorizationCount != 0 then
    .error "unexpected-authorization"
  else if p.existingAuthorizations > p.authorizationCount then
    .error "invalid-authorization-refund-count"
  else if p.txType < 2 && p.priorityCap != 0 then
    .error "legacy-tx-has-priority-cap"
  else if p.txType >= 2 && p.priorityCap > p.gasPriceCap then
    .error "priority-exceeds-fee-cap"
  else if p.gasLimit < intrinsicGas p then .error "below-intrinsic-gas"
  else if p.gasLimit < floorGas p then .error "below-calldata-floor"
  else if chargedGas p > p.gasLimit then .error "execution-out-of-gas"
  else if effectivePrice p < p.baseFee then .error "price-below-base-fee"
  else if p.senderBalance < maximumUpfront p then
    .error "insufficient-upfront-balance"
  else if p.senderBalance < totalChargedWei p then
    .error "insufficient-settlement-balance"
  else .ok (settleUnchecked p)

/-- The local intrinsic calculation includes authorization overhead in
    full before considering a refund or EIP-7623's calldata floor. -/
theorem authorization_intrinsic_bounded (p : Input) :
    25000 * p.authorizationCount ≤ intrinsicGas p := by
  unfold intrinsicGas
  omega

theorem settleUnchecked_nonce_advances (p : Input) :
    (settleUnchecked p).senderAfterNonce = p.senderNonce + 1 := rfl

/-- Whenever the final debit fits in the initial sender balance, the
    arithmetic settlement (execution gas + blob burn) conserves wei. -/
theorem settleUnchecked_balance_exact (p : Input)
    (h : totalChargedWei p ≤ p.senderBalance) :
    (settleUnchecked p).senderAfterBalance + totalChargedWei p =
      p.senderBalance := by
  simpa only [settleUnchecked] using Nat.sub_add_cancel h

/-- The blob fee is never treated as a miner tip. -/
theorem settleUnchecked_fee_conservation (p : Input)
    (h : p.baseFee ≤ effectivePrice p) :
    (settleUnchecked p).minerReward +
      (settleUnchecked p).baseFeeBurn + (settleUnchecked p).blobFeeBurn =
      totalChargedWei p := by
  simp only [settleUnchecked, totalChargedWei]
  have ht : effectivePrice p - p.baseFee + p.baseFee =
      effectivePrice p := Nat.sub_add_cancel h
  calc
    chargedGas p * (effectivePrice p - p.baseFee) +
      chargedGas p * p.baseFee + blobBurn p =
      chargedGas p * ((effectivePrice p - p.baseFee) + p.baseFee) +
      blobBurn p := by rw [Nat.mul_add]
    _ = totalChargedWei p := by simp [totalChargedWei, ht]

/- EIP-7702 authorization changes are separate from the transaction fee
   settlement, and must be written to the world state even for zero-value
   and zero-bytecode destination calls. -/

def addressBound : Nat := 2 ^ 160

structure AuthorizationInput where
  networkChainId : Nat
  signedChainId : Nat
  signedNonce : Nat
  currentNonce : Nat
  delegateAddress : Nat
  codeIsPermitted : Bool
  signatureVerified : Bool
  accountExists : Bool
  deriving Repr

/-- 0xef0100 || 20-byte big-endian address (not a hex text string). -/
def delegationCode (addr : Nat) : Array UInt8 :=
  #[0xef, 0x01, 0x00] ++
    ((List.range 20).map (fun i =>
      UInt8.ofNat ((addr / 256 ^ (19 - i)) % 256))).toArray

structure AuthorityAfter where
  nonce : Nat
  code : Array UInt8
  alreadyExisted : Bool
  refundGas : Nat
  deriving Repr

def authorizeUnchecked (a : AuthorizationInput) : AuthorityAfter :=
  { nonce := a.currentNonce + 1
    code := if a.delegateAddress = 0 then #[] else delegationCode a.delegateAddress
    alreadyExisted := a.accountExists
    refundGas := if a.accountExists then 12500 else 0 }

/-- The RLP signature and recovered authority address are checked by
    the external host and passed as signatureVerified. There is no Lean
    secp256k1 verification theorem yet. -/
def authorize (a : AuthorizationInput) : Except String AuthorityAfter :=
  if a.signedChainId != 0 && a.signedChainId != a.networkChainId then
    .error "authorization-chain-id-mismatch"
  else if a.signedNonce ≥ 2 ^ 64 - 1 then
    .error "authorization-nonce-too-large"
  else if a.delegateAddress ≥ addressBound then
    .error "delegation-address-out-of-range"
  else if !a.signatureVerified then .error "authorization-signature-not-verified"
  else if !a.codeIsPermitted then .error "authorization-code-not-permitted"
  else if a.signedNonce != a.currentNonce then
    .error "authorization-nonce-mismatch"
  else .ok (authorizeUnchecked a)

theorem authorizeUnchecked_nonce (a : AuthorizationInput) :
    (authorizeUnchecked a).nonce = a.currentNonce + 1 := rfl

theorem authorizeUnchecked_new_refund (a : AuthorizationInput)
    (h : a.accountExists = false) :
    (authorizeUnchecked a).refundGas = 0 := by
  simp [authorizeUnchecked, h]

#guard blobBaseFeeAtZero == 1
private def blobExample : Input := {
  zeros := 0, nonzeros := 0, accessAddresses := 0, accessKeys := 0,
  gasLimit := 0, gasPriceCap := 0, priorityCap := 0, baseFee := 0,
  senderBalance := 0, senderNonce := 0, executionUsed := 0,
  txType := 3, blobCount := 1, maxFeePerBlobGas := 1, excessBlobGas := 0,
  authorizationCount := 0, existingAuthorizations := 0 }
#guard blobGas blobExample == 131072
#guard (delegationCode 1).size == 23
#guard (delegationCode 1).getD 0 0 == 0xef
#guard (delegationCode 1).getD 1 0 == 0x01
#guard (delegationCode 1).getD 2 0 == 0x00
#guard (delegationCode 1).getD 22 0 == 0x01

#print axioms authorization_intrinsic_bounded
#print axioms settleUnchecked_nonce_advances
#print axioms settleUnchecked_balance_exact
#print axioms settleUnchecked_fee_conservation
#print axioms authorizeUnchecked_nonce
#print axioms authorizeUnchecked_new_refund

end EVMCleanroom.PragueEnvelope
