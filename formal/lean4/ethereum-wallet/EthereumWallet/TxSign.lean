import EthereumWallet.TxDecode

/-!
# Signing a transaction, with the encoding read back before it is returned

`signTransaction` validates the fields, signs the Keccak-256 of the signing
payload (`Sign.signHash`), assembles the raw signed transaction, and then
decodes that raw transaction with the independent decoder (`TxDecode`). The
result is returned only if the decoder gives back exactly the same fields,
the same signature, and the same signing bytes.

So for every transaction this package emits, of every kind:

  decode (encode tx sig) = (tx, sig, signing payload of tx)

is a theorem (`roundTrip_*` below), by the check that precedes the return,
with no proof about RLP itself. What that leaves unproved is completeness:
that a valid transaction is never refused. That is tested (vectors and the
differential run). The decoder's own limits (16 MiB, access list caps) show
up as `checkFailed`.

Sender recovery by the affine `SecpRecovery` of transaction admission is
tested against these signatures, not proved equal to the shared recovery
that the signing theorem is about.
-/

namespace EthereumWallet.TxSign

open EVMCleanroom
open EVMCleanroom.Precompiles.Secp256k1 (n)
open EthereumWallet.Secp
open EthereumWallet.Sign
open EthereumWallet.Tx
open EthereumWallet.TxDecode

/-- The raw signed transaction, returned only if the decoder reads it back unchanged. -/
def checkedRaw (tx : Unsigned) (sig : Signature) : Except Tx.Error ByteArray :=
  match decodeBack tx.kind (signedRaw tx sig).data with
  | .ok back =>
    if back = (tx, sig, (signingPayload tx).data) then .ok (signedRaw tx sig)
    else .error (.checkFailed "the decoded transaction differs from the one encoded")
  | .error e => .error (.checkFailed ("the decoder refused the encoding: " ++ reprStr e))

structure Signed where
  /-- The raw transaction, ready for `eth_sendRawTransaction` (not sent by this package). -/
  raw : ByteArray
  signature : Signature
  signingHash : ByteArray
  /-- The transaction hash: Keccak-256 of `raw`. -/
  hash : ByteArray

def signTransaction (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable) (kp : KeyPair)
    (tx : Unsigned) : Except Tx.Error Signed :=
  match validate tx with
  | some e => .error e
  | none =>
    match signHash risk t kp (signingHash tx) with
    | .error e => .error (.signing e)
    | .ok sig =>
      match checkedRaw tx sig with
      | .error e => .error e
      | .ok raw => .ok ⟨raw, sig, signingHash tx, keccak256 raw⟩

/-- Sign an EIP-7702 authorization tuple `(chainId, address, nonce)`. -/
def signAuthorization (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable) (kp : KeyPair)
    (chainId address nonce : Nat) : Except Tx.Error Authorization :=
  if chainId ≥ 2 ^ 256 ∨ address ≥ 2 ^ 160 ∨ nonce ≥ 2 ^ 64 - 1 then
    .error (.fieldRange "authorization")
  else
    match signHash risk t kp (authorizationHash chainId address nonce) with
    | .error e => .error (.signing e)
    | .ok sig => .ok ⟨chainId, address, nonce, sig.yParity, sig.r, sig.s⟩

/-- Kind: round trip (checked at run time), all kinds.
    Says: a raw transaction returned by `checkedRaw` is the encoding `signedRaw tx sig`, and
    the decoder for its kind reads it back as exactly `tx`, `sig` and the signing payload.
    Does not say: `checkedRaw` succeeds on every valid transaction (tested). -/
theorem checkedRaw_ok (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (h : checkedRaw tx sig = .ok raw) :
    raw = signedRaw tx sig ∧
      decodeBack tx.kind raw.data = .ok (tx, sig, (signingPayload tx).data) := by
  unfold checkedRaw at h
  split at h
  · rename_i back hback
    split at h
    · rename_i heq
      cases h
      exact ⟨rfl, by rw [hback, heq]⟩
    · cases h
  · cases h

/-- Kind: round trip against the existing independent decoder, kinds 0 to 3.
    Says: for a transaction that is not kind 4, `SignedTransaction.decode` accepts the
    returned raw bytes and its result, renamed by `ofDecoded`, is exactly the transaction,
    the signature (`r`, `s`, parity; for legacy the chain id and parity it derived from `v`)
    and the signing payload.
    Does not say: the decoder is complete, or that encoding never refuses. -/
theorem roundTrip_admissionDecoder (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (hk : tx.kind ≠ 4) (h : checkedRaw tx sig = .ok raw) :
    ∃ d, SignedTransaction.decode raw.data = .ok d ∧
      ofDecoded d = (tx, sig, (signingPayload tx).data) := by
  have hb := (checkedRaw_ok tx sig raw h).2
  unfold decodeBack at hb
  rw [if_neg hk] at hb
  split at hb
  · rename_i d hd
    injection hb with hb'
    exact ⟨d, hd, hb'⟩
  · cases hb

/-- decode ∘ encode = id for legacy transactions (with or without EIP-155). -/
theorem roundTrip_legacy (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (hk : tx.kind = 0) (h : checkedRaw tx sig = .ok raw) :
    ∃ d, SignedTransaction.decode raw.data = .ok d ∧
      ofDecoded d = (tx, sig, (signingPayload tx).data) :=
  roundTrip_admissionDecoder tx sig raw (by omega) h

/-- decode ∘ encode = id for EIP-2930 transactions. -/
theorem roundTrip_eip2930 (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (hk : tx.kind = 1) (h : checkedRaw tx sig = .ok raw) :
    ∃ d, SignedTransaction.decode raw.data = .ok d ∧
      ofDecoded d = (tx, sig, (signingPayload tx).data) :=
  roundTrip_admissionDecoder tx sig raw (by omega) h

/-- decode ∘ encode = id for EIP-1559 transactions. -/
theorem roundTrip_eip1559 (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (hk : tx.kind = 2) (h : checkedRaw tx sig = .ok raw) :
    ∃ d, SignedTransaction.decode raw.data = .ok d ∧
      ofDecoded d = (tx, sig, (signingPayload tx).data) :=
  roundTrip_admissionDecoder tx sig raw (by omega) h

/-- decode ∘ encode = id for EIP-4844 blob transactions (network form without sidecar). -/
theorem roundTrip_eip4844 (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (hk : tx.kind = 3) (h : checkedRaw tx sig = .ok raw) :
    ∃ d, SignedTransaction.decode raw.data = .ok d ∧
      ofDecoded d = (tx, sig, (signingPayload tx).data) :=
  roundTrip_admissionDecoder tx sig raw (by omega) h

/-- Kind: round trip, EIP-7702.
    Says: for a kind 4 transaction the wallet's set-code decoder (canonical RLP reader of
    the EVM work, field layout written here) reads the returned bytes back unchanged.
    Does not say: an independently written kind 4 decoder agrees (none exists here yet). -/
theorem roundTrip_eip7702 (tx : Unsigned) (sig : Signature) (raw : ByteArray)
    (hk : tx.kind = 4) (h : checkedRaw tx sig = .ok raw) :
    decodeSetCode raw.data = .ok (tx, sig, (signingPayload tx).data) := by
  have hb := (checkedRaw_ok tx sig raw h).2
  unfold decodeBack at hb
  rw [if_pos hk] at hb
  exact hb

/-- Kind: soundness of every signed transaction returned.
    Says: if `signTransaction` returns, then the transaction passed `validate`; the raw bytes
    are `signedRaw` of it and the returned signature; the decoder for its kind reads them back
    as the same fields, signature and signing payload; `r` is in `[1, n-1]`, `s` in `[1, n/2]`
    (EIP-2), `yParity` is a bit; and the shared recovery applied to the signing hash and the
    signature gives the signer's public key.
    Does not say: that it returns for every valid transaction; that the affine recovery of
    transaction admission agrees (tested); anything about timing. -/
theorem signTransaction_sound (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (tx : Unsigned) (out : Signed)
    (h : signTransaction risk t kp tx = .ok out) :
    validate tx = none ∧ out.raw = signedRaw tx out.signature ∧
      out.signingHash = signingHash tx ∧
      decodeBack tx.kind out.raw.data = .ok (tx, out.signature, (signingPayload tx).data) ∧
      0 < out.signature.r ∧ out.signature.r < n ∧ 0 < out.signature.s ∧
      out.signature.s ≤ n / 2 ∧ out.signature.yParity < 2 ∧
      Precompiles.Secp256k1.recover (bytesToNat (signingHash tx)) out.signature.yParity
        out.signature.r out.signature.s = some (kp.x, kp.y) := by
  unfold signTransaction at h
  split at h
  · cases h
  · rename_i hvalid
    split at h
    · cases h
    · rename_i sig hsig
      split at h
      · cases h
      · rename_i raw hraw
        cases h
        have hs := signHash_sound risk t kp _ sig hsig
        have hr := checkedRaw_ok tx sig raw hraw
        exact ⟨hvalid, hr.1, rfl, hr.2, hs.2⟩

/-- Kind: round trip at the sender level.
    Says: the address recovered (shared recovery) from the signing hash and signature of a
    returned transaction is the signer's address.
    Does not say: more than `signTransaction_sound`. -/
theorem signTransaction_sender (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (tx : Unsigned) (out : Signed)
    (h : signTransaction risk t kp tx = .ok out) :
    recoverAddress (bytesToNat (signingHash tx)) out.signature = some kp.address := by
  have hs := (signTransaction_sound risk t kp tx out h).2.2.2.2.2.2.2.2.2
  simp [recoverAddress, hs, KeyPair.address]

/-- Kind: refusal.
    Says: a transaction that breaks a rule of `validate` is refused with that rule's error,
    before the key is used.
    Does not say: which rules exist (see `validate`). -/
theorem signTransaction_invalid (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (tx : Unsigned) (e : Tx.Error) (h : validate tx = some e) :
    signTransaction risk t kp tx = .error e := by
  simp [signTransaction, h]

/-- Kind: soundness of a signed authorization (EIP-7702).
    Says: a returned authorization carries the requested tuple; its `s` is in `[1, n/2]` and
    `r` in `[1, n-1]`, `yParity` is a bit; and the shared recovery on
    `keccak256(0x05 ‖ rlp([chainId, address, nonce]))` gives the signer's public key.
    Does not say: that signing succeeds for every tuple in range (tested). -/
theorem signAuthorization_sound (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (chainId address nonce : Nat) (a : Authorization)
    (h : signAuthorization risk t kp chainId address nonce = .ok a) :
    a.chainId = chainId ∧ a.address = address ∧ a.nonce = nonce ∧
      0 < a.r ∧ a.r < n ∧ 0 < a.s ∧ a.s ≤ n / 2 ∧ a.yParity < 2 ∧
      Precompiles.Secp256k1.recover (bytesToNat (authorizationHash chainId address nonce))
        a.yParity a.r a.s = some (kp.x, kp.y) := by
  unfold signAuthorization at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i sig hsig
      cases h
      exact ⟨rfl, rfl, rfl, (signHash_sound risk t kp _ sig hsig).2⟩

#print axioms checkedRaw_ok
#print axioms roundTrip_admissionDecoder
#print axioms roundTrip_legacy
#print axioms roundTrip_eip2930
#print axioms roundTrip_eip1559
#print axioms roundTrip_eip4844
#print axioms roundTrip_eip7702
#print axioms signTransaction_sound
#print axioms signTransaction_sender
#print axioms signTransaction_invalid
#print axioms signAuthorization_sound

end EthereumWallet.TxSign
