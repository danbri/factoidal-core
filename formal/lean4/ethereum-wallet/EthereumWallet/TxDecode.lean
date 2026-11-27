import EthereumWallet.Tx
import EVMCleanroom.SignedTransaction

/-!
# Reading a signed transaction back through the independent decoder

For kinds 0 to 3 the decoder is `EVMCleanroom.SignedTransaction.decode`, the
transaction admission decoder of the EVM work (canonical RLP, EIP-155,
EIP-2718, EIP-2930, EIP-1559, EIP-4844). It was written without reference to
the wallet's encoder and shares no code with it. `ofDecoded` only renames its
result into the wallet's `Unsigned` and `Signature`.

That decoder has no EIP-7702 case yet. For kind 4, `decodeSetCode` here reads
the envelope with the same canonical RLP reader and field helpers
(`decodeRoot`, `members`, `scalarAt`, `signingBytes`, …). It is wallet code,
so the kind 4 check is weaker evidence than the others: the RLP layer is
independent of the encoder, the field layout is not independently written.
When the admission decoder gains kind 4, this function should give way to it.
-/

namespace EthereumWallet.TxDecode

open EVMCleanroom
open EVMCleanroom.SignedTransaction
open EVMCleanroom.CanonicalRLP (Item)
open EthereumWallet.Tx
open EthereumWallet.Sign (Signature)

/-- The decoder's result in the wallet's types, with the signing bytes it reconstructed. -/
def ofDecoded (d : Decoded) : Unsigned × Signature × Array UInt8 :=
  ({ kind := d.kind
     chainId := d.chain
     nonce := d.nonce
     maxPriorityFeePerGas := d.priorityFeeCap
     maxFeePerGas := d.gasPriceCap
     gasLimit := d.gasLimit
     to := d.to
     value := d.value
     data := d.data
     accessList := d.accessList.map fun entry => ⟨entry.address, entry.storageKeys⟩
     maxFeePerBlobGas := match d.blob with
       | none => 0
       | some blob => blob.maxFeePerBlobGas
     blobVersionedHashes := match d.blob with
       | none => []
       | some blob => blob.hashes.toList.map asNat
     authorizationList := [] },
   ⟨d.r, d.s, d.parity⟩, d.signing)

/-- Local cap on authorizations per transaction (a resource rule, not a protocol one). -/
def maxAuthorizations : Nat := 256

def readAuthorization (item : Item) : Except Failure Authorization := do
  let fields ← members item 7
  if fields.size != 6 then throw (.malformed "authorization tuple width")
  let address ← fixedBytes (← get fields 1) 20
  return {
    chainId := ← scalarAt fields 0
    address := asNat address
    nonce := ← scalarAt fields 2 8
    yParity := ← scalarAt fields 3 1
    r := ← scalarAt fields 4
    s := ← scalarAt fields 5 }

/-- An EIP-7702 envelope: `0x04 ‖ rlp([chainId, nonce, maxPriorityFeePerGas, maxFeePerGas,
    gasLimit, to, value, data, accessList, authorizationList, yParity, r, s])`. -/
def decodeSetCode (raw : Array UInt8) : Except Failure (Unsigned × Signature × Array UInt8) :=
  if raw.size > maxRawBytes then .error .resourceLimit
  else do
    if (raw[0]?).getD 0 != 4 then throw (.malformed "not a set-code envelope")
    let root ← decodeRoot (raw.extract 1 raw.size)
    let fields ← members root 15
    if fields.size != 13 then throw (.malformed "signed-field-count")
    let yParity ← scalarAt fields 10 1
    if yParity > 1 then throw .invalidSignature
    let dest ← destination (← get fields 5)
    if dest.isNone then throw (.malformed "set-code-creation")
    let access ← readAccessList (← get fields 8)
    let tuples ← members (← get fields 9) maxAuthorizations
    let authorizations ← tuples.mapM readAuthorization
    if authorizations.isEmpty then throw (.malformed "empty-authorization-list")
    return ({
      kind := 4
      chainId := some (← scalarAt fields 0)
      nonce := ← scalarAt fields 1
      maxPriorityFeePerGas := ← scalarAt fields 2
      maxFeePerGas := ← scalarAt fields 3
      gasLimit := ← scalarAt fields 4
      to := dest
      value := ← scalarAt fields 6
      data := ← byteString (← get fields 7)
      accessList := access.map fun entry => ⟨entry.address, entry.storageKeys⟩
      maxFeePerBlobGas := 0
      blobVersionedHashes := []
      authorizationList := authorizations.toList },
      ⟨← scalarAt fields 11, ← scalarAt fields 12, yParity⟩,
      signingBytes 4 fields 10 none)

/-- The decoder for a transaction of the given kind. -/
def decodeBack (kind : Nat) (raw : Array UInt8) :
    Except Failure (Unsigned × Signature × Array UInt8) :=
  if kind = 4 then decodeSetCode raw
  else
    match decode raw with
    | .ok d => .ok (ofDecoded d)
    | .error e => .error e

/-- Kind: resource admission.
    Says: an over-long kind 4 envelope is refused before any RLP work.
    Does not say: the envelope is invalid Ethereum data. -/
theorem decodeSetCode_over_limit (raw : Array UInt8) (h : raw.size > maxRawBytes) :
    decodeSetCode raw = .error .resourceLimit := by
  simp [decodeSetCode, h]

#print axioms decodeSetCode_over_limit

end EthereumWallet.TxDecode
