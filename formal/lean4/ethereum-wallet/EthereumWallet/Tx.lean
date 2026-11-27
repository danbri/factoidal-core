import EthereumWallet.Sign

/-!
# Unsigned Ethereum transactions: fields, signing payloads, signed encodings

Every current transaction type, written from the specifications:

| kind | Specification | Signing payload |
|---|---|---|
| 0 | legacy, EIP-155 replay protection | `rlp([nonce, gasPrice, gasLimit, to, value, data, chainId, 0, 0])` (the last three only with a chain id) |
| 1 | EIP-2930 | `0x01 ‖ rlp([chainId, nonce, gasPrice, gasLimit, to, value, data, accessList])` |
| 2 | EIP-1559 | `0x02 ‖ rlp([chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gasLimit, to, value, data, accessList])` |
| 3 | EIP-4844 | `0x03 ‖ rlp([… as kind 2 …, maxFeePerBlobGas, blobVersionedHashes])` (no sidecar here) |
| 4 | EIP-7702 | `0x04 ‖ rlp([… as kind 2 …, authorizationList])` |

The signing hash is Keccak-256 of the payload. An EIP-7702 authorization is
signed over `keccak256(0x05 ‖ rlp([chainId, address, nonce]))`.

The RLP encoder here (Yellow Paper, appendix B) is the wallet's own and
shares no code with the decoder in `EVMCleanroom.CanonicalRLP`; `TxSign.lean`
runs that decoder on every encoding before it is returned.

`validate` is the wallet's admission rule: field ranges, the canonical form
of fields a kind does not use (so that decoding gives back the same value),
and the per-kind rules of the EIPs (no contract creation for kinds 3 and 4,
at least one blob hash of version 0x01, at least one authorization).
-/

namespace EthereumWallet.Tx

open EVMCleanroom.Precompiles (natToBE)
open EthereumWallet.Secp (keccak256)
open EthereumWallet.Sign (Signature)

/-- Bytes in the minimal big-endian form of `n` (zero has none). -/
def byteLen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n / 8 + 1

def minimalBE (n : Nat) : ByteArray := natToBE (byteLen n) n

/-- RLP length prefix: `short + len` up to 55 bytes, else `long + (bytes of len)` then `len`. -/
def lengthPrefix (short long len : Nat) : ByteArray :=
  if len ≤ 55 then ⟨#[UInt8.ofNat (short + len)]⟩
  else ⟨#[UInt8.ofNat (long + byteLen len)]⟩ ++ minimalBE len

/-- RLP of a byte string. -/
def rlpBytes (b : ByteArray) : ByteArray :=
  if b.size = 1 ∧ b.data.getD 0 0 < 128 then b else lengthPrefix 128 183 b.size ++ b

/-- RLP of a non-negative integer (minimal big-endian bytes). -/
def rlpNat (n : Nat) : ByteArray := rlpBytes (minimalBE n)

/-- RLP of a fixed-width value such as an address or a hash (leading zeros kept). -/
def rlpFixed (width n : Nat) : ByteArray := rlpBytes (natToBE width n)

/-- RLP of a list whose members are already encoded and concatenated in `payload`. -/
def rlpList (payload : ByteArray) : ByteArray := lengthPrefix 192 247 payload.size ++ payload

def concat (parts : List ByteArray) : ByteArray := parts.foldl (· ++ ·) ByteArray.empty

structure AccessEntry where
  address : Nat
  storageKeys : List Nat
  deriving DecidableEq, Repr

/-- A signed EIP-7702 authorization tuple. -/
structure Authorization where
  chainId : Nat
  address : Nat
  nonce : Nat
  yParity : Nat
  r : Nat
  s : Nat
  deriving DecidableEq, Repr

/-- An unsigned transaction of any kind. Fields a kind does not use hold their
    empty value (`validate` insists on it). Addresses, storage keys and hashes
    are numbers, written at their fixed width when encoded. -/
structure Unsigned where
  kind : Nat
  /-- `none` only for a legacy transaction without EIP-155 replay protection. -/
  chainId : Option Nat
  nonce : Nat
  /-- Zero for kinds 0 and 1. -/
  maxPriorityFeePerGas : Nat
  /-- `gasPrice` for kinds 0 and 1. -/
  maxFeePerGas : Nat
  gasLimit : Nat
  /-- `none` creates a contract (kinds 0, 1, 2 only). -/
  to : Option Nat
  value : Nat
  data : Array UInt8
  accessList : List AccessEntry
  maxFeePerBlobGas : Nat
  blobVersionedHashes : List Nat
  authorizationList : List Authorization
  deriving DecidableEq, Repr

inductive Error where
  | unknownKind
  | missingChainId
  | fieldRange (field : String)
  | notEmpty (field : String)
  | creationNotAllowed
  | noBlobHashes
  | blobHashVersion
  | noAuthorizations
  | signing (e : Sign.Error)
  | checkFailed (reason : String)
  deriving DecidableEq, Repr

def accessEntryOk (e : AccessEntry) : Bool :=
  decide (e.address < 2 ^ 160) && e.storageKeys.all fun key => decide (key < 2 ^ 256)

def authorizationOk (a : Authorization) : Bool :=
  decide (a.chainId < 2 ^ 256) && decide (a.address < 2 ^ 160) && decide (a.nonce < 2 ^ 64) &&
    decide (a.yParity < 2 ^ 8) && decide (a.r < 2 ^ 256) && decide (a.s < 2 ^ 256)

/-- The rules after kind and chain id presence. -/
def validateFields (tx : Unsigned) : Option Error :=
  if (tx.chainId.getD 0) ≥ 2 ^ 64 then some (.fieldRange "chainId")
  else if tx.nonce ≥ 2 ^ 64 - 1 then some (.fieldRange "nonce")
  else if tx.gasLimit ≥ 2 ^ 64 then some (.fieldRange "gasLimit")
  else if tx.maxFeePerGas ≥ 2 ^ 256 then some (.fieldRange "maxFeePerGas")
  else if tx.maxPriorityFeePerGas ≥ 2 ^ 256 then some (.fieldRange "maxPriorityFeePerGas")
  else if tx.value ≥ 2 ^ 256 then some (.fieldRange "value")
  else if (tx.to.getD 0) ≥ 2 ^ 160 then some (.fieldRange "to")
  else if !tx.accessList.all accessEntryOk then some (.fieldRange "accessList")
  else if tx.kind < 2 ∧ tx.maxPriorityFeePerGas ≠ 0 then some (.notEmpty "maxPriorityFeePerGas")
  else if tx.kind = 0 ∧ tx.accessList ≠ [] then some (.notEmpty "accessList")
  else if tx.kind ≠ 3 ∧ (tx.maxFeePerBlobGas ≠ 0 ∨ tx.blobVersionedHashes ≠ []) then
    some (.notEmpty "blob fields")
  else if tx.kind ≠ 4 ∧ tx.authorizationList ≠ [] then some (.notEmpty "authorizationList")
  else if tx.kind ≥ 3 ∧ tx.to.isNone then some .creationNotAllowed
  else if tx.kind = 3 ∧ tx.blobVersionedHashes = [] then some .noBlobHashes
  else if tx.maxFeePerBlobGas ≥ 2 ^ 256 then some (.fieldRange "maxFeePerBlobGas")
  else if !tx.blobVersionedHashes.all (fun h => h / 2 ^ 248 == 1) then some .blobHashVersion
  else if tx.kind = 4 ∧ tx.authorizationList = [] then some .noAuthorizations
  else if !tx.authorizationList.all authorizationOk then some (.fieldRange "authorizationList")
  else none

/-- The first rule a transaction breaks, if any. -/
def validate (tx : Unsigned) : Option Error :=
  if tx.kind > 4 then some .unknownKind
  else if tx.kind ≠ 0 ∧ tx.chainId.isNone then some .missingChainId
  else validateFields tx

def encodeTo : Option Nat → ByteArray
  | none => rlpBytes ByteArray.empty
  | some address => rlpFixed 20 address

def encodeAccessEntry (e : AccessEntry) : ByteArray :=
  rlpList (rlpFixed 20 e.address ++ rlpList (concat (e.storageKeys.map (rlpFixed 32))))

def encodeAccessList (entries : List AccessEntry) : ByteArray :=
  rlpList (concat (entries.map encodeAccessEntry))

def encodeAuthorization (a : Authorization) : ByteArray :=
  rlpList (rlpNat a.chainId ++ rlpFixed 20 a.address ++ rlpNat a.nonce ++
    rlpNat a.yParity ++ rlpNat a.r ++ rlpNat a.s)

/-- The fields shared by kinds 2, 3 and 4, in order. -/
def feeMarketFields (tx : Unsigned) : ByteArray :=
  rlpNat (tx.chainId.getD 0) ++ rlpNat tx.nonce ++ rlpNat tx.maxPriorityFeePerGas ++
    rlpNat tx.maxFeePerGas ++ rlpNat tx.gasLimit ++ encodeTo tx.to ++ rlpNat tx.value ++
    rlpBytes ⟨tx.data⟩ ++ encodeAccessList tx.accessList

/-- The encoded unsigned fields of a transaction, concatenated (no list prefix,
    no EIP-155 suffix, no signature). -/
def unsignedFields (tx : Unsigned) : ByteArray :=
  if tx.kind = 0 then
    rlpNat tx.nonce ++ rlpNat tx.maxFeePerGas ++ rlpNat tx.gasLimit ++ encodeTo tx.to ++
      rlpNat tx.value ++ rlpBytes ⟨tx.data⟩
  else if tx.kind = 1 then
    rlpNat (tx.chainId.getD 0) ++ rlpNat tx.nonce ++ rlpNat tx.maxFeePerGas ++
      rlpNat tx.gasLimit ++ encodeTo tx.to ++ rlpNat tx.value ++ rlpBytes ⟨tx.data⟩ ++
      encodeAccessList tx.accessList
  else if tx.kind = 2 then feeMarketFields tx
  else if tx.kind = 3 then
    feeMarketFields tx ++ rlpNat tx.maxFeePerBlobGas ++
      rlpList (concat (tx.blobVersionedHashes.map (rlpFixed 32)))
  else
    feeMarketFields tx ++ rlpList (concat (tx.authorizationList.map encodeAuthorization))

/-- EIP-155: the chain id and two empty items close the legacy signing payload. -/
def eip155Suffix : Option Nat → ByteArray
  | none => ByteArray.empty
  | some chainId => rlpNat chainId ++ ⟨#[0x80, 0x80]⟩

/-- The exact bytes whose Keccak-256 is signed. -/
def signingPayload (tx : Unsigned) : ByteArray :=
  if tx.kind = 0 then rlpList (unsignedFields tx ++ eip155Suffix tx.chainId)
  else ⟨#[UInt8.ofNat tx.kind]⟩ ++ rlpList (unsignedFields tx)

def signingHash (tx : Unsigned) : ByteArray := keccak256 (signingPayload tx)

/-- The legacy `v`: `27 + yParity`, or `35 + 2·chainId + yParity` under EIP-155. -/
def legacyV (chainId : Option Nat) (yParity : Nat) : Nat :=
  match chainId with
  | none => 27 + yParity
  | some id => 35 + 2 * id + yParity

/-- The signature fields as they close the signed list. -/
def signatureFields (tx : Unsigned) (sig : Signature) : ByteArray :=
  rlpNat (if tx.kind = 0 then legacyV tx.chainId sig.yParity else sig.yParity) ++
    rlpNat sig.r ++ rlpNat sig.s

/-- The raw signed transaction (EIP-2718 envelope for kinds 1 to 4). -/
def signedRaw (tx : Unsigned) (sig : Signature) : ByteArray :=
  if tx.kind = 0 then rlpList (unsignedFields tx ++ signatureFields tx sig)
  else ⟨#[UInt8.ofNat tx.kind]⟩ ++ rlpList (unsignedFields tx ++ signatureFields tx sig)

/-- EIP-7702: the bytes signed by an authority, `0x05 ‖ rlp([chainId, address, nonce])`. -/
def authorizationPayload (chainId address nonce : Nat) : ByteArray :=
  ⟨#[5]⟩ ++ rlpList (rlpNat chainId ++ rlpFixed 20 address ++ rlpNat nonce)

def authorizationHash (chainId address nonce : Nat) : ByteArray :=
  keccak256 (authorizationPayload chainId address nonce)

/-- Kind: admission.
    Says: a transaction of a kind above 4 is refused.
    Does not say: kinds 0 to 4 are accepted. -/
theorem validate_unknown_kind (tx : Unsigned) (h : tx.kind > 4) :
    validate tx = some .unknownKind := by
  simp [validate, h]

/-- Kind: admission.
    Says: an accepted transaction has a known kind, and a chain id unless it is legacy.
    Does not say: the other rules (they are in `validate`'s definition, tested). -/
theorem validate_none (tx : Unsigned) (h : validate tx = none) :
    tx.kind ≤ 4 ∧ (tx.kind ≠ 0 → tx.chainId.isSome = true) := by
  unfold validate at h
  by_cases hk : tx.kind > 4
  · rw [if_pos hk] at h
    cases h
  · rw [if_neg hk] at h
    by_cases hc : tx.kind ≠ 0 ∧ tx.chainId.isNone = true
    · rw [if_pos hc] at h
      cases h
    · refine ⟨by omega, fun hne => ?_⟩
      cases hch : tx.chainId with
      | none => exact absurd ⟨hne, by rw [hch]; rfl⟩ hc
      | some _ => rfl

#print axioms validate_unknown_kind
#print axioms validate_none

end EthereumWallet.Tx
