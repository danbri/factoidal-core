import EthereumWallet.Abi.Signature

/-!
# Contract deployment: creation data and address prediction

* Creation transaction data is the initcode followed by the ABI-encoded
  constructor arguments.
* `CREATE`: the new address is the low 20 bytes of
  `keccak256(rlp([sender, nonce]))` (Yellow Paper, section 7).
* `CREATE2`: the low 20 bytes of
  `keccak256(0xff ‖ sender ‖ salt ‖ keccak256(initcode))` (EIP-1014).

The RLP encoder here is the general definition for byte strings and lists,
written from the Yellow Paper's appendix B; it is small and used only for
the `CREATE` preimage.
-/

namespace EthereumWallet.Calls

open EthereumWallet.Abi

/-- Creation transaction data. -/
def creationData (initcode : List UInt8) (ctorTypes : List AbiType) (args : List AbiValue) :
    List UInt8 :=
  initcode ++ encodeArgs ctorTypes args

/-- Kind: round trip. Says: the constructor arguments can be read back, strictly, from the
    creation data after the initcode.
    Does not say: where the initcode ends if that length is not known. -/
theorem creationData_args (initcode : List UInt8) (ts : List AbiType) (args : List AbiValue)
    (hty : typesOk ts = true) (hc : checkL ts args = true)
    (hl : (encodeArgs ts args).length < two256) :
    decodeArgsAt ts (toBytes (creationData initcode ts args)) initcode.length = .ok args := by
  have hw := window_toBytes (creationData initcode ts args)
  simp only [creationData] at hw ⊢
  exact decodeArgsAt_complete ts _ initcode.length args hty hc hl (by simpa using hw.right)
    (by rw [toBytes_size, List.length_append])

/-! ## RLP (encoding only) -/

inductive Rlp where
  | bytes (b : List UInt8)
  | list (items : List Rlp)

/-- Big-endian bytes of a number with no leading zero byte; empty for zero.
    The fuel is the largest number of bytes produced. -/
def minimalBE : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc else minimalBE fuel (n / 256) (UInt8.ofNat (n % 256) :: acc)

def rlpLength (len offset : Nat) : List UInt8 :=
  if len < 56 then [UInt8.ofNat (offset + len)]
  else
    let lb := minimalBE 8 len []
    UInt8.ofNat (offset + 55 + lb.length) :: lb

def rlpBytes (b : List UInt8) : List UInt8 :=
  match b with
  | [x] => if x.toNat < 128 then [x] else rlpLength 1 128 ++ b
  | _ => rlpLength b.length 128 ++ b

mutual
def Rlp.encode : Rlp → List UInt8
  | .bytes b => rlpBytes b
  | .list items =>
    let payload := Rlp.encodeList items
    rlpLength payload.length 192 ++ payload
def Rlp.encodeList : List Rlp → List UInt8
  | [] => []
  | x :: xs => x.encode ++ Rlp.encodeList xs
end

/-! ## CREATE -/

/-- Nonces are below `2^64` (EIP-2681). -/
def maxNonce : Nat := 2 ^ 64 - 1

def createPreimage (sender nonce : Nat) : List UInt8 :=
  (Rlp.list [.bytes (beBytes 20 sender), .bytes (minimalBE 8 nonce [])]).encode

/-- The address of a contract created by `sender` with account nonce `nonce`. -/
def createAddress (sender nonce : Nat) : Nat :=
  natOfBytes ((keccak256 (createPreimage sender nonce)).drop 12)

/-- Kind: definition check. Says: `createAddress` is the low 20 bytes of the Keccak-256 hash of
    the RLP encoding of the list (sender as 20 bytes, nonce as a minimal big-endian integer).
    Does not say: that `keccak256` is Keccak-256 or that `Rlp.encode` matches every RLP case
    (both tested against published addresses). -/
theorem createAddress_eq (sender nonce : Nat) :
    createAddress sender nonce
      = natOfBytes ((keccak256
          (Rlp.list [.bytes (beBytes 20 sender), .bytes (minimalBE 8 nonce [])]).encode).drop 12) :=
  rfl

theorem natOfBytes_fold_lt (l : List UInt8) (a : Nat) :
    l.foldl (fun a b => a * 256 + b.toNat) a < (a + 1) * 256 ^ l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (a * 256 + b.toNat)
    have hb : b.toNat < 256 := b.toNat_lt
    have h2 : (a * 256 + b.toNat + 1) * 256 ^ l.length ≤ ((a + 1) * 256) * 256 ^ l.length :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ l.length) 256, ← Nat.mul_assoc]
    omega

theorem natOfBytes_lt (l : List UInt8) : natOfBytes l < 256 ^ l.length := by
  have := natOfBytes_fold_lt l 0
  simpa [natOfBytes] using this

theorem low20_lt (h : List UInt8) (hl : h.length = 32) : natOfBytes (h.drop 12) < 2 ^ 160 := by
  have := natOfBytes_lt (h.drop 12)
  rw [List.length_drop, hl] at this
  exact this

/-- Kind: range. Says: a predicted `CREATE` address is a 20-byte value.
    Does not say: that no other account maps to it. -/
theorem createAddress_lt (sender nonce : Nat) : createAddress sender nonce < 2 ^ 160 :=
  low20_lt _ (keccak256_length _)

/-! ## CREATE2 -/

def create2Preimage (sender salt : Nat) (initcodeHash : List UInt8) : List UInt8 :=
  0xff :: (beBytes 20 sender ++ beBytes 32 salt ++ initcodeHash)

/-- The address of a contract created with `CREATE2` by `sender` (the factory) with `salt`,
    given the Keccak-256 hash of the initcode. -/
def create2AddressOfHash (sender salt : Nat) (initcodeHash : List UInt8) : Nat :=
  natOfBytes ((keccak256 (create2Preimage sender salt initcodeHash)).drop 12)

def create2Address (sender salt : Nat) (initcode : List UInt8) : Nat :=
  create2AddressOfHash sender salt (keccak256 initcode)

/-- Kind: definition check. Says: `create2Address` is the low 20 bytes of
    `keccak256(0xff ‖ sender (20 bytes) ‖ salt (32 bytes) ‖ keccak256(initcode))`.
    Does not say: that `keccak256` is Keccak-256 (tested against the EIP-1014 examples). -/
theorem create2Address_eq (sender salt : Nat) (initcode : List UInt8) :
    create2Address sender salt initcode
      = natOfBytes ((keccak256
          (0xff :: (beBytes 20 sender ++ beBytes 32 salt ++ keccak256 initcode))).drop 12) :=
  rfl

/-- Kind: size. Says: the `CREATE2` preimage is always 85 bytes.
    Does not say: anything about the hash. -/
theorem create2Preimage_length (sender salt : Nat) (initcode : List UInt8) :
    (create2Preimage sender salt (keccak256 initcode)).length = 85 := by
  simp [create2Preimage, beBytes_length, keccak256_length]

/-- Kind: range. Says: a predicted `CREATE2` address is a 20-byte value.
    Does not say: that the address is unused. -/
theorem create2Address_lt (sender salt : Nat) (initcode : List UInt8) :
    create2Address sender salt initcode < 2 ^ 160 :=
  low20_lt _ (keccak256_length _)

end EthereumWallet.Calls
