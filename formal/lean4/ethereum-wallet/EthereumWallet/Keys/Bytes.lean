/-
Byte-string helpers for the key modules: hex, big-endian numbers.
Imports nothing outside `Init`.
-/

namespace EthereumWallet.Keys

/-- The value of one ASCII hex digit, either case. -/
def hexVal? (c : UInt8) : Option UInt8 :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else none

/-- Decode `count` byte pairs of `src` from offset `i`. Structural on `count`. -/
def hexLoop (src : ByteArray) : Nat → Nat → ByteArray → Option ByteArray
  | 0, _, acc => some acc
  | count + 1, i, acc =>
    match hexVal? (src.get! i), hexVal? (src.get! (i + 1)) with
    | some h, some l => hexLoop src count (i + 2) (acc.push (h * 16 + l))
    | _, _ => none

/-- Strict hex decoding: an even number of hex digits, no prefix, no spaces. -/
def ofHex? (s : String) : Option ByteArray :=
  let src := s.toUTF8
  if src.size % 2 != 0 then none
  else hexLoop src (src.size / 2) 0 (ByteArray.emptyWithCapacity (src.size / 2))

/-- Hex decoding for literals in tests and tables: the empty array on bad input. -/
def ofHex! (s : String) : ByteArray := (ofHex? s).getD ByteArray.empty

/-- One lower-case hex digit for a value below 16. -/
def hexChar (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lower-case hex, two digits per byte. -/
def toHex (b : ByteArray) : String :=
  b.foldl (fun s x => (s.push (hexChar (x >>> 4))).push (hexChar (x &&& 15))) ""

/-- The big-endian number a byte string spells. -/
def bytesToNatBE (b : ByteArray) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Push the `count` low bytes of `n`, most significant first. Structural on `count`. -/
def pushNatBE (n : Nat) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | count + 1, acc => pushNatBE n count (acc.push (UInt8.ofNat (n >>> (8 * count))))

/-- `n` as exactly `len` big-endian bytes (the low `8 * len` bits of `n`). -/
def natToBytesBE (n len : Nat) : ByteArray :=
  pushNatBE n len ByteArray.empty

/-- `len` zero bytes. -/
def zeroBytes (len : Nat) : ByteArray := ByteArray.mk (Array.replicate len 0)

theorem pushNatBE_size (n count : Nat) (acc : ByteArray) :
    (pushNatBE n count acc).size = acc.size + count := by
  induction count generalizing acc with
  | zero => rfl
  | succ k ih => simp [pushNatBE, ih, ByteArray.size_push]; omega

/-- Kind: size.
    Says: `natToBytesBE n len` has exactly `len` bytes, whatever `n` is.
    Does not say: that no high bits of `n` were dropped. -/
theorem natToBytesBE_size (n len : Nat) : (natToBytesBE n len).size = len := by
  simp [natToBytesBE, pushNatBE_size]

end EthereumWallet.Keys
