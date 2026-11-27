import EVMCleanroom.Keccak
import EthereumWallet.Abi.Bytes

/-!
# Keccak-256 for the wallet's ABI and typed-data code

The hash is `EVMCleanroom.Keccak.digest`, selected in place from
`../evm-cleanroom` (see `lakefile.toml`). Its digest values are tested against
published vectors there and here; no theorem here says the function is
Keccak-256.
-/

namespace EthereumWallet.Abi

def keccak256 (l : List UInt8) : List UInt8 :=
  (EVMCleanroom.Keccak.digest (EVMCleanroom.ByteView.ofArray l.toArray)).toList

theorem keccak256_length (l : List UInt8) : (keccak256 l).length = 32 := by
  simp [keccak256]

/-- UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := ofBytes s.toUTF8

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Lower-case hex, no prefix. -/
def hexOf (l : List UInt8) : String :=
  String.ofList (l.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def unhexLoop : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | [_], _ => none
  | a :: b :: rest, acc =>
    match hexVal a, hexVal b with
    | some x, some y => unhexLoop rest (UInt8.ofNat (x * 16 + y) :: acc)
    | _, _ => none

/-- Bytes of a hex string with an even number of digits; an optional `0x` prefix. -/
def unhex (s : String) : Option (List UInt8) :=
  match s.toList with
  | '0' :: 'x' :: rest => unhexLoop rest []
  | cs => unhexLoop cs []

/-- Big-endian number of a byte list. -/
def natOfBytes (l : List UInt8) : Nat := l.foldl (fun a b => a * 256 + b.toNat) 0

end EthereumWallet.Abi
