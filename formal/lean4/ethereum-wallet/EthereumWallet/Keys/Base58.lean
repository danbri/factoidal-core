import L4Factoidal.Crypto.SHA2
import EthereumWallet.Keys.Bytes

/-!
# Base58 and Base58Check (as used by BIP-32 extended keys)

Inputs are bounded: `encode` refuses more than `maxBytes` bytes and `decode?` more than
`maxChars` characters, so the big-number work is bounded.

Not constant-time: the payload goes through `Nat` division and multiplication. An
extended private key encoded or decoded here is exposed to that timing.
-/

namespace EthereumWallet.Keys.Base58

open L4Factoidal.Crypto (sha256)

def alphabet : ByteArray := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toUTF8

def maxBytes : Nat := 128
def maxChars : Nat := 192

/-- The value of a Base58 character. Structural on the number of candidates left. -/
def digitFrom (c : UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | count + 1, i => if alphabet.get! i = c then some i else digitFrom c count (i + 1)

def digitVal? (c : UInt8) : Option Nat := digitFrom c 58 0

def leadingCount (b : ByteArray) (x : UInt8) : Nat → Nat → Nat
  | 0, i => i
  | count + 1, i => if b.get! i = x then leadingCount b x count (i + 1) else i

def encDigits : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc
    else encDigits fuel (n / 58) (Char.ofNat (alphabet.get! (n % 58)).toNat :: acc)

/-- Base58 text of a byte string; `none` above `maxBytes` bytes. -/
def encode (b : ByteArray) : Option String :=
  if maxBytes < b.size then none
  else
    let zeros := leadingCount b 0 b.size 0
    some (String.ofList (List.replicate zeros '1' ++ encDigits (2 * b.size) (bytesToNatBE b) []))

def decValue (src : ByteArray) : Nat → Nat → Nat → Option Nat
  | 0, _, acc => some acc
  | count + 1, i, acc =>
    match digitVal? (src.get! i) with
    | some v => decValue src count (i + 1) (acc * 58 + v)
    | none => none

def byteLen : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc => if n = 0 then acc else byteLen fuel (n / 256) (acc + 1)

/-- The bytes a Base58 text spells; `none` on a foreign character or above `maxChars`. -/
def decode? (s : String) : Option ByteArray :=
  let src := s.toUTF8
  if maxChars < src.size then none
  else
    match decValue src src.size 0 0 with
    | none => none
    | some n =>
      let ones := leadingCount src 49 src.size 0
      some (zeroBytes ones ++ natToBytesBE n (byteLen src.size n 0))

def checksum (payload : ByteArray) : ByteArray := (sha256 (sha256 payload)).extract 0 4

/-- Base58Check: payload followed by the first four bytes of its double SHA-256. -/
def checkEncode (payload : ByteArray) : Option String := encode (payload ++ checksum payload)

/-- The payload of a Base58Check text, if the checksum holds. -/
def checkDecode? (s : String) : Option ByteArray :=
  match decode? s with
  | none => none
  | some raw =>
    if raw.size < 4 then none
    else
      let payload := raw.extract 0 (raw.size - 4)
      if checksum payload = raw.extract (raw.size - 4) raw.size then some payload else none

/-- Kind: refusal (work bound). Says: text longer than `maxChars` bytes is not decoded. -/
theorem decode?_too_long (s : String) (h : maxChars < s.toUTF8.size) : decode? s = none := by
  show (if maxChars < s.toUTF8.size then none else _) = none
  rw [if_pos h]

/-- Kind: refusal (work bound). Says: more than `maxBytes` bytes are not encoded. -/
theorem encode_too_long (b : ByteArray) (h : maxBytes < b.size) : encode b = none := by
  simp [encode, h]

/-- Kind: soundness of the check.
    Says: an accepted text's payload is followed, in the decoded bytes, by its own checksum.
    Does not say: that `sha256` is SHA-256. -/
theorem checkDecode?_checksum (s : String) (payload : ByteArray) (h : checkDecode? s = some payload) :
    ∃ raw, decode? s = some raw ∧ 4 ≤ raw.size ∧ payload = raw.extract 0 (raw.size - 4)
      ∧ checksum payload = raw.extract (raw.size - 4) raw.size := by
  unfold checkDecode? at h
  cases hd : decode? s with
  | none => rw [hd] at h; cases h
  | some raw =>
    rw [hd] at h
    by_cases hs : raw.size < 4
    · simp [hs] at h
    · by_cases hc : checksum (raw.extract 0 (raw.size - 4)) = raw.extract (raw.size - 4) raw.size
      · simp [hs, hc] at h
        exact ⟨raw, rfl, by omega, h.symm, by rw [← h]; exact hc⟩
      · simp [hs, hc] at h

end EthereumWallet.Keys.Base58

open EthereumWallet.Keys in
#print axioms Base58.decode?_too_long
open EthereumWallet.Keys in
#print axioms Base58.encode_too_long
open EthereumWallet.Keys in
#print axioms Base58.checkDecode?_checksum
