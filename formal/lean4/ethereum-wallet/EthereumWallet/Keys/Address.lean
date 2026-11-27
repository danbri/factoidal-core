import EthereumWallet.Keys.Hash
import EthereumWallet.Keys.Curve

/-!
# Ethereum addresses and the ERC-55 (EIP-55) mixed-case checksum

Address: the last 20 bytes of Keccak-256 of the 64-byte `x ‖ y` of the public point.
Checksum: hex digit `i` of the address is upper case when it is a letter and nibble
`i` of Keccak-256 of the lower-case hex text is 8 or more.
-/

namespace EthereumWallet.Keys.Address

inductive Error where
  /-- Not "0x" followed by exactly 40 hex digits. -/
  | malformed
  /-- Mixed case that is not the ERC-55 form of the address. -/
  | checksum
  deriving DecidableEq, Repr

/-- The 20-byte address of a public point. -/
def ofPub (p : Secp.Pub) : ByteArray := (keccak256 (Secp.xyBytes p)).extract 12 32

/-- The address of a secret scalar; `none` for a scalar outside `1 .. n-1`. -/
def ofSecret (risk : SecretRisk) (k : Nat) : Option ByteArray :=
  (Secp.pubOfSecret risk k).map ofPub

/-- Lower-case hex of a byte string as ASCII bytes. -/
def hexLowerBytes (b : ByteArray) : ByteArray := (toHex b).toUTF8

/-- Hex digit `i` of the checksummed form. -/
def checksumChar (lower hash : ByteArray) (i : Nat) : Char :=
  let c := lower.get! i
  let nibble := if i % 2 = 0 then (hash.get! (i / 2)) >>> 4 else (hash.get! (i / 2)) &&& 15
  if 97 ≤ c ∧ 8 ≤ nibble then Char.ofNat (c.toNat - 32) else Char.ofNat c.toNat

/-- "0x" and the ERC-55 mixed-case hex of a 20-byte address. -/
def toChecksum (addr : ByteArray) : String :=
  let lower := hexLowerBytes addr
  let hash := keccak256 lower
  String.ofList ('0' :: 'x' :: (List.range lower.size).map (checksumChar lower hash))

/-- Read "0x" + 40 hex digits of any case, without checking the checksum. -/
def ofHexAnyCase? (s : String) : Option ByteArray :=
  let src := s.toUTF8
  if src.size ≠ 42 ∨ src.get! 0 ≠ 48 ∨ src.get! 1 ≠ 120 then none
  else hexLoop src 20 2 ByteArray.empty

/-- Strict ERC-55: accepted only if the text is exactly the checksummed form. -/
def ofChecksummed (s : String) : Except Error ByteArray :=
  match ofHexAnyCase? s with
  | none => .error .malformed
  | some addr => if toChecksum addr = s then .ok addr else .error .checksum

/-- Kind: soundness.
    Says: an address accepted by `ofChecksummed` re-encodes to exactly the text given,
    so no text with a wrong-case letter is accepted.
    Does not say: that every checksummed address is accepted (tested on the ERC-55
    vectors and on derived addresses, not proved), nor that Keccak is Keccak-256. -/
theorem ofChecksummed_sound (s : String) (addr : ByteArray) (h : ofChecksummed s = .ok addr) :
    toChecksum addr = s := by
  unfold ofChecksummed at h
  cases hx : ofHexAnyCase? s with
  | none => rw [hx] at h; cases h
  | some a =>
    rw [hx] at h
    by_cases hc : toChecksum a = s
    · simp [hc] at h; rw [← h]; exact hc
    · simp [hc] at h

end EthereumWallet.Keys.Address

open EthereumWallet.Keys in
#print axioms Address.ofChecksummed_sound
