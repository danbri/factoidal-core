/-
L4Factoidal.CID.Multiformats — Controlled Identifiers v1.0 (W3C
Recommendation, 15 May 2025, https://www.w3.org/TR/cid-1.0/): §3.1 Base
Encode, §3.2 Base Decode, §2.4 Multibase, §2.5 Multihash, and the Multikey
headers of §2.2.2 (https://github.com/danbri/factoidal/issues/1100, item 5).

This is byte encoding, not cryptography (`skills/crypto-policy/SKILL.md`).
Nothing here touches a curve or a digest.

## §3.1 and §3.2

The algorithms read the bytes as one big-endian number and write it in the
target base; each leading zero byte is one copy of the first alphabet
character. `baseEncode` and `baseDecode?` compute the same output with
`Nat` arithmetic ("Any algorithm with equivalent output MAY be used", §2.4).
For base 58 with the base-58-btc alphabet that is exactly
`VC.Multibase.base58Encode`, and the `#guard`s in `CID/Tests.lean` check
that the two agree.

## The `u` header

§2.4 names `u` with the base-64-url-no-pad alphabet and says to apply §3.1.
§3.1 with base 64 is a big-number conversion, and that is NOT the RFC 4648
§5 bit-grouping that the Multibase specification and every Multikey
implementation use for `u` (for the one byte `ff`, §3.1 gives `D_` and
RFC 4648 gives `_w`). This module decodes and encodes `u` as RFC 4648
base64url without padding (`JOSE.Base64Url`), and keeps the literal §3.1
reading as `baseEncode` for comparison. The divergence is recorded in
`docs/designissues/2026-10-27-cid-1.0.md`.

Every function is total; decoders return `Option` or `Except`. Loops over
input-proportional data are tail calls.
-/
import L4Factoidal.VC.Multibase
import L4Factoidal.JOSE.Base64Url

namespace L4Factoidal.CID

open L4Factoidal.VC.Multibase (Bytes base58Alphabet base58Decode? base58Encode)

/-! ## §3.1 Base Encode and §3.2 Base Decode -/

/-- The base-64-url-no-pad alphabet of §2.4, in order. -/
def base64UrlAlphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList

/-- The bytes as one big-endian number (a left fold: a loop). -/
def bytesValue (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The digits of `n` in base `base`, most significant first, put in front
of `acc`. `0 ↦ acc`. A tail call on a decreasing quotient. -/
def digitsAcc (base : Nat) (n : Nat) (acc : List Nat) : List Nat :=
  if _h : n = 0 ∨ base < 2 then acc
  else digitsAcc base (n / base) (n % base :: acc)
termination_by n
decreasing_by
  have hn : 0 < n := by omega
  have hb : 1 < base := by omega
  exact Nat.div_lt_self hn hb

/-- The big-endian bytes of `n`, put in front of `acc`. -/
def natBytesAcc (n : Nat) (acc : Bytes) : Bytes :=
  if h : n = 0 then acc
  else natBytesAcc (n / 256) ((n % 256).toUInt8 :: acc)
termination_by n
decreasing_by
  have hn : 0 < n := by omega
  exact Nat.div_lt_self hn (by decide)

/-- §3.1 Base Encode: `bytes`, `targetBase`, `baseAlphabet` → the
base-encoded string. One alphabet[0] per leading zero byte, then the value
of the remaining bytes in the target base. -/
def baseEncode (bytes : Bytes) (targetBase : Nat) (alphabet : List Char) : String :=
  let zeroes := (bytes.takeWhile (· == 0)).length
  let z := alphabet.headD '?'
  let ds := digitsAcc targetBase (bytesValue (bytes.dropWhile (· == 0))) []
  String.ofList (List.replicate zeroes z ++ ds.map (fun d => alphabet.getD d '?'))

/-- Index of a character in an alphabet. -/
def alphabetIndex? (alphabet : List Char) (c : Char) : Option Nat := alphabet.idxOf? c

/-- Digit values of a string; `none` at the first character outside the
alphabet. The accumulator holds the value so far (a loop). -/
def digitsValue? (alphabet : List Char) (base : Nat) : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
      match alphabetIndex? alphabet c with
      | some d => digitsValue? alphabet base cs (acc * base + d)
      | none => none

/-- §3.2 Base Decode: `sourceEncoding`, `sourceBase`, `baseAlphabet` → the
bytes. One zero byte per leading alphabet[0]; `none` for a character
outside the alphabet. -/
def baseDecode? (source : String) (sourceBase : Nat) (alphabet : List Char) : Option Bytes :=
  let cs := source.toList
  let z := alphabet.headD '?'
  let zeroes := (cs.takeWhile (· == z)).length
  (digitsValue? alphabet sourceBase (cs.dropWhile (· == z)) 0).map fun v =>
    List.replicate zeroes 0 ++ natBytesAcc v []

/-! ## §2.4 Multibase -/

/-- The two Multibase headers of §2.4. -/
inductive MultibaseHeader where
  /-- `z`, base-58-btc. -/
  | base58btc
  /-- `u`, base-64-url-no-pad (RFC 4648 §5, no padding; see the header). -/
  | base64url
  deriving Repr, DecidableEq

def MultibaseHeader.char : MultibaseHeader → Char
  | .base58btc => 'z'
  | .base64url => 'u'

/-- Encode bytes as a Multibase string with the given header. -/
def multibaseEncode (h : MultibaseHeader) (bs : Bytes) : String :=
  match h with
  | .base58btc => "z" ++ base58Encode bs
  | .base64url => "u" ++ JOSE.Base64Url.encode ⟨bs.toArray⟩

/-- Decode a Multibase string of either header; `none` for another header
or a character outside the alphabet. -/
def multibaseDecode? (s : String) : Option (MultibaseHeader × Bytes) :=
  match s.toList with
  | 'z' :: rest => (base58Decode? (String.ofList rest)).map (.base58btc, ·)
  | 'u' :: rest => (JOSE.Base64Url.decode (String.ofList rest)).map fun a => (.base64url, a.data.toList)
  | _ => none

/-- Is the string in the lexical space of the `multibase` datatype (§4.3.1)? -/
def isMultibase (s : String) : Bool := (multibaseDecode? s).isSome

/-! ## §2.5 Multihash -/

/-- The four Multihash identifiers of §2.5. -/
inductive HashId where
  | sha2_256
  | sha2_384
  | sha3_256
  | sha3_384
  deriving Repr, DecidableEq

/-- The Multihash header (one varint byte: every code is below 0x80). -/
def HashId.code : HashId → UInt8
  | .sha2_256 => 0x12
  | .sha2_384 => 0x20
  | .sha3_256 => 0x16
  | .sha3_384 => 0x15

/-- The digest length in bytes. -/
def HashId.length : HashId → Nat
  | .sha2_256 => 32
  | .sha2_384 => 48
  | .sha3_256 => 32
  | .sha3_384 => 48

def HashId.all : List HashId := [.sha2_256, .sha2_384, .sha3_256, .sha3_384]

def HashId.ofCode? (c : UInt8) : Option HashId := HashId.all.find? (·.code == c)

/-- Why a Multihash value does not decode. -/
inductive MultihashError where
  | empty
  | unknownHeader (code : Nat)
  | lengthMismatch (declared actual : Nat)
  deriving Repr, DecidableEq

/-- §2.5 encode: header varint, length varint, digest. Every length of the
table is below 0x80, so each varint is one byte. -/
def multihashEncode (h : HashId) (digest : Bytes) : Bytes :=
  h.code :: digest.length.toUInt8 :: digest

/-- §2.5 decode: remove the header, remove the length, and take the
digest, which MUST have the length of the header and the length the value
states. -/
def multihashDecode (bs : Bytes) : Except MultihashError (HashId × Bytes) :=
  match bs with
  | c :: l :: digest =>
      match HashId.ofCode? c with
      | none => .error (.unknownHeader c.toNat)
      | some h =>
          if l.toNat != h.length then .error (.lengthMismatch l.toNat h.length)
          else if digest.length != h.length then .error (.lengthMismatch h.length digest.length)
          else .ok (h, digest)
  | [c] => .error (.unknownHeader c.toNat)
  | [] => .error .empty

/-! ## §2.2.2 Multikey headers -/

/-- The key types of the §2.2.2 tables. -/
inductive KeyType where
  | p256
  | p384
  | ed25519
  | bls12381g2
  | sm2
  deriving Repr, DecidableEq

def KeyType.all : List KeyType := [.p256, .p384, .ed25519, .bls12381g2, .sm2]

/-- The two-byte varint header of a PUBLIC key of this type. -/
def KeyType.publicHeader : KeyType → Bytes
  | .p256 => [0x80, 0x24]
  | .p384 => [0x81, 0x24]
  | .ed25519 => [0xed, 0x01]
  | .bls12381g2 => [0xeb, 0x01]
  | .sm2 => [0x86, 0x24]

/-- The key length after the header (compressed points for the curves). -/
def KeyType.publicLength : KeyType → Nat
  | .p256 => 33
  | .p384 => 49
  | .ed25519 => 32
  | .bls12381g2 => 96
  | .sm2 => 33

/-- The two-byte varint header of a SECRET key of this type. -/
def KeyType.secretHeader : KeyType → Bytes
  | .p256 => [0x86, 0x26]
  | .p384 => [0x87, 0x26]
  | .ed25519 => [0x80, 0x26]
  | .bls12381g2 => [0x80, 0x30]
  | .sm2 => [0x90, 0x26]

def KeyType.name : KeyType → String
  | .p256 => "P-256"
  | .p384 => "P-384"
  | .ed25519 => "Ed25519"
  | .bls12381g2 => "BLS12-381 G2"
  | .sm2 => "SM2"

/-- Why a `publicKeyMultibase` value is not a public Multikey. -/
inductive MultikeyError where
  /-- Not a Multibase value, or not base-58-btc (§2.2.2: "MUST then be
  encoded using the base-58-btc alphabet"). -/
  | notBase58btc
  /-- The header is a SECRET-key header of the table. -/
  | secretKeyHeader
  /-- The header is in neither table. -/
  | unknownHeader
  /-- The key after the header has the wrong length for its type. -/
  | wrongLength (kt : KeyType) (got : Nat)
  deriving Repr, DecidableEq

def MultikeyError.describe : MultikeyError → String
  | .notBase58btc => "publicKeyMultibase is not a base-58-btc Multibase value"
  | .secretKeyHeader => "publicKeyMultibase has a secret-key header"
  | .unknownHeader => "publicKeyMultibase has no public-key header of CID 1.0 §2.2.2"
  | .wrongLength kt n => s!"publicKeyMultibase holds a {kt.name} key of {n} bytes, not {kt.publicLength}"

/-- Split off a two-byte header. -/
def header2? : Bytes → Option (Bytes × Bytes)
  | a :: b :: rest => some ([a, b], rest)
  | _ => none

/-- Decode a Multikey PUBLIC key (§2.2.2): base-58-btc, a public header of
the table, and the length of that type. A secret-key header and an
unknown header are errors ("Implementations that adhere to this
specification will raise errors"). -/
def decodePublicMultikey (s : String) : Except MultikeyError (KeyType × Bytes) :=
  match multibaseDecode? s with
  | some (.base58btc, bs) =>
      match header2? bs with
      | none => .error .unknownHeader
      | some (h, key) =>
          match KeyType.all.find? (·.publicHeader == h) with
          | some kt =>
              if key.length == kt.publicLength then .ok (kt, key)
              else .error (.wrongLength kt key.length)
          | none =>
              if KeyType.all.any (·.secretHeader == h) then .error .secretKeyHeader
              else .error .unknownHeader
  | _ => .error .notBase58btc

/-- The Multikey value of a public key: `z`, base-58-btc of header ++ key. -/
def encodePublicMultikey (kt : KeyType) (key : Bytes) : String :=
  multibaseEncode .base58btc (kt.publicHeader ++ key)

/-! ## Theorems -/

/-- A decoded Multikey has the length of its type. -/
theorem decodePublicMultikey_length {s : String} {kt : KeyType} {key : Bytes}
    (h : decodePublicMultikey s = .ok (kt, key)) : key.length = kt.publicLength := by
  unfold decodePublicMultikey at h
  split at h
  · split at h
    · simp at h
    · split at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rename_i hl
          simpa using hl
        · simp at h
      · split at h <;> simp at h
  · simp at h

/-- No public header of the table is a secret header of the table, so a
secret key is never decoded as a public one. -/
theorem public_secret_headers_disjoint :
    ∀ a ∈ KeyType.all, ∀ b ∈ KeyType.all, a.publicHeader ≠ b.secretHeader := by
  decide

/-- The Multihash decoder returns a digest of the declared length. -/
theorem multihashDecode_length {bs : Bytes} {h : HashId} {d : Bytes}
    (hd : multihashDecode bs = .ok (h, d)) : d.length = h.length := by
  unfold multihashDecode at hd
  split at hd
  · split at hd
    · simp at hd
    · split at hd
      · simp at hd
      · split at hd
        · simp at hd
        · rename_i h' _ hlen
          simp only [Except.ok.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          simpa using hlen
  · simp at hd
  · simp at hd

end L4Factoidal.CID
