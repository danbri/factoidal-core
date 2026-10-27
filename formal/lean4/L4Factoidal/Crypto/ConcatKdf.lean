/-
L4Factoidal.Crypto.ConcatKdf — the single-step key derivation function of
NIST SP 800-56A §5.8.1 ("Concat KDF"), as JWE (RFC 7518 §4.6.2) and XML
Encryption 1.1 (§5.4.1, `http://www.w3.org/2009/xmlenc11#ConcatKDF`) use
it. For https://github.com/danbri/factoidal/issues/1083.

## Crypto policy

`skills/crypto-policy/SKILL.md`: a derived construction over an unmodified
hash may be pure Lean. The Concat KDF is such a construction: SP 800-56A
§5.8.1 defines it as a chain of hash calls over a counter. The hash is a
PARAMETER (`KdfHash`); the library instances use the pure FIPS 180-4
functions of `Crypto/SHA2.lean` and `Crypto/SHA1.lean`, so the `#guard`s
below run at build time. A caller at an executable edge may pass
`sha256Hacl` (`Crypto/SHA2Native.lean`) in a `KdfHash` of its own.

## The function (SP 800-56A §5.8.1)

    reps = ceil(keydatalen / hashlen)
    if reps > 2^32 - 1: ABORT
    for counter = 1 .. reps:
      K(counter) = H(counter || Z || OtherInfo)    -- counter: 32-bit big-endian
    DerivedKeyingMaterial = leftmost keydatalen bits of K(1) || ... || K(reps)

`concatKdf` takes `keyDataLen` in OCTETS, because the result is a
`ByteArray`. JWE and XML Encryption derive whole-octet keys only.
`keyDataLen = 0` is refused: an empty derivation cannot be told apart
from a refusal.

## JWE OtherInfo (RFC 7518 §4.6.2), quoted

  "AlgorithmID: The AlgorithmID value is of the form Datalen || Data, where
  Data is a variable-length string of zero or more octets, and Datalen is a
  fixed-length, big-endian 32-bit counter that indicates the length (in
  octets) of Data. In the Direct Key Agreement case, Data is set to the
  octets of the ASCII representation of the "enc" Header Parameter value.
  In the Key Agreement with Key Wrapping case, Data is set to the octets of
  the ASCII representation of the "alg" (algorithm) Header Parameter
  value."

  PartyUInfo and PartyVInfo: the same `Datalen || Data` form over the
  base64url-decoded `apu` and `apv` (empty when absent).

  "SuppPubInfo: This is set to the keydatalen represented as a 32-bit
  big-endian integer."  "SuppPrivInfo: This is set to the empty octet
  sequence."

`jweOtherInfo?` builds exactly that; keydatalen there is in BITS, as the
RFC says. The RFC 7518 Appendix C example is a `#guard` below.

## XML Encryption 1.1 OtherInfo (§5.4.1), quoted

  "In [SP800-56A], AlgorithmID, PartyUInfo, PartyVInfo, SuppPubInfo and
  SuppPrivInfo attributes are all defined as arbitrary-length bitstrings,
  thus they may need to be padded in order to be encoded into hexBinary for
  XML Encryption. The following padding and encoding method MUST be used
  when encoding bitstring values for the AlgorithmID, PartyUInfo,
  PartyVInfo, SuppPubInfo and SuppPrivInfo:
    1. The bitstring is divided into octets using big-endian encoding. If
       the length of the bitstring is not a multiple of 8 then add padding
       bits (value 0) as necessary to the last octet to make it a multiple
       of 8.
    2. Prepend one octet to the octets string from step 1. This octet shall
       identify (in a big-endian representation) the number of padding bits
       added to the last octet in step 1.
    3. Encode the octet string resulting from step 2 as a hexBinary
       string."

  "Example: the bitstring 11011, which is 5 bits long, gets 3 additional
  padding bits to become the bitstring 11011000 (or D8 in hex). This
  bitstring is then prepended with one octet identifying the number of
  padding bits to become the octet string (in hex) 03D8, which then finally
  is encoded as a hexBinary string value of "03D8"."

  "Note that as specified in [SP800-56A], these attributes shall be
  concatenated to form a bit string "OtherInfo" that is used with the key
  derivation function. The concatenation SHALL be done using the original,
  unpadded bit string values."

  "Their presence is optional but AlgorithmID, PartyVInfo and PartyUInfo
  MUST be present for applications that need to comply with [SP800-56A]."

`decodePadded?` reads one attribute value (its hexBinary already decoded
to octets) into a `BitString`: the first octet is the padding count, which
must be at most 7 (and 0 when no octet follows), and the padding bits must
be zero, as step 1 says. `xmlEncOtherInfo?` concatenates the unpadded bit
strings in the order AlgorithmID, PartyUInfo, PartyVInfo, SuppPubInfo,
SuppPrivInfo; an absent attribute is the empty bit string.

## Known gap (expected failure)

When the unpadded bit strings do not add up to a whole number of octets,
`counter || Z || OtherInfo` is not an octet string, and the hash functions
of this tree take octet strings only. `xmlEncOtherInfo?` then answers
`none`. The §5.4.1 example (8 + 5 + 5 = 18 bits) is such a case. Open
issue: https://github.com/danbri/factoidal/issues/1097. The `#guard`
marked EXPECTED FAILURE below asserts the refusal and fails the build when
the case starts to be accepted.

## Loops

Every walk over input-proportional data is a structural tail recursion
with an accumulator (`deriveLoop`, `pushBits`, `concatBitsLoop`), per
CLAUDE.md and `tools/lean-tail-recursion-audit.py`.
-/
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.SHA1

namespace L4Factoidal.Crypto.ConcatKdf

/-- A hash function `H` of SP 800-56A §5.8.1 with its output length
`hashlen` in octets. -/
structure KdfHash where
  name : String
  digest : ByteArray → ByteArray
  outLen : Nat

/-- SHA-256 (pure Lean, FIPS 180-4). The JWE digest (RFC 7518 §4.6.2) and
an XML Encryption 1.1 MUST (§5.4.1). -/
def sha256Hash : KdfHash := ⟨"SHA-256", L4Factoidal.Crypto.sha256, 32⟩
/-- SHA-1 (pure Lean). XML Encryption 1.1 §5.4.1: "Compliant
implementations MUST support SHA-256 and SHA-1 (support for SHA-1 is
present only for backwards-compatibility reasons)". -/
def sha1Hash : KdfHash := ⟨"SHA-1", L4Factoidal.Crypto.sha1, 20⟩
/-- SHA-384 (pure Lean). OPTIONAL in XML Encryption 1.1 §5.4.1. -/
def sha384Hash : KdfHash := ⟨"SHA-384", L4Factoidal.Crypto.sha384, 48⟩
/-- SHA-512 (pure Lean). OPTIONAL in XML Encryption 1.1 §5.4.1. -/
def sha512Hash : KdfHash := ⟨"SHA-512", L4Factoidal.Crypto.sha512, 64⟩

/-- The largest value of a 32-bit unsigned counter. -/
def maxU32 : Nat := 4294967295

/-- `n` as a 32-bit big-endian octet string (callers check `n ≤ maxU32`). -/
def u32be (n : Nat) : ByteArray :=
  ⟨#[(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8,
     (n / 256 % 256).toUInt8, (n % 256).toUInt8]⟩

/-- `remaining` more rounds of `K(counter) = H(counter || Z || OtherInfo)`,
appended to `acc`. Structural tail recursion on `remaining`. -/
def deriveLoop (h : KdfHash) (z otherInfo : ByteArray) :
    (remaining counter : Nat) → (acc : ByteArray) → ByteArray
  | 0, _, acc => acc
  | r + 1, counter, acc =>
      deriveLoop h z otherInfo r (counter + 1)
        (acc ++ h.digest (u32be counter ++ z ++ otherInfo))

/-- The Concat KDF of SP 800-56A §5.8.1. `keyDataLen` is in OCTETS. `none`
when `keyDataLen = 0`, when the hash has no output, and when
`reps > 2^32 - 1` (the §5.8.1 ABORT). -/
def concatKdf (h : KdfHash) (z : ByteArray) (keyDataLen : Nat)
    (otherInfo : ByteArray) : Option ByteArray :=
  if keyDataLen = 0 ∨ h.outLen = 0 then none
  else
    let reps := (keyDataLen + h.outLen - 1) / h.outLen
    if reps > maxU32 then none
    else some ((deriveLoop h z otherInfo reps 1 ByteArray.empty).extract 0 keyDataLen)

/-! ## JWE (RFC 7518 §4.6.2) -/

/-- `Datalen || Data` with a 32-bit big-endian `Datalen`; `none` when
`Data` is longer than a 32-bit counter can state. -/
def lengthPrefixed? (data : ByteArray) : Option ByteArray :=
  if data.size > maxU32 then none else some (u32be data.size ++ data)

/-- The JWE OtherInfo of RFC 7518 §4.6.2: `AlgorithmID || PartyUInfo ||
PartyVInfo || SuppPubInfo`, SuppPrivInfo empty. `algId` is the ASCII of
`enc` (direct key agreement) or of `alg` (key agreement with key wrapping);
`apu` and `apv` are the base64url-decoded header values (empty when
absent); `keyDataLenBits` is keydatalen in BITS. -/
def jweOtherInfo? (algId apu apv : ByteArray) (keyDataLenBits : Nat) :
    Option ByteArray := do
  if keyDataLenBits > maxU32 then none
  let a ← lengthPrefixed? algId
  let u ← lengthPrefixed? apu
  let v ← lengthPrefixed? apv
  pure (a ++ u ++ v ++ u32be keyDataLenBits)

/-- JWE ECDH-ES key derivation (RFC 7518 §4.6.2): Concat KDF with SHA-256
over the JWE OtherInfo. `keyDataLenBits` must be a multiple of 8 (every JWE
key length is). -/
def jweDerive? (z algId apu apv : ByteArray) (keyDataLenBits : Nat) :
    Option ByteArray := do
  if keyDataLenBits % 8 ≠ 0 then none
  let other ← jweOtherInfo? algId apu apv keyDataLenBits
  concatKdf sha256Hash z (keyDataLenBits / 8) other

/-! ## XML Encryption 1.1 (§5.4.1) -/

/-- An SP 800-56A bit string: the octets of step 1 of XML Encryption 1.1
§5.4.1 and the count of zero padding bits at the end of the last octet.
Its length in bits is `8 * bytes.size - padBits`. -/
structure BitString where
  bytes : ByteArray
  padBits : Nat

/-- The length in bits. -/
def BitString.bitLen (b : BitString) : Nat := 8 * b.bytes.size - b.padBits

/-- The empty bit string (an absent attribute, or the value `00`). -/
def BitString.empty : BitString := ⟨ByteArray.empty, 0⟩

/-- Read one XML Encryption 1.1 §5.4.1 attribute value, given as the octets
of its hexBinary: first octet the padding count. `none` when the value is
empty, the count is more than 7, the count is not 0 with no octet after it,
or a padding bit is not zero. -/
def decodePadded? (v : ByteArray) : Option BitString :=
  if v.size = 0 then none
  else
    let p := (v.get! 0).toNat
    let content := v.extract 1 v.size
    if p > 7 then none
    else if content.size = 0 then (if p = 0 then some BitString.empty else none)
    else
      let last := (content.get! (content.size - 1)).toNat
      if last % (2 ^ p) ≠ 0 then none else some ⟨content, p⟩

/-- Bit `j` (0 is the most significant bit of octet 0) of `b`. -/
def bitAt (b : ByteArray) (j : Nat) : Nat :=
  (b.get! (j / 8)).toNat / 2 ^ (7 - j % 8) % 2

/-- The state of a bit-level concatenation: whole octets, then `nCur`
pending bits whose value is `cur`. -/
structure BitAcc where
  out : ByteArray
  cur : Nat
  nCur : Nat

/-- Append bits `j .. j + remaining - 1` of `b` to the accumulator.
Structural tail recursion on `remaining`. -/
def pushBits (b : ByteArray) : (remaining j : Nat) → BitAcc → BitAcc
  | 0, _, acc => acc
  | r + 1, j, acc =>
      let cur := acc.cur * 2 + bitAt b j
      let acc' : BitAcc :=
        if acc.nCur + 1 = 8 then ⟨acc.out.push cur.toUInt8, 0, 0⟩
        else ⟨acc.out, cur, acc.nCur + 1⟩
      pushBits b r (j + 1) acc'

/-- Append each bit string in turn. Structural tail recursion on the
list. An octet-aligned accumulator and a component with no padding take
the octet copy; every other case walks bits. -/
def concatBitsLoop : List BitString → BitAcc → BitAcc
  | [], acc => acc
  | s :: rest, acc =>
      let acc' :=
        if acc.nCur = 0 ∧ s.padBits = 0 then { acc with out := acc.out ++ s.bytes }
        else pushBits s.bytes s.bitLen 0 acc
      concatBitsLoop rest acc'

/-- The concatenation of bit strings as an octet string, or `none` when its
length in bits is not a multiple of 8
(https://github.com/danbri/factoidal/issues/1097). -/
def concatBits? (parts : List BitString) : Option ByteArray :=
  let acc := concatBitsLoop parts ⟨ByteArray.empty, 0, 0⟩
  if acc.nCur = 0 then some acc.out else none

/-- The five attributes of `xenc11:ConcatKDFParams`, each the octets of its
hexBinary value, `none` when the attribute is absent. -/
structure XmlEncParams where
  algorithmId : Option ByteArray := none
  partyUInfo : Option ByteArray := none
  partyVInfo : Option ByteArray := none
  suppPubInfo : Option ByteArray := none
  suppPrivInfo : Option ByteArray := none

/-- One attribute: absent is the empty bit string; present is decoded. -/
def attrBits? : Option ByteArray → Option BitString
  | none => some BitString.empty
  | some v => decodePadded? v

/-- The OtherInfo of XML Encryption 1.1 §5.4.1: the unpadded bit strings
of AlgorithmID, PartyUInfo, PartyVInfo, SuppPubInfo and SuppPrivInfo,
concatenated. `none` on a malformed attribute and on a total length that
is not a whole number of octets
(https://github.com/danbri/factoidal/issues/1097). -/
def xmlEncOtherInfo? (p : XmlEncParams) : Option ByteArray := do
  let a ← attrBits? p.algorithmId
  let u ← attrBits? p.partyUInfo
  let v ← attrBits? p.partyVInfo
  let s ← attrBits? p.suppPubInfo
  let r ← attrBits? p.suppPrivInfo
  concatBits? [a, u, v, s, r]

/-- XML Encryption 1.1 ConcatKDF: `keyLen` octets from `z` with the hash
of `ds:DigestMethod`. -/
def xmlEncDerive? (h : KdfHash) (z : ByteArray) (keyLen : Nat)
    (p : XmlEncParams) : Option ByteArray := do
  let other ← xmlEncOtherInfo? p
  concatKdf h z keyLen other

/-! ## Build-time checks -/

private def bytesOfList (l : List Nat) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩

-- RFC 7518 Appendix C: Z.
private def rfc7518Z : ByteArray := bytesOfList
  [158, 86, 217, 29, 129, 113, 53, 211, 114, 131, 66, 131, 191, 132,
   38, 156, 251, 49, 110, 163, 218, 128, 106, 72, 246, 218, 167, 121,
   140, 254, 144, 196]

-- RFC 7518 Appendix C: the OtherInfo octets.
#guard jweOtherInfo? "A128GCM".toUTF8 "Alice".toUTF8 "Bob".toUTF8 128 ==
  some (bytesOfList [0, 0, 0, 7, 65, 49, 50, 56, 71, 67, 77, 0, 0, 0, 5, 65,
    108, 105, 99, 101, 0, 0, 0, 3, 66, 111, 98, 0, 0, 0, 128])

-- RFC 7518 Appendix C: the derived key, base64url VqqN6vgjbSBcIijNcacQGg.
#guard jweDerive? rfc7518Z "A128GCM".toUTF8 "Alice".toUTF8 "Bob".toUTF8 128 ==
  some (bytesOfList [86, 170, 141, 234, 248, 35, 109, 32, 92, 34, 40, 205,
    113, 167, 16, 26])

-- Two rounds: a 48-octet key from SHA-256 is K(1) || first 16 octets of K(2),
-- and its first 16 octets equal the 16-octet derivation.
#guard (concatKdf sha256Hash rfc7518Z 48 ByteArray.empty).map (·.size) == some 48
#guard ((concatKdf sha256Hash rfc7518Z 48 ByteArray.empty).map (·.extract 0 16)) ==
  concatKdf sha256Hash rfc7518Z 16 ByteArray.empty
#guard (concatKdf sha256Hash rfc7518Z 48 ByteArray.empty).map (·.extract 32 48) ==
  some ((L4Factoidal.Crypto.sha256 (u32be 2 ++ rfc7518Z)).extract 0 16)

-- Refusals.
#guard concatKdf sha256Hash rfc7518Z 0 ByteArray.empty == none
#guard jweDerive? rfc7518Z "A128GCM".toUTF8 ByteArray.empty ByteArray.empty 127 == none

-- XML Encryption 1.1 §5.4.1 padding: the spec example 03D8 is the 5 bits 11011.
#guard (decodePadded? (bytesOfList [3, 0xD8])).map (·.bitLen) == some 5
#guard decodePadded? (bytesOfList [3, 0xD9]) |>.isNone      -- a padding bit is 1
#guard decodePadded? (bytesOfList [8, 0x00]) |>.isNone      -- count above 7
#guard decodePadded? (bytesOfList [1]) |>.isNone            -- count with no octet
#guard decodePadded? ByteArray.empty |>.isNone              -- no count octet
#guard (decodePadded? (bytesOfList [0])).map (·.bitLen) == some 0

-- Octet-aligned attributes concatenate as octets (the common case).
#guard xmlEncOtherInfo?
    { algorithmId := some (bytesOfList [0, 0xAA]),
      partyUInfo := some (bytesOfList [0, 1, 2]),
      partyVInfo := some (bytesOfList [0, 3]) } ==
  some (bytesOfList [0xAA, 1, 2, 3])

-- Non-zero padding that a later component re-aligns: 4 bits 1010 then
-- 4 bits 0101 is the octet 0xA5.
#guard xmlEncOtherInfo?
    { partyUInfo := some (bytesOfList [4, 0xA0]),
      partyVInfo := some (bytesOfList [4, 0x50]) } ==
  some (bytesOfList [0xA5])

-- EXPECTED FAILURE, https://github.com/danbri/factoidal/issues/1097: the
-- XML Encryption 1.1 §5.4.1 example (AlgorithmID 0000, PartyUInfo 03D8,
-- PartyVInfo 03D0; 8 + 5 + 5 = 18 bits) is refused today. When the case is
-- accepted this guard fails: then check the derived key against an
-- independent implementation, assert it here, and close the issue.
#guard xmlEncOtherInfo?
    { algorithmId := some (bytesOfList [0, 0]),
      partyUInfo := some (bytesOfList [3, 0xD8]),
      partyVInfo := some (bytesOfList [3, 0xD0]) } == none

end L4Factoidal.Crypto.ConcatKdf
