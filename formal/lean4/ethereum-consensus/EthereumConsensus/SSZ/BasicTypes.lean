import EthereumConsensus.SSZ.ByteProof

/-!
# SSZ basic-type wire codecs and merkle roots

Pure Lean 4.33.1 implementation of the consensus SSZ basic Boolean and
uint64 encodings. Basic roots are the encoded value zero-padded to 32 bytes.
They are *not* SHA-256 of the bytes. This module does not provide composite
SSZ layouts, container offsets, BLS verification or beacon transitions.

Normative reference: ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1.
Tracking: factoidal-core issue #840; complete Ethereum goal #725.
-/

namespace EthereumConsensus.SSZ

inductive BasicCodecError where
  | invalidLength
  | noncanonicalBoolean
  | resourceLimit
  deriving BEq, DecidableEq, Repr

/-- Exactly eight little-endian bytes. The integer is a Lean UInt64 and
    therefore already has the consensus uint64 range. -/
def encodeUInt64 (value : UInt64) : ByteArray :=
  let n := value.toNat
  ((((((((ByteArray.empty
    |>.push (UInt8.ofNat (n % 256)))
    |>.push (UInt8.ofNat ((n / 256) % 256)))
    |>.push (UInt8.ofNat ((n / (256 ^ 2)) % 256)))
    |>.push (UInt8.ofNat ((n / (256 ^ 3)) % 256)))
    |>.push (UInt8.ofNat ((n / (256 ^ 4)) % 256)))
    |>.push (UInt8.ofNat ((n / (256 ^ 5)) % 256)))
    |>.push (UInt8.ofNat ((n / (256 ^ 6)) % 256)))
    |>.push (UInt8.ofNat ((n / (256 ^ 7)) % 256)))

/-- Decode only a complete eight-byte wire representation. Each byte is
    weighted by its little-endian power of 256. -/
def decodeUInt64 (bytes : ByteArray) : Except BasicCodecError UInt64 :=
  if _h : bytes.size = 8 then
    .ok <| UInt64.ofNat <|
      (List.range 8).foldl
        (fun acc i => acc + bytes[i]!.toNat * 256 ^ i) 0
  else .error .invalidLength

/-- SSZ Boolean values have one byte: false = 00, true = 01. -/
def encodeBool (value : Bool) : ByteArray :=
  ByteArray.empty.push (if value then 1 else 0)

/-- A Boolean wire value must use one of the two canonical byte values.
    Other one-byte encodings are invalid, not silently true. -/
def decodeBool (bytes : ByteArray) : Except BasicCodecError Bool :=
  if _h : bytes.size = 1 then
    if bytes[0]! == 0 then .ok false
    else if bytes[0]! == 1 then .ok true
    else .error .noncanonicalBoolean
  else .error .invalidLength

/-- Right-pad basic SSZ serialization bytes with zeroes to form a 32-byte
    Merkle chunk. Only used after a bounded basic-type width check. -/
def zeroPadBasic (bytes : ByteArray) : ByteArray := Id.run do
  let mut out := bytes
  for _ in [bytes.size:32] do
    out := out.push 0
  return out

/-- Only an admitted basic value (at most 32 bytes) can form a root.
    The 32-byte Chunk constructor checks the post-padding width. -/
def checkedBasicRoot (bytes : ByteArray) : Except BasicCodecError Chunk :=
  if bytes.size > 32 then .error .resourceLimit
  else
    match Chunk.ofBytes (zeroPadBasic bytes) with
    | .ok chunk => .ok chunk
    | .error _ => .error .invalidLength

def uint64Root (value : UInt64) : Except BasicCodecError Chunk :=
  checkedBasicRoot (encodeUInt64 value)

def boolRoot (value : Bool) : Except BasicCodecError Chunk :=
  checkedBasicRoot (encodeBool value)

/-- Says: each actual unsigned-64 serializer returns eight bytes.
    Does not say: an arbitrary byte string is an SSZ uint64. -/
theorem encodeUInt64_size (value : UInt64) :
    (encodeUInt64 value).size = 8 := by
  rfl

/-- Says: the public unsigned-64 decoder refuses a width other than eight.
    Does not say: arbitrary input types can be reinterpreted as uint64. -/
theorem decodeUInt64_wrong_width (bytes : ByteArray)
    (h : bytes.size ≠ 8) :
    decodeUInt64 bytes = .error .invalidLength := by
  simp [decodeUInt64, h]

/-- Says: Boolean encoding always writes one byte.
    Does not say: a one-byte input is necessarily a valid Boolean. -/
theorem encodeBool_size (value : Bool) :
    (encodeBool value).size = 1 := by
  cases value <;> rfl

/-- Says: encoding then decoding a Boolean is an identity at actual entries.
    Does not say: noncanonical bytes are accepted. -/
theorem decodeBool_encode (value : Bool) :
    decodeBool (encodeBool value) = .ok value := by
  cases value <;> rfl

/-- Says: the Boolean decoder rejects any wire length other than one.
    Does not say: all length-one values are canonical. -/
theorem decodeBool_wrong_width (bytes : ByteArray)
    (h : bytes.size ≠ 1) :
    decodeBool bytes = .error .invalidLength := by
  simp [decodeBool, h]

/-- Says: a one-byte Boolean with value two is refused, not coerced to true.
    Does not say: other noncanonical inputs are admitted. -/
theorem decodeBool_rejects_two :
    decodeBool (ByteArray.empty.push 2) = .error .noncanonicalBoolean := by
  rfl

/-- Says: the checked root refuses any input longer than one SSZ chunk.
    Does not say: a composite SSZ object is validated by this function. -/
theorem checkedBasicRoot_rejects_long (bytes : ByteArray)
    (h : bytes.size > 32) :
    checkedBasicRoot bytes = .error .resourceLimit := by
  simp [checkedBasicRoot, h]

/- Executable verdict inspection without assuming that Except has a BEq or
   DecidableEq instance in the pinned Lean toolchain. -/
private def expectedOk {α : Type} [BEq α]
    (result : Except BasicCodecError α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def expectedError {α : Type}
    (result : Except BasicCodecError α) (expected : BasicCodecError) : Bool :=
  match result with
  | .ok _ => false
  | .error err => err == expected

#guard (encodeUInt64 0).size == 8
#guard (encodeUInt64 255)[0]! == 255
#guard (encodeUInt64 256)[0]! == 0
#guard (encodeUInt64 256)[1]! == 1
#guard (encodeUInt64 65536)[2]! == 1
#guard expectedOk decodeUInt64 (encodeUInt64 0) 0
#guard expectedOk decodeUInt64 (encodeUInt64 1) 1
#guard expectedOk decodeUInt64 (encodeUInt64 255) 255
#guard expectedOk decodeUInt64 (encodeUInt64 256) 256
#guard expectedOk (decodeUInt64 (encodeUInt64 18446744073709551615)) 18446744073709551615
#guard expectedError decodeUInt64 ByteArray.empty .invalidLength
#guard expectedOk decodeBool (encodeBool false) false
#guard expectedOk decodeBool (encodeBool true) true
#guard expectedError decodeBool (ByteArray.empty.push 2) .noncanonicalBoolean
#guard expectedError decodeBool (ByteArray.empty.push 255) .noncanonicalBoolean
#guard expectedError decodeBool ByteArray.empty .invalidLength
#guard (uint64Root 256).toOption.map (fun chunk => chunk.bytes.size) == some 32
#guard (boolRoot true).toOption.map (fun chunk => chunk.bytes.size) == some 32

#print axioms EthereumConsensus.SSZ.encodeUInt64_size
#print axioms EthereumConsensus.SSZ.decodeUInt64_wrong_width
#print axioms EthereumConsensus.SSZ.encodeBool_size
#print axioms EthereumConsensus.SSZ.decodeBool_encode
#print axioms EthereumConsensus.SSZ.decodeBool_wrong_width
#print axioms EthereumConsensus.SSZ.decodeBool_rejects_two
#print axioms EthereumConsensus.SSZ.checkedBasicRoot_rejects_long

end EthereumConsensus.SSZ
