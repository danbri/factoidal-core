/-
Versioned bytes and public output for local ASK attestations.
Tracking: https://github.com/danbri/factoidal-core/issues/745.

This module describes a journal, not a cryptographic proof. Hashing is a
parameter; the executable edge supplies the existing HACL* SHA-256 binding.
The graph commitment binds the original byte sequence and a 32-byte salt.
It is not an RDF canonicalisation or a statement of data authenticity.
-/
import Init

namespace L4Factoidal.Attestation

/-- A failed computation has no accepted journal. Diagnostic strings stay
local; they are not part of the proof's public output. -/
inductive Error where
  | invalidInput (reason : String)
  | invalidPolicy (reason : String)
  | exhausted (phase : String)
  | resourceLimit (phase : String)
  | hashRefused
  deriving Repr, DecidableEq

/-- Eight bytes, unsigned big endian. Admission bounds every encoded Nat
below 2^31, so the UInt64 conversion cannot truncate accepted fields. -/
def u64be (n : Nat) : ByteArray :=
  let w := n.toUInt64
  ByteArray.mk #[(w >>> 56).toUInt8, (w >>> 48).toUInt8,
    (w >>> 40).toUInt8, (w >>> 32).toUInt8, (w >>> 24).toUInt8,
    (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

def lengthPrefixed (bytes : ByteArray) : ByteArray := u64be bytes.size ++ bytes

def domain (name : String) : ByteArray := name.toUTF8.push 0

def graphMessage (salt originalBytes : ByteArray) : ByteArray :=
  domain "factoidal.ask.graph.v1" ++ salt ++ lengthPrefixed originalBytes

def policyMessage (encodedPolicy : ByteArray) : ByteArray :=
  domain "factoidal.ask.policy.v1" ++ lengthPrefixed encodedPolicy

def contextMessage (context : ByteArray) : ByteArray :=
  domain "factoidal.ask.context.v1" ++ lengthPrefixed context

/-- A digest value carries its exact byte-length invariant. This says
nothing about collision resistance or an opaque FFI implementation. -/
structure Digest32 where
  bytes : ByteArray
  size_eq : bytes.size = 32

def hash32 (hash : ByteArray → ByteArray) (message : ByteArray) : Except Error Digest32 :=
  let bytes := hash message
  if h : bytes.size = 32 then .ok ⟨bytes, h⟩ else .error .hashRefused

/-- The four public ABI words. Policy and context authorization are verifier
obligations; an arbitrary policy returning true is not an eligibility proof. -/
structure Journal where
  graphCommitment : Digest32
  policyHash : Digest32
  contextHash : Digest32
  satisfied : Bool

def boolWord (b : Bool) : ByteArray :=
  (ByteArray.mk (Array.replicate 31 0)).push (if b then 1 else 0)

/-- Encoding theorem.
Says: the Boolean occupies one complete ABI word.
Does not say: the Boolean describes an authorised computation. -/
theorem boolWord_size (b : Bool) : (boolWord b).size = 32 := by
  cases b <;> rfl

/-- Solidity ABI encoding of (bytes32, bytes32, bytes32, bool), exactly 128 bytes. -/
def Journal.encode (j : Journal) : ByteArray :=
  j.graphCommitment.bytes ++ j.policyHash.bytes ++ j.contextHash.bytes ++ boolWord j.satisfied

/-- Structural encoding theorem.
Says: every constructed public journal has the exact verifier ABI size.
Does not say: the journal has a ZK proof or its hashes are authentic. -/
theorem Journal.encode_size (j : Journal) : j.encode.size = 128 := by
  simp only [Journal.encode, ByteArray.size_append, j.graphCommitment.size_eq,
    j.policyHash.size_eq, j.contextHash.size_eq, boolWord_size]

/-- Success-only output. Failure never produces an all-zero/default journal. -/
def publicOutput : Except Error Journal → Option ByteArray
  | .ok j => some j.encode
  | .error _ => none

/-- Failure isolation theorem.
Says: every failure has no publishable output, including exhaustion.
Does not say: a host cannot ignore this API or publish a different value. -/
theorem publicOutput_error (e : Error) : publicOutput (.error e) = none := rfl

def Error.code : Error → UInt8
  | .invalidInput _ | .invalidPolicy _ => 2
  | .exhausted _ => 3
  | .resourceLimit _ => 4
  | .hashRefused => 5

/-- Flat transport result: 0=successful false, 1=successful true,
2=invalid, 3=exhausted, 4=resource limit, 5=hash refusal.
Only success carries the 128-byte journal. -/
def abiResult : Except Error Journal → UInt8 × ByteArray
  | .ok j => (if j.satisfied then 1 else 0, j.encode)
  | .error e => (e.code, ByteArray.empty)

/-- Failure isolation theorem.
Says: every failure returns an empty ABI output buffer.
Does not say: native pointer ownership or host marshalling is proved. -/
theorem abiResult_error_empty (e : Error) : (abiResult (.error e)).2 = ByteArray.empty := rfl

#print axioms boolWord_size
#print axioms Journal.encode_size
#print axioms publicOutput_error
#print axioms abiResult_error_empty

end L4Factoidal.Attestation
