/-
L4Factoidal.Qlvr.Id — the 64-bit QLever `Id` (Factoidal/qlvr,
https://github.com/danbri/factoidal/issues/778).

Format record: docs/designissues/2026-10-11-qlever-index-format.md, section 1.
Bits 63..60 hold the datatype tag, bits 59..0 the payload
(`global/FoldedValueId.h:36-37` at QLever commit ceace86). Every permutation
is sorted by the unsigned value of the 64 bits, so `Id` order is `UInt64`
order.

Nothing here reads a file or loops over input-proportional data.
-/

namespace L4Factoidal.Qlvr

/-- A QLever `Id`: the raw 64 bits as stored in a column. -/
structure Id where
  bits : UInt64
  deriving BEq, Repr, Inhabited, Hashable

instance : Ord Id := ⟨fun a b => compare a.bits b.bits⟩

def payloadMask : UInt64 := 0x0FFFFFFFFFFFFFFF

namespace Id

/-- The datatype tag, bits 63..60 (`global/Datatype.h:24-49`). -/
@[inline] def tag (x : Id) : Nat := (x.bits >>> 60).toNat

/-- The payload, bits 59..0. -/
@[inline] def payload (x : Id) : UInt64 := x.bits &&& payloadMask

/-- The `Id` of vocabulary entry `i` (tag 4). -/
def ofVocabIndex (i : Nat) : Id := ⟨((4 : UInt64) <<< 60) ||| (i.toUInt64 &&& payloadMask)⟩

/-- The `Id` of the integer `i` (tag 2, 60-bit two's complement). -/
def ofInt (i : Int) : Id :=
  let p : UInt64 := if i < 0 then (UInt64.ofNat (2 ^ 60 - i.natAbs)) else UInt64.ofNat i.toNat
  ⟨((2 : UInt64) <<< 60) ||| (p &&& payloadMask)⟩

end Id

/-- The decoded content of an `Id`. -/
inductive Value where
  /-- tag 0; the only valid Undefined `Id` is 0 (`FoldedValueId.h:241`) -/
  | undefined
  /-- tag 1: bit 0 is the value; bit 1 says the lexical form was `0`/`1`
      (`FoldedValueId.h:285-312`) -/
  | bool (value lexical01 : Bool)
  /-- tag 2: a 60-bit two's-complement integer -/
  | int (i : Int)
  /-- tag 3: the IEEE 754 binary64 bits, shifted left 4 (the 4 lowest
      mantissa bits were dropped at index time and are 0 here) -/
  | double (bits : UInt64)
  /-- tag 4: position in the vocabulary -/
  | vocabIndex (i : Nat)
  /-- tag 5: a runtime pointer; never in index files -/
  | localVocabIndex (p : Nat)
  | secondaryVocabIndex (i : Nat)
  | textRecordIndex (i : Nat)
  /-- tag 8: `DateYearOrDuration` bits (not decoded further here) -/
  | date (payload : Nat)
  /-- tag 9: two 30-bit quantised coordinates (not decoded further here) -/
  | geoPoint (payload : Nat)
  | wordVocabIndex (i : Nat)
  /-- tag 11: blank node number, printed `_:bn<n>` -/
  | blankNodeIndex (n : Nat)
  /-- tag 12: an IRI encoded from a configured prefix -/
  | encodedVal (payload : Nat)
  /-- tag 13..15, or tag 0 with a non-zero payload -/
  | invalid (tag payload : Nat)
  deriving Repr, BEq, Inhabited

/-- Sign-extend a 60-bit two's-complement payload (`util/NBitInteger.h:19-28`). -/
def int60 (p : UInt64) : Int :=
  if p &&& ((1 : UInt64) <<< 59) != 0 then Int.ofNat p.toNat - Int.ofNat (2 ^ 60) else Int.ofNat p.toNat

/-- Decode an `Id` (`global/FoldedValueId.h`). -/
def Id.decode (x : Id) : Value :=
  let p := x.payload
  match x.tag with
  | 0 => if p == 0 then .undefined else .invalid 0 p.toNat
  | 1 => .bool (p &&& 1 != 0) (p &&& 2 != 0)
  | 2 => .int (int60 p)
  | 3 => .double (x.bits <<< 4)
  | 4 => .vocabIndex p.toNat
  | 5 => .localVocabIndex p.toNat
  | 6 => .secondaryVocabIndex p.toNat
  | 7 => .textRecordIndex p.toNat
  | 8 => .date p.toNat
  | 9 => .geoPoint p.toNat
  | 10 => .wordVocabIndex p.toNat
  | 11 => .blankNodeIndex p.toNat
  | 12 => .encodedVal p.toNat
  | t => .invalid t p.toNat

-- Hexdumps from the format record, section 1.
#guard (Id.decode ⟨0x4000000000021740⟩) == .vocabIndex 137024
#guard (Id.decode ⟨0x20000000000000b8⟩) == .int 184
#guard (Id.decode ⟨0x20000000000007ea⟩) == .int 2026
#guard (Id.decode ⟨0x2FFFFFFFFFFFFFFF⟩) == .int (-1)
#guard (Id.decode ⟨0x2800000000000000⟩) == .int (-(2 ^ 59))
#guard (Id.decode (Id.ofInt (-5))) == .int (-5)
#guard (Id.ofInt 2026).bits == 0x20000000000007ea
#guard (Id.ofVocabIndex 137024).bits == 0x4000000000021740
#guard (Id.decode ⟨0⟩) == .undefined
#guard (Id.decode ⟨1⟩) == .invalid 0 1
#guard (Id.decode ⟨0x1000000000000003⟩) == .bool true true
#guard (Id.decode ⟨0xB000000000000007⟩) == .blankNodeIndex 7
-- 70.0 = 0x4051800000000000; stored shifted right 4 under tag 3.
#guard (Id.decode ⟨((3 : UInt64) <<< 60) ||| ((0x4051800000000000 : UInt64) >>> 4)⟩) == .double 0x4051800000000000

end L4Factoidal.Qlvr
