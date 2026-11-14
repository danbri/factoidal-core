/-
L4Factoidal.Prim.Float16: IEEE 754 binary16 ("half", float16) as bit patterns, converted to
and from binary64 by integer arithmetic on the bit fields: decoding is exact, encoding rounds
to nearest with ties to even, straight from the binary64 value (never through binary32, which
would round twice).

Used by the Web Neural Network tensors (`WebNN/Tensor.lean`: float16 operands) and by
BubblePopJS (`Float16Array`, `Math.f16round`, `DataView.getFloat16`/`setFloat16`).

The engine's floating point is Lean's `Float` (the platform's binary64) and `Float32`; this
module adds no arithmetic of its own: it only moves between the two encodings. The functions on
`Nat` bit patterns are the specification and are what the theorems are about; `toFloat` and
`ofFloat` apply them to `Float.toBits` / `Float.ofBits`, which are trusted (the Lean runtime).
-/

namespace L4Factoidal.Prim.Float16

/-- `n / 2^s` rounded to the nearest integer, ties to the even one. -/
def roundShift (n s : Nat) : Nat :=
  if s = 0 then n else
  let q := n >>> s
  let r := n - (q <<< s)
  let half := 1 <<< (s - 1)
  if r > half || (r == half && q % 2 == 1) then q + 1 else q

/-- The binary16 bit pattern nearest to the binary64 value with bit pattern `b` (ties to even;
overflow gives an infinity, any NaN gives the quiet NaN `0x7E00` with the sign kept). -/
def ofDoubleBits (b : Nat) : Nat :=
  let sign := ((b >>> 63) % 2) <<< 15
  let e := (b >>> 52) % 2048
  let m := b % 4503599627370496
  if e = 2047 then (if m = 0 then sign + 0x7C00 else sign + 0x7E00)
  else if e = 0 then sign
  else
    let sig := 4503599627370496 + m
    if e ≥ 1009 then
      let h := ((e - 1008) <<< 10) + roundShift sig 42 - 1024
      if h ≥ 0x7C00 then sign + 0x7C00 else sign + h
    else
      let s := 42 + (1009 - e)
      sign + (if s > 54 then 0 else roundShift sig s)

/-- The binary64 bit pattern of the value of the binary16 bit pattern `h` (exact; a NaN stays
a NaN, with its payload moved to the top of the fraction). -/
def toDoubleBits (h : Nat) : Nat :=
  let sign := ((h >>> 15) % 2) <<< 63
  let e := (h >>> 10) % 32
  let m := h % 1024
  if e = 31 then sign + (2047 <<< 52) + (m <<< 42)
  else if e = 0 then
    if m = 0 then sign
    else
      let k := Nat.log2 m
      sign + ((999 + k) <<< 52) + ((m - (1 <<< k)) <<< (52 - k))
  else sign + ((e + 1008) <<< 52) + (m <<< 42)

/-- The value of a binary16 bit pattern. -/
def toFloat (h : UInt16) : Float := Float.ofBits (toDoubleBits h.toNat).toUInt64

/-- The binary16 bit pattern nearest to `x`. -/
def ofFloat (x : Float) : UInt16 := (ofDoubleBits x.toBits.toNat).toUInt16

/-- `x` rounded to the nearest binary16 value (`Math.f16round`). -/
def round (x : Float) : Float := toFloat (ofFloat x)

/-- A binary16 bit pattern is a NaN. -/
def isNaNBits (h : Nat) : Bool := (h >>> 10) % 32 == 31 && h % 1024 != 0

/-- Every bit pattern from `lo` up to `lo + n` (exclusive) that is not a NaN survives the trip
to binary64 and back. -/
def roundTripRange (lo n : Nat) : Bool :=
  (List.range n).all fun k => isNaNBits (lo + k) || ofDoubleBits (toDoubleBits (lo + k)) == lo + k

/-- Kind: round trip, by exhaustive kernel evaluation (64 blocks of 1024 patterns). Says:
every one of the 65,536 binary16 bit patterns that is not a NaN (zeros, subnormals, normals
and infinities of both signs) is recovered exactly after decoding to a binary64 bit pattern
and encoding back, so encoding is a left inverse of decoding on numbers. Does not say:
anything about `Float.toBits` and `Float.ofBits` (the runtime), nor that encoding rounds
correctly for binary64 values that are not binary16 values (tested by `#guard`s below). -/
theorem roundTrip_all : (List.range 64).all (fun b => roundTripRange (b * 1024) 1024) = true := by
  decide +kernel

/-- Kind: totality of NaN handling. Says: every binary16 NaN bit pattern decodes to a binary64
NaN bit pattern and encodes back to a binary16 NaN. Does not say: that the payload is kept. -/
theorem nan_all : (List.range 2048).all (fun k =>
    let h := if k < 1024 then 0x7C00 + k else 0xFC00 + (k - 1024)
    !isNaNBits h || isNaNBits (ofDoubleBits (toDoubleBits h))) = true := by
  decide +kernel

#guard ofFloat 1.0 == 0x3C00 && ofFloat (-2.0) == 0xC000 && ofFloat 65504.0 == 0x7BFF
#guard ofFloat 65520.0 == 0x7C00 && ofFloat 65519.99 == 0x7BFF && ofFloat (-1e10) == 0xFC00
-- ties to even at the midpoint between 1 and the next value (1 + 2^-10), and just above it
#guard ofFloat 1.00048828125 == 0x3C00 && ofFloat 1.000488281250001 == 0x3C01
#guard ofFloat 1.00146484375 == 0x3C02
-- subnormals: the smallest (2^-24), half of it (a tie, to even: zero), just above half
#guard ofFloat 5.960464477539063e-8 == 0x0001 && ofFloat 2.9802322387695312e-8 == 0x0000
#guard ofFloat 2.98023223876954e-8 == 0x0001 && ofFloat 0.0 == 0 && ofFloat (-0.0) == 0x8000
#guard toFloat 0x3555 == 0.333251953125 && toFloat 0x0001 == 5.960464477539063e-8
#guard (toFloat 0x7E00).isNaN && toFloat 0xFC00 == -(1.0 / 0.0) && ofFloat (0.0 / 0.0) % 0x8000 == 0x7E00
-- a value that rounding through binary32 first gets wrong (double rounding):
-- 1 + 2^-11 + 2^-40 is above the midpoint, binary32 rounds it to the midpoint itself
#guard ofFloat 1.0004882812509095 == 0x3C01

end L4Factoidal.Prim.Float16
