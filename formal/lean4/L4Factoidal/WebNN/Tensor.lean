/-
L4Factoidal.WebNN.Tensor: the data of a tensor for the Web Neural Network API: the operand
data types, flat buffers of elements, the byte encoding scripts see, and the one primitive
that every data-movement operator is made of (`Buf.select`: read elements by flat number).

Floating point is the engine's: Lean's `Float` (binary64, as BubblePopJS numbers) and
`Float32`; float16 goes through `Prim.Float16`. A float tensor holds its elements as binary64
values that are exactly representable in its data type; each operator computes in binary64
and rounds once to the data type (`DType.normF`). For +, -, *, / and sqrt that single
rounding of the binary64 result equals the correctly rounded binary32 result (the binary64
significand is more than twice as wide). Integer tensors hold exact integers and wrap to the
data type as two's complement (`DType.wrapI`).

Buffers are flat (`FloatArray`, and `Array Int` whose small values are unboxed): no object per
element.
-/
import L4Factoidal.WebNN.Shape
import L4Factoidal.Prim.Float16
-- Hot `Nat`/`Int` to `Float` conversions and `Float` literals (see that module).
import L4Factoidal.Prim.FloatOfNat

namespace L4Factoidal.WebNN

open L4Factoidal.Prim

/-- `MLOperandDataType`, the types this engine computes. -/
inductive DType where
  | float32 | float16 | int32 | uint32 | int64 | uint64 | int8 | uint8
  deriving DecidableEq, Repr, Inhabited

namespace DType

def all : List DType := [float32, float16, int32, uint32, int64, uint64, int8, uint8]

def name : DType → String
  | float32 => "float32" | float16 => "float16" | int32 => "int32" | uint32 => "uint32"
  | int64 => "int64" | uint64 => "uint64" | int8 => "int8" | uint8 => "uint8"

def ofName? (s : String) : Option DType := all.find? (·.name == s)

/-- Bytes of one element. -/
def bytes : DType → Nat
  | float32 => 4 | float16 => 2 | int32 => 4 | uint32 => 4 | int64 => 8 | uint64 => 8 | int8 => 1 | uint8 => 1

def isFloat : DType → Bool
  | float32 | float16 => true
  | _ => false

def isSigned : DType → Bool
  | uint32 | uint64 | uint8 => false
  | _ => true

/-- Bits of an integer type (0 for a float type). -/
def bits : DType → Nat
  | int32 | uint32 => 32 | int64 | uint64 => 64 | int8 | uint8 => 8 | _ => 0

/-- The value range of an integer type: least, greatest, and the modulus `2^bits`. A kernel
takes it once and wraps each element with it (the 64-bit bounds are big numbers: they are
made once per operator call, not once per element). -/
structure IntRange where
  lo : Int
  hi : Int
  modulus : Int
  deriving Inhabited

def range : DType → IntRange
  | int8 => ⟨-128, 127, 256⟩
  | uint8 => ⟨0, 255, 256⟩
  | int32 => ⟨-2147483648, 2147483647, 4294967296⟩
  | uint32 => ⟨0, 4294967295, 4294967296⟩
  | int64 => let h : Int := (2 : Int) ^ 63; ⟨-h, h - 1, 2 * h⟩
  | uint64 => let h : Int := (2 : Int) ^ 64; ⟨0, h - 1, h⟩
  | _ => ⟨0, 0, 1⟩

def minInt (t : DType) : Int := t.range.lo
def maxInt (t : DType) : Int := t.range.hi

/-- An integer wrapped into the range (two's complement, as a C conversion). -/
@[inline] def IntRange.wrap (r : IntRange) (v : Int) : Int :=
  if r.lo ≤ v ∧ v ≤ r.hi then v else
  let x := v % r.modulus
  if x > r.hi then x - r.modulus else x

/-- An integer saturated into the range. -/
@[inline] def IntRange.sat (r : IntRange) (v : Int) : Int := if v < r.lo then r.lo else if v > r.hi then r.hi else v

def wrapI (t : DType) (v : Int) : Int := t.range.wrap v
def satI (t : DType) (v : Int) : Int := t.range.sat v

/-- A binary64 value rounded to a float type (to nearest, ties to even). -/
@[inline] def normF (t : DType) (x : Float) : Float :=
  match t with
  | float16 => Float16.round x
  | _ => x.toFloat32.toFloat

/-- Kind: range. Says: for a range that is a full residue system around zero
(`hi - lo + 1 = modulus`, `lo ≤ 0 ≤ hi`), wrapping any integer gives a value within it. -/
theorem wrap_range (r : IntRange) (v : Int) (hm : r.hi - r.lo + 1 = r.modulus) (hlo : r.lo ≤ 0)
    (hhi : 0 ≤ r.hi) : r.lo ≤ r.wrap v ∧ r.wrap v ≤ r.hi := by
  have hpos : 0 < r.modulus := by omega
  have h0 := Int.emod_nonneg v (Int.ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos v hpos
  simp only [IntRange.wrap]
  by_cases c1 : r.lo ≤ v ∧ v ≤ r.hi
  · rw [if_pos c1]; exact c1
  · rw [if_neg c1]
    by_cases c2 : v % r.modulus > r.hi
    · rw [if_pos c2]; omega
    · rw [if_neg c2]; omega

/-- Kind: range. Says: wrapping into each integer data type gives a value of that type, for
all six integer types. -/
theorem wrapI_range (t : DType) (v : Int) : t.minInt ≤ wrapI t v ∧ wrapI t v ≤ t.maxInt := by
  cases t <;> exact wrap_range _ v (by decide) (by decide) (by decide)

/-- Kind: congruence. Says: wrapping changes a value only by a multiple of the modulus, so
integer arithmetic followed by one wrap is arithmetic modulo `2^bits`. -/
theorem wrap_congr (r : IntRange) (v : Int) : (r.wrap v - v) % r.modulus = 0 := by
  have h := Int.emod_add_mul_ediv v r.modulus
  simp only [IntRange.wrap]
  by_cases h1 : r.lo ≤ v ∧ v ≤ r.hi
  · rw [if_pos h1]; simp
  · rw [if_neg h1]
    by_cases h2 : v % r.modulus > r.hi
    · rw [if_pos h2]
      have e : v % r.modulus - r.modulus - v = r.modulus * (-(v / r.modulus) - 1) := by
        rw [Int.mul_sub, Int.mul_neg, Int.mul_one]; omega
      rw [e]; exact Int.mul_emod_right _ _
    · rw [if_neg h2]
      have e : v % r.modulus - v = r.modulus * (-(v / r.modulus)) := by
        rw [Int.mul_neg]; omega
      rw [e]; exact Int.mul_emod_right _ _

end DType

/-- A flat buffer of elements: binary64 values for the float types, integers for the others. -/
inductive Buf where
  | f (a : FloatArray)
  | i (a : Array Int)
  deriving Inhabited

namespace Buf

def size : Buf → Nat
  | f a => a.size
  | i a => a.size

/-- Element `k` as a binary64 value (an integer is converted). -/
def getF (b : Buf) (k : Nat) : Float :=
  match b with
  | f a => a.get! k
  | i a => Float.ofInt (a[k]!)

/-- Element `k` as an integer (a float is truncated toward zero; NaN gives 0). -/
def getI (b : Buf) (k : Nat) : Int :=
  match b with
  | f a => (a.get! k).toInt64.toInt
  | i a => a[k]!

/-- The elements numbered by `idx`, in that order: the primitive of every data-movement
operator. A number past the end reads 0. -/
def select (b : Buf) (idx : Array Nat) : Buf :=
  match b with
  | f a => f (idx.foldl (fun (acc : FloatArray) k => acc.push (a.get! k)) (FloatArray.emptyWithCapacity idx.size))
  | i a => i (idx.map fun k => a[k]!)

def append : Buf → Buf → Buf
  | f a, f b => f (b.foldl (fun acc x => acc.push x) a)
  | i a, i b => i (a ++ b)
  | f a, i b => f (b.foldl (fun acc x => acc.push (Float.ofInt x)) a)
  | i a, f b => i (b.foldl (fun acc x => acc.push x.toInt64.toInt) a)

/-- A buffer of `n` copies of one value (given in both domains). -/
def fill (float : Bool) (n : Nat) (x : Float) (v : Int) : Buf :=
  if float then f (Nat.fold n (fun _ _ acc => acc.push x) (FloatArray.emptyWithCapacity n))
  else i (Array.replicate n v)

def isFloat : Buf → Bool
  | f _ => true
  | i _ => false

def toFloats : Buf → FloatArray
  | f a => a
  | i a => a.foldl (fun acc x => acc.push (Float.ofInt x)) (FloatArray.emptyWithCapacity a.size)

def toInts : Buf → Array Int
  | f a => a.foldl (fun acc x => acc.push x.toInt64.toInt) (Array.emptyWithCapacity a.size)
  | i a => a

/-- Kind: size. Says: `select` gives exactly one element per requested number. -/
theorem size_select_i (a : Array Int) (idx : Array Nat) : (select (i a) idx).size = idx.size := by
  simp [select, size]

/-- Kind: content. Says: element `k` of `select` on an integer buffer is the element of the
source that `idx[k]` numbers: data movement copies and never computes. Does not say: the same
for float buffers (`FloatArray` has no lemmas in core Lean; tested). -/
theorem select_i_get (a : Array Int) (idx : Array Nat) (k : Nat) (h : k < idx.size) :
    (match select (i a) idx with | i r => r[k]! | f _ => 0) = a[idx[k]]! := by
  simp [select, h]

end Buf

/-! ## Bytes (the little-endian element encoding of typed arrays) -/

namespace Bytes

@[inline] def u8 (b : ByteArray) (p : Nat) : Nat := (b.get! p).toNat

@[inline] def uLE (b : ByteArray) (p n : Nat) : Nat :=
  match n with
  | 1 => u8 b p
  | 2 => u8 b p + u8 b (p + 1) * 256
  | 4 => u8 b p + u8 b (p + 1) * 256 + u8 b (p + 2) * 65536 + u8 b (p + 3) * 16777216
  | _ => (u8 b p + u8 b (p + 1) * 256 + u8 b (p + 2) * 65536 + u8 b (p + 3) * 16777216) +
    (u8 b (p + 4) + u8 b (p + 5) * 256 + u8 b (p + 6) * 65536 + u8 b (p + 7) * 16777216) * 4294967296

def pushLE (out : ByteArray) (v n : Nat) : ByteArray :=
  Nat.fold n (fun k _ acc => acc.push ((v >>> (8 * k)) % 256).toUInt8) out

end Bytes

/-- Decode `count` elements of a data type from little-endian bytes (missing bytes read 0). -/
def Buf.ofBytes (t : DType) (b : ByteArray) (count : Nat) : Buf :=
  match t with
  | .float32 => .f (Nat.fold count (fun k _ acc =>
      acc.push (Float32.ofBits (Bytes.uLE b (4 * k) 4).toUInt32).toFloat) (FloatArray.emptyWithCapacity count))
  | .float16 => .f (Nat.fold count (fun k _ acc =>
      acc.push (Float16.toFloat (Bytes.uLE b (2 * k) 2).toUInt16)) (FloatArray.emptyWithCapacity count))
  | t =>
    let n := t.bytes
    let r := t.range
    .i (Array.ofFn (n := count) fun k =>
      let u : Int := Int.ofNat (Bytes.uLE b (n * k.val) n)
      r.wrap u)

/-- Encode a buffer as the little-endian bytes of a data type. -/
def Buf.toBytes (t : DType) (b : Buf) : ByteArray :=
  let n := b.size
  let out := ByteArray.emptyWithCapacity (n * t.bytes)
  match t with
  | .float32 => Nat.fold n (fun k _ acc => Bytes.pushLE acc (b.getF k).toFloat32.toBits.toNat 4) out
  | .float16 => Nat.fold n (fun k _ acc => Bytes.pushLE acc (Float16.ofFloat (b.getF k)).toNat 2) out
  | t =>
    let m : Int := t.range.modulus
    Nat.fold n (fun k _ acc => Bytes.pushLE acc ((b.getI k) % m).toNat t.bytes) out

/-- A tensor: data type, shape and elements (`buf.size = shape.size` for every tensor the
operators make: `Tensor.WellFormed`). -/
structure Tensor where
  dtype : DType
  shape : Shape
  buf : Buf
  deriving Inhabited

namespace Tensor

/-- The element count agrees with the shape, and the buffer's domain with the data type. -/
def wellFormed (t : Tensor) : Bool := t.buf.size == t.shape.size && t.buf.isFloat == t.dtype.isFloat

def ofBytes (t : DType) (s : Shape) (b : ByteArray) : Tensor := ⟨t, s, Buf.ofBytes t b s.size⟩
def toBytes (t : Tensor) : ByteArray := t.buf.toBytes t.dtype

/-- The same elements under another shape. -/
def reshape (t : Tensor) (s : Shape) : Tensor := { t with shape := s }

/-- Kind: definitional. Says: reshape keeps the element sequence (and the data type): only the
shape changes. -/
theorem reshape_buf (t : Tensor) (s : Shape) : (t.reshape s).buf = t.buf ∧ (t.reshape s).dtype = t.dtype :=
  ⟨rfl, rfl⟩

/-- Kind: well-formedness. Says: reshaping to a shape with the same element count keeps a
well-formed tensor well-formed. -/
theorem reshape_wellFormed (t : Tensor) (s : Shape) (h : t.wellFormed = true) (hs : s.size = t.shape.size) :
    (t.reshape s).wellFormed = true := by
  simp only [wellFormed, reshape, hs] at *
  exact h

end Tensor

private def bytesOf (l : List Nat) : ByteArray := ByteArray.mk (l.map (·.toUInt8)).toArray

#guard (Buf.ofBytes .float32 (bytesOf [0, 0, 128, 63, 0, 0, 0, 192]) 2).getF 1 == -2.0
#guard ((Buf.ofBytes .float32 (bytesOf [0, 0, 128, 63, 0, 0, 0, 192]) 2).toBytes .float32).data == #[0, 0, 128, 63, 0, 0, 0, 192]
#guard (Buf.ofBytes .int8 (bytesOf [255, 127, 128]) 3).toInts == #[-1, 127, -128]
#guard ((Buf.i #[-1, 127, -128, 300]).toBytes .int8).data == #[255, 127, 128, 44]
#guard (Buf.ofBytes .int64 (bytesOf [254, 255, 255, 255, 255, 255, 255, 255]) 1).toInts == #[-2]
#guard ((Buf.i #[-2]).toBytes .int64).data == #[254, 255, 255, 255, 255, 255, 255, 255]
#guard (Buf.ofBytes .uint64 (bytesOf [254, 255, 255, 255, 255, 255, 255, 255]) 1).toInts == #[18446744073709551614]
#guard ((Buf.f (FloatArray.mk #[1.0, 0.333251953125])).toBytes .float16).data == #[0, 60, 85, 53]
#guard DType.wrapI .int32 4294967295 == -1 && DType.wrapI .uint8 (-1) == 255 && DType.wrapI .int64 ((2 : Int) ^ 63) == -(2 : Int) ^ 63
#guard ((Buf.i #[10, 20, 30]).select #[2, 0, 0]).toInts == #[30, 10, 10]
#guard ((Buf.f (FloatArray.mk #[1.5, 2.5])).select #[1, 1, 0]).toFloats.data == #[2.5, 2.5, 1.5]

end L4Factoidal.WebNN
