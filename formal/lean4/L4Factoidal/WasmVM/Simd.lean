/-
L4Factoidal.WasmVM.Simd: the fixed-width SIMD instructions (v128; binary prefix 0xFD),
https://github.com/danbri/factoidal/issues/1244. Record: "SIMD" in
docs/designissues/2026-11-07-wasmvm-engine.md.

One instruction constructor (`Instr.simd`) carries the opcode number and the
immediates. This file gives, for each opcode number, its shape (`simdShape`: the
immediates in the binary format and the stack signature, used by the decoder and the
validator), and its result on `V128` values (`V128.evalUn`, `evalBin` and the others,
used by the interpreter's cold path).

A `V128` is two `UInt64` halves; lane `i` of width `w` bits is bits `i*w .. i*w+w`
(little-endian lane order, specification section 4.3.4 "Vectors"). Lane results are
computed lane by lane with the lane as a zero-extended `UInt64`; float lanes use the
scalar operations of `Numerics.lean` (`NumOp.evalUn`, `NumOp.evalBin`), so NaN and
signed-zero behaviour is that of the scalar instructions. Signed integer lanes use
`Int`. Relaxed SIMD (opcodes 0x100 and above) is not here.
-/
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Numerics

namespace L4Factoidal.WasmVM

/-- The shape of a SIMD instruction: its immediates and its stack signature. -/
inductive SimdShape where
  /-- `i32 → v128`, with a memarg; reads `width` bytes. -/
  | load (width : Nat)
  /-- `i32 v128 → `, with a memarg; writes 16 bytes. -/
  | store
  /-- `→ v128`, with 16 bytes. -/
  | const
  /-- `v128 v128 → v128`, with 16 lane indices. -/
  | shuffle
  | un | bin | tern
  /-- `v128 → i32`. -/
  | test
  /-- `v128 i32 → v128`. -/
  | shift
  /-- `t → v128`. -/
  | splat (t : ValType)
  /-- `v128 → t`, with a lane index below `lanes`. -/
  | extract (t : ValType) (lanes : Nat)
  /-- `v128 t → v128`, with a lane index below `lanes`. -/
  | replace (t : ValType) (lanes : Nat)
  /-- `i32 v128 → v128`, with a memarg and a lane index; reads `width` bytes. -/
  | loadLane (width : Nat)
  /-- `i32 v128 → `, with a memarg and a lane index; writes `width` bytes. -/
  | storeLane (width : Nat)
  deriving BEq, Repr, Inhabited

/-- Opcodes from 0x60 that take one vector and give one. -/
def simdUnHigh (c : Nat) : Bool :=
  c == 0x60 || c == 0x61 || c == 0x62 || (0x67 ≤ c && c ≤ 0x6a) || c == 0x74 || c == 0x75 ||
  c == 0x7a || (0x7c ≤ c && c ≤ 0x81) || (0x87 ≤ c && c ≤ 0x8a) || c == 0x94 ||
  c == 0xa0 || c == 0xa1 || (0xa7 ≤ c && c ≤ 0xaa) || c == 0xc0 || c == 0xc1 ||
  (0xc7 ≤ c && c ≤ 0xca) || c == 0xe0 || c == 0xe1 || c == 0xe3 ||
  c == 0xec || c == 0xed || c == 0xef || (0xf8 ≤ c && c ≤ 0xff)

/-- Opcode numbers from 0x60 to 0xff that name no instruction. -/
def simdReserved (c : Nat) : Bool :=
  c == 0x9a || c == 0xa2 || c == 0xa5 || c == 0xa6 || c == 0xaf || c == 0xb0 ||
  (0xb2 ≤ c && c ≤ 0xb4) || c == 0xbb || c == 0xc2 || c == 0xc5 || c == 0xc6 ||
  c == 0xcf || c == 0xd0 || (0xd2 ≤ c && c ≤ 0xd4) || c == 0xe2 || c == 0xee

/-- The shape of SIMD opcode `c` (the number after the 0xFD prefix); `none` when `c`
names no instruction of the fixed-width SIMD proposal. -/
def simdShape (c : Nat) : Option SimdShape :=
  if c == 0x00 then some (.load 16)
  else if c ≤ 0x06 then some (.load 8)
  else if c ≤ 0x0a then some (.load (1 <<< (c - 0x07)))
  else if c == 0x0b then some .store
  else if c == 0x0c then some .const
  else if c == 0x0d then some .shuffle
  else if c == 0x0e then some .bin
  else if c ≤ 0x11 then some (.splat .i32)
  else if c == 0x12 then some (.splat .i64)
  else if c == 0x13 then some (.splat .f32)
  else if c == 0x14 then some (.splat .f64)
  else if c == 0x15 || c == 0x16 then some (.extract .i32 16)
  else if c == 0x17 then some (.replace .i32 16)
  else if c == 0x18 || c == 0x19 then some (.extract .i32 8)
  else if c == 0x1a then some (.replace .i32 8)
  else if c == 0x1b then some (.extract .i32 4)
  else if c == 0x1c then some (.replace .i32 4)
  else if c == 0x1d then some (.extract .i64 2)
  else if c == 0x1e then some (.replace .i64 2)
  else if c == 0x1f then some (.extract .f32 4)
  else if c == 0x20 then some (.replace .f32 4)
  else if c == 0x21 then some (.extract .f64 2)
  else if c == 0x22 then some (.replace .f64 2)
  else if c ≤ 0x4c then some .bin
  else if c == 0x4d then some .un
  else if c ≤ 0x51 then some .bin
  else if c == 0x52 then some .tern
  else if c == 0x53 then some .test
  else if c ≤ 0x57 then some (.loadLane (1 <<< (c - 0x54)))
  else if c ≤ 0x5b then some (.storeLane (1 <<< (c - 0x58)))
  else if c == 0x5c then some (.load 4)
  else if c == 0x5d then some (.load 8)
  else if c == 0x5e || c == 0x5f then some .un
  else if c > 0xff || simdReserved c then none
  else if simdUnHigh c then some .un
  else if c % 32 == 3 || c % 32 == 4 then (if c < 0xe0 then some .test else some .bin)
  else if 0x60 ≤ c && c < 0xe0 && 11 ≤ c % 32 && c % 32 ≤ 13 then some .shift
  else some .bin

/-- A 128-bit vector: bits 0 to 63 and bits 64 to 127. -/
structure V128 where
  lo : UInt64
  hi : UInt64
  deriving BEq, Repr, Inhabited

namespace V128

def ones : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The low `w` bits set (`w` is 8, 16, 32 or 64). -/
@[inline] def mask (w : Nat) : UInt64 := if w ≥ 64 then ones else ((1 : UInt64) <<< w.toUInt64) - 1

/-- Lane `i` of width `w` bits, zero-extended. -/
def lane (w : Nat) (v : V128) (i : Nat) : UInt64 :=
  let off := i * w
  if off < 64 then (v.lo >>> off.toUInt64) &&& mask w
  else if off < 128 then (v.hi >>> (off - 64).toUInt64) &&& mask w
  else 0

/-- Lane `i` of width `w` set to the low `w` bits of `x`. -/
def setLane (w : Nat) (v : V128) (i : Nat) (x : UInt64) : V128 :=
  let off := i * w
  let m := mask w
  if off < 64 then
    let o := off.toUInt64
    { v with lo := (v.lo &&& ~~~(m <<< o)) ||| ((x &&& m) <<< o) }
  else if off < 128 then
    let o := (off - 64).toUInt64
    { v with hi := (v.hi &&& ~~~(m <<< o)) ||| ((x &&& m) <<< o) }
  else v

/-- The vector whose lane `i` of width `w` is `f i`. At most 16 lanes. -/
def build (w : Nat) (f : Nat → UInt64) : V128 := go (128 / w) 0 ⟨0, 0⟩
where
  go : Nat → Nat → V128 → V128
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) (acc.setLane w i (f i))

@[inline] def map1 (w : Nat) (f : UInt64 → UInt64) (a : V128) : V128 :=
  build w fun i => f (a.lane w i)

@[inline] def map2 (w : Nat) (f : UInt64 → UInt64 → UInt64) (a b : V128) : V128 :=
  build w fun i => f (a.lane w i) (b.lane w i)

/-- A lane of `w` bits as a signed integer. -/
def sx (w : Nat) (x : UInt64) : Int :=
  let n := x.toNat
  if n ≥ 2 ^ (w - 1) then (n : Int) - ((2 ^ w : Nat) : Int) else (n : Int)

/-- An integer modulo `2^w`, as a lane. -/
def ofInt (w : Nat) (i : Int) : UInt64 := UInt64.ofNat (i % ((2 ^ w : Nat) : Int)).toNat

/-- Signed saturation to `w` bits. -/
def satS (w : Nat) (i : Int) : UInt64 :=
  let m : Int := ((2 ^ (w - 1) : Nat) : Int)
  ofInt w (if i < -m then -m else if i > m - 1 then m - 1 else i)

/-- Unsigned saturation to `w` bits. -/
def satU (w : Nat) (i : Int) : UInt64 :=
  let m : Int := ((2 ^ w : Nat) : Int)
  ofInt w (if i < 0 then 0 else if i > m - 1 then m - 1 else i)

@[inline] def boolLane (b : Bool) : UInt64 := if b then ones else 0

/-- Integer comparison `j` (0 eq, 1 ne, 2 lt_s, 3 lt_u, 4 gt_s, 5 gt_u, 6 le_s, 7 le_u,
8 ge_s, 9 ge_u) of two lanes of `w` bits. -/
def cmpI (w j : Nat) (a b : UInt64) : UInt64 :=
  let sa := sx w a
  let sb := sx w b
  boolLane (match j with
    | 0 => a == b | 1 => a != b | 2 => sa < sb | 3 => a < b | 4 => sa > sb | 5 => a > b
    | 6 => sa ≤ sb | 7 => a ≤ b | 8 => sa ≥ sb | _ => a ≥ b)

/-- The scalar float comparison `j` (0 eq, 1 ne, 2 lt, 3 gt, 4 le, 5 ge). -/
def fcmpOp (is64 : Bool) : Nat → NumOp
  | 0 => if is64 then .f64_eq else .f32_eq
  | 1 => if is64 then .f64_ne else .f32_ne
  | 2 => if is64 then .f64_lt else .f32_lt
  | 3 => if is64 then .f64_gt else .f32_gt
  | 4 => if is64 then .f64_le else .f32_le
  | _ => if is64 then .f64_ge else .f32_ge

/-- The scalar float op at offset `k` of the float blocks (0xe0 for f32x4, 0xec for
f64x2): 0 abs, 1 neg, 3 sqrt, 4 add, 5 sub, 6 mul, 7 div, 8 min, 9 max. -/
def fOp (is64 : Bool) : Nat → NumOp
  | 0 => if is64 then .f64_abs else .f32_abs
  | 1 => if is64 then .f64_neg else .f32_neg
  | 3 => if is64 then .f64_sqrt else .f32_sqrt
  | 4 => if is64 then .f64_add else .f32_add
  | 5 => if is64 then .f64_sub else .f32_sub
  | 6 => if is64 then .f64_mul else .f32_mul
  | 7 => if is64 then .f64_div else .f32_div
  | 8 => if is64 then .f64_min else .f32_min
  | _ => if is64 then .f64_max else .f32_max

/-- Rounding `j`: 0 ceil, 1 floor, 2 trunc, 3 nearest (round half to even). -/
def roundOp (is64 : Bool) : Nat → NumOp
  | 0 => if is64 then .f64_ceil else .f32_ceil
  | 1 => if is64 then .f64_floor else .f32_floor
  | 2 => if is64 then .f64_trunc else .f32_trunc
  | _ => if is64 then .f64_nearest else .f32_nearest

/-- Integer lane op at offset `k` of an integer block (0x60 i8x16, 0x80 i16x8, 0xa0
i32x4, 0xc0 i64x2), two operands: 14 add, 15 add_sat_s, 16 add_sat_u, 17 sub,
18 sub_sat_s, 19 sub_sat_u, 21 mul, 22 min_s, 23 min_u, 24 max_s, 25 max_u, 27 avgr_u. -/
def intBin (w k : Nat) (x y : UInt64) : UInt64 :=
  match k with
  | 14 => x + y
  | 15 => satS w (sx w x + sx w y)
  | 16 => satU w ((x.toNat : Int) + (y.toNat : Int))
  | 17 => x - y
  | 18 => satS w (sx w x - sx w y)
  | 19 => satU w ((x.toNat : Int) - (y.toNat : Int))
  | 21 => x * y
  | 22 => if sx w x ≤ sx w y then x else y
  | 23 => if x ≤ y then x else y
  | 24 => if sx w x ≥ sx w y then x else y
  | 25 => if x ≥ y then x else y
  | 27 => UInt64.ofNat ((x.toNat + y.toNat + 1) / 2)
  | _ => 0

/-- Shift `k` (11 shl, 12 shr_s, 13 shr_u) of a lane of `w` bits by `n` modulo `w`. -/
def shiftLane (w k : Nat) (n : UInt64) (x : UInt64) : UInt64 :=
  let s := n.toNat % w
  match k with
  | 11 => x <<< s.toUInt64
  | 12 => ofInt w (sx w x >>> s)
  | _ => x >>> s.toUInt64

/-- Lanes of `w` bits made from the lanes of half that width, starting at source lane
`from`: sign-extended when `signed`. -/
def extendLanes (w : Nat) (signed : Bool) (from_ : Nat) (a : V128) : V128 :=
  let h := w / 2
  build w fun i =>
    let x := a.lane h (i + from_)
    if signed then ofInt w (sx h x) else x

/-- Products of `w` bits of the lanes of half that width, from source lane `from`. -/
def extMul (w : Nat) (signed : Bool) (from_ : Nat) (a b : V128) : V128 :=
  let h := w / 2
  build w fun i =>
    let x := a.lane h (i + from_)
    let y := b.lane h (i + from_)
    if signed then ofInt w (sx h x * sx h y) else x * y

/-- Sums of `w` bits of adjacent pairs of lanes of half that width. -/
def extAddPairwise (w : Nat) (signed : Bool) (a : V128) : V128 :=
  let h := w / 2
  build w fun i =>
    let x := a.lane h (2 * i)
    let y := a.lane h (2 * i + 1)
    if signed then ofInt w (sx h x + sx h y) else x + y

/-- Lanes of `w` bits from the signed lanes of twice that width of `a` then `b`,
saturated (signed or unsigned result). -/
def narrow (w : Nat) (signed : Bool) (a b : V128) : V128 :=
  let n := 64 / w
  build w fun i =>
    let x := if i < n then a.lane (2 * w) i else b.lane (2 * w) (i - n)
    if signed then satS w (sx (2 * w) x) else satU w (sx (2 * w) x)

/-- The lane width and the offset in its block of an integer opcode (0x60 to 0xdf). -/
@[inline] def blockW (c : Nat) : Nat := 8 <<< ((c - 0x60) / 32)
@[inline] def blockK (c : Nat) : Nat := (c - 0x60) % 32

/-- One vector to one vector. -/
def evalUn (c : Nat) (a : V128) : V128 :=
  if c == 0x4d then ⟨~~~a.lo, ~~~a.hi⟩
  else if c == 0x5e then build 32 fun i => if i < 2 then NumOp.f32_demote_f64.evalUn (a.lane 64 i) else 0
  else if c == 0x5f then build 64 fun i => NumOp.f64_promote_f32.evalUn (a.lane 32 i)
  else if 0x67 ≤ c && c ≤ 0x6a then map1 32 (roundOp false (c - 0x67)).evalUn a
  else if c == 0x74 then map1 64 NumOp.f64_ceil.evalUn a
  else if c == 0x75 then map1 64 NumOp.f64_floor.evalUn a
  else if c == 0x7a then map1 64 NumOp.f64_trunc.evalUn a
  else if c == 0x94 then map1 64 NumOp.f64_nearest.evalUn a
  else if 0x7c ≤ c && c ≤ 0x7f then extAddPairwise (if c < 0x7e then 16 else 32) (c % 2 == 0) a
  else if 0xe0 ≤ c && c < 0xec then map1 32 (fOp false (c - 0xe0)).evalUn a
  else if 0xec ≤ c && c < 0xf8 then map1 64 (fOp true (c - 0xec)).evalUn a
  else if c == 0xf8 then map1 32 NumOp.i32_trunc_sat_f32_s.evalUn a
  else if c == 0xf9 then map1 32 NumOp.i32_trunc_sat_f32_u.evalUn a
  else if c == 0xfa then map1 32 NumOp.f32_convert_i32_s.evalUn a
  else if c == 0xfb then map1 32 NumOp.f32_convert_i32_u.evalUn a
  else if c == 0xfc then build 32 fun i => if i < 2 then NumOp.i32_trunc_sat_f64_s.evalUn (a.lane 64 i) else 0
  else if c == 0xfd then build 32 fun i => if i < 2 then NumOp.i32_trunc_sat_f64_u.evalUn (a.lane 64 i) else 0
  else if c == 0xfe then build 64 fun i => NumOp.f64_convert_i32_s.evalUn (a.lane 32 i)
  else if c == 0xff then build 64 fun i => NumOp.f64_convert_i32_u.evalUn (a.lane 32 i)
  else
    let w := blockW c
    let k := blockK c
    if k == 0 then map1 w (fun x => if sx w x < 0 then 0 - x else x) a
    else if k == 1 then map1 w (fun x => 0 - x) a
    else if k == 2 then map1 w Num.popcnt64 a
    else if 7 ≤ k && k ≤ 10 then extendLanes w (k < 9) (if k % 2 == 0 then 64 / (w / 2) else 0) a
    else a

/-- Float lanes: `k` 4 to 9 through the scalar op; 10 pmin (`b < a ? b : a`), 11 pmax
(`a < b ? b : a`). -/
def floatBin (is64 : Bool) (k : Nat) (x y : UInt64) : UInt64 :=
  let lt := if is64 then NumOp.f64_lt else NumOp.f32_lt
  if k == 10 then (if lt.evalBin y x != 0 then y else x)
  else if k == 11 then (if lt.evalBin x y != 0 then y else x)
  else (fOp is64 k).evalBin x y

/-- Two vectors to one vector (not `i8x16.shuffle`, which has an immediate). -/
def evalBin (c : Nat) (a b : V128) : V128 :=
  if c == 0x0e then build 8 fun i => let j := (b.lane 8 i).toNat; if j < 16 then a.lane 8 j else 0
  else if 0x23 ≤ c && c ≤ 0x40 then map2 (8 <<< ((c - 0x23) / 10)) (cmpI (8 <<< ((c - 0x23) / 10)) ((c - 0x23) % 10)) a b
  else if 0x41 ≤ c && c ≤ 0x46 then map2 32 (fun x y => boolLane ((fcmpOp false (c - 0x41)).evalBin x y != 0)) a b
  else if 0x47 ≤ c && c ≤ 0x4c then map2 64 (fun x y => boolLane ((fcmpOp true (c - 0x47)).evalBin x y != 0)) a b
  else if c == 0x4e then ⟨a.lo &&& b.lo, a.hi &&& b.hi⟩
  else if c == 0x4f then ⟨a.lo &&& ~~~b.lo, a.hi &&& ~~~b.hi⟩
  else if c == 0x50 then ⟨a.lo ||| b.lo, a.hi ||| b.hi⟩
  else if c == 0x51 then ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩
  else if c == 0x65 || c == 0x66 then narrow 8 (c == 0x65) a b
  else if c == 0x85 || c == 0x86 then narrow 16 (c == 0x85) a b
  else if c == 0x82 then map2 16 (fun x y => satS 16 ((sx 16 x * sx 16 y + 0x4000) >>> 15)) a b
  else if c == 0xba then build 32 fun i =>
    ofInt 32 (sx 16 (a.lane 16 (2 * i)) * sx 16 (b.lane 16 (2 * i)) +
      sx 16 (a.lane 16 (2 * i + 1)) * sx 16 (b.lane 16 (2 * i + 1)))
  else if 0xd6 ≤ c && c ≤ 0xdb then
    -- i64x2: eq, ne, lt_s, gt_s, le_s, ge_s.
    let j := if c == 0xd6 then 0 else if c == 0xd7 then 1 else 2 * (c - 0xd8) + 2
    map2 64 (cmpI 64 j) a b
  else if 0xe0 ≤ c && c < 0xec then map2 32 (floatBin false (c - 0xe0)) a b
  else if 0xec ≤ c && c < 0xf8 then map2 64 (floatBin true (c - 0xec)) a b
  else
    let w := blockW c
    let k := blockK c
    -- 28 low_s, 29 high_s, 30 low_u, 31 high_u.
    if k ≥ 28 then extMul w (k < 30) (if k % 2 == 1 then 64 / (w / 2) else 0) a b
    else map2 w (intBin w k) a b

/-- `i8x16.shuffle`: lane `i` is lane `s[i]` of the 32 lanes of `a` then `b`. -/
def shuffle (s a b : V128) : V128 :=
  build 8 fun i => let j := (s.lane 8 i).toNat; if j < 16 then a.lane 8 j else b.lane 8 (j - 16)

/-- `v128.bitselect`: the bits of `a` where `m` is 1, of `b` where it is 0. -/
def bitselect (a b m : V128) : V128 :=
  ⟨(a.lo &&& m.lo) ||| (b.lo &&& ~~~m.lo), (a.hi &&& m.hi) ||| (b.hi &&& ~~~m.hi)⟩

/-- Whether every lane of `w` bits is not zero, from lane `i` on. -/
def allTrue (w : Nat) (a : V128) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, i => a.lane w i != 0 && allTrue w a k (i + 1)

/-- The top bits of the lanes of `w` bits, lane `i` in bit `i`. -/
def bitmask (w : Nat) (a : V128) : Nat → Nat → UInt64 → UInt64
  | 0, _, acc => acc
  | k + 1, i, acc => bitmask w a k (i + 1) (acc ||| ((a.lane w i >>> (w - 1).toUInt64) <<< i.toUInt64))

/-- One vector to an i32 slot: `any_true` (0x53), `all_true` (offset 3), `bitmask` (4). -/
def evalTest (c : Nat) (a : V128) : UInt64 :=
  if c == 0x53 then (if a.lo != 0 || a.hi != 0 then 1 else 0)
  else
    let w := blockW c
    if blockK c == 3 then (if allTrue w a (128 / w) 0 then 1 else 0)
    else bitmask w a (128 / w) 0 0

/-- A vector shifted lane by lane by the i32 `n`. -/
def evalShift (c : Nat) (a : V128) (n : UInt64) : V128 :=
  let w := blockW c
  map1 w (shiftLane w (blockK c) n) a

/-- The width in bits of the lanes that a splat, extract or replace opcode names. -/
def laneW (c : Nat) : Nat :=
  if c == 0x0f || (0x15 ≤ c && c ≤ 0x17) then 8
  else if c == 0x10 || (0x18 ≤ c && c ≤ 0x1a) then 16
  else if c == 0x11 || c == 0x13 || c == 0x1b || c == 0x1c || c == 0x1f || c == 0x20 then 32
  else 64

def splat (c : Nat) (x : UInt64) : V128 := build (laneW c) fun _ => x

/-- The slot bits of lane `l`: an i32 result is zero-extended, after sign extension of
the lane for `extract_lane_s` (0x15, 0x18). -/
def extract (c l : Nat) (a : V128) : UInt64 :=
  let w := laneW c
  let x := a.lane w l
  if c == 0x15 || c == 0x18 then ofInt 32 (sx w x) else x

def replace (c l : Nat) (a : V128) (x : UInt64) : V128 := a.setLane (laneW c) l x

/-- The vector that a load of opcode `c` makes from the bytes read (`x`, zero-extended;
not for `v128.load`, which reads both halves). -/
def ofLoad (c : Nat) (x : UInt64) : V128 :=
  let v : V128 := ⟨x, 0⟩
  if 0x01 ≤ c && c ≤ 0x06 then
    let w := 16 <<< ((c - 1) / 2)
    extendLanes w (c % 2 == 1) 0 v
  else if 0x07 ≤ c && c ≤ 0x0a then build (8 <<< (c - 0x07)) fun _ => x
  else v

end V128
end L4Factoidal.WasmVM
