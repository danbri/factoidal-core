/-
L4Factoidal.WasmVM.Numerics: the numeric instructions on 64-bit slots
(https://github.com/danbri/factoidal/issues/1244).

A slot holds the bits of a value: i32 and f32 zero-extended, i64 and f64 whole.
`evalUn`/`evalBin` give the result bits. An instruction that can trap
(`NumOp.mayTrap`) is first checked with `trapUn`/`trapBin`, which return `none`
when it does not trap; `Option.none` is a scalar, so the common path allocates
nothing.

Integers use `UInt32`/`UInt64` and the signed views `Int32`/`Int64`. Lean's shifts
are already modulo the bit width; signed division and remainder are checked for the
two trapping cases before they run.

Floats use `Float32`/`Float` through `ofBits`/`toBits` (a copy of the bits in C).
Where the result could depend on the host C library or hardware:
- `+ - * / sqrt`: IEEE 754 operations of the hardware, correctly rounded. A NaN result
  is the hardware's: on ARM64 and x86-64 an arithmetic NaN (quiet bit set), which the
  spec allows; for non-NaN inputs the default NaN, which is canonical.
- `ceil`, `floor`: C `ceilf`/`floor`, exact by IEEE 754. `trunc` and `nearest` are
  written here from `ceil`/`floor`, so C `round` (half away from zero) is not used.
- `abs`, `neg`, `copysign`: on bits only, as the spec requires (no NaN change).
- `min`, `max`: explicit NaN and signed-zero cases; the NaN result is `a + b`, an
  arithmetic NaN.
- conversions from integers: one C conversion straight to the target width, so
  i64 → f32 is rounded once (a path through f64 would round twice).
- truncations: range-checked here; the conversion itself is Lean's saturating cast,
  exact inside the range. The saturating instructions use that cast directly.
-/
import L4Factoidal.WasmVM.Syntax

namespace L4Factoidal.WasmVM

/-- Why a run trapped. `message` gives the text the spec test suite uses. -/
inductive Trap where
  | unreachable | divByZero | intOverflow | invalidConversion
  | memOOB | tableOOB | undefinedElement | uninitializedElement
  | indirectTypeMismatch | nullReference | callStackExhausted
  | dataOOB | elemOOB
  | host (msg : String)
  deriving BEq, Repr, Inhabited

def Trap.message : Trap → String
  | .unreachable => "unreachable"
  | .divByZero => "integer divide by zero"
  | .intOverflow => "integer overflow"
  | .invalidConversion => "invalid conversion to integer"
  | .memOOB => "out of bounds memory access"
  | .tableOOB => "out of bounds table access"
  | .undefinedElement => "undefined element"
  | .uninitializedElement => "uninitialized element"
  | .indirectTypeMismatch => "indirect call type mismatch"
  | .nullReference => "null reference"
  | .callStackExhausted => "call stack exhausted"
  | .dataOOB => "out of bounds memory access"
  | .elemOOB => "out of bounds table access"
  | .host m => m

namespace Num

@[inline] def f32 (a : UInt64) : Float32 := Float32.ofBits a.toUInt32
@[inline] def ofF32 (x : Float32) : UInt64 := x.toBits.toUInt64
@[inline] def f64 (a : UInt64) : Float := Float.ofBits a
@[inline] def ofF64 (x : Float) : UInt64 := x.toBits
@[inline] def ofBool (b : Bool) : UInt64 := if b then 1 else 0
@[inline] def lo (a : UInt64) : UInt32 := a.toUInt32
@[inline] def ofI32 (x : UInt32) : UInt64 := x.toUInt64

/-! ### Bit counts -/

def popcnt64 (x : UInt64) : UInt64 :=
  let x : UInt64 := x - ((x >>> 1) &&& (0x5555555555555555 : UInt64))
  let x : UInt64 := (x &&& (0x3333333333333333 : UInt64)) + ((x >>> 2) &&& (0x3333333333333333 : UInt64))
  let x : UInt64 := (x + (x >>> 4)) &&& (0x0F0F0F0F0F0F0F0F : UInt64)
  (x * (0x0101010101010101 : UInt64)) >>> (56 : UInt64)

def clz64 (x : UInt64) : UInt64 := Id.run do
  if x == 0 then return 64
  let mut n : UInt64 := 0
  let mut x := x
  if x &&& (0xFFFFFFFF00000000 : UInt64) == 0 then n := n + 32; x := x <<< 32
  if x &&& (0xFFFF000000000000 : UInt64) == 0 then n := n + 16; x := x <<< 16
  if x &&& (0xFF00000000000000 : UInt64) == 0 then n := n + 8; x := x <<< 8
  if x &&& (0xF000000000000000 : UInt64) == 0 then n := n + 4; x := x <<< 4
  if x &&& (0xC000000000000000 : UInt64) == 0 then n := n + 2; x := x <<< 2
  if x &&& (0x8000000000000000 : UInt64) == 0 then n := n + 1
  return n

def ctz64 (x : UInt64) : UInt64 :=
  if x == 0 then 64 else popcnt64 ((x &&& (0 - x)) - 1)

def clz32 (x : UInt32) : UInt64 := clz64 (x.toUInt64 <<< 32) - (if x == 0 then 32 else 0)
def ctz32 (x : UInt32) : UInt64 := if x == 0 then 32 else ctz64 x.toUInt64
def popcnt32 (x : UInt32) : UInt64 := popcnt64 x.toUInt64

/-! ### Floats -/

@[inline] def copysign32 (a b : UInt32) : UInt32 := (a &&& (0x7FFFFFFF : UInt32)) ||| (b &&& (0x80000000 : UInt32))
@[inline] def copysign64 (a b : UInt64) : UInt64 :=
  (a &&& (0x7FFFFFFFFFFFFFFF : UInt64)) ||| (b &&& (0x8000000000000000 : UInt64))

def truncF32 (x : Float32) : Float32 := if x < 0 then x.ceil else x.floor
def truncF64 (x : Float) : Float := if x < 0 then x.ceil else x.floor

/-- Round to nearest, ties to even; the sign of zero is kept. -/
def nearestF32 (x : Float32) : Float32 :=
  if x.isNaN then x + x
  else if x.abs ≥ 8388608.0 then x
  else
    let r := x.floor
    let d := x - r
    let y := if d < 0.5 then r else if d > 0.5 then r + 1.0
      else if (r * 0.5).floor == r * 0.5 then r else r + 1.0
    Float32.ofBits (copysign32 y.toBits x.toBits)

def nearestF64 (x : Float) : Float :=
  if x.isNaN then x + x
  else if x.abs ≥ 4503599627370496.0 then x
  else
    let r := x.floor
    let d := x - r
    let y := if d < 0.5 then r else if d > 0.5 then r + 1.0
      else if (r * 0.5).floor == r * 0.5 then r else r + 1.0
    Float.ofBits (copysign64 y.toBits x.toBits)

def minF32 (a b : UInt32) : UInt32 :=
  let x := Float32.ofBits a; let y := Float32.ofBits b
  if x.isNaN || y.isNaN then (x + y).toBits
  else if x == y then a ||| b
  else if x < y then a else b

def maxF32 (a b : UInt32) : UInt32 :=
  let x := Float32.ofBits a; let y := Float32.ofBits b
  if x.isNaN || y.isNaN then (x + y).toBits
  else if x == y then a &&& b
  else if x > y then a else b

def minF64 (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a; let y := Float.ofBits b
  if x.isNaN || y.isNaN then (x + y).toBits
  else if x == y then a ||| b
  else if x < y then a else b

def maxF64 (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a; let y := Float.ofBits b
  if x.isNaN || y.isNaN then (x + y).toBits
  else if x == y then a &&& b
  else if x > y then a else b

/-! ### Truncation ranges. `x` is already truncated toward zero, and not NaN. -/

@[inline] def inI32 (t : Float) : Bool := t ≥ -2147483648.0 && t ≤ 2147483647.0
@[inline] def inU32 (t : Float) : Bool := t > -1.0 && t < 4294967296.0
@[inline] def inI64 (t : Float) : Bool := t ≥ -9223372036854775808.0 && t < 9223372036854775808.0
@[inline] def inU64 (t : Float) : Bool := t > -1.0 && t < 18446744073709551616.0

/-- The f64 value of a float slot of the operand type of a truncation. -/
@[inline] def truncSrc (fromF64 : Bool) (a : UInt64) : Float :=
  if fromF64 then f64 a else (f32 a).toFloat

def truncCheck (fromF64 : Bool) (inRange : Float → Bool) (a : UInt64) : Option Trap :=
  let x := truncSrc fromF64 a
  if x.isNaN then some .invalidConversion
  else if inRange (truncF64 x) then none else some .intOverflow

end Num

namespace NumOp
open Num

/-- Binary instructions take two operands; the rest take one. -/
def isBinary : NumOp → Bool
  | i32_eq | i32_ne | i32_lt_s | i32_lt_u | i32_gt_s | i32_gt_u
  | i32_le_s | i32_le_u | i32_ge_s | i32_ge_u
  | i64_eq | i64_ne | i64_lt_s | i64_lt_u | i64_gt_s | i64_gt_u
  | i64_le_s | i64_le_u | i64_ge_s | i64_ge_u
  | f32_eq | f32_ne | f32_lt | f32_gt | f32_le | f32_ge
  | f64_eq | f64_ne | f64_lt | f64_gt | f64_le | f64_ge
  | i32_add | i32_sub | i32_mul | i32_div_s | i32_div_u
  | i32_rem_s | i32_rem_u | i32_and | i32_or | i32_xor | i32_shl | i32_shr_s | i32_shr_u
  | i32_rotl | i32_rotr
  | i64_add | i64_sub | i64_mul | i64_div_s | i64_div_u
  | i64_rem_s | i64_rem_u | i64_and | i64_or | i64_xor | i64_shl | i64_shr_s | i64_shr_u
  | i64_rotl | i64_rotr
  | f32_add | f32_sub | f32_mul | f32_div | f32_min | f32_max | f32_copysign
  | f64_add | f64_sub | f64_mul | f64_div | f64_min | f64_max | f64_copysign => true
  | _ => false

def mayTrap : NumOp → Bool
  | i32_div_s | i32_div_u | i32_rem_s | i32_rem_u
  | i64_div_s | i64_div_u | i64_rem_s | i64_rem_u
  | i32_trunc_f32_s | i32_trunc_f32_u | i32_trunc_f64_s | i32_trunc_f64_u
  | i64_trunc_f32_s | i64_trunc_f32_u | i64_trunc_f64_s | i64_trunc_f64_u => true
  | _ => false

/-- Operand and result types: `(operand, result)`. Binary instructions take two
operands of the operand type. -/
def sig : NumOp → ValType × ValType
  | i32_eqz => (.i32, .i32)
  | i32_eq | i32_ne | i32_lt_s | i32_lt_u | i32_gt_s | i32_gt_u
  | i32_le_s | i32_le_u | i32_ge_s | i32_ge_u => (.i32, .i32)
  | i64_eqz | i64_eq | i64_ne | i64_lt_s | i64_lt_u | i64_gt_s | i64_gt_u
  | i64_le_s | i64_le_u | i64_ge_s | i64_ge_u => (.i64, .i32)
  | f32_eq | f32_ne | f32_lt | f32_gt | f32_le | f32_ge => (.f32, .i32)
  | f64_eq | f64_ne | f64_lt | f64_gt | f64_le | f64_ge => (.f64, .i32)
  | i32_clz | i32_ctz | i32_popcnt | i32_add | i32_sub | i32_mul | i32_div_s | i32_div_u
  | i32_rem_s | i32_rem_u | i32_and | i32_or | i32_xor | i32_shl | i32_shr_s | i32_shr_u
  | i32_rotl | i32_rotr => (.i32, .i32)
  | i64_clz | i64_ctz | i64_popcnt | i64_add | i64_sub | i64_mul | i64_div_s | i64_div_u
  | i64_rem_s | i64_rem_u | i64_and | i64_or | i64_xor | i64_shl | i64_shr_s | i64_shr_u
  | i64_rotl | i64_rotr => (.i64, .i64)
  | f32_abs | f32_neg | f32_ceil | f32_floor | f32_trunc | f32_nearest | f32_sqrt
  | f32_add | f32_sub | f32_mul | f32_div | f32_min | f32_max | f32_copysign => (.f32, .f32)
  | f64_abs | f64_neg | f64_ceil | f64_floor | f64_trunc | f64_nearest | f64_sqrt
  | f64_add | f64_sub | f64_mul | f64_div | f64_min | f64_max | f64_copysign => (.f64, .f64)
  | i32_wrap_i64 => (.i64, .i32)
  | i32_trunc_f32_s | i32_trunc_f32_u => (.f32, .i32)
  | i32_trunc_f64_s | i32_trunc_f64_u => (.f64, .i32)
  | i64_extend_i32_s | i64_extend_i32_u => (.i32, .i64)
  | i64_trunc_f32_s | i64_trunc_f32_u => (.f32, .i64)
  | i64_trunc_f64_s | i64_trunc_f64_u => (.f64, .i64)
  | f32_convert_i32_s | f32_convert_i32_u => (.i32, .f32)
  | f32_convert_i64_s | f32_convert_i64_u => (.i64, .f32)
  | f32_demote_f64 => (.f64, .f32)
  | f64_convert_i32_s | f64_convert_i32_u => (.i32, .f64)
  | f64_convert_i64_s | f64_convert_i64_u => (.i64, .f64)
  | f64_promote_f32 => (.f32, .f64)
  | i32_reinterpret_f32 => (.f32, .i32)
  | i64_reinterpret_f64 => (.f64, .i64)
  | f32_reinterpret_i32 => (.i32, .f32)
  | f64_reinterpret_i64 => (.i64, .f64)
  | i32_extend8_s | i32_extend16_s => (.i32, .i32)
  | i64_extend8_s | i64_extend16_s | i64_extend32_s => (.i64, .i64)
  | i32_trunc_sat_f32_s | i32_trunc_sat_f32_u => (.f32, .i32)
  | i32_trunc_sat_f64_s | i32_trunc_sat_f64_u => (.f64, .i32)
  | i64_trunc_sat_f32_s | i64_trunc_sat_f32_u => (.f32, .i64)
  | i64_trunc_sat_f64_s | i64_trunc_sat_f64_u => (.f64, .i64)

/-- Trap check of a one-operand instruction. -/
def trapUn (op : NumOp) (a : UInt64) : Option Trap :=
  match op with
  | i32_trunc_f32_s => truncCheck false inI32 a
  | i32_trunc_f32_u => truncCheck false inU32 a
  | i32_trunc_f64_s => truncCheck true inI32 a
  | i32_trunc_f64_u => truncCheck true inU32 a
  | i64_trunc_f32_s => truncCheck false inI64 a
  | i64_trunc_f32_u => truncCheck false inU64 a
  | i64_trunc_f64_s => truncCheck true inI64 a
  | i64_trunc_f64_u => truncCheck true inU64 a
  | _ => none

/-- Trap check of a two-operand instruction. -/
def trapBin (op : NumOp) (a b : UInt64) : Option Trap :=
  match op with
  | i32_div_s => if lo b == 0 then some .divByZero
      else if lo a == 0x80000000 && lo b == 0xFFFFFFFF then some .intOverflow else none
  | i32_div_u | i32_rem_s | i32_rem_u => if lo b == 0 then some .divByZero else none
  | i64_div_s => if b == 0 then some .divByZero
      else if a == (0x8000000000000000 : UInt64) && b == (0xFFFFFFFFFFFFFFFF : UInt64) then some .intOverflow
      else none
  | i64_div_u | i64_rem_s | i64_rem_u => if b == 0 then some .divByZero else none
  | _ => none

/-- Result of a one-operand instruction (after `trapUn` returned `none`). -/
def evalUn (op : NumOp) (a : UInt64) : UInt64 :=
  match op with
  | i32_eqz => ofBool (lo a == 0)
  | i64_eqz => ofBool (a == 0)
  | i32_clz => clz32 (lo a)
  | i32_ctz => ctz32 (lo a)
  | i32_popcnt => popcnt32 (lo a)
  | i64_clz => clz64 a
  | i64_ctz => ctz64 a
  | i64_popcnt => popcnt64 a
  | f32_abs => a &&& (0x7FFFFFFF : UInt64)
  | f32_neg => (a ^^^ (0x80000000 : UInt64)) &&& (0xFFFFFFFF : UInt64)
  | f32_ceil => ofF32 (f32 a).ceil
  | f32_floor => ofF32 (f32 a).floor
  | f32_trunc => ofF32 (truncF32 (f32 a))
  | f32_nearest => ofF32 (nearestF32 (f32 a))
  | f32_sqrt => ofF32 (f32 a).sqrt
  | f64_abs => a &&& (0x7FFFFFFFFFFFFFFF : UInt64)
  | f64_neg => a ^^^ (0x8000000000000000 : UInt64)
  | f64_ceil => ofF64 (f64 a).ceil
  | f64_floor => ofF64 (f64 a).floor
  | f64_trunc => ofF64 (truncF64 (f64 a))
  | f64_nearest => ofF64 (nearestF64 (f64 a))
  | f64_sqrt => ofF64 (f64 a).sqrt
  | i32_wrap_i64 => a &&& (0xFFFFFFFF : UInt64)
  | i32_trunc_f32_s | i32_trunc_sat_f32_s => ofI32 (truncSrc false a).toInt32.toUInt32
  | i32_trunc_f32_u | i32_trunc_sat_f32_u => ofI32 (truncSrc false a).toUInt32
  | i32_trunc_f64_s | i32_trunc_sat_f64_s => ofI32 (truncSrc true a).toInt32.toUInt32
  | i32_trunc_f64_u | i32_trunc_sat_f64_u => ofI32 (truncSrc true a).toUInt32
  | i64_trunc_f32_s | i64_trunc_sat_f32_s => (truncSrc false a).toInt64.toUInt64
  | i64_trunc_f32_u | i64_trunc_sat_f32_u => (truncSrc false a).toUInt64
  | i64_trunc_f64_s | i64_trunc_sat_f64_s => (truncSrc true a).toInt64.toUInt64
  | i64_trunc_f64_u | i64_trunc_sat_f64_u => (truncSrc true a).toUInt64
  | i64_extend_i32_s => (lo a).toInt32.toInt64.toUInt64
  | i64_extend_i32_u => a &&& (0xFFFFFFFF : UInt64)
  | f32_convert_i32_s => ofF32 (lo a).toInt32.toFloat32
  | f32_convert_i32_u => ofF32 (lo a).toFloat32
  | f32_convert_i64_s => ofF32 a.toInt64.toFloat32
  | f32_convert_i64_u => ofF32 a.toFloat32
  | f32_demote_f64 => ofF32 (f64 a).toFloat32
  | f64_convert_i32_s => ofF64 (lo a).toInt32.toFloat
  | f64_convert_i32_u => ofF64 (lo a).toFloat
  | f64_convert_i64_s => ofF64 a.toInt64.toFloat
  | f64_convert_i64_u => ofF64 a.toFloat
  | f64_promote_f32 => ofF64 (f32 a).toFloat
  | i32_reinterpret_f32 | i64_reinterpret_f64 | f32_reinterpret_i32 | f64_reinterpret_i64 => a
  | i32_extend8_s => ofI32 a.toUInt8.toInt8.toInt32.toUInt32
  | i32_extend16_s => ofI32 a.toUInt16.toInt16.toInt32.toUInt32
  | i64_extend8_s => a.toUInt8.toInt8.toInt64.toUInt64
  | i64_extend16_s => a.toUInt16.toInt16.toInt64.toUInt64
  | i64_extend32_s => a.toUInt32.toInt32.toInt64.toUInt64
  | _ => 0

/-- Result of a two-operand instruction (after `trapBin` returned `none`). -/
@[inline] def evalBin (op : NumOp) (a b : UInt64) : UInt64 :=
  match op with
  | i32_eq => ofBool (lo a == lo b)
  | i32_ne => ofBool (lo a != lo b)
  | i32_lt_s => ofBool ((lo a).toInt32 < (lo b).toInt32)
  | i32_lt_u => ofBool (lo a < lo b)
  | i32_gt_s => ofBool ((lo a).toInt32 > (lo b).toInt32)
  | i32_gt_u => ofBool (lo a > lo b)
  | i32_le_s => ofBool ((lo a).toInt32 ≤ (lo b).toInt32)
  | i32_le_u => ofBool (lo a ≤ lo b)
  | i32_ge_s => ofBool ((lo a).toInt32 ≥ (lo b).toInt32)
  | i32_ge_u => ofBool (lo a ≥ lo b)
  | i64_eq => ofBool (a == b)
  | i64_ne => ofBool (a != b)
  | i64_lt_s => ofBool (a.toInt64 < b.toInt64)
  | i64_lt_u => ofBool (a < b)
  | i64_gt_s => ofBool (a.toInt64 > b.toInt64)
  | i64_gt_u => ofBool (a > b)
  | i64_le_s => ofBool (a.toInt64 ≤ b.toInt64)
  | i64_le_u => ofBool (a ≤ b)
  | i64_ge_s => ofBool (a.toInt64 ≥ b.toInt64)
  | i64_ge_u => ofBool (a ≥ b)
  | f32_eq => ofBool (f32 a == f32 b)
  | f32_ne => ofBool (!(f32 a == f32 b))
  | f32_lt => ofBool (f32 a < f32 b)
  | f32_gt => ofBool (f32 a > f32 b)
  | f32_le => ofBool (f32 a ≤ f32 b)
  | f32_ge => ofBool (f32 a ≥ f32 b)
  | f64_eq => ofBool (f64 a == f64 b)
  | f64_ne => ofBool (!(f64 a == f64 b))
  | f64_lt => ofBool (f64 a < f64 b)
  | f64_gt => ofBool (f64 a > f64 b)
  | f64_le => ofBool (f64 a ≤ f64 b)
  | f64_ge => ofBool (f64 a ≥ f64 b)
  | i32_add => ofI32 (lo a + lo b)
  | i32_sub => ofI32 (lo a - lo b)
  | i32_mul => ofI32 (lo a * lo b)
  | i32_div_s => ofI32 ((lo a).toInt32 / (lo b).toInt32).toUInt32
  | i32_div_u => ofI32 (lo a / lo b)
  | i32_rem_s => if lo b == 0xFFFFFFFF then 0 else ofI32 ((lo a).toInt32 % (lo b).toInt32).toUInt32
  | i32_rem_u => ofI32 (lo a % lo b)
  | i32_and => a &&& b
  | i32_or => a ||| b
  | i32_xor => a ^^^ b
  | i32_shl => ofI32 (lo a <<< lo b)
  | i32_shr_s => ofI32 ((lo a).toInt32 >>> (lo b).toInt32).toUInt32
  | i32_shr_u => ofI32 (lo a >>> lo b)
  | i32_rotl => let k := lo b % 32; ofI32 ((lo a <<< k) ||| (lo a >>> (32 - k)))
  | i32_rotr => let k := lo b % 32; ofI32 ((lo a >>> k) ||| (lo a <<< (32 - k)))
  | i64_add => a + b
  | i64_sub => a - b
  | i64_mul => a * b
  | i64_div_s => (a.toInt64 / b.toInt64).toUInt64
  | i64_div_u => a / b
  | i64_rem_s => if b == (0xFFFFFFFFFFFFFFFF : UInt64) then 0 else (a.toInt64 % b.toInt64).toUInt64
  | i64_rem_u => a % b
  | i64_and => a &&& b
  | i64_or => a ||| b
  | i64_xor => a ^^^ b
  | i64_shl => a <<< b
  | i64_shr_s => (a.toInt64 >>> b.toInt64).toUInt64
  | i64_shr_u => a >>> b
  | i64_rotl => let k := b % 64; (a <<< k) ||| (a >>> (64 - k))
  | i64_rotr => let k := b % 64; (a >>> k) ||| (a <<< (64 - k))
  | f32_add => ofF32 (f32 a + f32 b)
  | f32_sub => ofF32 (f32 a - f32 b)
  | f32_mul => ofF32 (f32 a * f32 b)
  | f32_div => ofF32 (f32 a / f32 b)
  | f32_min => ofI32 (minF32 (lo a) (lo b))
  | f32_max => ofI32 (maxF32 (lo a) (lo b))
  | f32_copysign => ofI32 (copysign32 (lo a) (lo b))
  | f64_add => ofF64 (f64 a + f64 b)
  | f64_sub => ofF64 (f64 a - f64 b)
  | f64_mul => ofF64 (f64 a * f64 b)
  | f64_div => ofF64 (f64 a / f64 b)
  | f64_min => minF64 a b
  | f64_max => maxF64 a b
  | f64_copysign => copysign64 a b
  | _ => 0

end NumOp
end L4Factoidal.WasmVM
