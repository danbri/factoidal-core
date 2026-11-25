import L4Factoidal.JS.RyuTables

/-!
# L4Factoidal.JS.Ryu — shortest decimal digits of a double, on 64-bit words

`Number::toString` (ECMA-262 §6.1.6.1.20) writes the fewest decimal digits `s` (with exponent `n`)
such that `s × 10^(n-k)` reads back as the value; of two such, the one nearer the value; of two
equally near, the even one (§6.1.6.1.20 Note 2, which V8 and QuickJS-NG follow).

`XPath4.shortestDigits` finds these digits with exact rational arithmetic (`Nat`, so GMP), and
reads each candidate back: about 20 µs a conversion
(https://github.com/danbri/factoidal-core/issues/1076). This module computes the same digits with
Ryū (Ulf Adams, "Ryū: fast float-to-string conversion", PLDI 2018; the algorithm of `d2s.c` of
the reference implementation, with its full 128-bit tables): fixed-width `UInt64` arithmetic, a
128-bit product made from four 32-bit products, two constant tables (`RyuTables.lean`), no `Nat`
arithmetic and no `Float` arithmetic.

Status: checked by differential test against `XPath4.shortestDigits` and against Node and
QuickJS-NG (`tools/ryu-differential.sh`); not proved. `numToString` keeps the exact algorithm as
`numToStringRef` (`JS/Number.lean`).
-/
namespace L4Factoidal.JS.Ryu

/-- The high 64 bits of the 128-bit product `a × b`, from four 32 × 32-bit products. -/
@[inline] def mulHi (a b : UInt64) : UInt64 :=
  let aLo := a &&& 0xFFFFFFFF
  let aHi := a >>> 32
  let bLo := b &&& 0xFFFFFFFF
  let bHi := b >>> 32
  let p0 := aLo * bLo
  let p1 := aLo * bHi
  let p2 := aHi * bLo
  let p3 := aHi * bHi
  let mid := (p0 >>> 32) + (p1 &&& 0xFFFFFFFF) + (p2 &&& 0xFFFFFFFF)
  p3 + (p1 >>> 32) + (p2 >>> 32) + (mid >>> 32)

/-- `⌊m × (hi·2^64 + lo) / 2^j⌋` for `64 < j < 128` and a result below 2^64 (Ryū `mulShift64`). -/
@[inline] def mulShift64 (m lo hi j : UInt64) : UInt64 :=
  let b0hi := mulHi m lo
  let b2lo := m * hi
  let b2hi := mulHi m hi
  let sum := b0hi + b2lo
  let h := b2hi + (if sum < b0hi then 1 else 0)
  let d := j - 64
  (sum >>> d) ||| (h <<< (64 - d))

/-- `⌊log₂ 5^e⌋ + 1` for `e ≤ 3528` (Ryū `pow5bits`). -/
@[inline] def pow5bits (e : UInt64) : UInt64 := ((e * 1217359) >>> 19) + 1
/-- `⌊log₁₀ 2^e⌋` for `e ≤ 1650` (Ryū `log10Pow2`). -/
@[inline] def log10Pow2 (e : UInt64) : UInt64 := (e * 78913) >>> 18
/-- `⌊log₁₀ 5^e⌋` for `e ≤ 2620` (Ryū `log10Pow5`). -/
@[inline] def log10Pow5 (e : UInt64) : UInt64 := (e * 732923) >>> 20

/-- The number of factors 5 of `v`, plus `count` (at most 64 steps; `v < 2^64` has at most 27). -/
def pow5Factor (v count : UInt64) : Nat → UInt64
  | 0 => count
  | fuel + 1 => if v % 5 == 0 then pow5Factor (v / 5) (count + 1) fuel else count

@[inline] def multipleOfPowerOf5 (v p : UInt64) : Bool := pow5Factor v 0 64 ≥ p

/-- A positive decimal `digits × 10^exp10`. -/
structure Decimal where
  digits : UInt64
  exp10 : Int
  deriving BEq, Repr

/-- The last step of the exact-bounds case of Ryū (`vmIsTrailingZeros || vrIsTrailingZeros`):
round half to even when the removed digits are exactly one half. -/
@[inline] def finishExact (vr vm removed lastDig : UInt64) (vmTZ vrTZ accept : Bool) (e10 : Int) :
    Decimal :=
  let lastDig := if vrTZ && lastDig == 5 && vr % 2 == 0 then 4 else lastDig
  let out := vr + (if (vr == vm && (!accept || !vmTZ)) || lastDig ≥ 5 then 1 else 0)
  { digits := out, exp10 := e10 + Int.ofNat removed.toNat }

/-- Remove digits while the lower bound `vm` ends in zero (at most 20 steps). -/
def loopVmZeros (vr vp vm removed lastDig : UInt64) (vrTZ accept : Bool) (e10 : Int) : Nat → Decimal
  | 0 => finishExact vr vm removed lastDig true vrTZ accept e10
  | fuel + 1 =>
    if vm % 10 == 0 && vm != 0 then
      loopVmZeros (vr / 10) (vp / 10) (vm / 10) (removed + 1) (vr % 10) (vrTZ && lastDig == 0) accept
        e10 fuel
    else finishExact vr vm removed lastDig true vrTZ accept e10

/-- Remove digits while the interval `(vm, vp)` holds a shorter decimal, keeping track of
whether the removed digits of `vm` and `vr` are all zero (at most 20 steps). -/
def loopExact (vr vp vm removed lastDig : UInt64) (vmTZ vrTZ accept : Bool) (e10 : Int) :
    Nat → Decimal
  | 0 =>
    if vmTZ then loopVmZeros vr vp vm removed lastDig vrTZ accept e10 24
    else finishExact vr vm removed lastDig false vrTZ accept e10
  | fuel + 1 =>
    if vp / 10 > vm / 10 then
      loopExact (vr / 10) (vp / 10) (vm / 10) (removed + 1) (vr % 10) (vmTZ && vm % 10 == 0)
        (vrTZ && lastDig == 0) accept e10 fuel
    else if vmTZ then loopVmZeros vr vp vm removed lastDig vrTZ accept e10 24
    else finishExact vr vm removed lastDig false vrTZ accept e10

/-- Remove digits while the interval `(vm, vp)` holds a shorter decimal; the common case, where
no removed digits can be exactly one half (at most 20 steps). -/
def loopCommon (vr vp vm removed : UInt64) (roundUp : Bool) (e10 : Int) : Nat → Decimal
  | 0 => { digits := vr + (if vr == vm || roundUp then 1 else 0), exp10 := e10 + Int.ofNat removed.toNat }
  | fuel + 1 =>
    if vp / 10 > vm / 10 then
      loopCommon (vr / 10) (vp / 10) (vm / 10) (removed + 1) (vr % 10 ≥ 5) e10 fuel
    else { digits := vr + (if vr == vm || roundUp then 1 else 0), exp10 := e10 + Int.ofNat removed.toNat }

@[inline] def shorten (vr vp vm : UInt64) (vmTZ vrTZ accept : Bool) (e10 : Int) : Decimal :=
  if vmTZ || vrTZ then loopExact vr vp vm 0 0 vmTZ vrTZ accept e10 24
  else if vp / 100 > vm / 100 then loopCommon (vr / 100) (vp / 100) (vm / 100) 2 (vr % 100 ≥ 50) e10 24
  else loopCommon vr vp vm 0 false e10 24

/-- The shortest decimal of a positive finite double given by its bits (sign bit clear, not zero),
nearest the value, ties to even (Ryū `d2d`). May end in zeros; see `stripZeros`. -/
def d2d (bits : UInt64) : Decimal :=
  let ieeeMantissa := bits &&& 0xFFFFFFFFFFFFF
  let ieeeExponent := (bits >>> 52) &&& 0x7FF
  let m2 := if ieeeExponent == 0 then ieeeMantissa else ieeeMantissa ||| 0x10000000000000
  -- e2 = be - 1077 (Ryū subtracts 2 more than the IEEE bias and 52, for the factor 4 below)
  let be := if ieeeExponent == 0 then 1 else ieeeExponent
  let accept := m2 &&& 1 == 0
  let mv := 4 * m2
  let mmShift : UInt64 := if ieeeMantissa != 0 || ieeeExponent ≤ 1 then 1 else 0
  let mm := mv - 1 - mmShift
  if be ≥ 1077 then
    let e2 := be - 1077
    let q := log10Pow2 e2 - (if e2 > 3 then 1 else 0)
    let i := q + (124 + pow5bits q) - e2
    let lo := invTable[(2 * q).toNat]!
    let hi := invTable[(2 * q + 1).toNat]!
    let vr := mulShift64 mv lo hi i
    let vp := mulShift64 (mv + 2) lo hi i
    let vm := mulShift64 mm lo hi i
    let e10 : Int := Int.ofNat q.toNat
    if q ≤ 21 then
      if mv % 5 == 0 then shorten vr vp vm false (multipleOfPowerOf5 mv q) accept e10
      else if accept then shorten vr vp vm (multipleOfPowerOf5 mm q) false accept e10
      else shorten vr (vp - (if multipleOfPowerOf5 (mv + 2) q then 1 else 0)) vm false false accept e10
    else shorten vr vp vm false false accept e10
  else
    let ne := 1077 - be
    let q := log10Pow5 ne - (if ne > 1 then 1 else 0)
    let e10 : Int := Int.ofNat q.toNat - Int.ofNat ne.toNat
    let i := ne - q
    let j := q + 125 - pow5bits i
    let lo := powTable[(2 * i).toNat]!
    let hi := powTable[(2 * i + 1).toNat]!
    let vr := mulShift64 mv lo hi j
    let vp := mulShift64 (mv + 2) lo hi j
    let vm := mulShift64 mm lo hi j
    if q ≤ 1 then
      if accept then shorten vr vp vm (mmShift == 1) true accept e10
      else shorten vr (vp - 1) vm false true accept e10
    else if q < 63 then shorten vr vp vm false (mv &&& ((1 <<< q) - 1) == 0) accept e10
    else shorten vr vp vm false false accept e10

/-- Trailing zeros of the digits moved into the exponent (at most 20 steps). -/
def stripZeros (d : UInt64) (e : Int) : Nat → Decimal
  | 0 => { digits := d, exp10 := e }
  | fuel + 1 => if d != 0 && d % 10 == 0 then stripZeros (d / 10) (e + 1) fuel else { digits := d, exp10 := e }

/-- The shortest digits of a positive finite double `x`, with no trailing zeros:
`x` reads back from `digits × 10^exp10`. -/
@[inline] def shortest (x : Float) : Decimal :=
  let r := d2d (x.toBits &&& 0x7FFFFFFFFFFFFFFF)
  stripZeros r.digits r.exp10 24

/-! ## Writing digits -/

/-- `s` followed by the `w` lowest decimal digits of `v`, most significant first, with leading
zeros (callers pass `w ≤ 20`, so the recursion is at most 20 deep). -/
def pushDigits (s : String) (v : UInt64) : Nat → String
  | 0 => s
  | w + 1 => (pushDigits s (v / 10) w).push (Char.ofUInt8 (48 + (v % 10).toUInt8))

/-- The number of decimal digits of `v` (1 for 0; at most 20). -/
def digitCount (v : UInt64) (k : Nat) : Nat → Nat
  | 0 => k
  | fuel + 1 => if v < 10 then k else digitCount (v / 10) (k + 1) fuel

/-- `s` followed by `w` zeros (callers pass `w ≤ 21`). -/
def pushZeros (s : String) : Nat → String
  | 0 => s
  | w + 1 => pushZeros (s.push '0') w

/-- `10^i` for `i ≤ 19`. -/
def pow10 : Array UInt64 := #[1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000,
  1000000000, 10000000000, 100000000000, 1000000000000, 10000000000000, 100000000000000,
  1000000000000000, 10000000000000000, 100000000000000000, 1000000000000000000,
  10000000000000000000]

/-- The exponent part `e±N` of §6.1.6.1.20 steps 11 and 12. -/
@[inline] def pushExp (s : String) (e : Int) : String :=
  let s := s.push 'e' |>.push (if e < 0 then '-' else '+')
  let a : UInt64 := e.natAbs.toUInt64
  pushDigits s a (digitCount a 1 4)

/-- The layout of §6.1.6.1.20 steps 6 to 12 for `digits × 10^exp10` (`digits` with no trailing
zero, at most 17 digits), after the sign. -/
def layout (s : String) (d : Decimal) : String :=
  let v := d.digits
  let k := digitCount v 1 24
  let n : Int := d.exp10 + Int.ofNat k
  if Int.ofNat k ≤ n && n ≤ 21 then
    pushZeros (pushDigits s v k) (n - Int.ofNat k).toNat
  else if 0 < n && n ≤ 21 then
    let f := k - n.toNat
    let p := pow10[f]!
    pushDigits ((pushDigits s (v / p) n.toNat).push '.') (v % p) f
  else if -6 < n && n ≤ 0 then
    pushDigits (pushZeros (s ++ "0.") (-n).toNat) v k
  else
    let s := if k == 1 then pushDigits s v 1 else
      let p := pow10[k - 1]!
      pushDigits ((pushDigits s (v / p) 1).push '.') (v % p) (k - 1)
    pushExp s (n - 1)

/-- Number::toString (§6.1.6.1.20) of a finite, nonzero double, by Ryū. -/
def finiteToString (x : Float) : String :=
  layout (if x < 0 then "-" else "") (shortest x)

end L4Factoidal.JS.Ryu

namespace L4Factoidal.JS.Ryu

/-! Checks (tests, not proofs). Each table entry against the formula of `tools/gen-ryu-tables.py`. -/
#guard invTable.size == 684 && powTable.size == 652
#guard (List.range 342).all fun i =>
  let p := 5 ^ i
  invTable[2 * i]!.toNat + invTable[2 * i + 1]!.toNat * 2 ^ 64 == 2 ^ (Nat.log2 p + 125) / p + 1
#guard (List.range 326).all fun i =>
  let p := 5 ^ i
  let b := Nat.log2 p + 1
  powTable[2 * i]!.toNat + powTable[2 * i + 1]!.toNat * 2 ^ 64 ==
    (if b ≥ 125 then p / 2 ^ (b - 125) else p * 2 ^ (125 - b))
#guard mulHi 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF == 0xFFFFFFFFFFFFFFFE
#guard (List.range 64).all fun i =>
  let a : UInt64 := (0x9E3779B97F4A7C15 : UInt64) * (UInt64.ofNat i + 1)
  let b : UInt64 := (0xC2B2AE3D27D4EB4F : UInt64) ^^^ (UInt64.ofNat i <<< (7 : UInt64))
  (mulHi a b).toNat == a.toNat * b.toNat / 2 ^ 64
-- Values of ECMA-262 §6.1.6.1.20 as V8 and QuickJS-NG print them.
#guard [0.1, 0.30000000000000004, 123.456, 1e21, 1e-7, 0.000001, 5e-324,
  1.7976931348623157e308, -2.5, 4.35].map finiteToString ==
  ["0.1", "0.30000000000000004", "123.456", "1e+21", "1e-7", "0.000001", "5e-324",
   "1.7976931348623157e+308", "-2.5", "4.35"]

end L4Factoidal.JS.Ryu
