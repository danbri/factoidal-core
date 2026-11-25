import L4Factoidal.XPath4.Atomic
import L4Factoidal.JS.Ryu

/-!
# L4Factoidal.JS.NumFmt — toFixed, toExponential, toPrecision (§21.1.3.2, .3, .5)

Exact: a finite double is `num / den` (`XPath4.floatParts`), and the digits are the
integer nearest to `num / den × 10^k`, the larger on a tie, as the specification says;
no floating point rounding is involved.
-/
namespace L4Factoidal.JS.NumFmt

/-- The integer nearest to `num/den × 10^f`, the larger on a tie (§21.1.3.3 step 10). -/
def roundScaled (num den : Nat) (f : Int) : Nat :=
  let (a, b) := if f ≥ 0 then (num * 10 ^ f.toNat, den) else (num, den * 10 ^ (-f).toNat)
  (2 * a + b) / (2 * b)

/-- The exponent `e` with 10^e ≤ num/den < 10^(e+1) (num > 0). -/
def exponent (num den : Nat) : Int :=
  if num ≥ den then ((toString (num / den)).length : Int) - 1
  else
    let rec go : Nat → Nat → Int
      | 0, _ => -400
      | fuel + 1, k => if num * 10 ^ k ≥ den then -(k : Int) else go fuel (k + 1)
    go 400 1

def zeros (k : Nat) : String := String.ofList (List.replicate k '0')

/-- `n` as `f + 1` significant digits with exponent `e` (10^f ≤ n < 10^(f+1)). -/
def sigDigits (num den f : Nat) : String × Int :=
  let e := exponent num den
  let n := roundScaled num den (f - e)
  if n ≥ 10 ^ (f + 1) then (toString (roundScaled num den (f - (e + 1))), e + 1) else
  let s := toString n
  (zeros (f + 1 - s.length) ++ s, e)

/-- Number.prototype.toFixed (§21.1.3.3) of a finite x with |x| < 1e21. -/
def fixed (neg : Bool) (num den f : Nat) : String :=
  let n := roundScaled num den f
  let m := if n == 0 then "0" else toString n
  let m := if f == 0 then m else
    let m := if m.length ≤ f then zeros (f + 1 - m.length) ++ m else m
    String.ofList (m.toList.take (m.length - f)) ++ "." ++ String.ofList (m.toList.drop (m.length - f))
  (if neg && n != 0 then "-" else if neg then "-" else "") ++ m

def expStr (e : Int) : String := "e" ++ (if e < 0 then "-" else "+") ++ toString e.natAbs

/-- The text of toExponential from the digits `m` (`f + 1` of them) and the exponent `e`. -/
def expoLayout (neg : Bool) (m : String) (e : Int) (f : Nat) : String :=
  let body := if f == 0 then m else String.ofList (m.toList.take 1) ++ "." ++ String.ofList (m.toList.drop 1)
  (if neg then "-" else "") ++ body ++ expStr e

/-- Number.prototype.toExponential (§21.1.3.2) with `f` fraction digits, of x = ±num/den
(num = 0 for zero). -/
def expo (neg : Bool) (num den f : Nat) : String :=
  let (m, e) := if num == 0 then (zeros (f + 1), (0 : Int)) else sigDigits num den f
  expoLayout neg m e f

/-- The text of toPrecision from the digits `m` (`p` of them) and the exponent `e`. -/
def precisionLayout (neg : Bool) (m : String) (e : Int) (p : Nat) : String :=
  let sign := if neg then "-" else ""
  if e < -6 || e ≥ p then
    sign ++ (if p == 1 then m else String.ofList (m.toList.take 1) ++ "." ++ String.ofList (m.toList.drop 1)) ++ expStr e
  else if e == p - 1 then sign ++ m
  else if e ≥ 0 then
    sign ++ String.ofList (m.toList.take (e.toNat + 1)) ++ "." ++ String.ofList (m.toList.drop (e.toNat + 1))
  else sign ++ "0." ++ zeros ((-(e + 1)).toNat) ++ m

/-- Number.prototype.toPrecision (§21.1.3.5) with `p` significant digits. -/
def precision (neg : Bool) (num den p : Nat) : String :=
  let (m, e) := if num == 0 then (zeros p, (0 : Int)) else sigDigits num den (p - 1)
  precisionLayout neg m e p

/-- Sign and exact value of a finite double; zero (either sign) is positive. -/
def ofFloat (x : Float) : Bool × Nat × Nat :=
  if x == 0 then (false, 0, 1) else XPath4.floatParts x

/-- Trailing zeros off. -/
def strip (d : Nat) : Nat → Nat
  | 0 => d
  | fuel + 1 => if d != 0 && d % 10 == 0 then strip (d / 10) fuel else d

/-- The fraction digits of `toExponential(undefined)`: as many as the shortest digits that
read back as `x` (Number::toString) have, less one. -/
def shortestFracRef (x : Float) : Nat :=
  let (d0, _) := XPath4.shortestDigits false x.abs
  (toString (strip d0 30)).length - 1

/-- `shortestFracRef` by Ryū (`JS/Ryu.lean`), for a finite nonzero `x`. -/
def shortestFrac (x : Float) : Nat :=
  Ryu.digitCount (Ryu.shortest x).digits 1 24 - 1

/-! ## Fast paths on 64-bit words (issue 1076)

A finite nonzero double is `m × 2^e2` with `m < 2^53`. For a scale `10^k` with `k ≤ 19`, the
product `m × 10^k` fits in 128 bits, so the integer nearest `|x| × 10^k` (or its floor) is a
128-bit product and a shift, exactly. When the result does not fit in 64 bits, or the scale is
out of range, the functions below give `noFast` and the callers take the exact `Nat` path above.
Checked by differential test against that path (`leanjs numfmt-diff`); not proved. -/

/-- No fast answer: the caller takes the exact path. -/
def noFast : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The significand `m` of `|x| = m × 2^e2`, from the bits of a finite double. -/
@[inline] def mantOf (b : UInt64) : UInt64 :=
  let e := (b >>> 52) &&& 0x7FF
  let f := b &&& 0xFFFFFFFFFFFFF
  if e == 0 then f else f ||| 0x10000000000000

/-- The exponent `e2` of `|x| = m × 2^e2`, from the bits of a finite double. -/
@[inline] def expOf (b : UInt64) : Int :=
  let e := (b >>> 52) &&& 0x7FF
  (if e == 0 then 1 else Int.ofNat e.toNat) - 1075

/-- `⌊m × 2^e2 × 10^k⌋` (`round = false`), or the integer nearest it, the larger on a tie
(`round = true`), for `m < 2^53` and `k ≤ 19`; `noFast` when that is 2^64 - 1 or more. -/
def scaled (m : UInt64) (e2 : Int) (k : Nat) (round : Bool) : UInt64 :=
  let p := Ryu.pow10[k]!
  let lo := m * p
  let hi := Ryu.mulHi m p
  if e2 ≥ 0 then
    let e := e2.toNat
    if hi == 0 && e < 64 then
      let r := lo <<< e.toUInt64
      if r >>> e.toUInt64 == lo then r else noFast
    else noFast
  else
    let s := (-e2).toNat
    -- m × 10^k < 2^117, so for s ≥ 128 the value is below one half
    if s ≥ 128 then 0
    else
      let h : UInt64 := if round && s ≤ 64 then (1 : UInt64) <<< (s - 1).toUInt64 else 0
      let lo2 := lo + h
      let hi2 := hi + (if lo2 < lo then 1 else 0) +
        (if round && s > 64 then (1 : UInt64) <<< (s - 65).toUInt64 else 0)
      if s ≥ 64 then hi2 >>> (s - 64).toUInt64
      else if hi2 >>> s.toUInt64 != 0 then noFast
      else (lo2 >>> s.toUInt64) ||| (hi2 <<< (64 - s).toUInt64)

/-- `p` significant digits of `|x| = m × 2^e2` (`1 ≤ p ≤ 19`), rounded half up, as `n` with
`10^(p-1) ≤ n < 10^p` and the exponent `e` with `10^e ≤ |x| < 10^(e+1)` (as `sigDigits`);
`digits = noFast` when the scale `10^(p-1-e)` is out of range. -/
def sigFast (m : UInt64) (e2 : Int) (p : Nat) : Ryu.Decimal :=
  -- |x| is in [2^b, 2^(b+1)), so e is ⌊b log₁₀ 2⌋ or one more; `go` corrects the estimate
  let b : Int := e2 + Int.ofNat m.log2.toNat
  let rec go (e : Int) : Nat → Ryu.Decimal
    | 0 => { digits := noFast, exp10 := 0 }
    | fuel + 1 =>
      let k : Int := Int.ofNat p - 1 - e
      if k < 0 || k > 19 then { digits := noFast, exp10 := 0 } else
      let t := scaled m e2 k.toNat false
      if t == noFast then { digits := noFast, exp10 := 0 }
      else if t < Ryu.pow10[p - 1]! then go (e - 1) fuel
      else if t ≥ Ryu.pow10[p]! then go (e + 1) fuel
      else
        let n := scaled m e2 k.toNat true
        if n == Ryu.pow10[p]! then { digits := Ryu.pow10[p - 1]!, exp10 := e + 1 }
        else { digits := n, exp10 := e }
  go ((b * 78913) / 262144) 4

/-- Number.prototype.toFixed (§21.1.3.3) of a finite `x` with `|x| < 10^21`, `f ≤ 100`: the
fast path when `f ≤ 19` and the scaled value fits in 64 bits, else `fixed`. -/
def fixedOf (x : Float) (f : Nat) : String :=
  let b := x.toBits
  let n := if x == 0 then 0 else if f ≤ 19 then scaled (mantOf b) (expOf b) f true else noFast
  if n == noFast then
    let (s, num, den) := ofFloat x
    fixed s num den f
  else
    let s0 := if x < 0 then "-" else ""
    if f == 0 then Ryu.pushDigits s0 n (Ryu.digitCount n 1 24)
    else
      let p := Ryu.pow10[f]!
      let ip := n / p
      Ryu.pushDigits ((Ryu.pushDigits s0 ip (Ryu.digitCount ip 1 24)).push '.') (n % p) f

/-- Number.prototype.toExponential (§21.1.3.2) of a finite `x` with `f` fraction digits: the
fast path for `f ≤ 18`, else `expo`. -/
def expoOf (x : Float) (f : Nat) : String :=
  let b := x.toBits
  let r : Ryu.Decimal := if x == 0 || f > 18 then { digits := noFast, exp10 := 0 }
    else sigFast (mantOf b) (expOf b) (f + 1)
  if r.digits == noFast then
    let (s, num, den) := ofFloat x
    expo s num den f
  else expoLayout (x < 0) (Ryu.pushDigits "" r.digits (f + 1)) r.exp10 f

/-- Number.prototype.toPrecision (§21.1.3.5) of a finite `x` with `p` significant digits
(`1 ≤ p ≤ 100`): the fast path for `p ≤ 19`, else `precision`. -/
def precisionOf (x : Float) (p : Nat) : String :=
  let b := x.toBits
  let r : Ryu.Decimal := if x == 0 || p > 19 || p == 0 then { digits := noFast, exp10 := 0 }
    else sigFast (mantOf b) (expOf b) p
  if r.digits == noFast then
    let (s, num, den) := ofFloat x
    precision s num den p
  else precisionLayout (x < 0) (Ryu.pushDigits "" r.digits p) r.exp10 p

/-- `toExponential()` with no argument (§21.1.3.2 step 10): as many digits as Number::toString. -/
def expoShortest (x : Float) : String :=
  if x == 0 then expoOf x 0 else expoOf x (shortestFrac x)

/-! Checks against the values of §21.1.3.2, §21.1.3.3, §21.1.3.5 (as V8 and QuickJS print them). -/
#guard (let (s, n, d) := ofFloat 123.456; (fixed s n d 2, expo s n d 2, precision s n d 4, precision s n d 2)) ==
  ("123.46", "1.23e+2", "123.5", "1.2e+2")
#guard (let (s, n, d) := ofFloat 0.000001234; (fixed s n d 10, expo s n d 3, precision s n d 2)) ==
  ("0.0000012340", "1.234e-6", "0.0000012")
#guard (let (s, n, d) := ofFloat (-1.5); (fixed s n d 0, expo s n d 0, precision s n d 1)) == ("-2", "-2e+0", "-2")
#guard (let (s, n, d) := ofFloat 0.5; (fixed s n d 0, fixed s n d 1)) == ("1", "0.5")
#guard (let (s, n, d) := ofFloat 1.45; fixed s n d 1) == "1.4"
#guard (let (s, n, d) := ofFloat 123.456; expo s n d (shortestFrac 123.456)) == "1.23456e+2"

end L4Factoidal.JS.NumFmt
