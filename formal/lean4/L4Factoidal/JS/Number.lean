import L4Factoidal.JS.Lexer
import L4Factoidal.JS.Ryu

/-!
# L4Factoidal.JS.Number — the Number type's operations (§6.1.6.1, §7.1)

Numbers are Lean `Float` (IEEE 754 binary64, the C `double`). `+ - * /` are the
hardware operations, which IEEE 754 rounds correctly, as §6.1.6.1 requires.
What C does not give with the JavaScript meaning is written here:

- `Number::toString` (§6.1.6.1.20): the shortest digits that read back as the
  value, by Ryū on 64-bit words (`JS/Ryu.lean`), then the JavaScript layout. Safe
  integers take a direct path. `numToStringRef` keeps the exact algorithm
  (`XPath4.shortestDigits`, rational arithmetic) as the reference of the
  differential test (`leanjs numfmt-diff`; issue 1076).
- `StringToNumber` (§7.1.4.1.1): the `StringNumericLiteral` grammar checked
  here, the rounding done by `XPath4.floatOfParsed`.
- `Number::remainder` (§6.1.6.1.6), the C `fmod`: exact, on the dyadic rationals
  of the two values.
- `ToInt32`, `ToUint32` (§7.1.6, §7.1.7): exact, on the integer part.
- `Number::exponentiate` (§6.1.6.1.3): C `pow` with the cases where JavaScript
  differs (`1 ** NaN`, `(±1) ** ±Infinity` are NaN).

NaN: the Lean model of `Float.ofBits` maps every NaN to one canonical NaN, and so
does compiled code. ECMAScript allows this: the NaN values are not
distinguishable from ECMAScript code (§6.1.6.1), and SetValueInBuffer (§25.1.3.17)
lets an implementation choose any NaN encoding.
-/

namespace L4Factoidal.JS

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

/-! Constants that hot functions read. A `Float` literal that the compiler leaves in a function
body is a call of `Float.ofScientific` at each evaluation, and in Lean 4.33.1 that call reads
2^53 from decimal text (`L4Factoidal/Prim/FloatOfNat.lean`). A definition with no argument is
made once, when the module starts. `tools/lean-literal-parse-audit.py` and the generated C
(`.lake/build/ir/L4Factoidal/JS/Number.c`) show which literals stay in a body. -/

/-- `+0`. -/
@[noinline] def posZero : Float := 0.0
/-- `-0`. -/
@[noinline] def negZero : Float := -0.0
/-- 10^21: from here `Number::toString` writes an exponent (§6.1.6.1.20). -/
@[noinline] def tenPow21 : Float := 1e21
/-- 2^32 - 1: an array index is an integer below it (§6.1.7 array index). A named constant:
a `Float` literal in a function body is converted from its decimal digits at each use. -/
@[noinline] def maxIndexF : Float := 4294967295.0
/-- 2^32: an array length is an integer below it (§10.4.2.4 ArraySetLength). -/
@[noinline] def twoPow32F : Float := 4294967296.0
/-- 2^53 - 1 (§21.1.2.6 Number.MAX_SAFE_INTEGER). -/
@[noinline] def maxSafeF : Float := 9007199254740991.0

/-- `x` is `-0`. -/
def isNegZero (x : Float) : Bool := x == 0 && (x.toBits >>> 63) == 1

@[noinline] private def mathHalf : Float := 0.5

/-- ECMA-262 §21.3.2.29. Round to the nearest integer, with ties toward
positive infinity. Compare the fractional part to one half: adding one
half to the original value can round across the boundary first. -/
def mathRoundNumber (x : Float) : Float :=
  if !x.isFinite || x == posZero then x
  else if x < posZero && x ≥ -mathHalf then negZero
  else
    let lower := x.floor
    if x - lower < mathHalf then lower else lower + 1

theorem mathRoundNumber_zero (x : Float) (h : (x == posZero) = true) :
    mathRoundNumber x = x := by
  simp [mathRoundNumber, h]

theorem mathRoundNumber_nonfinite (x : Float) (h : x.isFinite = false) :
    mathRoundNumber x = x := by
  simp [mathRoundNumber, h]

#guard mathRoundNumber (Float.ofBits 0x3fdfffffffffffff) == posZero
#guard isNegZero (mathRoundNumber (-0.5))
#guard mathRoundNumber 4503599627370497.0 == 4503599627370497.0

/-- Coefficients of the Taylor correction to expm1, highest degree first.
Each factorial in this range is exactly representable in binary64. -/
@[noinline] private def expMinusOneCoefficients : Array Float :=
  #[1.0 / 1307674368000.0, 1.0 / 87178291200.0, 1.0 / 6227020800.0,
    1.0 / 479001600.0, 1.0 / 39916800.0, 1.0 / 3628800.0,
    1.0 / 362880.0, 1.0 / 40320.0, 1.0 / 5040.0, 1.0 / 720.0,
    1.0 / 120.0, 1.0 / 24.0, 1.0 / 6.0, 0.5]

/-- ECMA-262 §21.3.2.15. Around zero, evaluate the degree-15 series without
subtracting two nearly equal numbers. Outside that interval use the exponential. -/
def mathExpMinusOne (x : Float) : Float :=
  if x == posZero then x
  else if x.abs ≤ mathHalf then
    let correction := expMinusOneCoefficients.foldl (fun acc c => c + x * acc) posZero
    x + x * x * correction
  else Float.exp x - 1

/-- ECMA-262 §21.3.2.22. Correct for the rounding of `1+x` in the interval
where cancellation in the uncorrected logarithm matters most. -/
def mathLogOnePlus (x : Float) : Float :=
  if x == posZero then x
  else
    let y := 1 + x
    if y == 1 then x
    else if x.abs < mathHalf then Float.log y + (x - (y - 1)) / y
    else Float.log y

/-- The zero path returns the input, preserving its sign. -/
theorem mathExpMinusOne_zero (x : Float) (h : (x == posZero) = true) :
    mathExpMinusOne x = x := by
  simp [mathExpMinusOne, h]

/-- The zero path returns the input, preserving its sign. -/
theorem mathLogOnePlus_zero (x : Float) (h : (x == posZero) = true) :
    mathLogOnePlus x = x := by
  simp [mathLogOnePlus, h]

#guard isNegZero (mathExpMinusOne negZero)
#guard isNegZero (mathLogOnePlus negZero)
#guard (mathExpMinusOne (Float.ofBits 1)).toBits == 1
#guard (mathLogOnePlus (Float.ofBits 1)).toBits == 1

/-- The exact value of a finite double as `sign, num / den` (`XPath4.floatParts`). -/
def parts (x : Float) : Bool × Nat × Nat := XPath4.floatParts x

/-- `x` is an integral number (§6.1.6.1: finite with no fraction). -/
def isIntegral (x : Float) : Bool := x.isFinite && x.floor == x

/-- The integer part of a finite double, exactly (rounding toward zero). -/
def truncInt (x : Float) : Int :=
  if x.abs < 9007199254740992.0 then x.toInt64.toInt
  else
    let (neg, num, den) := parts x
    let q : Int := (num / den : Nat)
    if neg then -q else q

/-- The digit `d` (below 36) of a radix: `0`-`9`, then `a`-`z` (§6.1.6.1.20). `Nat.toDigits`
is not used: Lean's `Nat.digitChar` gives `*` for 16 and above, so `(35).toString(36)` was
`"*"` and the class names that CSS-in-JS libraries make with base 36 (Emotion: BBC News) did
not match their rules (2026-11-23). -/
def radixDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- `n` in base `b` (2 to 36), with no leading zeros; "0" for 0. At most 1100 digits (a
double's integer part has at most 1024 binary digits). -/
def natToRadix (b n : Nat) : String := Id.run do
  if n == 0 || b < 2 then return "0"
  let mut k := n
  let mut out : List Char := []
  for _ in [0:1100] do
    if k > 0 then
      out := radixDigit (k % b) :: out
      k := k / b
  return String.ofList out

/-- 2^53 as a `Float`, made once when the module starts. Written in place, in a function small
enough to be inlined, the literal is read from decimal text at each call (its mantissa,
90071992547409920, is a `Nat` literal above 2^32; checked in the generated C of Lean 4.33.1). -/
@[noinline] def twoPow53F : Float := 9007199254740992.0

/-- No array index: the bound of `arrayIndex?` (2^32 - 1). -/
def noIndex : Nat := 4294967295

/-- Number::toString with radix 10 (§6.1.6.1.20): the reference, with exact rational arithmetic
(`XPath4.shortestDigits`, about 20 µs for a fraction). `numToString` gives the same text by Ryū;
`leanjs numfmt-diff` compares the two. -/
def numToStringRef (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0 then "0"
  else if x.isInf then (if x < 0 then "-Infinity" else "Infinity")
  else if isIntegral x && x.abs < twoPow53F then
    let i := truncInt x
    toString i
  else
    let neg := x < 0
    let (d0, q) := XPath4.shortestDigits false x.abs
    -- strip trailing zeros: d0 = d × 10^z
    let rec strip (d : Nat) (z : Nat) : Nat → Nat × Nat
      | 0 => (d, z)
      | fuel + 1 => if d != 0 && d % 10 == 0 then strip (d / 10) (z + 1) fuel else (d, z)
    let (d, _) := strip d0 0 20
    let ds := toString d
    let k : Int := ds.length
    let n : Int := q + 1
    let body :=
      if k ≤ n && n ≤ 21 then ds ++ String.ofList (List.replicate (n - k).toNat '0')
      else if 0 < n && n ≤ 21 then
        String.ofList (ds.toList.take n.toNat) ++ "." ++ String.ofList (ds.toList.drop n.toNat)
      else if -6 < n && n ≤ 0 then
        "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ ds
      else
        let e := n - 1
        let es := (if e < 0 then "-" else "+") ++ toString e.natAbs
        if k == 1 then ds ++ "e" ++ es
        else String.ofList (ds.toList.take 1) ++ "." ++ String.ofList (ds.toList.drop 1) ++ "e" ++ es
    if neg then "-" ++ body else body

/-- Number::toString with radix 10 (§6.1.6.1.20). The non-integral and large values take Ryū
(`Ryu.finiteToString`, 64-bit words, no big numbers). Equal to `numToStringRef` on every double
tested (`leanjs numfmt-diff`, issue 1076); not proved. -/
def numToString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0 then "0"
  else if x.isInf then (if x < 0 then "-Infinity" else "Infinity")
  else if isIntegral x && x.abs < tenPow21 then
    -- An integer below 2^53 is its own shortest digits; above, an integer's exact digits can be
    -- longer than the shortest (2^60 is 1152921504606847000, not ...976): issue 1076.
    match truncInt x with
    | .ofNat n => if n < noIndex || x.abs < twoPow53F then toString (Int.ofNat n) else Ryu.finiteToString x
    | .negSucc n => if x.abs < twoPow53F then toString (Int.negSucc n) else Ryu.finiteToString x
  else Ryu.finiteToString x

/-- StrWhiteSpaceChar (§7.1.4.1): WhiteSpace and LineTerminator. -/
def isStrWs (c : Char) : Bool := isWs c || isLineTerm c

def trimJs (s : String) : String :=
  let cs := s.toList.dropWhile isStrWs
  String.ofList (cs.reverse.dropWhile isStrWs).reverse

/-- StringToNumber (§7.1.4.1.1). -/
def strToNumber (s0 : String) : Float :=
  let s := trimJs s0
  if s.isEmpty then 0 else
  let cs := s.toList.toArray
  let radix (b : Nat) (ok : Char → Bool) : Float :=
    if cs.size > 2 && (List.range (cs.size - 2)).all (fun k => ok (charAt cs (k + 2)))
    then floatOfNat (digitsVal cs b cs.size 2 cs.size 0) else nan
  let c0 := charAt cs 0; let c1 := charAt cs 1
  if c0 == '0' && (c1 == 'x' || c1 == 'X') then radix 16 (fun c => (hexVal c).isSome)
  else if c0 == '0' && (c1 == 'o' || c1 == 'O') then radix 8 (fun c => '0' ≤ c && c ≤ '7')
  else if c0 == '0' && (c1 == 'b' || c1 == 'B') then radix 2 (fun c => c == '0' || c == '1')
  else
    let (neg, i) := if c0 == '-' then (true, 1) else if c0 == '+' then (false, 1) else (false, 0)
    let rest := slice cs i cs.size
    if rest == "Infinity" then (if neg then -inf else inf) else
    let j := scanWhile cs Char.isDigit cs.size i
    let (k, fracOk) := if charAt cs j == '.' then (scanWhile cs Char.isDigit cs.size (j + 1), true) else (j, false)
    let nDigits := (j - i) + (if fracOk then k - j - 1 else 0)
    if nDigits == 0 then nan else
    let (k2, expV, ok) :=
      if charAt cs k == 'e' || charAt cs k == 'E' then
        let (en, st) := if charAt cs (k + 1) == '-' then (true, k + 2)
          else if charAt cs (k + 1) == '+' then (false, k + 2) else (false, k + 1)
        let e := scanWhile cs Char.isDigit cs.size st
        let v : Int := digitsVal cs 10 cs.size st e 0
        (e, (if en then -v else v), e > st)
      else (k, (0 : Int), true)
    if !ok || k2 != cs.size then nan else
    let intD := slice cs i j
    let fracD := if fracOk then slice cs (j + 1) k else ""
    let m := (intD ++ fracD).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
    let f := XPath4.floatOfParsed (.num false m (expV - fracD.length))
    if neg then -f else f

/-- `m × 2^e` as a double, exactly when it is representable. -/
def dyadic (neg : Bool) (m : Nat) (e : Int) : Float :=
  -- m × 2^e = (m × 5^(-e)) × 10^e when e < 0
  let f :=
    if e ≥ 0 then XPath4.floatOfParsed (.num false (m * 2 ^ e.toNat) 0)
    else XPath4.floatOfParsed (.num false (m * 5 ^ (-e).toNat) e)
  if neg then -f else f

/-- Number::remainder (§6.1.6.1.6): the result has the sign of the dividend and
is exact (C `fmod`). -/
def jsMod (n d : Float) : Float :=
  if n.isNaN || d.isNaN || n.isInf || d == 0 then nan
  else if d.isInf then n
  else if n == 0 then n
  else if n.abs < 9007199254740992.0 && d.abs < 9007199254740992.0 && isIntegral n && isIntegral d then
    let r := (truncInt n).tmod (truncInt d)
    if r == 0 then (if n < 0 then negZero else posZero) else Float.ofInt r
  else
    let (nn, an, bn) := parts n
    let (_, ad, bd) := parts d
    -- |n| = an/bn, |d| = ad/bd, both denominators powers of two
    let den := Nat.max bn bd
    let a := an * (den / bn)
    let b := ad * (den / bd)
    let r := a % b
    if r == 0 then (if nn then negZero else posZero) else
    -- r / den with den = 2^k
    let k := Nat.log2 den
    dyadic nn r (-(k : Int))

/-- ToInt32 (§7.1.6) as an `Int` in `[-2^31, 2^31)`. -/
def toInt32 (x : Float) : Int :=
  if !x.isFinite || x == 0 then 0 else
  let m := (truncInt x) % 4294967296
  if m ≥ 2147483648 then m - 4294967296 else m

/-- ToUint32 (§7.1.7). -/
def toUint32 (x : Float) : Nat :=
  if !x.isFinite || x == 0 then 0 else ((truncInt x) % 4294967296).toNat

/-! ### ToInt32 and ToUint32 on machine integers

`toInt32` and `toUint32` above are the definitions: exact, on `Int`. Their compiled code is slow
for a reason that is not in the algorithm. A Lean `Int` is a machine scalar only in the signed
32-bit range, so the modulus 4294967296 is a GMP number and every `% 4294967296` is a GMP
remainder (`lean_int_big_emod`). Measured 2026-11-09 (Linux x86_64, `leanc -O3`): 45 ns for one
`toInt32` against 2 ns for the form below. Every bit operator of a script calls them two or
three times.

Below 2^53 in magnitude `truncInt x` is `x.toInt64.toInt`, and the low 32 bits of that `Int64`
are the answer (`Int64.toInt32`, a truncation). The theorems prove the two forms equal for every
`x`; the `csimp` theorems make compiled code use the fast forms. -/

/-- `t.bmod (2 ^ 32)` written the way `toInt32` writes it. -/
theorem bmod_two_pow_32 (t : Int) :
    t.bmod (2 ^ 32) =
      (if t % 4294967296 ≥ 2147483648 then t % 4294967296 - 4294967296 else t % 4294967296) := by
  unfold Int.bmod
  simp only [show ((2 : Nat) ^ 32 : Nat) = 4294967296 from by decide]
  split <;> split <;> omega

/-- The unsigned value of an `Int32` is its `Int` value modulo 2^32. -/
theorem toNat_toUInt32_eq_emod (i : Int32) : i.toUInt32.toNat = (i.toInt % 4294967296).toNat := by
  rw [← Int32.toNat_toBitVec, ← Int32.toInt_toBitVec, BitVec.toInt_eq_toNat_bmod]
  have hlt := i.toBitVec.isLt
  unfold Int.bmod
  simp only [show ((2 : Nat) ^ 32 : Nat) = 4294967296 from by decide]
  split <;> omega


/-- `toInt32` for compiled code: the low 32 bits of `x.toInt64` when `|x| < 2^53`. -/
def toInt32Fast (x : Float) : Int :=
  if !x.isFinite || x == 0 then 0 else
  if x.abs < twoPow53F then x.toInt64.toInt32.toInt else toInt32 x

theorem toInt32_eq_fast (x : Float) : toInt32 x = toInt32Fast x := by
  unfold toInt32Fast
  split
  · simp [toInt32, *]
  · next h0 =>
    split
    · next hs =>
      have hs : x.abs < 9007199254740992.0 := hs
      simp only [toInt32, h0, truncInt, hs, if_true, Bool.false_eq_true, if_false]
      rw [Int64.toInt_toInt32, bmod_two_pow_32]
    · rfl

@[csimp] theorem toInt32_eq_toInt32Fast : @toInt32 = @toInt32Fast := funext toInt32_eq_fast

/-- `toUint32` for compiled code: the low 32 bits of `x.toInt64`, unsigned, when `|x| < 2^53`. -/
def toUint32Fast (x : Float) : Nat :=
  if !x.isFinite || x == 0 then 0 else
  if x.abs < twoPow53F then x.toInt64.toInt32.toUInt32.toNat else toUint32 x

theorem toUint32_eq_fast (x : Float) : toUint32 x = toUint32Fast x := by
  unfold toUint32Fast
  split
  · simp [toUint32, *]
  · next h0 =>
    split
    · next hs =>
      have hs : x.abs < 9007199254740992.0 := hs
      simp only [toUint32, h0, truncInt, hs, if_true, Bool.false_eq_true, if_false]
      rw [toNat_toUInt32_eq_emod, Int64.toInt_toInt32, bmod_two_pow_32]
      split <;> omega
    · rfl

@[csimp] theorem toUint32_eq_toUint32Fast : @toUint32 = @toUint32Fast := funext toUint32_eq_fast

/-- Number::exponentiate (§6.1.6.1.3). -/
def jsPow (b e : Float) : Float :=
  if e.isNaN then nan
  else if e == 0 then 1
  else if b.isNaN then nan
  else if b.abs == 1 && e.isInf then nan
  else Float.pow b e

/-- `ToIntegerOrInfinity` (§7.1.5). -/
def toIntegerOrInf (x : Float) : Float :=
  if x.isNaN then 0 else if x.isInf then x else
  let t := if x < 0 then (-x).floor else x.floor
  let t := if x < 0 then -t else t
  if t == 0 then 0 else t

/-- A canonical array index (§6.1.7): the string of a Nat below 2^32 - 1. -/
def arrayIndex? (s : String) : Option Nat :=
  if s.isEmpty || s.length > 10 then none
  else if !s.all Char.isDigit then none
  else if s.length > 1 && s.front == '0' then none
  else
    let n := s.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
    if n < 4294967295 then some n else none


/-- The array index a Number is as a property key, with no key string made: `noIndex` when its
key (`numToString`) is not a canonical array index. It follows the cases of `numToString`, so
that `arrayIndex? (numToString x) = some (numIndex x)` whenever this is an index
(`arrayIndex?_keyOfNum` in `JS/Theorems.lean`: proved with no assumption about floating point). -/
def numIndex (x : Float) : Nat :=
  if x.isNaN then noIndex
  else if x == 0 then 0
  else if x.isInf then noIndex
  else if isIntegral x && x.abs < tenPow21 then
    match truncInt x with
    | .ofNat i => if i < noIndex then i else noIndex
    | _ => noIndex
  else noIndex

/-- The UTF-16 length of a string (§6.1.4: code units). -/
def utf16Length (s : String) : Nat :=
  s.foldl (fun a c => a + (if c.toNat ≥ 0x10000 then 2 else 1)) 0

/-- Number::toString(radix) for a radix other than 10 (§21.1.3.6, the digits are
implementation-approximated): the exact integer part in base `radix`, then the fraction's
digits, exactly, until it ends or for at most 52 digits. NaN, the infinities and 0 are
written as with radix 10. -/
def toStringRadix (x : Float) (radix : Nat) : String :=
  if radix == 10 || !x.isFinite || x == 0 || radix < 2 || radix > 36 then numToString x else
  let (neg, num, den) := parts x
  let whole := natToRadix radix (num / den)
  let frac := Id.run do
    let mut r := num % den
    let mut out : List Char := []
    for _ in [0:52] do
      if r > 0 && den > 0 then
        r := r * radix
        out := radixDigit (r / den) :: out
        r := r % den
    return String.ofList out.reverse
  (if neg then "-" else "") ++ whole ++ (if frac.isEmpty then "" else "." ++ frac)

#guard toStringRadix 0.5 36 == "0.i"
#guard toStringRadix (-255) 16 == "-ff"
#guard toStringRadix 3.5 2 == "11.1"
#guard natToRadix 36 35 == "z"
#guard natToRadix 36 1295 == "zz"
#guard natToRadix 16 255 == "ff"
#guard natToRadix 2 5 == "101"

end L4Factoidal.JS
