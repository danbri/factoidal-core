/-
L4Factoidal.Qlvr.Format — QLever's lexical forms for `Int`, `Double` and
`Bool` Ids (Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

QLever (`index/ExportIds.cpp:233-292` at commit ceace86) prints

  * an `Int` with `std::to_string`, datatype `xsd:int`;
  * a finite `Double` with `%.1f` when its fractional part is zero, and with
    `%.13g` otherwise, adding `.0` when the `%.13g` text has neither `.` nor
    `e`; datatype `xsd:decimal`;
  * a NaN or infinite `Double` as `NaN`, `INF`, `-INF`, datatype `xsd:double`;
  * a `Bool` as `true`/`false`, or `1`/`0` when the input used those forms.

This module computes the C `printf` results EXACTLY: the binary64 value is
`m * 2^e` with natural `m`, so the decimal digits come from exact `Nat`
arithmetic, rounded half to even on the exact value (glibc's behaviour in the
default rounding mode). No `Float` operation is used, so the result does not
depend on the host's floating-point formatting.

The work per number is bounded by the size of the exponent (at most 1,074
binary digits); nothing loops over input-proportional data.
-/

namespace L4Factoidal.Qlvr.Format

/-- A binary64 value split into its parts. -/
inductive Fp where
  | nan
  | inf (neg : Bool)
  /-- `(-1)^neg * m * 2^e` -/
  | finite (neg : Bool) (m : Nat) (e : Int)
  deriving Repr, BEq

/-- Split IEEE 754 binary64 bits. -/
def classify (b : UInt64) : Fp :=
  let neg := (b >>> 63) == 1
  let ef := ((b >>> 52) &&& 0x7FF).toNat
  let f := (b &&& 0xFFFFFFFFFFFFF).toNat
  if ef == 0x7FF then (if f == 0 then .inf neg else .nan)
  else if ef == 0 then .finite neg f (-1074)
  else .finite neg (f + 2 ^ 52) (Int.ofNat ef - 1075)

/-- `m * 2^e` as numerator and denominator. -/
def ratio (m : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ e.natAbs)

/-- The number of decimal digits of `n` (1 for 0). -/
def ndigits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- `num / den ≥ 10^x`. -/
def geqPow10 (num den : Nat) (x : Int) : Bool :=
  if x ≥ 0 then num ≥ den * 10 ^ x.toNat else num * 10 ^ x.natAbs ≥ den

/-- Drop trailing `'0'`s of a digit list. -/
def trimZeros (l : List Char) : List Char := (l.reverse.dropWhile (· == '0')).reverse

/-- C's `%.Pg` (`P ≥ 1`) of the positive rational `num / den`, no sign. -/
def fmtG (P num den : Nat) : String :=
  let x0 : Int := Int.ofNat (ndigits num) - Int.ofNat (ndigits den)
  let x : Int := if geqPow10 num den x0 then x0 else x0 - 1
  let s : Int := Int.ofNat P - 1 - x
  let (n, d) := if s ≥ 0 then (num * 10 ^ s.toNat, den) else (num, den * 10 ^ s.natAbs)
  let q := n / d
  let r := n % d
  let q := if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q
  let (q, x) := if q == 10 ^ P then (10 ^ (P - 1), x + 1) else (q, x)
  let ds := (Nat.toDigits 10 q)
  if x < -4 || x ≥ Int.ofNat P then
    let frac := trimZeros ds.tail
    let mant := String.ofList (ds.take 1 ++ (if frac.isEmpty then [] else '.' :: frac))
    let ex := x.natAbs
    let exs := if ex < 10 then "0" ++ toString ex else toString ex
    mant ++ "e" ++ (if x < 0 then "-" else "+") ++ exs
  else if x ≥ 0 then
    let ip := ds.take (x.toNat + 1)
    let frac := trimZeros (ds.drop (x.toNat + 1))
    String.ofList (ip ++ (if frac.isEmpty then [] else '.' :: frac))
  else
    let frac := trimZeros (List.replicate (x.natAbs - 1) '0' ++ ds)
    String.ofList ('0' :: (if frac.isEmpty then [] else '.' :: frac))

/-- QLever's lexical form of a `Double` and its datatype local name
    (`decimal` for finite values, `double` for NaN and the infinities). -/
def doubleLexical (bits : UInt64) : String × String :=
  match classify bits with
  | .nan => ("NaN", "double")
  | .inf neg => (if neg then "-INF" else "INF", "double")
  | .finite neg m e =>
    let sign := if neg then "-" else ""
    let integral := e ≥ 0 || m % 2 ^ e.natAbs == 0
    if integral then
      let n := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ e.natAbs
      (sign ++ toString n ++ ".0", "decimal")
    else
      let (num, den) := ratio m e
      let g := fmtG 13 num den
      let g := if g.contains '.' || g.contains 'e' then g else g ++ ".0"
      (sign ++ g, "decimal")

/-- QLever's lexical form of an `Int` (`std::to_string`). -/
def intLexical (i : Int) : String := toString i

/-- QLever's lexical form of a `Bool` (`getBoolLiteral`). -/
def boolLexical (value lexical01 : Bool) : String :=
  if lexical01 then (if value then "1" else "0") else (if value then "true" else "false")

-- Expected strings: Python's `%.1f` / `%.13g` (C printf) with QLever's rule.
#guard (doubleLexical 0x3fb999999999999a).1 == "0.1"
#guard (doubleLexical 0x406ac00000000000).1 == "214.0"
#guard (doubleLexical 0x4415af1d78b58c40).1 == "100000000000000000000.0"
#guard (doubleLexical 0x3eef75104d551d69).1 == "1.5e-05"
#guard (doubleLexical 0x4271f71fb04cb666).1 == "1234567890123.0"
#guard (doubleLexical 0x3ee4f8b588e368f1).1 == "1e-05"
#guard (doubleLexical 0x3f1a36e2eb1c432d).1 == "0.0001"
#guard (doubleLexical 0x42dc12218377de66).1 == "1.234567890123e+14"
#guard (doubleLexical 0xc004000000000000).1 == "-2.5"
#guard (doubleLexical 0x4052200000000000).1 == "72.5"
#guard (doubleLexical 0x3fd5555555555555).1 == "0.3333333333333"
#guard (doubleLexical 0x4005666666666666).1 == "2.675"
#guard (doubleLexical 0x0000000000000001).1 == "4.940656458412e-324"
#guard (doubleLexical 0x3f1a36e2eb1c42e3).1 == "0.0001"
#guard (doubleLexical 0x3f50624dd2f1a915).1 == "0.0009999999999999"
#guard (doubleLexical 0x8000000000000000).1 == "-0.0"
#guard doubleLexical 0x7ff8000000000000 == ("NaN", "double")
#guard doubleLexical 0xfff0000000000000 == ("-INF", "double")
#guard (doubleLexical 0x0000000000000000).2 == "decimal"
#guard boolLexical true true == "1"
#guard boolLexical false false == "false"

end L4Factoidal.Qlvr.Format
