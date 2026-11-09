import L4Factoidal.XPath4.Atomic

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

/-- Number.prototype.toExponential (§21.1.3.2) with `f` fraction digits, of x = ±num/den
(num = 0 for zero). -/
def expo (neg : Bool) (num den f : Nat) : String :=
  let (m, e) := if num == 0 then (zeros (f + 1), (0 : Int)) else sigDigits num den f
  let body := if f == 0 then m else String.ofList (m.toList.take 1) ++ "." ++ String.ofList (m.toList.drop 1)
  (if neg then "-" else "") ++ body ++ expStr e

/-- Number.prototype.toPrecision (§21.1.3.5) with `p` significant digits. -/
def precision (neg : Bool) (num den p : Nat) : String :=
  let (m, e) := if num == 0 then (zeros p, (0 : Int)) else sigDigits num den (p - 1)
  let sign := if neg then "-" else ""
  if e < -6 || e ≥ p then
    sign ++ (if p == 1 then m else String.ofList (m.toList.take 1) ++ "." ++ String.ofList (m.toList.drop 1)) ++ expStr e
  else if e == p - 1 then sign ++ m
  else if e ≥ 0 then
    sign ++ String.ofList (m.toList.take (e.toNat + 1)) ++ "." ++ String.ofList (m.toList.drop (e.toNat + 1))
  else sign ++ "0." ++ zeros ((-(e + 1)).toNat) ++ m

/-- Sign and exact value of a finite double; zero (either sign) is positive. -/
def ofFloat (x : Float) : Bool × Nat × Nat :=
  if x == 0 then (false, 0, 1) else XPath4.floatParts x

/-- Trailing zeros off. -/
def strip (d : Nat) : Nat → Nat
  | 0 => d
  | fuel + 1 => if d != 0 && d % 10 == 0 then strip (d / 10) fuel else d

/-- The fraction digits of `toExponential(undefined)`: as many as the shortest digits that
read back as `x` (Number::toString) have, less one. -/
def shortestFrac (x : Float) : Nat :=
  let (d0, _) := XPath4.shortestDigits false x.abs
  (toString (strip d0 30)).length - 1

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
