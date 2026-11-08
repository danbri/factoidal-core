import L4Factoidal.JS.Lexer

/-!
# L4Factoidal.JS.Number — the Number type's operations (§6.1.6.1, §7.1)

Numbers are Lean `Float` (IEEE 754 binary64, the C `double`). `+ - * /` are the
hardware operations, which IEEE 754 rounds correctly, as §6.1.6.1 requires.
What C does not give with the JavaScript meaning is written here:

- `Number::toString` (§6.1.6.1.20): the shortest digits that read back as the
  value, from `XPath4.shortestDigits` (exact rational arithmetic), then the
  JavaScript layout. Safe integers take a direct path.
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

/-- `x` is `-0`. -/
def isNegZero (x : Float) : Bool := x == 0 && (x.toBits >>> 63) == 1

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

/-- Number::toString with radix 10 (§6.1.6.1.20). -/
def numToString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0 then "0"
  else if x.isInf then (if x < 0 then "-Infinity" else "Infinity")
  else if isIntegral x && x.abs < 1e21 then
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
    if r == 0 then (if n < 0 then -0.0 else 0.0) else Float.ofInt r
  else
    let (nn, an, bn) := parts n
    let (_, ad, bd) := parts d
    -- |n| = an/bn, |d| = ad/bd, both denominators powers of two
    let den := Nat.max bn bd
    let a := an * (den / bn)
    let b := ad * (den / bd)
    let r := a % b
    if r == 0 then (if nn then -0.0 else 0.0) else
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

/-- The UTF-16 length of a string (§6.1.4: code units). -/
def utf16Length (s : String) : Nat :=
  s.foldl (fun a c => a + (if c.toNat ≥ 0x10000 then 2 else 1)) 0

end L4Factoidal.JS
