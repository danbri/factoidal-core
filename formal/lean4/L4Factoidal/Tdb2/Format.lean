/-
L4Factoidal.Tdb2.Format — lexical forms Apache Jena TDB2 gives to the terms it
stores by value (https://github.com/danbri/factoidal/issues/834).

Format record: docs/designissues/2026-10-13-tdb2-format.md, sections 4 and 5.
Each function names the Jena 6.2.0 method whose output it reproduces. These are
Jena's forms, not canonical forms chosen here: a TDB2 reader must print what
Jena prints, or a dump differs from `tdb2.tdbdump`.

No function here recurses once per input item. The digit loops are bounded by
the number of digits (at most a few hundred for a double).
-/

namespace L4Factoidal.Tdb2

/-- The first `n` characters. -/
def sTake (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

/-- All but the first `n` characters. -/
def sDrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- `n` zeros. -/
def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- `BigDecimal.valueOf(value, scale).toPlainString()` for `scale ≥ 0`. -/
def plainDecimal (value : Int) (scale : Nat) : String :=
  let digits := toString value.natAbs
  let sign := if value < 0 then "-" else ""
  if scale == 0 then sign ++ digits
  else
    let padded := zeros (scale + 1 - min (scale + 1) digits.length) ++ digits
    let cut := padded.length - scale
    sign ++ (sTake padded cut) ++ "." ++ (sDrop padded cut)

/-- `BigDecimal.valueOf(value, scale).toPlainString()` for any `int` scale
    (Jena `ThriftConvert.convert`, field `valDecimal`). -/
def plainDecimalInt (value : Int) (scale : Int) : String :=
  if scale ≤ 0 then
    (if value < 0 then "-" else "") ++ toString value.natAbs ++ zeros scale.natAbs
  else plainDecimal value scale.toNat

/-- `XSDNumUtils.canonicalDecimalStrWithDot(BigDecimal.valueOf(value, scale))`:
    trailing zeros removed, and ".0" when no fraction digit is left
    (`NodeIdInline.extract`, case `XSD_DECIMAL`). -/
def canonicalDecimalWithDot (value : Int) (scale : Nat) : String := Id.run do
  if value == 0 then return "0.0"
  if scale == 0 then return plainDecimal value 0 ++ ".0"
  let mut v := value
  let mut s := scale
  for _ in [0:scale] do
    if s > 0 && v % 10 == 0 then
      v := v / 10
      s := s - 1
  let str := plainDecimal v s
  return if s == 0 then str ++ ".0" else str

#guard canonicalDecimalWithDot 0 3 == "0.0"
#guard canonicalDecimalWithDot 15 1 == "1.5"
#guard canonicalDecimalWithDot 1500 3 == "1.5"
#guard canonicalDecimalWithDot 1000 3 == "1.0"
#guard canonicalDecimalWithDot (-5) 2 == "-0.05"
#guard canonicalDecimalWithDot 7 0 == "7.0"
#guard plainDecimalInt 12 (-2) == "1200"
#guard plainDecimalInt 12 3 == "0.012"

/-- `NumberUtils.formatInt(sb, v, width)`: zero padded to `width`. -/
def pad (v width : Nat) : String :=
  let s := toString v
  zeros (width - min width s.length) ++ s

/-- `DateTimeNode.unpack(v, isDateTime)`: the 56 value bits of an inline
    `xsd:dateTime` / `xsd:date` NodeId. Bit fields (low bit first): milliseconds
    16, minutes 6, hours 5, day 5, month 4, year 13, timezone 7 (quarter hours,
    0x7F = "Z", 0x7E = none). -/
def dateTimeLex (v : Nat) (withTime : Bool) : String :=
  let bits := fun (lo n : Nat) => (v >>> lo) % (2 ^ n)
  let year := bits 36 13
  let month := bits 32 4
  let day := bits 27 5
  let hour := bits 22 5
  let minute := bits 16 6
  let milli := bits 0 16
  let tz := bits 49 7
  let date := pad year 4 ++ "-" ++ pad month 2 ++ "-" ++ pad day 2
  let time :=
    if !withTime then ""
    else
      let sec := milli / 1000
      let frac := milli % 1000
      let fracStr :=
        if frac == 0 then ""
        else if frac % 100 == 0 then "." ++ pad (frac / 100) 1
        else if frac % 10 == 0 then "." ++ pad (frac / 10) 2
        else "." ++ pad frac 3
      "T" ++ pad hour 2 ++ ":" ++ pad minute 2 ++ ":" ++ pad sec 2 ++ fracStr
  let zone :=
    if tz == 0x7F then "Z"
    else if tz == 0x7E then ""
    else
      let neg := tz ≥ 0x40
      let q := if neg then 0x80 - tz else tz
      (if neg then "-" else "+") ++ pad (q / 4) 2 ++ ":" ++ pad ((q % 4) * 15) 2
  date ++ time ++ zone

/-! ## Java `Double.toString` / `Float.toString` (JDK 19 and later)

The shortest decimal (at least two digits) inside the rounding interval of the
binary value, the closest one when several have that length, the even one on a
tie; then Java's layout: plain for `10^-3 ≤ |x| < 10^7`, else `d.dddE<n>`.
Exact arithmetic on `Nat`: a number is `A · 2^a · 10^b`. -/

/-- Compare `A·2^a2·10^a10` with `B·2^b2·10^b10` exactly. -/
def cmpScaled (A : Nat) (a2 a10 : Int) (B : Nat) (b2 b10 : Int) : Ordering :=
  let pa := a2 + a10
  let pb := b2 + b10
  let p2 := min pa pb
  let p5 := min a10 b10
  let lhs := A * 2 ^ (pa - p2).toNat * 5 ^ (a10 - p5).toNat
  let rhs := B * 2 ^ (pb - p2).toNat * 5 ^ (b10 - p5).toNat
  compare lhs rhs

/-- `(digits, e)` with `x = 0.digits · 10^e`, for `x = m · 2^e2 > 0`.
    `boundary`: the lower neighbour is half as far (the significand field is
    zero and the exponent is not the smallest). `maxDigits`: 17 for a double, 9
    for a float. -/
def shortestDigits (m : Nat) (e2 : Int) (boundary : Bool) (maxDigits : Nat) :
    String × Int := Id.run do
  let even := m % 2 == 0
  let hi := 4 * m + 2
  let lo := if boundary then 4 * m - 1 else 4 * m - 2
  -- floor(log10 x): estimate from log2, then correct.
  let lg : Int := (Nat.log2 m : Int) + e2
  let mut est : Int := (lg * 30103) / 100000
  for _ in [0:4] do
    if cmpScaled 1 0 (est + 1) m e2 0 != .gt then est := est + 1
  for _ in [0:4] do
    if cmpScaled 1 0 est m e2 0 == .gt then est := est - 1
  let mut best : String × Int := (toString m, 0)
  for i in [0:maxDigits - 1] do
    let p := i + 2
    let k : Int := est - p + 1
    -- D = round-half-even(m·2^e2 / 10^k)
    let num := m * 2 ^ (max e2 0).toNat * 10 ^ (max (-k) 0).toNat
    let den := 2 ^ (max (-e2) 0).toNat * 10 ^ (max k 0).toNat
    let q := num / den
    let r := num % den
    let q := if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q
    let (q, k) := if q == 10 ^ p then (10 ^ (p - 1), k + 1) else (q, k)
    let cLo := cmpScaled q 0 k lo (e2 - 2) 0
    let cHi := cmpScaled q 0 k hi (e2 - 2) 0
    let inside := (cLo == .gt || (even && cLo == .eq)) && (cHi == .lt || (even && cHi == .eq))
    if inside then
      let ds := toString q
      best := (ds, k + ds.length)
      break
  -- Strip trailing zeros of the digit string (keep at least one digit).
  let (ds, e) := best
  let trimmed := (ds.toList.reverse.dropWhile (· == '0')).reverse
  return (String.ofList (if trimmed.isEmpty then ['0'] else trimmed), e)

/-- Java's layout of `(digits, e)`, `x = 0.digits · 10^e`, `x > 0`. -/
def javaLayout (ds : String) (e : Int) : String :=
  -- 10^-3 ≤ x < 10^7  ⇔  -2 ≤ e ≤ 7
  if -2 ≤ e && e ≤ 7 then
    if e ≤ 0 then "0." ++ zeros e.natAbs ++ ds
    else if ds.length ≤ e.toNat then ds ++ zeros (e.toNat - ds.length) ++ ".0"
    else sTake ds e.toNat ++ "." ++ sDrop ds e.toNat
  else
    let rest := sDrop ds 1
    sTake ds 1 ++ "." ++ (if rest.isEmpty then "0" else rest) ++ "E" ++ toString (e - 1)

/-- `Double.toString(Double.longBitsToDouble(bits))`. -/
def javaDoubleString (bits : UInt64) : String :=
  let b := bits.toNat
  let neg := b >>> 63 == 1
  let exp := (b >>> 52) % 2048
  let frac := b % 2 ^ 52
  let sign := if neg then "-" else ""
  if exp == 2047 then (if frac != 0 then "NaN" else sign ++ "Infinity")
  else if exp == 0 && frac == 0 then sign ++ "0.0"
  else
    let (m, e2) : Nat × Int :=
      if exp == 0 then (frac, -1074) else (2 ^ 52 + frac, (exp : Int) - 1075)
    let (ds, e) := shortestDigits m e2 (frac == 0 && exp > 1) 17
    sign ++ javaLayout ds e

/-- `Float.toString(Float.intBitsToFloat(bits))`. -/
def javaFloatString (bits : UInt32) : String :=
  let b := bits.toNat
  let neg := b >>> 31 == 1
  let exp := (b >>> 23) % 256
  let frac := b % 2 ^ 23
  let sign := if neg then "-" else ""
  if exp == 255 then (if frac != 0 then "NaN" else sign ++ "Infinity")
  else if exp == 0 && frac == 0 then sign ++ "0.0"
  else
    let (m, e2) : Nat × Int :=
      if exp == 0 then (frac, -149) else (2 ^ 23 + frac, (exp : Int) - 150)
    let (ds, e) := shortestDigits m e2 (frac == 0 && exp > 1) 9
    sign ++ javaLayout ds e

/-- `XSDNumUtils.stringForm(double)`: INF / -INF / NaN, else Double.toString
    with "e0" appended when it has no exponent. -/
def xsdDoubleString (bits : UInt64) : String :=
  let s := javaDoubleString bits
  if s == "Infinity" then "INF" else if s == "-Infinity" then "-INF"
  else if s == "NaN" then s
  else if s.contains 'E' then s else s ++ "e0"

/-- `XSDNumUtils.stringForm(float)`: INF / -INF / NaN, else Float.toString. -/
def xsdFloatString (bits : UInt32) : String :=
  let s := javaFloatString bits
  if s == "Infinity" then "INF" else if s == "-Infinity" then "-INF" else s

-- Values checked against Java 21 `Double.toString` / `Float.toString`.
#guard javaDoubleString 0x3FF0000000000000 == "1.0"           -- 1.0
#guard javaDoubleString 0x4059000000000000 == "100.0"         -- 100.0
#guard javaDoubleString 0x3FB999999999999A == "0.1"           -- 0.1
#guard javaDoubleString 0x3F1A36E2EB1C432D == "1.0E-4"        -- 1.0E-4
#guard javaDoubleString 0x416312D000000000 == "1.0E7"         -- 1.0E7
#guard javaDoubleString 0x0000000000000001 == "4.9E-324"      -- Double.MIN_VALUE
#guard javaDoubleString 0x7FEFFFFFFFFFFFFF == "1.7976931348623157E308"
#guard javaDoubleString 0xC00921FB54442D18 == "-3.141592653589793"
#guard javaDoubleString 0x4415AF1D78B58C40 == "1.0E20"
#guard xsdDoubleString 0x4059000000000000 == "100.0e0"
#guard xsdDoubleString 0x3F1A36E2EB1C432D == "1.0E-4"
#guard javaFloatString 0x3DCCCCCD == "0.1"                    -- 0.1f
#guard javaFloatString 0x3F800000 == "1.0"
#guard javaFloatString 0x00000001 == "1.4E-45"                -- Float.MIN_VALUE
-- Negative guards: the layout must not print an exponent in the plain range,
-- nor a plain form outside it.
#guard javaDoubleString 0x4059000000000000 != "1.0E2"
#guard javaDoubleString 0x416312D000000000 != "10000000.0"

#guard dateTimeLex ((2010 <<< 36) ||| (6 <<< 32) ||| (21 <<< 27) ||| (11 <<< 22) ||| (28 <<< 16)
    ||| 1000 ||| (0x7F <<< 49)) true == "2010-06-21T11:28:01Z"
#guard dateTimeLex ((2010 <<< 36) ||| (12 <<< 32) ||| (21 <<< 27) ||| (0x7E <<< 49)) false
    == "2010-12-21"
#guard dateTimeLex ((2010 <<< 36) ||| (12 <<< 32) ||| (21 <<< 27) ||| ((0x80 - 32) <<< 49)) false
    == "2010-12-21-08:00"

end L4Factoidal.Tdb2
