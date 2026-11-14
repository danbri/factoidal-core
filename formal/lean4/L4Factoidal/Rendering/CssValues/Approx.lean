/-
L4Factoidal.Rendering.CssValues.Approx — rational approximations of the functions whose
values are irrational: exponential, logarithm, power, sine, cosine and arctangent.

Used by the colour conversions that need a transfer function, a cube root or an angle
(`Color.lean`) and by the math functions of CSS Values 4 §10.4–§10.5 (`Numeric.lean`).
Each is a series in exact rational arithmetic, each step rounded to 18 decimal places. A
result is an approximation (within about 1e-10 of the real value), never an exact value,
except where a comment says a case is exact; no theorem speaks about the approximate
values.
-/
import L4Factoidal.Rendering.CssValues.Token

namespace L4Factoidal.Rendering.CssValues.Color

/-- `x` modulo `m` (for `m > 0`): in `[0, m)`. -/
def rmod (x m : Rat) : Rat := x - m * ((x / m).floor : Int)

/-- Rounding to the nearest integer, halves upwards. -/
def roundHalfUp (x : Rat) : Int := (x + (1 : Rat) / 2).floor

/-- `x` rounded to `n` decimal places (halves upwards). -/
def roundTo (n : Nat) (x : Rat) : Rat := ((roundHalfUp (x * pow10 n) : Int) : Rat) / pow10 n

def q18 (x : Rat) : Rat := roundTo 18 x

/-- ln 2 to 30 decimal places. -/
def ln2 : Rat := (693147180559945309417232121458 : Rat) / pow10 30

/-- π to 30 decimal places. -/
def piApprox : Rat := (3141592653589793238462643383280 : Rat) / pow10 30

/-- The terms of the exponential series from the `k`-th on, added to `sum`. -/
def expSeries : Nat → Nat → Rat → Rat → Rat → Rat
  | 0, _, _, _, sum => sum
  | fuel + 1, k, r, term, sum =>
    let t := q18 (term * r / (k : Rat))
    expSeries fuel (k + 1) r t (sum + t)

/-- An approximation of `e ^ z`: `z` is reduced by a multiple of ln 2 to at most 0.35 in
size, then 30 terms of the series. -/
def expApprox (z : Rat) : Rat :=
  let k : Int := roundHalfUp (z / ln2)
  let r := z - (k : Rat) * ln2
  let e := expSeries 30 1 r 1 1
  if 0 ≤ k then e * ((2 ^ k.toNat : Nat) : Rat) else e / ((2 ^ (-k).toNat : Nat) : Rat)

/-- `x = m * 2 ^ k` with `m` in `[2/3, 4/3)` (for `x > 0`, within the fuel). -/
def normPow2 : Nat → Rat → Int → Rat × Int
  | 0, m, k => (m, k)
  | fuel + 1, m, k =>
    if (4 : Rat) / 3 ≤ m then normPow2 fuel (m / 2) (k + 1)
    else if m < (2 : Rat) / 3 then normPow2 fuel (m * 2) (k - 1)
    else (m, k)

/-- The series `t + t^3/3 + t^5/5 + ...` continued: `p` is the last power, `j` its index. -/
def atanhSeries : Nat → Nat → Rat → Rat → Rat → Rat
  | 0, _, _, _, sum => sum
  | fuel + 1, j, t2, p, sum =>
    let p' := q18 (p * t2)
    atanhSeries fuel (j + 2) t2 p' (sum + p' / ((j + 2 : Nat) : Rat))

/-- An approximation of `ln x` for `x > 0`. -/
def lnApprox (x : Rat) : Rat :=
  let (m, k) := normPow2 400 x 0
  let t := q18 ((m - 1) / (m + 1))
  2 * atanhSeries 24 1 (q18 (t * t)) t t + (k : Rat) * ln2

/-- An approximation of `x ^ y` for `x ≥ 0` (0 for `x ≤ 0`; exactly 1 for `x = 1`). -/
def powApprox (x y : Rat) : Rat :=
  if x ≤ 0 then 0 else q18 (expApprox (q18 (y * lnApprox x)))

/-- `f` applied to the size of `x`, with the sign of `x`. -/
def signed (f : Rat → Rat) (x : Rat) : Rat := if x < 0 then -(f (-x)) else f x

def cbrtApprox (x : Rat) : Rat := signed (fun a => powApprox a ((1 : Rat) / 3)) x

/-- The alternating series of sine (from `term = r`, `n = 1`) or cosine (`term = 1`, `n = 0`). -/
def trigSeries : Nat → Nat → Rat → Rat → Rat → Rat
  | 0, _, _, _, sum => sum
  | fuel + 1, n, r2, term, sum =>
    let t := q18 (-(term * r2) / (((n + 1) * (n + 2) : Nat) : Rat))
    trigSeries fuel (n + 2) r2 t (sum + t)

/-- Approximations of the sine and cosine of an angle in degrees; exact at multiples of 90. -/
def sinCosDeg (deg : Rat) : Rat × Rat :=
  let d := rmod deg 360
  if d == 0 then (0, 1) else if d == 90 then (1, 0)
  else if d == 180 then (0, -1) else if d == 270 then (-1, 0)
  else
    let r := q18 ((d - 180) * piApprox / 180)
    let r2 := q18 (r * r)
    -- sin d = -sin (d - 180), cos d = -cos (d - 180); the reduced angle is within ±π.
    (-(trigSeries 30 1 r2 r r), -(trigSeries 30 0 r2 1 1))

/-- The series `t - t^3/3 + t^5/5 - ...` continued. -/
def atanSeries : Nat → Nat → Rat → Rat → Rat → Rat
  | 0, _, _, _, sum => sum
  | fuel + 1, j, t2, p, sum =>
    let p' := q18 (-(p * t2))
    atanSeries fuel (j + 2) t2 p' (sum + p' / ((j + 2 : Nat) : Rat))

/-- An approximation of the arctangent, in degrees, of `t` in `[0, 1]`: the angle is halved
twice (`tan (a/2) = t / (1 + √(1 + t²))`), then the series. -/
def atanUnitDeg (t : Rat) : Rat :=
  let half (t : Rat) : Rat := q18 (t / (1 + powApprox (1 + t * t) ((1 : Rat) / 2)))
  let u := half (half t)
  4 * atanSeries 24 1 (q18 (u * u)) u u * 180 / piApprox

/-- An approximation of the angle of the point `(x, y)` in degrees in `[0, 360)`; exact on
the axes. -/
def atan2Deg (y x : Rat) : Rat :=
  let ay := if y < 0 then -y else y
  let ax := if x < 0 then -x else x
  if ax == 0 && ay == 0 then 0
  else
    let base := if ay ≤ ax then atanUnitDeg (ay / ax) else 90 - atanUnitDeg (ax / ay)
    if 0 ≤ x then (if 0 ≤ y then base else rmod (360 - base) 360)
    else (if 0 ≤ y then 180 - base else 180 + base)

end L4Factoidal.Rendering.CssValues.Color
