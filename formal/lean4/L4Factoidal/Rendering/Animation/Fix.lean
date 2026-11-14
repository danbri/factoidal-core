/-
L4Factoidal.Rendering.Animation.Fix: the numbers of the animation code.

Every number of the animation model (a time in milliseconds, a progress, a length, a
colour channel) is an `Int` that counts units of 10⁻⁹ (`scale`). Arithmetic on them is
exact integer arithmetic with one stated rounding (`roundDiv`, to the nearest unit, a
half upward), so the properties the model relies on are theorems about `Int`, not tests
of floating point: an interpolation at progress 0 is the start value and at 1 the end
value (`lerp_zero`, `lerp_one`), the interpolation of a value with itself is that value
(`lerp_self`), and for a progress in [0, 1] the result lies between the two values
(`lerp_between`).

Nine decimal places are more than CSS serializes (six) and more than the Web Animations
tests compare (0.0005 ms). No literal here is 2³¹ or more (32-bit Wasm rule).
-/
namespace L4Factoidal.Rendering.Animation.Fix

/-- Units in one: 10⁹. -/
def scale : Int := 1000000000

/-- The number 1. -/
def one : Int := scale

/-- One half. -/
def half : Int := 500000000

/-- A whole number. -/
def ofInt (n : Int) : Int := n * scale

/-- `n / d` to the nearest integer, a half upward (`d > 0`). -/
def roundDiv (n d : Int) : Int := (2 * n + d) / (2 * d)

/-- The product of two numbers. -/
def mul (a b : Int) : Int := roundDiv (a * b) scale

/-- The quotient of two numbers; `none` when the divisor is 0. -/
def div (a b : Int) : Option Int :=
  if b == 0 then none
  else if b > 0 then some (roundDiv (a * scale) b)
  else some (roundDiv (-(a * scale)) (-b))

/-- `a` towards `b` by the progress `p`: `a + (b - a) × p`. -/
def lerp (a b p : Int) : Int := a + mul (b - a) p

/-- The largest whole number not above `a`, as a number. -/
def floor (a : Int) : Int := a / scale * scale

/-- `a` rounded to a whole number (a half upward), as a number. -/
def round (a : Int) : Int := roundDiv a scale * scale

/-- `a` between `lo` and `hi`. -/
def clamp (lo hi a : Int) : Int := max lo (min hi a)

/-! ## Theorems -/

/-- Kind: arithmetic identity. Says: a product with 0 is 0. Does not say: anything about
rounding of other products. -/
theorem mul_zero (a : Int) : mul a 0 = 0 := by
  simp [mul, roundDiv, scale]

/-- Kind: arithmetic identity. Says: a product with 1 is the number itself, with no
rounding error. Does not say: `mul` is associative (it rounds). -/
theorem mul_one (a : Int) : mul a one = a := by
  simp only [mul, roundDiv, one, scale]; omega

/-- Kind: arithmetic identity. Says: 0 times anything is 0. Does not say: more. -/
theorem zero_mul (p : Int) : mul 0 p = 0 := by
  simp [mul, roundDiv, scale]

/-- Kind: interpolation endpoint. Says: at progress 0 the interpolation is the start
value, exactly. Does not say: anything for a progress near 0. -/
theorem lerp_zero (a b : Int) : lerp a b 0 = a := by
  simp [lerp, mul_zero]

/-- Kind: interpolation endpoint. Says: at progress 1 the interpolation is the end value,
exactly. Does not say: anything for a progress near 1. -/
theorem lerp_one (a b : Int) : lerp a b one = b := by
  simp only [lerp, mul_one]; omega

/-- Kind: interpolation identity. Says: a value interpolated with itself is that value,
at every progress (also outside [0, 1]). Does not say: more. -/
theorem lerp_self (a p : Int) : lerp a a p = a := by
  simp [lerp, zero_mul]

/-- Kind: rounding bound. Says: for a divisor above 0, `roundDiv` of a numerator that is not
negative is not negative. Does not say: the size of the rounding error. -/
theorem roundDiv_nonneg {n d : Int} (hn : 0 ≤ n) (hd : 0 < d) : 0 ≤ roundDiv n d := by
  unfold roundDiv
  apply Int.ediv_nonneg <;> omega

/-- Kind: rounding bound. Says: `roundDiv` does not decrease when the numerator grows
(divisor above 0). Does not say: it is strictly increasing. -/
theorem roundDiv_mono {n m d : Int} (h : n ≤ m) (hd : 0 < d) : roundDiv n d ≤ roundDiv m d := by
  unfold roundDiv
  apply Int.ediv_le_ediv <;> omega

/-- Kind: rounding identity. Says: an exact multiple divides with no error. Does not say:
more. -/
theorem roundDiv_mul (k d : Int) (hd : 0 < d) : roundDiv (k * d) d = k := by
  unfold roundDiv
  have h : 2 * (k * d) + d = d + (2 * d) * k := by
    rw [Int.mul_comm k d, ← Int.mul_assoc, Int.add_comm]
  rw [h, Int.add_mul_ediv_left _ _ (by omega : (2 * d) ≠ 0)]
  have : d / (2 * d) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  omega

/-- Kind: range. Says: for `d ≥ 0` and a progress `p` in [0, 1], the product `d × p` is in
[0, d]. Does not say: anything outside [0, 1]. -/
theorem mul_between {d p : Int} (hd : 0 ≤ d) (hp0 : 0 ≤ p) (hp1 : p ≤ one) :
    0 ≤ mul d p ∧ mul d p ≤ d := by
  constructor
  · exact roundDiv_nonneg (Int.mul_nonneg hd hp0) (by decide)
  · have h1 : d * p ≤ d * scale := Int.mul_le_mul_of_nonneg_left hp1 hd
    have h2 := roundDiv_mono (d := scale) h1 (by decide)
    rw [roundDiv_mul d scale (by decide)] at h2
    exact h2

/-- Kind: range. Says: for `d ≤ 0` and a progress in [0, 1], the product `d × p` is in
[d, 0]. Does not say: anything outside [0, 1]. -/
theorem mul_between_neg {d p : Int} (hd : d ≤ 0) (hp0 : 0 ≤ p) (hp1 : p ≤ one) :
    d ≤ mul d p ∧ mul d p ≤ 0 := by
  constructor
  · have h1 : d * scale ≤ d * p := Int.mul_le_mul_of_nonpos_left hd hp1
    have h2 := roundDiv_mono (d := scale) h1 (by decide)
    rw [roundDiv_mul d scale (by decide)] at h2
    exact h2
  · have h1 : d * p ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hd hp0
    have h2 : roundDiv (d * p) scale ≤ roundDiv 0 scale := roundDiv_mono h1 (by decide)
    have h3 : roundDiv 0 scale = 0 := by decide
    unfold mul
    omega

/-- Kind: range. Says: for a progress in [0, 1] the interpolation lies between its two
values (whichever is larger). Does not say: anything for a progress outside [0, 1], where
the result leaves the range (extrapolation). -/
theorem lerp_between (a b p : Int) (hp0 : 0 ≤ p) (hp1 : p ≤ one) :
    min a b ≤ lerp a b p ∧ lerp a b p ≤ max a b := by
  unfold lerp
  by_cases h : a ≤ b
  · have := mul_between (d := b - a) (by omega) hp0 hp1
    omega
  · have := mul_between_neg (d := b - a) (by omega) hp0 hp1
    omega

/-- Kind: range. Says: a clamped value is in the range, when the range is not empty. Does
not say: more. -/
theorem clamp_between (lo hi a : Int) (h : lo ≤ hi) : lo ≤ clamp lo hi a ∧ clamp lo hi a ≤ hi := by
  unfold clamp; omega

/-- Kind: idempotence. Says: clamping twice is clamping once. Does not say: more. -/
theorem clamp_idem (lo hi a : Int) : clamp lo hi (clamp lo hi a) = clamp lo hi a := by
  unfold clamp; omega

/-! ## Text -/

/-- The digits of a natural number, at least `width` of them (zeros in front). -/
def padDigits (width n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- The decimal text of a number with at most `places` (≤ 9) decimal places, rounded, with
no trailing zeros, no "-0" and no exponent. -/
def formatPlaces (places : Nat) (x : Int) : String :=
  let places := min places 9
  let unit : Int := (10 : Int) ^ (9 - places)
  let r := roundDiv x unit
  let neg := r < 0
  let m := r.natAbs
  let p := 10 ^ places
  let whole := m / p
  let frac := m % p
  let fracText := (padDigits places frac).toList.reverse.dropWhile (· == '0') |>.reverse
  let body := if frac == 0 then toString whole else toString whole ++ "." ++ String.ofList fracText
  if neg then "-" ++ body else body

/-- The decimal text with all nine places (times, for the script API). -/
def format (x : Int) : String := formatPlaces 9 x

/-- The decimal text as CSS serializes a number: at most six decimal places. -/
def formatCss (x : Int) : String := formatPlaces 6 x

/-- Read decimal text: an optional sign, digits with an optional fraction, and an
optional exponent (`1e-7`, as JavaScript writes small numbers). Digits beyond the ninth
decimal place are rounded. `none` for anything else (`Infinity`, `NaN`, empty). -/
def parse (s : String) : Option Int := Id.run do
  let cs := s.trimAscii.toString.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let whole := cs.takeWhile Char.isDigit
  let rest := cs.drop whole.length
  let (frac, rest) := match rest with
    | '.' :: r => let f := r.takeWhile Char.isDigit; (f, r.drop f.length)
    | r => ([], r)
  if whole.isEmpty && frac.isEmpty then return none
  let (exp, rest) : Int × List Char := match rest with
    | 'e' :: r | 'E' :: r =>
      let (eneg, r) := match r with
        | '-' :: r => (true, r)
        | '+' :: r => (false, r)
        | r => (false, r)
      let ds := r.takeWhile Char.isDigit
      if ds.isEmpty then (0, 'x' :: r)
      else
        let e : Int := Int.ofNat ((String.ofList ds).toNat?.getD 0)
        ((if eneg then -e else e), r.drop ds.length)
    | r => (0, r)
  if !rest.isEmpty then return none
  if exp > 30 || exp < -30 then return none
  -- mantissa as an integer of `whole ++ frac`, with `frac.length` decimal places
  let digits := whole ++ frac
  if digits.length > 60 then return none
  let m : Int := Int.ofNat ((String.ofList digits).toNat?.getD 0)
  -- value = m × 10^(exp - frac.length); in units of 10⁻⁹: m × 10^(9 + exp - frac.length)
  let e : Int := 9 + exp - Int.ofNat frac.length
  let v : Int := if e ≥ 0 then m * (10 : Int) ^ e.toNat else roundDiv m ((10 : Int) ^ (-e).toNat)
  return some (if neg then -v else v)

#guard parse "1" == some one
#guard parse "-0.5" == some (-half)
#guard parse "+.25" == some 250000000
#guard parse "1e-7" == some 100
#guard parse "1.5e3" == some (ofInt 1500)
#guard parse "0.23333333333333334" == some 233333333
#guard parse "" == none
#guard parse "Infinity" == none
#guard parse "1px" == none
#guard parse "1e" == none
#guard format one == "1"
#guard format (-half) == "-0.5"
#guard format 233333333 == "0.233333333"
#guard formatCss 233333333 == "0.233333"
#guard formatCss 999999999 == "1"
#guard formatCss (-1) == "0"
#guard formatCss (ofInt 12 + 500000000) == "12.5"
#guard format 0 == "0"
#guard (parse (format 123456789012)) == some 123456789012
#guard lerp (ofInt 10) (ofInt 20) half == ofInt 15
#guard lerp (ofInt 10) (ofInt 20) (-300000000) == ofInt 7
#guard lerp (ofInt 10) (ofInt 20) (ofInt 1 + half) == ofInt 25
#guard mul (ofInt 3) (ofInt 4) == ofInt 12
#guard div (ofInt 1) (ofInt 4) == some 250000000
#guard div (ofInt 1) (ofInt (-4)) == some (-250000000)
#guard div one 0 == none
#guard floor (ofInt 2 + half) == ofInt 2
#guard floor (-half) == ofInt (-1)
#guard round (ofInt 2 + half) == ofInt 3
#guard round (-half) == 0

end L4Factoidal.Rendering.Animation.Fix
