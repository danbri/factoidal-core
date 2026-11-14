/-
L4Factoidal.Rendering.Animation.Easing: easing functions (CSS Easing Functions 1: §2
`linear`, §3 cubic Bézier, §4 step functions), read from CSS text, evaluated and
serialized.

A progress is a number of `Animation.Fix` (units of 10⁻⁹). A cubic Bézier is solved with
exact integers: the curve's x and y at a parameter `t` are whole numbers over 10²⁷
(`bezNum`), the parameter is found by bisection on `t`, and only the result is rounded. A
step function is integer division. So the stated properties are theorems: a step
function does not decrease as its input grows (`evalSteps_mono`), `linear` is the
identity, and a cubic Bézier maps 0 to 0 and 1 to 1.
-/
import L4Factoidal.Rendering.Animation.Fix

namespace L4Factoidal.Rendering.Animation

/-- CSS Easing 1 §4.1 `<step-position>`; `end_` is `end` and `jump-end`. -/
inductive StepPos where
  | start | jumpStart | end_ | jumpNone | jumpBoth
  deriving DecidableEq, Repr, Inhabited

inductive Easing where
  | linear
  | ease | easeIn | easeOut | easeInOut
  /-- `cubic-bezier(x1, y1, x2, y2)`, with x1 and x2 in [0, 1]. -/
  | cubic (x1 y1 x2 y2 : Int)
  /-- `steps(n, position)`, n ≥ 1 (n ≥ 2 for `jump-none`). -/
  | steps (n : Nat) (pos : StepPos)
  /-- `linear(...)` (CSS Easing 2 §2.2): the points as (input, output), at least two, every
  input present and none below the one before it (`linearPoints`). -/
  | points (pts : List (Int × Int))
  deriving DecidableEq, Repr, Inhabited

namespace Easing
open Fix (scale one roundDiv)

/-- 10²⁷: the denominator of `bezNum`. -/
def cube : Int := scale * scale * scale

/-- The cubic Bézier with control values `a` and `b` (the end values are 0 and 1) at the
parameter `t` in [0, 1], as a numerator over 10²⁷:
3(1-t)²t·a + 3(1-t)t²·b + t³. Exact. -/
def bezNum (a b t : Int) : Int :=
  let u := scale - t
  3 * u * u * t * a + 3 * u * t * t * b + t * t * t * scale

/-- Bisection for the parameter `t` in [`lo`, `hi`] where the x of the curve is `target`
(a numerator over 10²⁷); x does not decrease with `t` when x1 and x2 are in [0, 1]. -/
def solveGo (x1 x2 target : Int) : Nat → Int → Int → Int
  | 0, lo, hi =>
    if bezNum x1 x2 hi - target < target - bezNum x1 x2 lo then hi else lo
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    let v := bezNum x1 x2 mid
    if v == target then mid
    else if v < target then solveGo x1 x2 target fuel mid hi
    else solveGo x1 x2 target fuel lo mid

/-- The parameter at which the curve's x is `p` (in [0, 1]). 32 halvings of [0, 10⁹]
leave an interval of one unit. -/
def solveT (x1 x2 p : Int) : Int := solveGo x1 x2 (p * cube) 32 0 scale

/-- A cubic Bézier easing at input `p` (CSS Easing 1 §3): inside [0, 1] the y at the
parameter whose x is `p`; outside, the tangent at the nearer end point (§3: "the curve is
extended infinitely using tangent of the curve at the closest endpoint"). -/
def evalCubic (x1 y1 x2 y2 p : Int) : Int :=
  if p == 0 then 0
  else if p == one then one
  else if p < 0 then
    let slope : Int := if x1 > 0 then (Fix.div y1 x1).getD 0
      else if y1 == 0 && x2 > 0 then (Fix.div y2 x2).getD 0
      else 0
    Fix.mul p slope
  else if p > one then
    let slope : Int := if x2 < one then (Fix.div (y2 - one) (x2 - one)).getD 0
      else if y2 == one && x1 < one then (Fix.div (y1 - one) (x1 - one)).getD 0
      else 0
    one + Fix.mul (p - one) slope
  else roundDiv (bezNum y1 y2 (solveT x1 x2 p)) cube

/-- The number of jumps of a step function (CSS Easing 1 §4.2). -/
def jumps (n : Nat) : StepPos → Int
  | .jumpNone => (n : Int) - 1
  | .jumpBoth => (n : Int) + 1
  | _ => (n : Int)

/-- The step before clamping: ⌊p·n⌋, one more for a jump at the start, one less on the
before flag when p·n is whole. -/
def stepRaw (n : Nat) (pos : StepPos) (p : Int) (before : Bool) : Int :=
  p * (n : Int) / scale
    + (if pos == .start || pos == .jumpStart || pos == .jumpBoth then 1 else 0)
    - (if before && p * (n : Int) % scale == 0 then 1 else 0)

/-- The current step of CSS Easing 1 §4.2, clamped as the section says: not below 0 for
an input ≥ 0, not above the jumps for an input ≤ 1. -/
def stepOf (n : Nat) (pos : StepPos) (p : Int) (before : Bool) : Int :=
  let s := stepRaw n pos p before
  let s := if 0 ≤ p ∧ s < 0 then 0 else s
  if p ≤ one ∧ jumps n pos < s then jumps n pos else s

/-- A step function at input `p` with the before flag (CSS Easing 1 §4.2). -/
def evalSteps (n : Nat) (pos : StepPos) (p : Int) (before : Bool) : Int :=
  let j := jumps n pos
  if j ≤ 0 then p else roundDiv (stepOf n pos p before * scale) j

/-- CSS Easing 2 §2.2.1 "calculate linear easing output progress": the segment from the
last point whose input is not above `x` (the first segment before all of them, the last
past all of them) to the next point, continued as a straight line; two points of one
input give the second's output. `prev` is the point before `rest`. A loop over the
points: each call is a tail call. -/
def evalPointsGo (x : Int) : (Int × Int) → List (Int × Int) → Int
  | _, [] => x
  | a, b :: rest =>
    -- the segment a to b is the one when it is the last, or the next point is past x
    let here := match rest with
      | [] => true
      | _ => x < b.1
    if here then
      if a.1 == b.1 then b.2 else a.2 + roundDiv ((x - a.1) * (b.2 - a.2)) (b.1 - a.1)
    else evalPointsGo x b rest

def evalPoints (pts : List (Int × Int)) (x : Int) : Int :=
  match pts with
  | [] => x
  | [a] => a.2
  | a :: rest => evalPointsGo x a rest

/-- CSS Easing 2 §2.2 "create a linear easing function" from the stops as written (an
output and up to two inputs each): a first stop with no input is at 0, a last one at 1 or
at the largest input before it; an input is never below the largest before it; a stop
with two inputs is two points; the stops with no input between two that have one are
spread evenly. None for fewer than two stops. -/
def linearPoints (stops : List (Int × List Int)) : Option (List (Int × Int)) := Id.run do
  if stops.length < 2 then return none
  let n := stops.length
  let mut largest : Option Int := none
  let mut pts : Array (Option Int × Int) := #[]
  let mut i := 0
  for (out, inputs) in stops do
    let up := fun (v : Int) (l : Option Int) => match l with
      | some m => max v m
      | none => v
    match inputs with
    | [] =>
      if i == 0 then
        pts := pts.push (some 0, out)
        largest := some 0
      else if i + 1 == n then pts := pts.push (some (up one largest), out)
      else pts := pts.push (none, out)
    | a :: more =>
      let v := up a largest
      pts := pts.push (some v, out)
      largest := some v
      match more with
      | b :: _ =>
        let w := up b largest
        pts := pts.push (some w, out)
        largest := some w
      | [] => pure ()
    i := i + 1
  -- the inputs left out: evenly between the inputs on either side
  let mut out : Array (Int × Int) := #[]
  for k in [0:pts.size] do
    match pts[k]! with
    | (some v, o) => out := out.push (v, o)
    | (none, o) =>
      -- the point before has its input by now; the next point with one is ahead
      let lo := (out.back?.map (·.1)).getD 0
      let ahead := (List.range (pts.size - k)).find? fun d => ((pts[k + d]?).bind (·.1)).isSome
      match ahead with
      | some d =>
        let hi := (((pts[k + d]?).bind (·.1))).getD one
        out := out.push (lo + (hi - lo) / ((d : Int) + 1), o)
      | none => out := out.push (lo, o)
  return some out.toList

/-- The output progress of an easing function for an input progress (CSS Easing 1 §2 to
§4). `before` is the before flag of Web Animations §4.10.1 (only step functions read it). -/
def eval (e : Easing) (p : Int) (before : Bool := false) : Int :=
  match e with
  | .linear => p
  | .ease => evalCubic 250000000 100000000 250000000 one p
  | .easeIn => evalCubic 420000000 0 one one p
  | .easeOut => evalCubic 0 0 580000000 one p
  | .easeInOut => evalCubic 420000000 0 580000000 one p
  | .cubic x1 y1 x2 y2 => evalCubic x1 y1 x2 y2 p
  | .steps n pos => evalSteps n pos p before
  | .points pts => evalPoints pts p

/-! ## Text -/

/-- The text of an easing function, as `getComputedStyle` and the Web Animations API give
it (CSS Easing 1 §2.1, §3.1, §4.3 serialization): keywords stay; `steps(n, end)` is
`steps(n)`; `step-start` and `step-end` are their `steps()` forms. -/
def toText : Easing → String
  | .linear => "linear"
  | .ease => "ease"
  | .easeIn => "ease-in"
  | .easeOut => "ease-out"
  | .easeInOut => "ease-in-out"
  | .cubic x1 y1 x2 y2 =>
    s!"cubic-bezier({Fix.formatCss x1}, {Fix.formatCss y1}, {Fix.formatCss x2}, {Fix.formatCss y2})"
  | .steps n pos =>
    match pos with
    | .end_ => s!"steps({n})"
    | .start => s!"steps({n}, start)"
    | .jumpStart => s!"steps({n}, jump-start)"
    | .jumpNone => s!"steps({n}, jump-none)"
    | .jumpBoth => s!"steps({n}, jump-both)"
  -- CSS Easing 2 §2.2.2: every point with its output and its input as a percentage
  | .points pts =>
    "linear(" ++ ", ".intercalate (pts.map fun (i, o) => s!"{Fix.formatCss o} {Fix.formatCss (i * 100)}%") ++ ")"

/-- The arguments of `name(...)` when `s` is that function call, split at commas. -/
def callArgs (name s : String) : Option (List String) :=
  if s.startsWith (name ++ "(") && s.endsWith ")" then
    let inner := ((s.drop (name.length + 1)).toString.dropEnd 1).toString
    some ((inner.splitOn ",").map (·.trimAscii.toString))
  else none

/-- Read an easing function (CSS Easing 1 `<easing-function>`); `none` when the text is
not one: an x outside [0, 1], a step count below 1 (below 2 for `jump-none`), or other
text. ASCII case-insensitive. -/
def parse (text : String) : Option Easing :=
  let s := text.trimAscii.toString.toLower
  match s with
  | "linear" => some .linear
  | "ease" => some .ease
  | "ease-in" => some .easeIn
  | "ease-out" => some .easeOut
  | "ease-in-out" => some .easeInOut
  | "step-start" => some (.steps 1 .start)
  | "step-end" => some (.steps 1 .end_)
  | _ =>
    match callArgs "cubic-bezier" s with
    | some [a, b, c, d] =>
      match Fix.parse a, Fix.parse b, Fix.parse c, Fix.parse d with
      | some x1, some y1, some x2, some y2 =>
        if 0 ≤ x1 && x1 ≤ one && 0 ≤ x2 && x2 ≤ one then some (.cubic x1 y1 x2 y2) else none
      | _, _, _, _ => none
    | some _ => none
    | none =>
      match callArgs "steps" s with
      | some [n] =>
        match n.toNat? with
        | some k => if k ≥ 1 && n.all Char.isDigit then some (.steps k .end_) else none
        | none => none
      | some [n, pos] =>
        let p : Option StepPos := match pos with
          | "start" => some .start
          | "jump-start" => some .jumpStart
          | "end" | "jump-end" => some .end_
          | "jump-none" => some .jumpNone
          | "jump-both" => some .jumpBoth
          | _ => none
        match n.toNat?, p with
        | some k, some p =>
          if k ≥ 1 && n.all Char.isDigit && (p != .jumpNone || k ≥ 2) then some (.steps k p) else none
        | _, _ => none
      | _ =>
        -- `linear(<number> && <percentage>{0,2} #)`
        match callArgs "linear" s with
        | some args =>
          let stops := args.mapM fun (arg : String) =>
            let words := (arg.splitOn " ").filter (· != "")
            let numbers := words.filterMap fun w => if w.endsWith "%" then none else Fix.parse w
            let inputs := words.filterMap fun w =>
              if w.endsWith "%" then (Fix.parse (w.dropEnd 1).toString).map (roundDiv · 100) else none
            if numbers.length == 1 && inputs.length ≤ 2 && numbers.length + inputs.length == words.length then
              some (numbers.headD 0, inputs)
            else none
          (stops.bind linearPoints).map .points
        | none => none

/-! ## Theorems -/

/-- A square is not negative. -/
theorem sq_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have n : 0 ≤ -x := by omega
    have := Int.mul_nonneg n n
    rwa [Int.neg_mul_neg] at this

/-- The polynomial of `bezNum_mono` over any scale `S > 0`. The difference of the two
sides is affine in `a` and in `b`, so `S²` times it is the sum over the four corners of
the square [0, S]² of the corner's difference, each weighted by a product of distances to
the opposite sides; each corner's difference is `S (t - s)` times a sum of squares or of
products of non-negative numbers. -/
theorem bez_mono (S a b s t : Int) (hS : 0 < S) (ha0 : 0 ≤ a) (ha1 : a ≤ S) (hb0 : 0 ≤ b) (hb1 : b ≤ S)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ S) :
    3 * (S - s) * (S - s) * s * a + 3 * (S - s) * s * s * b + s * s * s * S ≤
    3 * (S - t) * (S - t) * t * a + 3 * (S - t) * t * t * b + t * t * t * S := by
  have d : 0 ≤ t - s := by omega
  have u : 0 ≤ S - t := by omega
  have v : 0 ≤ S - s := by omega
  have t0 : 0 ≤ t := by omega
  have a' : 0 ≤ S - a := by omega
  have b' : 0 ≤ S - b := by omega
  -- the corners (a, b) = (0, 0), (S, S), (S, 0), (0, S), each without its factor S
  have c00 : 0 ≤ (t - s) * (t * t + t * s + s * s) :=
    Int.mul_nonneg d (by
      have h1 := Int.mul_nonneg t0 t0
      have h2 := Int.mul_nonneg t0 hs
      have h3 := Int.mul_nonneg hs hs
      omega)
  have c11 : 0 ≤ (t - s) * ((S - t) * (S - t) + (S - t) * (S - s) + (S - s) * (S - s)) :=
    Int.mul_nonneg d (by
      have h1 := Int.mul_nonneg u u
      have h2 := Int.mul_nonneg u v
      have h3 := Int.mul_nonneg v v
      omega)
  have c10 : 0 ≤ (t - s) * (3 * ((t + s - S) * (t + s - S)) + (t - s) * (t - s)) :=
    Int.mul_nonneg d (by
      have h1 := sq_nonneg (t + s - S)
      have h2 := Int.mul_nonneg d d
      omega)
  have c01 : 0 ≤ (t - s) * (3 * ((S - t) * (t + s)) + (t - s) * (t + 2 * s)) :=
    Int.mul_nonneg d (by
      have h1 := Int.mul_nonneg u (by omega : 0 ≤ t + s)
      have h2 := Int.mul_nonneg d (by omega : 0 ≤ t + 2 * s)
      omega)
  have w11 := Int.mul_nonneg (Int.mul_nonneg ha0 hb0) c11
  have w10 := Int.mul_nonneg (Int.mul_nonneg ha0 b') c10
  have w01 := Int.mul_nonneg (Int.mul_nonneg a' hb0) c01
  have w00 := Int.mul_nonneg (Int.mul_nonneg a' b') c00
  -- S·S times the difference of the two sides is S times the weighted sum of the corners
  have key : S * S * ((3 * (S - t) * (S - t) * t * a + 3 * (S - t) * t * t * b + t * t * t * S) -
        (3 * (S - s) * (S - s) * s * a + 3 * (S - s) * s * s * b + s * s * s * S)) =
      S * (a * b * ((t - s) * ((S - t) * (S - t) + (S - t) * (S - s) + (S - s) * (S - s))) +
           a * (S - b) * ((t - s) * (3 * ((t + s - S) * (t + s - S)) + (t - s) * (t - s))) +
           (S - a) * b * ((t - s) * (3 * ((S - t) * (t + s)) + (t - s) * (t + 2 * s))) +
           (S - a) * (S - b) * ((t - s) * (t * t + t * s + s * s))) := by
    grind
  have sum : 0 ≤ S * (a * b * ((t - s) * ((S - t) * (S - t) + (S - t) * (S - s) + (S - s) * (S - s))) +
           a * (S - b) * ((t - s) * (3 * ((t + s - S) * (t + s - S)) + (t - s) * (t - s))) +
           (S - a) * b * ((t - s) * (3 * ((S - t) * (t + s)) + (t - s) * (t + 2 * s))) +
           (S - a) * (S - b) * ((t - s) * (t * t + t * s + s * s))) :=
    Int.mul_nonneg (Int.le_of_lt hS) (by omega)
  rw [← key] at sum
  have pos : 0 < S * S := Int.mul_pos hS hS
  have diff : 0 ≤ (3 * (S - t) * (S - t) * t * a + 3 * (S - t) * t * t * b + t * t * t * S) -
        (3 * (S - s) * (S - s) * s * a + 3 * (S - s) * s * s * b + s * s * s * S) := by
    first
      | exact Int.nonneg_of_mul_nonneg_right sum pos
      | exact Int.le_of_mul_le_mul_left (by simpa using sum) pos
  omega

/-- Kind: monotonicity. Says: the x of a cubic Bézier whose control values are in [0, 1]
does not decrease as the parameter goes from 0 to 1 (exactly, as numerators over 10²⁷):
what the bisection of `solveT` relies on, and why CSS Easing 1 §3 restricts x1 and x2 to
[0, 1]. Does not say: that `solveT` finds the nearest parameter (tested), nor that the
easing's output is monotone (it is not when y1 or y2 is outside [0, 1]). -/
theorem bezNum_mono (a b s t : Int) (ha0 : 0 ≤ a) (ha1 : a ≤ scale) (hb0 : 0 ≤ b) (hb1 : b ≤ scale)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ scale) : bezNum a b s ≤ bezNum a b t := by
  have hS : (0 : Int) < scale := by decide
  exact bez_mono scale a b s t hS ha0 ha1 hb0 hb1 hs hst ht

/-- Kind: identity. Says: `linear` gives its input, whatever the before flag. Does not
say: anything about the other functions. -/
theorem eval_linear (p : Int) (before : Bool) : eval .linear p before = p := rfl

/-- Kind: end point. Says: every cubic Bézier easing maps input 0 to 0. Does not say: its
value near 0. -/
theorem evalCubic_zero (x1 y1 x2 y2 : Int) : evalCubic x1 y1 x2 y2 0 = 0 := by
  simp [evalCubic]

/-- Kind: end point. Says: every cubic Bézier easing maps input 1 to 1. Does not say: its
value near 1. -/
theorem evalCubic_one (x1 y1 x2 y2 : Int) : evalCubic x1 y1 x2 y2 one = one := by
  simp [evalCubic, one, scale]

/-- Kind: end points. Says: the keyword and `cubic-bezier()` easings map 0 to 0 and 1 to
1. Does not say: this of step functions (a jump at the start maps 0 above 0). -/
theorem eval_ends (e : Easing) (h : ∀ n pos, e ≠ .steps n pos) (h' : ∀ pts, e ≠ .points pts) (before : Bool) :
    eval e 0 before = 0 ∧ eval e one before = one := by
  cases e with
  | linear => exact ⟨rfl, rfl⟩
  | ease => exact ⟨evalCubic_zero .., evalCubic_one ..⟩
  | easeIn => exact ⟨evalCubic_zero .., evalCubic_one ..⟩
  | easeOut => exact ⟨evalCubic_zero .., evalCubic_one ..⟩
  | easeInOut => exact ⟨evalCubic_zero .., evalCubic_one ..⟩
  | cubic x1 y1 x2 y2 => exact ⟨evalCubic_zero .., evalCubic_one ..⟩
  | steps n pos => exact absurd rfl (h n pos)
  | points pts => exact absurd rfl (h' pts)

/-- Kind: identity. Says: `linear(0, 1)` is the identity, as the keyword `linear`, at
every input, in range or not. Does not say: anything of other point lists. -/
theorem evalPoints_identity (p : Int) : evalPoints [(0, 0), (one, one)] p = p := by
  have ne : ((0 : Int) == one) = false := by decide
  have h := Fix.roundDiv_mul p one (by decide)
  simp [evalPoints, evalPointsGo, ne, h]

/-- Kind: end points. Says: a `linear()` function of two points at inputs 0 and 1 gives
the first output at 0 and the second at 1, exactly. Does not say: this of lists whose
first input is not 0 or whose last is not 1 (their ends are on a continued segment). -/
theorem evalPoints_ends (a b : Int) :
    evalPoints [(0, a), (one, b)] 0 = a ∧ evalPoints [(0, a), (one, b)] one = b := by
  have ne : ((0 : Int) == one) = false := by decide
  have z : roundDiv 0 one = 0 := by decide
  have h : roundDiv (one * (b - a)) one = b - a := by
    rw [Int.mul_comm]
    exact Fix.roundDiv_mul (b - a) one (by decide)
  constructor
  · simp [evalPoints, evalPointsGo, ne, z]
  · simp [evalPoints, evalPointsGo, ne, h]
    omega

/-- The straight line of one `linear()` segment from point `a` to point `b` at input `x`
(the expression `evalPointsGo` evaluates for points of different inputs). -/
def segment (a b : Int × Int) (x : Int) : Int :=
  a.2 + roundDiv ((x - a.1) * (b.2 - a.2)) (b.1 - a.1)

/-- Kind: unfolding. Says: a `linear()` function of two points of increasing input is its
one segment, at every input (also outside the two inputs, where the line continues). -/
theorem evalPoints_two (a b : Int × Int) (h : a.1 < b.1) (x : Int) :
    evalPoints [a, b] x = segment a b x := by
  have ne : (a.1 == b.1) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [evalPoints, evalPointsGo, segment, ne]

/-- Kind: monotonicity. Says: on a segment whose output does not fall, the output
progress does not fall as the input grows (all inputs, exactly, rounding included).
Does not say: this of a whole point list (its segments may fall). -/
theorem segment_mono (a b : Int × Int) (h : a.1 < b.1) (ho : a.2 ≤ b.2) {x y : Int} (hxy : x ≤ y) :
    segment a b x ≤ segment a b y := by
  unfold segment
  have hm : (x - a.1) * (b.2 - a.2) ≤ (y - a.1) * (b.2 - a.2) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hr := Fix.roundDiv_mono hm (show 0 < b.1 - a.1 by omega)
  omega

/-- Kind: bound. Says: between the inputs of its two points, a segment whose output does
not fall stays between the two outputs. Does not say: this outside the two inputs. -/
theorem segment_between (a b : Int × Int) (h : a.1 < b.1) (ho : a.2 ≤ b.2) {x : Int}
    (h0 : a.1 ≤ x) (h1 : x ≤ b.1) : a.2 ≤ segment a b x ∧ segment a b x ≤ b.2 := by
  unfold segment
  have hd : 0 < b.1 - a.1 := by omega
  constructor
  · have hn := Fix.roundDiv_nonneg
      (Int.mul_nonneg (show 0 ≤ x - a.1 by omega) (show 0 ≤ b.2 - a.2 by omega)) hd
    omega
  · have hm : (x - a.1) * (b.2 - a.2) ≤ (b.2 - a.2) * (b.1 - a.1) := by
      rw [Int.mul_comm (b.2 - a.2)]
      exact Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have hr := Fix.roundDiv_mono hm hd
    rw [Fix.roundDiv_mul _ _ hd] at hr
    omega

/-- Kind: monotonicity. Says: `linear(a, b)` with `a ≤ b` (two points, inputs 0 and 1)
does not decrease, at every input. -/
theorem evalPoints_two_mono (a b : Int) (ho : a ≤ b) {x y : Int} (hxy : x ≤ y) :
    evalPoints [(0, a), (one, b)] x ≤ evalPoints [(0, a), (one, b)] y := by
  have h : ((0 : Int), a).1 < (one, b).1 := by show (0 : Int) < one; decide
  rw [evalPoints_two _ _ h, evalPoints_two _ _ h]
  exact segment_mono _ _ h ho hxy

/-- Kind: monotonicity. Says: the step before clamping does not decrease as the input
grows, for one before flag and at least one step. Does not say: more. -/
theorem stepRaw_mono (n : Nat) (pos : StepPos) (before : Bool) (hn : 0 < n) {p q : Int} (h : p ≤ q) :
    stepRaw n pos p before ≤ stepRaw n pos q before := by
  have hn' : (0 : Int) < (n : Int) := by omega
  have hprod : p * (n : Int) ≤ q * (n : Int) := Int.mul_le_mul_of_nonneg_right h (by omega)
  have hdiv : p * (n : Int) / scale ≤ q * (n : Int) / scale := Int.ediv_le_ediv (by decide) hprod
  -- when q·n is whole and p < q, ⌊p·n⌋ is below q·n
  have strict : p < q → q * (n : Int) % scale = 0 → p * (n : Int) / scale + 1 ≤ q * (n : Int) / scale := by
    intro hlt hmod
    have hlt' : p * (n : Int) < q * (n : Int) := Int.mul_lt_mul_of_pos_right hlt hn'
    have hq : q * (n : Int) / scale * scale = q * (n : Int) :=
      Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hmod)
    have : p * (n : Int) / scale < q * (n : Int) / scale :=
      Int.ediv_lt_of_lt_mul (by decide) (by rw [hq]; exact hlt')
    omega
  unfold stepRaw
  by_cases hpq : p = q
  · subst hpq; exact Int.le_refl _
  · have hlt : p < q := by omega
    by_cases hq : (before && q * (n : Int) % scale == 0) = true
    · have hmod : q * (n : Int) % scale = 0 := by simp_all
      have := strict hlt hmod
      rw [if_pos hq]
      split <;> omega
    · rw [if_neg hq]
      split <;> omega

/-- Kind: monotonicity. Says: the current step of a step function does not decrease as
the input grows (same before flag, at least one step). Does not say: more. -/
theorem stepOf_mono (n : Nat) (pos : StepPos) (before : Bool) (hn : 0 < n) {p q : Int} (h : p ≤ q) :
    stepOf n pos p before ≤ stepOf n pos q before := by
  have hr := stepRaw_mono n pos before hn h
  unfold stepOf
  simp only
  split <;> split <;> split <;> split <;> omega

/-- Kind: monotonicity (CSS Easing 1 §4: a step function is a non-decreasing staircase).
Says: for one before flag, at least one step and a positive number of jumps, the output of
a step function does not decrease as the input grows, over all inputs (also outside
[0, 1]). Does not say: anything of cubic Bézier easings, whose output can go down when a
control point's y is outside [0, 1]. -/
theorem evalSteps_mono (n : Nat) (pos : StepPos) (before : Bool) (hn : 0 < n) (hj : 0 < jumps n pos)
    {p q : Int} (h : p ≤ q) : evalSteps n pos p before ≤ evalSteps n pos q before := by
  unfold evalSteps
  simp only
  rw [if_neg (by omega), if_neg (by omega)]
  apply Fix.roundDiv_mono _ hj
  exact Int.mul_le_mul_of_nonneg_right (stepOf_mono n pos before hn h) (by decide)

/-- Kind: range. Says: for an input in [0, 1], the current step is between 0 and the
number of jumps (when that is not negative). Does not say: this outside [0, 1]. -/
theorem stepOf_range (n : Nat) (pos : StepPos) (before : Bool) (p : Int) (h0 : 0 ≤ p) (h1 : p ≤ one)
    (hj : 0 ≤ jumps n pos) : 0 ≤ stepOf n pos p before ∧ stepOf n pos p before ≤ jumps n pos := by
  unfold stepOf
  simp only
  split <;> split <;> omega

#guard eval .linear 123 == 123
#guard eval (.steps 1 .end_) Fix.half == 0
#guard eval (.steps 1 .start) Fix.half == one
#guard eval (.steps 4 .end_) Fix.half == Fix.half
#guard eval (.steps 4 .end_) 0 == 0
#guard eval (.steps 4 .start) 0 == 250000000
#guard eval (.steps 4 .start) 0 true == 0
#guard eval (.steps 4 .end_) one == one
#guard eval (.steps 4 .end_) one true == 750000000
#guard eval (.steps 3 .jumpNone) Fix.half == Fix.half
#guard eval (.steps 3 .jumpBoth) Fix.half == Fix.half
#guard eval (.steps 2 .jumpNone) 0 == 0
#guard eval (.steps 2 .jumpNone) one == one
-- the easing the interpolation tests build: cubic-bezier(0, b, 1, b) with b = (8y - 1)/6
-- gives y at 0.5
#guard eval (.cubic 0 (-233333333) one (-233333333)) Fix.half == -50000000
#guard (parse "cubic-bezier(0, 0.23333333333333334, 1, 0.23333333333333334)").map (eval · Fix.half) == some 300000000
#guard (parse "cubic-bezier(0, 1.8333333333333333, 1, 1.8333333333333333)").map (eval · Fix.half) == some 1500000000
#guard (parse "cubic-bezier(0, -0.5666666666666667, 1, -0.5666666666666667)").map (eval · Fix.half) == some (-300000000)
#guard (parse "cubic-bezier(0, 0.6333333333333333, 1, 0.6333333333333333)").map (eval · Fix.half) == some 600000000
-- ease at 0.5 is about 0.8024
#guard (eval .ease Fix.half - 802403388).natAbs < 100
#guard eval .ease 0 == 0 && eval .ease one == one
-- outside [0, 1]: the end tangents
#guard eval (.cubic 500000000 one 500000000 one) (-one) == -2 * one
#guard eval .linear (2 * one) == 2 * one
#guard parse "ease-in" == some .easeIn
#guard parse " STEPS(3, Jump-Both) " == some (.steps 3 .jumpBoth)
#guard parse "steps(1, jump-none)" == none
#guard parse "steps(0)" == none
#guard parse "steps(2.5)" == none
#guard parse "cubic-bezier(1.5, 0, 1, 1)" == none
#guard parse "cubic-bezier(0.1, 5, 0.23, 0)" == some (.cubic 100000000 (5 * one) 230000000 0)
#guard parse "step-start" == some (.steps 1 .start)
#guard parse "bounce" == none
-- linear() (css/css-easing/linear-timing-functions-output.html, -syntax.html)
#guard (parse "linear(0, 1.5, 1)").map (fun e => [0, 250000000, Fix.half, 750000000, one].map (eval e ·)) ==
  some [0, 750000000, 1500000000, 1250000000, one]
#guard (parse "linear(1, -0.5, 0)").map (fun e => [0, 250000000, Fix.half, 750000000, one].map (eval e ·)) ==
  some [one, 250000000, -500000000, -250000000, 0]
#guard (parse "linear(0, 1)").map (eval · 330000000) == some 330000000
-- past the ends the first and the last segment continue
#guard (parse "linear(0, 0.5 25%, 1)").map (fun e => [-one, 2 * one].map (eval e ·)) == some [-2 * one, 1666666667]
#guard (parse "linear(0, 1)").map toText == some "linear(0 0%, 1 100%)"
#guard (parse "linear(0, 0.5 25%, 1)").map toText == some "linear(0 0%, 0.5 25%, 1 100%)"
#guard (parse "linear(0, 0.25, 0.5 50%, 1)").map toText == some "linear(0 0%, 0.25 25%, 0.5 50%, 1 100%)"
-- a stop with two inputs is two points; an input never goes back
#guard (parse "linear(0, 0.5 25% 75%, 1)").map toText == some "linear(0 0%, 0.5 25%, 0.5 75%, 1 100%)"
#guard (parse "linear(0 50%, 0.5 25%, 1)").map toText == some "linear(0 50%, 0.5 50%, 1 100%)"
#guard (parse "linear(25% 0, 1)").map toText == some "linear(0 25%, 1 100%)"
#guard parse "linear(1)" == none && parse "linear()" == none && parse "linear(0 1, 1)" == none && parse "linear(0 1% 2% 3%, 1)" == none
#guard ((parse "linear(0, 0.5 25%, 1)").map toText).bind parse == parse "linear(0, 0.5 25%, 1)"
#guard toText (.steps 1 .start) == "steps(1, start)"
#guard toText (.steps 2 .end_) == "steps(2)"
#guard toText (.cubic 100000000 (5 * one) 230000000 0) == "cubic-bezier(0.1, 5, 0.23, 0)"
-- parse after serialize is the identity on these
#guard [Easing.linear, .ease, .easeIn, .easeOut, .easeInOut, .cubic 100000000 (-one) 230000000 (2 * one),
  .steps 1 .start, .steps 3 .jumpStart, .steps 2 .end_, .steps 2 .jumpNone, .steps 5 .jumpBoth].all
  fun e => parse (toText e) == some e

end Easing
end L4Factoidal.Rendering.Animation
