/-
L4Factoidal.WebNN.Approx: one definition of each transcendental function WebNN needs (exp,
expm1, log, log1p, tanh, sigmoid, softplus, erf, erfc, elu, gelu), shared by the CPU reference
and the GPU kernels (record: docs/designissues/2026-11-14-gpu-compute-and-webnn.md, part 2).

Each function is written once, over an abstract arithmetic (`Arith`): only +, −, ×, ÷, a
fused multiply-add, comparisons and selection, `floor`, `abs`, and the exact scalings
`ldexp` and `frexp`; no library transcendental. Three instances evaluate the same
expression tree in the same order:

- `Float` (binary64): the CPU reference (`Compute.unaryF` and the operators that use these
  functions call it, then round once to the tensor's type);
- `Float32`: a bit-level model of the GPU's single-precision evaluation, for measurement on
  the CPU (its `fma` is the binary64 product-sum rounded once to binary32, which can differ
  from a true fused binary32 operation by a double rounding in rare cases);
- `Wgsl.Expr`: the WGSL the GPU kernels run, built as `let` statements (`share`) and literal
  `for` loops, then validated and hardened by `Wgsl.finish` like any page shader.

Why `fma` is written out: the WGSL-to-Metal path fuses `a * b + c` into a fused
multiply-add even through a `let` (measured, record section 2.9); writing every product-sum
as `fma` makes the fused form the definition, so the compiler has nothing left to choose.

Forms: exp by Cody–Waite reduction (`n = ⌊x·log₂e + ½⌋`, `r = x − n·ln2` in two parts) and the
degree-8 Taylor polynomial on `|r| ≤ ln2/2`; expm1 by the degree-9 Taylor polynomial below
`|x| < 0.35`, else `exp(x) − 1`; log by `frexp`, the reduction of the mantissa to
`[√½, √2)` and `2·atanh(s)` to `s¹³`; log1p by `2·atanh(y/(2+y))` below `y < 1`; tanh by
`expm1(2|x|)/(expm1(2|x|)+2)` (`x` itself below `2⁻¹²`, 1 above 9); erf and erfc by the
reference's series (90 terms) and continued fraction (60 levels), erfc by the continued
fraction (200 levels) from ½ up (no cancellation in `1 − erf`); `e^(−x²)` from `x² = hi + lo`.
-/
import L4Factoidal.PageGpu.Wgsl

namespace L4Factoidal.WebNN.Approx

/-- An arithmetic in which the functions below are written. `Cond` is its type of conditions. -/
class Arith (m : Type → Type) (α : Type) where
  Cond : Type
  lit : Float → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  abs : α → α
  floor : α → α
  /-- `a · b + c` rounded once. -/
  fma : α → α → α → α
  lt : α → α → Cond
  /-- `if c then a else b` (both evaluated: the arithmetic has no effects). -/
  sel : Cond → α → α → α
  /-- `a · 2ⁿ`, `n` an integral value. -/
  ldexp : α → α → α
  /-- `frexp`: the fraction in `[½, 1)` and the exponent of a finite non-zero value. -/
  frexpM : α → α
  frexpE : α → α
  /-- A value used more than once is computed once. -/
  share : α → m α
  /-- `n` iterations over the values `vs`, the body given the iteration's number. -/
  loop : Nat → List α → (α → List α → m (List α)) → m (List α)
  /-- The format's range: the largest finite value, the smallest normal value, and the
  arguments beyond which `e^x` overflows or is below half the smallest subnormal. -/
  maxFinite : Float
  minNormal : Float
  expHi : Float
  expLo : Float

open Arith

section
variable {m : Type → Type} {α : Type} [Monad m] [A : Arith m α]

local notation "L" => (Arith.lit m : Float → α)

/-- `fma`-Horner: `c₀ + x·(c₁ + x·(… + x·cₙ))`, the coefficients from the constant term up. -/
def horner (x : α) (cs : List Float) : α :=
  match cs.reverse with
  | [] => L 0.0
  | c :: rest => rest.foldl (fun acc k => fma (m := m) acc x (L k)) (L c)

/-- 1/k! for k = 0 … n. -/
def invFact (n : Nat) : List Float :=
  (List.range (n + 1)).map fun k => 1.0 / (List.range k).foldl (fun p i => p * Float.ofNat (i + 1)) 1.0

def log2e : Float := 1.4426950408889634
/-- ln 2 in two parts: `ln2hi` has 18 significant bits, so `n · ln2hi` is exact in binary32
for `|n| ≤ 2⁶`… and in the fused form for every `n` this reduction meets. -/
def ln2hi : Float := 0.693145751953125
def ln2lo : Float := 1.4286068203094172e-6

/-- `e^x`. -/
def exp (x : α) : m α := do
  let lo := Arith.expLo m α
  let hi := Arith.expHi m α
  let x ← share (sel (m := m) (lt (m := m) x (L lo)) (L lo) (sel (m := m) (lt (m := m) (L hi) x) (L hi) x))
  let n ← share (floor (m := m) (fma (m := m) x (L log2e) (L 0.5)))
  let r ← share (fma (m := m) n (L (-ln2lo)) (fma (m := m) n (L (-ln2hi)) x))
  pure (ldexp (m := m) (horner (m := m) r (invFact 8)) n)

/-- `e^x − 1`, accurate near 0. -/
def expm1 (x : α) : m α := do
  let x ← share x
  let small ← share (mul (m := m) x (horner (m := m) x ((invFact 9).drop 1)))
  let big ← exp x
  pure (sel (m := m) (lt (m := m) (abs (m := m) x) (L 0.35)) small (sub (m := m) big (L 1.0)))

/-- `2·atanh(s) = 2(s + s³/3 + … + s¹³/13)`, for `|s| ≤ 0.18`. -/
def atanh2 (s : α) : m α := do
  let s ← share s
  let s2 ← share (mul (m := m) s s)
  pure (mul (m := m) (mul (m := m) (L 2.0) s) (horner (m := m) s2 ((List.range 7).map fun k => 1.0 / Float.ofNat (2 * k + 1))))

/-- A positive infinity and a NaN computed at run time (a WGSL constant expression may not
overflow or divide by zero): `1/(|x|·0)` and `(|x|·0)/(|x|·0)`, for a finite `x`. -/
def infOf (x : α) : α := div (m := m) (L 1.0) (mul (m := m) (abs (m := m) x) (L 0.0))
def nanOf (x : α) : α := let z := mul (m := m) (abs (m := m) x) (L 0.0); div (m := m) z z

/-- `ln x`: `−∞` at 0, NaN below 0, `x` at `+∞`. -/
def log (x : α) : m α := do
  let x ← share x
  let fm ← share (frexpM (m := m) x)
  let fe ← share (frexpE (m := m) x)
  let lo := lt (m := m) fm (L 0.70710678118654752)
  let mm ← share (sel (m := m) lo (mul (m := m) fm (L 2.0)) fm)
  let e ← share (sel (m := m) lo (sub (m := m) fe (L 1.0)) fe)
  let ath ← atanh2 (div (m := m) (sub (m := m) mm (L 1.0)) (add (m := m) mm (L 1.0)))
  let v := fma (m := m) e (L ln2hi) (fma (m := m) e (L ln2lo) ath)
  let zero := sub (m := m) (L 0.0) (infOf (m := m) mm)
  pure (sel (m := m) (lt (m := m) x (L 0.0)) (nanOf (m := m) mm)
    (sel (m := m) (lt (m := m) x (L (Arith.minNormal m α))) (sel (m := m) (lt (m := m) (L 0.0) x) v zero)
      (sel (m := m) (lt (m := m) (L (Arith.maxFinite m α)) x) x v)))

/-- `ln(1 + y)` for `y ≥ 0`, accurate near 0. -/
def log1p (y : α) : m α := do
  let y ← share y
  let small ← atanh2 (div (m := m) y (add (m := m) (L 2.0) y))
  let big ← log (add (m := m) (L 1.0) y)
  pure (sel (m := m) (lt (m := m) y (L 1.0)) small big)

/-- `tanh x`. -/
def tanh (x : α) : m α := do
  let x ← share x
  let a ← share (abs (m := m) x)
  let em ← share (← expm1 (mul (m := m) (L 2.0) a))
  let t := div (m := m) em (add (m := m) em (L 2.0))
  let t := sel (m := m) (lt (m := m) (L 9.0) a) (L 1.0) t
  let t ← share (sel (m := m) (lt (m := m) x (L 0.0)) (neg (m := m) t) t)
  pure (sel (m := m) (lt (m := m) a (L 2.44140625e-4)) x t)

/-- `1/(1 + e^(−x))`. -/
def sigmoid (x : α) : m α := do
  let e ← exp (neg (m := m) x)
  pure (div (m := m) (L 1.0) (add (m := m) (L 1.0) e))

/-- `ln(1 + e^x)`: `x` above 40. -/
def softplus (x : α) : m α := do
  let x ← share x
  let l ← log1p (← exp x)
  pure (sel (m := m) (lt (m := m) (L 40.0) x) x l)

/-- `x^y`: for an integral `|y| < 2²⁴`, binary powering over its 25 bits (exact for exact
products; `1/xⁿ` for negative `y`); otherwise `e^(y · ln x)` (NaN for negative `x`). -/
def pow (x y : α) : m α := do
  let x ← share x
  let y ← share y
  let ay ← share (abs (m := m) y)
  let r ← loop (m := m) 25 [L 1.0, x, ay] fun _ vs => do
    let acc := vs.headD (L 1.0)
    let b := vs.getD 1 (L 1.0)
    let n := vs.getD 2 (L 0.0)
    let h ← share (floor (m := m) (mul (m := m) n (L 0.5)))
    let bit := sub (m := m) n (mul (m := m) h (L 2.0))
    pure [sel (m := m) (lt (m := m) (L 0.5) bit) (mul (m := m) acc b) acc, mul (m := m) b b, h]
  let ip ← share (r.headD (L 1.0))
  let ipow := sel (m := m) (lt (m := m) y (L 0.0)) (div (m := m) (L 1.0) ip) ip
  let l ← log x
  let e ← share (← exp (mul (m := m) y l))
  pure (sel (m := m) (lt (m := m) (floor (m := m) y) y) e (sel (m := m) (lt (m := m) ay (L 16777216.0)) ipow e))

def sqrtPi : Float := 1.7724538509055159

/-- `e^(−c·x²)` for `c` a power of 2 (exact scaling): `x²` as `hi + lo` (`lo = fma(x, x, −hi)`,
exact when the fma is fused), so the exponent carries no rounding of `x²`:
`e^(−c·hi) · (1 − c·lo)`. -/
def expNegSq (x : α) (c : Float) : m α := do
  let x ← share x
  let hi ← share (mul (m := m) x x)
  let lo ← share (fma (m := m) x x (neg (m := m) hi))
  let e ← exp (mul (m := m) (L (-c)) hi)
  pure (mul (m := m) e (fma (m := m) (L (-c)) lo (L 1.0)))

/-- `erf a` for `0 ≤ a < 2.5`: the series `2/√π · e^(−a²) · Σ 2ⁿa^(2n+1)/(1·3·…·(2n+1))`, 90 terms. -/
def erfSmall (a : α) (e : α) : m α := do
  let a ← share a
  let x2 ← share (mul (m := m) (L 2.0) (mul (m := m) a a))
  let r ← loop (m := m) 90 [a, a] fun n vs => do
    let s := vs.headD a
    let term := vs.getD 1 a
    let term' ← share (div (m := m) (mul (m := m) term x2) (fma (m := m) n (L 2.0) (L 3.0)))
    pure [add (m := m) s term', term']
  pure (mul (m := m) (mul (m := m) (L (2.0 / sqrtPi)) e) (r.headD a))

/-- `erfc a` by the continued fraction with `levels` levels (60 from 2.5 up; 200 from ½ up,
relative error below 10⁻⁸ there). -/
def erfcLarge (a : α) (e : α) (levels : Nat := 60) : m α := do
  let a ← share a
  let r ← loop (m := m) levels [a] fun k vs =>
    pure [add (m := m) a (div (m := m) (div (m := m) (sub (m := m) (L (Float.ofNat levels)) k) (L 2.0)) (vs.headD a))]
  pure (div (m := m) e (mul (m := m) (L sqrtPi) (r.headD a)))

/-- `erf x` (the reference's branch at 2.5). -/
def erf (x : α) : m α := do
  let x ← share x
  let a ← share (abs (m := m) x)
  let e ← share (← expNegSq a 1.0)
  let s ← share (← erfSmall a e)
  let l ← erfcLarge a e
  let r ← share (sel (m := m) (lt (m := m) a (L 2.5)) s (sub (m := m) (L 1.0) l))
  pure (sel (m := m) (lt (m := m) x (L 0.0)) (neg (m := m) r) r)

/-- `erfc a` for `a ≥ 0`, with no cancellation: `1 − erf a` below ½ (where `erf a < 0.53`),
the continued fraction (200 levels) from ½ up. -/
def erfcPos (a : α) : m α := do
  let a ← share a
  let e ← share (← expNegSq a 1.0)
  let s ← erfSmall a e
  let l ← share (← erfcLarge a e 200)
  pure (sel (m := m) (lt (m := m) a (L 0.5)) (sub (m := m) (L 1.0) s) l)

/-- `elu`: `x` above 0, `alpha · expm1(x)` below. -/
def elu (alpha : Float) (x : α) : m α := do
  let x ← share x
  let e ← expm1 x
  pure (sel (m := m) (lt (m := m) x (L 0.0)) (mul (m := m) (L alpha) e) x)

/-- `gelu x = x/2 · erfc(−x/√2)`: `x/2 · (1 + erf(x/√2))` from 0 up, `x/2 · erfc(|x|/√2)`
below (no cancellation). -/
def gelu (x : α) : m α := do
  let x ← share x
  let a ← share (div (m := m) (abs (m := m) x) (L 1.4142135623730951))
  -- e^(−a²) = e^(−x²/2), from x itself (a carries the rounding of the division)
  let e ← share (← expNegSq x 0.5)
  let ef ← erfSmall a e
  let el ← share (← erfcLarge a e 200)
  let erfA := sel (m := m) (lt (m := m) a (L 2.5)) ef (sub (m := m) (L 1.0) el)
  let erfcA := sel (m := m) (lt (m := m) a (L 0.5)) (sub (m := m) (L 1.0) ef) el
  let h ← share (mul (m := m) (L 0.5) x)
  pure (sel (m := m) (lt (m := m) x (L 0.0)) (mul (m := m) h erfcA) (mul (m := m) h (add (m := m) (L 1.0) erfA)))
end

/-! ## The binary64 instance: the CPU reference -/

instance : Arith Id Float where
  Cond := Bool
  lit := id
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := fun x => -x
  abs := Float.abs
  floor := Float.floor
  fma := fun a b c => a * b + c
  lt := (· < ·)
  sel := fun c a b => if c then a else b
  ldexp := fun a n => if n.isNaN || n.isInf then a else a.scaleB n.toInt64.toInt
  frexpM := fun x => (Float.frExp x).1
  frexpE := fun x => Float.ofInt (Float.frExp x).2
  share := pure
  loop := fun n vs body => (List.range n).foldlM (fun acc k => body (Float.ofNat k) acc) vs
  maxFinite := 1.7976931348623157e308
  minNormal := 2.2250738585072014e-308
  expHi := 710.0
  expLo := -746.0

/-! ## The binary32 instance: a model of the GPU's evaluation, for measurement -/

instance : Arith Id Float32 where
  Cond := Bool
  lit := Float.toFloat32
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := fun x => -x
  abs := Float32.abs
  floor := Float32.floor
  fma := fun a b c => (a.toFloat * b.toFloat + c.toFloat).toFloat32
  lt := (· < ·)
  sel := fun c a b => if c then a else b
  ldexp := fun a n => if n.isNaN || n.isInf then a else a.scaleB n.toFloat.toInt64.toInt
  frexpM := fun x => (Float32.frExp x).1
  frexpE := fun x => (Float.ofInt (Float32.frExp x).2).toFloat32
  share := pure
  loop := fun n vs body => (List.range n).foldlM (fun acc k => body (Float.ofNat k).toFloat32 acc) vs
  maxFinite := 3.40282347e38
  minNormal := 1.17549435e-38
  expHi := 89.0
  expLo := -104.0

/-! ## The WGSL instance: the GPU kernels -/

open L4Factoidal.PageGpu

/-- Statements made so far (in order) and the next name. -/
abbrev Gen := StateM (Array Wgsl.Stmt × Nat)

/-- An `f32` literal: nine significant digits of the binary32 value (it reads back as that
value), a minus sign as negation. Only finite constants are written in these forms. -/
def sci9 (x : Float) : String := Id.run do
  let e0 := (Float.floor (Float.log10 x)).toInt64.toInt
  let scaled := fun (e : Int) => x * Float.pow 10.0 (Float.ofInt (8 - e))
  let mut e := e0
  let mut mm := (scaled e).round
  if mm ≥ 1000000000.0 then e := e + 1; mm := (scaled e).round
  if mm < 100000000.0 then e := e - 1; mm := (scaled e).round
  let d := (toString mm.toUInt64.toNat).toList
  return String.ofList (d.take 1) ++ "." ++ String.ofList (d.drop 1) ++ "e" ++ (if e < 0 then "-" ++ toString (-e) else toString e)

def flit (x : Float) : Wgsl.Expr :=
  let x := x.toFloat32.toFloat
  if x == 0.0 then .lit (.float "0.0") else
  let t := Wgsl.Expr.lit (.float (sci9 (if x < 0.0 then -x else x)))
  if x < 0.0 then .unary "-" t else t

def call1 (f : String) (a : Wgsl.Expr) : Wgsl.Expr := .call (.fn f) (.cons a .nil)
def f32of (a : Wgsl.Expr) : Wgsl.Expr := .call (.ty (.scalar .f32)) (.cons a .nil)

def emit (s : Wgsl.Stmt) : Gen Unit := modify fun (ss, n) => (ss.push s, n)
def freshName (p : String) : Gen String := modifyGet fun (ss, n) => (s!"{p}{n}", (ss, n + 1))

instance : Arith Gen Wgsl.Expr where
  Cond := Wgsl.Expr
  lit := flit
  add := .binary "+"
  sub := .binary "-"
  mul := .binary "*"
  div := .binary "/"
  neg := .unary "-"
  abs := call1 "abs"
  floor := call1 "floor"
  fma := fun a b c => .call (.fn "fma") (.cons a (.cons b (.cons c .nil)))
  lt := .binary "<"
  sel := fun c a b => .call (.fn "select") (.cons b (.cons a (.cons c .nil)))
  ldexp := fun a n => .call (.fn "ldexp") (.cons a (.cons (.call (.ty (.scalar .i32)) (.cons n .nil)) .nil))
  frexpM := fun x => .member (call1 "frexp" x) "fract"
  frexpE := fun x => f32of (.member (call1 "frexp" x) "exp")
  share := fun e => do
    let n ← freshName "v"
    emit (.letS n none e)
    pure (.name n)
  loop := fun n vs body => do
    let names ← vs.mapM fun v => do
      let nm ← freshName "w"
      emit (.varS nm none (some v))
      pure nm
    let t ← freshName "t"
    let (outer, k) ← get
    set ((#[] : Array Wgsl.Stmt), k)
    let res ← body (f32of (.name t)) (names.map .name)
    for (nm, r) in names.zip res do emit (.assign (.name nm) "" r)
    let (inner, k) ← get
    set (outer.push (.forS t .u32 0 n false (inner.foldr .cons .nil)), k)
    pure (names.map .name)
  maxFinite := 3.40282347e38
  minNormal := 1.17549435e-38
  expHi := 89.0
  expLo := -104.0

/-- The statements and the value of a function of the form at `x`, as WGSL. -/
def gen (f : Wgsl.Expr → Gen Wgsl.Expr) (x : Wgsl.Expr) (start : Nat := 0) : List Wgsl.Stmt × Wgsl.Expr :=
  let (v, (ss, _)) := (f x).run (#[], start)
  (ss.toList, v)

end L4Factoidal.WebNN.Approx
