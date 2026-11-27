import EVMCleanroom.Precompiles.Montgomery
import EVMCleanroom.Precompiles.FastTower

/-!
# The quadratic extension on flat limbs, with lazy reduction

`Quad256` and `Quad384` hold an element `re + im·u` of `Fp[u]/(u² + 1)` as eight or twelve
unboxed 64-bit limbs in one object, both coordinates in Montgomery form (`Mont256`,
`Mont384`). They are the `QuadOps` dictionaries the pairing tower is specialised on for
alt_bn128 and BLS12-381. Compared with the generic `Fq2 F` over a `FieldOps` dictionary:

* one allocation per result, where a pair of boxed coordinates takes three;
* conditional subtractions choose limb by limb with a mask (`sel`), so no intermediate
  field element is ever a heap object;
* **lazy reduction** in the product: the three double-width products of Karatsuba are
  combined before reduction, so a product costs two Montgomery reductions, not three
  (Aranha, Karabina, Longa, Gebotys and López, "Faster explicit formulas for computing
  pairings over ordinary curves", EUROCRYPT 2011, for the idea). The double-width
  differences stay inside what `redc` accepts because both moduli leave two spare bits:
  `4N < 2^256` and `4N < 2^384` (guards in the curve modules).

Generated from one template for the two widths (the rows of `redcRaw` are those of
`U256.redc` and `U384.redc` in `Limb.lean`, without the final conditional subtraction).

Proved here: only the representation facts (`mk2_re_im`, `re_im_mk2`). The arithmetic is
tested, not proved: every operation is compared with `Fp2` of `Field.lean` by build-time
guards in the curve modules and by `evm-pairingperf` on edge values and pseudo-random ones.

Nothing is constant-time by intent: the masks avoid allocation, not timing differences,
and `inv` goes through the variable-time `Fp.inv`.
-/

set_option linter.unusedVariables false

namespace EVMCleanroom.Precompiles

open Limb

/-- An element `re + im·u` of the quadratic extension of a 4-limb Montgomery field: 8 unboxed limbs in one object. -/
structure Quad256 where
  r0 : UInt64
  r1 : UInt64
  r2 : UInt64
  r3 : UInt64
  i0 : UInt64
  i1 : UInt64
  i2 : UInt64
  i3 : UInt64

namespace Quad256

@[inline] def re (x : Quad256) : U256 := ⟨x.r0, x.r1, x.r2, x.r3⟩
@[inline] def im (x : Quad256) : U256 := ⟨x.i0, x.i1, x.i2, x.i3⟩
@[inline] def mk2 (r i : U256) : Quad256 := ⟨r.l0, r.l1, r.l2, r.l3, i.l0, i.l1, i.l2, i.l3⟩

/-- All ones when the condition holds, else zero. -/
@[inline] def maskOf (c : Bool) : UInt64 := if c then 0xFFFFFFFFFFFFFFFF else 0

/-- Limb-wise choice: `x` for the all-ones mask, `y` for the zero mask. No branch on an object. -/
@[inline] def sel (m : UInt64) (x y : U256) : U256 :=
  let k := ~~~m
  ⟨(x.l0 &&& m) ||| (y.l0 &&& k), (x.l1 &&& m) ||| (y.l1 &&& k), (x.l2 &&& m) ||| (y.l2 &&& k), (x.l3 &&& m) ||| (y.l3 &&& k)⟩

@[inline] def andMask (m : UInt64) (x : U256) : U256 := ⟨x.l0 &&& m, x.l1 &&& m, x.l2 &&& m, x.l3 &&& m⟩

/-- `U256.condSub` by a mask: the value `e · 2^256 + a` minus `N` when it is at least `N`. -/
@[inline] def reduceOnce (N : U256) (e : UInt64) (a : U256) : U256 :=
  let d := U256.subBorrow a N
  sel (maskOf (e != 0 || d.1 == 0)) d.2 a

/-- Sum of two canonical residues. -/
@[inline] def addN (N a b : U256) : U256 :=
  let s := U256.addCarry a b
  reduceOnce N s.1 s.2

/-- Difference of two canonical residues. -/
@[inline] def subN (N a b : U256) : U256 :=
  let d := U256.subBorrow a b
  (U256.addCarry d.2 (andMask (maskOf (d.1 != 0)) N)).2

/-- Negation of a canonical residue. -/
@[inline] def negN (N a : U256) : U256 :=
  (U256.subBorrow (andMask (maskOf (!a.isZero)) N) a).2

/-- `(borrow, a − b)` on 8 limbs. -/
@[inline] def subW (a b : U512) : UInt64 × U512 :=
  let r := sbb a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := sbb a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := sbb a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := sbb a.l3 b.l3 c; let s3 := r.2; let c := r.1
  let r := sbb a.l4 b.l4 c; let s4 := r.2; let c := r.1
  let r := sbb a.l5 b.l5 c; let s5 := r.2; let c := r.1
  let r := sbb a.l6 b.l6 c; let s6 := r.2; let c := r.1
  let r := sbb a.l7 b.l7 c; let s7 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩)

/-- Add `x · 2^256`, dropping the carry out of the top limb. -/
@[inline] def addHigh (t : U512) (x : U256) : U512 :=
  let r := adc t.l4 x.l0 0; let s0 := r.2; let c := r.1
  let r := adc t.l5 x.l1 c; let s1 := r.2; let c := r.1
  let r := adc t.l6 x.l2 c; let s2 := r.2; let c := r.1
  let r := adc t.l7 x.l3 c; let s3 := r.2; let c := r.1
  ⟨t.l0, t.l1, t.l2, t.l3, s0, s1, s2, s3⟩

/-- The rows of `U256.redc` without its final conditional subtraction: `(e, a)` with
    `e · 2^256 + a = (t + m·N) / 2^256`, below `2N` for `t < N · 2^256`. -/
@[inline] def redcRaw (N : U256) (inv : UInt64) (t : U512) : UInt64 × U256 :=
  let t0 := t.l0
  let t1 := t.l1
  let t2 := t.l2
  let t3 := t.l3
  let t4 := t.l4
  let t5 := t.l5
  let t6 := t.l6
  let t7 := t.l7
  let e : UInt64 := 0
  let m := t0 * inv
  let r := mac m N.l0 t0 0; let t0 := r.2; let c := r.1
  let r := mac m N.l1 t1 c; let t1 := r.2; let c := r.1
  let r := mac m N.l2 t2 c; let t2 := r.2; let c := r.1
  let r := mac m N.l3 t3 c; let t3 := r.2; let c := r.1
  let r := adc t4 c e; let t4 := r.2; let e := r.1
  let m := t1 * inv
  let r := mac m N.l0 t1 0; let t1 := r.2; let c := r.1
  let r := mac m N.l1 t2 c; let t2 := r.2; let c := r.1
  let r := mac m N.l2 t3 c; let t3 := r.2; let c := r.1
  let r := mac m N.l3 t4 c; let t4 := r.2; let c := r.1
  let r := adc t5 c e; let t5 := r.2; let e := r.1
  let m := t2 * inv
  let r := mac m N.l0 t2 0; let t2 := r.2; let c := r.1
  let r := mac m N.l1 t3 c; let t3 := r.2; let c := r.1
  let r := mac m N.l2 t4 c; let t4 := r.2; let c := r.1
  let r := mac m N.l3 t5 c; let t5 := r.2; let c := r.1
  let r := adc t6 c e; let t6 := r.2; let e := r.1
  let m := t3 * inv
  let r := mac m N.l0 t3 0; let t3 := r.2; let c := r.1
  let r := mac m N.l1 t4 c; let t4 := r.2; let c := r.1
  let r := mac m N.l2 t5 c; let t5 := r.2; let c := r.1
  let r := mac m N.l3 t6 c; let t6 := r.2; let c := r.1
  let r := adc t7 c e; let t7 := r.2; let e := r.1
  (e, ⟨t4, t5, t6, t7⟩)

/-- Montgomery reduction of a value below `N · 2^256` to the canonical residue. -/
@[inline] def redcN (N : U256) (inv : UInt64) (t : U512) : U256 :=
  let r := redcRaw N inv t
  reduceOnce N r.1 r.2

def zero : Quad256 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
def one (M : Mont256) : Quad256 := mk2 M.one U256.zero

def add (M : Mont256) (x y : Quad256) : Quad256 := mk2 (addN M.n x.re y.re) (addN M.n x.im y.im)
def sub (M : Mont256) (x y : Quad256) : Quad256 := mk2 (subN M.n x.re y.re) (subN M.n x.im y.im)
def neg (M : Mont256) (x : Quad256) : Quad256 := mk2 (negN M.n x.re) (negN M.n x.im)
def double (M : Mont256) (x : Quad256) : Quad256 := mk2 (addN M.n x.re x.re) (addN M.n x.im x.im)
def conj (M : Mont256) (x : Quad256) : Quad256 := mk2 x.re (negN M.n x.im)

/-- Karatsuba with lazy reduction: three wide products, two Montgomery reductions.
    `re = redc(a₀b₀ − a₁b₁ + [N·R when negative])`, `im = redc((a₀+a₁)(b₀+b₁) − a₀b₀ − a₁b₁)`.
    Needs `2N < 2^256` so that the unreduced sums fit and both values are below `N·R`. -/
def mul (M : Mont256) (x y : Quad256) : Quad256 :=
  let N := M.n
  let v0 := U256.mulWide x.re y.re
  let v1 := U256.mulWide x.im y.im
  let d := subW v0 v1
  let c0 := redcN N M.n0inv (addHigh d.2 (andMask (maskOf (d.1 != 0)) N))
  let sa := (U256.addCarry x.re x.im).2
  let sb := (U256.addCarry y.re y.im).2
  let w := U256.mulWide sa sb
  let c1 := redcN N M.n0inv (subW (subW w v0).2 v1).2
  mk2 c0 c1

/-- `re = redc((a₀+a₁)(a₀+N−a₁))`, `im = redc(a₀·2a₁)`: two wide products, two reductions.
    Needs `4N < 2^256`. -/
def sqr (M : Mont256) (x : Quad256) : Quad256 :=
  let N := M.n
  let sa := (U256.addCarry x.re x.im).2
  let sd := (U256.addCarry x.re (negN N x.im)).2
  let d2 := (U256.addCarry x.im x.im).2
  mk2 (redcN N M.n0inv (U256.mulWide sa sd)) (redcN N M.n0inv (U256.mulWide x.re d2))

/-- Multiply both coordinates by the real part of `y`. -/
def mulReal (M : Mont256) (x y : Quad256) : Quad256 :=
  mk2 (redcN M.n M.n0inv (U256.mulWide x.re y.re)) (redcN M.n M.n0inv (U256.mulWide x.im y.re))

/-- Multiply by `ξ = 9 + u` (`nine`) or by `ξ = 1 + u`, by additions only. -/
def mulXi (M : Mont256) (nine : Bool) (x : Quad256) : Quad256 :=
  let N := M.n
  if nine then
    let x2 := addN N x.re x.re
    let x4 := addN N x2 x2
    let x8 := addN N x4 x4
    let y2 := addN N x.im x.im
    let y4 := addN N y2 y2
    let y8 := addN N y4 y4
    mk2 (subN N (addN N x8 x.re) x.im) (addN N (addN N y8 x.im) x.re)
  else mk2 (subN N x.re x.im) (addN N x.re x.im)

/-- Inverse through the norm: one base-field inversion. Zero maps to zero. -/
def inv (M : Mont256) (x : Quad256) : Quad256 :=
  let n := M.inv (M.add (M.sqr x.re) (M.sqr x.im))
  mk2 (M.mul x.re n) (M.neg (M.mul x.im n))

def isZero (x : Quad256) : Bool := (x.r0 ||| x.r1 ||| x.r2 ||| x.r3 ||| x.i0 ||| x.i1 ||| x.i2 ||| x.i3) == 0
def eq (x y : Quad256) : Bool :=
  ((x.r0 ^^^ y.r0) ||| (x.r1 ^^^ y.r1) ||| (x.r2 ^^^ y.r2) ||| (x.r3 ^^^ y.r3) ||| (x.i0 ^^^ y.i0) ||| (x.i1 ^^^ y.i1) ||| (x.i2 ^^^ y.i2) ||| (x.i3 ^^^ y.i3)) == 0

/-- From and to the `Nat` representation of `Field.lean`. -/
def ofFp2 (M : Mont256) (a : Fp2) : Quad256 := mk2 (M.ofNat a.c0) (M.ofNat a.c1)
def toFp2 (M : Mont256) (x : Quad256) : Fp2 := ⟨M.toNat x.re, M.toNat x.im⟩
/-- A base-field element as the real number `(a, 0)`. -/
def ofReal (a : U256) : Quad256 := mk2 a U256.zero

/-- The dictionary the tower is specialised on. -/
def ops (M : Mont256) (nine : Bool) : QuadOps Quad256 where
  zero := zero
  one := one M
  add := add M
  sub := sub M
  neg := neg M
  double := double M
  mul := mul M
  sqr := sqr M
  conj := conj M
  mulReal := mulReal M
  inv := inv M
  mulXi := mulXi M nine
  isZero := isZero
  eq := eq

/-- Kind: representation.
    Says: splitting into the two coordinates and joining them again is the identity, both ways.
    Does not say: anything about the arithmetic. -/
theorem mk2_re_im (x : Quad256) : mk2 x.re x.im = x := by cases x; rfl
theorem re_im_mk2 (r i : U256) : (mk2 r i).re = r ∧ (mk2 r i).im = i := by cases r; cases i; exact ⟨rfl, rfl⟩

#print axioms mk2_re_im
#print axioms re_im_mk2

end Quad256
/-- An element `re + im·u` of the quadratic extension of a 6-limb Montgomery field: 12 unboxed limbs in one object. -/
structure Quad384 where
  r0 : UInt64
  r1 : UInt64
  r2 : UInt64
  r3 : UInt64
  r4 : UInt64
  r5 : UInt64
  i0 : UInt64
  i1 : UInt64
  i2 : UInt64
  i3 : UInt64
  i4 : UInt64
  i5 : UInt64

namespace Quad384

@[inline] def re (x : Quad384) : U384 := ⟨x.r0, x.r1, x.r2, x.r3, x.r4, x.r5⟩
@[inline] def im (x : Quad384) : U384 := ⟨x.i0, x.i1, x.i2, x.i3, x.i4, x.i5⟩
@[inline] def mk2 (r i : U384) : Quad384 := ⟨r.l0, r.l1, r.l2, r.l3, r.l4, r.l5, i.l0, i.l1, i.l2, i.l3, i.l4, i.l5⟩

/-- All ones when the condition holds, else zero. -/
@[inline] def maskOf (c : Bool) : UInt64 := if c then 0xFFFFFFFFFFFFFFFF else 0

/-- Limb-wise choice: `x` for the all-ones mask, `y` for the zero mask. No branch on an object. -/
@[inline] def sel (m : UInt64) (x y : U384) : U384 :=
  let k := ~~~m
  ⟨(x.l0 &&& m) ||| (y.l0 &&& k), (x.l1 &&& m) ||| (y.l1 &&& k), (x.l2 &&& m) ||| (y.l2 &&& k), (x.l3 &&& m) ||| (y.l3 &&& k), (x.l4 &&& m) ||| (y.l4 &&& k), (x.l5 &&& m) ||| (y.l5 &&& k)⟩

@[inline] def andMask (m : UInt64) (x : U384) : U384 := ⟨x.l0 &&& m, x.l1 &&& m, x.l2 &&& m, x.l3 &&& m, x.l4 &&& m, x.l5 &&& m⟩

/-- `U384.condSub` by a mask: the value `e · 2^384 + a` minus `N` when it is at least `N`. -/
@[inline] def reduceOnce (N : U384) (e : UInt64) (a : U384) : U384 :=
  let d := U384.subBorrow a N
  sel (maskOf (e != 0 || d.1 == 0)) d.2 a

/-- Sum of two canonical residues. -/
@[inline] def addN (N a b : U384) : U384 :=
  let s := U384.addCarry a b
  reduceOnce N s.1 s.2

/-- Difference of two canonical residues. -/
@[inline] def subN (N a b : U384) : U384 :=
  let d := U384.subBorrow a b
  (U384.addCarry d.2 (andMask (maskOf (d.1 != 0)) N)).2

/-- Negation of a canonical residue. -/
@[inline] def negN (N a : U384) : U384 :=
  (U384.subBorrow (andMask (maskOf (!a.isZero)) N) a).2

/-- `(borrow, a − b)` on 12 limbs. -/
@[inline] def subW (a b : U768) : UInt64 × U768 :=
  let r := sbb a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := sbb a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := sbb a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := sbb a.l3 b.l3 c; let s3 := r.2; let c := r.1
  let r := sbb a.l4 b.l4 c; let s4 := r.2; let c := r.1
  let r := sbb a.l5 b.l5 c; let s5 := r.2; let c := r.1
  let r := sbb a.l6 b.l6 c; let s6 := r.2; let c := r.1
  let r := sbb a.l7 b.l7 c; let s7 := r.2; let c := r.1
  let r := sbb a.l8 b.l8 c; let s8 := r.2; let c := r.1
  let r := sbb a.l9 b.l9 c; let s9 := r.2; let c := r.1
  let r := sbb a.l10 b.l10 c; let s10 := r.2; let c := r.1
  let r := sbb a.l11 b.l11 c; let s11 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩)

/-- Add `x · 2^384`, dropping the carry out of the top limb. -/
@[inline] def addHigh (t : U768) (x : U384) : U768 :=
  let r := adc t.l6 x.l0 0; let s0 := r.2; let c := r.1
  let r := adc t.l7 x.l1 c; let s1 := r.2; let c := r.1
  let r := adc t.l8 x.l2 c; let s2 := r.2; let c := r.1
  let r := adc t.l9 x.l3 c; let s3 := r.2; let c := r.1
  let r := adc t.l10 x.l4 c; let s4 := r.2; let c := r.1
  let r := adc t.l11 x.l5 c; let s5 := r.2; let c := r.1
  ⟨t.l0, t.l1, t.l2, t.l3, t.l4, t.l5, s0, s1, s2, s3, s4, s5⟩

/-- The rows of `U384.redc` without its final conditional subtraction: `(e, a)` with
    `e · 2^384 + a = (t + m·N) / 2^384`, below `2N` for `t < N · 2^384`. -/
@[inline] def redcRaw (N : U384) (inv : UInt64) (t : U768) : UInt64 × U384 :=
  let t0 := t.l0
  let t1 := t.l1
  let t2 := t.l2
  let t3 := t.l3
  let t4 := t.l4
  let t5 := t.l5
  let t6 := t.l6
  let t7 := t.l7
  let t8 := t.l8
  let t9 := t.l9
  let t10 := t.l10
  let t11 := t.l11
  let e : UInt64 := 0
  let m := t0 * inv
  let r := mac m N.l0 t0 0; let t0 := r.2; let c := r.1
  let r := mac m N.l1 t1 c; let t1 := r.2; let c := r.1
  let r := mac m N.l2 t2 c; let t2 := r.2; let c := r.1
  let r := mac m N.l3 t3 c; let t3 := r.2; let c := r.1
  let r := mac m N.l4 t4 c; let t4 := r.2; let c := r.1
  let r := mac m N.l5 t5 c; let t5 := r.2; let c := r.1
  let r := adc t6 c e; let t6 := r.2; let e := r.1
  let m := t1 * inv
  let r := mac m N.l0 t1 0; let t1 := r.2; let c := r.1
  let r := mac m N.l1 t2 c; let t2 := r.2; let c := r.1
  let r := mac m N.l2 t3 c; let t3 := r.2; let c := r.1
  let r := mac m N.l3 t4 c; let t4 := r.2; let c := r.1
  let r := mac m N.l4 t5 c; let t5 := r.2; let c := r.1
  let r := mac m N.l5 t6 c; let t6 := r.2; let c := r.1
  let r := adc t7 c e; let t7 := r.2; let e := r.1
  let m := t2 * inv
  let r := mac m N.l0 t2 0; let t2 := r.2; let c := r.1
  let r := mac m N.l1 t3 c; let t3 := r.2; let c := r.1
  let r := mac m N.l2 t4 c; let t4 := r.2; let c := r.1
  let r := mac m N.l3 t5 c; let t5 := r.2; let c := r.1
  let r := mac m N.l4 t6 c; let t6 := r.2; let c := r.1
  let r := mac m N.l5 t7 c; let t7 := r.2; let c := r.1
  let r := adc t8 c e; let t8 := r.2; let e := r.1
  let m := t3 * inv
  let r := mac m N.l0 t3 0; let t3 := r.2; let c := r.1
  let r := mac m N.l1 t4 c; let t4 := r.2; let c := r.1
  let r := mac m N.l2 t5 c; let t5 := r.2; let c := r.1
  let r := mac m N.l3 t6 c; let t6 := r.2; let c := r.1
  let r := mac m N.l4 t7 c; let t7 := r.2; let c := r.1
  let r := mac m N.l5 t8 c; let t8 := r.2; let c := r.1
  let r := adc t9 c e; let t9 := r.2; let e := r.1
  let m := t4 * inv
  let r := mac m N.l0 t4 0; let t4 := r.2; let c := r.1
  let r := mac m N.l1 t5 c; let t5 := r.2; let c := r.1
  let r := mac m N.l2 t6 c; let t6 := r.2; let c := r.1
  let r := mac m N.l3 t7 c; let t7 := r.2; let c := r.1
  let r := mac m N.l4 t8 c; let t8 := r.2; let c := r.1
  let r := mac m N.l5 t9 c; let t9 := r.2; let c := r.1
  let r := adc t10 c e; let t10 := r.2; let e := r.1
  let m := t5 * inv
  let r := mac m N.l0 t5 0; let t5 := r.2; let c := r.1
  let r := mac m N.l1 t6 c; let t6 := r.2; let c := r.1
  let r := mac m N.l2 t7 c; let t7 := r.2; let c := r.1
  let r := mac m N.l3 t8 c; let t8 := r.2; let c := r.1
  let r := mac m N.l4 t9 c; let t9 := r.2; let c := r.1
  let r := mac m N.l5 t10 c; let t10 := r.2; let c := r.1
  let r := adc t11 c e; let t11 := r.2; let e := r.1
  (e, ⟨t6, t7, t8, t9, t10, t11⟩)

/-- Montgomery reduction of a value below `N · 2^384` to the canonical residue. -/
@[inline] def redcN (N : U384) (inv : UInt64) (t : U768) : U384 :=
  let r := redcRaw N inv t
  reduceOnce N r.1 r.2

def zero : Quad384 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def one (M : Mont384) : Quad384 := mk2 M.one U384.zero

def add (M : Mont384) (x y : Quad384) : Quad384 := mk2 (addN M.n x.re y.re) (addN M.n x.im y.im)
def sub (M : Mont384) (x y : Quad384) : Quad384 := mk2 (subN M.n x.re y.re) (subN M.n x.im y.im)
def neg (M : Mont384) (x : Quad384) : Quad384 := mk2 (negN M.n x.re) (negN M.n x.im)
def double (M : Mont384) (x : Quad384) : Quad384 := mk2 (addN M.n x.re x.re) (addN M.n x.im x.im)
def conj (M : Mont384) (x : Quad384) : Quad384 := mk2 x.re (negN M.n x.im)

/-- Karatsuba with lazy reduction: three wide products, two Montgomery reductions.
    `re = redc(a₀b₀ − a₁b₁ + [N·R when negative])`, `im = redc((a₀+a₁)(b₀+b₁) − a₀b₀ − a₁b₁)`.
    Needs `2N < 2^384` so that the unreduced sums fit and both values are below `N·R`. -/
def mul (M : Mont384) (x y : Quad384) : Quad384 :=
  let N := M.n
  let v0 := U384.mulWide x.re y.re
  let v1 := U384.mulWide x.im y.im
  let d := subW v0 v1
  let c0 := redcN N M.n0inv (addHigh d.2 (andMask (maskOf (d.1 != 0)) N))
  let sa := (U384.addCarry x.re x.im).2
  let sb := (U384.addCarry y.re y.im).2
  let w := U384.mulWide sa sb
  let c1 := redcN N M.n0inv (subW (subW w v0).2 v1).2
  mk2 c0 c1

/-- `re = redc((a₀+a₁)(a₀+N−a₁))`, `im = redc(a₀·2a₁)`: two wide products, two reductions.
    Needs `4N < 2^384`. -/
def sqr (M : Mont384) (x : Quad384) : Quad384 :=
  let N := M.n
  let sa := (U384.addCarry x.re x.im).2
  let sd := (U384.addCarry x.re (negN N x.im)).2
  let d2 := (U384.addCarry x.im x.im).2
  mk2 (redcN N M.n0inv (U384.mulWide sa sd)) (redcN N M.n0inv (U384.mulWide x.re d2))

/-- Multiply both coordinates by the real part of `y`. -/
def mulReal (M : Mont384) (x y : Quad384) : Quad384 :=
  mk2 (redcN M.n M.n0inv (U384.mulWide x.re y.re)) (redcN M.n M.n0inv (U384.mulWide x.im y.re))

/-- Multiply by `ξ = 9 + u` (`nine`) or by `ξ = 1 + u`, by additions only. -/
def mulXi (M : Mont384) (nine : Bool) (x : Quad384) : Quad384 :=
  let N := M.n
  if nine then
    let x2 := addN N x.re x.re
    let x4 := addN N x2 x2
    let x8 := addN N x4 x4
    let y2 := addN N x.im x.im
    let y4 := addN N y2 y2
    let y8 := addN N y4 y4
    mk2 (subN N (addN N x8 x.re) x.im) (addN N (addN N y8 x.im) x.re)
  else mk2 (subN N x.re x.im) (addN N x.re x.im)

/-- Inverse through the norm: one base-field inversion. Zero maps to zero. -/
def inv (M : Mont384) (x : Quad384) : Quad384 :=
  let n := M.inv (M.add (M.sqr x.re) (M.sqr x.im))
  mk2 (M.mul x.re n) (M.neg (M.mul x.im n))

def isZero (x : Quad384) : Bool := (x.r0 ||| x.r1 ||| x.r2 ||| x.r3 ||| x.r4 ||| x.r5 ||| x.i0 ||| x.i1 ||| x.i2 ||| x.i3 ||| x.i4 ||| x.i5) == 0
def eq (x y : Quad384) : Bool :=
  ((x.r0 ^^^ y.r0) ||| (x.r1 ^^^ y.r1) ||| (x.r2 ^^^ y.r2) ||| (x.r3 ^^^ y.r3) ||| (x.r4 ^^^ y.r4) ||| (x.r5 ^^^ y.r5) ||| (x.i0 ^^^ y.i0) ||| (x.i1 ^^^ y.i1) ||| (x.i2 ^^^ y.i2) ||| (x.i3 ^^^ y.i3) ||| (x.i4 ^^^ y.i4) ||| (x.i5 ^^^ y.i5)) == 0

/-- From and to the `Nat` representation of `Field.lean`. -/
def ofFp2 (M : Mont384) (a : Fp2) : Quad384 := mk2 (M.ofNat a.c0) (M.ofNat a.c1)
def toFp2 (M : Mont384) (x : Quad384) : Fp2 := ⟨M.toNat x.re, M.toNat x.im⟩
/-- A base-field element as the real number `(a, 0)`. -/
def ofReal (a : U384) : Quad384 := mk2 a U384.zero

/-- The dictionary the tower is specialised on. -/
def ops (M : Mont384) (nine : Bool) : QuadOps Quad384 where
  zero := zero
  one := one M
  add := add M
  sub := sub M
  neg := neg M
  double := double M
  mul := mul M
  sqr := sqr M
  conj := conj M
  mulReal := mulReal M
  inv := inv M
  mulXi := mulXi M nine
  isZero := isZero
  eq := eq

/-- Kind: representation.
    Says: splitting into the two coordinates and joining them again is the identity, both ways.
    Does not say: anything about the arithmetic. -/
theorem mk2_re_im (x : Quad384) : mk2 x.re x.im = x := by cases x; rfl
theorem re_im_mk2 (r i : U384) : (mk2 r i).re = r ∧ (mk2 r i).im = i := by cases r; cases i; exact ⟨rfl, rfl⟩

#print axioms mk2_re_im
#print axioms re_im_mk2

end Quad384
end EVMCleanroom.Precompiles
