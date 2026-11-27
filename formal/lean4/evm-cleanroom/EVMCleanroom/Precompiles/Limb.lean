/-!
# Fixed-width limbs: the primitive steps

Field elements of the curve precompiles are kept in 64-bit limbs (`UInt64`),
least significant first: four limbs for the 256-bit fields, six for the
381-bit field. Compiled Lean keeps a `UInt64` unboxed, so a field operation
is a short run of machine arithmetic and one small allocation for the result,
where the `Nat` path pays an allocation and a call into the big-number
library for every intermediate value.

Lean has no primitive for the high half of a 64-bit product, so `mac` builds
the 128-bit product from four 32-bit by 32-bit products. Halves are taken with
`%` and `/` by `2^32` (compiled to a mask and a shift), which keeps the
statements about them linear.

This module imports nothing. The specifications of these steps on natural
numbers are proved in `LimbProofs.lean`.
-/

set_option linter.unusedVariables false

namespace EVMCleanroom.Precompiles

namespace Limb

/-- `2^32`. -/
@[inline] def half : UInt64 := 4294967296

/-- `(high, low)` of `a * b + c + d`, which always fits in 128 bits. -/
@[inline] def mac (a b c d : UInt64) : UInt64 × UInt64 :=
  let a0 := a % half
  let a1 := a / half
  let b0 := b % half
  let b1 := b / half
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := p00 / half + p01 % half + p10 % half
  let lo0 := p00 % half + mid * half
  let hi0 := p11 + p01 / half + p10 / half + mid / half
  let lo1 := lo0 + c
  let hi1 := hi0 + (if lo1 < lo0 then 1 else 0)
  let lo2 := lo1 + d
  let hi2 := hi1 + (if lo2 < lo1 then 1 else 0)
  (hi2, lo2)

/-- `(carry, low)` of `a + b + c`; the carry is 0, 1 or 2 (2 only when `c` is large). -/
@[inline] def adc (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a + b
  let c1 : UInt64 := if s < a then 1 else 0
  let t := s + c
  let c2 : UInt64 := if t < s then 1 else 0
  (c1 + c2, t)

/-- `(borrow, low)` of `a - b - c`. -/
@[inline] def sbb (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a - b
  let c1 : UInt64 := if a < b then 1 else 0
  let t := s - c
  let c2 : UInt64 := if s < c then 1 else 0
  (c1 + c2, t)

end Limb

open Limb

/-- Four limbs, least significant first. -/
structure U256 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64

/-- Eight limbs: a product of two `U256` values before reduction. -/
structure U512 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64

/-- Six limbs, least significant first. -/
structure U384 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64

/-- Twelve limbs: a product of two `U384` values before reduction. -/
structure U768 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  l9 : UInt64
  l10 : UInt64
  l11 : UInt64

def U256.toNat (a : U256) : Nat :=
  a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192

def U512.toNat (a : U512) : Nat :=
  a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192 +
    a.l4.toNat * 2 ^ 256 + a.l5.toNat * 2 ^ 320 + a.l6.toNat * 2 ^ 384 + a.l7.toNat * 2 ^ 448

def U384.toNat (a : U384) : Nat :=
  a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192 +
    a.l4.toNat * 2 ^ 256 + a.l5.toNat * 2 ^ 320

def U768.toNat (a : U768) : Nat :=
  a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192 +
    a.l4.toNat * 2 ^ 256 + a.l5.toNat * 2 ^ 320 + a.l6.toNat * 2 ^ 384 + a.l7.toNat * 2 ^ 448 +
    a.l8.toNat * 2 ^ 512 + a.l9.toNat * 2 ^ 576 + a.l10.toNat * 2 ^ 640 + a.l11.toNat * 2 ^ 704

/-- The low 256 bits of a natural number. -/
def U256.ofNat (n : Nat) : U256 :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64⟩

/-- The low 384 bits of a natural number. -/
def U384.ofNat (n : Nat) : U384 :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64,
   (n >>> 256).toUInt64, (n >>> 320).toUInt64⟩

@[inline] def U256.zero : U256 := ⟨0, 0, 0, 0⟩
@[inline] def U384.zero : U384 := ⟨0, 0, 0, 0, 0, 0⟩

/-- A four-limb value as the low half of an eight-limb one. -/
@[inline] def U256.widen (a : U256) : U512 := ⟨a.l0, a.l1, a.l2, a.l3, 0, 0, 0, 0⟩
@[inline] def U384.widen (a : U384) : U768 := ⟨a.l0, a.l1, a.l2, a.l3, a.l4, a.l5, 0, 0, 0, 0, 0, 0⟩

/-! ### Four limbs -/

/-- `(borrow, a - b)` on 4 limbs. -/
@[inline] def U256.subBorrow (a b : U256) : UInt64 × U256 :=
  let r := sbb a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := sbb a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := sbb a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := sbb a.l3 b.l3 c; let s3 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3⟩)

/-- `(carry, a + b)` on 4 limbs. -/
@[inline] def U256.addCarry (a b : U256) : UInt64 × U256 :=
  let r := adc a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := adc a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := adc a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := adc a.l3 b.l3 c; let s3 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3⟩)

/-- The value `e · 2^256 + a` reduced once: subtract `N` when it is at least `N`.
    For a value below `2N` the result is the canonical residue. -/
@[inline] def U256.condSub (N : U256) (e : UInt64) (a : U256) : U256 :=
  let r := U256.subBorrow a N
  if e != 0 || r.1 == 0 then r.2 else a

/-- Sum of two canonical residues modulo `N`. -/
@[inline] def U256.addMod (N a b : U256) : U256 :=
  let r := U256.addCarry a b
  U256.condSub N r.1 r.2

/-- Difference of two canonical residues modulo `N`. -/
@[inline] def U256.subMod (N a b : U256) : U256 :=
  let r := U256.subBorrow a b
  if r.1 != 0 then (U256.addCarry r.2 N).2 else r.2

@[inline] def U256.isZero (a : U256) : Bool := (a.l0 ||| a.l1 ||| a.l2 ||| a.l3) == 0

@[inline] def U256.beq (a b : U256) : Bool :=
  ((a.l0 ^^^ b.l0) ||| (a.l1 ^^^ b.l1) ||| (a.l2 ^^^ b.l2) ||| (a.l3 ^^^ b.l3)) == 0

/-- Negation of a canonical residue modulo `N`. -/
@[inline] def U256.negMod (N a : U256) : U256 := if a.isZero then a else (U256.subBorrow N a).2

/-- The full product, 8 limbs: schoolbook rows, one `mac` per limb pair. -/
@[inline] def U256.mulWide (a b : U256) : U512 :=
  let r := mac a.l0 b.l0 0 0; let t0 := r.2; let c := r.1
  let r := mac a.l0 b.l1 0 c; let t1 := r.2; let c := r.1
  let r := mac a.l0 b.l2 0 c; let t2 := r.2; let c := r.1
  let r := mac a.l0 b.l3 0 c; let t3 := r.2; let t4 := r.1
  let r := mac a.l1 b.l0 t1 0; let t1 := r.2; let c := r.1
  let r := mac a.l1 b.l1 t2 c; let t2 := r.2; let c := r.1
  let r := mac a.l1 b.l2 t3 c; let t3 := r.2; let c := r.1
  let r := mac a.l1 b.l3 t4 c; let t4 := r.2; let t5 := r.1
  let r := mac a.l2 b.l0 t2 0; let t2 := r.2; let c := r.1
  let r := mac a.l2 b.l1 t3 c; let t3 := r.2; let c := r.1
  let r := mac a.l2 b.l2 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l2 b.l3 t5 c; let t5 := r.2; let t6 := r.1
  let r := mac a.l3 b.l0 t3 0; let t3 := r.2; let c := r.1
  let r := mac a.l3 b.l1 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l3 b.l2 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l3 b.l3 t6 c; let t6 := r.2; let t7 := r.1
  ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩

/-- Montgomery reduction of a 8-limb value below `N · 2^256`: `4` rows, each clearing one
    low limb by adding a multiple of the modulus; then one conditional subtraction. -/
@[inline] def U256.redc (N : U256) (inv : UInt64) (t : U512) : U256 :=
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
  U256.condSub N e ⟨t4, t5, t6, t7⟩

/-! ### Six limbs -/

/-- `(borrow, a - b)` on 6 limbs. -/
@[inline] def U384.subBorrow (a b : U384) : UInt64 × U384 :=
  let r := sbb a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := sbb a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := sbb a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := sbb a.l3 b.l3 c; let s3 := r.2; let c := r.1
  let r := sbb a.l4 b.l4 c; let s4 := r.2; let c := r.1
  let r := sbb a.l5 b.l5 c; let s5 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3, s4, s5⟩)

/-- `(carry, a + b)` on 6 limbs. -/
@[inline] def U384.addCarry (a b : U384) : UInt64 × U384 :=
  let r := adc a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := adc a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := adc a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := adc a.l3 b.l3 c; let s3 := r.2; let c := r.1
  let r := adc a.l4 b.l4 c; let s4 := r.2; let c := r.1
  let r := adc a.l5 b.l5 c; let s5 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3, s4, s5⟩)

/-- The value `e · 2^384 + a` reduced once: subtract `N` when it is at least `N`.
    For a value below `2N` the result is the canonical residue. -/
@[inline] def U384.condSub (N : U384) (e : UInt64) (a : U384) : U384 :=
  let r := U384.subBorrow a N
  if e != 0 || r.1 == 0 then r.2 else a

/-- Sum of two canonical residues modulo `N`. -/
@[inline] def U384.addMod (N a b : U384) : U384 :=
  let r := U384.addCarry a b
  U384.condSub N r.1 r.2

/-- Difference of two canonical residues modulo `N`. -/
@[inline] def U384.subMod (N a b : U384) : U384 :=
  let r := U384.subBorrow a b
  if r.1 != 0 then (U384.addCarry r.2 N).2 else r.2

@[inline] def U384.isZero (a : U384) : Bool := (a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) == 0

@[inline] def U384.beq (a b : U384) : Bool :=
  ((a.l0 ^^^ b.l0) ||| (a.l1 ^^^ b.l1) ||| (a.l2 ^^^ b.l2) ||| (a.l3 ^^^ b.l3) ||| (a.l4 ^^^ b.l4) ||| (a.l5 ^^^ b.l5)) == 0

/-- Negation of a canonical residue modulo `N`. -/
@[inline] def U384.negMod (N a : U384) : U384 := if a.isZero then a else (U384.subBorrow N a).2

/-- The full product, 12 limbs: schoolbook rows, one `mac` per limb pair. -/
@[inline] def U384.mulWide (a b : U384) : U768 :=
  let r := mac a.l0 b.l0 0 0; let t0 := r.2; let c := r.1
  let r := mac a.l0 b.l1 0 c; let t1 := r.2; let c := r.1
  let r := mac a.l0 b.l2 0 c; let t2 := r.2; let c := r.1
  let r := mac a.l0 b.l3 0 c; let t3 := r.2; let c := r.1
  let r := mac a.l0 b.l4 0 c; let t4 := r.2; let c := r.1
  let r := mac a.l0 b.l5 0 c; let t5 := r.2; let t6 := r.1
  let r := mac a.l1 b.l0 t1 0; let t1 := r.2; let c := r.1
  let r := mac a.l1 b.l1 t2 c; let t2 := r.2; let c := r.1
  let r := mac a.l1 b.l2 t3 c; let t3 := r.2; let c := r.1
  let r := mac a.l1 b.l3 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l1 b.l4 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l1 b.l5 t6 c; let t6 := r.2; let t7 := r.1
  let r := mac a.l2 b.l0 t2 0; let t2 := r.2; let c := r.1
  let r := mac a.l2 b.l1 t3 c; let t3 := r.2; let c := r.1
  let r := mac a.l2 b.l2 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l2 b.l3 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l2 b.l4 t6 c; let t6 := r.2; let c := r.1
  let r := mac a.l2 b.l5 t7 c; let t7 := r.2; let t8 := r.1
  let r := mac a.l3 b.l0 t3 0; let t3 := r.2; let c := r.1
  let r := mac a.l3 b.l1 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l3 b.l2 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l3 b.l3 t6 c; let t6 := r.2; let c := r.1
  let r := mac a.l3 b.l4 t7 c; let t7 := r.2; let c := r.1
  let r := mac a.l3 b.l5 t8 c; let t8 := r.2; let t9 := r.1
  let r := mac a.l4 b.l0 t4 0; let t4 := r.2; let c := r.1
  let r := mac a.l4 b.l1 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l4 b.l2 t6 c; let t6 := r.2; let c := r.1
  let r := mac a.l4 b.l3 t7 c; let t7 := r.2; let c := r.1
  let r := mac a.l4 b.l4 t8 c; let t8 := r.2; let c := r.1
  let r := mac a.l4 b.l5 t9 c; let t9 := r.2; let t10 := r.1
  let r := mac a.l5 b.l0 t5 0; let t5 := r.2; let c := r.1
  let r := mac a.l5 b.l1 t6 c; let t6 := r.2; let c := r.1
  let r := mac a.l5 b.l2 t7 c; let t7 := r.2; let c := r.1
  let r := mac a.l5 b.l3 t8 c; let t8 := r.2; let c := r.1
  let r := mac a.l5 b.l4 t9 c; let t9 := r.2; let c := r.1
  let r := mac a.l5 b.l5 t10 c; let t10 := r.2; let t11 := r.1
  ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩

/-- Montgomery reduction of a 12-limb value below `N · 2^384`: `6` rows, each clearing one
    low limb by adding a multiple of the modulus; then one conditional subtraction. -/
@[inline] def U384.redc (N : U384) (inv : UInt64) (t : U768) : U384 :=
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
  U384.condSub N e ⟨t6, t7, t8, t9, t10, t11⟩

end EVMCleanroom.Precompiles
