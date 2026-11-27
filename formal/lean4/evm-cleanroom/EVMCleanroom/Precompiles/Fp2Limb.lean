import EVMCleanroom.Precompiles.Field

/-!
# The quadratic extension `F[u]/(u² + 1)` over any base field dictionary

`Q2 F` is a pair of base-field elements; with the limb fields of
`Montgomery.lean` as the base it is the `Fp2` of BLS12-381 `G2` on limbs.
Multiplication is Karatsuba's (three base multiplications), squaring uses
`(a + b)(a − b)` and `2ab` (two), the inverse goes through the norm
`a² + b²` (one base inversion).

This is the small extension the group-operation precompiles need. The pairing
work has its own limb tower; the two should be unified at integration.

Nothing is proved here: the operations are compared with `Fp2` of
`Field.lean` by the guards of `BLS12381Fast.lean` and the differential runs
of `evm-blsops`. Nothing is constant-time.
-/

namespace EVMCleanroom.Precompiles

/-- An element `c0 + c1·u` with `u² = −1`. -/
structure Q2 (F : Type) where
  c0 : F
  c1 : F

namespace Q2

variable {F : Type}

@[inline] def add (O : FieldOps F) (a b : Q2 F) : Q2 F := ⟨O.add a.c0 b.c0, O.add a.c1 b.c1⟩
@[inline] def sub (O : FieldOps F) (a b : Q2 F) : Q2 F := ⟨O.sub a.c0 b.c0, O.sub a.c1 b.c1⟩
@[inline] def neg (O : FieldOps F) (a : Q2 F) : Q2 F := ⟨O.neg a.c0, O.neg a.c1⟩
@[inline] def conj (O : FieldOps F) (a : Q2 F) : Q2 F := ⟨a.c0, O.neg a.c1⟩
@[inline] def isZero (O : FieldOps F) (a : Q2 F) : Bool := O.isZero a.c0 && O.isZero a.c1
@[inline] def eq (O : FieldOps F) (a b : Q2 F) : Bool := O.eq a.c0 b.c0 && O.eq a.c1 b.c1

/-- Karatsuba: `(a0 b0 − a1 b1) + ((a0 + a1)(b0 + b1) − a0 b0 − a1 b1) u`. -/
@[inline] def mul (O : FieldOps F) (a b : Q2 F) : Q2 F :=
  let v0 := O.mul a.c0 b.c0
  let v1 := O.mul a.c1 b.c1
  ⟨O.sub v0 v1, O.sub (O.sub (O.mul (O.add a.c0 a.c1) (O.add b.c0 b.c1)) v0) v1⟩

/-- `(a0 + a1)(a0 − a1) + 2 a0 a1 u`. -/
@[inline] def sqr (O : FieldOps F) (a : Q2 F) : Q2 F :=
  let t := O.mul a.c0 a.c1
  ⟨O.mul (O.add a.c0 a.c1) (O.sub a.c0 a.c1), O.add t t⟩

/-- Multiplication by a base-field element. -/
@[inline] def scale (O : FieldOps F) (k : F) (a : Q2 F) : Q2 F := ⟨O.mul k a.c0, O.mul k a.c1⟩

/-- Inverse through the norm; zero maps to zero. -/
@[inline] def inv (O : FieldOps F) (a : Q2 F) : Q2 F :=
  let n := O.inv (O.add (O.sqr a.c0) (O.sqr a.c1))
  ⟨O.mul a.c0 n, O.neg (O.mul a.c1 n)⟩

/-- The dictionary of the extension over the dictionary of the base field. -/
def ops (O : FieldOps F) : FieldOps (Q2 F) where
  zero := ⟨O.zero, O.zero⟩
  one := ⟨O.one, O.zero⟩
  add := add O
  sub := sub O
  mul := mul O
  sqr := sqr O
  neg := neg O
  inv := inv O
  isZero := isZero O
  eq := eq O

end Q2

-- Over the `Nat` field of 19 elements the extension agrees with `Fp2`.
private def o19 : FieldOps Nat := Fp.ops 19
private def toFp2 (a : Q2 Nat) : Fp2 := ⟨a.c0, a.c1⟩
#guard toFp2 (Q2.mul o19 ⟨3, 7⟩ ⟨11, 18⟩) == Fp2.mul 19 ⟨3, 7⟩ ⟨11, 18⟩
#guard toFp2 (Q2.sqr o19 ⟨3, 7⟩) == Fp2.sqr 19 ⟨3, 7⟩ && toFp2 (Q2.sqr o19 ⟨0, 7⟩) == Fp2.sqr 19 ⟨0, 7⟩
#guard toFp2 (Q2.inv o19 ⟨3, 7⟩) == Fp2.inv 19 ⟨3, 7⟩ && toFp2 (Q2.inv o19 ⟨0, 0⟩) == Fp2.zero
#guard toFp2 (Q2.mul o19 (Q2.inv o19 ⟨5, 13⟩) ⟨5, 13⟩) == Fp2.one
#guard toFp2 (Q2.sub o19 ⟨3, 7⟩ ⟨11, 18⟩) == Fp2.sub 19 ⟨3, 7⟩ ⟨11, 18⟩ && toFp2 (Q2.neg o19 ⟨0, 7⟩) == Fp2.neg 19 ⟨0, 7⟩

end EVMCleanroom.Precompiles
