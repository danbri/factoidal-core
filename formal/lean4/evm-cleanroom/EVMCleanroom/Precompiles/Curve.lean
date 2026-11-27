import EVMCleanroom.Precompiles.Field

/-!
# Short Weierstrass curves `y² = x³ + b` in Jacobian coordinates

One implementation over a `FieldOps` dictionary serves secp256k1, alt_bn128
(G1 and G2) and BLS12-381 (G1 and G2): all have `a = 0`.

A Jacobian point `(X, Y, Z)` stands for the affine point `(X/Z², Y/Z³)`; the
point at infinity is any triple with `Z = 0`. Formulas are the textbook
chord-and-tangent rules written in Jacobian form; the addition handles the
infinity, doubling and inverse cases explicitly.

Group laws are not proved. They are exercised by guards (generator order,
`[a]P + [b]P = [a+b]P`) and the published vectors of each precompile.
-/

namespace EVMCleanroom.Precompiles

structure JPoint (F : Type) where
  x : F
  y : F
  z : F

namespace Curve

variable {F : Type}

def infinity (O : FieldOps F) : JPoint F := ⟨O.one, O.one, O.zero⟩

@[inline] def isInfinity (O : FieldOps F) (p : JPoint F) : Bool := O.isZero p.z

def ofAffine (O : FieldOps F) (x y : F) : JPoint F := ⟨x, y, O.one⟩

/-- Is the affine pair on `y² = x³ + b`? -/
def onCurve (O : FieldOps F) (b x y : F) : Bool :=
  O.eq (O.sqr y) (O.add (O.mul (O.sqr x) x) b)

@[specialize] def double (O : FieldOps F) (p : JPoint F) : JPoint F :=
  let a := O.sqr p.x
  let b := O.sqr p.y
  let c := O.sqr b
  let xb := O.add p.x b
  let d0 := O.sub (O.sub (O.sqr xb) a) c
  let d := O.add d0 d0
  let e := O.add (O.add a a) a
  let x3 := O.sub (O.sqr e) (O.add d d)
  let c2 := O.add c c
  let c4 := O.add c2 c2
  let c8 := O.add c4 c4
  let y3 := O.sub (O.mul e (O.sub d x3)) c8
  let yz := O.mul p.y p.z
  ⟨x3, y3, O.add yz yz⟩

@[specialize] def add (O : FieldOps F) (p q : JPoint F) : JPoint F :=
  if O.isZero p.z then q
  else if O.isZero q.z then p
  else
    let z1z1 := O.sqr p.z
    let z2z2 := O.sqr q.z
    let u1 := O.mul p.x z2z2
    let u2 := O.mul q.x z1z1
    let s1 := O.mul (O.mul p.y q.z) z2z2
    let s2 := O.mul (O.mul q.y p.z) z1z1
    let h := O.sub u2 u1
    let r := O.sub s2 s1
    if O.isZero h then
      if O.isZero r then double O p else infinity O
    else
      let hh := O.sqr h
      let hhh := O.mul hh h
      let v := O.mul u1 hh
      let x3 := O.sub (O.sub (O.sqr r) hhh) (O.add v v)
      let y3 := O.sub (O.mul r (O.sub v x3)) (O.mul s1 hhh)
      ⟨x3, y3, O.mul (O.mul h p.z) q.z⟩

def neg (O : FieldOps F) (p : JPoint F) : JPoint F := ⟨p.x, O.neg p.y, p.z⟩

/-- Double-and-add over the low `bits` bits of `k`, most significant first. -/
@[specialize] def mulLoop (O : FieldOps F) (k : Nat) (p : JPoint F) : Nat → JPoint F → JPoint F
  | 0, acc => acc
  | bits+1, acc =>
    let doubled := double O acc
    mulLoop O k p bits (if k.testBit bits then add O doubled p else doubled)

/-- Scalar multiplication by any natural number (the loop length is its bit length). -/
def mul (O : FieldOps F) (k : Nat) (p : JPoint F) : JPoint F :=
  if k = 0 then infinity O else mulLoop O k p (Nat.log2 k + 1) (infinity O)

/-- Simultaneous double-and-add for `[k1]p1 + [k2]p2`; `p12` is `p1 + p2`. -/
@[specialize] def mul2Loop (O : FieldOps F) (k1 : Nat) (p1 : JPoint F) (k2 : Nat) (p2 p12 : JPoint F) :
    Nat → JPoint F → JPoint F
  | 0, acc => acc
  | bits+1, acc =>
    let doubled := double O acc
    let next :=
      match k1.testBit bits, k2.testBit bits with
      | true, true => add O doubled p12
      | true, false => add O doubled p1
      | false, true => add O doubled p2
      | false, false => doubled
    mul2Loop O k1 p1 k2 p2 p12 bits next

/-- `[k1]p1 + [k2]p2` with one shared doubling chain. -/
def mul2 (O : FieldOps F) (k1 : Nat) (p1 : JPoint F) (k2 : Nat) (p2 : JPoint F) : JPoint F :=
  mul2Loop O k1 p1 k2 p2 (add O p1 p2) (Nat.log2 (max k1 k2) + 1) (infinity O)

/-- Affine coordinates, `none` for the point at infinity. One field inversion. -/
def toAffine (O : FieldOps F) (p : JPoint F) : Option (F × F) :=
  if O.isZero p.z then none
  else
    let zi := O.inv p.z
    let zi2 := O.sqr zi
    some (O.mul p.x zi2, O.mul p.y (O.mul zi2 zi))

/-- Equality of the points represented, without inversion. -/
def same (O : FieldOps F) (p q : JPoint F) : Bool :=
  match O.isZero p.z, O.isZero q.z with
  | true, true => true
  | false, false =>
    let z1z1 := O.sqr p.z
    let z2z2 := O.sqr q.z
    O.eq (O.mul p.x z2z2) (O.mul q.x z1z1) &&
      O.eq (O.mul (O.mul p.y q.z) z2z2) (O.mul (O.mul q.y p.z) z1z1)
  | _, _ => false

/-- Kind: loop bound.
    Says: scalar multiplication by zero is the point at infinity without entering the loop;
    for other scalars the loop runs exactly `log2 k + 1` steps (by its definition).
    Does not say: the result is the group multiple. -/
theorem mul_zero (O : FieldOps F) (p : JPoint F) : mul O 0 p = infinity O := by
  simp [mul]

/-- Kind: identity handling.
    Says: adding the point at infinity on either side returns the other operand unchanged.
    Does not say: associativity or any other group law. -/
theorem add_infinity_left (O : FieldOps F) (p q : JPoint F) (h : O.isZero p.z = true) :
    add O p q = q := by
  simp [add, h]

theorem add_infinity_right (O : FieldOps F) (p q : JPoint F) (hp : O.isZero p.z = false)
    (hq : O.isZero q.z = true) : add O p q = p := by
  simp [add, hp, hq]

#print axioms mul_zero
#print axioms add_infinity_left
#print axioms add_infinity_right

end Curve

end EVMCleanroom.Precompiles
