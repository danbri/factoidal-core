import EVMCleanroom.Precompiles.Secp256k1Glv

/-!
# secp256k1 points on limbs: formulas and tables of the fast paths

Part of the fast paths for public data (`Secp256k1Fast.lean`, which has the overview).

A point is twelve 64-bit limbs in one object (Jacobian `X, Y, Z`; infinity is `Z = 0`), and
each formula is compiled as one function with the field operations of `Secp256k1FieldFast`
inlined. Formulas: Jacobian doubling for `a = 0` with `S = 4·X·Y²` and `M = 3·X²` (Cohen,
Miyaji and Ono, "Efficient elliptic curve exponentiation using mixed coordinates", 1998),
chord addition and mixed addition in the same coordinates; infinity, equal points and
opposite points are explicit branches.

Nothing here is proved; the functions are tested through `Secp256k1Fast` (guards, the
differential run of `evm-secpperf`, the ECRECOVER vectors). Variable-time: the special
cases of the additions are branches. Public data only.
-/

namespace EVMCleanroom.Precompiles.Secp256k1.Fast


/-! ### Points: twelve limbs in one object -/

/-- A Jacobian point `(X, Y, Z)`; infinity is `Z = 0`. -/
structure Pt where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  y0 : UInt64
  y1 : UInt64
  y2 : UInt64
  y3 : UInt64
  z0 : UInt64
  z1 : UInt64
  z2 : UInt64
  z3 : UInt64

/-- An affine point. -/
structure Aff where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  y0 : UInt64
  y1 : UInt64
  y2 : UInt64
  y3 : UInt64

@[inline] def Pt.x (p : Pt) : U256 := ⟨p.x0, p.x1, p.x2, p.x3⟩
@[inline] def Pt.y (p : Pt) : U256 := ⟨p.y0, p.y1, p.y2, p.y3⟩
@[inline] def Pt.z (p : Pt) : U256 := ⟨p.z0, p.z1, p.z2, p.z3⟩
@[inline] def Pt.ofXYZ (x y z : U256) : Pt :=
  ⟨x.l0, x.l1, x.l2, x.l3, y.l0, y.l1, y.l2, y.l3, z.l0, z.l1, z.l2, z.l3⟩
@[inline] def Aff.x (p : Aff) : U256 := ⟨p.x0, p.x1, p.x2, p.x3⟩
@[inline] def Aff.y (p : Aff) : U256 := ⟨p.y0, p.y1, p.y2, p.y3⟩
@[inline] def Aff.ofXY (x y : U256) : Aff := ⟨x.l0, x.l1, x.l2, x.l3, y.l0, y.l1, y.l2, y.l3⟩

def infinity : Pt := ⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩
def affZero : Aff := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
@[inline] def Pt.isInfinity (p : Pt) : Bool := (p.z0 ||| p.z1 ||| p.z2 ||| p.z3) == 0

set_option maxRecDepth 16384 in
/-- `[2]p`. Three multiplications and four squarings; infinity maps to infinity (`Z₃ = 2·Y·Z`). -/
def dbl (p : Pt) : Pt :=
  let x := p.x
  let y := p.y
  let z := p.z
  let a := Ff.sqr x
  let b := Ff.sqr y
  let c := Ff.sqr b
  let d := Ff.mulSmall (Ff.mul x b) 4
  let e := Ff.mulSmall a 3
  let f := Ff.sqr e
  let x3 := Ff.sub f (Ff.add d d)
  let y3 := Ff.sub (Ff.mul e (Ff.sub d x3)) (Ff.mulSmall c 8)
  let yz := Ff.mul y z
  Pt.ofXYZ x3 y3 (Ff.add yz yz)

set_option maxRecDepth 16384 in
/-- `p + q` for an affine `q` (negated first when `negate` is set). Eight multiplications and
    three squarings in the general case. -/
def madd (p : Pt) (q : Aff) (negate : Bool) : Pt :=
  let qx := q.x
  let qy := Ff.cneg negate q.y
  if p.isInfinity then Pt.ofXYZ qx qy Ff.one
  else
    let x := p.x
    let y := p.y
    let z := p.z
    let zz := Ff.sqr z
    let u2 := Ff.mul qx zz
    let s2 := Ff.mul (Ff.mul qy z) zz
    let h := Ff.sub u2 x
    let r := Ff.sub s2 y
    if U256.isZero h then
      if U256.isZero r then dbl p else infinity
    else
      let hh := Ff.sqr h
      let hhh := Ff.mul hh h
      let v := Ff.mul x hh
      let x3 := Ff.sub (Ff.sub (Ff.sqr r) hhh) (Ff.add v v)
      let y3 := Ff.sub (Ff.mul r (Ff.sub v x3)) (Ff.mul y hhh)
      Pt.ofXYZ x3 y3 (Ff.mul z h)

set_option maxRecDepth 16384 in
/-- `p + q` for Jacobian points (`q` negated first when `negate` is set). Twelve multiplications
    and four squarings in the general case. -/
def padd (p q : Pt) (negate : Bool) : Pt :=
  if p.isInfinity then Pt.ofXYZ q.x (Ff.cneg negate q.y) q.z
  else if q.isInfinity then p
  else
    let x1 := p.x
    let y1 := p.y
    let z1 := p.z
    let x2 := q.x
    let y2 := Ff.cneg negate q.y
    let z2 := q.z
    let z1z1 := Ff.sqr z1
    let z2z2 := Ff.sqr z2
    let u1 := Ff.mul x1 z2z2
    let u2 := Ff.mul x2 z1z1
    let s1 := Ff.mul (Ff.mul y1 z2) z2z2
    let s2 := Ff.mul (Ff.mul y2 z1) z1z1
    let h := Ff.sub u2 u1
    let r := Ff.sub s2 s1
    if U256.isZero h then
      if U256.isZero r then dbl p else infinity
    else
      let hh := Ff.sqr h
      let hhh := Ff.mul hh h
      let v := Ff.mul u1 hh
      let x3 := Ff.sub (Ff.sub (Ff.sqr r) hhh) (Ff.add v v)
      let y3 := Ff.sub (Ff.mul r (Ff.sub v x3)) (Ff.mul s1 hhh)
      Pt.ofXYZ x3 y3 (Ff.mul (Ff.mul h z1) z2)

/-! ### Tables -/

def betaL : U256 := U256.ofNat beta

/-- The endomorphism `φ` on a Jacobian and on an affine point: `X ↦ beta·X`. -/
def lamPt (p : Pt) : Pt := Pt.ofXYZ (Ff.mul p.x betaL) p.y p.z
def lamAff (p : Aff) : Aff := Aff.ofXY (Ff.mul p.x betaL) p.y

def oddLoop (twice : Pt) : Nat → Pt → Array Pt → Array Pt
  | 0, _, acc => acc
  | c+1, cur, acc => oddLoop twice c (padd cur twice false) (acc.push cur)

/-- `[1]p, [3]p, …, [2·count − 1]p`. -/
def oddTable (p : Pt) (count : Nat) : Array Pt := oddLoop (dbl p) count p #[]

/-- Running products `z₀, z₀z₁, …` of the `Z` coordinates. -/
def prefixLoop (pts : Array Pt) : Nat → Nat → U256 → Array U256 → Array U256
  | 0, _, _, acc => acc
  | c+1, i, run, acc =>
    let next := Ff.mulO run (pts.getD i infinity).z
    prefixLoop pts c (i + 1) next (acc.push next)

/-- From the last point down: `inv` is the inverse of the product up to index `i`. -/
def affLoop (pts : Array Pt) (pre : Array U256) : Nat → U256 → Array Aff → Array Aff
  | 0, _, acc => acc
  | i+1, inv, acc =>
    let p := pts.getD i infinity
    let zi := if i = 0 then inv else Ff.mulO inv (pre.getD (i - 1) Ff.one)
    let zi2 := Ff.sqrO zi
    affLoop pts pre i (Ff.mulO inv p.z)
      (acc.push (Aff.ofXY (Ff.mulO p.x zi2) (Ff.mulO p.y (Ff.mulO zi2 zi))))

/-- Affine forms of finite points with one field inversion (Montgomery's simultaneous
    inversion, 1987). The points must not be at infinity. -/
def toAffTable (pts : Array Pt) : Array Aff :=
  let pre := prefixLoop pts pts.size 0 Ff.one #[]
  (affLoop pts pre pts.size (Ff.inv (pre.getD (pts.size - 1) Ff.one)) #[]).reverse

def gPt : Pt := Pt.ofXYZ (U256.ofNat gx) (U256.ofNat gy) Ff.one

/-- The odd multiples `G, 3G, …, 127G`, affine. Built once. -/
def gTable : Array Aff := toAffTable (oddTable gPt 64)
/-- `φ` of the same points: the odd multiples of `[lam]G`. -/
def lgTable : Array Aff := gTable.map lamAff

end EVMCleanroom.Precompiles.Secp256k1.Fast
