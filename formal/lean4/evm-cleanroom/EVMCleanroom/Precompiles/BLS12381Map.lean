import EVMCleanroom.Precompiles.BLS12381Fast

/-!
# BLS12-381 map to curve on limbs (0x10, 0x11) and square roots

The same contract as `BLS12381.runMapG1` and `runMapG2` (EIP-2537, RFC 9380):
simplified SWU onto the isogenous curve, the isogeny, and clearing the
cofactor. `BLS12381.lean` stays the definition; this module follows published
variants of the same steps that need no field inversion before the final
conversion to affine coordinates:

* Simplified SWU in the straight-line form of RFC 9380, appendix F.2: the
  `x` coordinate is kept as a fraction `xn/xd`, and `y = √(gxn/gxd)` comes
  from one exponentiation. For `G1` this is `sqrt_ratio` for `p ≡ 3 (mod 4)`
  (RFC 9380, F.2.1.2): `y₁ = (u v)·(u v³)^((p−3)/4)`; when `u/v` is not a
  square, `y₁·√(−Z)` is a root of `Z·u/v`.
* For `G2` the square root of a ratio in `Fp2` is taken through the norm
  (the method of `BLS12381.sqrt2?`): with `α = num·conj(den)` and
  `d = N(den)`, `s = √N(α)`, `A = α₀ ± s`, `B = 2d` and
  `e = (A B³)^((p−3)/4)`, the candidate is `(A B e) + (α₁ B e) u`, or that
  times `u` when `A/B` is not a square. Two exponentiations in `Fp`, no
  inversion; the result is verified by `y²·den = num` before use.
* The isogeny is evaluated on the fraction in homogeneous form and returns a
  Jacobian point.
* Cofactor: for `G1` the multiplication by `1 + z` of the definition (a
  64-bit scalar). For `G2` the endomorphism method of Budroni and Pintore
  ("Efficient hash maps to G2 on BLS curves", 2017) as given in RFC 9380,
  appendix G.4 (`clear_cofactor_bls12381_g2`), two multiplications by `z` and
  a few applications of `ψ`, in place of the 636-bit multiplication by
  `h_eff`. This is a published algorithm that is NOT proved here: it is
  compared with the plain multiplication by `h_eff` of the definition.

Exponentiations use four-bit windows.

Tested against the definition, not proved equal: guards below (fixed inputs
including `u = 0`, real and imaginary `u`), the differential run of
`evm-blsops` over pseudo-random and edge inputs for both maps, for the square
roots and for the cofactor clearing on points outside the subgroup, and the
published vectors.

Proved: input-length rules, gas accounting, output lengths (the statements
of `BLS12381.runMap_success`).

Not constant-time.
-/

namespace EVMCleanroom.Precompiles.BLS12381.Fast

/-! ### Powers and square roots in the base field -/

def powTableLoop (a : U384) : Nat → U384 → Array U384 → Array U384
  | 0, _, table => table
  | count+1, last, table =>
    let next := fmul last a
    powTableLoop a count next (table.push next)

/-- `a⁰, a¹, …, a¹⁵`. -/
def powTable (a : U384) : Array U384 := powTableLoop a 15 M.one (#[M.one])

def powWindowLoop (e : Nat) (table : Array U384) : Nat → U384 → U384
  | 0, acc => acc
  | i+1, acc =>
    let acc := fsqr (fsqr (fsqr (fsqr acc)))
    let digit := (e >>> (4 * i)) % 16
    powWindowLoop e table i (if digit = 0 then acc else fmul acc (table.getD digit M.one))

/-- `a^e` with four-bit windows: `4·⌈bits/4⌉` squarings and at most `⌈bits/4⌉ + 14` multiplications. -/
def powWindow (a : U384) (e : Nat) : U384 :=
  powWindowLoop e (powTable a) (Nat.log2 e / 4 + 1) M.one

/-- `(p − 3)/4`: `a^((p−3)/4)·a` is a square root of `a` when `a` is a square. -/
def rootExponent : Nat := (p - 3) / 4

/-- A checked square root in the base field: `none` when `a` is not a square. -/
def sqrt1? (a : U384) : Option U384 :=
  let root := fmul (powWindow a rootExponent) a
  if U384.beq (fsqr root) a then some root else none

/-- `1/2`. -/
def half : U384 := M.ofNat ((p + 1) / 2)

/-- A square root of `num/den` in `Fp2`, verified (`y²·den = num`); `none` when the ratio is
    not a square. `den` must not be zero. Two exponentiations, no inversion. -/
def sqrtRatio2? (num den : Q2 U384) : Option (Q2 U384) :=
  let d := fadd (fsqr den.c0) (fsqr den.c1)
  let alpha := Q2.mul fp num (Q2.conj fp den)
  let n := fadd (fsqr alpha.c0) (fsqr alpha.c1)
  let s := fmul (powWindow n rootExponent) n
  if !U384.beq (fsqr s) n then none
  else
    let plus := fadd alpha.c0 s
    let a := if plus.isZero then fsub alpha.c0 s else plus
    let b := fadd d d
    let e := powWindow (fmul (fmul a b) (fsqr b)) rootExponent
    let be := fmul b e
    let first : Q2 U384 := ⟨fmul a be, fmul alpha.c1 be⟩
    if Q2.eq fp (Q2.mul fp (Q2.sqr fp first) den) num then some first
    else
      let second : Q2 U384 := ⟨fneg first.c1, first.c0⟩
      if Q2.eq fp (Q2.mul fp (Q2.sqr fp second) den) num then some second else none

/-- A checked square root in `Fp2`. -/
def sqrt2? (a : Q2 U384) : Option (Q2 U384) := sqrtRatio2? a ⟨M.one, U384.zero⟩

/-! ### Signs (RFC 9380, section 4.1) on canonical values -/

def sgn0 (a : U384) : Bool := (fromMont a).l0 % 2 == 1

def sgn02 (a : Q2 U384) : Bool :=
  let c0 := fromMont a.c0
  c0.l0 % 2 == 1 || (c0.isZero && (fromMont a.c1).l0 % 2 == 1)

/-! ### Constants in Montgomery form -/

def swuA1 : U384 := M.ofNat BLS12381.swuA1
def swuB1 : U384 := M.ofNat BLS12381.swuB1
def swuZ1 : U384 := M.ofNat 11
/-- `√(−11)`. -/
def sqrtMinusZ1Nat : Nat :=
  0x4610e003bd3ac94dfa9246c390d7a78942602029175a4ca366d601f33f3946e3ed39794735c38315d874bc1d70637c3
def sqrtMinusZ1 : U384 := M.ofNat sqrtMinusZ1Nat

def swuA2 : Q2 U384 := toLimbs2 ⟨0, 240⟩
def swuB2 : Q2 U384 := toLimbs2 ⟨1012, 1012⟩
def swuZ2 : Q2 U384 := toLimbs2 (Fp2.neg p ⟨2, 1⟩)
def one2 : Q2 U384 := ⟨M.one, U384.zero⟩
def zero2 : Q2 U384 := ⟨U384.zero, U384.zero⟩

/-- The isogeny polynomials, lowest degree first, denominators with their leading one. -/
def iso1XNum : Array U384 := BLS12381.iso1XNum.map M.ofNat
def iso1XDen : Array U384 := (BLS12381.iso1XDen.push 1).map M.ofNat
def iso1YNum : Array U384 := BLS12381.iso1YNum.map M.ofNat
def iso1YDen : Array U384 := (BLS12381.iso1YDen.push 1).map M.ofNat
def iso2XNum : Array (Q2 U384) := BLS12381.iso2XNum.map toLimbs2
def iso2XDen : Array (Q2 U384) := (BLS12381.iso2XDen.push Fp2.one).map toLimbs2
def iso2YNum : Array (Q2 U384) := BLS12381.iso2YNum.map toLimbs2
def iso2YDen : Array (Q2 U384) := (BLS12381.iso2YDen.push Fp2.one).map toLimbs2

/-! ### Isogeny on a fraction -/

section
variable {F : Type}

@[specialize] def homLoop (O : FieldOps F) (xn xd : F) (coefficients : Array F) : Nat → F → F → F
  | 0, acc, _ => acc
  | i+1, acc, power =>
    let power := O.mul power xd
    homLoop O xn xd coefficients i (O.add (O.mul acc xn) (O.mul (coefficients.getD i O.zero) power)) power

/-- `Σ cᵢ·xn^i·xd^(n−i)` for the `n + 1` coefficients, lowest degree first: the polynomial
    at `xn/xd`, times `xd^n`. -/
@[specialize] def hom (O : FieldOps F) (xn xd : F) (coefficients : Array F) : F :=
  homLoop O xn xd coefficients (coefficients.size - 1) (coefficients.getD (coefficients.size - 1) O.zero) O.one

/-- The isogeny at the point `(xn/xd, y)`, as a Jacobian point; a zero denominator gives
    the point at infinity. The `x` numerator must have one coefficient more than the `x`
    denominator, the `y` numerator as many as the `y` denominator (guarded below). -/
@[specialize] def isogenyFraction (O : FieldOps F) (xNum xDen yNum yDen : Array F) (xn xd y : F) : JPoint F :=
  let xNumerator := hom O xn xd xNum
  let xDenominator := O.mul (hom O xn xd xDen) xd
  let yNumerator := hom O xn xd yNum
  let yDenominator := hom O xn xd yDen
  if O.isZero xDenominator || O.isZero yDenominator then Curve.infinity O
  else
    let yd2 := O.sqr yDenominator
    ⟨O.mul (O.mul xNumerator xDenominator) yd2,
     O.mul (O.mul y yNumerator) (O.mul (O.mul (O.sqr xDenominator) xDenominator) yd2),
     O.mul xDenominator yDenominator⟩

end

/-! ### Map to G1 -/

/-- Simplified SWU onto the curve isogenous to `G1`'s: `(xn, xd, y)` with `x = xn/xd`. -/
def swu1 (u : U384) : U384 × U384 × U384 :=
  let tv1 := fmul swuZ1 (fsqr u)
  let tv2 := fadd (fsqr tv1) tv1
  let tv3 := fmul swuB1 (fadd tv2 M.one)
  let tv4 := fmul swuA1 (if tv2.isZero then swuZ1 else fneg tv2)
  let tv6 := fsqr tv4
  let gxd := fmul tv6 tv4
  let gxn := fadd (fmul (fadd (fsqr tv3) (fmul swuA1 tv6)) tv3) (fmul swuB1 gxd)
  let uv := fmul gxn gxd
  let y1 := fmul (powWindow (fmul (fsqr gxd) uv) rootExponent) uv
  let square := U384.beq (fmul (fsqr y1) gxd) gxn
  let xn := if square then tv3 else fmul tv1 tv3
  let y := if square then y1 else fmul (fmul tv1 u) (fmul y1 sqrtMinusZ1)
  (xn, tv4, if sgn0 u != sgn0 y then fneg y else y)

def mapToG1 (u : U384) : JPoint U384 :=
  let s := swu1 u
  let point := isogenyFraction fp iso1XNum iso1XDen iso1YNum iso1YDen s.1 s.2.1 s.2.2
  Curve.add fp (mulParameter1 point) point

/-! ### Map to G2 -/

/-- Simplified SWU onto the curve isogenous to `G2`'s twist: `(xn, xd, y)` with `x = xn/xd`. -/
def swu2 (u : Q2 U384) : Q2 U384 × Q2 U384 × Q2 U384 :=
  let tv1 := Q2.mul fp swuZ2 (Q2.sqr fp u)
  let tv2 := Q2.add fp (Q2.sqr fp tv1) tv1
  let tv3 := Q2.mul fp swuB2 (Q2.add fp tv2 one2)
  let tv4 := Q2.mul fp swuA2 (if Q2.isZero fp tv2 then swuZ2 else Q2.neg fp tv2)
  let tv6 := Q2.sqr fp tv4
  let gxd := Q2.mul fp tv6 tv4
  let gxn := Q2.add fp (Q2.mul fp (Q2.add fp (Q2.sqr fp tv3) (Q2.mul fp swuA2 tv6)) tv3) (Q2.mul fp swuB2 gxd)
  let chosen : Q2 U384 × Q2 U384 :=
    match sqrtRatio2? gxn gxd with
    | some y => (tv3, y)
    | none =>
      (Q2.mul fp tv1 tv3,
       (sqrtRatio2? (Q2.mul fp (Q2.mul fp (Q2.sqr fp tv1) tv1) gxn) gxd).getD zero2)
  (chosen.1, tv4, if sgn02 u != sgn02 chosen.2 then Q2.neg fp chosen.2 else chosen.2)

def neg2 (point : JPoint (Q2 U384)) : JPoint (Q2 U384) := ⟨point.x, Q2.neg fp point.y, point.z⟩

/-- Multiplication by the effective cofactor `h_eff` of `G2` (RFC 9380, appendix G.4;
    the curve parameter is `−z`). Published algorithm, not proved here. -/
def clearCofactor2 (point : JPoint (Q2 U384)) : JPoint (Q2 U384) :=
  let t1 := neg2 (mulParameter2 point)
  let t2 := psiJ point
  let t3 := psiJ (psiJ (Curve.double fp2 point))
  let t3 := Curve.add fp2 t3 (neg2 t2)
  let t2 := Curve.add fp2 t1 t2
  let t2 := neg2 (mulParameter2 t2)
  let t3 := Curve.add fp2 t3 t2
  let t3 := Curve.add fp2 t3 (neg2 t1)
  Curve.add fp2 t3 (neg2 point)

def mapToG2 (u : Q2 U384) : JPoint (Q2 U384) :=
  let s := swu2 u
  clearCofactor2 (isogenyFraction fp2 iso2XNum iso2XDen iso2YNum iso2YDen s.1 s.2.1 s.2.2)

def mapG1Body (input : ByteArray) : Body :=
  match decodeFp input 0 with
  | some u => .output (encodeG1 (mapToG1 u))
  | none => .invalid

def mapG2Body (input : ByteArray) : Body :=
  match decodeFp2 input 0 with
  | some u => .output (encodeG2 (mapToG2 u))
  | none => .invalid

/-- Precompile 0x10 on limbs. -/
def runMapG1 (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 64 then .failure else charge gas 5500 fun _ => mapG1Body input

/-- Precompile 0x11 on limbs. -/
def runMapG2 (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 128 then .failure else charge gas 23800 fun _ => mapG2Body input

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful map of a field element to G1 on limbs had exactly 64 input bytes,
    cost 5500 gas and returned 128 bytes; the map to G2 had 128 input bytes, cost 23800
    and returned 256 bytes.
    Does not say: the point is the RFC 9380 image, or equals that of `BLS12381.runMapG1`
    and `runMapG2` (differential runs and vectors, not proved). -/
theorem runMap_success (gas : Nat) (input out : ByteArray) (left : Nat) :
    (runMapG1 gas input = .success out left → input.size = 64 ∧ out.size = 128 ∧ left + 5500 = gas) ∧
    (runMapG2 gas input = .success out left → input.size = 128 ∧ out.size = 256 ∧ left + 23800 = gas) := by
  constructor
  · intro h
    have ⟨hSize, hBody, hGas⟩ := fixed_success 64 5500 gas input out left mapG1Body h
    refine ⟨hSize, ?_, hGas⟩
    simp only [mapG1Body] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG1_size _
    · exact Body.noConfusion hBody
  · intro h
    have ⟨hSize, hBody, hGas⟩ := fixed_success 128 23800 gas input out left mapG2Body h
    refine ⟨hSize, ?_, hGas⟩
    simp only [mapG2Body] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG2_size _
    · exact Body.noConfusion hBody

/-! ### Guards against the definition -/

private def fe (n : Nat) : ByteArray := natToBE 64 n
private def map1Agrees (u : Nat) : Bool := (runMapG1 100000 (fe u)).same (BLS12381.runMapG1 100000 (fe u))
private def map2Agrees (u : Fp2) : Bool :=
  (runMapG2 100000 (fe u.c0 ++ fe u.c1)).same (BLS12381.runMapG2 100000 (fe u.c0 ++ fe u.c1))
private def root2Agrees (a : Fp2) : Bool :=
  match sqrt2? (toLimbs2 a), BLS12381.sqrt2? a with
  | some root, some _ => ofLimbs2 (Q2.sqr fp root) == a
  | none, none => true
  | _, _ => false
private def wide : Nat := 0x123456789abcdef0fedcba9876543210a5a5a5a55a5a5a5a0f0f0f0ff0f0f0f0c3c3c3c33c3c3c3c1122334455667788

#guard sqrtMinusZ1Nat ^ 2 % p == p - 11 && p % 4 == 3 && 4 * rootExponent + 3 == p && M.toNat half * 2 % p == 1
#guard iso1XNum.size == iso1XDen.size + 1 && iso1YNum.size == iso1YDen.size &&
  iso2XNum.size == iso2XDen.size + 1 && iso2YNum.size == iso2YDen.size
#guard M.toNat (powWindow (M.ofNat 3) 0xfedcba9876543210f) == Fp.pow p 3 0xfedcba9876543210f &&
  M.toNat (powWindow (M.ofNat wide) 1) == wide && M.toNat (powWindow (M.ofNat wide) 16) == Fp.pow p wide 16
#guard [0, 1, 2, 3, 4, 5, wide, p - 1, p - 4].all fun a => (sqrt1? (M.ofNat a)).map M.toNat == Fp.sqrt? p a
#guard root2Agrees ⟨0, 0⟩ && root2Agrees ⟨4, 0⟩ && root2Agrees ⟨5, 0⟩ && root2Agrees ⟨p - 4, 0⟩ &&
  root2Agrees ⟨0, 4⟩ && root2Agrees ⟨0, 5⟩ && root2Agrees ⟨3, 4⟩ && root2Agrees ⟨wide, 7⟩ &&
  root2Agrees (Fp2.sqr p ⟨wide, 5⟩) && root2Agrees (Fp2.sqr p ⟨0, wide⟩) && root2Agrees (Fp2.sqr p ⟨wide, 0⟩) &&
  root2Agrees ⟨1, 1⟩ && root2Agrees ⟨2, 1⟩
#guard sgn0 (M.ofNat 5) && !sgn0 (M.ofNat 4) && !sgn0 (M.ofNat 0) &&
  [(⟨0, 0⟩ : Fp2), ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨wide, wide + 1⟩].all fun a =>
    sgn02 (toLimbs2 a) == (BLS12381.sgn02 a == 1)
#guard map1Agrees 0 && map1Agrees 1 && map1Agrees 2 && map1Agrees (p - 1) && map1Agrees wide
#guard map1Agrees p == true && (match runMapG1 100000 (fe p) with | .failure => true | _ => false) &&
  map1Agrees (2 ^ 384) && (runMapG1 100000 (fe 1 ++ fe 1)).same (BLS12381.runMapG1 100000 (fe 1 ++ fe 1))
#guard map2Agrees ⟨0, 0⟩ && map2Agrees ⟨1, 0⟩ && map2Agrees ⟨0, 1⟩ && map2Agrees ⟨1, 2⟩
#guard map2Agrees ⟨wide, p - 1⟩ && map2Agrees ⟨p, 1⟩ && map2Agrees ⟨1, 2 ^ 384⟩
-- Clearing the cofactor by endomorphisms against the multiplication by h_eff, on a point outside the subgroup.
private def outside : Fp2 × Fp2 :=
  (⟨2, 1⟩, (BLS12381.sqrt2? (Fp2.add p (Fp2.mul p (Fp2.sqr p ⟨2, 1⟩) ⟨2, 1⟩) BLS12381.twistB)).getD Fp2.zero)
#guard Curve.onCurve field2 BLS12381.twistB outside.1 outside.2 && !BLS12381.inSubgroup2 outside.1 outside.2
#guard (Curve.toAffineFast fp2 (clearCofactor2 (Curve.ofAffine fp2 (toLimbs2 outside.1) (toLimbs2 outside.2)))).map
    (fun point => (ofLimbs2 point.1, ofLimbs2 point.2)) ==
  Curve.toAffine field2 (Curve.mul field2 cofactor2 (Curve.ofAffine field2 outside.1 outside.2))
#guard (Curve.toAffineFast fp2 (clearCofactor2 (Curve.infinity fp2))).isNone

#print axioms runMap_success

end EVMCleanroom.Precompiles.BLS12381.Fast
