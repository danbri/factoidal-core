import EVMCleanroom.Precompiles.BLS12381
import EVMCleanroom.Precompiles.BLS12381Field
import EVMCleanroom.Precompiles.LimbBytes
import EVMCleanroom.Precompiles.Fp2Limb
import EVMCleanroom.Precompiles.CurveFast
import EVMCleanroom.Precompiles.LimbInverse
import EVMCleanroom.Precompiles.LimbSquare

/-!
# BLS12-381 on limbs: decoding, subgroup checks, G1 and G2 addition (0x0b, 0x0d)

The same contracts as in `BLS12381.lean` (EIP-2537), computed on the six-limb
Montgomery field `BLS12381.baseField` and on `Q2` over it for `G2`.
`BLS12381.lean` stays the definition and the differential oracle.

## Decoding

`decodeFp`, `decodeFp2`, `decodeG1`, `decodeG2` apply the EIP-2537 rules (top
16 bytes zero, value below `p`, all-zero bytes for the point at infinity, the
curve equation, and on request the order-`r` subgroup) and return coordinates
in Montgomery form.

## Subgroup checks by endomorphism

The definition checks `[r]P = O` with a 255-bit scalar multiplication. Here:

* `G1` (`inSubgroup1`): `P` is accepted iff `φ(P) = −[z²]P`, where
  `φ(x, y) = (βx, y)`, `β` is the cube root of unity `beta` below, and
  `z = 0xd201000000010000` is the absolute value of the curve parameter.
* `G2` (`inSubgroup2`): `Q` is accepted iff `ψ(Q) = −[z]Q` (the curve parameter
  is `−z`), where `ψ(x, y) = (x̄·psiX, ȳ·psiY)` is the untwist-Frobenius-twist
  endomorphism of the twist.

Sources: Scott, "A note on group membership tests for G1, G2 and GT on BLS
pairing-friendly curves" (2021), sections 4 and 6: for a BLS12 curve with
parameter `u`, a point `Q` of the twist over `Fp2` has order `r` iff
`ψ(Q) = [u]Q`, and a point `P` of the curve over `Fp` has order `r` iff
`φ(P) = −[u²]P` for the matching cube root of unity. Bowe, "Faster subgroup
checks for BLS12-381" (2019) gives the earlier variants of both tests.

These criteria are NOT proved here, and they are consensus-critical. The
argument for soundness (an accepted point has order dividing `r`), from
facts about the endomorphisms that are standard but not formalised here:

* `G1`: `φ` is an endomorphism with `φ² + φ + 1 = 0` (because `β² + β + 1 = 0`).
  If `φ(P) = −[z²]P` then `φ²(P) = [z⁴]P`, so `[z⁴ − z² + 1]P = O`, and
  `z⁴ − z² + 1 = r`.
* `G2`: `ψ` satisfies the characteristic equation of Frobenius,
  `ψ² − [t]ψ + [p] = 0` with trace `t = u + 1` (Galbraith and Scott 2008).
  If `ψ(Q) = [u]Q` then `[u² − (u + 1)u + p]Q = [p − u]Q = O`, and
  `p − u = h₁·r` with `h₁ = (u − 1)²/3` the cofactor of `G1`. The order of `Q`
  also divides the order `h₂·r` of the twist, and `gcd(h₁, h₂) = 1`, so it
  divides `r`.

Completeness (points of order `r` are accepted) holds because `φ` and `ψ` act
on the subgroups as multiplication by `−z²` and by `p ≡ u (mod r)`.

Evidence in this repository: build-time guards for the numeric facts used
(`β³ = 1`, `β ≠ 1`, `r = z⁴ − z² + 1`, `p + z = h₁·r`, `gcd(h₁, h₂) = 1`,
`2·h₂·r = 2p² + 2p + 2 − t² + 3|t|f` with `4p − t² = 3f²`, the constants of
`ψ` as powers of the twist constant, the tests on the generators) and guards
comparing both checks with the definitional ones on points inside and
outside the subgroups; the differential run of `evm-blsops` compares them on
pseudo-random subgroup points, curve points outside the subgroup, points of
small order (cofactor multiples) and sums of a subgroup point and a
small-order point; the published vectors include the failure files for
points outside the subgroup.

## Proved

Input-length rules, gas accounting, output lengths (the statements of
`BLS12381.runG1Add_success` and `runG2Add_success`). Not proved: that the
bytes are those of the definition (differential runs and vectors).

Nothing is constant-time.
-/

namespace EVMCleanroom.Precompiles.BLS12381.Fast

/-- The base field in Montgomery form. -/
def M : Mont384 := BLS12381.baseField

/-! The field operations as plain functions. The Montgomery routines of `Montgomery.lean`
are marked for inlining; here each is instantiated once for this modulus, and the curve
code calls these (inlining them at every use made the compiler exceed its step limit). -/

def fmul (a b : U384) : U384 := BLS12381.baseField.mul a b
def fsqr (a : U384) : U384 := BLS12381.baseField.sqrFast a
def fadd (a b : U384) : U384 := BLS12381.baseField.add a b
def fsub (a b : U384) : U384 := BLS12381.baseField.sub a b
def fneg (a : U384) : U384 := BLS12381.baseField.neg a
def finv (a : U384) : U384 := BLS12381.baseField.invFast a
def toMont (a : U384) : U384 := BLS12381.baseField.toMont a
def fromMont (a : U384) : U384 := BLS12381.baseField.fromMont a

def fp : FieldOps U384 where
  zero := U384.zero
  one := BLS12381.baseField.one
  add := fadd
  sub := fsub
  mul := fmul
  sqr := fsqr
  neg := fneg
  inv := finv
  isZero := U384.isZero
  eq := U384.beq

def fp2 : FieldOps (Q2 U384) := Q2.ops fp

abbrev G1Affine := U384 × U384
abbrev G2Affine := Q2 U384 × Q2 U384

/-- A `Nat` pair of the definition in Montgomery form, and back. -/
def toLimbs2 (a : Fp2) : Q2 U384 := ⟨M.ofNat a.c0, M.ofNat a.c1⟩
def ofLimbs2 (a : Q2 U384) : Fp2 := ⟨M.toNat a.c0, M.toNat a.c1⟩

/-- The curve coefficient 4, and the twist coefficient `4 + 4u`. -/
def four : U384 := M.ofNat 4
def twistB : Q2 U384 := ⟨four, four⟩

/-! ### Decoding -/

/-- A 64-byte field element: top 16 bytes zero, value below `p`. Montgomery form. -/
def decodeFp (data : ByteArray) (off : Nat) : Option U384 :=
  if be64 data off != 0 || be64 data (off + 8) != 0 then none
  else
    let value := U384.ofBE data (off + 16)
    if U384.lt value M.n then some (toMont value) else none

def decodeFp2 (data : ByteArray) (off : Nat) : Option (Q2 U384) :=
  match decodeFp data off, decodeFp data (off + 64) with
  | some c0, some c1 => some ⟨c0, c1⟩
  | _, _ => none

@[inline] def onCurve1 (x y : U384) : Bool :=
  U384.beq (fsqr y) (fadd (fmul (fsqr x) x) four)

@[inline] def onCurve2 (x y : Q2 U384) : Bool :=
  Q2.eq fp (Q2.sqr fp y) (Q2.add fp (Q2.mul fp (Q2.sqr fp x) x) twistB)

/-! ### Subgroup checks -/

/-- The cube root of unity `β` with `φ(P) = (βx, y) = −[z²]P` on `G1`. -/
def betaNat : Nat :=
  0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe
def beta : U384 := M.ofNat betaNat

/-- `1 / (1 + u)^((p − 1)/3)` and `1 / (1 + u)^((p − 1)/2)`: the constants of `ψ`. -/
def psiXNat : Fp2 :=
  ⟨0, 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad⟩
def psiYNat : Fp2 :=
  ⟨0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2,
   0x6af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09⟩
def psiX : Q2 U384 := toLimbs2 psiXNat
def psiY : Q2 U384 := toLimbs2 psiYNat

/-- The cofactor of `G1`, `(z + 1)²/3`, and of `G2`. -/
def h1 : Nat := (parameter + 1) ^ 2 / 3
def h2 : Nat :=
  0x5d543a95414e7f1091d50792876a202cd91de4547085abaa68a205b2e5a7ddfa628f1cb4d9e82ef21537e293a6691ae1616ec6e786f0c70cf1c38e31c7238e5

/-- `f` with `4p − t² = 3f²` for the trace `t = 1 − z` (used only in the guard on the twist order). -/
def traceF : Nat := 0x5e368889a40203366585c2acf9586d5664ab0000aaaa5555

/-- `[z]P` on `G1` for the 64-bit curve parameter `z` (Hamming weight 6). -/
def mulParameter1 (point : JPoint U384) : JPoint U384 :=
  Curve.mulLoop fp parameter point 64 (Curve.infinity fp)

/-- `[z]Q` on `G2`. -/
def mulParameter2 (point : JPoint (Q2 U384)) : JPoint (Q2 U384) :=
  Curve.mulLoop fp2 parameter point 64 (Curve.infinity fp2)

/-- Is the affine curve point `(x, y)` in the order-`r` subgroup? The test is
    `φ(P) = −[z²]P`, compared without inversion. Published criterion, not proved here. -/
def inSubgroup1 (x y : U384) : Bool :=
  let q := mulParameter1 (mulParameter1 (Curve.ofAffine fp x y))
  if U384.isZero q.z then false
  else
    let zz := fsqr q.z
    U384.beq q.x (fmul (fmul beta x) zz) && U384.beq (fneg q.y) (fmul y (fmul zz q.z))

/-- `ψ` on an affine point of the twist. -/
def psi (x y : Q2 U384) : G2Affine := (Q2.mul fp (Q2.conj fp x) psiX, Q2.mul fp (Q2.conj fp y) psiY)

/-- `ψ` on a Jacobian point of the twist. -/
def psiJ (point : JPoint (Q2 U384)) : JPoint (Q2 U384) :=
  ⟨Q2.mul fp (Q2.conj fp point.x) psiX, Q2.mul fp (Q2.conj fp point.y) psiY, Q2.conj fp point.z⟩

/-- Is the affine twist point `(x, y)` in the order-`r` subgroup? The test is
    `ψ(Q) = −[z]Q`, compared without inversion. Published criterion, not proved here. -/
def inSubgroup2 (x y : Q2 U384) : Bool :=
  let q := mulParameter2 (Curve.ofAffine fp2 x y)
  if Q2.isZero fp q.z then false
  else
    let image := psi x y
    let zz := Q2.sqr fp q.z
    Q2.eq fp q.x (Q2.mul fp image.1 zz) && Q2.eq fp (Q2.neg fp q.y) (Q2.mul fp image.2 (Q2.mul fp zz q.z))

/-- Decode a `G1` point; the outer `none` is invalid input, the inner `none` infinity. -/
def decodeG1 (data : ByteArray) (off : Nat) (subgroup : Bool) : Option (Option G1Affine) :=
  match decodeFp data off, decodeFp data (off + 64) with
  | some x, some y =>
    if x.isZero && y.isZero then some none
    else if !onCurve1 x y then none
    else if subgroup && !inSubgroup1 x y then none
    else some (some (x, y))
  | _, _ => none

def decodeG2 (data : ByteArray) (off : Nat) (subgroup : Bool) : Option (Option G2Affine) :=
  match decodeFp2 data off, decodeFp2 data (off + 128) with
  | some x, some y =>
    if Q2.isZero fp x && Q2.isZero fp y then some none
    else if !onCurve2 x y then none
    else if subgroup && !inSubgroup2 x y then none
    else some (some (x, y))
  | _, _ => none

/- The proofs below and in the modules that use the decoders treat decoding as opaque;
   unfolding it would expose the limb arithmetic. -/
attribute [irreducible] decodeFp decodeFp2 decodeG1 decodeG2

/-! ### Encoding -/

/-- Append a field element as 64 bytes: 16 zero bytes and the canonical value. -/
def pushFp (acc : ByteArray) (a : U384) : ByteArray :=
  U384.pushBE (pushBE64 (pushBE64 acc 0) 0) (fromMont a)

theorem pushFp_size (acc : ByteArray) (a : U384) : (pushFp acc a).size = acc.size + 64 := by
  simp only [pushFp, U384.pushBE_size, pushBE64_size] <;> omega

def jacobian1 : Option G1Affine → JPoint U384
  | none => Curve.infinity fp
  | some (x, y) => Curve.ofAffine fp x y

def jacobian2 : Option G2Affine → JPoint (Q2 U384)
  | none => Curve.infinity fp2
  | some (x, y) => Curve.ofAffine fp2 x y

def encodeG1 (point : JPoint U384) : ByteArray :=
  match Curve.toAffineFast fp point with
  | none => natToBE 128 0
  | some (x, y) => pushFp (pushFp ByteArray.empty x) y

def encodeG2 (point : JPoint (Q2 U384)) : ByteArray :=
  match Curve.toAffineFast fp2 point with
  | none => natToBE 256 0
  | some (x, y) => pushFp (pushFp (pushFp (pushFp ByteArray.empty x.c0) x.c1) y.c0) y.c1

/-- Kind: length.
    Says: an encoded `G1` point has exactly 128 bytes, an encoded `G2` point exactly 256.
    Does not say: which bytes. -/
theorem encodeG1_size (point : JPoint U384) : (encodeG1 point).size = 128 := by
  unfold encodeG1
  split
  · exact natToBE_size _ _
  · simp [pushFp_size]

theorem encodeG2_size (point : JPoint (Q2 U384)) : (encodeG2 point).size = 256 := by
  unfold encodeG2
  split
  · exact natToBE_size _ _
  · simp [pushFp_size]

/-! ### Addition -/

def add1 (a b : Option G1Affine) : JPoint U384 :=
  match a, b with
  | none, _ => jacobian1 b
  | _, none => jacobian1 a
  | some first, some second => Curve.addAffine fp first.1 first.2 second.1 second.2

def add2 (a b : Option G2Affine) : JPoint (Q2 U384) :=
  match a, b with
  | none, _ => jacobian2 b
  | _, none => jacobian2 a
  | some first, some second => Curve.addAffine fp2 first.1 first.2 second.1 second.2

def g1AddBody (data : ByteArray) : Body :=
  match decodeG1 data 0 false, decodeG1 data 128 false with
  | some a, some b => .output (encodeG1 (add1 a b))
  | _, _ => .invalid

def g2AddBody (data : ByteArray) : Body :=
  match decodeG2 data 0 false, decodeG2 data 256 false with
  | some a, some b => .output (encodeG2 (add2 a b))
  | _, _ => .invalid

/-- Precompile 0x0b on limbs. -/
def runG1Add (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 256 then .failure else charge gas 375 fun _ => g1AddBody input

/-- Precompile 0x0d on limbs. -/
def runG2Add (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 512 then .failure else charge gas 600 fun _ => g2AddBody input

/-- Shared shape of the fixed-length operations: wrong length fails; success has the
    exact price. -/
theorem fixed_success (size price gas : Nat) (input out : ByteArray) (left : Nat)
    (body : ByteArray → Body)
    (h : (if input.size ≠ size then Result.failure else charge gas price fun _ => body input) =
      .success out left) :
    input.size = size ∧ body input = .output out ∧ left + price = gas := by
  split at h
  · cases h
  · rename_i hSize
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    exact ⟨by omega, hBody, hGas⟩

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful G1 addition on limbs had exactly 256 input bytes, cost exactly 375
    gas and returned exactly 128 bytes.
    Does not say: the bytes encode the group sum, or equal those of `BLS12381.runG1Add`
    (differential runs and vectors, not proved). -/
theorem runG1Add_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG1Add gas input = .success out left) :
    input.size = 256 ∧ out.size = 128 ∧ left + 375 = gas := by
  have ⟨hSize, hBody, hGas⟩ := fixed_success 256 375 gas input out left g1AddBody h
  refine ⟨hSize, ?_, hGas⟩
  simp only [g1AddBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG1_size _
  · exact Body.noConfusion hBody

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful G2 addition on limbs had exactly 512 input bytes, cost exactly 600
    gas and returned exactly 256 bytes.
    Does not say: the bytes encode the group sum, or equal those of `BLS12381.runG2Add`
    (differential runs and vectors, not proved). -/
theorem runG2Add_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG2Add gas input = .success out left) :
    input.size = 512 ∧ out.size = 256 ∧ left + 600 = gas := by
  have ⟨hSize, hBody, hGas⟩ := fixed_success 512 600 gas input out left g2AddBody h
  refine ⟨hSize, ?_, hGas⟩
  simp only [g2AddBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG2_size _
  · exact Body.noConfusion hBody

/-! ### Guards -/

private def fe (n : Nat) : ByteArray := natToBE 64 n
private def bytes1 (point : Nat × Nat) : ByteArray := fe point.1 ++ fe point.2
private def bytes2 (point : Fp2 × Fp2) : ByteArray :=
  fe point.1.c0 ++ fe point.1.c1 ++ fe point.2.c0 ++ fe point.2.c1
private def multiple1 (k : Nat) (point : Nat × Nat) : Nat × Nat :=
  (Curve.toAffine field (Curve.mul field k (Curve.ofAffine field point.1 point.2))).getD (0, 0)
private def multiple2 (k : Nat) (point : Fp2 × Fp2) : Fp2 × Fp2 :=
  (Curve.toAffine field2 (Curve.mul field2 k (Curve.ofAffine field2 point.1 point.2))).getD (Fp2.zero, Fp2.zero)
private def sum1 (a b : Nat × Nat) : Nat × Nat :=
  (Curve.toAffine field (Curve.add field (Curve.ofAffine field a.1 a.2) (Curve.ofAffine field b.1 b.2))).getD (0, 0)
private def sum2 (a b : Fp2 × Fp2) : Fp2 × Fp2 :=
  (Curve.toAffine field2 (Curve.add field2 (Curve.ofAffine field2 a.1 a.2) (Curve.ofAffine field2 b.1 b.2))).getD
    (Fp2.zero, Fp2.zero)
/-- A curve point with the given `x`, if `x³ + 4` is a square: almost surely outside the subgroup. -/
private def lift1 (x : Nat) : Nat × Nat := (x, (Fp.sqrt? p ((x * x % p * x + 4) % p)).getD 0)
private def lift2 (x : Fp2) : Fp2 × Fp2 :=
  (x, (sqrt2? (Fp2.add p (Fp2.mul p (Fp2.sqr p x) x) BLS12381.twistB)).getD Fp2.zero)
private def g1Add (a b : ByteArray) : Bool :=
  (runG1Add 1000 (a ++ b)).same (BLS12381.runG1Add 1000 (a ++ b))
private def g2Add (a b : ByteArray) : Bool :=
  (runG2Add 1000 (a ++ b)).same (BLS12381.runG2Add 1000 (a ++ b))
private def sub1Agrees (point : Nat × Nat) : Bool :=
  inSubgroup1 (M.ofNat point.1) (M.ofNat point.2) == BLS12381.inSubgroup1 point.1 point.2
private def sub2Agrees (point : Fp2 × Fp2) : Bool :=
  inSubgroup2 (toLimbs2 point.1) (toLimbs2 point.2) == BLS12381.inSubgroup2 point.1 point.2

/- Test values are functions of a unit argument, compiled without closed-term extraction: a constant
   would be computed whenever a program that links this module starts (the small-order points below
   cost milliseconds each). -/
set_option compiler.extract_closed false in
private def a1 (_ : Unit) : Nat × Nat := multiple1 5 g1Generator
set_option compiler.extract_closed false in
private def b1 (_ : Unit) : Nat × Nat := multiple1 7 g1Generator
set_option compiler.extract_closed false in
private def a2 (_ : Unit) : Fp2 × Fp2 := multiple2 5 g2Generator
set_option compiler.extract_closed false in
private def b2 (_ : Unit) : Fp2 × Fp2 := multiple2 7 g2Generator
set_option compiler.extract_closed false in
/-- Curve points outside the subgroups (`x = 5` and `x = 2 + u` lift; checked below). -/
private def out1 (_ : Unit) : Nat × Nat := lift1 5
set_option compiler.extract_closed false in
private def out2 (_ : Unit) : Fp2 × Fp2 := lift2 ⟨2, 1⟩
set_option compiler.extract_closed false in
/-- Points of order 3 and 11 on the curve, 13 and 23 on the twist (cofactor multiples; the
    11-, 13- and 23-parts of the groups are not cyclic, hence the squares). -/
private def order3 (_ : Unit) : Nat × Nat := multiple1 (h1 * r / 3) (out1 ())
set_option compiler.extract_closed false in
private def order11 (_ : Unit) : Nat × Nat := multiple1 (h1 * r / 121) (out1 ())
set_option compiler.extract_closed false in
private def order13 (_ : Unit) : Fp2 × Fp2 := multiple2 (h2 * r / 169) (out2 ())
set_option compiler.extract_closed false in
private def order23 (_ : Unit) : Fp2 × Fp2 := multiple2 (h2 * r / 529) (out2 ())

-- The Montgomery parameters belong to the modulus of the definition.
#guard M.n.toNat == p && M.toNat four == 4 && M.toNat M.one == 1
#guard M.toNat (fmul (M.ofNat (p - 5)) (M.ofNat (p - 7))) == 35 && M.toNat (finv (M.ofNat 7)) == Fp.inv p 7 &&
  M.toNat (fsub (M.ofNat 3) (M.ofNat 5)) == p - 2 && (fromMont (toMont (U384.ofNat 12345))).toNat == 12345
-- The limb inverse: the unverified candidate is the inverse of the definition (381 bits fit 383).
#guard M.n.toNat < 2 ^ 383 &&
  [1, 2, 3, 7, p - 1, p - 2, (p - 1) / 2, (p + 1) / 2, 2 ^ 64, 2 ^ 380, betaNat, traceF].all fun a =>
    M.toNat (M.invCandidate (M.ofNat a)) == Fp.inv p a && M.toNat (finv (M.ofNat a)) == Fp.inv p a
#guard (finv U384.zero).isZero
-- The field square through the dedicated squaring is the product with itself.
#guard [0, 1, 2, p - 1, p - 2, (p - 1) / 2, 2 ^ 380, 2 ^ 64 - 1, betaNat, traceF].all fun a =>
  M.toNat (fsqr (M.ofNat a)) == a * a % p && (fsqr (M.ofNat a)).toNat == (M.sqr (M.ofNat a)).toNat
-- Numeric facts behind the subgroup criteria.
#guard betaNat ^ 3 % p == 1 && betaNat != 1 && (betaNat ^ 2 + betaNat + 1) % p == 0
#guard r == parameter ^ 4 - parameter ^ 2 + 1 && (parameter + 1) ^ 2 % 3 == 0 && p + parameter == h1 * r
#guard Nat.gcd h1 h2 == 1 && h1 == 3 * 11 ^ 2 * 10177 ^ 2 * 859267 ^ 2 * 52437899 ^ 2
#guard h2 % (13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069) == 0
-- The order of the twist: with trace t = 1 − z and 4p − t² = 3f², 2·#E'(Fp2) = 2p² + 2p + 2 − t² + 3|t|f.
#guard 3 * traceF ^ 2 == 4 * p - (parameter - 1) ^ 2
#guard 2 * h2 * r == 2 * p ^ 2 + 2 * p + 2 - (parameter - 1) ^ 2 + 3 * (parameter - 1) * traceF
-- The effective cofactor of the map to G2 is h₂·3(z² − 1).
#guard cofactor2 == h2 * (3 * (parameter ^ 2 - 1)) && cofactor1 == parameter + 1
-- The constants of ψ are the stated powers of the twist constant 1 + u.
#guard Fp2.mul p psiXNat (Fp2.pow p ⟨1, 1⟩ ((p - 1) / 3)) == Fp2.one
#guard Fp2.mul p psiYNat (Fp2.pow p ⟨1, 1⟩ ((p - 1) / 2)) == Fp2.one
-- On the generators (definition's arithmetic): φ(G₁) = −[z²]G₁ and ψ(G₂) = −[z]G₂.
#guard (Fp.mul p betaNat g1Generator.1, Fp.neg p g1Generator.2) == multiple1 (parameter ^ 2) g1Generator
#guard (Fp2.mul p (Fp2.conj p g2Generator.1) psiXNat, Fp2.neg p (Fp2.mul p (Fp2.conj p g2Generator.2) psiYNat)) ==
  multiple2 parameter g2Generator
-- The limb checks accept the generators and multiples, as the definition does.
#guard inSubgroup1 (M.ofNat g1Generator.1) (M.ofNat g1Generator.2) && sub1Agrees (a1 ()) && sub1Agrees (b1 ())
#guard inSubgroup2 (toLimbs2 g2Generator.1) (toLimbs2 g2Generator.2) && sub2Agrees (a2 ()) && sub2Agrees (b2 ())
-- Points outside the subgroups are on the curve and are rejected, as by the definition.
#guard Curve.onCurve field 4 (out1 ()).1 (out1 ()).2 && !BLS12381.inSubgroup1 (out1 ()).1 (out1 ()).2 && sub1Agrees (out1 ())
#guard Curve.onCurve field2 BLS12381.twistB (out2 ()).1 (out2 ()).2 && !BLS12381.inSubgroup2 (out2 ()).1 (out2 ()).2 && sub2Agrees (out2 ())
-- Small-order points, and a subgroup point plus a small-order point.
#guard
  let t3 := order3 ()
  let t11 := order11 ()
  let mixed := sum1 (a1 ()) t3
  t3 != (0, 0) && t11 != (0, 0) && multiple1 3 t3 == (0, 0) && multiple1 11 t11 == (0, 0) &&
    !inSubgroup1 (M.ofNat t3.1) (M.ofNat t3.2) && sub1Agrees t3 && sub1Agrees t11 && sub1Agrees mixed &&
    sub1Agrees (sum1 (b1 ()) t11) && !inSubgroup1 (M.ofNat mixed.1) (M.ofNat mixed.2) &&
    g1Add (bytes1 t3) (bytes1 t3) && g1Add (bytes1 t3) (bytes1 mixed)
#guard
  let t13 := order13 ()
  let t23 := order23 ()
  let mixed := sum2 (a2 ()) t13
  t13 != (Fp2.zero, Fp2.zero) && t23 != (Fp2.zero, Fp2.zero) &&
    multiple2 13 t13 == (Fp2.zero, Fp2.zero) && multiple2 23 t23 == (Fp2.zero, Fp2.zero) &&
    !inSubgroup2 (toLimbs2 t13.1) (toLimbs2 t13.2) && sub2Agrees t13 && sub2Agrees t23 && sub2Agrees mixed &&
    sub2Agrees (sum2 (b2 ()) t23) && !inSubgroup2 (toLimbs2 mixed.1) (toLimbs2 mixed.2) &&
    g2Add (bytes2 t13) (bytes2 t13) && g2Add (bytes2 t13) (bytes2 mixed)
-- The limb Fp2 against the definition on full-size values.
#guard ofLimbs2 (Q2.mul fp (toLimbs2 (a2 ()).1) (toLimbs2 (b2 ()).2)) == Fp2.mul p (a2 ()).1 (b2 ()).2 &&
  ofLimbs2 (Q2.sqr fp (toLimbs2 (a2 ()).2)) == Fp2.sqr p (a2 ()).2 && ofLimbs2 (Q2.inv fp (toLimbs2 (b2 ()).1)) == Fp2.inv p (b2 ()).1 &&
  ofLimbs2 (Q2.sub fp (toLimbs2 (a2 ()).1) (toLimbs2 (b2 ()).2)) == Fp2.sub p (a2 ()).1 (b2 ()).2
-- Addition: generic, doubling, inverse points, infinity, points outside the subgroup, invalid input.
#guard g1Add (bytes1 (a1 ())) (bytes1 (b1 ())) && g1Add (bytes1 (a1 ())) (bytes1 (a1 ())) && g1Add (bytes1 (a1 ())) (bytes1 ((a1 ()).1, p - (a1 ()).2)) &&
  g1Add (fe 0 ++ fe 0) (bytes1 (b1 ())) && g1Add (bytes1 (b1 ())) (fe 0 ++ fe 0) && g1Add (fe 0 ++ fe 0) (fe 0 ++ fe 0) &&
  g1Add (bytes1 (out1 ())) (bytes1 (a1 ()))
#guard g1Add (bytes1 (p, (a1 ()).2)) (bytes1 (b1 ())) && g1Add (bytes1 ((a1 ()).1, (a1 ()).2 + 1)) (bytes1 (b1 ())) &&
  g1Add (natToBE 64 (2 ^ 384 + (a1 ()).1) ++ fe (a1 ()).2) (bytes1 (b1 ())) && g1Add (bytes1 (a1 ())) (natToBE 64 (2 ^ 500) ++ fe 1) &&
  g1Add (bytes1 (a1 ())) (fe 0 ++ fe 2) && g1Add (bytes1 (a1 ())) (fe 1) && g1Add ByteArray.empty ByteArray.empty
#guard (g1AddBody (bytes1 (a1 ()) ++ bytes1 (b1 ()))).same (.output (bytes1 (multiple1 12 g1Generator)))
#guard g2Add (bytes2 (a2 ())) (bytes2 (b2 ())) && g2Add (bytes2 (a2 ())) (bytes2 (a2 ())) &&
  g2Add (bytes2 (a2 ())) (bytes2 ((a2 ()).1, Fp2.neg p (a2 ()).2)) && g2Add (natToBE 256 0) (bytes2 (b2 ())) &&
  g2Add (bytes2 (b2 ())) (natToBE 256 0) && g2Add (natToBE 256 0) (natToBE 256 0) && g2Add (bytes2 (out2 ())) (bytes2 (a2 ()))
#guard g2Add (bytes2 (⟨p, 0⟩, (a2 ()).2)) (bytes2 (b2 ())) && g2Add (bytes2 ((a2 ()).1, ⟨(a2 ()).2.c0, (a2 ()).2.c1 + 1⟩)) (bytes2 (b2 ())) &&
  g2Add (natToBE 64 (2 ^ 384) ++ (bytes2 (a2 ())).extract 64 256) (bytes2 (b2 ())) && g2Add (bytes2 (a2 ())) (fe 1)
#guard (g2AddBody (bytes2 (a2 ()) ++ bytes2 (b2 ()))).same (.output (bytes2 (multiple2 12 g2Generator)))
-- Decoding with the subgroup check agrees with the definition's verdicts.
#guard (decodeG1 (bytes1 (a1 ())) 0 true).isSome && (decodeG1 (bytes1 (out1 ())) 0 true).isNone &&
  (decodeG1 (bytes1 (out1 ())) 0 false).isSome &&
  (match decodeG1 (fe 0 ++ fe 0) 0 true with | some none => true | _ => false)
#guard (decodeG2 (bytes2 (a2 ())) 0 true).isSome && (decodeG2 (bytes2 (out2 ())) 0 true).isNone &&
  (decodeG2 (bytes2 (out2 ())) 0 false).isSome && (decodeG2 (natToBE 256 0) 0 true).isSome

#print axioms pushFp_size
#print axioms encodeG1_size
#print axioms encodeG2_size
#print axioms fixed_success
#print axioms runG1Add_success
#print axioms runG2Add_success

end EVMCleanroom.Precompiles.BLS12381.Fast
