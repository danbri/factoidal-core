import EVMCleanroom.Precompiles.BN254
import EVMCleanroom.Precompiles.BN254Field
import EVMCleanroom.Precompiles.LimbBytes
import EVMCleanroom.Precompiles.CurveFast
import EVMCleanroom.Precompiles.LimbInverse
import EVMCleanroom.Precompiles.LimbSquare

/-!
# alt_bn128 addition and scalar multiplication on limbs (0x06, 0x07)

The same contract as `BN254.runAdd` and `BN254.runMul` (EIP-196, prices of
EIP-1108), computed on the four-limb Montgomery field `BN254.baseField`:

* coordinates are read straight into limbs and compared with `p` by a borrow;
* the curve equation is checked in Montgomery form;
* the addition is the affine chord-and-tangent rule (one inversion, three
  multiplications); the multiplication reduces
  the scalar (given up to `2^256 − 1`) modulo the group order, splits it along
  the endomorphism `φ(x, y) = (βx, y)` into two parts of about 127 bits and
  runs one doubling chain of that length with two tables of sixteen multiples
  (see "Scalar multiplication with the endomorphism" below);
* one field inversion per call (`Mont256.invFast` of `LimbInverse.lean`), none when
  the result already has `Z = 1` (an operand at infinity, scalar one).

`BN254.lean` stays the definition. This module is tested against it, not
proved equal: group laws are not proved anywhere. Evidence: the guards below
(infinity on either side, equal and inverse points, scalars `0, 1, 2, r − 1,
r, r + 1, 2^256 − 1`, invalid encodings), the differential run of `evm-blsops`
over pseudo-random valid and invalid inputs, and the published vectors
through the router.

Proved: gas accounting, output lengths, prefix-only input handling (the
statements of `BN254.runAdd_success`, `runMul_success`, `run_reads_prefix`).

Not constant-time: the window loop branches on scalar digits and its length is
the bit length of the scalar parts.
-/

namespace EVMCleanroom.Precompiles.BN254.Fast

/-- The base field in Montgomery form. -/
def M : Mont256 := BN254.baseField

/-! The field operations as plain functions. The Montgomery routines of `Montgomery.lean`
are marked for inlining; here each is instantiated once for this modulus, and the curve
code calls these (inlining them at every use made the compiler exceed its step limit). -/

def fmul (a b : U256) : U256 := BN254.baseField.mul a b
def fsqr (a : U256) : U256 := BN254.baseField.sqrFast a
def fadd (a b : U256) : U256 := BN254.baseField.add a b
def fsub (a b : U256) : U256 := BN254.baseField.sub a b
def fneg (a : U256) : U256 := BN254.baseField.neg a
def finv (a : U256) : U256 := BN254.baseField.invFast a
def toMont (a : U256) : U256 := BN254.baseField.toMont a
def fromMont (a : U256) : U256 := BN254.baseField.fromMont a

def ops : FieldOps U256 where
  zero := U256.zero
  one := BN254.baseField.one
  add := fadd
  sub := fsub
  mul := fmul
  sqr := fsqr
  neg := fneg
  inv := finv
  isZero := U256.isZero
  eq := U256.beq

/-- The curve coefficient 3 in Montgomery form. -/
def three : U256 := M.ofNat 3

/-- A decoded `G1` point in Montgomery form: `none` is the point at infinity. -/
abbrev Affine := Option (U256 × U256)

@[inline] def onCurve (x y : U256) : Bool :=
  U256.beq (fsqr y) (fadd (fmul (fsqr x) x) three)

/-- Decode a `G1` point at `off`; the outer `none` is invalid input. -/
def decodeG1 (data : ByteArray) (off : Nat) : Option Affine :=
  let x := U256.ofBE data off
  let y := U256.ofBE data (off + 32)
  if !(U256.lt x M.n && U256.lt y M.n) then none
  else if x.isZero && y.isZero then some none
  else
    let xm := toMont x
    let ym := toMont y
    if onCurve xm ym then some (some (xm, ym)) else none

/- The proofs below treat decoding as opaque; unfolding it would expose the limb arithmetic. -/
attribute [irreducible] decodeG1

def toJacobian : Affine → JPoint U256
  | none => Curve.infinity ops
  | some (x, y) => Curve.ofAffine ops x y

def encodeG1 (point : JPoint U256) : ByteArray :=
  match Curve.toAffineFast ops point with
  | none => natToBE 64 0
  | some (x, y) => U256.pushBE (U256.pushBE ByteArray.empty (fromMont x)) (fromMont y)

theorem encodeG1_size (point : JPoint U256) : (encodeG1 point).size = 64 := by
  unfold encodeG1
  split
  · exact natToBE_size _ _
  · simp [U256.pushBE_size]

def addPoints (a b : Affine) : JPoint U256 :=
  match a, b with
  | none, _ => toJacobian b
  | _, none => toJacobian a
  | some first, some second => Curve.addAffine ops first.1 first.2 second.1 second.2

/-! ### Scalar multiplication with the endomorphism

`φ(x, y) = (βx, y)` is an endomorphism of the curve (`β³ = 1`), and on the group, which
has prime order `r`, it is the multiplication by `λ = 36x⁴ − 1` (`λ² + λ + 1 ≡ 0 mod r`).
A scalar is reduced modulo `r` and written as `k₁ + k₂λ` with `|k₁|, |k₂|` of about 127
bits (Gallant, Lambert, Vanstone, "Faster point multiplication on elliptic curves with
efficient endomorphisms", 2001: rounding against the short lattice basis `(a₁, b₁)`,
`(a₂, b₂)` of the vectors with `a + bλ ≡ 0 mod r`). Then `[k]P = [k₁]P + [k₂]φ(P)` with one
doubling chain of half the length; the table of `φ(P)` is the table of `P` with every `x`
multiplied by `β`, and a negative part negates `y`.

Not proved: that `φ` is the multiplication by `λ`, or the splitting identity (guards on
the constants and on sample scalars below; `evm-blsops` checks `k₁ + k₂λ ≡ k (mod r)` and
the sizes of the parts on a pseudo-random walk, and compares whole results with the
definition). The window count is taken from the actual sizes of the parts, so the result
does not depend on a size bound. -/

def lambdaNat : Nat := 21888242871839275217838484774961031246154997185409878258781734729429964517155
def betaNat : Nat := 21888242871839275220042445260109153167277707414472061641714758635765020556616
def beta : U256 := M.ofNat betaNat
/-- The lattice basis `(glvA1, −glvB1)`, `(glvA2, glvB2)`; its determinant is `r`. -/
def glvA1 : Nat := 147946756881789319000765030803803410728
def glvB1 : Nat := 9931322734385697763
def glvA2 : Nat := 9931322734385697763
def glvB2 : Nat := 147946756881789319010696353538189108491

/-- `(k₁, k₂)` with `k₁ + k₂·λ ≡ k (mod r)` and both parts short. -/
def glvSplit (k : Nat) : Int × Int :=
  let m := k % r
  let c1 := (2 * m * glvB2 + r) / (2 * r)
  let c2 := (2 * m * glvB1 + r) / (2 * r)
  (Int.ofNat m - Int.ofNat (c1 * glvA1) - Int.ofNat (c2 * glvA2),
   Int.ofNat (c1 * glvB1) - Int.ofNat (c2 * glvB2))

/-- `[k](x, y)` for a curve point. -/
def mulGlv (k : Nat) (x y : U256) : JPoint U256 :=
  if k % r = 0 then Curve.infinity ops
  else
    let parts := glvSplit k
    let first := Curve.table16 ops x (if parts.1 < 0 then fneg y else y)
    let flip := decide (parts.1 < 0) != decide (parts.2 < 0)
    let second := first.map fun point : JPoint U256 =>
      ⟨fmul beta point.x, if flip then fneg point.y else point.y, point.z⟩
    Curve.strausLoop ops (#[(parts.1.natAbs, first), (parts.2.natAbs, second)])
      (Curve.windowCount 4 (max parts.1.natAbs parts.2.natAbs)) (Curve.infinity ops)

def mulPoint (k : Nat) : Affine → JPoint U256
  | none => Curve.infinity ops
  | some (x, y) => mulGlv k x y

def addBody (data : ByteArray) : Body :=
  match decodeG1 data 0, decodeG1 data 64 with
  | some a, some b => .output (encodeG1 (addPoints a b))
  | _, _ => .invalid

def mulBody (data : ByteArray) : Body :=
  match decodeG1 data 0 with
  | some a => .output (encodeG1 (mulPoint (beNat data 64 32) a))
  | none => .invalid

/-- Precompile 0x06 on limbs. -/
def runAdd (gas : Nat) (input : ByteArray) : Result :=
  charge gas 150 fun _ => addBody (readPadded input 0 128)

/-- Precompile 0x07 on limbs. -/
def runMul (gas : Nat) (input : ByteArray) : Result :=
  charge gas 6000 fun _ => mulBody (readPadded input 0 96)

/-- Shared shape of the two operations: success has the exact price and the body's bytes. -/
theorem charged_success (price gas : Nat) (out : ByteArray) (left : Nat) (body : Body)
    (h : charge gas price (fun _ => body) = .success out left) : body = .output out ∧ left + price = gas :=
  charge_success _ _ _ _ _ h

/-- Kind: output contract and accounting.
    Says: a successful addition on limbs costs exactly 150 gas and returns exactly 64 bytes.
    Does not say: the bytes encode the group sum, or equal those of `BN254.runAdd`
    (differential runs and vectors, not proved). -/
theorem runAdd_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runAdd gas input = .success out left) : out.size = 64 ∧ left + 150 = gas := by
  have ⟨hBody, hGas⟩ := charged_success 150 gas out left (addBody (readPadded input 0 128)) h
  refine ⟨?_, hGas⟩
  simp only [addBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG1_size _
  · exact Body.noConfusion hBody

/-- Kind: output contract and accounting.
    Says: a successful multiplication on limbs costs exactly 6000 gas and returns exactly 64 bytes.
    Does not say: the bytes encode the scalar multiple, or equal those of `BN254.runMul`
    (differential runs and vectors, not proved). -/
theorem runMul_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runMul gas input = .success out left) : out.size = 64 ∧ left + 6000 = gas := by
  have ⟨hBody, hGas⟩ := charged_success 6000 gas out left (mulBody (readPadded input 0 96)) h
  refine ⟨?_, hGas⟩
  simp only [mulBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG1_size _
  · exact Body.noConfusion hBody

/-- Kind: input-length handling.
    Says: addition depends only on the zero-padded first 128 bytes, multiplication on
    the first 96.
    Does not say: anything about what those bytes mean. -/
theorem run_reads_prefix (gas : Nat) (x y : ByteArray) :
    (readPadded x 0 128 = readPadded y 0 128 → runAdd gas x = runAdd gas y) ∧
    (readPadded x 0 96 = readPadded y 0 96 → runMul gas x = runMul gas y) := by
  constructor <;> intro h <;> simp [runAdd, runMul, h]

/-- Kind: identity handling.
    Says: a scalar multiple of the point at infinity, and the multiple by zero of any
    point, is the point at infinity without entering a loop.
    Does not say: anything for other operands. -/
theorem mulPoint_trivial (k : Nat) (a : Affine) : mulPoint k none = Curve.infinity ops ∧
    mulPoint 0 a = Curve.infinity ops := by
  constructor
  · rfl
  · cases a with
    | none => rfl
    | some point =>
      obtain ⟨x, y⟩ := point
      show mulGlv 0 x y = Curve.infinity ops
      simp [mulGlv]

/-! ### Guards against the `Nat` definition -/

private def word (n : Nat) : ByteArray := natToBE 32 n
private def g : Nat × Nat := (1, 2)
private def multiple (k : Nat) : Nat × Nat :=
  (Curve.toAffine field (Curve.mul field k (Curve.ofAffine field 1 2))).getD (0, 0)
private def pointBytes (point : Nat × Nat) : ByteArray := word point.1 ++ word point.2
private def addInput (a b : Nat × Nat) : ByteArray := pointBytes a ++ pointBytes b
private def mulInput (a : Nat × Nat) (k : Nat) : ByteArray := pointBytes a ++ word k
private def addAgrees (input : ByteArray) : Bool :=
  (runAdd 1000 input).same (BN254.runAdd 1000 input)
private def mulAgrees (input : ByteArray) : Bool :=
  (runMul 10000 input).same (BN254.runMul 10000 input)

-- The Montgomery parameters belong to the modulus of the definition.
#guard M.n.toNat == p && M.toNat three == 3 && M.toNat M.one == 1
#guard M.toNat (fmul (M.ofNat (p - 5)) (M.ofNat (p - 7))) == 35 && M.toNat (finv (M.ofNat 7)) == Fp.inv p 7 &&
  M.toNat (fsub (M.ofNat 3) (M.ofNat 5)) == p - 2 && (fromMont (toMont (U256.ofNat 12345))).toNat == 12345
-- The limb inverse: the unverified candidate is the inverse of the definition (254 bits fit 255).
#guard M.n.toNat < 2 ^ 255 &&
  [1, 2, 3, 7, p - 1, p - 2, (p - 1) / 2, (p + 1) / 2, 2 ^ 64, 2 ^ 253, 0x1234567890abcdef1234567890abcdef % p].all fun a =>
    M.toNat (M.invCandidate (M.ofNat a)) == Fp.inv p a && M.toNat (finv (M.ofNat a)) == Fp.inv p a
#guard (finv U256.zero).isZero
-- The field square through the dedicated squaring is the product with itself.
#guard [0, 1, 2, p - 1, p - 2, (p - 1) / 2, 2 ^ 253, 2 ^ 64 - 1, 0xfedcba9876543210f0e1d2c3b4a5968778695a4b3c2d1e % p].all fun a =>
  M.toNat (fsqr (M.ofNat a)) == a * a % p && (fsqr (M.ofNat a)).toNat == (M.sqr (M.ofNat a)).toNat
-- Addition: generic, doubling, inverse points, infinity on either side and on both.
#guard addAgrees (addInput (multiple 5) (multiple 7)) && addAgrees (addInput (multiple 5) (multiple 5)) && addAgrees (addInput g g)
#guard addAgrees (addInput (multiple 5) ((multiple 5).1, p - (multiple 5).2)) && addAgrees (addInput (0, 0) (multiple 7)) &&
  addAgrees (addInput (multiple 7) (0, 0)) && addAgrees (addInput (0, 0) (0, 0))
-- The result bytes are the known multiples.
#guard (addBody (addInput (multiple 5) (multiple 7))).same (.output (pointBytes (multiple 12)))
-- Invalid input: a coordinate equal to or above p, a point off the curve, (0, y), short and long input.
#guard addAgrees (addInput (p, 2) g) && addAgrees (addInput (1, p + 2) g) && addAgrees (addInput g (1, 3)) &&
  addAgrees (addInput (0, 1) g) && addAgrees (addInput g (2 ^ 256 - 1, 2 ^ 256 - 1)) &&
  addAgrees (word 1) && addAgrees ByteArray.empty && addAgrees (addInput (multiple 5) (multiple 7) ++ word 99) &&
  addAgrees ((addInput (multiple 5) (multiple 7)).extract 0 127)
#guard !(match addBody (addInput g (1, 3)) with | .invalid => false | _ => true)
-- The endomorphism constants: β³ = 1, λ² + λ + 1 ≡ 0, λ = 36x⁴ − 1, the basis vectors lie in the lattice, its
-- determinant is r, and φ(G) = [λ]G on the definition's arithmetic.
#guard betaNat ^ 3 % p == 1 && betaNat != 1 && (lambdaNat ^ 2 + lambdaNat + 1) % r == 0 &&
  lambdaNat == (36 * parameter ^ 4 - 1) % r
#guard (glvA1 + (r - glvB1) * lambdaNat) % r == 0 && (glvA2 + glvB2 * lambdaNat) % r == 0 &&
  glvA1 * glvB2 + glvA2 * glvB1 == r
#guard (Fp.mul p betaNat 1, 2) == multiple lambdaNat
private def splitOk (k : Nat) : Bool :=
  let parts := glvSplit k
  (parts.1 + parts.2 * Int.ofNat lambdaNat - Int.ofNat k) % Int.ofNat r == 0 &&
    parts.1.natAbs < 2 ^ 128 && parts.2.natAbs < 2 ^ 128
#guard [0, 1, 2, r - 1, r, r + 1, r / 2, lambdaNat, lambdaNat + 1, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 127, 2 ^ 128 + 1,
  0xf0e1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdeffedcba9876543210].all splitOk
#guard (List.range 300).all fun i => splitOk ((i * i + 3) * (2 ^ 250 - 2 ^ (i % 250) + 7 * i))
-- Multiplication: scalars 0, 1, 2, r − 1, r, r + 1, 2^256 − 1 and a 256-bit one; infinity; invalid input.
#guard mulAgrees (mulInput (multiple 5) 0) && mulAgrees (mulInput (multiple 5) 1) && mulAgrees (mulInput (multiple 5) 2) &&
  mulAgrees (mulInput (multiple 7) (r - 1)) && mulAgrees (mulInput (multiple 7) r) && mulAgrees (mulInput (multiple 7) (r + 1))
#guard mulAgrees (mulInput g (2 ^ 256 - 1)) &&
  mulAgrees (mulInput (multiple 5) 0xf0e1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdeffedcba9876543210) &&
  mulAgrees (mulInput (multiple 7) 0x10000000000000000) && mulAgrees (mulInput (multiple 7) 16) &&
  mulAgrees (mulInput (multiple 5) lambdaNat) && mulAgrees (mulInput (multiple 7) (2 * r)) && mulAgrees (mulInput g (r / 2)) &&
  mulAgrees (mulInput (multiple 5) (2 ^ 127)) && mulAgrees (mulInput (multiple 7) glvB2)
#guard mulAgrees (mulInput (0, 0) 5) && mulAgrees (mulInput (1, 3) 5) && mulAgrees (mulInput (p, 2) 5) &&
  mulAgrees (word 1 ++ word 2) && mulAgrees ByteArray.empty && mulAgrees (mulInput (multiple 5) 7 ++ word 1)
#guard (mulBody (mulInput g 12)).same (.output (pointBytes (multiple 12)))
#guard (match runAdd 149 (addInput g g) with | .failure => true | _ => false)
#guard (match runMul 5999 (mulInput g 2) with | .failure => true | _ => false)

#print axioms encodeG1_size
#print axioms charged_success
#print axioms runAdd_success
#print axioms runMul_success
#print axioms run_reads_prefix
#print axioms mulPoint_trivial

end EVMCleanroom.Precompiles.BN254.Fast
