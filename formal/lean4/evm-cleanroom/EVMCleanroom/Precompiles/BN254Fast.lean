import EVMCleanroom.Precompiles.BN254
import EVMCleanroom.Precompiles.BN254Field
import EVMCleanroom.Precompiles.LimbBytes
import EVMCleanroom.Precompiles.CurveFast

/-!
# alt_bn128 addition and scalar multiplication on limbs (0x06, 0x07)

The same contract as `BN254.runAdd` and `BN254.runMul` (EIP-196, prices of
EIP-1108), computed on the four-limb Montgomery field `BN254.baseField`:

* coordinates are read straight into limbs and compared with `p` by a borrow;
* the curve equation is checked in Montgomery form;
* the addition is one mixed Jacobian addition, the multiplication a windowed
  one (`Curve.windowMul`: a table of sixteen multiples, four doublings per four
  scalar bits). The scalar is used as given, up to `2^256 − 1`, as in the
  definition;
* one field inversion per call (the `Nat` Euclid of `Mont256.inv`), none when
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
the bit length of the scalar.
-/

namespace EVMCleanroom.Precompiles.BN254.Fast

/-- The base field in Montgomery form. -/
def M : Mont256 := BN254.baseField
def ops : FieldOps U256 := Mont256.ops BN254.baseField

/-- The curve coefficient 3 in Montgomery form. -/
def three : U256 := M.ofNat 3

/-- A decoded `G1` point in Montgomery form: `none` is the point at infinity. -/
abbrev Affine := Option (U256 × U256)

@[inline] def onCurve (x y : U256) : Bool :=
  U256.beq (M.sqr y) (M.add (M.mul (M.sqr x) x) three)

/-- Decode a `G1` point at `off`; the outer `none` is invalid input. -/
def decodeG1 (data : ByteArray) (off : Nat) : Option Affine :=
  let x := U256.ofBE data off
  let y := U256.ofBE data (off + 32)
  if !(U256.lt x M.n && U256.lt y M.n) then none
  else if x.isZero && y.isZero then some none
  else
    let xm := M.toMont x
    let ym := M.toMont y
    if onCurve xm ym then some (some (xm, ym)) else none

def toJacobian : Affine → JPoint U256
  | none => Curve.infinity ops
  | some (x, y) => Curve.ofAffine ops x y

def encodeG1 (point : JPoint U256) : ByteArray :=
  match Curve.toAffineFast ops point with
  | none => natToBE 64 0
  | some (x, y) => U256.pushBE (U256.pushBE ByteArray.empty (M.fromMont x)) (M.fromMont y)

theorem encodeG1_size (point : JPoint U256) : (encodeG1 point).size = 64 := by
  unfold encodeG1
  split
  · exact natToBE_size _ _
  · simp [U256.pushBE_size]

def addPoints (a b : Affine) : JPoint U256 :=
  match b with
  | none => toJacobian a
  | some (x, y) => Curve.addMixed ops (toJacobian a) x y

def mulPoint (k : Nat) : Affine → JPoint U256
  | none => Curve.infinity ops
  | some (x, y) => Curve.windowMul ops k x y

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

/-- Kind: output contract and accounting.
    Says: a successful addition on limbs costs exactly 150 gas and returns exactly 64 bytes.
    Does not say: the bytes encode the group sum, or equal those of `BN254.runAdd`
    (differential runs and vectors, not proved). -/
theorem runAdd_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runAdd gas input = .success out left) : out.size = 64 ∧ left + 150 = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
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
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
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
      exact Curve.windowMul_zero ops x y

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
private def p5 : Nat × Nat := multiple 5
private def p7 : Nat × Nat := multiple 7

-- The Montgomery parameters belong to the modulus of the definition.
#guard M.n.toNat == p && M.toNat three == 3 && M.toNat M.one == 1
-- Addition: generic, doubling, inverse points, infinity on either side and on both.
#guard addAgrees (addInput p5 p7) && addAgrees (addInput p5 p5) && addAgrees (addInput g g)
#guard addAgrees (addInput p5 (p5.1, p - p5.2)) && addAgrees (addInput (0, 0) p7) &&
  addAgrees (addInput p7 (0, 0)) && addAgrees (addInput (0, 0) (0, 0))
-- The result bytes are the known multiples.
#guard (addBody (addInput p5 p7)).same (.output (pointBytes (multiple 12)))
-- Invalid input: a coordinate equal to or above p, a point off the curve, (0, y), short and long input.
#guard addAgrees (addInput (p, 2) g) && addAgrees (addInput (1, p + 2) g) && addAgrees (addInput g (1, 3)) &&
  addAgrees (addInput (0, 1) g) && addAgrees (addInput g (2 ^ 256 - 1, 2 ^ 256 - 1)) &&
  addAgrees (word 1) && addAgrees ByteArray.empty && addAgrees (addInput p5 p7 ++ word 99) &&
  addAgrees ((addInput p5 p7).extract 0 127)
#guard !(match addBody (addInput g (1, 3)) with | .invalid => false | _ => true)
-- Multiplication: scalars 0, 1, 2, r − 1, r, r + 1, 2^256 − 1 and a 256-bit one; infinity; invalid input.
#guard mulAgrees (mulInput p5 0) && mulAgrees (mulInput p5 1) && mulAgrees (mulInput p5 2) &&
  mulAgrees (mulInput p7 (r - 1)) && mulAgrees (mulInput p7 r) && mulAgrees (mulInput p7 (r + 1))
#guard mulAgrees (mulInput g (2 ^ 256 - 1)) &&
  mulAgrees (mulInput p5 0xf0e1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdeffedcba9876543210) &&
  mulAgrees (mulInput p7 0x10000000000000000) && mulAgrees (mulInput p7 16)
#guard mulAgrees (mulInput (0, 0) 5) && mulAgrees (mulInput (1, 3) 5) && mulAgrees (mulInput (p, 2) 5) &&
  mulAgrees (word 1 ++ word 2) && mulAgrees ByteArray.empty && mulAgrees (mulInput p5 7 ++ word 1)
#guard (mulBody (mulInput g 12)).same (.output (pointBytes (multiple 12)))
#guard (match runAdd 149 (addInput g g) with | .failure => true | _ => false)
#guard (match runMul 5999 (mulInput g 2) with | .failure => true | _ => false)

#print axioms encodeG1_size
#print axioms runAdd_success
#print axioms runMul_success
#print axioms run_reads_prefix
#print axioms mulPoint_trivial

end EVMCleanroom.Precompiles.BN254.Fast
