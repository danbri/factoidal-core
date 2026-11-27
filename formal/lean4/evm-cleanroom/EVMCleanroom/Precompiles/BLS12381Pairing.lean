import EVMCleanroom.Precompiles.BLS12381
import EVMCleanroom.Precompiles.BLS12381Field
import EVMCleanroom.Precompiles.FastPairing

/-!
# BLS12-381 pairing check (0x0f) on the limb tower

The same contract as `BLS12381.runPairing` (EIP-2537), computed by `FastPairing` over
`BLS12381.baseField` (six 64-bit limbs, Montgomery form). `BLS12381.lean` with
`Pairing.lean` and `Tower.lean` stays the definition and the differential oracle.

Decoding, with the subgroup checks of both groups, is still `BLS12381.decodeG1` and
`BLS12381.decodeG2` (the definitional `[r]P = O`). Only the product check is replaced.

The Miller loop runs over the binary digits of `|x|` (weight six), so the Miller value is
the same field element as `Pairing.miller`. `FastPairing.finalExponentiation` computes the
cube of the value of `Pairing.finalExponentiation` (`hardPower = 3`, coprime to `r`), so
the verdict is the same.

Proved: gas accounting, the output length, the input-length rules. Not proved: the verdict
(guards below, the differential check `evm-pairingperf`, the published vectors).
Nothing is constant-time: the precompiles handle public data only.
-/

namespace EVMCleanroom.Precompiles.BLS12381Pairing

open BLS12381 (p r parameter baseField)

/-- An `Fp2` element in Montgomery limbs, and back. -/
def toLimbs (a : Fp2) : Fq2 U384 := Fq2.ofNat baseField.ofNat a
def ofLimbs (a : Fq2 U384) : Fp2 := Fq2.toNat baseField.toNat a

/-- `ξ = 1 + u`, with the Frobenius constants of `BLS12381.tower` converted once. -/
def towerParams : TowerParams U384 :=
  { xiNine := false
    frob1 := toLimbs BLS12381.tower.frob[1]!
    frob2 := toLimbs BLS12381.tower.frob[2]!
    frob3 := toLimbs BLS12381.tower.frob[3]!
    frob4 := toLimbs BLS12381.tower.frob[4]!
    frob5 := toLimbs BLS12381.tower.frob[5]! }

/-- The binary digits of `|x|` below its leading one: the Miller loop and the hard part. -/
def xDigits : List Digit := signedDigits parameter 0 (Nat.log2 parameter)

def fastCurve : FastCurve U384 :=
  { tower := towerParams, divide := false, loopDigits := xDigits, frobeniusSteps := false,
    negative := true, xDigits := xDigits, bnFamily := false }

/-- The fast final exponentiation gives this power of the value of `Pairing.finalExponentiation`. -/
def hardPower : Nat := 3

/-- A pair of finite points, in limbs. -/
def pairOf (a : Nat × Nat) (b : Fp2 × Fp2) : PairState U384 :=
  FastPairing.pairState baseField.ops (baseField.ofNat a.1) (baseField.ofNat a.2) (toLimbs b.1) (toLimbs b.2)

/-- Decode `count` pairs starting at `off`, as `BLS12381.decodePairs`. -/
def decodePairs (data : ByteArray) : Nat → Nat → List (PairState U384) → Option (List (PairState U384))
  | 0, _, acc => some acc
  | count+1, off, acc =>
    match BLS12381.decodeG1 data off true, BLS12381.decodeG2 data (off + 128) true with
    | some a, some b =>
      match a, b with
      | some a, some b => decodePairs data count (off + 384) (pairOf a b :: acc)
      | _, _ => decodePairs data count (off + 384) acc
    | _, _ => none

/-- The product of the Miller values, the final exponentiation and the verdict on limbs. -/
def millerProduct (pairs : List (PairState U384)) : Fq12 U384 :=
  FastPairing.millerProduct baseField.ops fastCurve pairs
def finalExponentiation (f : Fq12 U384) : Fq12 U384 :=
  FastPairing.finalExponentiation baseField.ops fastCurve f
def productIsOne (pairs : List (PairState U384)) : Bool :=
  FastPairing.productIsOne baseField.ops fastCurve pairs

def pairingBody (input : ByteArray) : Body :=
  match decodePairs input (input.size / 384) 0 [] with
  | none => .invalid
  | some pairs => .output (natToBE 32 (if productIsOne pairs then 1 else 0))

/-- Precompile 0x0f. -/
def runPairing (gas : Nat) (input : ByteArray) : Result :=
  if input.size = 0 ∨ input.size % 384 ≠ 0 then .failure
  else charge gas (BLS12381.pairingGas input.size) fun _ => pairingBody input

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful pairing check had a non-empty input of whole 384-byte pairs, cost
    exactly 37700 + 32600 per pair and returned exactly 32 bytes.
    Does not say: the verdict is correct (guards, differential check and vectors, not proved). -/
theorem runPairing_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runPairing gas input = .success out left) :
    input.size ≠ 0 ∧ input.size % 384 = 0 ∧ out.size = 32 ∧ left + BLS12381.pairingGas input.size = gas := by
  unfold runPairing at h
  split at h
  · cases h
  · rename_i hLen
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, by omega, ?_, hGas⟩
    simp only [pairingBody] at hBody
    split at hBody
    · exact Body.noConfusion hBody
    · exact Body.output.inj hBody ▸ natToBE_size _ _

/-- Kind: input-length rule.
    Says: an empty input, or one that is not a multiple of 384 bytes, fails at any gas.
    Does not say: anything about well-sized input. -/
theorem runPairing_bad_length (gas : Nat) (input : ByteArray) (h : input.size = 0 ∨ input.size % 384 ≠ 0) :
    runPairing gas input = .failure := by
  unfold runPairing
  exact if_pos h

/-- Kind: loop bound.
    Says: the price contains 32600 gas for every 384 bytes of input, and `pairingBody`
    decodes exactly `input.size / 384` pairs, so every pair that enters the shared Miller
    loop is paid for (`FastPairingProofs.bls_decodePairs_length` bounds the list).
    Does not say: how long a Miller loop takes. -/
theorem pairingGas_pays_pairs (size : Nat) : 32600 * (size / 384) ≤ BLS12381.pairingGas size := by
  simp only [BLS12381.pairingGas]; omega

/-- Kind: value of the empty product.
    Says: with no finite pair the verdict is one without any field arithmetic.
    Does not say: anything about a non-empty product. -/
theorem productIsOne_nil : productIsOne [] = true := rfl

/-! ### Build-time guards against the `Nat` path -/

private def g1 : Nat × Nat := BLS12381.g1Generator
private def g2 : Fp2 × Fp2 := BLS12381.g2Generator
private def mul1 (k : Nat) : Nat × Nat :=
  (Curve.toAffine BLS12381.field (Curve.mul BLS12381.field k (Curve.ofAffine BLS12381.field g1.1 g1.2))).getD (0, 0)
private def mul2 (k : Nat) : Fp2 × Fp2 :=
  (Curve.toAffine BLS12381.field2 (Curve.mul BLS12381.field2 k (Curve.ofAffine BLS12381.field2 g2.1 g2.2))).getD
    (Fp2.zero, Fp2.zero)
private def neg1 (a : Nat × Nat) : Nat × Nat := (a.1, Fp.neg p a.2)

private def flat (g : Fq12 U384) : Fp12 := Fq12.toFlat baseField.toNat g
private def lift (a : Fp12) : Fq12 U384 := Fq12.ofFlat baseField.ofNat a
private def oldEasyOf (f : Fp12) : Fp12 :=
  let T := BLS12381.tower
  let easy1 := Fp12.mul T (Fp12.conj T f) (Fp12.inv T f)
  Fp12.mul T (Fp12.frobenius T (Fp12.frobenius T easy1)) easy1

private def oldSample : Fp12 := Pairing.miller BLS12381.curve g1 g2
private def oldOther : Fp12 := Fp12.frobenius BLS12381.tower (Fp12.sqr BLS12381.tower oldSample)
private def sample : Fq12 U384 := lift oldSample
private def other : Fq12 U384 := lift oldOther
private def oldEasy : Fp12 := oldEasyOf oldSample
private def easy : Fq12 U384 := FastPairing.easyPart baseField.ops fastCurve sample
private def a2 : Fp2 := oldSample.c1
private def b2 : Fp2 := oldSample.c4
private def c2 : Fp2 := oldSample.c5

-- The limb field and the digits.
#guard baseField.toNat (baseField.ofNat 5) == 5 && baseField.toNat baseField.one == 1
#guard digitsValue xDigits 1 == Int.ofNat parameter
-- Fq2 against Fp2.
#guard ofLimbs (Fq2.mul baseField.ops (toLimbs a2) (toLimbs b2)) == Fp2.mul p a2 b2
#guard ofLimbs (Fq2.sqr baseField.ops (toLimbs a2)) == Fp2.sqr p a2
#guard ofLimbs (Fq2.inv baseField.ops (toLimbs a2)) == Fp2.inv p a2
#guard ofLimbs (Fq2.mulXi baseField.ops false (toLimbs a2)) == Fp2.mul p a2 ⟨1, 1⟩
-- Fq12 against the flat Fp12: product, square, inverse, Frobenius, conjugate, sparse product.
#guard flat sample == oldSample
#guard flat (Fq12.mul baseField.ops towerParams sample other) == Fp12.mul BLS12381.tower oldSample oldOther
#guard flat (Fq12.sqr baseField.ops towerParams sample) == Fp12.sqr BLS12381.tower oldSample
#guard flat (Fq12.inv baseField.ops towerParams sample) == Fp12.inv BLS12381.tower oldSample
#guard flat (Fq12.frobenius baseField.ops towerParams sample) == Fp12.frobenius BLS12381.tower oldSample
#guard flat (Fq12.conj baseField.ops sample) == Fp12.conj BLS12381.tower oldSample
#guard flat (Fq12.mulLineM baseField.ops towerParams sample (toLimbs a2) (toLimbs b2) (toLimbs c2)) ==
  Fp12.mul BLS12381.tower oldSample ⟨a2, Fp2.zero, b2, c2, Fp2.zero, Fp2.zero⟩
-- The easy part, then cyclotomic squaring and the power by |x| on its result.
#guard flat easy == oldEasy
#guard flat (Fq12.cyclotomicSqr baseField.ops towerParams easy) == Fp12.sqr BLS12381.tower oldEasy
#guard flat (FastPairing.expX baseField.ops fastCurve easy) == Fp12.pow BLS12381.tower oldEasy parameter
-- The hard part is the cube of the old hard part.
#guard flat (FastPairing.hardPart baseField.ops fastCurve easy) ==
  Fp12.pow BLS12381.tower (Pairing.hardPart BLS12381.curve oldEasy) hardPower
#guard Nat.gcd hardPower r == 1
-- The Miller value is the old one, for one pair and for a product with shared squarings.
#guard flat (millerProduct [pairOf g1 g2]) == oldSample
#guard flat (millerProduct [pairOf g1 g2, pairOf (mul1 5) (mul2 7)]) ==
  Fp12.mul BLS12381.tower oldSample (Pairing.miller BLS12381.curve (mul1 5) (mul2 7))
-- The verdict: e(P, Q)·e(−P, Q) = 1, a product that is not one, the empty product computed
-- in full, and bilinearity in each argument.
#guard productIsOne [pairOf g1 g2, pairOf (neg1 g1) g2]
#guard !productIsOne [pairOf g1 g2]
#guard Fq12.isOne baseField.ops (finalExponentiation (millerProduct []))
#guard productIsOne [pairOf (mul1 5) g2, pairOf (neg1 (mul1 2)) g2, pairOf (neg1 (mul1 3)) g2]
#guard productIsOne [pairOf g1 (mul2 5), pairOf (neg1 g1) (mul2 2), pairOf (neg1 g1) (mul2 3)]
-- The body: the empty input fails.
#guard (match runPairing 1000000 ByteArray.empty with | .failure => true | _ => false)

#print axioms runPairing_success
#print axioms runPairing_bad_length
#print axioms pairingGas_pays_pairs
#print axioms productIsOne_nil

end EVMCleanroom.Precompiles.BLS12381Pairing
