import EVMCleanroom.Precompiles.BN254
import EVMCleanroom.Precompiles.BN254Field
import EVMCleanroom.Precompiles.FastPairing
import EVMCleanroom.Precompiles.QuadLimb

/-!
# alt_bn128 pairing check (0x08) on the limb tower

The same contract as `BN254.runPairing` (EIP-197, prices of EIP-1108), computed by
`FastPairing` over `BN254.baseField` (four 64-bit limbs, Montgomery form). `BN254.lean`
with `Pairing.lean` and `Tower.lean` stays the definition and the differential oracle.

Decoding is the old one except for the `G2` subgroup check: canonical coordinates, the
all-zero encoding of infinity and the curve equations are checked on natural numbers
exactly as in `BN254.decodeG1` and `BN254.decodeG2`.

## The `G2` subgroup check

`BN254.decodeG2` accepts a point `Q` of the twist `E'(Fp2)` when `[r]Q = O` (the
definition: a 254-bit scalar multiplication). Here the test is

    ψ(Q) = [6x²]Q,

with `ψ` the untwist-Frobenius-twist endomorphism (`FastPairing.psiX`, `psiY`) and `x` the
curve parameter: one 127-bit signed-digit multiplication.

Source: El Housni, Guillevic and Piellard, "Co-factor clearing and subgroup membership
testing on pairing-friendly curves", AFRICACRYPT 2022, the section on `G2` membership for
BN curves. The exact statement relied on: for a point `Q` of `E'(Fp2)`, `Q` has order
dividing `r` if and only if `ψ(Q) = [t − 1]Q`, where `t = 6x² + 1` is the trace of
Frobenius of `E` over `Fp`. The argument, for the record:

* `ψ` satisfies the characteristic equation of the Frobenius of `E`, `ψ² − [t]ψ + [p] = 0`,
  on `E'`. If `ψ(Q) = [t − 1]Q`, substituting gives `[(t−1)² − t(t−1) + p]Q = [p + 1 − t]Q = [r]Q = O`.
* Conversely the points of order `r` of `E'(Fp2)` map to the `p`-eigenspace of Frobenius in
  `E[r]`, so `ψ(Q) = [p]Q = [t − 1]Q` for them (`p ≡ t − 1` modulo `r`).
* `#E'(Fp2) = r·(2p − r)` and `gcd(r, 2p − r) = 1`, so the points with `[r]Q = O` are exactly
  the subgroup of order `r`.

**This criterion is not proved here.** It is consensus-critical: accepting a point outside
the subgroup, or refusing one inside, is a consensus fault. What is proved is only the
arithmetic of the first step for this curve (`p + 1 = r + (6x² + 1)` and the recoding of
`6x²`, in `FastPairingProofs`). The evidence for the rest is by test:

* build-time guards below: the generator and a multiple are accepted; a point of the twist
  outside the subgroup and a point of order 10069 (a factor of the cofactor) are refused,
  as by the definition; the characteristic equation holds on the outside point (on the
  `Nat` path); the fast scalar multiplication agrees with `Curve.mul` on it;
* the run-time differential check `evm-pairingperf` compares the test with `[r]Q = O` on
  multiples of the generator and on many points of the twist outside the subgroup (random
  `x`, solved for `y` on the `Nat` path; the cofactor has 254 bits, so a random point of
  the twist is outside), and on points of small order;
* the published pairing vectors, with their failure cases.

### The shorter relation (measured, not routed)

The same paper gives a relation with a scalar of half the length:

    [x+1]Q + ψ([x]Q) + ψ²([x]Q) = ψ³([2x]Q)

(`inG2Short`, `FastPairing.psiShortRelation`). It is about 0.08 ms per point faster than the
routed test. Its soundness needs one more published fact, the order `r·(2p − r)` of
`E'(Fp2)`: with `ψ² = [t]ψ − [p]` the left side minus the right is `([a] + [b]ψ)Q` for two
integers `a`, `b`; composing with `[a] + [b]([t] − ψ)` gives `[a² + abt + b²p]Q = O`, and that
integer is a multiple of `r` whose greatest common divisor with `r·(2p − r)` is `r`
(`FastPairingProofs.bn_short_relation_arithmetic`), so `[r]Q = O`. It is compared with the
definition and with the routed test on every input of the differential check and in the
guards below. The precompile uses `inG2`; routing `inG2Short` is a one-line change in
`decodeG2` for whoever decides that the extra assumption is acceptable.

## Final value

`FastPairing.finalExponentiation` computes the power `2x(6x²+3x+1)` of the value of
`Pairing.finalExponentiation` (`hardPower`, coprime to `r`), so the verdict is the same.

Proved: gas accounting, the output length, the input-length rule, the number of pairs
entering the Miller loop. Not proved: the verdict (guards, differential check, vectors).
Nothing is constant-time: the precompiles handle public data only.
-/

namespace EVMCleanroom.Precompiles.BN254Pairing

open BN254 (p r parameter baseField)

/-- The quadratic extension on flat limbs with `ξ = 9 + u`: the dictionary every generic
    function below is specialised on. -/
local notation "quad" => Quad256.ops baseField true

/-- An `Fp2` element in Montgomery limbs, and back. -/
def toLimbs (a : Fp2) : Quad256 := Quad256.ofFp2 baseField a
def ofLimbs (a : Quad256) : Fp2 := Quad256.toFp2 baseField a

/-- The Frobenius constants of `BN254.tower`, converted once. -/
def towerParams : TowerParams Quad256 :=
  { frob1 := toLimbs BN254.tower.frob[1]!
    frob2 := toLimbs BN254.tower.frob[2]!
    frob3 := toLimbs BN254.tower.frob[3]!
    frob4 := toLimbs BN254.tower.frob[4]!
    frob5 := toLimbs BN254.tower.frob[5]! }

/-- The Miller loop scalar `6x + 2`. -/
def loopScalar : Nat := 6 * parameter + 2

/-- `x = xPos − xNeg` in non-adjacent form (24 non-zero digits; the binary form has 28). -/
def xPos : Nat := 0x450a14044a890a01
def xNeg : Nat := 0x20815000200010

/-- The scalar of the subgroup test, `6x² = t − 1`. -/
def psiScalar : Nat := 6 * parameter ^ 2
/-- `6x² = psiPos − psiNeg` in non-adjacent form (40 non-zero digits; the binary form has 70). -/
def psiPos : Nat := 0x80500249000082000040a08408810148
def psiNeg : Nat := 0x110280001148280408020a0120040402

/-- `6x + 2 = loopPos − loopNeg` in non-adjacent form (22 non-zero digits; the binary form has 37). -/
def loopPos : Nat := 0x22002004200804028
def loopNeg : Nat := 0x82889008420a0480

def loopDigits : List Digit := signedDigits loopPos loopNeg (Nat.log2 loopPos)
def xDigits : List Digit := signedDigits xPos xNeg (Nat.log2 xPos)
def psiDigits : List Digit := signedDigits psiPos psiNeg (Nat.log2 psiPos)

def fastCurve : FastCurve Quad256 :=
  { tower := towerParams, divide := true, loopDigits := loopDigits, frobeniusSteps := true,
    negative := false, xDigits := xDigits, bnFamily := true }

/-- The fast final exponentiation gives this power of the value of `Pairing.finalExponentiation`. -/
def hardPower : Nat := 2 * parameter * (6 * parameter ^ 2 + 3 * parameter + 1)

/-- Subgroup membership of a point of the twist by `ψ(Q) = [6x²]Q` (see the module comment).
    Tested against `[r]Q = O`, not proved. -/
def inG2 (x y : Fp2) : Bool :=
  FastPairing.psiEqualsMultiple quad towerParams psiDigits (toLimbs x) (toLimbs y)

/-- The shorter relation `[x+1]Q + ψ([x]Q) + ψ²([x]Q) = ψ³([2x]Q)` of the same paper (see the
    module comment). Measured and tested beside `inG2`; not used by the precompile. -/
def inG2Short (x y : Fp2) : Bool :=
  FastPairing.psiShortRelation quad towerParams xDigits (toLimbs x) (toLimbs y)

/-- Decode a `G2` point at `off` (imaginary parts first), as `BN254.decodeG2` but with the
    subgroup check `inG2`. -/
def decodeG2 (data : ByteArray) (off : Nat) : Option BN254.Affine2 :=
  let x1 := beNat data off 32
  let x0 := beNat data (off + 32) 32
  let y1 := beNat data (off + 64) 32
  let y0 := beNat data (off + 96) 32
  if x0 ≥ p ∨ x1 ≥ p ∨ y0 ≥ p ∨ y1 ≥ p then none
  else if x0 = 0 ∧ x1 = 0 ∧ y0 = 0 ∧ y1 = 0 then some none
  else
    let x : Fp2 := ⟨x0, x1⟩
    let y : Fp2 := ⟨y0, y1⟩
    if !Curve.onCurve BN254.field2 BN254.twistB x y then none
    else if inG2 x y then some (some (x, y))
    else none

/-- A pair of finite points, in limbs. -/
def pairOf (a : Nat × Nat) (b : Fp2 × Fp2) : PairState Quad256 :=
  FastPairing.pairState quad (Quad256.ofReal (baseField.ofNat a.1)) (Quad256.ofReal (baseField.ofNat a.2))
    (toLimbs b.1) (toLimbs b.2)

/-- Decode `count` pairs starting at `off`. Pairs with a point at infinity contribute one
    to the product and are dropped after validation, as in `BN254.decodePairs`. -/
def decodePairs (data : ByteArray) : Nat → Nat → List (PairState Quad256) → Option (List (PairState Quad256))
  | 0, _, acc => some acc
  | count+1, off, acc =>
    match BN254.decodeG1 data off, decodeG2 data (off + 64) with
    | some a, some b =>
      match a, b with
      | some a, some b => decodePairs data count (off + 192) (pairOf a b :: acc)
      | _, _ => decodePairs data count (off + 192) acc
    | _, _ => none

/-- The product of the Miller values, the final exponentiation and the verdict on limbs. -/
def millerProduct (pairs : List (PairState Quad256)) : Fq12 Quad256 :=
  FastPairing.millerProduct quad fastCurve pairs
def finalExponentiation (f : Fq12 Quad256) : Fq12 Quad256 :=
  FastPairing.finalExponentiation quad fastCurve f
def productIsOne (pairs : List (PairState Quad256)) : Bool :=
  FastPairing.productIsOne quad fastCurve pairs

def pairingBody (input : ByteArray) : Body :=
  if input.size % 192 ≠ 0 then .invalid
  else
    match decodePairs input (input.size / 192) 0 [] with
    | none => .invalid
    | some pairs => .output (natToBE 32 (if productIsOne pairs then 1 else 0))

/-- Precompile 0x08. -/
def runPairing (gas : Nat) (input : ByteArray) : Result :=
  charge gas (BN254.pairingGas input.size) fun _ => pairingBody input

/-- Kind: output contract, accounting and input-length rule.
    Says: a successful pairing check had an input of whole 192-byte pairs, cost exactly
    45000 + 34000 per pair, and returned exactly 32 bytes.
    Does not say: the 32 bytes are the correct verdict (guards, differential check and
    vectors, not proved). -/
theorem runPairing_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runPairing gas input = .success out left) :
    input.size % 192 = 0 ∧ out.size = 32 ∧ left + BN254.pairingGas input.size = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  simp only [pairingBody] at hBody
  split at hBody
  · exact Body.noConfusion hBody
  · rename_i hLen
    split at hBody
    · exact Body.noConfusion hBody
    · exact ⟨by omega, Body.output.inj hBody ▸ natToBE_size _ _, hGas⟩

/-- Kind: input-length rule.
    Says: a pairing input that is not a multiple of 192 bytes fails at any gas.
    Does not say: anything about well-sized input. -/
theorem runPairing_bad_length (gas : Nat) (input : ByteArray) (h : input.size % 192 ≠ 0) :
    runPairing gas input = .failure := by
  unfold runPairing charge
  split
  · rfl
  · simp [pairingBody, h]

/-- Kind: loop bound.
    Says: the price contains 34000 gas for every 192 bytes of input, and `pairingBody`
    decodes exactly `input.size / 192` pairs, so every pair that enters the shared Miller
    loop is paid for (`FastPairingProofs.bn_decodePairs_length` bounds the list).
    Does not say: how long a Miller loop takes. -/
theorem pairingGas_pays_pairs (size : Nat) : 34000 * (size / 192) ≤ BN254.pairingGas size := by
  simp only [BN254.pairingGas]; omega

/-- Kind: value of the empty product.
    Says: with no finite pair the verdict is one without any field arithmetic.
    Does not say: anything about a non-empty product. -/
theorem productIsOne_nil : productIsOne [] = true := rfl

/-! ### Build-time guards against the `Nat` path -/

private def g1 : Nat × Nat := (1, 2)
private def g2 : Fp2 × Fp2 :=
  (⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634⟩,
   ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531⟩)

private def mul1 (k : Nat) : Nat × Nat :=
  (Curve.toAffine BN254.field (Curve.mul BN254.field k (Curve.ofAffine BN254.field g1.1 g1.2))).getD (0, 0)
private def mul2 (k : Nat) : Fp2 × Fp2 :=
  (Curve.toAffine BN254.field2 (Curve.mul BN254.field2 k (Curve.ofAffine BN254.field2 g2.1 g2.2))).getD
    (Fp2.zero, Fp2.zero)
private def neg1 (a : Nat × Nat) : Nat × Nat := (a.1, Fp.neg p a.2)
private def jac (q : Fp2 × Fp2) : JPoint Fp2 := Curve.ofAffine BN254.field2 q.1 q.2
private def definitional (q : Fp2 × Fp2) : Bool :=
  Curve.isInfinity BN254.field2 (Curve.mul BN254.field2 r (jac q))

private def flat (g : Fq12 Quad256) : Fp12 := Fq12.toFlat ofLimbs g
private def lift (a : Fp12) : Fq12 Quad256 := Fq12.ofFlat toLimbs a
private def oldEasyOf (f : Fp12) : Fp12 :=
  let T := BN254.tower
  let easy1 := Fp12.mul T (Fp12.conj T f) (Fp12.inv T f)
  Fp12.mul T (Fp12.frobenius T (Fp12.frobenius T easy1)) easy1

private def oldSample : Fp12 := Pairing.miller BN254.curve g1 g2
private def oldOther : Fp12 := Fp12.frobenius BN254.tower (Fp12.sqr BN254.tower oldSample)
private def sample : Fq12 Quad256 := lift oldSample
private def other : Fq12 Quad256 := lift oldOther
private def oldEasy : Fp12 := oldEasyOf oldSample
private def easy : Fq12 Quad256 := FastPairing.easyPart quad fastCurve sample
private def a2 : Fp2 := oldSample.c1
private def b2 : Fp2 := oldSample.c4
private def c2 : Fp2 := oldSample.c5

-- The limb field, the spare bits lazy reduction needs, and the recodings.
#guard baseField.toNat (baseField.ofNat 5) == 5 && baseField.toNat baseField.one == 1 && 4 * p < 2 ^ 256
#guard loopPos - loopNeg == loopScalar && loopPos &&& loopNeg == 0 && xPos - xNeg == parameter &&
  xPos &&& xNeg == 0 && psiPos - psiNeg == psiScalar && psiPos &&& psiNeg == 0
#guard digitsValue loopDigits 1 == Int.ofNat loopScalar && digitsValue xDigits 1 == Int.ofNat parameter &&
  digitsValue psiDigits 1 == Int.ofNat psiScalar
-- The flat quadratic extension against Fp2, on sample and edge values.
private def edge2 : List Fp2 := [a2, b2, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨p - 1, p - 1⟩, ⟨p - 1, 0⟩, ⟨0, p - 1⟩, ⟨p - 1, 1⟩, ⟨1, p - 1⟩]
#guard edge2.all fun a => edge2.all fun b =>
  ofLimbs (Quad256.mul baseField (toLimbs a) (toLimbs b)) == Fp2.mul p a b &&
  ofLimbs (Quad256.add baseField (toLimbs a) (toLimbs b)) == Fp2.add p a b &&
  ofLimbs (Quad256.sub baseField (toLimbs a) (toLimbs b)) == Fp2.sub p a b &&
  ofLimbs (Quad256.mulReal baseField (toLimbs a) (toLimbs b)) == Fp2.scale p b.c0 a &&
  Quad256.eq (toLimbs a) (toLimbs b) == (a == b)
#guard edge2.all fun a =>
  ofLimbs (Quad256.sqr baseField (toLimbs a)) == Fp2.sqr p a &&
  ofLimbs (Quad256.neg baseField (toLimbs a)) == Fp2.neg p a &&
  ofLimbs (Quad256.double baseField (toLimbs a)) == Fp2.add p a a &&
  ofLimbs (Quad256.conj baseField (toLimbs a)) == Fp2.conj p a &&
  ofLimbs (Quad256.mulXi baseField true (toLimbs a)) == Fp2.mul p a ⟨9, 1⟩ &&
  ofLimbs (Quad256.mulXi baseField false (toLimbs a)) == Fp2.mul p a ⟨1, 1⟩ &&
  ofLimbs (Quad256.inv baseField (toLimbs a)) == Fp2.inv p a &&
  Quad256.isZero (toLimbs a) == Fp2.isZero a && ofLimbs (toLimbs a) == a
#guard ofLimbs Quad256.zero == Fp2.zero && ofLimbs (Quad256.one baseField) == Fp2.one
-- The generic quadratic extension over the limb field (kept as the second route to the tower).
#guard Fq2.toNat baseField.toNat (Fq2.mul baseField.ops (Fq2.ofNat baseField.ofNat a2) (Fq2.ofNat baseField.ofNat b2)) ==
  Fp2.mul p a2 b2
-- Fq12 against the flat Fp12: product, square, inverse, Frobenius, conjugate, sparse product.
#guard flat sample == oldSample
#guard flat (Fq12.mul quad sample other) == Fp12.mul BN254.tower oldSample oldOther
#guard flat (Fq12.sqr quad sample) == Fp12.sqr BN254.tower oldSample
#guard flat (Fq12.inv quad sample) == Fp12.inv BN254.tower oldSample
#guard flat (Fq12.frobenius quad towerParams sample) == Fp12.frobenius BN254.tower oldSample
#guard flat (Fq12.conj quad sample) == Fp12.conj BN254.tower oldSample
#guard flat (Fq12.mulLineD quad sample (toLimbs a2) (toLimbs b2) (toLimbs c2)) ==
  Fp12.mul BN254.tower oldSample ⟨a2, b2, Fp2.zero, c2, Fp2.zero, Fp2.zero⟩
-- The easy part, then cyclotomic squaring and the power by x on its result.
#guard flat easy == oldEasy
#guard flat (Fq12.cyclotomicSqr quad easy) == Fp12.sqr BN254.tower oldEasy
#guard flat (FastPairing.expX quad fastCurve easy) == Fp12.pow BN254.tower oldEasy parameter
-- The hard part is the stated power of the old hard part, and that power is coprime to r.
#guard flat (FastPairing.hardPart quad fastCurve easy) ==
  Fp12.pow BN254.tower (Pairing.hardPart BN254.curve oldEasy) hardPower
#guard Nat.gcd hardPower r == 1
-- The Miller value. With binary digits it is the old value; with the signed digits used
-- here it differs by a factor that the easy part removes, so the values after the easy
-- part are compared: for one pair, and for a product with shared squarings.
#guard flat (FastPairing.millerProduct quad { fastCurve with loopDigits := signedDigits loopScalar 0 (Nat.log2 loopScalar) }
  [pairOf g1 g2]) == oldSample
#guard flat (FastPairing.easyPart quad fastCurve (millerProduct [pairOf g1 g2])) == oldEasy
#guard flat (FastPairing.easyPart quad fastCurve (millerProduct [pairOf g1 g2, pairOf (mul1 5) (mul2 7)])) ==
  oldEasyOf (Fp12.mul BN254.tower oldSample (Pairing.miller BN254.curve (mul1 5) (mul2 7)))
-- The verdict: e(P, Q)·e(−P, Q) = 1, a product that is not one, the empty product computed
-- in full, and bilinearity in each argument.
#guard productIsOne [pairOf g1 g2, pairOf (neg1 g1) g2]
#guard !productIsOne [pairOf g1 g2, pairOf g1 g2]
#guard Fq12.isOne quad (finalExponentiation (millerProduct []))
#guard productIsOne [pairOf (mul1 5) g2, pairOf (neg1 (mul1 2)) g2, pairOf (neg1 (mul1 3)) g2]
#guard productIsOne [pairOf g1 (mul2 5), pairOf (neg1 g1) (mul2 2), pairOf (neg1 g1) (mul2 3)]
#guard productIsOne [pairOf (mul1 5) (mul2 7), pairOf (neg1 (mul1 35)) g2]

-- The subgroup test. A point of the twist outside the subgroup, and a point of order 10069.
private def outside : Fp2 × Fp2 :=
  (⟨6215087815076330926179520016461010917137519558660815034878824735059242618923,
    15951728188012883138265176510482648277956245750475693862477712774865526280408⟩,
   ⟨3883977897564888010651085404774470414463111034944669274151467203191618805695,
    19498073560140031588371260485875504435560004141507859856993853994986969832168⟩)
private def smallOrder : Fp2 × Fp2 :=
  (⟨9623466969819186210096099112386315455791237079390456581453738055980425269292,
    17692382642665795858331459766236260286187917687754477715501738521284345041308⟩,
   ⟨12865421648231312951340958604967729539437910403193079944083607760704855770454,
    14259550034904450902393517181334394889178378255868966757665071873786609510755⟩)
private def psiNat (q : Fp2 × Fp2) : Fp2 × Fp2 := Pairing.twistFrobenius BN254.curve q
private def fastMultiple (q : Fp2 × Fp2) : JPoint Fp2 :=
  let m := FastPairing.g2MulDigits quad (toLimbs q.1) (toLimbs q.2) (Quad256.neg baseField (toLimbs q.2))
    psiDigits ⟨toLimbs q.1, toLimbs q.2, Quad256.one baseField⟩
  ⟨ofLimbs m.x, ofLimbs m.y, ofLimbs m.z⟩

#guard inG2 g2.1 g2.2 && definitional g2 && inG2Short g2.1 g2.2
#guard inG2 (mul2 7).1 (mul2 7).2 && inG2Short (mul2 7).1 (mul2 7).2
#guard Curve.onCurve BN254.field2 BN254.twistB outside.1 outside.2 && !definitional outside
#guard !inG2 outside.1 outside.2 && !inG2Short outside.1 outside.2
#guard Curve.onCurve BN254.field2 BN254.twistB smallOrder.1 smallOrder.2 && !definitional smallOrder &&
  Curve.isInfinity BN254.field2 (Curve.mul BN254.field2 10069 (jac smallOrder))
#guard !inG2 smallOrder.1 smallOrder.2 && !inG2Short smallOrder.1 smallOrder.2
-- The fast multiple [6x²]Q is the one of the Nat path, also outside the subgroup.
#guard Curve.same BN254.field2 (fastMultiple outside) (Curve.mul BN254.field2 psiScalar (jac outside))
#guard Curve.same BN254.field2 (fastMultiple smallOrder) (Curve.mul BN254.field2 psiScalar (jac smallOrder))
-- ψ is the old twist Frobenius, and satisfies ψ² − [t]ψ + [p] = 0 with t = 6x² + 1 outside the subgroup.
#guard ofLimbs (FastPairing.psiX quad towerParams (toLimbs outside.1)) == (psiNat outside).1 &&
  ofLimbs (FastPairing.psiY quad towerParams (toLimbs outside.2)) == (psiNat outside).2
#guard Curve.same BN254.field2
  (Curve.add BN254.field2 (jac (psiNat (psiNat outside))) (Curve.mul BN254.field2 p (jac outside)))
  (Curve.mul BN254.field2 (psiScalar + 1) (jac (psiNat outside)))
#guard p + 1 == r + (psiScalar + 1) && Nat.gcd r (2 * p - r) == 1
-- The order of the twist group kills the outside point: [r·(2p − r)]Q = O.
#guard Curve.isInfinity BN254.field2 (Curve.mul BN254.field2 (r * (2 * p - r)) (jac outside))
-- The body: empty input, a valid two-pair product, a bad length.
#guard (match runPairing 45000 ByteArray.empty with
  | .success out left => toHex out == "0000000000000000000000000000000000000000000000000000000000000001" && left == 0
  | _ => false)
#guard (match runPairing 100000 (natToBE 191 0) with | .failure => true | _ => false)

#print axioms runPairing_success
#print axioms runPairing_bad_length
#print axioms pairingGas_pays_pairs
#print axioms productIsOne_nil

end EVMCleanroom.Precompiles.BN254Pairing
