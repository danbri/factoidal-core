import EVMCleanroom.Precompiles.FastTower
import EVMCleanroom.Precompiles.Curve

/-!
# The pairing product check on the limb tower

The same question as `Pairing.productIsOne` (is a product of pairings one?), computed on
`FastTower` over any base-field representation, for both precompile families: alt_bn128
(D-type twist, optimal ate with the two Frobenius steps) and BLS12-381 (M-type twist, ate
loop over the curve parameter). `Pairing.lean` stays the definition and the oracle.

What differs from `Pairing.lean`:

* **Lines folded into the point steps.** `doubleStep` and `addStep` compute the new
  Jacobian point and the three line coefficients from shared intermediate values. The
  coefficients are the ones derived in `Pairing.lean` (tangent scaled by `2YZ³`, chord by
  `ZH`), so with the same scalar digits the Miller value is the same field element as
  `Pairing.miller`, not only the same up to a subfield factor.
* **Sparse line multiplication** (`Fq12.mulLineD`, `Fq12.mulLineM`): 13 `Fq2` products
  in place of a full `Fq12` product.
* **One shared squaring per digit** for a product of pairs: `millerLoop` squares the one
  accumulator once and multiplies every pair's line in, where `Pairing.millerProduct` runs
  a whole loop per pair.
* **Signed digits.** Loop scalars are given as `pos − neg` (`signedDigits`); a minus digit
  adds `−Q`. With a signed recoding the Miller value differs from the binary one by factors
  that the final exponentiation removes (vertical lines, which lie in a proper subfield),
  so only the final value is compared in that case.
* **Final exponentiation, hard part.** After the easy part the value is in the cyclotomic
  subgroup, where squaring is `Fq12.cyclotomicSqr` and the inverse is the conjugate. The
  hard part is an exponentiation chain in the curve parameter `x`:
  - BN curves (`hardBN`): Fuentes-Castañeda, Knapp and Rodríguez-Henríquez, "Faster hashing
    to G2", SAC 2011, the section on the final exponentiation. With `a = f^(12x³+6x²+6x)`
    and `b = a·f^(−2x)` the result is `a·f^(6x²)·f · b^p · a^(p²) · (b·f⁻¹)^(p³)`, which is
    `f^(λ₀ + λ₁p + λ₂p² + λ₃p³)` for `λ₀ = 12x³+12x²+6x+1`, `λ₁ = 12x³+6x²+4x`,
    `λ₂ = 12x³+6x²+6x`, `λ₃ = 12x³+6x²+4x−1`. That exponent equals
    `2x(6x²+3x+1) · (p⁴−p²+1)/r` (an identity of integers, proved for the alt_bn128
    parameter in `FastPairingProofs`).
  - BLS12 curves (`hardBLS`): the decomposition
    `(x−1)²·(x+p)·(x²+p²−1) + 3 = 3·(p⁴−p²+1)/r` (Hayashida, Hayasaka and Teruya,
    "Efficient final exponentiation via cyclotomic structure for pairings over families of
    elliptic curves", 2020), for a negative parameter: `f^x` is the conjugate of `f^|x|`.
  So the value computed is a fixed power of the value of `Pairing.finalExponentiation`:
  the power `2x(6x²+3x+1)` for BN and the cube for BLS12. Both are coprime to `r`
  (proved for the two parameters in `FastPairingProofs`), and the value of the old code has
  order dividing `r`, so "is the product one" has the same answer. The precompiles ask
  nothing else.

Also here: Jacobian arithmetic on the twist with a signed-digit multiplication
(`g2MulDigits`, complete in the affine addend), and the untwist-Frobenius-twist
endomorphism `ψ` of a D-type twist with the test `ψ(Q) = [k]Q` (`psiEqualsMultiple`), which
`BN254Pairing` uses for subgroup membership.

Proved here: the number of digits (so the number of loop steps), the value of the empty
product, identity handling of the addition. Not proved: every function value. The Miller
value, the final exponentiation and the verdict are compared with `Pairing.lean` by
build-time guards in the curve modules and by the run-time differential check
`evm-pairingperf`, and through the published vectors. Bilinearity is not proved anywhere.

Nothing is constant-time: the precompiles handle public data only.
-/

namespace EVMCleanroom.Precompiles

/-- A signed binary digit. -/
inductive Digit where
  | zero
  | plus
  | minus
  deriving DecidableEq

def signedDigitsLoop (pos neg : Nat) : Nat → Nat → List Digit → List Digit
  | 0, _, acc => acc
  | n+1, i, acc =>
    signedDigitsLoop pos neg n (i + 1)
      ((if pos.testBit i then Digit.plus else if neg.testBit i then Digit.minus else Digit.zero) :: acc)

/-- The digits of `pos − neg` at the bit positions `count − 1, …, 0`, most significant
    first. The loops start from the base itself, which stands for a leading `plus` at
    position `count`. -/
def signedDigits (pos neg count : Nat) : List Digit := signedDigitsLoop pos neg count 0 []

/-- The integer a digit list stands for after a prefix of value `acc`. -/
def digitsValue : List Digit → Int → Int
  | [], acc => acc
  | .zero :: rest, acc => digitsValue rest (2 * acc)
  | .plus :: rest, acc => digitsValue rest (2 * acc + 1)
  | .minus :: rest, acc => digitsValue rest (2 * acc - 1)

theorem signedDigitsLoop_length (pos neg n i : Nat) (acc : List Digit) :
    (signedDigitsLoop pos neg n i acc).length = acc.length + n := by
  induction n generalizing i acc with
  | zero => simp [signedDigitsLoop]
  | succ n ih => simp [signedDigitsLoop, ih]; omega

/-- Kind: loop bound.
    Says: a digit list has exactly `count` digits, so a loop over it runs `count` steps.
    Does not say: which digits (the value is checked per constant in `FastPairingProofs`). -/
theorem signedDigits_length (pos neg count : Nat) : (signedDigits pos neg count).length = count := by
  simp [signedDigits, signedDigitsLoop_length]

/-- The curve-specific data of the fast pairing. -/
structure FastCurve (F : Type) where
  tower : TowerParams F
  /-- D-type twist (alt_bn128); otherwise M-type (BLS12-381). -/
  divide : Bool
  /-- Digits of the Miller loop scalar below its leading one: `6x + 2` for alt_bn128,
      `|x|` for BLS12-381. -/
  loopDigits : List Digit
  /-- The two extra Frobenius chord steps of the optimal ate pairing on BN curves. -/
  frobeniusSteps : Bool
  /-- Conjugate at the end (negative curve parameter). -/
  negative : Bool
  /-- Digits of `|x|` below its leading one, for the hard part. -/
  xDigits : List Digit
  /-- The BN chain for the hard part; otherwise the BLS12 chain. -/
  bnFamily : Bool

/-- One pair of the product, with the running point of its Miller loop. `nx` is `−x_P`. -/
structure PairState (F : Type) where
  nx : F
  y : F
  qx : Fq2 F
  qy : Fq2 F
  nqy : Fq2 F
  t : JPoint (Fq2 F)

namespace FastPairing

variable {F : Type}

/-- The state of a pair of finite points `P = (x, y)`, `Q = (qx, qy)`. -/
@[specialize] def pairState (O : FieldOps F) (x y : F) (qx qy : Fq2 F) : PairState F :=
  { nx := O.neg x, y := y, qx := qx, qy := qy, nqy := Fq2.neg O qy, t := ⟨qx, qy, Fq2.one O⟩ }

/-- Multiply by a line with coefficient `atY` at `y_P`, `atX` at `x_P` and the free term,
    placed according to the twist kind as in `Pairing.line`. -/
@[specialize] def mulLine (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) (atY atX free : Fq2 F) : Fq12 F :=
  if C.divide then Fq12.mulLineD O C.tower f atY atX free else Fq12.mulLineM O C.tower f free atX atY

/-- Double the running point and multiply the tangent line at it, evaluated at `P`, into `f`.
    The point is `Curve.double`; the line is `Pairing.tangent` (scaled by `2YZ³`). -/
@[specialize] def doubleStep (O : FieldOps F) (C : FastCurve F) (nx y : F) (t : JPoint (Fq2 F)) (f : Fq12 F) :
    JPoint (Fq2 F) × Fq12 F :=
  let xx := Fq2.sqr O t.x
  let yy := Fq2.sqr O t.y
  let zz := Fq2.sqr O t.z
  let yz := Fq2.mul O t.y t.z
  let y4 := Fq2.sqr O yy
  let s0 := Fq2.sub O (Fq2.sub O (Fq2.sqr O (Fq2.add O t.x yy)) xx) y4
  let s := Fq2.double O s0
  let e := Fq2.add O (Fq2.double O xx) xx
  let x3 := Fq2.sub O (Fq2.sqr O e) (Fq2.double O s)
  let y8 := Fq2.double O (Fq2.double O (Fq2.double O y4))
  let y3 := Fq2.sub O (Fq2.mul O e (Fq2.sub O s x3)) y8
  let z3 := Fq2.double O yz
  let la := Fq2.scale O y (Fq2.mul O z3 zz)
  let lb := Fq2.scale O nx (Fq2.mul O e zz)
  let lc := Fq2.sub O (Fq2.mul O e t.x) (Fq2.double O yy)
  (⟨x3, y3, z3⟩, mulLine O C f la lb lc)

/-- Add the affine `(qx, qy)` to the running point and multiply the chord through both,
    evaluated at `P`, into `f`. The point is `Curve.add` for a finite `t` different from
    `±(qx, qy)` (always the case for points of prime order `r` inside the loop); the line is
    `Pairing.chord` (scaled by `ZH`). -/
@[specialize] def addStep (O : FieldOps F) (C : FastCurve F) (nx y : F) (qx qy : Fq2 F) (t : JPoint (Fq2 F))
    (f : Fq12 F) : JPoint (Fq2 F) × Fq12 F :=
  let zz := Fq2.sqr O t.z
  let h := Fq2.sub O (Fq2.mul O qx zz) t.x
  let r := Fq2.sub O (Fq2.mul O qy (Fq2.mul O zz t.z)) t.y
  let zh := Fq2.mul O t.z h
  let hh := Fq2.sqr O h
  let hhh := Fq2.mul O hh h
  let v := Fq2.mul O t.x hh
  let x3 := Fq2.sub O (Fq2.sub O (Fq2.sqr O r) hhh) (Fq2.double O v)
  let y3 := Fq2.sub O (Fq2.mul O r (Fq2.sub O v x3)) (Fq2.mul O t.y hhh)
  let la := Fq2.scale O y zh
  let lb := Fq2.scale O nx r
  let lc := Fq2.sub O (Fq2.mul O r qx) (Fq2.mul O zh qy)
  (⟨x3, y3, zh⟩, mulLine O C f la lb lc)

/-- One digit for every pair: the doubling step, then the addition step of a non-zero digit. -/
@[specialize] def stepPairs (O : FieldOps F) (C : FastCurve F) (d : Digit) :
    List (PairState F) → List (PairState F) → Fq12 F → Fq12 F × List (PairState F)
  | [], seen, f => (f, seen)
  | s :: rest, seen, f =>
    let r := doubleStep O C s.nx s.y s.t f
    match d with
    | .zero => stepPairs O C d rest ({ s with t := r.1 } :: seen) r.2
    | .plus =>
      let r2 := addStep O C s.nx s.y s.qx s.qy r.1 r.2
      stepPairs O C d rest ({ s with t := r2.1 } :: seen) r2.2
    | .minus =>
      let r2 := addStep O C s.nx s.y s.qx s.nqy r.1 r.2
      stepPairs O C d rest ({ s with t := r2.1 } :: seen) r2.2

/-- The shared Miller loop: one squaring of the accumulator per digit, then every pair's lines. -/
@[specialize] def millerLoop (O : FieldOps F) (C : FastCurve F) :
    List Digit → List (PairState F) → Fq12 F → Fq12 F × List (PairState F)
  | [], states, f => (f, states)
  | d :: rest, states, f =>
    let r := stepPairs O C d states [] (Fq12.sqr O C.tower f)
    millerLoop O C rest r.2 r.1

/-- The untwist-Frobenius-twist endomorphism `ψ` on affine coordinates of a D-type twist:
    `(x, y) ↦ (x̄·ξ^((p−1)/3), ȳ·ξ^((p−1)/2))` (`Pairing.twistFrobenius`). -/
@[specialize] def psiX (O : FieldOps F) (T : TowerParams F) (x : Fq2 F) : Fq2 F :=
  Fq2.mul O (Fq2.conj O x) T.frob2
@[specialize] def psiY (O : FieldOps F) (T : TowerParams F) (y : Fq2 F) : Fq2 F :=
  Fq2.mul O (Fq2.conj O y) T.frob3

/-- The two Frobenius chord steps of the optimal ate pairing on BN curves, for every pair:
    add `ψ(Q)`, then the line through the result and `−ψ²(Q)`. -/
@[specialize] def frobeniusSteps (O : FieldOps F) (C : FastCurve F) : List (PairState F) → Fq12 F → Fq12 F
  | [], f => f
  | s :: rest, f =>
    let q1x := psiX O C.tower s.qx
    let q1y := psiY O C.tower s.qy
    let q2x := psiX O C.tower q1x
    let q2ny := Fq2.neg O (psiY O C.tower q1y)
    let r1 := addStep O C s.nx s.y q1x q1y s.t f
    let r2 := addStep O C s.nx s.y q2x q2ny r1.1 r1.2
    frobeniusSteps O C rest r2.2

/-- The product of the Miller values of the pairs (finite points only). -/
@[specialize] def millerProduct (O : FieldOps F) (C : FastCurve F) (pairs : List (PairState F)) : Fq12 F :=
  let r := millerLoop O C C.loopDigits pairs (Fq12.one O)
  let f := if C.frobeniusSteps then frobeniusSteps O C r.2 r.1 else r.1
  if C.negative then Fq12.conj O f else f

/-- `f ↦ f^((p⁶−1)(p²+1))`, as in `Pairing.finalExponentiation`: one inversion. -/
@[specialize] def easyPart (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) : Fq12 F :=
  let T := C.tower
  let easy1 := Fq12.mul O T (Fq12.conj O f) (Fq12.inv O T f)
  Fq12.mul O T (Fq12.frobenius O T (Fq12.frobenius O T easy1)) easy1

/-- Signed square-and-multiply in the cyclotomic subgroup; `baseInv` is the conjugate. -/
@[specialize] def expLoop (O : FieldOps F) (T : TowerParams F) (base baseInv : Fq12 F) :
    List Digit → Fq12 F → Fq12 F
  | [], acc => acc
  | d :: rest, acc =>
    let s := Fq12.cyclotomicSqr O T acc
    match d with
    | .zero => expLoop O T base baseInv rest s
    | .plus => expLoop O T base baseInv rest (Fq12.mul O T s base)
    | .minus => expLoop O T base baseInv rest (Fq12.mul O T s baseInv)

/-- `f^|x|` for `f` in the cyclotomic subgroup. -/
@[specialize] def expX (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) : Fq12 F :=
  expLoop O C.tower f (Fq12.conj O f) C.xDigits f

/-- The hard part on BN curves: `f^(2x(6x²+3x+1)·(p⁴−p²+1)/r)` (see the module comment). -/
@[specialize] def hardBN (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) : Fq12 F :=
  let T := C.tower
  let fx := expX O C f
  let f2x := Fq12.cyclotomicSqr O T fx
  let f4x := Fq12.cyclotomicSqr O T f2x
  let f6x := Fq12.mul O T f4x f2x
  let f6x2 := expX O C f6x
  let f12x2 := Fq12.cyclotomicSqr O T f6x2
  let f12x3 := expX O C f12x2
  let a := Fq12.mul O T (Fq12.mul O T f12x3 f6x2) f6x
  let b := Fq12.mul O T a (Fq12.conj O f2x)
  let t0 := Fq12.mul O T (Fq12.mul O T a f6x2) f
  let fb := Fq12.frobenius O T b
  let fa := Fq12.frobenius O T (Fq12.frobenius O T a)
  let fc := Fq12.frobenius O T (Fq12.frobenius O T (Fq12.frobenius O T (Fq12.mul O T b (Fq12.conj O f))))
  Fq12.mul O T (Fq12.mul O T t0 fb) (Fq12.mul O T fa fc)

/-- The hard part on BLS12 curves with a negative parameter: `f^(3·(p⁴−p²+1)/r)`
    (see the module comment). -/
@[specialize] def hardBLS (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) : Fq12 F :=
  let T := C.tower
  let t0 := Fq12.mul O T (Fq12.conj O (expX O C f)) (Fq12.conj O f)
  let t1 := Fq12.mul O T (Fq12.conj O (expX O C t0)) (Fq12.conj O t0)
  let t2 := Fq12.mul O T (Fq12.conj O (expX O C t1)) (Fq12.frobenius O T t1)
  let t2xx := expX O C (expX O C t2)
  let t3 := Fq12.mul O T (Fq12.mul O T t2xx (Fq12.frobenius O T (Fq12.frobenius O T t2))) (Fq12.conj O t2)
  Fq12.mul O T t3 (Fq12.mul O T (Fq12.cyclotomicSqr O T f) f)

@[specialize] def hardPart (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) : Fq12 F :=
  if C.bnFamily then hardBN O C f else hardBLS O C f

@[specialize] def finalExponentiation (O : FieldOps F) (C : FastCurve F) (f : Fq12 F) : Fq12 F :=
  hardPart O C (easyPart O C f)

/-- Is the product of the pairings of these finite pairs equal to one? One shared Miller
    loop and one final exponentiation. The empty product is one. -/
@[specialize] def productIsOne (O : FieldOps F) (C : FastCurve F) (pairs : List (PairState F)) : Bool :=
  match pairs with
  | [] => true
  | _ :: _ => Fq12.isOne O (finalExponentiation O C (millerProduct O C pairs))

/-! ### Jacobian arithmetic on the twist, and `ψ` -/

/-- `Curve.double` on the twist. A point with `Z = 0` (infinity) or `Y = 0` gives `Z = 0`. -/
@[specialize] def g2Double (O : FieldOps F) (t : JPoint (Fq2 F)) : JPoint (Fq2 F) :=
  let xx := Fq2.sqr O t.x
  let yy := Fq2.sqr O t.y
  let y4 := Fq2.sqr O yy
  let s0 := Fq2.sub O (Fq2.sub O (Fq2.sqr O (Fq2.add O t.x yy)) xx) y4
  let s := Fq2.double O s0
  let e := Fq2.add O (Fq2.double O xx) xx
  let x3 := Fq2.sub O (Fq2.sqr O e) (Fq2.double O s)
  let y8 := Fq2.double O (Fq2.double O (Fq2.double O y4))
  let y3 := Fq2.sub O (Fq2.mul O e (Fq2.sub O s x3)) y8
  ⟨x3, y3, Fq2.double O (Fq2.mul O t.y t.z)⟩

/-- Add the finite affine point `(qx, qy)`: complete (infinity, doubling and inverse cases),
    because the subgroup test runs it on points of any order. -/
@[specialize] def g2AddAffine (O : FieldOps F) (t : JPoint (Fq2 F)) (qx qy : Fq2 F) : JPoint (Fq2 F) :=
  if Fq2.isZero O t.z then ⟨qx, qy, Fq2.one O⟩
  else
    let zz := Fq2.sqr O t.z
    let h := Fq2.sub O (Fq2.mul O qx zz) t.x
    let r := Fq2.sub O (Fq2.mul O qy (Fq2.mul O zz t.z)) t.y
    if Fq2.isZero O h then
      if Fq2.isZero O r then g2Double O t else ⟨Fq2.one O, Fq2.one O, Fq2.zero O⟩
    else
      let hh := Fq2.sqr O h
      let hhh := Fq2.mul O hh h
      let v := Fq2.mul O t.x hh
      let x3 := Fq2.sub O (Fq2.sub O (Fq2.sqr O r) hhh) (Fq2.double O v)
      let y3 := Fq2.sub O (Fq2.mul O r (Fq2.sub O v x3)) (Fq2.mul O t.y hhh)
      ⟨x3, y3, Fq2.mul O t.z h⟩

/-- Signed double-and-add: `[k]Q` for the digits of `k` below its leading one, from `acc = Q`. -/
@[specialize] def g2MulDigits (O : FieldOps F) (qx qy nqy : Fq2 F) : List Digit → JPoint (Fq2 F) → JPoint (Fq2 F)
  | [], acc => acc
  | d :: rest, acc =>
    let doubled := g2Double O acc
    match d with
    | .zero => g2MulDigits O qx qy nqy rest doubled
    | .plus => g2MulDigits O qx qy nqy rest (g2AddAffine O doubled qx qy)
    | .minus => g2MulDigits O qx qy nqy rest (g2AddAffine O doubled qx nqy)

/-- Does the Jacobian point stand for the finite affine point `(x, y)`? -/
@[specialize] def g2EqualsAffine (O : FieldOps F) (t : JPoint (Fq2 F)) (x y : Fq2 F) : Bool :=
  if Fq2.isZero O t.z then false
  else
    let zz := Fq2.sqr O t.z
    Fq2.eq O t.x (Fq2.mul O x zz) && Fq2.eq O t.y (Fq2.mul O y (Fq2.mul O zz t.z))

/-- `ψ(Q) = [k]Q` for a finite point `Q = (x, y)` of a D-type twist, `k` given by its digits. -/
@[specialize] def psiEqualsMultiple (O : FieldOps F) (T : TowerParams F) (digits : List Digit) (x y : Fq2 F) : Bool :=
  g2EqualsAffine O (g2MulDigits O x y (Fq2.neg O y) digits ⟨x, y, Fq2.one O⟩) (psiX O T x) (psiY O T y)

/-- Kind: value of the empty product.
    Says: the product over no pairs is one, without any field arithmetic.
    Does not say: anything about a non-empty product (guards and vectors, not proved). -/
theorem productIsOne_nil (O : FieldOps F) (C : FastCurve F) : productIsOne O C [] = true := rfl

/-- Kind: loop bound.
    Says: with no digits left the Miller loop, the exponentiation loop and the scalar
    multiplication return their accumulator, so each runs exactly one step per digit.
    Does not say: what a step computes. -/
theorem loops_nil (O : FieldOps F) (C : FastCurve F) (states : List (PairState F)) (f base baseInv : Fq12 F)
    (qx qy nqy : Fq2 F) (acc : JPoint (Fq2 F)) :
    millerLoop O C [] states f = (f, states) ∧ expLoop O C.tower base baseInv [] f = f ∧
      g2MulDigits O qx qy nqy [] acc = acc := by
  simp [millerLoop, expLoop, g2MulDigits]

/-- Kind: loop bound.
    Says: one digit step keeps every pair: the number of running points after it is the
    number before.
    Does not say: what the points or the accumulator are. -/
theorem stepPairs_length (O : FieldOps F) (C : FastCurve F) (d : Digit) (states seen : List (PairState F))
    (f : Fq12 F) : (stepPairs O C d states seen f).2.length = states.length + seen.length := by
  induction states generalizing seen f with
  | nil => simp [stepPairs]
  | cons s rest ih =>
    cases d <;> simp [stepPairs, ih] <;> omega

/-- Kind: identity handling.
    Says: adding a finite affine point to the point at infinity gives that point.
    Does not say: any other group law. -/
theorem g2AddAffine_infinity (O : FieldOps F) (t : JPoint (Fq2 F)) (qx qy : Fq2 F)
    (h : Fq2.isZero O t.z = true) : g2AddAffine O t qx qy = ⟨qx, qy, Fq2.one O⟩ := by
  simp [g2AddAffine, h]

/-- Kind: refusal of infinity.
    Says: the point at infinity is never equal to a finite affine point, so `ψ(Q) = [k]Q`
    fails when `[k]Q` is infinity.
    Does not say: the test is a subgroup test (see `BN254Pairing`). -/
theorem g2EqualsAffine_infinity (O : FieldOps F) (t : JPoint (Fq2 F)) (x y : Fq2 F)
    (h : Fq2.isZero O t.z = true) : g2EqualsAffine O t x y = false := by
  simp [g2EqualsAffine, h]

#print axioms signedDigitsLoop_length
#print axioms signedDigits_length
#print axioms productIsOne_nil
#print axioms loops_nil
#print axioms stepPairs_length
#print axioms g2AddAffine_infinity
#print axioms g2EqualsAffine_infinity

end FastPairing

end EVMCleanroom.Precompiles
