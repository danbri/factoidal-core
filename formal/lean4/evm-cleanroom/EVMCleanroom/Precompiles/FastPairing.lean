import EVMCleanroom.Precompiles.FastTower
import EVMCleanroom.Precompiles.Curve

/-!
# The pairing product check on the limb tower

The same question as `Pairing.productIsOne` (is a product of pairings one?), computed on
`FastTower` over any `QuadOps` dictionary, for both precompile families: alt_bn128
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
endomorphism `ψ` of a D-type twist with the tests `ψ(Q) = [k]Q` (`psiEqualsMultiple`) and
`[x+1]Q + ψ([x]Q) + ψ²([x]Q) = ψ³([2x]Q)` (`psiShortRelation`), which `BN254Pairing` uses
for subgroup membership.

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
structure FastCurve (K : Type) where
  tower : TowerParams K
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

/-- One pair of the product, with the running point of its Miller loop. `nx` and `y` are
    `−x_P` and `y_P` as real elements of `K`. -/
structure PairState (K : Type) where
  nx : K
  y : K
  qx : K
  qy : K
  nqy : K
  t : JPoint K

namespace FastPairing

variable {K : Type}

/-- The state of a pair of finite points `P = (x, y)` (each coordinate as the real element
    `(x, 0)` of `K`) and `Q = (qx, qy)`. -/
@[specialize] def pairState (Q : QuadOps K) (x y : K) (qx qy : K) : PairState K :=
  { nx := Q.neg x, y := y, qx := qx, qy := qy, nqy := Q.neg qy, t := ⟨qx, qy, Q.one⟩ }

/-- Multiply by a line with coefficient `atY` at `y_P`, `atX` at `x_P` and the free term,
    placed according to the twist kind as in `Pairing.line`. -/
@[specialize] def mulLine (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) (atY atX free : K) : Fq12 K :=
  if C.divide then Fq12.mulLineD Q f atY atX free else Fq12.mulLineM Q f free atX atY

/-- Double the running point and multiply the tangent line at it, evaluated at `P`, into `f`.
    The point is `Curve.double`; the line is `Pairing.tangent` (scaled by `2YZ³`). -/
@[specialize] def doubleStep (Q : QuadOps K) (C : FastCurve K) (nx y : K) (t : JPoint K) (f : Fq12 K) :
    JPoint K × Fq12 K :=
  let xx := Q.sqr t.x
  let yy := Q.sqr t.y
  let zz := Q.sqr t.z
  let yz := Q.mul t.y t.z
  let y4 := Q.sqr yy
  let s0 := Q.sub (Q.sub (Q.sqr (Q.add t.x yy)) xx) y4
  let s := Q.double s0
  let e := Q.add (Q.double xx) xx
  let x3 := Q.sub (Q.sqr e) (Q.double s)
  let y8 := Q.double (Q.double (Q.double y4))
  let y3 := Q.sub (Q.mul e (Q.sub s x3)) y8
  let z3 := Q.double yz
  let la := Q.mulReal (Q.mul z3 zz) y
  let lb := Q.mulReal (Q.mul e zz) nx
  let lc := Q.sub (Q.mul e t.x) (Q.double yy)
  (⟨x3, y3, z3⟩, mulLine Q C f la lb lc)

/-- Add the affine `(qx, qy)` to the running point and multiply the chord through both,
    evaluated at `P`, into `f`. The point is `Curve.add` for a finite `t` different from
    `±(qx, qy)` (always the case for points of prime order `r` inside the loop); the line is
    `Pairing.chord` (scaled by `ZH`). -/
@[specialize] def addStep (Q : QuadOps K) (C : FastCurve K) (nx y : K) (qx qy : K) (t : JPoint K)
    (f : Fq12 K) : JPoint K × Fq12 K :=
  let zz := Q.sqr t.z
  let h := Q.sub (Q.mul qx zz) t.x
  let r := Q.sub (Q.mul qy (Q.mul zz t.z)) t.y
  let zh := Q.mul t.z h
  let hh := Q.sqr h
  let hhh := Q.mul hh h
  let v := Q.mul t.x hh
  let x3 := Q.sub (Q.sub (Q.sqr r) hhh) (Q.double v)
  let y3 := Q.sub (Q.mul r (Q.sub v x3)) (Q.mul t.y hhh)
  let la := Q.mulReal zh y
  let lb := Q.mulReal r nx
  let lc := Q.sub (Q.mul r qx) (Q.mul zh qy)
  (⟨x3, y3, zh⟩, mulLine Q C f la lb lc)

/-- One digit for every pair: the doubling step, then the addition step of a non-zero digit. -/
@[specialize] def stepPairs (Q : QuadOps K) (C : FastCurve K) (d : Digit) :
    List (PairState K) → List (PairState K) → Fq12 K → Fq12 K × List (PairState K)
  | [], seen, f => (f, seen)
  | s :: rest, seen, f =>
    let r := doubleStep Q C s.nx s.y s.t f
    match d with
    | .zero => stepPairs Q C d rest ({ s with t := r.1 } :: seen) r.2
    | .plus =>
      let r2 := addStep Q C s.nx s.y s.qx s.qy r.1 r.2
      stepPairs Q C d rest ({ s with t := r2.1 } :: seen) r2.2
    | .minus =>
      let r2 := addStep Q C s.nx s.y s.qx s.nqy r.1 r.2
      stepPairs Q C d rest ({ s with t := r2.1 } :: seen) r2.2

/-- The shared Miller loop: one squaring of the accumulator per digit, then every pair's lines. -/
@[specialize] def millerLoop (Q : QuadOps K) (C : FastCurve K) :
    List Digit → List (PairState K) → Fq12 K → Fq12 K × List (PairState K)
  | [], states, f => (f, states)
  | d :: rest, states, f =>
    let r := stepPairs Q C d states [] (Fq12.sqr Q f)
    millerLoop Q C rest r.2 r.1

/-- The untwist-Frobenius-twist endomorphism `ψ` on affine coordinates of a D-type twist:
    `(x, y) ↦ (x̄·ξ^((p−1)/3), ȳ·ξ^((p−1)/2))` (`Pairing.twistFrobenius`). -/
@[specialize] def psiX (Q : QuadOps K) (T : TowerParams K) (x : K) : K :=
  Q.mul (Q.conj x) T.frob2
@[specialize] def psiY (Q : QuadOps K) (T : TowerParams K) (y : K) : K :=
  Q.mul (Q.conj y) T.frob3

/-- The two Frobenius chord steps of the optimal ate pairing on BN curves, for every pair:
    add `ψ(Q)`, then the line through the result and `−ψ²(Q)`. -/
@[specialize] def frobeniusSteps (Q : QuadOps K) (C : FastCurve K) : List (PairState K) → Fq12 K → Fq12 K
  | [], f => f
  | s :: rest, f =>
    let q1x := psiX Q C.tower s.qx
    let q1y := psiY Q C.tower s.qy
    let q2x := psiX Q C.tower q1x
    let q2ny := Q.neg (psiY Q C.tower q1y)
    let r1 := addStep Q C s.nx s.y q1x q1y s.t f
    let r2 := addStep Q C s.nx s.y q2x q2ny r1.1 r1.2
    frobeniusSteps Q C rest r2.2

/-- The product of the Miller values of the pairs (finite points only). -/
@[specialize] def millerProduct (Q : QuadOps K) (C : FastCurve K) (pairs : List (PairState K)) : Fq12 K :=
  let r := millerLoop Q C C.loopDigits pairs (Fq12.one Q)
  let f := if C.frobeniusSteps then frobeniusSteps Q C r.2 r.1 else r.1
  if C.negative then Fq12.conj Q f else f

/-- `f ↦ f^((p⁶−1)(p²+1))`, as in `Pairing.finalExponentiation`: one inversion. -/
@[specialize] def easyPart (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) : Fq12 K :=
  let T := C.tower
  let easy1 := Fq12.mul Q (Fq12.conj Q f) (Fq12.inv Q f)
  Fq12.mul Q (Fq12.frobenius Q T (Fq12.frobenius Q T easy1)) easy1

/-- Signed square-and-multiply in the cyclotomic subgroup; `baseInv` is the conjugate. -/
@[specialize] def expLoop (Q : QuadOps K) (base baseInv : Fq12 K) :
    List Digit → Fq12 K → Fq12 K
  | [], acc => acc
  | d :: rest, acc =>
    let s := Fq12.cyclotomicSqr Q acc
    match d with
    | .zero => expLoop Q base baseInv rest s
    | .plus => expLoop Q base baseInv rest (Fq12.mul Q s base)
    | .minus => expLoop Q base baseInv rest (Fq12.mul Q s baseInv)

/-- `f^|x|` for `f` in the cyclotomic subgroup. -/
@[specialize] def expX (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) : Fq12 K :=
  expLoop Q f (Fq12.conj Q f) C.xDigits f

/-- The hard part on BN curves: `f^(2x(6x²+3x+1)·(p⁴−p²+1)/r)` (see the module comment). -/
@[specialize] def hardBN (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) : Fq12 K :=
  let T := C.tower
  let fx := expX Q C f
  let f2x := Fq12.cyclotomicSqr Q fx
  let f4x := Fq12.cyclotomicSqr Q f2x
  let f6x := Fq12.mul Q f4x f2x
  let f6x2 := expX Q C f6x
  let f12x2 := Fq12.cyclotomicSqr Q f6x2
  let f12x3 := expX Q C f12x2
  let a := Fq12.mul Q (Fq12.mul Q f12x3 f6x2) f6x
  let b := Fq12.mul Q a (Fq12.conj Q f2x)
  let t0 := Fq12.mul Q (Fq12.mul Q a f6x2) f
  let fb := Fq12.frobenius Q T b
  let fa := Fq12.frobenius Q T (Fq12.frobenius Q T a)
  let fc := Fq12.frobenius Q T (Fq12.frobenius Q T (Fq12.frobenius Q T (Fq12.mul Q b (Fq12.conj Q f))))
  Fq12.mul Q (Fq12.mul Q t0 fb) (Fq12.mul Q fa fc)

/-- The hard part on BLS12 curves with a negative parameter: `f^(3·(p⁴−p²+1)/r)`
    (see the module comment). -/
@[specialize] def hardBLS (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) : Fq12 K :=
  let T := C.tower
  let t0 := Fq12.mul Q (Fq12.conj Q (expX Q C f)) (Fq12.conj Q f)
  let t1 := Fq12.mul Q (Fq12.conj Q (expX Q C t0)) (Fq12.conj Q t0)
  let t2 := Fq12.mul Q (Fq12.conj Q (expX Q C t1)) (Fq12.frobenius Q T t1)
  let t2xx := expX Q C (expX Q C t2)
  let t3 := Fq12.mul Q (Fq12.mul Q t2xx (Fq12.frobenius Q T (Fq12.frobenius Q T t2))) (Fq12.conj Q t2)
  Fq12.mul Q t3 (Fq12.mul Q (Fq12.cyclotomicSqr Q f) f)

@[specialize] def hardPart (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) : Fq12 K :=
  if C.bnFamily then hardBN Q C f else hardBLS Q C f

@[specialize] def finalExponentiation (Q : QuadOps K) (C : FastCurve K) (f : Fq12 K) : Fq12 K :=
  hardPart Q C (easyPart Q C f)

/-- Is the product of the pairings of these finite pairs equal to one? One shared Miller
    loop and one final exponentiation. The empty product is one. -/
@[specialize] def productIsOne (Q : QuadOps K) (C : FastCurve K) (pairs : List (PairState K)) : Bool :=
  match pairs with
  | [] => true
  | _ :: _ => Fq12.isOne Q (finalExponentiation Q C (millerProduct Q C pairs))

/-! ### Jacobian arithmetic on the twist, and `ψ` -/

/-- `Curve.double` on the twist. A point with `Z = 0` (infinity) or `Y = 0` gives `Z = 0`. -/
@[specialize] def g2Double (Q : QuadOps K) (t : JPoint K) : JPoint K :=
  let xx := Q.sqr t.x
  let yy := Q.sqr t.y
  let y4 := Q.sqr yy
  let s0 := Q.sub (Q.sub (Q.sqr (Q.add t.x yy)) xx) y4
  let s := Q.double s0
  let e := Q.add (Q.double xx) xx
  let x3 := Q.sub (Q.sqr e) (Q.double s)
  let y8 := Q.double (Q.double (Q.double y4))
  let y3 := Q.sub (Q.mul e (Q.sub s x3)) y8
  ⟨x3, y3, Q.double (Q.mul t.y t.z)⟩

/-- Add the finite affine point `(qx, qy)`: complete (infinity, doubling and inverse cases),
    because the subgroup test runs it on points of any order. -/
@[specialize] def g2AddAffine (Q : QuadOps K) (t : JPoint K) (qx qy : K) : JPoint K :=
  if Q.isZero t.z then ⟨qx, qy, Q.one⟩
  else
    let zz := Q.sqr t.z
    let h := Q.sub (Q.mul qx zz) t.x
    let r := Q.sub (Q.mul qy (Q.mul zz t.z)) t.y
    if Q.isZero h then
      if Q.isZero r then g2Double Q t else ⟨Q.one, Q.one, Q.zero⟩
    else
      let hh := Q.sqr h
      let hhh := Q.mul hh h
      let v := Q.mul t.x hh
      let x3 := Q.sub (Q.sub (Q.sqr r) hhh) (Q.double v)
      let y3 := Q.sub (Q.mul r (Q.sub v x3)) (Q.mul t.y hhh)
      ⟨x3, y3, Q.mul t.z h⟩

/-- Signed double-and-add: `[k]Q` for the digits of `k` below its leading one, from `acc = Q`. -/
@[specialize] def g2MulDigits (Q : QuadOps K) (qx qy nqy : K) : List Digit → JPoint K → JPoint K
  | [], acc => acc
  | d :: rest, acc =>
    let doubled := g2Double Q acc
    match d with
    | .zero => g2MulDigits Q qx qy nqy rest doubled
    | .plus => g2MulDigits Q qx qy nqy rest (g2AddAffine Q doubled qx qy)
    | .minus => g2MulDigits Q qx qy nqy rest (g2AddAffine Q doubled qx nqy)

/-- Does the Jacobian point stand for the finite affine point `(x, y)`? -/
@[specialize] def g2EqualsAffine (Q : QuadOps K) (t : JPoint K) (x y : K) : Bool :=
  if Q.isZero t.z then false
  else
    let zz := Q.sqr t.z
    Q.eq t.x (Q.mul x zz) && Q.eq t.y (Q.mul y (Q.mul zz t.z))

/-- `ψ(Q) = [k]Q` for a finite point `Q = (x, y)` of a D-type twist, `k` given by its digits. -/
@[specialize] def psiEqualsMultiple (Q : QuadOps K) (T : TowerParams K) (digits : List Digit) (x y : K) : Bool :=
  g2EqualsAffine Q (g2MulDigits Q x y (Q.neg y) digits ⟨x, y, Q.one⟩) (psiX Q T x) (psiY Q T y)

/-- `Curve.add` on the twist: complete (infinity, doubling and inverse cases). -/
@[specialize] def g2Add (Q : QuadOps K) (p q : JPoint K) : JPoint K :=
  if Q.isZero p.z then q
  else if Q.isZero q.z then p
  else
    let z1z1 := Q.sqr p.z
    let z2z2 := Q.sqr q.z
    let u1 := Q.mul p.x z2z2
    let u2 := Q.mul q.x z1z1
    let s1 := Q.mul (Q.mul p.y q.z) z2z2
    let s2 := Q.mul (Q.mul q.y p.z) z1z1
    let h := Q.sub u2 u1
    let r := Q.sub s2 s1
    if Q.isZero h then
      if Q.isZero r then g2Double Q p else ⟨Q.one, Q.one, Q.zero⟩
    else
      let hh := Q.sqr h
      let hhh := Q.mul hh h
      let v := Q.mul u1 hh
      let x3 := Q.sub (Q.sub (Q.sqr r) hhh) (Q.double v)
      let y3 := Q.sub (Q.mul r (Q.sub v x3)) (Q.mul s1 hhh)
      ⟨x3, y3, Q.mul (Q.mul h p.z) q.z⟩

/-- `Curve.same` on the twist: equality of the points represented, without inversion. -/
@[specialize] def g2Same (Q : QuadOps K) (p q : JPoint K) : Bool :=
  match Q.isZero p.z, Q.isZero q.z with
  | true, true => true
  | false, false =>
    let z1z1 := Q.sqr p.z
    let z2z2 := Q.sqr q.z
    Q.eq (Q.mul p.x z2z2) (Q.mul q.x z1z1) &&
      Q.eq (Q.mul (Q.mul p.y q.z) z2z2) (Q.mul (Q.mul q.y p.z) z1z1)
  | _, _ => false

/-- `ψ` on Jacobian coordinates of a D-type twist: `(X, Y, Z) ↦ (X̄·frob₂, Ȳ·frob₃, Z̄)`.
    Infinity goes to infinity. -/
@[specialize] def psiJ (Q : QuadOps K) (T : TowerParams K) (p : JPoint K) : JPoint K :=
  ⟨Q.mul (Q.conj p.x) T.frob2, Q.mul (Q.conj p.y) T.frob3, Q.conj p.z⟩

/-- The relation `[x+1]Q + ψ([x]Q) + ψ²([x]Q) = ψ³([2x]Q)` for a finite point `Q = (x, y)` of
    a D-type twist, with the digits of the curve parameter: one scalar multiplication of
    half the length of `psiEqualsMultiple`'s. -/
@[specialize] def psiShortRelation (Q : QuadOps K) (T : TowerParams K) (digits : List Digit) (x y : K) : Bool :=
  let a := g2MulDigits Q x y (Q.neg y) digits ⟨x, y, Q.one⟩
  let pa := psiJ Q T a
  let lhs := g2Add Q (g2AddAffine Q a x y) (g2Add Q pa (psiJ Q T pa))
  let rhs := psiJ Q T (psiJ Q T (psiJ Q T (g2Double Q a)))
  g2Same Q lhs rhs

/-- Kind: value of the empty product.
    Says: the product over no pairs is one, without any field arithmetic.
    Does not say: anything about a non-empty product (guards and vectors, not proved). -/
theorem productIsOne_nil (Q : QuadOps K) (C : FastCurve K) : productIsOne Q C [] = true := rfl

/-- Kind: loop bound.
    Says: with no digits left the Miller loop, the exponentiation loop and the scalar
    multiplication return their accumulator, so each runs exactly one step per digit.
    Does not say: what a step computes. -/
theorem loops_nil (Q : QuadOps K) (C : FastCurve K) (states : List (PairState K)) (f base baseInv : Fq12 K)
    (qx qy nqy : K) (acc : JPoint K) :
    millerLoop Q C [] states f = (f, states) ∧ expLoop Q base baseInv [] f = f ∧
      g2MulDigits Q qx qy nqy [] acc = acc := by
  simp [millerLoop, expLoop, g2MulDigits]

/-- Kind: loop bound.
    Says: one digit step keeps every pair: the number of running points after it is the
    number before.
    Does not say: what the points or the accumulator are. -/
theorem stepPairs_length (Q : QuadOps K) (C : FastCurve K) (d : Digit) (states seen : List (PairState K))
    (f : Fq12 K) : (stepPairs Q C d states seen f).2.length = states.length + seen.length := by
  induction states generalizing seen f with
  | nil => simp [stepPairs]
  | cons s rest ih =>
    cases d <;> simp [stepPairs, ih] <;> omega

/-- Kind: identity handling.
    Says: adding a finite affine point to the point at infinity gives that point.
    Does not say: any other group law. -/
theorem g2AddAffine_infinity (Q : QuadOps K) (t : JPoint K) (qx qy : K)
    (h : Q.isZero t.z = true) : g2AddAffine Q t qx qy = ⟨qx, qy, Q.one⟩ := by
  simp [g2AddAffine, h]

/-- Kind: refusal of infinity.
    Says: the point at infinity is never equal to a finite affine point, so `ψ(Q) = [k]Q`
    fails when `[k]Q` is infinity.
    Does not say: the test is a subgroup test (see `BN254Pairing`). -/
theorem g2EqualsAffine_infinity (Q : QuadOps K) (t : JPoint K) (x y : K)
    (h : Q.isZero t.z = true) : g2EqualsAffine Q t x y = false := by
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
