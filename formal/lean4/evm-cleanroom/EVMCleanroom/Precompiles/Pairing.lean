import EVMCleanroom.Precompiles.Tower
import EVMCleanroom.Precompiles.Curve

/-!
# Pairing product check on curves with a sextic twist

One Miller loop and final exponentiation for both pairing precompile families:
alt_bn128 (D-type twist, optimal ate with the two Frobenius steps) and
BLS12-381 (M-type twist, ate loop over the curve parameter).

Derivation (written here, not taken from an implementation). With
`Fp12 = Fp2[w]/(w⁶ − ξ)` the twist `E'` maps to the curve by
`(x, y) ↦ (x w², y w³)` for a D-type twist (`E' : y² = x³ + b/ξ`) and by
`(x, y) ↦ (x / w², y / w³)` for an M-type twist (`E' : y² = x³ + b ξ`). If `λ`
is the slope of a chord or tangent on the twist at `(x₁, y₁)`, the line through
the mapped points, evaluated at `P = (xP, yP)` in `E(Fp)`, is

* D-type: `yP − λ·xP·w + (λ x₁ − y₁)·w³`;
* M-type: `(λ x₁ − y₁) − λ·xP·w² + yP·w³` after multiplying by `w³`.

Factors that lie in a proper subfield of `Fp12` (the denominators of `λ`, and
`w³` in the M-type case) are removed by the final exponentiation, so the lines
are computed without inversions from Jacobian coordinates `(X, Y, Z)` of the
running point:

* tangent, scaled by `2YZ³`: `yP·2YZ³`, `−xP·3X²Z²`, `3X³ − 2Y²`;
* chord to the affine `(x₂, y₂)`, scaled by `ZH` with `H = x₂Z² − X`,
  `R = y₂Z³ − Y`: `yP·ZH`, `−xP·R`, `R x₂ − ZH y₂`.

The precompiles only ask whether a product of pairings is one. That question
has the same answer for any fixed non-degenerate bilinear pairing, so the
normalisation of the value does not matter for them.

Final exponentiation: `f ↦ f^((p¹²−1)/r)` as `(p⁶−1)`, `(p²+1)` and the hard
part `(p⁴−p²+1)/r`. The hard part is written in base `p` (four digits) and
evaluated by simultaneous square-and-multiply over the four Frobenius images,
which is valid for any such curve and needs no curve-specific chain.

Nothing here is proved. Bilinearity and non-degeneracy are checked by guards
in the curve modules and by the published vectors.
-/

namespace EVMCleanroom.Precompiles

inductive TwistKind where
  | divide
  | multiply
  deriving DecidableEq

structure PairingCurve where
  tower : Tower
  /-- Order of the prime-order groups. -/
  r : Nat
  twist : TwistKind
  /-- Miller loop scalar: `6x + 2` for alt_bn128, `|x|` for BLS12-381. -/
  loop : Nat
  /-- The two extra Frobenius chord steps of the optimal ate pairing on BN curves. -/
  frobeniusSteps : Bool
  /-- Conjugate at the end (negative curve parameter). -/
  negative : Bool
  /-- Base-`p` digits of `(p⁴ − p² + 1) / r`, least significant first. -/
  hardDigits : Array Nat

def hardDigitsOf (p r : Nat) : Array Nat :=
  let e := (p ^ 4 - p ^ 2 + 1) / r
  #[e % p, e / p % p, e / p ^ 2 % p, e / p ^ 3]

namespace Pairing

abbrev G1 := Nat × Nat
abbrev G2 := Fp2 × Fp2

/-- Place the three line coefficients according to the twist kind. -/
@[inline] def line (C : PairingCurve) (atYP atXP free : Fp2) : Fp12 :=
  match C.twist with
  | .divide => ⟨atYP, atXP, Fp2.zero, free, Fp2.zero, Fp2.zero⟩
  | .multiply => ⟨free, Fp2.zero, atXP, atYP, Fp2.zero, Fp2.zero⟩

/-- Tangent line at the running point, evaluated at `P`. -/
def tangent (C : PairingCurve) (t : JPoint Fp2) (P : G1) : Fp12 :=
  let p := C.tower.p
  let m := Fp2.mul p
  let xx := Fp2.sqr p t.x
  let zz := Fp2.sqr p t.z
  let yz := m t.y t.z
  let a := Fp2.scale p (2 * P.2) (m yz zz)
  let b := Fp2.neg p (Fp2.scale p (3 * P.1) (m xx zz))
  let c := Fp2.sub p (Fp2.scale p 3 (m xx t.x)) (Fp2.scale p 2 (Fp2.sqr p t.y))
  line C a b c

/-- Chord through the running point and the affine `q`, evaluated at `P`. -/
def chord (C : PairingCurve) (t : JPoint Fp2) (q : G2) (P : G1) : Fp12 :=
  let p := C.tower.p
  let m := Fp2.mul p
  let zz := Fp2.sqr p t.z
  let h := Fp2.sub p (m q.1 zz) t.x
  let r := Fp2.sub p (m q.2 (m zz t.z)) t.y
  let zh := m t.z h
  let a := Fp2.scale p P.2 zh
  let b := Fp2.neg p (Fp2.scale p P.1 r)
  let c := Fp2.sub p (m r q.1) (m zh q.2)
  line C a b c

structure MillerState where
  f : Fp12
  t : JPoint Fp2

def millerLoop (C : PairingCurve) (P : G1) (q : G2) : Nat → MillerState → MillerState
  | 0, s => s
  | bits+1, s =>
    let O := Fp2.ops C.tower.p
    let f := Fp12.mul C.tower (Fp12.sqr C.tower s.f) (tangent C s.t P)
    let t := Curve.double O s.t
    if C.loop.testBit bits then
      millerLoop C P q bits ⟨Fp12.mul C.tower f (chord C t q P), Curve.add O t (Curve.ofAffine O q.1 q.2)⟩
    else millerLoop C P q bits ⟨f, t⟩

/-- The `p`-power Frobenius on twist coordinates. -/
def twistFrobenius (C : PairingCurve) (q : G2) : G2 :=
  let p := C.tower.p
  (Fp2.mul p (Fp2.conj p q.1) C.tower.frob[2]!, Fp2.mul p (Fp2.conj p q.2) C.tower.frob[3]!)

/-- The Miller function value for one pair of finite points. -/
def miller (C : PairingCurve) (P : G1) (q : G2) : Fp12 :=
  let O := Fp2.ops C.tower.p
  let s := millerLoop C P q (Nat.log2 C.loop) ⟨Fp12.one, Curve.ofAffine O q.1 q.2⟩
  let s :=
    if C.frobeniusSteps then
      let q1 := twistFrobenius C q
      let q2 := twistFrobenius C q1
      let q2neg : G2 := (q2.1, Fp2.neg C.tower.p q2.2)
      let f1 := Fp12.mul C.tower s.f (chord C s.t q1 P)
      let t1 := Curve.add O s.t (Curve.ofAffine O q1.1 q1.2)
      ⟨Fp12.mul C.tower f1 (chord C t1 q2neg P), t1⟩
    else s
  if C.negative then Fp12.conj C.tower s.f else s.f

/-- Simultaneous square-and-multiply: `table[i]` is the product of the bases selected by
    the bits of `i`; one squaring and at most one multiplication per exponent bit. -/
def multiPowLoop (T : Tower) (digits : Array Nat) (table : Array Fp12) : Nat → Fp12 → Fp12
  | 0, acc => acc
  | k+1, acc =>
    let square := Fp12.sqr T acc
    let index := (if digits[0]!.testBit k then 1 else 0) + (if digits[1]!.testBit k then 2 else 0) +
      (if digits[2]!.testBit k then 4 else 0) + (if digits[3]!.testBit k then 8 else 0)
    multiPowLoop T digits table k (if index = 0 then square else Fp12.mul T square table[index]!)

/-- `f^(d₀ + d₁ p + d₂ p² + d₃ p³)` from the four Frobenius images of `f`. -/
def hardPart (C : PairingCurve) (f : Fp12) : Fp12 :=
  let T := C.tower
  let f1 := Fp12.frobenius T f
  let f2 := Fp12.frobenius T f1
  let f3 := Fp12.frobenius T f2
  let bases := #[f, f1, f2, f3]
  let table := (Array.range 16).map fun i =>
    (Array.range 4).foldl (fun acc j => if i.testBit j then Fp12.mul T acc bases[j]! else acc) Fp12.one
  multiPowLoop T C.hardDigits table (Nat.log2 T.p + 1) Fp12.one

def finalExponentiation (C : PairingCurve) (f : Fp12) : Fp12 :=
  let T := C.tower
  let easy1 := Fp12.mul T (Fp12.conj T f) (Fp12.inv T f)
  let easy2 := Fp12.mul T (Fp12.frobenius T (Fp12.frobenius T easy1)) easy1
  hardPart C easy2

/-- The pairing value for one pair of finite points. -/
def pairing (C : PairingCurve) (P : G1) (q : G2) : Fp12 :=
  finalExponentiation C (miller C P q)

def millerProduct (C : PairingCurve) : List (G1 × G2) → Fp12 → Fp12
  | [], acc => acc
  | (P, q) :: rest, acc => millerProduct C rest (Fp12.mul C.tower acc (miller C P q))

/-- Is the product of the pairings of these finite pairs equal to one? One shared
    final exponentiation. The empty product is one. -/
def productIsOne (C : PairingCurve) (pairs : List (G1 × G2)) : Bool :=
  Fp12.isOne (finalExponentiation C (millerProduct C pairs Fp12.one))

end Pairing

end EVMCleanroom.Precompiles
