import EVMCleanroom.Precompiles.Field

/-!
# The degree-twelve extension used by the pairing precompiles

`Fp12` is represented directly as `Fp2[w]/(w⁶ − ξ)`: six `Fp2` coefficients
of `1, w, …, w⁵`. The same code serves alt_bn128 (`ξ = 9 + u`) and BLS12-381
(`ξ = 1 + u`). The usual tower appears as sub-structures: the even powers of
`w` form `Fp6 = Fp2[v]/(v³ − ξ)` with `v = w²`.

Multiplication accumulates the unreduced `Fp2` products as integers and
reduces each of the twelve coordinates once.

Nothing here is proved beyond canonical form of products. The algebra is
exercised by build-time guards on both curves (inverse, Frobenius as a
`p`-th power, associativity samples) and by the pairing vectors.
-/

namespace EVMCleanroom.Precompiles

/-- Parameters of `Fp2[w]/(w⁶ − ξ)`, with the Frobenius constants
    `frob[i] = ξ^(i·(p−1)/6)` computed once. -/
structure Tower where
  p : Nat
  xi : Fp2
  frob : Array Fp2

def Tower.make (p : Nat) (xi : Fp2) : Tower :=
  let g := Fp2.pow p xi ((p - 1) / 6)
  let g2 := Fp2.mul p g g
  let g3 := Fp2.mul p g2 g
  let g4 := Fp2.mul p g3 g
  let g5 := Fp2.mul p g4 g
  { p, xi, frob := #[Fp2.one, g, g2, g3, g4, g5] }

structure Fp12 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  c3 : Fp2
  c4 : Fp2
  c5 : Fp2
  deriving BEq, Repr, Inhabited

/-- An unreduced `Fp2` value. -/
structure Wide where
  re : Int
  im : Int

instance : Add Wide := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩

namespace Fp12

def zero : Fp12 := ⟨Fp2.zero, Fp2.zero, Fp2.zero, Fp2.zero, Fp2.zero, Fp2.zero⟩
def one : Fp12 := ⟨Fp2.one, Fp2.zero, Fp2.zero, Fp2.zero, Fp2.zero, Fp2.zero⟩

@[inline] def wmul (a b : Fp2) : Wide :=
  ⟨(a.c0 : Int) * b.c0 - (a.c1 : Int) * b.c1, (a.c0 : Int) * b.c1 + (a.c1 : Int) * b.c0⟩

/-- Multiply an unreduced value by `ξ`. -/
@[inline] def wxi (T : Tower) (x : Wide) : Wide :=
  ⟨x.re * T.xi.c0 - x.im * T.xi.c1, x.re * T.xi.c1 + x.im * T.xi.c0⟩

@[inline] def reduce (p : Nat) (x : Wide) : Fp2 :=
  ⟨(x.re % (p : Int)).toNat, (x.im % (p : Int)).toNat⟩

/-- Product in `Fp2[w]/(w⁶ − ξ)`: coefficient `k` is the sum of `aᵢ bⱼ` over
    `i + j = k`, plus `ξ` times the sum over `i + j = k + 6`. -/
def mul (T : Tower) (a b : Fp12) : Fp12 :=
  {
    c0 := reduce T.p (wmul a.c0 b.c0 + wxi T (wmul a.c1 b.c5 + wmul a.c2 b.c4 + wmul a.c3 b.c3 + wmul a.c4 b.c2 + wmul a.c5 b.c1))
    c1 := reduce T.p (wmul a.c0 b.c1 + wmul a.c1 b.c0 + wxi T (wmul a.c2 b.c5 + wmul a.c3 b.c4 + wmul a.c4 b.c3 + wmul a.c5 b.c2))
    c2 := reduce T.p (wmul a.c0 b.c2 + wmul a.c1 b.c1 + wmul a.c2 b.c0 + wxi T (wmul a.c3 b.c5 + wmul a.c4 b.c4 + wmul a.c5 b.c3))
    c3 := reduce T.p (wmul a.c0 b.c3 + wmul a.c1 b.c2 + wmul a.c2 b.c1 + wmul a.c3 b.c0 + wxi T (wmul a.c4 b.c5 + wmul a.c5 b.c4))
    c4 := reduce T.p (wmul a.c0 b.c4 + wmul a.c1 b.c3 + wmul a.c2 b.c2 + wmul a.c3 b.c1 + wmul a.c4 b.c0 + wxi T (wmul a.c5 b.c5))
    c5 := reduce T.p (wmul a.c0 b.c5 + wmul a.c1 b.c4 + wmul a.c2 b.c3 + wmul a.c3 b.c2 + wmul a.c4 b.c1 + wmul a.c5 b.c0) }

@[inline] def wsqr (a : Fp2) : Wide :=
  ⟨((a.c0 : Int) + a.c1) * ((a.c0 : Int) - a.c1), 2 * ((a.c0 : Int) * a.c1)⟩

@[inline] def wdouble (x : Wide) : Wide := ⟨2 * x.re, 2 * x.im⟩

/-- Square: the symmetric products of `mul` are computed once and doubled. -/
def sqr (T : Tower) (a : Fp12) : Fp12 :=
  {
    c0 := reduce T.p (wsqr a.c0 + wxi T (wdouble (wmul a.c1 a.c5 + wmul a.c2 a.c4) + wsqr a.c3))
    c1 := reduce T.p (wdouble (wmul a.c0 a.c1) + wxi T (wdouble (wmul a.c2 a.c5 + wmul a.c3 a.c4)))
    c2 := reduce T.p (wdouble (wmul a.c0 a.c2) + wsqr a.c1 + wxi T (wdouble (wmul a.c3 a.c5) + wsqr a.c4))
    c3 := reduce T.p (wdouble (wmul a.c0 a.c3 + wmul a.c1 a.c2) + wxi T (wdouble (wmul a.c4 a.c5)))
    c4 := reduce T.p (wdouble (wmul a.c0 a.c4 + wmul a.c1 a.c3) + wsqr a.c2 + wxi T (wsqr a.c5))
    c5 := reduce T.p (wdouble (wmul a.c0 a.c5 + wmul a.c1 a.c4 + wmul a.c2 a.c3)) }

/-- The `p⁶`-power Frobenius: `w ↦ −w`. -/
def conj (T : Tower) (a : Fp12) : Fp12 :=
  { a with c1 := Fp2.neg T.p a.c1, c3 := Fp2.neg T.p a.c3, c5 := Fp2.neg T.p a.c5 }

/-- The `p`-power Frobenius: conjugate each coefficient and multiply by `ξ^(i(p−1)/6)`. -/
def frobenius (T : Tower) (a : Fp12) : Fp12 :=
  let f (i : Nat) (c : Fp2) : Fp2 := Fp2.mul T.p (Fp2.conj T.p c) T.frob[i]!
  ⟨Fp2.conj T.p a.c0, f 1 a.c1, f 2 a.c2, f 3 a.c3, f 4 a.c4, f 5 a.c5⟩

/-- Inverse: `a · conj a` lies in `Fp6` (even powers of `w`), which is inverted by the
    cubic-extension formula over `Fp2`. Zero maps to zero. -/
def inv (T : Tower) (a : Fp12) : Fp12 :=
  let p := T.p
  let m := Fp2.mul p
  let xi := Fp2.mul p T.xi
  let abar := conj T a
  let d := mul T a abar
  let (d0, d1, d2) := (d.c0, d.c2, d.c4)
  let t0 := Fp2.sub p (Fp2.sqr p d0) (xi (m d1 d2))
  let t1 := Fp2.sub p (xi (Fp2.sqr p d2)) (m d0 d1)
  let t2 := Fp2.sub p (Fp2.sqr p d1) (m d0 d2)
  let norm := Fp2.add p (m d0 t0) (xi (Fp2.add p (m d2 t1) (m d1 t2)))
  let ni := Fp2.inv p norm
  let e : Fp12 := ⟨m t0 ni, Fp2.zero, m t1 ni, Fp2.zero, m t2 ni, Fp2.zero⟩
  mul T abar e

def powLoop (T : Tower) (base : Fp12) (e : Nat) : Nat → Fp12 → Fp12
  | 0, acc => acc
  | k+1, acc =>
    let square := sqr T acc
    powLoop T base e k (if e.testBit k then mul T square base else square)

def pow (T : Tower) (base : Fp12) (e : Nat) : Fp12 :=
  if e = 0 then one else powLoop T base e (Nat.log2 e + 1) one

def isOne (a : Fp12) : Bool := a == one

/-- Kind: canonical representation.
    Says: every coordinate of a product is below the modulus.
    Does not say: the product is the field product for non-canonical inputs. -/
theorem mul_canonical (T : Tower) (a b : Fp12) (h : 0 < T.p) :
    (mul T a b).c0.c0 < T.p ∧ (mul T a b).c0.c1 < T.p ∧ (mul T a b).c5.c0 < T.p ∧ (mul T a b).c5.c1 < T.p := by
  have hp : (0 : Int) < (T.p : Int) := by exact_mod_cast h
  have key : ∀ x : Int, (x % (T.p : Int)).toNat < T.p := by
    intro x
    have h1 := Int.emod_lt_of_pos x hp
    have h2 := Int.emod_nonneg x (Int.ne_of_gt hp)
    omega
  simp only [mul, reduce]
  exact ⟨key _, key _, key _, key _⟩

#print axioms mul_canonical

end Fp12

end EVMCleanroom.Precompiles
