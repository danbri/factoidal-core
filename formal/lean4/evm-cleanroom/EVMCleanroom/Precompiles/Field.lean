import EVMCleanroom.Precompiles.Basic

/-!
# Prime fields and their quadratic extension, on canonical representatives

`Fp` operations take the modulus explicitly and work on natural numbers below
it. `Fp2` is `Fp[u]/(u² + 1)`, the quadratic extension used by both pairing
curves of the precompiles (alt_bn128 and BLS12-381). `FieldOps` is a plain
dictionary so the curve arithmetic in `Curve.lean` is written once.

Nothing here is constant-time: the precompiles handle public data only.

All operations expect canonical arguments (below the modulus); the decoders
of every precompile enforce that before any arithmetic. Addition, subtraction
and negation then need no division.

Proved here: results stay canonical (below the modulus), and the division-free
operations agree with the residues on canonical values. Field laws and
primality of the moduli are not proved; inverses and square roots are checked
by the callers (`a * inv a = 1`, `sqrt a ^ 2 = a`) before use, and by guards.
-/

namespace EVMCleanroom.Precompiles

/-- Field operations on some representation. `inv` maps zero to zero. -/
class FieldOps (F : Type) where
  zero : F
  one : F
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  sqr : F → F
  neg : F → F
  inv : F → F
  isZero : F → Bool
  eq : F → F → Bool

namespace Fp

/-- Sum of two canonical values: one comparison and at most one subtraction, no division. -/
@[inline] def add (p a b : Nat) : Nat := if a + b < p then a + b else a + b - p
/-- Difference of two canonical values, without division. -/
@[inline] def sub (p a b : Nat) : Nat := if b ≤ a then a - b else a + p - b
@[inline] def mul (p a b : Nat) : Nat := (a * b) % p
/-- Negation of a canonical value. -/
@[inline] def neg (p a : Nat) : Nat := if a = 0 then 0 else p - a

/-- Extended Euclid on `(p, a)`; the Bézout coefficient of `a` is tracked as an
    integer. Returns 0 when `a` has no inverse or the fuel runs out. -/
def invLoop : Nat → Nat → Nat → Int → Int → Int
  | 0, _, _, _, _ => 0
  | fuel+1, r0, r1, t0, t1 =>
    if r1 = 0 then (if r0 = 1 then t0 else 0)
    else invLoop fuel r1 (r0 % r1) t1 (t0 - ((r0 / r1 : Nat) : Int) * t1)

/-- Modular inverse, zero for a non-invertible argument. The fuel exceeds the
    Euclid step bound of about 1.45 log₂ p. -/
def inv (p a : Nat) : Nat :=
  (invLoop (2 * Nat.log2 p + 8) p (a % p) 0 1 % (p : Int)).toNat

/-- Square-and-multiply, most significant bit first, `bits` steps. -/
def powLoop (p base e : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc =>
    let square := acc * acc % p
    powLoop p base e k (if e.testBit k then square * base % p else square)

def pow (p base e : Nat) : Nat := powLoop p base e (Nat.log2 e + 1) (1 % p)

/-- A square root for `p ≡ 3 (mod 4)`, checked: `none` when `a` is not a square. -/
def sqrt? (p a : Nat) : Option Nat :=
  let root := pow p a ((p + 1) / 4)
  if root * root % p == a % p then some root else none

/-- Kind: canonical representation.
    Says: sums, differences and negations of values below the modulus stay below it;
    products do for any inputs.
    Does not say: anything for non-canonical inputs of `add`, `sub` and `neg`. -/
theorem add_lt (p a b : Nat) (ha : a < p) (hb : b < p) : add p a b < p := by
  unfold add; split <;> omega
theorem sub_lt (p a b : Nat) (ha : a < p) (hb : b < p) : sub p a b < p := by
  unfold sub; split <;> omega
theorem mul_lt (p a b : Nat) (h : 0 < p) : mul p a b < p := Nat.mod_lt _ h
theorem neg_lt (p a : Nat) (ha : a < p) : neg p a < p := by
  unfold neg; split <;> omega

/-- Kind: algebraic fact.
    Says: on canonical values the division-free sum, difference and negation are the
    residues of the integer sum, difference and negation.
    Does not say: the modulus is prime. -/
theorem add_eq_mod (p a b : Nat) (ha : a < p) (hb : b < p) : add p a b = (a + b) % p := by
  unfold add
  split
  · rename_i h; exact (Nat.mod_eq_of_lt h).symm
  · rename_i h
    have h1 : a + b - p < p := by omega
    have h2 : a + b = (a + b - p) + p := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
    omega

theorem sub_eq_mod (p a b : Nat) (ha : a < p) (hb : b < p) : sub p a b = (a + (p - b)) % p := by
  unfold sub
  split
  · rename_i h
    have h1 : a + (p - b) = (a - b) + p := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rename_i h
    have h1 : a + (p - b) = a + p - b := by omega
    rw [h1, Nat.mod_eq_of_lt (by omega)]

/-- Kind: canonical representation.
    Says: the inverse routine returns a value below the modulus.
    Does not say: it is an inverse (callers and guards check `a * inv a = 1`). -/
theorem inv_lt (p a : Nat) (h : 0 < p) : inv p a < p := by
  unfold inv
  have hp : (0 : Int) < (p : Int) := by exact_mod_cast h
  have h1 := Int.emod_lt_of_pos (invLoop (2 * Nat.log2 p + 8) p (a % p) 0 1) hp
  have h2 := Int.emod_nonneg (invLoop (2 * Nat.log2 p + 8) p (a % p) 0 1) (Int.ne_of_gt hp)
  omega

/-- Kind: algebraic fact.
    Says: subtraction then addition of the same canonical value is the identity.
    Does not say: the modulus is prime. -/
theorem add_sub_cancel (p a b : Nat) (ha : a < p) (hb : b < p) : add p (sub p a b) b = a := by
  unfold add sub
  split <;> split <;> omega

/-- Kind: algebraic fact.
    Says: multiplication commutes.
    Does not say: the modulus is prime. -/
theorem mul_comm (p a b : Nat) : mul p a b = mul p b a := by simp [mul, Nat.mul_comm]

/-- Kind: algebraic fact.
    Says: addition commutes.
    Does not say: the modulus is prime. -/
theorem add_comm (p a b : Nat) : add p a b = add p b a := by simp [add, Nat.add_comm]

/-- Kind: algebraic fact.
    Says: a canonical value plus its negation is zero.
    Does not say: the modulus is prime. -/
theorem add_neg (p a : Nat) (ha : a < p) : add p a (neg p a) = 0 := by
  unfold add neg
  split <;> split <;> omega

def ops (p : Nat) : FieldOps Nat where
  zero := 0
  one := 1 % p
  add := add p
  sub := sub p
  mul := mul p
  sqr := fun a => mul p a a
  neg := neg p
  inv := inv p
  isZero := fun a => a == 0
  eq := fun a b => a == b

end Fp

/-- An element `c0 + c1·u` of `Fp[u]/(u² + 1)`. -/
structure Fp2 where
  c0 : Nat
  c1 : Nat
  deriving BEq, Repr, Inhabited

namespace Fp2

def zero : Fp2 := ⟨0, 0⟩
def one : Fp2 := ⟨1, 0⟩

@[inline] def add (p : Nat) (a b : Fp2) : Fp2 := ⟨Fp.add p a.c0 b.c0, Fp.add p a.c1 b.c1⟩
@[inline] def sub (p : Nat) (a b : Fp2) : Fp2 := ⟨Fp.sub p a.c0 b.c0, Fp.sub p a.c1 b.c1⟩
@[inline] def neg (p : Nat) (a : Fp2) : Fp2 := ⟨Fp.neg p a.c0, Fp.neg p a.c1⟩
@[inline] def conj (p : Nat) (a : Fp2) : Fp2 := ⟨a.c0, Fp.neg p a.c1⟩

/-- `(a0 + a1 u)(b0 + b1 u) = (a0 b0 − a1 b1) + (a0 b1 + a1 b0) u`, one reduction per coordinate. -/
@[inline] def mul (p : Nat) (a b : Fp2) : Fp2 :=
  ⟨(a.c0 * b.c0 + (p - a.c1) * b.c1) % p, (a.c0 * b.c1 + a.c1 * b.c0) % p⟩

@[inline] def sqr (p : Nat) (a : Fp2) : Fp2 :=
  ⟨((a.c0 + a.c1) * (a.c0 + (p - a.c1))) % p, (2 * a.c0 * a.c1) % p⟩

@[inline] def scale (p : Nat) (k : Nat) (a : Fp2) : Fp2 := ⟨(k * a.c0) % p, (k * a.c1) % p⟩

/-- Inverse through the norm `a0² + a1²`; zero maps to zero. -/
def inv (p : Nat) (a : Fp2) : Fp2 :=
  let n := Fp.inv p ((a.c0 * a.c0 + a.c1 * a.c1) % p)
  ⟨(a.c0 * n) % p, ((p - a.c1) * n) % p⟩

@[inline] def isZero (a : Fp2) : Bool := a.c0 == 0 && a.c1 == 0

def powLoop (p : Nat) (base : Fp2) (e : Nat) : Nat → Fp2 → Fp2
  | 0, acc => acc
  | k+1, acc =>
    let square := sqr p acc
    powLoop p base e k (if e.testBit k then mul p square base else square)

def pow (p : Nat) (base : Fp2) (e : Nat) : Fp2 := powLoop p base e (Nat.log2 e + 1) one

/-- Kind: canonical representation.
    Says: products have both coordinates below the modulus.
    Does not say: the product is the field product for non-canonical inputs. -/
theorem mul_canonical (p : Nat) (a b : Fp2) (h : 0 < p) : (mul p a b).c0 < p ∧ (mul p a b).c1 < p :=
  ⟨Nat.mod_lt _ h, Nat.mod_lt _ h⟩

theorem add_canonical (p : Nat) (a b : Fp2) (ha : a.c0 < p ∧ a.c1 < p) (hb : b.c0 < p ∧ b.c1 < p) :
    (add p a b).c0 < p ∧ (add p a b).c1 < p :=
  ⟨Fp.add_lt _ _ _ ha.1 hb.1, Fp.add_lt _ _ _ ha.2 hb.2⟩

theorem sub_canonical (p : Nat) (a b : Fp2) (ha : a.c0 < p ∧ a.c1 < p) (hb : b.c0 < p ∧ b.c1 < p) :
    (sub p a b).c0 < p ∧ (sub p a b).c1 < p :=
  ⟨Fp.sub_lt _ _ _ ha.1 hb.1, Fp.sub_lt _ _ _ ha.2 hb.2⟩

theorem inv_canonical (p : Nat) (a : Fp2) (h : 0 < p) : (inv p a).c0 < p ∧ (inv p a).c1 < p :=
  ⟨Nat.mod_lt _ h, Nat.mod_lt _ h⟩

def ops (p : Nat) : FieldOps Fp2 where
  zero := zero
  one := one
  add := add p
  sub := sub p
  mul := mul p
  sqr := sqr p
  neg := neg p
  inv := inv p
  isZero := isZero
  eq := fun a b => a == b

end Fp2

private def p25519 : Nat := 2 ^ 255 - 19
private def p13 : Nat := 13

#guard Fp.inv 13 5 == 8 && Fp.inv 13 0 == 0 && Fp.inv 13 13 == 0 && Fp.inv 12 4 == 0
#guard Fp.mul p25519 (Fp.inv p25519 123456789) 123456789 == 1
#guard Fp.mul p25519 (Fp.inv p25519 (p25519 - 1)) (p25519 - 1) == 1
#guard Fp.pow 13 2 12 == 1 && Fp.pow 13 2 0 == 1 && Fp.pow 13 0 0 == 1 && Fp.pow 1 5 3 == 0
#guard Fp.sub 13 3 5 == 11 && Fp.neg 13 0 == 0 && Fp.add 13 12 12 == 11
-- 19 ≡ 3 (mod 4): 5 is a square (9² = 81 = 5), 2 is not.
#guard Fp.sqrt? 19 5 == some 9 && Fp.sqrt? 19 2 == none
-- Fp2 over 19: u² = −1.
#guard Fp2.mul 19 ⟨0, 1⟩ ⟨0, 1⟩ == ⟨18, 0⟩
#guard Fp2.mul 19 (Fp2.inv 19 ⟨3, 7⟩) ⟨3, 7⟩ == Fp2.one
#guard Fp2.sqr 19 ⟨3, 7⟩ == Fp2.mul 19 ⟨3, 7⟩ ⟨3, 7⟩
#guard Fp2.pow 19 ⟨3, 7⟩ 360 == Fp2.one

#print axioms Fp.inv_lt
#print axioms Fp.add_eq_mod
#print axioms Fp.sub_eq_mod
#print axioms Fp.add_sub_cancel
#print axioms Fp.mul_comm
#print axioms Fp.add_comm
#print axioms Fp.add_neg
#print axioms Fp2.mul_canonical
#print axioms Fp2.inv_canonical
#print axioms Fp.add_lt
#print axioms Fp.sub_lt
#print axioms Fp.mul_lt
#print axioms Fp.neg_lt
#print axioms Fp2.add_canonical
#print axioms Fp2.sub_canonical

end EVMCleanroom.Precompiles
