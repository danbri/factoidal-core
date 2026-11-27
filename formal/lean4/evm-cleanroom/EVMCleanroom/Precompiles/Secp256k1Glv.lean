import EVMCleanroom.Precompiles.Secp256k1
import EVMCleanroom.Precompiles.Secp256k1FieldFast

/-!
# secp256k1: the endomorphism constants, the scalar decomposition and the scalar inverse

Part of the fast paths for public data (`Secp256k1Fast.lean`, which has the overview).

The curve has the endomorphism `φ(x, y) = (beta·x, y)`, which acts on the group as
multiplication by `lam` (Gallant, Lambert and Vanstone, "Faster point multiplication on
elliptic curves with efficient endomorphisms", CRYPTO 2001). A scalar `k` is split as
`k ≡ k1 + k2·lam (mod n)` with short `k1`, `k2` by rounding against a reduced lattice basis
(Algorithm 3.74 of Hankerson, Menezes and Vanstone, "Guide to Elliptic Curve Cryptography",
2004).

Proved: the identity and the size bound of the split hold for every scalar. Both are
**checked at run time** on the rounded candidate, and a candidate that failed either check
would be replaced by the trivial split `(k, 0)`. The relations of the constants are proved by
evaluation. The scalar inverse is the old one or passed the check `a · x mod n = 1`.

Not proved: that `φ` is multiplication by `lam` on the curve (a guard in `Secp256k1Fast`
tests `[lam]G = (beta·gx, gy)` and the differential runs test the rest).

Variable-time: `Nat` and `Int` arithmetic, and a binary GCD. Public data only.
-/

namespace EVMCleanroom.Precompiles.Secp256k1

/-! ### Constants of the endomorphism -/

/-- A cube root of unity modulo the group order: `φ(P) = [lam]P`. -/
def lam : Nat := 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
/-- A cube root of unity modulo the field prime: `φ(x, y) = (beta·x, y)`. -/
def beta : Nat := 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
/-- The reduced lattice basis `(a1, −glvB1)`, `(a2, a1)` of the pairs `(a, b)` with `a + b·lam ≡ 0 (mod n)`. -/
def glvA1 : Nat := 0x3086d221a7d46bcde86c90e49284eb15
def glvB1 : Nat := 0xe4437ed6010e88286f547fa90abfe4c3
def glvA2 : Nat := 0x114ca50f7a8e2f3f657c1108d9d44cfd8
def halfN : Nat := n / 2
def glvBound : Nat := 2 ^ 129

/-- The rounded decomposition: `c1 = ⌊a1·k/n⌉`, `c2 = ⌊glvB1·k/n⌉`,
    `k1 = k − c1·a1 − c2·a2`, `k2 = c1·glvB1 − c2·a1`. -/
def glvCandidate (k : Nat) : Int × Int :=
  let c1 := (glvA1 * k + halfN) / n
  let c2 := (glvB1 * k + halfN) / n
  ((k : Int) - ((c1 * glvA1 + c2 * glvA2 : Nat) : Int), ((c1 * glvB1 : Nat) : Int) - ((c2 * glvA1 : Nat) : Int))

/-- `k ≡ k1 + k2·lam (mod n)`, as a run-time check. -/
def glvRel (k : Nat) (s : Int × Int) : Bool := (s.1 + s.2 * (lam : Int) - (k : Int)) % (n : Int) == 0
/-- Both halves are below `2^129` in absolute value, as a run-time check. -/
def glvSmall (s : Int × Int) : Bool := s.1.natAbs < glvBound && s.2.natAbs < glvBound

def glvPick (k : Nat) (c : Int × Int) : Int × Int :=
  if glvSmall c && glvRel k c then c else ((k : Int), 0)

/-- `(k1, k2)` with `k ≡ k1 + k2·lam (mod n)`: the rounded candidate when it passes both
    checks, else `(k, 0)`. -/
def glvSplit (k : Nat) : Int × Int := glvPick k (glvCandidate k)

/-- Kind: decomposition identity (checked at run time, with a fall-back).
    Says: for every `k` the two halves satisfy `k1 + k2·lam ≡ k (mod n)`.
    Does not say: that `φ` is multiplication by `lam` on the curve (tested), or that the
    candidate ever fails the check (it did not in any test). -/
theorem glvSplit_rel (k : Nat) : glvRel k (glvSplit k) = true := by
  unfold glvSplit glvPick
  by_cases h : (glvSmall (glvCandidate k) && glvRel k (glvCandidate k)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true] at h
    exact h.2
  · rw [if_neg h]
    simp [glvRel]

theorem glvSplit_identity (k : Nat) :
    ((glvSplit k).1 + (glvSplit k).2 * (lam : Int) - (k : Int)) % (n : Int) = 0 := by
  have h := glvSplit_rel k
  unfold glvRel at h
  first
    | exact eq_of_beq h
    | exact beq_iff_eq.mp h
    | simpa using h

/-- Kind: size bound (checked at run time, with a fall-back).
    Says: both halves are below `2^129` in absolute value, or the decomposition is the
    trivial `(k, 0)`.
    Does not say: that the trivial case never occurs (tested only; the theory gives
    `|k1|, |k2| < 2^128` for this basis). -/
theorem glvSplit_bound (k : Nat) : glvSmall (glvSplit k) = true ∨ glvSplit k = ((k : Int), 0) := by
  unfold glvSplit glvPick
  by_cases h : (glvSmall (glvCandidate k) && glvRel k (glvCandidate k)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true] at h
    exact Or.inl h.1
  · rw [if_neg h]
    exact Or.inr rfl

/-- Kind: constants (by evaluation).
    Says: `lam` is a root of `x² + x + 1` modulo `n`, `beta` is a cube root of one modulo `p`,
    and both basis vectors lie in the lattice `a + b·lam ≡ 0 (mod n)` (the first has `b = −glvB1`).
    Does not say: `n` or `p` is prime, or which of the two non-trivial roots pairs with which
    (the guard on `lgTable` tests `[lam]G = (beta·gx, gy)`). -/
theorem lam_cubic : (lam * lam + lam + 1) % n = 0 := by first | decide | rfl
theorem beta_cubic : beta * beta % p * beta % p = 1 := by first | decide | rfl
theorem glv_basis_1 : (glvA1 + (n - glvB1) * lam) % n = 0 := by first | decide | rfl
theorem glv_basis_2 : (glvA2 + glvA1 * lam) % n = 0 := by first | decide | rfl

/-! ### Scalar inverse -/

def scalarInvCandidate (a : Nat) : Nat := (Ff.xgcd scalarField.n (U256.ofNat a)).toNat

def scalarInvPick (a x : Nat) : Nat := if a * x % n = 1 then x else scalarInv a

/-- Inverse modulo the group order by the binary extended GCD on limbs, checked by a
    multiplication; any candidate that fails the check is replaced by the old `scalarInv`. -/
def scalarInvFast (a : Nat) : Nat := scalarInvPick a (scalarInvCandidate a)

/-- Kind: checked result.
    Says: `scalarInvFast a` is the old `scalarInv a`, or it satisfies `a · x mod n = 1`.
    Does not say: that the two agree when the check passes (they do if `n` is prime and the old
    routine is right; neither is proved), or that the result is below `n` (tested). -/
theorem scalarInvFast_spec (a : Nat) : scalarInvFast a = scalarInv a ∨ a * scalarInvFast a % n = 1 := by
  unfold scalarInvFast scalarInvPick
  by_cases h : a * scalarInvCandidate a % n = 1
  · rw [if_pos h]; exact Or.inr h
  · rw [if_neg h]; exact Or.inl rfl

#print axioms glvSplit_rel
#print axioms glvSplit_identity
#print axioms glvSplit_bound
#print axioms lam_cubic
#print axioms beta_cubic
#print axioms glv_basis_1
#print axioms glv_basis_2
#print axioms scalarInvFast_spec

end EVMCleanroom.Precompiles.Secp256k1
