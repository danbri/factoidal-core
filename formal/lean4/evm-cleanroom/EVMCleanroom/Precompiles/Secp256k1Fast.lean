import EVMCleanroom.Precompiles.Secp256k1
import EVMCleanroom.Precompiles.Secp256k1FieldFast
import EVMCleanroom.Precompiles.ScalarMul

/-!
# secp256k1: fast paths for public data

`recoverFast`, `mulAddFast` and `mulBaseFast` have the contracts of
`Secp256k1.recover`, `mulAdd` and `mulBase` and are several times faster.
**They are for public data only and must never be given a secret scalar**:
their running time, their table indices and their branches depend on the
scalars (see `docs/designissues/2026-11-27-ethereum-secp256k1-fast-paths-timing.md`).
`Secp256k1.recover`/`mulAdd`/`mulBase` are unchanged and remain the definition
and the differential oracle.

How `[u1]G + [u2]Q` is computed:

* each scalar is split with the curve endomorphism `φ(x, y) = (β·x, y)`, which
  acts as multiplication by `λ` (Gallant, Lambert and Vanstone, "Faster point
  multiplication on elliptic curves with efficient endomorphisms", CRYPTO
  2001): `k ≡ k1 + k2·λ (mod n)` with `|k1|, |k2| < 2^129`, using the
  rounding of their Algorithm 3.74 form (Hankerson, Menezes and Vanstone 2004)
  on the reduced basis `(a1, b1), (a2, b2)`;
* the four half-length scalars are recoded into signed digits
  (`ScalarMul.wnaf`: half-window 128 for the two `G` halves, 16 for the two
  `Q` halves) and consumed by one shared doubling chain (Straus 1964);
* the `G` halves read two fixed tables of 64 affine points each (the odd
  multiples of `G` and of `φ(G)`, built once), added with a mixed addition;
  the `Q` halves read two tables of 8 Jacobian points built per call;
* points are twelve 64-bit limbs in one object, and the point formulas are
  compiled with the field operations of `Secp256k1FieldFast` inlined.

Formulas: Jacobian doubling for `a = 0` with `S = 4·X·Y²` and `M = 3·X²`
(Cohen, Miyaji and Ono 1998), chord addition and mixed addition in the same
coordinates; the special cases (infinity, equal points, opposite points) are
explicit branches.

Proved here:
* the decomposition identity and its size bound hold for every scalar
  (`glvSplit_identity`, `glvSplit_bound`): both are **checked at run time** on
  the candidate, and a candidate that failed either check would be replaced by
  the trivial decomposition `(k, 0)`, for which the identity is immediate;
* `λ² + λ + 1 ≡ 0 (mod n)`, `β³ ≡ 1 (mod p)` and the basis relations
  (`lam_cubic`, `beta_cubic`, `glv_basis_1`, `glv_basis_2`), by evaluation;
* the shared doubling chain of the fast path runs at most `maxLen = 136` times
  (`go_len`): the length is checked, and a longer recoding (not expected: the
  tested maximum is 130) is handed to the old path;
* every returned point passed the curve equation in the `Nat` field
  (`mulBaseFast_onCurve`, `mulAddFast_onCurve`, `recoverFast_onCurve`), and
  out-of-range signatures recover nothing (`recoverFast_range`);
* the scalar inverse is either the old one or passed the check
  `a · x mod n = 1` (`scalarInvFast_spec`).

Tested, not proved: that the fast functions return what the old ones return.
No group law is proved in this package, the limb field is not proved against
the `Nat` field, and the endomorphism is not proved to be multiplication by
`λ`. The evidence is the guards below (edge cases against the old functions),
the run-time differential check of `evm-secpperf` in CI, and the published
ECRECOVER vectors through the router.
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

namespace Fast

/-! ### Points: twelve limbs in one object -/

/-- A Jacobian point `(X, Y, Z)`; infinity is `Z = 0`. -/
structure Pt where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  y0 : UInt64
  y1 : UInt64
  y2 : UInt64
  y3 : UInt64
  z0 : UInt64
  z1 : UInt64
  z2 : UInt64
  z3 : UInt64

/-- An affine point. -/
structure Aff where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  y0 : UInt64
  y1 : UInt64
  y2 : UInt64
  y3 : UInt64

@[inline] def Pt.x (p : Pt) : U256 := ⟨p.x0, p.x1, p.x2, p.x3⟩
@[inline] def Pt.y (p : Pt) : U256 := ⟨p.y0, p.y1, p.y2, p.y3⟩
@[inline] def Pt.z (p : Pt) : U256 := ⟨p.z0, p.z1, p.z2, p.z3⟩
@[inline] def Pt.ofXYZ (x y z : U256) : Pt :=
  ⟨x.l0, x.l1, x.l2, x.l3, y.l0, y.l1, y.l2, y.l3, z.l0, z.l1, z.l2, z.l3⟩
@[inline] def Aff.x (p : Aff) : U256 := ⟨p.x0, p.x1, p.x2, p.x3⟩
@[inline] def Aff.y (p : Aff) : U256 := ⟨p.y0, p.y1, p.y2, p.y3⟩
@[inline] def Aff.ofXY (x y : U256) : Aff := ⟨x.l0, x.l1, x.l2, x.l3, y.l0, y.l1, y.l2, y.l3⟩

def infinity : Pt := ⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩
def affZero : Aff := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
@[inline] def Pt.isInfinity (p : Pt) : Bool := (p.z0 ||| p.z1 ||| p.z2 ||| p.z3) == 0

/-- `[2]p`. Three multiplications and four squarings; infinity maps to infinity (`Z₃ = 2·Y·Z`). -/
def dbl (p : Pt) : Pt :=
  let x := p.x
  let y := p.y
  let z := p.z
  let a := Ff.sqr x
  let b := Ff.sqr y
  let c := Ff.sqr b
  let d := Ff.mulSmall (Ff.mul x b) 4
  let e := Ff.mulSmall a 3
  let f := Ff.sqr e
  let x3 := Ff.sub f (Ff.add d d)
  let y3 := Ff.sub (Ff.mul e (Ff.sub d x3)) (Ff.mulSmall c 8)
  let yz := Ff.mul y z
  Pt.ofXYZ x3 y3 (Ff.add yz yz)

/-- `p + q` for an affine `q` (negated first when `negate` is set). Eight multiplications and
    three squarings in the general case. -/
def madd (p : Pt) (q : Aff) (negate : Bool) : Pt :=
  let qx := q.x
  let qy := Ff.cneg negate q.y
  if p.isInfinity then Pt.ofXYZ qx qy Ff.one
  else
    let x := p.x
    let y := p.y
    let z := p.z
    let zz := Ff.sqr z
    let u2 := Ff.mul qx zz
    let s2 := Ff.mul (Ff.mul qy z) zz
    let h := Ff.sub u2 x
    let r := Ff.sub s2 y
    if U256.isZero h then
      if U256.isZero r then dbl p else infinity
    else
      let hh := Ff.sqr h
      let hhh := Ff.mul hh h
      let v := Ff.mul x hh
      let x3 := Ff.sub (Ff.sub (Ff.sqr r) hhh) (Ff.add v v)
      let y3 := Ff.sub (Ff.mul r (Ff.sub v x3)) (Ff.mul y hhh)
      Pt.ofXYZ x3 y3 (Ff.mul z h)

/-- `p + q` for Jacobian points (`q` negated first when `negate` is set). Twelve multiplications
    and four squarings in the general case. -/
def padd (p q : Pt) (negate : Bool) : Pt :=
  if p.isInfinity then Pt.ofXYZ q.x (Ff.cneg negate q.y) q.z
  else if q.isInfinity then p
  else
    let x1 := p.x
    let y1 := p.y
    let z1 := p.z
    let x2 := q.x
    let y2 := Ff.cneg negate q.y
    let z2 := q.z
    let z1z1 := Ff.sqr z1
    let z2z2 := Ff.sqr z2
    let u1 := Ff.mul x1 z2z2
    let u2 := Ff.mul x2 z1z1
    let s1 := Ff.mul (Ff.mul y1 z2) z2z2
    let s2 := Ff.mul (Ff.mul y2 z1) z1z1
    let h := Ff.sub u2 u1
    let r := Ff.sub s2 s1
    if U256.isZero h then
      if U256.isZero r then dbl p else infinity
    else
      let hh := Ff.sqr h
      let hhh := Ff.mul hh h
      let v := Ff.mul u1 hh
      let x3 := Ff.sub (Ff.sub (Ff.sqr r) hhh) (Ff.add v v)
      let y3 := Ff.sub (Ff.mul r (Ff.sub v x3)) (Ff.mul s1 hhh)
      Pt.ofXYZ x3 y3 (Ff.mul (Ff.mul h z1) z2)

/-! ### Tables -/

def betaL : U256 := U256.ofNat beta

/-- The endomorphism `φ` on a Jacobian and on an affine point: `X ↦ beta·X`. -/
def lamPt (p : Pt) : Pt := Pt.ofXYZ (Ff.mul p.x betaL) p.y p.z
def lamAff (p : Aff) : Aff := Aff.ofXY (Ff.mul p.x betaL) p.y

def oddLoop (twice : Pt) : Nat → Pt → Array Pt → Array Pt
  | 0, _, acc => acc
  | c+1, cur, acc => oddLoop twice c (padd cur twice false) (acc.push cur)

/-- `[1]p, [3]p, …, [2·count − 1]p`. -/
def oddTable (p : Pt) (count : Nat) : Array Pt := oddLoop (dbl p) count p #[]

/-- Running products `z₀, z₀z₁, …` of the `Z` coordinates. -/
def prefixLoop (pts : Array Pt) : Nat → Nat → U256 → Array U256 → Array U256
  | 0, _, _, acc => acc
  | c+1, i, run, acc =>
    let next := Ff.mulO run (pts.getD i infinity).z
    prefixLoop pts c (i + 1) next (acc.push next)

/-- From the last point down: `inv` is the inverse of the product up to index `i`. -/
def affLoop (pts : Array Pt) (pre : Array U256) : Nat → U256 → Array Aff → Array Aff
  | 0, _, acc => acc
  | i+1, inv, acc =>
    let p := pts.getD i infinity
    let zi := if i = 0 then inv else Ff.mulO inv (pre.getD (i - 1) Ff.one)
    let zi2 := Ff.sqrO zi
    affLoop pts pre i (Ff.mulO inv p.z)
      (acc.push (Aff.ofXY (Ff.mulO p.x zi2) (Ff.mulO p.y (Ff.mulO zi2 zi))))

/-- Affine forms of finite points with one field inversion (Montgomery's simultaneous
    inversion, 1987). The points must not be at infinity. -/
def toAffTable (pts : Array Pt) : Array Aff :=
  let pre := prefixLoop pts pts.size 0 Ff.one #[]
  (affLoop pts pre pts.size (Ff.inv (pre.getD (pts.size - 1) Ff.one)) #[]).reverse

def gPt : Pt := Pt.ofXYZ (U256.ofNat gx) (U256.ofNat gy) Ff.one

/-- The odd multiples `G, 3G, …, 127G`, affine. Built once. -/
def gTable : Array Aff := toAffTable (oddTable gPt 64)
/-- `φ` of the same points: the odd multiples of `[lam]G`. -/
def lgTable : Array Aff := gTable.map lamAff

/-! ### The shared doubling chain -/

@[inline] def addG (table : Array Aff) (d : Int) (flip : Bool) (acc : Pt) : Pt :=
  if d = 0 then acc else madd acc (table.getD (d.natAbs / 2) affZero) (flip != decide (d < 0))

@[inline] def addQ (table : Array Pt) (d : Int) (flip : Bool) (acc : Pt) : Pt :=
  if d = 0 then acc else padd acc (table.getD (d.natAbs / 2) infinity) (flip != decide (d < 0))

/-- Digits from index `i − 1` down to 0: one doubling, then at most four additions. -/
def mainLoop (qT lqT : Array Pt) (d1 d2 d3 d4 : Array Int) (f1 f2 f3 f4 : Bool) : Nat → Pt → Pt
  | 0, acc => acc
  | i+1, acc =>
    mainLoop qT lqT d1 d2 d3 d4 f1 f2 f3 f4 i
      (addQ lqT (d4.getD i 0) f4 (addQ qT (d3.getD i 0) f3
        (addG lgTable (d2.getD i 0) f2 (addG gTable (d1.getD i 0) f1 (dbl acc)))))

/-- The recoded halves of `u1` (for `G`, `φ(G)`) and `u2` (for `Q`, `φ(Q)`), their signs,
    and the length of the longest. -/
structure Plan where
  d1 : Array Int
  d2 : Array Int
  d3 : Array Int
  d4 : Array Int
  f1 : Bool
  f2 : Bool
  f3 : Bool
  f4 : Bool
  len : Nat

def planOf (s1 s2 : Int × Int) (d1 d2 d3 d4 : Array Int) : Plan :=
  { d1 := d1, d2 := d2, d3 := d3, d4 := d4,
    f1 := decide (s1.1 < 0), f2 := decide (s1.2 < 0), f3 := decide (s2.1 < 0), f4 := decide (s2.2 < 0),
    len := max (max d1.size d2.size) (max d3.size d4.size) }

def planSplit (s1 s2 : Int × Int) : Plan :=
  planOf s1 s2 (ScalarMul.wnaf 128 s1.1.natAbs) (ScalarMul.wnaf 128 s1.2.natAbs)
    (ScalarMul.wnaf 16 s2.1.natAbs) (ScalarMul.wnaf 16 s2.2.natAbs)

def plan (u1 u2 : Nat) : Plan := planSplit (glvSplit u1) (glvSplit u2)

/-- The most doublings the fast path will do. -/
def maxLen : Nat := 136

def runPlan (pl : Plan) (qT : Array Pt) : Pt :=
  mainLoop qT (qT.map lamPt) pl.d1 pl.d2 pl.d3 pl.d4 pl.f1 pl.f2 pl.f3 pl.f4 pl.len infinity

/-- Run a plan with the table of `q`; `none` when the recoding is longer than `maxLen`. -/
def go (pl : Plan) (qT : Array Pt) : Option Pt :=
  if pl.len ≤ maxLen then some (runPlan pl qT) else none

/-- `[u1]G + [u2]q` for `u1, u2 < n` and a finite `q` on the curve. -/
def mulAddPt (u1 u2 : Nat) (q : Pt) : Option Pt := go (plan u1 u2) (oddTable q 8)

/-- `[k]G` for `k < n`: the same chain with no `Q` digits. -/
def mulBasePt (k : Nat) : Option Pt := go (plan k 0) #[]

/-- Kind: loop bound (checked at run time).
    Says: when the fast path runs, its doubling chain has at most `maxLen = 136` steps, each
    with at most four additions.
    Does not say: that the recoding is never longer (tested: at most 130; a longer one is
    handed to the old path by the callers). -/
theorem go_len (pl : Plan) (qT : Array Pt) (r : Pt) (h : go pl qT = some r) :
    pl.len ≤ maxLen ∧ r = mainLoop qT (qT.map lamPt) pl.d1 pl.d2 pl.d3 pl.d4 pl.f1 pl.f2 pl.f3 pl.f4 pl.len
      infinity := by
  unfold go at h
  by_cases hl : pl.len ≤ maxLen
  · rw [if_pos hl] at h
    cases h
    exact ⟨hl, rfl⟩
  · rw [if_neg hl] at h
    cases h

/-- Affine coordinates as natural numbers, given the inverse of `Z`. -/
def affineOf (pt : Pt) (zi : U256) : Nat × Nat :=
  let zi2 := Ff.sqrO zi
  ((Ff.mulO pt.x zi2).toNat, (Ff.mulO pt.y (Ff.mulO zi2 zi)).toNat)

/-- Keep a pair only if it satisfies the curve equation in the `Nat` field (`Secp256k1.onCurve`). -/
def keepOnCurve (c : Nat × Nat) : Option (Nat × Nat) := if onCurve c.1 c.2 then some c else none

/-- Affine coordinates as natural numbers, kept only if they satisfy the curve equation in the
    `Nat` field; one field inversion. -/
def checkedAffineFast (pt : Pt) : Option (Nat × Nat) :=
  if pt.isInfinity then none else keepOnCurve (affineOf pt (Ff.inv pt.z))

/-- Kind: on-curve preservation (checked at run time).
    Says: every point returned by `checkedAffineFast` has canonical coordinates and satisfies
    `y² = x³ + 7` in the `Nat` field.
    Does not say: it is the group-theoretic result of the operation that produced it. -/
theorem keepOnCurve_onCurve (c : Nat × Nat) (x y : Nat) (h : keepOnCurve c = some (x, y)) :
    onCurve x y = true := by
  unfold keepOnCurve at h
  split at h
  · rename_i hCurve
    cases h
    exact hCurve
  · cases h

theorem checkedAffineFast_onCurve (pt : Pt) (x y : Nat) (h : checkedAffineFast pt = some (x, y)) :
    onCurve x y = true := by
  unfold checkedAffineFast at h
  split at h
  · cases h
  · exact keepOnCurve_onCurve _ _ _ h

/-- The candidate root with the wanted parity, if its square is `rhs`. -/
def pickRoot (rhs root : U256) (parity : Nat) : Option U256 :=
  if U256.beq (Ff.sqrO root) rhs then some (Ff.cneg ((root.l0 &&& 1) != parity.toUInt64) root) else none

/-- The ordinate with the given parity for abscissa `x < p`, when `x³ + 7` is a square. -/
def liftY (x : U256) (parity : Nat) : Option U256 :=
  let rhs := Ff.add (Ff.mulO (Ff.sqrO x) x) ⟨7, 0, 0, 0⟩
  pickRoot rhs (Ff.sqrtCandidate rhs) parity

/-- `[u1]G + [u2](x, y)` checked; the old path when the fast one declines. -/
def mulAddChecked (u1 u2 x : Nat) (y : U256) : Option (Nat × Nat) :=
  match mulAddPt u1 u2 (Pt.ofXYZ (U256.ofNat x) y Ff.one) with
  | some pt => checkedAffineFast pt
  | none => mulAdd u1 u2 (x, y.toNat)

theorem mulAddChecked_onCurve (u1 u2 x : Nat) (y : U256) (a b : Nat)
    (h : mulAddChecked u1 u2 x y = some (a, b)) : onCurve a b = true := by
  unfold mulAddChecked at h
  split at h
  · exact checkedAffineFast_onCurve _ _ _ h
  · exact mulAdd_onCurve _ _ _ _ _ h

end Fast

open Fast

/-! ### The public functions -/

/-- `[k]G` for a **public** scalar; `none` for the point at infinity. Variable-time. -/
def mulBaseFast (k : Nat) : Option (Nat × Nat) :=
  match mulBasePt (k % n) with
  | some pt => checkedAffineFast pt
  | none => mulBase k

/-- `[u1]G + [u2]Q` for **public** scalars and an affine `Q`; `none` for the point at infinity.
    A `Q` that is not on the curve goes to the old path. Variable-time. -/
def mulAddFast (u1 u2 : Nat) (q : Nat × Nat) : Option (Nat × Nat) :=
  if onCurve q.1 q.2 then mulAddChecked (u1 % n) (u2 % n) q.1 (U256.ofNat q.2) else mulAdd u1 u2 q

/-- The public key for message hash `z`, parity bit and signature `(r, s)`, with the contract of
    `Secp256k1.recover` (full range `[1, n−1]` for `s`). Public data only. Variable-time. -/
def recoverFast (z parity r s : Nat) : Option (Nat × Nat) :=
  if r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s ∨ 1 < parity then none
  else
    match liftY (U256.ofNat r) parity with
    | none => none
    | some y => mulAddChecked ((n - z % n) * scalarInvFast r % n) (s * scalarInvFast r % n) r y

/-- Kind: on-curve preservation.
    Says: `mulBaseFast`, `mulAddFast` and `recoverFast` return only points that satisfy the
    curve equation in the `Nat` field, with canonical coordinates.
    Does not say: they return the correct multiple or key, or the same as the old functions
    (tested, not proved). -/
theorem mulBaseFast_onCurve (k x y : Nat) (h : mulBaseFast k = some (x, y)) : onCurve x y = true := by
  unfold mulBaseFast at h
  split at h
  · exact checkedAffineFast_onCurve _ _ _ h
  · exact mulBase_onCurve _ _ _ h

theorem mulAddFast_onCurve (u1 u2 : Nat) (q : Nat × Nat) (x y : Nat)
    (h : mulAddFast u1 u2 q = some (x, y)) : onCurve x y = true := by
  unfold mulAddFast at h
  split at h
  · exact mulAddChecked_onCurve _ _ _ _ _ _ h
  · exact mulAdd_onCurve _ _ _ _ _ h

theorem recoverFast_onCurve (z parity r s x y : Nat) (h : recoverFast z parity r s = some (x, y)) :
    onCurve x y = true := by
  unfold recoverFast at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact mulAddChecked_onCurve _ _ _ _ _ _ h

/-- Kind: range check.
    Says: `r` or `s` outside `[1, n-1]`, or a parity above one, recovers nothing.
    Does not say: in-range signatures are valid. -/
theorem recoverFast_range (z parity r s : Nat) (h : r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s ∨ 1 < parity) :
    recoverFast z parity r s = none := by
  simp [recoverFast, h]

/-! ### Guards (tests) against the old functions -/

private def affNat (a : Aff) : Nat × Nat := (a.x.toNat, a.y.toNat)

-- The fixed tables: entry `i` is `[2i+1]G`, and `φ` of it is `[(2i+1)·lam]G`.
#guard gTable.size == 64 && lgTable.size == 64
#guard (List.range 64).all fun i => some (affNat (gTable.getD i affZero)) == mulBase (2 * i + 1)
#guard [0, 1, 31, 63].all fun i => some (affNat (lgTable.getD i affZero)) == mulBase ((2 * i + 1) * lam % n)
#guard mulBase lam == some (beta * gx % p, gy)

-- Decomposition: the halves are short, and both signs occur.
private def splitCases : List Nat :=
  [0, 1, 2, n - 1, n - 2, lam, n - lam, lam + 1, lam - 1, 2 ^ 128, 2 ^ 128 - 1, 2 ^ 255, n / 2, n / 2 + 1, n / 3,
   0xdeadbeefcafebabe0123456789abcdeffedcba9876543210aaaaaaaa55555555,
   0x3086d221a7d46bcde86c90e49284eb15, 0xe4437ed6010e88286f547fa90abfe4c3,
   0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0]
#guard splitCases.all fun k => glvSmall (glvCandidate k) && glvRel k (glvCandidate k)
#guard glvSplit 0 == (0, 0) && glvSplit 1 == (1, 0) && glvSplit lam == (0, 1) && glvSplit (n - 1) == (-1, 0)
  && glvSplit (n - lam) == (0, -1)
#guard splitCases.any (fun k => (glvSplit k).1 < 0 && (glvSplit k).2 < 0)
  && splitCases.any (fun k => (glvSplit k).1 < 0 && (glvSplit k).2 > 0)
  && splitCases.any (fun k => (glvSplit k).1 > 0 && (glvSplit k).2 < 0)
#guard splitCases.all fun k => (plan k (n - 1 - k)).len ≤ 130

-- Scalar inverse.
#guard [1, 2, 3, n - 1, n - 2, lam, 2 ^ 128, 2 ^ 255 + 1].all fun a =>
  scalarInvCandidate a == scalarInv a && scalarInvFast a == scalarInv a
#guard scalarInvFast 0 == 0

-- Fixed base, including scalars with a zero or negative half and results at infinity.
#guard splitCases.all fun k => mulBaseFast k == mulBase k
#guard mulBaseFast n == none && mulBaseFast (n + 5) == mulBase 5 && mulBaseFast (2 * n) == none
#guard (splitCases.filterMap fun k => mulBasePt (k % n)).length == splitCases.length

-- Double multiplication: `u1 = 0`, `u2 = 0`, `Q = ±G`, sums at infinity, and general cases.
private def g1 : Nat × Nat := (gx, gy)
private def gNeg : Nat × Nat := (gx, p - gy)
private def q3 : Nat × Nat := (0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9,
   0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672)
private def addCases : List (Nat × Nat × (Nat × Nat)) :=
  [(0, 0, g1), (1, 0, g1), (0, 1, g1), (1, 1, g1), (1, 1, gNeg), (1, n - 1, g1), (n - 1, 1, g1), (2, 2, gNeg),
   (5, 7, q3), (n - 6, 2, q3), (0, 1, q3), (0, n - 1, q3), (0xdeadbeef, 0, q3), (lam, lam, q3), (n - lam, lam, g1),
   (lam, 1, gNeg), (3, n - 1, q3), (n - 3, 1, q3), (2 ^ 255, 2 ^ 254 + 1, q3),
   (0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0, n / 3, q3),
   (n / 3, 0xdeadbeefcafebabe0123456789abcdeffedcba9876543210aaaaaaaa55555555, gNeg)]
#guard addCases.all fun (u1, u2, q) => mulAddFast u1 u2 q == mulAdd u1 u2 q
#guard mulAddFast 1 1 gNeg == none && mulAddFast (n - 6) 2 q3 == none && mulAddFast 5 7 q3 == mulBase 26
-- A point that is not on the curve goes to the old path.
#guard mulAddFast 3 5 (1, 1) == mulAdd 3 5 (1, 1)

-- Recovery: a known signature, both parities, high `s`, hash edge values, an `r` that is no abscissa.
private def tz : Nat := 0x18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c
private def tr : Nat := 0x73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f
private def ts : Nat := 0xeeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549
private def recCases : List (Nat × Nat × Nat × Nat) :=
  [(tz, 1, tr, ts), (tz, 0, tr, ts), (tz, 0, tr, n - ts), (tz, 1, tr, n - ts), (0, 1, tr, ts), (n, 0, tr, ts),
   (2 ^ 256 - 1, 1, tr, ts), (tz, 1, 1, 1), (tz, 0, 1, n - 1), (tz, 0, n - 1, 1), (tz, 1, 5, 7), (tz, 0, 2, 3),
   (tz, 0, gx, 1), (0, 0, gx, gx), (n - gx, 1, gx, 1), (tz, 2, tr, ts), (tz, 1, 0, ts), (tz, 1, tr, 0),
   (tz, 1, n, ts), (tz, 1, tr, n), (tz, 1, p - 1, ts)]
#guard recCases.all fun (z, v, r, s) => recoverFast z v r s == recover z v r s
#guard (recoverFast tz 1 tr ts).isSome && recoverFast tz 1 5 7 == none

#print axioms glvSplit_rel
#print axioms glvSplit_identity
#print axioms glvSplit_bound
#print axioms lam_cubic
#print axioms beta_cubic
#print axioms glv_basis_1
#print axioms glv_basis_2
#print axioms scalarInvFast_spec
#print axioms Fast.go_len
#print axioms Fast.keepOnCurve_onCurve
#print axioms Fast.checkedAffineFast_onCurve
#print axioms Fast.mulAddChecked_onCurve
#print axioms mulBaseFast_onCurve
#print axioms mulAddFast_onCurve
#print axioms recoverFast_onCurve
#print axioms recoverFast_range

end EVMCleanroom.Precompiles.Secp256k1
