import EVMCleanroom.Precompiles.Curve

/-!
# secp256k1: the one shared field and point module

Jacobian arithmetic on `y² = x³ + 7` over the secp256k1 prime (SEC 2, section
2.4.1), on the shared `Curve` code. This module imports only
`Precompiles.Curve` → `Precompiles.Field` → `Precompiles.Basic` (nothing else,
no Keccak, no EVM), so another package can take exactly these four files
through a `srcDir` library.

API for callers:

* `mulBase k` — `[k]G` as an affine point, for signing and key derivation;
* `mulAdd u1 u2 q` — `[u1]G + [u2]Q` with one shared doubling chain, for
  verification and recovery;
* `recover z parity r s` — the ECDSA public key for a message hash and
  signature, with the full `[1, n-1]` range for `s` (callers that need the
  EIP-2 low-`s` rule check `s ≤ n / 2` themselves);
* `liftX x parity` — the curve point with abscissa `x` and the given parity;
* `scalarInv a` — inverse modulo the group order (zero for zero).

Every point these functions return has passed `onCurve` at run time, so the
theorems below hold for all inputs without assuming any group law. What is
not proved: that the Jacobian formulas compute the group operation (and hence
agreement with the affine arithmetic of `SecpRecovery.lean`). That agreement
is tested: guards here on fixed scalars, and `PrecompileCallTests.lean`
compares recovered keys with the affine implementation.

Nothing here is constant-time. Signing with a secret scalar through `mulBase`
leaks timing; a caller that handles secrets must take that into account.
-/

namespace EVMCleanroom.Precompiles.Secp256k1

def p : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def n : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
def gx : Nat := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
def gy : Nat := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

def field : FieldOps Nat := Fp.ops p
def generator : JPoint Nat := Curve.ofAffine field gx gy

/-- Is the affine pair a point of the curve with canonical coordinates? -/
def onCurve (x y : Nat) : Bool := x < p && y < p && Curve.onCurve field 7 x y

/-- Affine coordinates of a Jacobian point, kept only if they satisfy the curve equation. -/
def checkedAffine (point : JPoint Nat) : Option (Nat × Nat) :=
  match Curve.toAffine field point with
  | some (x, y) => if onCurve x y then some (x, y) else none
  | none => none

/-- `[k]G`; `none` when the result is the point at infinity (`k ≡ 0 mod n`). -/
def mulBase (k : Nat) : Option (Nat × Nat) :=
  checkedAffine (Curve.mul field k generator)

/-- `[u1]G + [u2]Q` for an affine `Q`; `none` for the point at infinity. -/
def mulAdd (u1 u2 : Nat) (q : Nat × Nat) : Option (Nat × Nat) :=
  checkedAffine (Curve.mul2 field u1 generator u2 (Curve.ofAffine field q.1 q.2))

/-- Inverse modulo the group order; zero maps to zero. -/
def scalarInv (a : Nat) : Nat := Fp.inv n a

/-- The point with abscissa `x` whose ordinate has the given parity, if `x³ + 7` is a square. -/
def liftX (x parity : Nat) : Option (Nat × Nat) :=
  match Fp.sqrt? p ((x * x % p * x + 7) % p) with
  | none => none
  | some root =>
    let y := if root % 2 = parity then root else Fp.neg p root
    if onCurve x y then some (x, y) else none

/-- The public key `(x, y)` for message hash `z`, parity bit and signature `(r, s)`:
    `Q = r⁻¹ (s·R − z·G)` with `R` the point of abscissa `r`. -/
def recover (z parity r s : Nat) : Option (Nat × Nat) :=
  if r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s ∨ 1 < parity then none
  else
    match liftX r parity with
    | none => none
    | some point =>
      let rInv := scalarInv r
      mulAdd ((n - z % n) * rInv % n) (s * rInv % n) point

/-- Kind: on-curve preservation (checked at run time).
    Says: every point returned by `checkedAffine` has canonical coordinates and
    satisfies `y² = x³ + 7`.
    Does not say: it is the group-theoretic result of the operation that produced it. -/
theorem checkedAffine_onCurve (point : JPoint Nat) (x y : Nat)
    (h : checkedAffine point = some (x, y)) : onCurve x y = true := by
  unfold checkedAffine at h
  split at h
  · split at h
    · rename_i hCurve
      cases h
      exact hCurve
    · cases h
  · cases h

/-- Kind: on-curve preservation.
    Says: `mulBase`, `mulAdd` and `recover` return only points on the curve.
    Does not say: they return the correct multiple or key (tested, not proved). -/
theorem mulBase_onCurve (k x y : Nat) (h : mulBase k = some (x, y)) : onCurve x y = true :=
  checkedAffine_onCurve _ _ _ h

theorem mulAdd_onCurve (u1 u2 : Nat) (q : Nat × Nat) (x y : Nat)
    (h : mulAdd u1 u2 q = some (x, y)) : onCurve x y = true :=
  checkedAffine_onCurve _ _ _ h

theorem liftX_onCurve (x parity : Nat) (point : Nat × Nat) (h : liftX x parity = some point) :
    onCurve point.1 point.2 = true ∧ point.1 = x := by
  unfold liftX at h
  split at h
  · cases h
  · rename_i root _
    have h' : (if onCurve x (if root % 2 = parity then root else Fp.neg p root) = true then
        some (x, if root % 2 = parity then root else Fp.neg p root) else none) = some point := h
    by_cases hCurve : onCurve x (if root % 2 = parity then root else Fp.neg p root) = true
    · rw [if_pos hCurve] at h'
      cases h'
      exact ⟨hCurve, rfl⟩
    · rw [if_neg hCurve] at h'
      cases h'

theorem recover_onCurve (z parity r s x y : Nat) (h : recover z parity r s = some (x, y)) :
    onCurve x y = true := by
  unfold recover at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact mulAdd_onCurve _ _ _ _ _ h

/-- Kind: range check.
    Says: `r` or `s` outside `[1, n-1]`, or a parity above one, recovers nothing.
    Does not say: in-range signatures are valid. -/
theorem recover_range (z parity r s : Nat) (h : r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s ∨ 1 < parity) :
    recover z parity r s = none := by
  simp [recover, h]

/-- Kind: canonical representation.
    Says: a point accepted by `onCurve` has both coordinates below the field prime.
    Does not say: anything about its order. -/
theorem onCurve_canonical (x y : Nat) (h : onCurve x y = true) : x < p ∧ y < p := by
  simp only [onCurve, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

#guard onCurve gx gy
#guard mulBase 1 == some (gx, gy)
#guard mulBase n == none && mulBase 0 == none
#guard (mulBase (n - 1)).map (·.1) == some gx
-- [2]G and [3]G (the published multiples of the generator, SEC 2 test values).
#guard mulBase 2 == some
  (0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5,
   0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a)
#guard mulBase 3 == some
  (0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9,
   0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672)
-- [a]G + [b]([c]G) = [a + b c]G, and addition of the inverse gives infinity.
#guard (mulBase 3).bind (mulAdd 5 7) == mulBase 26
#guard (mulBase 3).bind (mulAdd (n - 6) 2) == none
#guard (mulBase 0xdeadbeef).bind (mulAdd 0 1) == mulBase 0xdeadbeef
#guard scalarInv 0 == 0 && scalarInv 7 * 7 % n == 1
#guard liftX gx (gy % 2) == some (gx, gy) && liftX gx (1 - gy % 2) == some (gx, p - gy)
#guard liftX 5 0 == none

#print axioms checkedAffine_onCurve
#print axioms mulBase_onCurve
#print axioms mulAdd_onCurve
#print axioms liftX_onCurve
#print axioms recover_onCurve
#print axioms recover_range
#print axioms onCurve_canonical

end EVMCleanroom.Precompiles.Secp256k1
