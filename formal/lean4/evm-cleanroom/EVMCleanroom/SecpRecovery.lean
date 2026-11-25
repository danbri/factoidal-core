import EVMCleanroom.Keccak

/-!
Independent experimental secp256k1 public-key recovery for Ethereum
transactions (SEC 2 section 2.4.1; ECDSA recovery equation; EIP-2).
Only public protocol data is consumed. No signing, private keys, FFI,
external implementation or runtime proof assistance. General group-law,
field-primality, cryptographic refinement and native cost proofs remain open.
-/
namespace EVMCleanroom.SecpRecovery

def p : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def n : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

structure Acceptance where
  private mk ::

/-- For explicitly opted-in experimental test execution only. -/
def dangerouslyAcceptUnverified : Acceptance := ⟨⟩

inductive Failure where
  | invalidSignature
  | arithmeticRefusal
  deriving Repr, BEq

inductive Point where
  | infinity
  | affine (x y : Nat)
  deriving Repr, BEq

def generator : Point := .affine
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

def onCurve : Point → Bool
  | .infinity => false
  | .affine x y => x < p && y < p && y*y % p == (x*x*x+7) % p

def subMod (m a b : Nat) : Nat := (a % m + m - b % m) % m

/-- Bounded square-and-multiply, used for the field square root. -/
def powLoop (m : Nat) : Nat → Nat → Nat → Nat → Option Nat
  | 0, e, _, acc => if e == 0 then some acc else none
  | fuel+1, e, b, acc =>
    if e == 0 then some acc
    else powLoop m fuel (e / 2) (b*b % m)
      (if e % 2 == 1 then acc*b % m else acc)

/-- Euclidean remainders with coefficients reduced modulo m. The returned
candidate is independently checked before use. Exhaustion is not invalidity. -/
def invLoop (m : Nat) : Nat → Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel+1, r0, r1, t0, t1 =>
    if r1 == 0 then
      if r0 == 1 then some t0 else none
    else invLoop m fuel r1 (r0 % r1) t1 (subMod m t0 ((r0 / r1)*t1))

def checkedInverse (m a : Nat) : Option Nat := do
  let candidate ← invLoop m 512 m (a % m) 0 1
  if a*candidate % m == 1 then some candidate else none

private def slopeAdd (x y u l : Nat) : Point :=
  let x' := subMod p (subMod p (l*l) x) u
  .affine x' (subMod p (l * subMod p x x') y)

/-- Affine addition; the point at infinity is distinct from arithmetic refusal. -/
def add (a b : Point) : Option Point :=
  match a, b with
  | .infinity, q => some q
  | q, .infinity => some q
  | .affine x y, .affine u v =>
    if x == u then
      if (y+v) % p == 0 then some .infinity
      else do
        let inv ← checkedInverse p (2*y % p)
        some (slopeAdd x y u (3*x*x*inv % p))
    else do
      let inv ← checkedInverse p (subMod p u x)
      some (slopeAdd x y u (subMod p v y * inv % p))

def mulLoop : Nat → Nat → Point → Point → Option Point
  | 0, k, _, acc => if k == 0 then some acc else none
  | fuel+1, k, q, acc =>
    if k == 0 then some acc
    else
      match (if k % 2 == 1 then add acc q else some acc), add q q with
      | some next, some doubled => mulLoop fuel (k / 2) doubled next
      | _, _ => none

def mul (k : Nat) (q : Point) : Option Point := mulLoop 256 k q .infinity

/-- Cancun transaction rule. High-S ECRECOVER is a separate future path. -/
def signatureBounds (z parity r s : Nat) : Bool :=
  z < 2^256 && parity < 2 && 0 < r && r < n && 0 < s && s ≤ n/2

def recoveryPoint (r parity : Nat) : Except Failure Point := do
  let a := (r*r*r+7) % p
  let y ← (powLoop p 256 ((p+1)/4) a 1).toExcept .arithmeticRefusal
  if y*y % p != a then throw .invalidSignature
  let q := Point.affine r (if y % 2 == parity then y else (p-y) % p)
  if !onCurve q then throw .invalidSignature
  return q

def combine (u v : Nat) (q : Point) : Option Point := do
  let a ← mul u generator
  let b ← mul v q
  add a b

def candidate (z parity r s : Nat) : Except Failure Point := do
  let q ← recoveryPoint r parity
  let inv ← (checkedInverse n r).toExcept .arithmeticRefusal
  (combine ((n-z%n)*inv%n) (s*inv%n) q).toExcept .arithmeticRefusal

/-- Re-evaluate the actual ECDSA verification equation for the recovered point. -/
def verifyEquation (z r s : Nat) (q : Point) : Option Bool := do
  let w ← checkedInverse n s
  let result ← combine (z*w%n) (r*w%n) q
  return match result with
  | .infinity => false
  | .affine x _ => x % n == r

def checkPoint (z r s : Nat) (q : Point) : Except Failure Point :=
  if !onCurve q then .error .invalidSignature
  else match verifyEquation z r s q with
  | none => .error .arithmeticRefusal
  | some false => .error .invalidSignature
  | some true => .ok q

def recoverPoint (_ : Acceptance) (z parity r s : Nat) : Except Failure Point :=
  if signatureBounds z parity r s then
    match candidate z parity r s with
    | .error error => .error error
    | .ok q => checkPoint z r s q
  else .error .invalidSignature

def fixed32 (v : Nat) : Array UInt8 :=
  (Array.range 32).map fun i => UInt8.ofNat (v / 256^(31-i) % 256)

def addressOf (a : Keccak.Acceptance) (q : Point) : Except Failure Nat :=
  match q with
  | .infinity => .error .arithmeticRefusal
  | .affine x y =>
    .ok (Keccak.experimentalDigestWord a (ByteView.ofArray (fixed32 x ++ fixed32 y)) % 2^160)

def recoverAddress (a : Keccak.Acceptance) (c : Acceptance)
    (z parity r s : Nat) : Except Failure Nat :=
  match recoverPoint c z parity r s with
  | .error e => .error e
  | .ok q => addressOf a q

/-- Kind: admission.
Says: failure of the actual scalar guard cannot recover a point.
Does not say: every permitted signature is valid. -/
theorem refused_bounds (c : Acceptance) (z parity r s : Nat)
    (h : signatureBounds z parity r s = false) :
    recoverPoint c z parity r s = .error .invalidSignature := by
  simp only [recoverPoint, h, Bool.false_eq_true, ↓reduceIte]

/-- Kind: executable linkage.
Says: an accepted point is on the curve and passed the actual ECDSA equation.
Does not say: the arithmetic implements the independent mathematical group. -/
theorem checked_point (z r s : Nat) (q out : Point)
    (h : checkPoint z r s q = .ok out) :
    out = q ∧ onCurve out = true ∧ verifyEquation z r s out = some true := by
  unfold checkPoint at h
  cases curve : onCurve q with
  | false => simp [curve] at h
  | true =>
    cases verdict : verifyEquation z r s q with
    | none => simp [curve, verdict] at h
    | some b =>
      cases b with
      | false => simp [curve, verdict] at h
      | true =>
        simp only [curve, Bool.not_true, Bool.false_eq_true, ↓reduceIte, verdict] at h
        cases h
        exact ⟨rfl, curve, verdict⟩

/-- Kind: executable linkage.
Says: successful recovery used the actual bounded scalar guard and checked point.
Does not say: completeness or collision resistance. -/
theorem recover_checked (c : Acceptance) (z parity r s : Nat) (q : Point)
    (h : recoverPoint c z parity r s = .ok q) :
    signatureBounds z parity r s = true ∧ onCurve q = true ∧
      verifyEquation z r s q = some true := by
  unfold recoverPoint at h
  cases bounds : signatureBounds z parity r s with
  | false => simp [bounds] at h
  | true =>
    cases made : candidate z parity r s with
    | error e => simp [bounds, made] at h
    | ok point =>
      simp only [bounds, ↓reduceIte, made] at h
      exact ⟨rfl, (checked_point z r s point q h).2⟩

#print axioms refused_bounds
#print axioms checked_point
#print axioms recover_checked

end EVMCleanroom.SecpRecovery
