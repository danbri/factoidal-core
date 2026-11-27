import EVMCleanroom.Precompiles.Curve

/-!
# P256VERIFY (precompile 0x100, EIP-7951)

ECDSA signature verification on secp256r1 (NIST P-256, FIPS 186-5 and SEC 2
section 2.4.2): `y² = x³ − 3x + b` over the 256-bit prime `p`, group order `n`.

Input, exactly 160 bytes: message hash `h`, signature `r`, `s`, public key
`qx`, `qy`, each 32 big-endian bytes. The call always costs 6900 gas and never
halts exceptionally: it returns the 32-byte value one when the signature
verifies and no bytes otherwise (wrong length, `r` or `s` outside `[1, n-1]`,
a coordinate not below `p`, a point off the curve, the encoding `(0, 0)`, the
point at infinity as `R' = [h/s]G + [r/s]Q`, or `R'.x ≢ r (mod n)`).

Proved: gas accounting, the two possible outputs, the input-length rule.
Not proved: the verification equation (published vectors).
-/

namespace EVMCleanroom.Precompiles.P256

def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
def n : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
def a : Nat := p - 3
def b : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
def gx : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
def gy : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

def field : FieldOps Nat := Fp.ops p
def generator : JPoint Nat := Curve.ofAffine field gx gy

def gasCost : Nat := 6900

/-- Does `(r, s)` verify for hash `h` under the public key `(qx, qy)`? -/
def verify (h r s qx qy : Nat) : Bool :=
  if r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s then false
  else if p ≤ qx ∨ p ≤ qy then false
  else if qx = 0 ∧ qy = 0 then false
  else if !Curve.onCurveA field a b qx qy then false
  else
    let sInv := Fp.inv n s
    let point := Curve.mul2A field a (h % n * sInv % n) generator (r * sInv % n) (Curve.ofAffine field qx qy)
    match Curve.toAffine field point with
    | none => false
    | some (x, _) => x % n == r

def one32 : ByteArray := natToBE 32 1

def body (input : ByteArray) : Body :=
  if input.size ≠ 160 then .output ByteArray.empty
  else if verify (beNat input 0 32) (beNat input 32 32) (beNat input 64 32) (beNat input 96 32)
      (beNat input 128 32) then .output one32
  else .output ByteArray.empty

/-- Precompile 0x100. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  charge gas gasCost fun _ => body input

/-- Kind: output contract.
    Says: the body always produces output: either no bytes or the 32-byte value one; and
    any input that is not exactly 160 bytes gives no bytes.
    Does not say: which signatures verify (vectors, not proved). -/
theorem body_output (input : ByteArray) :
    (body input = .output ByteArray.empty ∨ body input = .output one32) ∧
      (input.size ≠ 160 → body input = .output ByteArray.empty) := by
  unfold body
  constructor
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  · intro h; simp [h]

/-- Kind: gas admission and accounting.
    Says: with less than 6900 gas the call fails; with at least 6900 it always succeeds,
    costs exactly 6900, and returns no bytes or exactly the 32-byte value one. There is no
    input that makes a funded call halt.
    Does not say: which case applies. -/
theorem run_total (gas : Nat) (input : ByteArray) :
    (gas < 6900 → run gas input = .failure) ∧
    (6900 ≤ gas → run gas input = .success ByteArray.empty (gas - 6900) ∨
      run gas input = .success one32 (gas - 6900)) := by
  constructor
  · intro h; exact charge_underfunded _ _ _ h
  · intro h
    rcases (body_output input).1 with hBody | hBody
    · exact Or.inl (charge_funded gas gasCost _ _ h hBody)
    · exact Or.inr (charge_funded gas gasCost _ _ h hBody)

/-- Kind: accounting.
    Says: a successful call returns the exact unspent gas.
    Does not say: anything about the output. -/
theorem run_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run gas input = .success out left) : left + 6900 = gas :=
  (charge_success _ _ _ _ _ h).2

/-- Kind: range check.
    Says: `r` or `s` outside `[1, n-1]` never verifies.
    Does not say: in-range signatures verify. -/
theorem verify_range (h r s qx qy : Nat) (hRange : r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s) :
    verify h r s qx qy = false := by
  simp [verify, hRange]

#guard p == 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
#guard Curve.onCurveA field a b gx gy
#guard Curve.isInfinity field (Curve.mul2A field a n generator 0 generator)
#guard !Curve.isInfinity field (Curve.mul2A field a (n - 1) generator 0 generator)
-- [2]G + [3]G = [5]G, and doubling agrees with adding a point to itself.
#guard Curve.same field (Curve.mul2A field a 2 generator 3 generator) (Curve.mul2A field a 5 generator 0 generator)
#guard Curve.same field (Curve.doubleA field a generator) (Curve.addA field a generator generator)
#guard one32.size == 32
#guard (match run 6900 ByteArray.empty with | .success out 0 => out.size == 0 | _ => false)
#guard (match run 6899 ByteArray.empty with | .failure => true | _ => false)

#print axioms body_output
#print axioms run_total
#print axioms run_success
#print axioms verify_range

end EVMCleanroom.Precompiles.P256
