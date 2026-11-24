import Lean

/-! Experimental public-key admission for BLS12-381 G1. No private scalars,
signature verification, pairing or production state-transition acceptance.
Constants: RFC 9380 §8.8.1 and pairing-friendly-curves-11 §4.
All arithmetic below is independently authored over Lean Nat. -/
namespace EthereumConsensus.BLS

def modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def order : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

private def addF (a b : Nat) : Nat := (a + b) % modulus
private def subF (a b : Nat) : Nat := (a + modulus - b % modulus) % modulus
private def mulF (a b : Nat) : Nat := (a * b) % modulus
private def sq (a : Nat) : Nat := mulF a a

-- Fixed fuel: the exponent used below is smaller than 2^381.
private def powLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel+1, base, exponent, acc =>
    powLoop fuel (sq base) (exponent / 2)
      (if exponent % 2 = 1 then mulF acc base else acc)

structure AffinePoint where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

private structure Projective where
  x : Nat
  y : Nat
  z : Nat

private def infinity : Projective := ⟨0, 1, 0⟩
private def lift (p : AffinePoint) : Projective := ⟨p.x, p.y, 1⟩

-- Jacobian coordinates x=X/Z², y=Y/Z³. Tangent formula for a=0.
private def double (p : Projective) : Projective :=
  if p.z = 0 ∨ p.y = 0 then infinity
  else
    let a := sq p.x
    let b := sq p.y
    let c := sq b
    let d := mulF 4 (mulF p.x b)
    let e := mulF 3 a
    let x := subF (sq e) (mulF 2 d)
    let y := subF (mulF e (subF d x)) (mulF 8 c)
    ⟨x, y, mulF 2 (mulF p.y p.z)⟩

-- Mixed addition, derived by clearing the affine chord denominators.
-- H=U-X, R=S-Y. Z'=ZH; handle equal/opposite points first.
private def addMixed (p : Projective) (q : AffinePoint) : Projective :=
  if p.z = 0 then lift q
  else
    let zz := sq p.z
    let u := mulF q.x zz
    let s := mulF q.y (mulF zz p.z)
    let h := subF u p.x
    let r := subF s p.y
    if h = 0 then
      if r = 0 then double p else infinity
    else
      let hh := sq h
      let hhh := mulF h hh
      let v := mulF p.x hh
      let x := subF (subF (sq r) hhh) (mulF 2 v)
      let y := subF (mulF r (subF v x)) (mulF p.y hhh)
      ⟨x, y, mulF p.z h⟩

-- MSB-first multiplication by the fixed 255-bit subgroup order.
private def orderLoop (q : AffinePoint) : Nat → Projective → Projective
  | 0, acc => acc
  | n+1, acc =>
    let d := double acc
    let next := if (order / 2^n) % 2 = 1 then addMixed d q else d
    orderLoop q n next

def subgroupCheck (q : AffinePoint) : Bool :=
  (orderLoop q 255 infinity).z == 0

def largeY (y : Nat) : Bool := decide (y > (modulus - 1) / 2)

def coordinateChecks (q : AffinePoint) (sign : Bool) : Bool :=
  decide (q.x < modulus) && decide (q.y < modulus) &&
  (sq q.y == addF (mulF (sq q.x) q.x) 4) && (largeY q.y == sign)

inductive KeyError where
  | width
  | notCompressed
  | infinityKey
  | nonCanonicalX
  | notOnCurve
  | notSubgroup
  deriving Repr, DecidableEq

private def admitPoint (q : AffinePoint) (sign : Bool) : Except KeyError AffinePoint :=
  if coordinateChecks q sign then
    if subgroupCheck q then .ok q else .error .notSubgroup
  else .error .notOnCurve

private def recover (x : Nat) (sign : Bool) : Except KeyError (AffinePoint × Bool) :=
  if x ≥ modulus then .error .nonCanonicalX
  else
    let rhs := addF (mulF (sq x) x) 4
    let root := powLoop 381 rhs ((modulus + 1) / 4) 1
    let y := if largeY root == sign then root else (modulus - root) % modulus
    .ok (⟨x, y⟩, sign)

private def candidate (bytes : ByteArray) : Except KeyError (AffinePoint × Bool) :=
  if bytes.size ≠ 48 then .error .width
  else
    let encoded := bytes.data.foldl (fun a b => a * 256 + b.toNat) 0
    let flags := encoded / 2^381
    if flags < 4 then .error .notCompressed
    else if flags ≥ 6 then .error .infinityKey
    else recover (encoded % 2^381) (flags == 5)

def decodePublicKey (bytes : ByteArray) : Except KeyError AffinePoint :=
  match candidate bytes with
  | .error e => .error e
  | .ok (q, sign) => admitPoint q sign

/-- Kind: admission. Says: wrong-length input refuses before arithmetic.
Does not say: well-sized keys are valid. -/
theorem decodePublicKey_wrong_width (bytes : ByteArray) (h : bytes.size ≠ 48) :
    decodePublicKey bytes = .error .width := by
  simp only [decodePublicKey, candidate, if_pos h]

/-- Kind: refinement. Says: an admitted result is the actual point and has both
checked predicates. Does not say: projective multiplication refines the group law. -/
theorem admitPoint_ok (q result : AffinePoint) (sign : Bool)
    (h : admitPoint q sign = .ok result) :
    result = q ∧ coordinateChecks result sign = true ∧ subgroupCheck result = true := by
  by_cases hc : coordinateChecks q sign = true
  · by_cases hs : subgroupCheck q = true
    · simp only [admitPoint, if_pos hc, if_pos hs, Except.ok.injEq] at h
      subst result
      exact ⟨rfl, hc, hs⟩
    · simp [admitPoint, hc, hs] at h
  · simp [admitPoint, hc] at h

/-- Kind: refinement. Says: the checked coordinate predicate entails the
canonical field bounds, curve equation and requested sign.
Does not say: the recovered square root always exists. -/
theorem coordinateChecks_sound (q : AffinePoint) (sign : Bool)
    (h : coordinateChecks q sign = true) :
    ((q.x < modulus ∧ q.y < modulus) ∧
      sq q.y = addF (mulF (sq q.x) q.x) 4) ∧ largeY q.y = sign := by
  simpa [coordinateChecks, Bool.and_eq_true] using h

/-- Kind: linkage. Says: successful byte decoding went through candidate
recovery and the concrete coordinate and subgroup checks.
Does not say: signature verification or mathematical subgroup completeness. -/
theorem decodePublicKey_ok (bytes : ByteArray) (result : AffinePoint)
    (h : decodePublicKey bytes = .ok result) :
    ∃ sign : Bool, candidate bytes = .ok (result, sign) ∧
      coordinateChecks result sign = true ∧ subgroupCheck result = true := by
  cases hc : candidate bytes with
  | error e => simp [decodePublicKey, hc] at h
  | ok pair =>
    obtain ⟨q, sign⟩ := pair
    simp only [decodePublicKey, hc] at h
    obtain ⟨he, hv, hs⟩ := admitPoint_ok q result sign h
    subst result
    exact ⟨sign, hc, hv, hs⟩

#print axioms EthereumConsensus.BLS.decodePublicKey_wrong_width
#print axioms EthereumConsensus.BLS.admitPoint_ok
#print axioms EthereumConsensus.BLS.coordinateChecks_sound
#print axioms EthereumConsensus.BLS.decodePublicKey_ok

end EthereumConsensus.BLS

-- Test transport only; the native verdict and coordinates are emitted by Lean.
open EthereumConsensus.BLS

private def nibble (b : UInt8) : Except String UInt8 :=
  if 48 ≤ b && b ≤ 57 then .ok (b - 48)
  else if 97 ≤ b && b ≤ 102 then .ok (b - 97 + 10)
  else .error "invalid_hex"

private def readHex (s : String) : Except String ByteArray := do
  let bytes := s.toUTF8
  if bytes.size % 2 != 0 || bytes.size > 128 then throw "invalid_hex"
  let mut out := ByteArray.empty
  for i in [:bytes.size / 2] do
    let hi ← nibble bytes[2*i]!
    let lo ← nibble bytes[2*i+1]!
    out := out.push (16 * hi + lo)
  return out

private def errorName : KeyError → String
  | .width => "width"
  | .notCompressed => "not_compressed"
  | .infinityKey => "infinity_key"
  | .nonCanonicalX => "non_canonical_x"
  | .notOnCurve => "not_on_curve"
  | .notSubgroup => "not_subgroup"

private def dispatch (s : String) : Except String String := do
  let bytes ← readHex s
  let p ← (decodePublicKey bytes).mapError errorName
  return "ok " ++ toString p.x ++ " " ++ toString p.y

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 256 then .error "resource_limit"
      else dispatch line.trimAscii.toString
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
