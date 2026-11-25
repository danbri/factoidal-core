import Init

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
    exact ⟨sign, rfl, hv, hs⟩

/-- Kind: refinement. Says: candidate decoding errors propagate unchanged.
Does not say: candidate recovery is mathematically complete. -/
theorem decodePublicKey_candidate_error (bytes : ByteArray) (e : KeyError)
    (h : candidate bytes = .error e) :
    decodePublicKey bytes = .error e := by
  simp only [decodePublicKey, h]

/-- Kind: refinement. Says: the recovered point is returned when both checks pass.
Does not say: the checks establish the mathematical group law. -/
theorem decodePublicKey_candidate_ok (bytes : ByteArray) (q : AffinePoint) (sign : Bool)
    (h : candidate bytes = .ok (q, sign))
    (hc : coordinateChecks q sign = true) (hs : subgroupCheck q = true) :
    decodePublicKey bytes = .ok q := by
  simp only [decodePublicKey, h, admitPoint, if_pos hc, if_pos hs]

/-- Kind: rejection. Says: a recovered point failing coordinate checks is refused.
Does not say: the candidate recovery algorithm finds every valid point. -/
theorem decodePublicKey_candidate_bad_coordinates (bytes : ByteArray) (q : AffinePoint)
    (sign : Bool) (h : candidate bytes = .ok (q, sign))
    (hc : coordinateChecks q sign ≠ true) :
    decodePublicKey bytes = .error .notOnCurve := by
  simp only [decodePublicKey, h, admitPoint, if_neg hc]

/-- Kind: rejection. Says: a coordinate-checked candidate failing subgroup check
is refused. Does not say: the subgroup algorithm refines scalar multiplication. -/
theorem decodePublicKey_candidate_bad_subgroup (bytes : ByteArray) (q : AffinePoint)
    (sign : Bool) (h : candidate bytes = .ok (q, sign))
    (hc : coordinateChecks q sign = true) (hs : subgroupCheck q ≠ true) :
    decodePublicKey bytes = .error .notSubgroup := by
  simp only [decodePublicKey, h, admitPoint, if_pos hc, if_neg hs]

#print axioms EthereumConsensus.BLS.decodePublicKey_wrong_width
#print axioms EthereumConsensus.BLS.admitPoint_ok
#print axioms EthereumConsensus.BLS.coordinateChecks_sound
#print axioms EthereumConsensus.BLS.decodePublicKey_ok
#print axioms EthereumConsensus.BLS.decodePublicKey_candidate_error
#print axioms EthereumConsensus.BLS.decodePublicKey_candidate_ok
#print axioms EthereumConsensus.BLS.decodePublicKey_candidate_bad_coordinates
#print axioms EthereumConsensus.BLS.decodePublicKey_candidate_bad_subgroup

inductive AggregateError where
  | resourceLimit
  | emptyKeys
  | invalidKey (reason : KeyError)
  | infinitySum
  | invalidSum
  deriving Repr, DecidableEq

def maxAggregateKeys : Nat := 2048

-- The caller has checked the key count. One tail call per key.
private def aggregateLoop : List ByteArray → Projective → Except AggregateError Projective
  | [], acc => .ok acc
  | bytes :: rest, acc =>
    match decodePublicKey bytes with
    | .error e => .error (.invalidKey e)
    | .ok q => aggregateLoop rest (addMixed acc q)

private def normalise (p : Projective) : AffinePoint :=
  let zi := powLoop 381 p.z (modulus - 2) 1
  let zi2 := sq zi
  ⟨mulF p.x zi2, mulF p.y (mulF zi2 zi)⟩

private def finishAggregate (p : Projective) : Except AggregateError AffinePoint :=
  if p.z = 0 then .error .infinitySum
  else
    let q := normalise p
    if coordinateChecks q (largeY q.y) then
      if subgroupCheck q then .ok q else .error .invalidSum
    else .error .invalidSum

/-- Sum every validated compressed key, including repeated keys. This is the
public-key phase of FastAggregateVerify, not signature authentication. -/
def aggregatePublicKeys (keys : List ByteArray) : Except AggregateError AffinePoint :=
  if keys.length > maxAggregateKeys then .error .resourceLimit
  else if keys.isEmpty then .error .emptyKeys
  else
    match aggregateLoop keys infinity with
    | .error e => .error e
    | .ok p => finishAggregate p

/-- Kind: resource bound. Says: oversize lists refuse before point arithmetic.
Does not say: the transport allocates no memory before calling this function. -/
theorem aggregatePublicKeys_over_limit (keys : List ByteArray)
    (h : keys.length > maxAggregateKeys) :
    aggregatePublicKeys keys = .error .resourceLimit := by
  simp only [aggregatePublicKeys, if_pos h]

/-- Kind: admission. Says: zero keys are not an aggregate verification input.
Does not say: the consensus-specific empty committee exception is implemented. -/
theorem aggregatePublicKeys_empty :
    aggregatePublicKeys [] = .error .emptyKeys := by
  rfl

/-- Kind: linkage. Says: a singleton fold uses the actual decoded point.
Does not say: normalisation refines projective arithmetic. -/
theorem aggregateLoop_singleton (bytes : ByteArray) (q : AffinePoint) (p : Projective)
    (h : decodePublicKey bytes = .ok q) :
    aggregateLoop [bytes] p = .ok (addMixed p q) := by
  simp only [aggregateLoop, h]

/-- Kind: rejection. Says: the first invalid key is not ignored by the fold.
Does not say: every mathematical invalidity is detected by the decoder. -/
theorem aggregateLoop_bad_first (bytes : ByteArray) (rest : List ByteArray)
    (p : Projective) (e : KeyError) (h : decodePublicKey bytes = .error e) :
    aggregateLoop (bytes :: rest) p = .error (.invalidKey e) := by
  simp only [aggregateLoop, h]

/-- Kind: rejection. Says: a zero projective Z cannot produce a public key.
Does not say: the group law is proved. -/
theorem finishAggregate_infinity (p : Projective) (h : p.z = 0) :
    finishAggregate p = .error .infinitySum := by
  simp only [finishAggregate, if_pos h]

/-- Kind: linkage. Says: a returned aggregate passes both actual point checks.
Does not say: the arithmetic refines the mathematical sum. -/
theorem finishAggregate_ok (p : Projective) (result : AffinePoint)
    (h : finishAggregate p = .ok result) :
    coordinateChecks result (largeY result.y) = true ∧ subgroupCheck result = true := by
  by_cases hz : p.z = 0
  · simp [finishAggregate, hz] at h
  · by_cases hc : coordinateChecks (normalise p) (largeY (normalise p).y) = true
    · by_cases hs : subgroupCheck (normalise p) = true
      · simp only [finishAggregate, if_neg hz, if_pos hc, if_pos hs, Except.ok.injEq] at h
        subst result
        exact ⟨hc, hs⟩
      · simp only [finishAggregate, if_neg hz, if_pos hc, if_neg hs] at h
        cases h
    · simp only [finishAggregate, if_neg hz, if_neg hc] at h
      cases h

/-- Kind: linkage. Says: the public aggregate entry point returns only checked
points. Does not say: the BLS signature is verified. -/
theorem aggregatePublicKeys_ok (keys : List ByteArray) (result : AffinePoint)
    (h : aggregatePublicKeys keys = .ok result) :
    coordinateChecks result (largeY result.y) = true ∧ subgroupCheck result = true := by
  by_cases hl : keys.length > maxAggregateKeys
  · simp [aggregatePublicKeys, hl] at h
  · by_cases he : keys.isEmpty = true
    · simp [aggregatePublicKeys, hl, he] at h
    · cases hf : aggregateLoop keys infinity with
      | error e => simp [aggregatePublicKeys, hl, he, hf] at h
      | ok p =>
        simp only [aggregatePublicKeys, if_neg hl, if_neg he, hf] at h
        exact finishAggregate_ok p result h

#print axioms EthereumConsensus.BLS.aggregatePublicKeys_over_limit
#print axioms EthereumConsensus.BLS.aggregatePublicKeys_empty
#print axioms EthereumConsensus.BLS.aggregateLoop_singleton
#print axioms EthereumConsensus.BLS.aggregateLoop_bad_first
#print axioms EthereumConsensus.BLS.finishAggregate_infinity
#print axioms EthereumConsensus.BLS.finishAggregate_ok
#print axioms EthereumConsensus.BLS.aggregatePublicKeys_ok

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

private def aggregateErrorName : AggregateError → String
  | .resourceLimit => "resource_limit"
  | .emptyKeys => "empty_keys"
  | .invalidKey e => errorName e
  | .infinitySum => "infinity_sum"
  | .invalidSum => "invalid_sum"

private def dispatchAggregate (parts : List String) : Except String String := do
  if parts.length > maxAggregateKeys then throw "resource_limit"
  let mut keys : List ByteArray := []
  for part in parts do
    keys := (← readHex part) :: keys
  let p ← (aggregatePublicKeys keys.reverse).mapError aggregateErrorName
  return "ok " ++ toString p.x ++ " " ++ toString p.y

private def dispatchLine (line : String) : Except String String :=
  if line.utf8ByteSize > 200000 then .error "resource_limit"
  else
    let s := line.trimAscii.toString
    match s.splitOn " " with
    | "agg" :: parts => dispatchAggregate parts
    | _ => if line.utf8ByteSize > 256 then .error "resource_limit" else dispatch s

def EthereumConsensus.BLS.G1PublicKeyCLI.run : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := dispatchLine line
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
