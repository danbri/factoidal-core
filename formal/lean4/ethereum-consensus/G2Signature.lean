import Lean

/-! Experimental compressed G2 signature admission, not a signature verdict.
Field and twist: RFC 9380 section 8.8.2. Serialization is the Ethereum
96-byte compressed format, imaginary coefficient first. No secret inputs. -/
namespace EthereumConsensus.BLS.G2

def modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
def order : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

private def aadd (a b : Nat) : Nat := (a+b) % modulus
private def asub (a b : Nat) : Nat := (a+modulus-b%modulus) % modulus
private def amul (a b : Nat) : Nat := a*b % modulus

private def powLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n+1, b, e, acc =>
    powLoop n (amul b b) (e/2) (if e%2=1 then amul acc b else acc)

private def sqrtF (a : Nat) : Nat := powLoop 381 a ((modulus+1)/4) 1
private def invF (a : Nat) : Nat := powLoop 381 a (modulus-2) 1

structure Fp2 where
  re : Nat
  im : Nat
  deriving Repr, DecidableEq

private def zero : Fp2 := ⟨0,0⟩
private def one : Fp2 := ⟨1,0⟩
private def plus (a b : Fp2) : Fp2 := ⟨aadd a.re b.re, aadd a.im b.im⟩
private def minus (a b : Fp2) : Fp2 := ⟨asub a.re b.re, asub a.im b.im⟩
private def times (a b : Fp2) : Fp2 :=
  ⟨asub (amul a.re b.re) (amul a.im b.im),
    aadd (amul a.re b.im) (amul a.im b.re)⟩
private def square (a : Fp2) : Fp2 := times a a
private def scale (n : Nat) (a : Fp2) : Fp2 := ⟨amul n a.re, amul n a.im⟩
private def neg (a : Fp2) : Fp2 := minus zero a
def canonical (a : Fp2) : Bool := decide (a.re < modulus) && decide (a.im < modulus)

-- Recover a candidate via the norm to Fp. If b is nonzero, the real
-- coefficient of a root cannot be zero. Final square equality is mandatory.
private def sqrt2 (a : Fp2) : Fp2 :=
  if a.im = 0 then
    let x := sqrtF a.re
    if amul x x = a.re then ⟨x,0⟩ else ⟨0,sqrtF (asub 0 a.re)⟩
  else
    let norm := aadd (amul a.re a.re) (amul a.im a.im)
    let s := sqrtF norm
    let half := (modulus+1)/2
    let t := amul (aadd a.re s) half
    let v := sqrtF t
    let x := if v != 0 && amul v v == t then v
             else sqrtF (amul (asub a.re s) half)
    ⟨x, amul a.im (invF (amul 2 x))⟩

structure Point where
  x : Fp2
  y : Fp2
  deriving Repr, DecidableEq

private structure Projective where
  x : Fp2
  y : Fp2
  z : Fp2

private def infinity : Projective := ⟨zero,one,zero⟩
private def rhs (x : Fp2) : Fp2 := plus (times (square x) x) ⟨4,4⟩

-- Jacobian tangent and chord with cleared denominators.
private def double (p : Projective) : Projective :=
  if p.z = zero ∨ p.y = zero then infinity
  else
    let b := square p.y
    let d := scale 4 (times p.x b)
    let e := scale 3 (square p.x)
    let x := minus (square e) (scale 2 d)
    let y := minus (times e (minus d x)) (scale 8 (square b))
    ⟨x,y,scale 2 (times p.y p.z)⟩

private def addMixed (p : Projective) (q : Point) : Projective :=
  if p.z = zero then ⟨q.x,q.y,one⟩
  else
    let zz := square p.z
    let h := minus (times q.x zz) p.x
    let r := minus (times q.y (times zz p.z)) p.y
    if h = zero then
      if r = zero then double p else infinity
    else
      let hh := square h
      let hhh := times h hh
      let v := times p.x hh
      let x := minus (minus (square r) hhh) (scale 2 v)
      let y := minus (times r (minus v x)) (times p.y hhh)
      ⟨x,y,times p.z h⟩

private def orderLoop (q : Point) : Nat → Projective → Projective
  | 0, acc => acc
  | n+1, acc =>
    let d := double acc
    orderLoop q n (if (order / 2^n)%2 = 1 then addMixed d q else d)

def subgroupCheck (q : Point) : Bool := decide ((orderLoop q 255 infinity).z = zero)
def largeY (y : Fp2) : Bool :=
  decide ((if y.im = 0 then y.re else y.im) > (modulus-1)/2)

def coordinateChecks (q : Point) (sign : Bool) : Bool :=
  canonical q.x && canonical q.y && decide (square q.y = rhs q.x) &&
    (largeY q.y == sign)

inductive SignatureError where
  | width
  | notCompressed
  | infinitySignature
  | nonCanonicalX
  | notOnCurve
  | notSubgroup
  deriving Repr, DecidableEq

private def checkPoint (q : Point) (sign : Bool) : Except SignatureError Point :=
  if coordinateChecks q sign then
    if subgroupCheck q then .ok q else .error .notSubgroup
  else .error .notOnCurve

private def recover (x : Fp2) (sign : Bool) : Except SignatureError (Point × Bool) :=
  if canonical x then
    let root := sqrt2 (rhs x)
    let y := if largeY root == sign then root else neg root
    .ok (⟨x,y⟩,sign)
  else .error .nonCanonicalX

private def candidate (bytes : ByteArray) : Except SignatureError (Point × Bool) :=
  if bytes.size ≠ 96 then .error .width
  else
    let encoded := bytes.data.foldl (fun a b => a*256+b.toNat) 0
    let hi := encoded / 2^384
    let flags := hi / 2^381
    if flags < 4 then .error .notCompressed
    else if flags ≥ 6 then .error .infinitySignature
    else recover ⟨encoded % 2^384, hi % 2^381⟩ (flags == 5)

def decodeSignature (bytes : ByteArray) : Except SignatureError Point :=
  match candidate bytes with
  | .error e => .error e
  | .ok (q,sign) => checkPoint q sign

/-- Kind: admission. Says: wrong byte width refuses before arithmetic.
Does not say: the host line reader is bounded before allocation. -/
theorem decodeSignature_wrong_width (b : ByteArray) (h : b.size ≠ 96) :
    decodeSignature b = .error .width := by
  simp only [decodeSignature,candidate,if_pos h]

/-- Kind: linkage. Says: wire rejection is propagated unchanged.
Does not say: serialization completeness. -/
theorem decodeSignature_candidate_error (b : ByteArray) (e : SignatureError)
    (h : candidate b = .error e) : decodeSignature b = .error e := by
  simp only [decodeSignature,h]

/-- Kind: linkage. Says: a successful point passes the actual checks.
Does not say: the projective arithmetic refines a mathematical group. -/
theorem checkPoint_ok (q result : Point) (sign : Bool)
    (h : checkPoint q sign = .ok result) :
    result = q ∧ coordinateChecks q sign = true ∧ subgroupCheck q = true := by
  by_cases hc : coordinateChecks q sign = true
  · by_cases hs : subgroupCheck q = true
    · simp only [checkPoint,if_pos hc,if_pos hs,Except.ok.injEq] at h
      exact ⟨h.symm,hc,hs⟩
    · simp only [checkPoint,if_pos hc,if_neg hs] at h
      cases h
  · simp only [checkPoint,if_neg hc] at h
    cases h

/-- Kind: rejection. Says: failing the subgroup predicate is never accepted.
Does not say: completeness of the subgroup algorithm. -/
theorem checkPoint_bad_subgroup (q : Point) (sign : Bool)
    (hc : coordinateChecks q sign = true) (hs : subgroupCheck q ≠ true) :
    checkPoint q sign = .error .notSubgroup := by
  simp only [checkPoint,if_pos hc,if_neg hs]

/-- Kind: rejection. Says: failing the coordinate predicate refuses.
Does not say: completeness of square-root recovery. -/
theorem checkPoint_bad_coordinates (q : Point) (sign : Bool)
    (hc : coordinateChecks q sign ≠ true) :
    checkPoint q sign = .error .notOnCurve := by
  simp only [checkPoint,if_neg hc]

/-- Kind: linkage. Says: every public success has a checked point and sign.
Does not say: a signature authenticates a message. -/
theorem decodeSignature_ok (b : ByteArray) (q : Point)
    (h : decodeSignature b = .ok q) :
    ∃ sign : Bool, coordinateChecks q sign = true ∧ subgroupCheck q = true := by
  cases he : candidate b with
  | error e => simp [decodeSignature,he] at h
  | ok v =>
    rcases v with ⟨p,s⟩
    simp only [decodeSignature,he] at h
    obtain ⟨eq,hc,hs⟩ := checkPoint_ok p q s h
    subst q
    exact ⟨s,hc,hs⟩

#print axioms EthereumConsensus.BLS.G2.decodeSignature_wrong_width
#print axioms EthereumConsensus.BLS.G2.decodeSignature_candidate_error
#print axioms EthereumConsensus.BLS.G2.checkPoint_ok
#print axioms EthereumConsensus.BLS.G2.checkPoint_bad_subgroup
#print axioms EthereumConsensus.BLS.G2.checkPoint_bad_coordinates
#print axioms EthereumConsensus.BLS.G2.decodeSignature_ok
end EthereumConsensus.BLS.G2

open EthereumConsensus.BLS.G2
private def nibble (b : UInt8) : Except String UInt8 :=
  if 48 ≤ b && b ≤ 57 then .ok (b-48)
  else if 97 ≤ b && b ≤ 102 then .ok (b-97+10)
  else .error "invalid_hex"

private def readHex (s : String) : Except String ByteArray := do
  let bytes := s.toUTF8
  if bytes.size % 2 != 0 || bytes.size > 256 then throw "invalid_hex"
  let mut out := ByteArray.empty
  for i in [:bytes.size / 2] do
    let hi ← nibble bytes[2*i]!
    let lo ← nibble bytes[2*i+1]!
    out := out.push (16*hi+lo)
  return out

private def errorName : SignatureError → String
  | .width => "width"
  | .notCompressed => "not_compressed"
  | .infinitySignature => "infinity_signature"
  | .nonCanonicalX => "non_canonical_x"
  | .notOnCurve => "not_on_curve"
  | .notSubgroup => "not_subgroup"

private def dispatch (s : String) : Except String String := do
  let bytes ← readHex s
  let p ← (decodeSignature bytes).mapError errorName
  return "ok " ++ toString p.x.re ++ " " ++ toString p.x.im ++ " " ++
    toString p.y.re ++ " " ++ toString p.y.im

def EthereumConsensus.BLS.G2SignatureCLI.run : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 512 then .error "resource_limit"
                  else dispatch line.trimAscii.toString
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
