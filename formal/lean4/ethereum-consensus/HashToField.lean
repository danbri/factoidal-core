import Init
import L4Factoidal.Crypto.SHA2

/-! Experimental public-message hash-to-field for BLS12-381 G2.
RFC 9380 sections 5.2, 5.3.1, 8.8.2. No secret inputs, signing or
signature verdict. The fixed Ethereum entry accepts a 32-byte signing root. -/
namespace EthereumConsensus.BLS.HashField

open L4Factoidal.Crypto (sha256)

def modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def maxMessage : Nat := 4096
def popDST : ByteArray := "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8

inductive HashError where
  | resourceLimit
  | dstWidth
  | signingRootWidth
  | internalInvariant
  deriving Repr, DecidableEq

private def singleton (n : Nat) : ByteArray := ByteArray.empty.push (UInt8.ofNat n)

private def xorDigest (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [:32] do
    out := out.push (a[i]! ^^^ b[i]!)
  return out

/-- Eight SHA-256 blocks for count=2, m=2, L=64.
Called only after message/DST admission. -/
private def expand256 (msg dst : ByteArray) : ByteArray := Id.run do
  let dstPrime := dst ++ singleton dst.size
  let zPad : ByteArray := ⟨Array.replicate 64 0⟩
  let b0 := sha256 (zPad ++ msg ++ singleton 1 ++ singleton 0 ++ singleton 0 ++ dstPrime)
  let mut previous := sha256 (b0 ++ singleton 1 ++ dstPrime)
  let mut out := previous
  for i in [:7] do
    previous := sha256 (xorDigest b0 previous ++ singleton (i+2) ++ dstPrime)
    out := out ++ previous
  return out

private def reduceChunk (data : ByteArray) (offset : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [:64] do
    n := n*256 + data[offset+i]!.toNat
  return n % modulus

def canonical (a : Array Nat) : Bool :=
  (a.size == 4) && a.all (fun v => decide (v < modulus))

private def coefficients (data : ByteArray) : Array Nat :=
  #[reduceChunk data 0, reduceChunk data 64, reduceChunk data 128, reduceChunk data 192]

private def checkedCoefficients (data : ByteArray) : Except HashError (Array Nat) :=
  if data.size ≠ 256 then .error .internalInvariant
  else
    let result := coefficients data
    if canonical result then .ok result else .error .internalInvariant

/-- Generic short-DST test entry. The development bounds are not RFC invalidity.
The output is (u[0].re, u[0].im, u[1].re, u[1].im). -/
def hashToField (msg dst : ByteArray) : Except HashError (Array Nat) :=
  if msg.size > maxMessage then .error .resourceLimit
  else if dst.size = 0 ∨ dst.size > 255 then .error .dstWidth
  else checkedCoefficients (expand256 msg dst)

/-- Ethereum POP suite entry for public consensus signing roots. -/
def consensusHashToField (root : ByteArray) : Except HashError (Array Nat) :=
  if root.size ≠ 32 then .error .signingRootWidth
  else hashToField root popDST

/-- Kind: resource admission. Says: oversized messages refuse before expansion.
Does not say: host transport allocates only bounded memory. -/
theorem hashToField_over_limit (msg dst : ByteArray) (h : msg.size > maxMessage) :
    hashToField msg dst = .error .resourceLimit := by
  simp only [hashToField,if_pos h]

/-- Kind: admission. Says: the short-DST entry refuses empty or oversized DST.
Does not say: RFC long-DST preprocessing is implemented. -/
theorem hashToField_bad_dst (msg dst : ByteArray) (hm : ¬ msg.size > maxMessage)
    (hd : dst.size = 0 ∨ dst.size > 255) :
    hashToField msg dst = .error .dstWidth := by
  simp only [hashToField,if_neg hm,if_pos hd]

/-- Kind: linkage. Says: an admitted request uses the actual SHA expansion.
Does not say: that expansion refines the full RFC mathematical definition. -/
theorem hashToField_delegates (msg dst : ByteArray) (hm : ¬ msg.size > maxMessage)
    (hd : ¬ (dst.size = 0 ∨ dst.size > 255)) :
    hashToField msg dst = checkedCoefficients (expand256 msg dst) := by
  simp only [hashToField,if_neg hm,if_neg hd]

/-- Kind: output invariant. Says: success returns exactly the computed canonical coefficients.
Does not say: cryptographic security or completeness of expansion. -/
theorem checkedCoefficients_ok (data : ByteArray) (out : Array Nat)
    (h : checkedCoefficients data = .ok out) :
    out = coefficients data ∧ canonical out = true := by
  by_cases hw : data.size ≠ 256
  · simp only [checkedCoefficients,if_pos hw] at h
    cases h
  · by_cases hc : canonical (coefficients data) = true
    · simp only [checkedCoefficients,if_neg hw,if_pos hc,Except.ok.injEq] at h
      subst out
      exact ⟨rfl,hc⟩
    · simp only [checkedCoefficients,if_neg hw,if_neg hc] at h
      cases h

/-- Kind: linkage. Says: public hash-to-field success has canonical coefficients.
Does not say: the map to an elliptic curve or signature verification is implemented. -/
theorem hashToField_ok (msg dst : ByteArray) (out : Array Nat)
    (h : hashToField msg dst = .ok out) : canonical out = true := by
  by_cases hm : msg.size > maxMessage
  · simp only [hashToField,if_pos hm] at h
    cases h
  · by_cases hd : dst.size = 0 ∨ dst.size > 255
    · simp only [hashToField,if_neg hm,if_pos hd] at h
      cases h
    · rw [hashToField_delegates msg dst hm hd] at h
      exact (checkedCoefficients_ok (expand256 msg dst) out h).2

/-- Kind: admission. Says: the consensus entry refuses non-32-byte roots.
Does not say: the supplied root is authenticated. -/
theorem consensusHashToField_wrong_width (root : ByteArray) (h : root.size ≠ 32) :
    consensusHashToField root = .error .signingRootWidth := by
  simp only [consensusHashToField,if_pos h]

/-- Kind: linkage. Says: admitted consensus roots use the fixed POP domain.
Does not say: the domain proves possession or authenticates a signature. -/
theorem consensusHashToField_delegates (root : ByteArray) (h : root.size = 32) :
    consensusHashToField root = hashToField root popDST := by
  have hn : ¬ root.size ≠ 32 := fun hne => hne h
  simp only [consensusHashToField,if_neg hn]

#print axioms EthereumConsensus.BLS.HashField.hashToField_over_limit
#print axioms EthereumConsensus.BLS.HashField.hashToField_bad_dst
#print axioms EthereumConsensus.BLS.HashField.hashToField_delegates
#print axioms EthereumConsensus.BLS.HashField.checkedCoefficients_ok
#print axioms EthereumConsensus.BLS.HashField.hashToField_ok
#print axioms EthereumConsensus.BLS.HashField.consensusHashToField_wrong_width
#print axioms EthereumConsensus.BLS.HashField.consensusHashToField_delegates

end EthereumConsensus.BLS.HashField

/-! Public verification experiment: RFC 9380 sections 6.6.2, 6.6.3, 8.8.2
and Appendix E.3. Field primitives reused from repository G2Signature.lean
(blob 9a135cce63739f5e62017e98bd76a888b0d89306); the parity sign here is NOT the compressed signature sign. -/
namespace EthereumConsensus.BLS.G2Map

def modulus : Nat := HashField.modulus

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

private def inverse (a : Fp2) : Fp2 :=
  let d := invF (aadd (amul a.re a.re) (amul a.im a.im))
  ⟨amul a.re d, asub 0 (amul a.im d)⟩

private def divide (a b : Fp2) : Fp2 := times a (inverse b)
def sign0 (a : Fp2) : Bool :=
  if a.re = 0 then a.im % 2 == 1 else a.re % 2 == 1

private def curveA : Fp2 := ⟨0,240⟩
private def curveB : Fp2 := ⟨1012,1012⟩
private def zConst : Fp2 := ⟨modulus-2,modulus-1⟩
private def rhsPrime (x : Fp2) : Fp2 :=
  plus (plus (times (square x) x) (times curveA x)) curveB

private def swu (u : Fp2) : Point :=
  let t := times zConst (square u)
  let v := inverse (plus (square t) t)
  let x1 := if v = zero then divide curveB (times zConst curveA)
            else times (divide (neg curveB) curveA) (plus one v)
  let g1 := rhsPrime x1
  let y1 := sqrt2 g1
  let x := if square y1 = g1 then x1 else times t x1
  let y := if square y1 = g1 then y1 else sqrt2 (rhsPrime x)
  ⟨x, if sign0 u == sign0 y then y else neg y⟩

-- Coefficients are in descending degree order for Horner evaluation.
private def poly (x : Fp2) (cs : List Fp2) : Fp2 :=
  cs.foldl (fun a c => plus (times a x) c) zero

private def xn : List Fp2 := [
  ⟨0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1,0⟩,
  ⟨0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e,0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d⟩,
  ⟨0,0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a⟩,
  ⟨0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6,0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6⟩]
private def xd : List Fp2 := [one,⟨12,modulus-12⟩,⟨0,modulus-72⟩]
private def yn : List Fp2 := [
  ⟨0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10,0⟩,
  ⟨0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c,0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f⟩,
  ⟨0,0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be⟩,
  ⟨0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706,0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706⟩]
private def yd : List Fp2 := [one,⟨18,modulus-18⟩,⟨0,modulus-216⟩,⟨modulus-432,modulus-432⟩]

private def iso (q : Point) : Option Point :=
  let dx := poly q.x xd
  let dy := poly q.x yd
  if dx = zero ∨ dy = zero then none
  else some ⟨divide (poly q.x xn) dx, times q.y (divide (poly q.x yn) dy)⟩

def onTarget (q : Point) : Bool :=
  canonical q.x && canonical q.y &&
    decide (square q.y = plus (times (square q.x) q.x) ⟨4,4⟩)

inductive MapError where
  | noncanonical
  | internalInvariant
  | hashError (e : HashField.HashError)
  deriving Repr, DecidableEq

private def checkedTarget (q : Option Point) : Except MapError (Option Point) :=
  match q with
  | none => .ok none
  | some p => if onTarget p then .ok (some p) else .error .internalInvariant

private def primeCheck (u : Fp2) (q : Point) : Bool :=
  decide (square q.y = rhsPrime q.x) && (sign0 q.y == sign0 u)

private def mapped (u : Fp2) : Except MapError (Option Point) :=
  let q := swu u
  if primeCheck u q then checkedTarget (iso q)
  else .error .internalInvariant

def mapField (u : Fp2) : Except MapError (Option Point) :=
  if canonical u then mapped u else .error .noncanonical

private def mapCoefficients (a : Array Nat) : Except MapError (Option Point × Option Point) := do
  if a.size ≠ 4 then throw .internalInvariant
  let q0 ← mapField ⟨a[0]!,a[1]!⟩
  let q1 ← mapField ⟨a[2]!,a[3]!⟩
  return (q0,q1)

def mapSigningRoot (root : ByteArray) : Except MapError (Option Point × Option Point) :=
  match HashField.consensusHashToField root with
  | .error e => .error (.hashError e)
  | .ok a => mapCoefficients a

/-- Kind: admission.
Says: noncanonical fields refuse before SSWU.
Does not say: all admitted field values map successfully. -/
theorem mapField_noncanonical (u : Fp2) (h : canonical u ≠ true) :
    mapField u = .error .noncanonical := by
  simp only [mapField,if_neg h]

/-- Kind: linkage.
Says: canonical fields use the concrete map.
Does not say: mathematical refinement of SSWU. -/
theorem mapField_delegates (u : Fp2) (h : canonical u = true) :
    mapField u = mapped u := by
  simp only [mapField,if_pos h]

/-- Kind: checked output.
Says: the target checker returns a finite point unchanged only on its checked curve.
Does not say: the isogeny is a group homomorphism. -/
theorem checkedTarget_ok (q out : Point) (h : checkedTarget (some q) = .ok (some out)) :
    q = out ∧ onTarget out = true := by
  by_cases hc : onTarget q = true
  · simp only [checkedTarget,if_pos hc,Except.ok.injEq,Option.some.injEq] at h
    subst out
    exact ⟨rfl,hc⟩
  · simp only [checkedTarget,if_neg hc] at h
    cases h

private theorem checkedTarget_finite (q : Option Point) (out : Point)
    (h : checkedTarget q = .ok (some out)) : onTarget out = true := by
  cases q with
  | none =>
    simp only [checkedTarget,Except.ok.injEq] at h
    cases h
  | some p => exact (checkedTarget_ok p out h).2

/-- Kind: public output invariant.
Says: a successful finite map output passes the actual target-curve check.
Does not say: completeness or normative isogeny refinement. -/
theorem mapField_ok (u : Fp2) (out : Point)
    (h : mapField u = .ok (some out)) : onTarget out = true := by
  by_cases hc : canonical u = true
  · rw [mapField_delegates u hc] at h
    by_cases hp : primeCheck u (swu u) = true
    · simp only [mapped,if_pos hp] at h
      exact checkedTarget_finite (iso (swu u)) out h
    · simp only [mapped,if_neg hp] at h
      cases h
  · simp only [mapField,if_neg hc] at h
    cases h

/-- Kind: exceptional output.
Says: the target checker preserves infinity.
Does not say: the isogeny's exceptional inputs are complete. -/
theorem checkedTarget_infinity : checkedTarget none = .ok none := rfl

/-- Kind: linkage.
Says: hash failure is carried into the actual root map.
Does not say: a supplied signing root is authenticated. -/
theorem mapSigningRoot_hash_error (root : ByteArray) (e : HashField.HashError)
    (h : HashField.consensusHashToField root = .error e) :
    mapSigningRoot root = .error (.hashError e) := by
  simp only [mapSigningRoot,h]

/-- Kind: linkage.
Says: hash success feeds the two field maps.
Does not say: the result is a subgroup point or a signature verdict. -/
theorem mapSigningRoot_delegates (root : ByteArray) (a : Array Nat)
    (h : HashField.consensusHashToField root = .ok a) :
    mapSigningRoot root = mapCoefficients a := by
  simp only [mapSigningRoot,h]

#print axioms EthereumConsensus.BLS.G2Map.mapField_noncanonical
#print axioms EthereumConsensus.BLS.G2Map.mapField_delegates
#print axioms EthereumConsensus.BLS.G2Map.checkedTarget_ok
#print axioms EthereumConsensus.BLS.G2Map.mapField_ok
#print axioms EthereumConsensus.BLS.G2Map.checkedTarget_infinity
#print axioms EthereumConsensus.BLS.G2Map.mapSigningRoot_hash_error
#print axioms EthereumConsensus.BLS.G2Map.mapSigningRoot_delegates


-- Reuse the repository-owned G2Signature Jacobian tangent and mixed chord.
private structure Projective where
  x : Fp2
  y : Fp2
  z : Fp2

private def infinity : Projective := ⟨zero,one,zero⟩

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


private def groupOrder : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def effectiveCofactor : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551

private def scalarLoop (k : Nat) (q : Point) : Nat → Projective → Projective
  | 0, acc => acc
  | n+1, acc =>
    let d := double acc
    scalarLoop k q n (if (k / 2^n)%2 = 1 then addMixed d q else d)

private def normalise (p : Projective) : Option Point :=
  if p.z = zero then none
  else
    let iz := inverse p.z
    let iz2 := square iz
    some ⟨times p.x iz2, times p.y (times iz2 iz)⟩

private def liftPoint : Option Point → Projective
  | none => infinity
  | some q => ⟨q.x,q.y,one⟩

private def addPoints (a b : Option Point) : Option Point :=
  match b with
  | none => a
  | some q => normalise (addMixed (liftPoint a) q)

def subgroupCheck (q : Point) : Bool :=
  decide ((scalarLoop groupOrder q 255 infinity).z = zero)

private def clearCheck (q : Option Point) : Except MapError (Option Point) :=
  match q with
  | none => .ok none
  | some p =>
    if onTarget p && subgroupCheck p then .ok (some p)
    else .error .internalInvariant

private def pointAdmitted : Option Point → Bool
  | none => true
  | some p => onTarget p

private def clearSum (a b : Option Point) : Option Point :=
  match addPoints a b with
  | none => none
  | some q => normalise (scalarLoop effectiveCofactor q 636 infinity)

def clearMapped (a b : Option Point) : Except MapError (Option Point) :=
  if pointAdmitted a && pointAdmitted b then clearCheck (clearSum a b)
  else .error .internalInvariant

private def complete (m : Except MapError (Option Point × Option Point)) :
    Except MapError (Option Point) :=
  match m with
  | .error e => .error e
  | .ok (a,b) => clearMapped a b

def hashSigningRoot (root : ByteArray) : Except MapError (Option Point) :=
  complete (mapSigningRoot root)

def hashToCurve (msg dst : ByteArray) : Except MapError (Option Point) :=
  complete (match HashField.hashToField msg dst with
    | .error e => .error (.hashError e)
    | .ok a => mapCoefficients a)

/-- Kind: checked output.
Says: finite output of the concrete final checker passes both predicates.
Does not say: group-law correctness or completeness. -/
theorem clearCheck_ok (q out : Point) (h : clearCheck (some q) = .ok (some out)) :
    q = out ∧ (onTarget out && subgroupCheck out) = true := by
  by_cases hc : (onTarget q && subgroupCheck q) = true
  · simp only [clearCheck,if_pos hc,Except.ok.injEq,Option.some.injEq] at h
    subst out
    exact ⟨rfl,hc⟩
  · simp only [clearCheck,if_neg hc] at h
    cases h

private theorem clearCheck_finite (q : Option Point) (out : Point)
    (h : clearCheck q = .ok (some out)) : (onTarget out && subgroupCheck out) = true := by
  cases q with
  | none =>
    simp only [clearCheck,Except.ok.injEq] at h
    cases h
  | some p => exact (clearCheck_ok p out h).2

/-- Kind: public output invariant.
Says: a successful finite clearing result passes both executable predicates.
Does not say: the predicates are universally equivalent to the mathematical group. -/
theorem clearMapped_ok (a b : Option Point) (out : Point)
    (h : clearMapped a b = .ok (some out)) : (onTarget out && subgroupCheck out) = true := by
  by_cases hc : (pointAdmitted a && pointAdmitted b) = true
  · simp only [clearMapped,if_pos hc] at h
    exact clearCheck_finite (clearSum a b) out h
  · simp only [clearMapped,if_neg hc] at h
    cases h

/-- Kind: linkage.
Says: map failures propagate into the public hash-to-curve.
Does not say: the root is authenticated. -/
theorem hashSigningRoot_error (root : ByteArray) (e : MapError)
    (h : mapSigningRoot root = .error e) : hashSigningRoot root = .error e := by
  simp only [hashSigningRoot,h,complete]

/-- Kind: linkage.
Says: a mapped root uses the actual clearing function.
Does not say: universal RFC refinement. -/
theorem hashSigningRoot_delegates (root : ByteArray) (a b : Option Point)
    (h : mapSigningRoot root = .ok (a,b)) : hashSigningRoot root = clearMapped a b := by
  simp only [hashSigningRoot,h,complete]

/-- Kind: linkage.
Says: generic hash-to-field errors propagate.
Does not say: all admitted messages map successfully. -/
theorem hashToCurve_error (msg dst : ByteArray) (e : HashField.HashError)
    (h : HashField.hashToField msg dst = .error e) :
    hashToCurve msg dst = .error (.hashError e) := by
  simp only [hashToCurve,h,complete]

/-- Kind: linkage.
Says: generic hash-to-field success enters the same concrete completion path.
Does not say: signature verification. -/
theorem hashToCurve_delegates (msg dst : ByteArray) (a : Array Nat)
    (h : HashField.hashToField msg dst = .ok a) :
    hashToCurve msg dst = complete (mapCoefficients a) := by
  simp only [hashToCurve,h]

#print axioms EthereumConsensus.BLS.G2Map.clearCheck_ok
#print axioms EthereumConsensus.BLS.G2Map.clearMapped_ok
#print axioms EthereumConsensus.BLS.G2Map.hashSigningRoot_error
#print axioms EthereumConsensus.BLS.G2Map.hashSigningRoot_delegates
#print axioms EthereumConsensus.BLS.G2Map.hashToCurve_error
#print axioms EthereumConsensus.BLS.G2Map.hashToCurve_delegates

end EthereumConsensus.BLS.G2Map

-- Test-only byte transport. No host hash or field answer.
open EthereumConsensus.BLS.HashField
private def nibble (b : UInt8) : Except String UInt8 :=
  if 48 ≤ b && b ≤ 57 then .ok (b-48)
  else if 97 ≤ b && b ≤ 102 then .ok (b-97+10)
  else .error "invalid_hex"

private def readHex (s : String) : Except String ByteArray := do
  if s = "-" then return ByteArray.empty
  let b := s.toUTF8
  if b.size % 2 != 0 then throw "invalid_hex"
  let mut out := ByteArray.empty
  for i in [:b.size/2] do
    let hi ← nibble b[2*i]!
    let lo ← nibble b[2*i+1]!
    out := out.push (16*hi+lo)
  return out

private def errorName : HashError → String
  | .resourceLimit => "resource_limit"
  | .dstWidth => "dst_width"
  | .signingRootWidth => "signing_root_width"
  | .internalInvariant => "internal_invariant"


private def mapErrorName : EthereumConsensus.BLS.G2Map.MapError → String
  | .noncanonical => "noncanonical"
  | .internalInvariant => "internal_invariant"
  | .hashError e => errorName e

private def printMapPoint : Option EthereumConsensus.BLS.G2Map.Point → String
  | none => "infinity"
  | some p => String.intercalate " " ([p.x.re,p.x.im,p.y.re,p.y.im].map toString)

private def readMapNat (s : String) : Except String Nat :=
  if s.utf8ByteSize > 116 then .error "resource_limit"
  else match s.toNat? with
    | none => .error "invalid_decimal"
    | some n => .ok n

private def mapDispatch (a b : String) : Except String String := do
  let re ← readMapNat a
  let im ← readMapNat b
  let q ← (EthereumConsensus.BLS.G2Map.mapField ⟨re,im⟩).mapError mapErrorName
  return "ok " ++ printMapPoint q

private def mapRootDispatch (root : String) : Except String String := do
  let bytes ← readHex root
  let (a,b) ← (EthereumConsensus.BLS.G2Map.mapSigningRoot bytes).mapError mapErrorName
  return "ok " ++ printMapPoint a ++ " ; " ++ printMapPoint b

private def dispatchHash (s : String) : Except String String := do
  let result ← match s.splitOn " " with
    | ["pop", root] => do
      let bytes ← readHex root
      (consensusHashToField bytes).mapError errorName
    | ["field", msg, dst] => do
      let m ← readHex msg
      let d ← readHex dst
      (hashToField m d).mapError errorName
    | _ => throw "operation"
  return "ok " ++ String.intercalate " " (result.toList.map toString)


private def readClearPoint (s : String) : Except String (Option EthereumConsensus.BLS.G2Map.Point) := do
  if s = "-" then return none
  match s.splitOn "," with
  | [a,b,c,d] =>
    let x ← readMapNat a
    let y ← readMapNat b
    let z ← readMapNat c
    let w ← readMapNat d
    return some ⟨⟨x,y⟩,⟨z,w⟩⟩
  | _ => throw "operation"

private def clearDispatch (a b : String) : Except String String := do
  let p ← readClearPoint a
  let q ← readClearPoint b
  let out ← (EthereumConsensus.BLS.G2Map.clearMapped p q).mapError mapErrorName
  return "ok " ++ printMapPoint out

private def curveDispatch (msg dst : String) : Except String String := do
  let m ← readHex msg
  let d ← readHex dst
  let out ← (EthereumConsensus.BLS.G2Map.hashToCurve m d).mapError mapErrorName
  return "ok " ++ printMapPoint out

private def curveRootDispatch (root : String) : Except String String := do
  let bytes ← readHex root
  let out ← (EthereumConsensus.BLS.G2Map.hashSigningRoot bytes).mapError mapErrorName
  return "ok " ++ printMapPoint out

private def dispatch (s : String) : Except String String :=
  match s.splitOn " " with
  | ["clear",a,b] => clearDispatch a b
  | ["curve",msg,dst] => curveDispatch msg dst
  | ["curveroot",root] => curveRootDispatch root
  | ["map",a,b] => mapDispatch a b
  | ["maproot",root] => mapRootDispatch root
  | _ => dispatchHash s

def EthereumConsensus.BLS.HashToFieldCLI.run : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 9000 then .error "resource_limit"
                  else dispatch line.trimAscii.toString
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
