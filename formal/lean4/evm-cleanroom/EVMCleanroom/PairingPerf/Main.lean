import EVMCleanroom.Precompiles.BN254Pairing
import EVMCleanroom.Precompiles.BLS12381Pairing
import EVMCleanroom.Precompiles.KZGPairing

/-!
# `evm-pairingperf`: the fast pairing checks against the `Nat` definitions, and their time

    evm-pairingperf [SCALE]
    evm-pairingperf [--dangerously-enable-unverified-keccak] --bench FILE REPEATS

Without `--bench`: first an executable differential check of the limb tower and the fast
pairing (`FastTower`, `FastPairing`, `BN254Pairing`, `BLS12381Pairing`, `KZGPairing`) against
the definitional `Nat` path (`Tower`, `Pairing`, `BN254`, `BLS12381`, `KZG`) over
deterministic pseudo-random inputs; `SCALE` (default 100) is a percentage of the default
case counts. Any difference makes the exit status 1. Then the time of the old and the new
path on a two-pair input, as a whole and per stage (decoding with subgroup checks, Miller
loops, final exponentiation).

With `--bench`: the OLD path of the three precompiles (0x08, 0x0a, 0x0f) on the cases of a
batch file, in the output format of `evm-precompile --bench`, so `bench.py` can report the
old and the new path from one CI run. Other addresses are skipped.

The algebra is tested here, not proved.
-/

namespace EVMCleanroom.PairingPerf

open EVMCleanroom.Precompiles

/-- A deterministic walk for test inputs (not a cryptographic generator). -/
def stepRng (x : Nat) : Nat :=
  (x * x + 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89) % (2 ^ 521 - 1)

structure Check where
  name : String
  cases : Nat
  failures : Nat
  note : String := ""

def randFp2 (p seed : Nat) : Fp2 × Nat :=
  let a := stepRng seed
  let b := stepRng a
  (⟨a % p, b % p⟩, b)

def randFp12 (p seed : Nat) : Fp12 × Nat := Id.run do
  let mut x := seed
  let mut cs : Array Fp2 := #[]
  for _ in [0:6] do
    let r := randFp2 p x
    cs := cs.push r.1
    x := r.2
  return (⟨cs[0]!, cs[1]!, cs[2]!, cs[3]!, cs[4]!, cs[5]!⟩, x)

def oldEasy (T : Tower) (f : Fp12) : Fp12 :=
  let easy1 := Fp12.mul T (Fp12.conj T f) (Fp12.inv T f)
  Fp12.mul T (Fp12.frobenius T (Fp12.frobenius T easy1)) easy1

/-- Every operation of the quadratic extension and of the tower on random elements, against
    `Field.lean` and `Tower.lean`. -/
@[specialize] def checkTower {K : Type} (name : String) (Q : QuadOps K) (C : FastCurve K) (toFp2 : K → Fp2)
    (ofFp2 : Fp2 → K) (old : PairingCurve) (hardPower count : Nat) : Array Check := Id.run do
  let T := C.tower
  let oldT := old.tower
  let p := oldT.p
  let flat := Fq12.toFlat toFp2
  let lift := Fq12.ofFlat ofFp2
  let mut seed := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
  let mut mulBad := 0
  let mut sqrBad := 0
  let mut invBad := 0
  let mut frobBad := 0
  let mut conjBad := 0
  let mut lineBad := 0
  let mut quadBad := 0
  let mut cycBad := 0
  let mut hardBad := 0
  for i in [0:count] do
    let ra := randFp12 p seed
    let rb := randFp12 p ra.2
    seed := rb.2
    let a := ra.1
    let b := rb.1
    let fa := lift a
    let fb := lift b
    if flat (Fq12.mul Q fa fb) != Fp12.mul oldT a b then mulBad := mulBad + 1
    if flat (Fq12.sqr Q fa) != Fp12.sqr oldT a then sqrBad := sqrBad + 1
    if flat (Fq12.inv Q fa) != Fp12.inv oldT a then invBad := invBad + 1
    if flat (Fq12.frobenius Q T fa) != Fp12.frobenius oldT a then frobBad := frobBad + 1
    if flat (Fq12.conj Q fa) != Fp12.conj oldT a then conjBad := conjBad + 1
    let l0 := b.c0
    let l1 := b.c1
    let l2 := b.c2
    let sparse : Fp12 := if C.divide then ⟨l0, l1, Fp2.zero, l2, Fp2.zero, Fp2.zero⟩
      else ⟨l0, Fp2.zero, l1, l2, Fp2.zero, Fp2.zero⟩
    let fastLine := if C.divide then Fq12.mulLineD Q fa (ofFp2 l0) (ofFp2 l1) (ofFp2 l2)
      else Fq12.mulLineM Q fa (ofFp2 l0) (ofFp2 l1) (ofFp2 l2)
    if flat fastLine != Fp12.mul oldT a sparse then lineBad := lineBad + 1
    -- The quadratic extension: every operation, on six random pairs per case and on edge values.
    let edges : Array Fp2 := #[⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨p - 1, p - 1⟩, ⟨p - 1, 0⟩, ⟨0, p - 1⟩, ⟨p - 2, 1⟩, ⟨(p - 1) / 2, (p + 1) / 2⟩]
    let xs : Array Fp2 := #[a.c0, a.c1, a.c2, a.c3, a.c4, a.c5, edges[i % 8]!, edges[(i / 8) % 8]!]
    let ys : Array Fp2 := #[b.c0, b.c1, b.c2, b.c3, b.c4, edges[(i / 64) % 8]!, b.c5, edges[i % 8]!]
    for j in [0:8] do
      let u := xs[j]!
      let v := ys[j]!
      let x := ofFp2 u
      let y := ofFp2 v
      if toFp2 (Q.mul x y) != Fp2.mul p u v || toFp2 (Q.sqr x) != Fp2.sqr p u ||
          toFp2 (Q.inv x) != Fp2.inv p u || toFp2 (Q.mulXi x) != Fp2.mul p u oldT.xi ||
          toFp2 (Q.add x y) != Fp2.add p u v || toFp2 (Q.sub x y) != Fp2.sub p u v ||
          toFp2 (Q.neg x) != Fp2.neg p u || toFp2 (Q.conj x) != Fp2.conj p u ||
          toFp2 (Q.double x) != Fp2.add p u u || toFp2 (Q.mulReal x y) != Fp2.scale p v.c0 u ||
          Q.isZero x != Fp2.isZero u || Q.eq x y != (u == v) || !Q.eq x x || toFp2 x != u then
        quadBad := quadBad + 1
    -- The cyclotomic subgroup: squaring, and (one case in eight) the hard part as the stated power.
    let e := oldEasy oldT a
    let fe := FastPairing.easyPart Q C fa
    if flat fe != e || flat (Fq12.cyclotomicSqr Q fe) != Fp12.sqr oldT e then cycBad := cycBad + 1
    if i % 8 == 0 then
      if flat (FastPairing.hardPart Q C fe) != Fp12.pow oldT (Pairing.hardPart old e) hardPower then hardBad := hardBad + 1
  return #[⟨name ++ " quadratic extension, every operation", 8 * count, quadBad, ""⟩, ⟨name ++ " Fq12 mul", count, mulBad, ""⟩,
    ⟨name ++ " Fq12 sqr", count, sqrBad, ""⟩, ⟨name ++ " Fq12 inverse", count, invBad, ""⟩,
    ⟨name ++ " Fq12 Frobenius", count, frobBad, ""⟩, ⟨name ++ " Fq12 conjugate", count, conjBad, ""⟩,
    ⟨name ++ " sparse line product", count, lineBad, ""⟩, ⟨name ++ " easy part and cyclotomic squaring", count, cycBad, ""⟩,
    ⟨name ++ " hard part = old hard part ^ hardPower", (count + 7) / 8, hardBad, ""⟩]

/-- The Miller value (when the digits are binary; after the easy part otherwise), the final
    value as the stated power of the old one, and the verdict, for one list of finite pairs.
    Returns the three mismatch flags. -/
@[specialize] def compareProduct {K : Type} (Q : QuadOps K) (C : FastCurve K) (toFp2 : K → Fp2) (ofFp2 : Fp2 → K)
    (old : PairingCurve) (hardPower : Nat) (exact : Bool) (pairs : List (Pairing.G1 × Pairing.G2)) : Nat × Nat × Nat :=
  let states := pairs.map fun (a, b) =>
    FastPairing.pairState Q (ofFp2 ⟨a.1, 0⟩) (ofFp2 ⟨a.2, 0⟩) (ofFp2 b.1) (ofFp2 b.2)
  let fm := FastPairing.millerProduct Q C states
  let om := Pairing.millerProduct old pairs Fp12.one
  let ff := FastPairing.finalExponentiation Q C fm
  let ofin := Pairing.finalExponentiation old om
  let m := if exact then (if Fq12.toFlat toFp2 fm != om then 1 else 0)
    else (if Fq12.toFlat toFp2 (FastPairing.easyPart Q C fm) != oldEasy old.tower om then 1 else 0)
  let f := if Fq12.toFlat toFp2 ff != Fp12.pow old.tower ofin hardPower then 1 else 0
  let v := if FastPairing.productIsOne Q C states != Pairing.productIsOne old pairs then 1 else 0
  (m, f, v)

def sameResult : Result → Result → Bool
  | .success a x, .success b y => a.data == b.data && x == y
  | .failure, .failure => true
  | .refusal, .refusal => true
  | _, _ => false

def isSuccessOne : Result → Bool
  | .success out _ => out.size == 32 && out.data[31]! == 1
  | _ => false

def isSuccess : Result → Bool
  | .success _ _ => true
  | _ => false

/-! ### alt_bn128 -/

def bnG2 : Fp2 × Fp2 :=
  (⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634⟩,
   ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531⟩)

def bnMul1 (k : Nat) : Option (Nat × Nat) :=
  Curve.toAffine BN254.field (Curve.mul BN254.field k (Curve.ofAffine BN254.field 1 2))
def bnMul2 (k : Nat) (q : Fp2 × Fp2) : Option (Fp2 × Fp2) :=
  Curve.toAffine BN254.field2 (Curve.mul BN254.field2 k (Curve.ofAffine BN254.field2 q.1 q.2))

def bnEncode1 : Option (Nat × Nat) → ByteArray
  | none => natToBE 64 0
  | some (x, y) => natToBE 32 x ++ natToBE 32 y
def bnEncode2 : Option (Fp2 × Fp2) → ByteArray
  | none => natToBE 128 0
  | some (x, y) => natToBE 32 x.c1 ++ natToBE 32 x.c0 ++ natToBE 32 y.c1 ++ natToBE 32 y.c0

def bnDefinitional (q : Fp2 × Fp2) : Bool :=
  Curve.isInfinity BN254.field2 (Curve.mul BN254.field2 BN254.r (Curve.ofAffine BN254.field2 q.1 q.2))

/-- A checked square root in `Fp2` for `p ≡ 3 (mod 4)` (the method of `BLS12381.sqrt2?`). -/
def sqrtFp2 (p : Nat) (a : Fp2) : Option Fp2 :=
  let candidate : Option Fp2 :=
    if a.c1 = 0 then
      match Fp.sqrt? p a.c0 with
      | some root => some ⟨root, 0⟩
      | none => (Fp.sqrt? p (Fp.neg p a.c0)).map fun root => ⟨0, root⟩
    else
      match Fp.sqrt? p ((a.c0 * a.c0 + a.c1 * a.c1) % p) with
      | none => none
      | some s =>
        let half := Fp.inv p 2
        let pick (t : Nat) : Option Fp2 :=
          (Fp.sqrt? p t).map fun x0 => ⟨x0, Fp.mul p a.c1 (Fp.inv p (2 * x0 % p))⟩
        match pick (Fp.mul p (Fp.add p a.c0 s) half) with
        | some root => some root
        | none => pick (Fp.mul p (Fp.sub p a.c0 s) half)
  match candidate with
  | some root => if Fp2.sqr p root == a then some root else none
  | none => none

/-- A point of the alt_bn128 twist with a pseudo-random `x` (almost surely outside the subgroup). -/
def bnTwistPoint (seed : Nat) : (Fp2 × Fp2) × Nat := Id.run do
  let p := BN254.p
  let mut s := seed
  let mut found : Fp2 × Fp2 := bnG2
  for _ in [0:64] do
    let r := randFp2 p s
    s := r.2
    let x := r.1
    match sqrtFp2 p (Fp2.add p (Fp2.mul p (Fp2.sqr p x) x) BN254.twistB) with
    | some y =>
      found := (x, if s % 2 == 0 then y else Fp2.neg p y)
      break
    | none => pure ()
  return (found, s)

/-- The subgroup test against `[r]Q = O`: multiples of the generator, cofactor-cleared random
    points (inside), random points of the twist (outside), and points of order 10069. -/
def checkBnSubgroup (count : Nat) : Array Check := Id.run do
  let cofactor := 2 * BN254.p - BN254.r
  let mut seed := 0x6a09e667f3bcc908bb67ae8584caa73b3c6ef372fe94f82ba54ff53a5f1d36f1
  let mut bad := 0
  let mut badShort := 0
  let mut insideSeen := 0
  let mut outsideSeen := 0
  let mut smallSeen := 0
  let mut wrongSide := 0
  let mut cases := 0
  -- Multiples of the generator.
  for _ in [0:count] do
    seed := stepRng seed
    match bnMul2 (seed % BN254.r) bnG2 with
    | some q =>
      cases := cases + 1
      insideSeen := insideSeen + 1
      if !BN254Pairing.inG2 q.1 q.2 then bad := bad + 1
      if !BN254Pairing.inG2Short q.1 q.2 then badShort := badShort + 1
      if !bnDefinitional q then wrongSide := wrongSide + 1
    | none => pure ()
  -- Random points of the twist: the definition decides which side they are on.
  for i in [0:3 * count] do
    let r := bnTwistPoint seed
    seed := r.2
    let q := r.1
    cases := cases + 1
    let expect := bnDefinitional q
    if expect then insideSeen := insideSeen + 1 else outsideSeen := outsideSeen + 1
    if BN254Pairing.inG2 q.1 q.2 != expect then bad := bad + 1
    if BN254Pairing.inG2Short q.1 q.2 != expect then badShort := badShort + 1
    -- One in sixteen: the same point with the cofactor cleared (inside), and with the
    -- order-r part and all of the cofactor but 10069 cleared (order 1 or 10069).
    if i % 16 == 0 then
      match bnMul2 cofactor q with
      | some c =>
        cases := cases + 1
        let e := bnDefinitional c
        if e then insideSeen := insideSeen + 1 else wrongSide := wrongSide + 1
        if BN254Pairing.inG2 c.1 c.2 != e then bad := bad + 1
        if BN254Pairing.inG2Short c.1 c.2 != e then badShort := badShort + 1
      | none => pure ()
      match bnMul2 (BN254.r * (cofactor / 10069)) q with
      | some c =>
        cases := cases + 1
        smallSeen := smallSeen + 1
        let e := bnDefinitional c
        if e then wrongSide := wrongSide + 1
        if BN254Pairing.inG2 c.1 c.2 != e then bad := bad + 1
        if BN254Pairing.inG2Short c.1 c.2 != e then badShort := badShort + 1
      | none => pure ()
  return #[⟨"alt_bn128 G2 subgroup test = definitional [r]Q = O", cases, bad,
    s!"{insideSeen} inside, {outsideSeen} random points outside, {smallSeen} of order 10069"⟩,
    ⟨"alt_bn128 G2 short relation = definitional [r]Q = O", cases, badShort, ""⟩,
    ⟨"alt_bn128 subgroup test inputs on the expected side", cases, wrongSide, ""⟩]

/-- alt_bn128 on the generic `Fq2` over the limb field: the second route to the tower. -/
def bnGenericCurve : FastCurve (Fq2 U256) :=
  let c (i : Nat) : Fq2 U256 := Fq2.ofNat BN254.baseField.ofNat BN254.tower.frob[i]!
  { tower := { frob1 := c 1, frob2 := c 2, frob3 := c 3, frob4 := c 4, frob5 := c 5 }, divide := true,
    loopDigits := BN254Pairing.loopDigits, frobeniusSteps := true, negative := false,
    xDigits := BN254Pairing.xDigits, bnFamily := true }

/-- Random finite pairs: the Miller value, the final value and the verdict. -/
def checkBnPairs (count : Nat) : Array Check := Id.run do
  let exact := BN254Pairing.loopDigits.all fun d => d != Digit.minus
  let mut seed := 0x510e527fade682d19b05688c2b3e6c1f1f83d9abfb41bd6b5be0cd19137e2179
  let mut miller := 0
  let mut finalBad := 0
  let mut verdict := 0
  let mut generic := 0
  for i in [0:count] do
    let mut pairs : List (Pairing.G1 × Pairing.G2) := []
    for _ in [0:1 + i % 3] do
      let a := stepRng seed
      let b := stepRng a
      seed := b
      match bnMul1 (a % BN254.r), bnMul2 (b % BN254.r) bnG2 with
      | some x, some y => pairs := (x, y) :: pairs
      | _, _ => pure ()
    let r := compareProduct (Quad256.ops BN254.baseField true) BN254Pairing.fastCurve BN254Pairing.ofLimbs
      BN254Pairing.toLimbs BN254.curve BN254Pairing.hardPower exact pairs
    if i % 8 == 0 then
      let g := compareProduct (Fq2.quadOps BN254.baseField.ops true) bnGenericCurve (Fq2.toNat BN254.baseField.toNat)
        (Fq2.ofNat BN254.baseField.ofNat) BN254.curve BN254Pairing.hardPower exact pairs
      generic := generic + g.1 + g.2.1 + g.2.2
    miller := miller + r.1
    finalBad := finalBad + r.2.1
    verdict := verdict + r.2.2
  return #[⟨"alt_bn128 Miller value = old Miller value" ++ (if exact then "" else " after the easy part (signed digits)"), count, miller, ""⟩,
    ⟨"alt_bn128 products on the generic Fq2 over the limb field", (count + 7) / 8, generic, ""⟩,
    ⟨"alt_bn128 final value = old final value ^ hardPower", count, finalBad, ""⟩,
    ⟨"alt_bn128 product verdict", count, verdict, ""⟩]

/-- Whole calls of 0x08, old body against new: products that are one, products that are
    not, pairs with infinity, and inputs with one byte changed. -/
def checkBnBody (count : Nat) : Array Check := Id.run do
  let r := BN254.r
  let mut seed := 0x428a2f98d728ae227137449123ef65cdb5c0fbcfec4d3b2fe9b5dba58189dbbc
  let mut bad := 0
  let mut ones := 0
  let mut zeros := 0
  let mut fails := 0
  let mut cases := 0
  for i in [0:count] do
    let n := 1 + i % 4
    let mut input := ByteArray.empty
    let mut sum := 0
    for j in [0:n] do
      let a := stepRng seed
      let b := stepRng a
      seed := b
      -- The last pair closes the product to one in two cases of three.
      let closing := j + 1 == n && i % 3 != 0 && n > 1
      let a := if closing then (r - sum % r) % r else a % r
      let b := if closing then 1 else b % r
      -- Now and then a point at infinity on one side.
      let a := if !closing && b % 11 == 0 then 0 else a
      let b := if !closing && a % 13 == 1 then 0 else b
      sum := sum + a * b
      input := input ++ bnEncode1 (bnMul1 a) ++ bnEncode2 (bnMul2 b bnG2)
    let gas := BN254.pairingGas input.size
    let oldR := BN254.runPairing gas input
    let newR := BN254Pairing.runPairing gas input
    cases := cases + 1
    if !sameResult oldR newR then bad := bad + 1
    if isSuccessOne oldR then ones := ones + 1 else if isSuccess oldR then zeros := zeros + 1 else fails := fails + 1
    -- One byte changed (mostly off the curve or non-canonical; both must agree).
    let at_ := seed % input.size
    let changed := input.set! at_ (input.get! at_ + 1)
    let oldC := BN254.runPairing gas changed
    let newC := BN254Pairing.runPairing gas changed
    cases := cases + 1
    if !sameResult oldC newC then bad := bad + 1
    if isSuccessOne oldC then ones := ones + 1 else if isSuccess oldC then zeros := zeros + 1 else fails := fails + 1
    -- A G2 point of the twist outside the subgroup in the first pair: both must fail.
    if i % 4 == 0 then
      let t := bnTwistPoint seed
      seed := t.2
      let other := bnEncode1 (bnMul1 5) ++ bnEncode2 (some t.1) ++ input.extract 192 input.size
      let oldO := BN254.runPairing gas other
      let newO := BN254Pairing.runPairing gas other
      cases := cases + 1
      if !sameResult oldO newO then bad := bad + 1
      if isSuccessOne oldO then ones := ones + 1 else if isSuccess oldO then zeros := zeros + 1 else fails := fails + 1
  return #[⟨"alt_bn128 pairing call (0x08), old body = new body", cases, bad,
    s!"{ones} products equal to one, {zeros} not, {fails} failures"⟩]

/-! ### BLS12-381 -/

def blsMul1 (k : Nat) : Option (Nat × Nat) :=
  Curve.toAffine BLS12381.field (Curve.mul BLS12381.field k
    (Curve.ofAffine BLS12381.field BLS12381.g1Generator.1 BLS12381.g1Generator.2))
def blsMul2 (k : Nat) : Option (Fp2 × Fp2) :=
  Curve.toAffine BLS12381.field2 (Curve.mul BLS12381.field2 k
    (Curve.ofAffine BLS12381.field2 BLS12381.g2Generator.1 BLS12381.g2Generator.2))

def blsEncode1 : Option (Nat × Nat) → ByteArray
  | none => natToBE 128 0
  | some (x, y) => natToBE 64 x ++ natToBE 64 y
def blsEncode2 : Option (Fp2 × Fp2) → ByteArray
  | none => natToBE 256 0
  | some (x, y) => natToBE 64 x.c0 ++ natToBE 64 x.c1 ++ natToBE 64 y.c0 ++ natToBE 64 y.c1

def checkBlsPairs (count : Nat) : Array Check := Id.run do
  let mut seed := 0x3956c25bf348b53859f111f1b605d019923f82a4af194f9bab1c5ed5da6d8118
  let mut miller := 0
  let mut finalBad := 0
  let mut verdict := 0
  for i in [0:count] do
    let mut pairs : List (Pairing.G1 × Pairing.G2) := []
    for _ in [0:1 + i % 3] do
      let a := stepRng seed
      let b := stepRng a
      seed := b
      match blsMul1 (a % BLS12381.r), blsMul2 (b % BLS12381.r) with
      | some x, some y => pairs := (x, y) :: pairs
      | _, _ => pure ()
    let r := compareProduct (Quad384.ops BLS12381.baseField false) BLS12381Pairing.fastCurve BLS12381Pairing.ofLimbs
      BLS12381Pairing.toLimbs BLS12381.curve BLS12381Pairing.hardPower true pairs
    miller := miller + r.1
    finalBad := finalBad + r.2.1
    verdict := verdict + r.2.2
  return #[⟨"bls12-381 Miller value = old Miller value", count, miller, ""⟩,
    ⟨"bls12-381 final value = old final value ^ 3", count, finalBad, ""⟩,
    ⟨"bls12-381 product verdict", count, verdict, ""⟩]

def checkBlsBody (count : Nat) : Array Check := Id.run do
  let r := BLS12381.r
  let mut seed := 0xd807aa98a303024212835b0145706fbe243185be4ee4b28c550c7dc3d5ffb4e2
  let mut bad := 0
  let mut ones := 0
  let mut zeros := 0
  let mut fails := 0
  let mut cases := 0
  for i in [0:count] do
    let n := 1 + i % 3
    let mut input := ByteArray.empty
    let mut sum := 0
    for j in [0:n] do
      let a := stepRng seed
      let b := stepRng a
      seed := b
      let closing := j + 1 == n && i % 3 != 0 && n > 1
      let a := if closing then (r - sum % r) % r else a % r
      let b := if closing then 1 else b % r
      let a := if !closing && b % 11 == 0 then 0 else a
      let b := if !closing && a % 13 == 1 then 0 else b
      sum := sum + a * b
      input := input ++ blsEncode1 (blsMul1 a) ++ blsEncode2 (blsMul2 b)
    let gas := BLS12381.pairingGas input.size
    let oldR := BLS12381.runPairing gas input
    let newR := BLS12381Pairing.runPairing gas input
    cases := cases + 1
    if !sameResult oldR newR then bad := bad + 1
    if isSuccessOne oldR then ones := ones + 1 else if isSuccess oldR then zeros := zeros + 1 else fails := fails + 1
    let at_ := seed % input.size
    let changed := input.set! at_ (input.get! at_ + 1)
    let oldC := BLS12381.runPairing gas changed
    let newC := BLS12381Pairing.runPairing gas changed
    cases := cases + 1
    if !sameResult oldC newC then bad := bad + 1
    if isSuccessOne oldC then ones := ones + 1 else if isSuccess oldC then zeros := zeros + 1 else fails := fails + 1
  return #[⟨"bls12-381 pairing call (0x0f), old body = new body", cases, bad,
    s!"{ones} products equal to one, {zeros} not, {fails} failures"⟩]

/-- `KZG.verify` against the fast one: constant polynomials (true), and random points and
    scalars (false, apart from the constructed cases). -/
def checkKzg (count : Nat) : Array Check := Id.run do
  let r := BLS12381.r
  let mut seed := 0x72be5d74f27b896f80deb1fe3b1696b19bdc06a725c71235c19bf174cf692694
  let mut bad := 0
  let mut trues := 0
  for i in [0:count] do
    let a := stepRng seed
    let b := stepRng a
    let z := stepRng b
    seed := z
    let c := a % r
    let commitment := blsMul1 c
    let proof := if i % 3 == 0 then none else blsMul1 (b % r)
    let y := if i % 2 == 0 then c else (c + 1) % r
    let o := KZG.verify commitment proof (z % r) y
    let n := KZGPairing.verify commitment proof (z % r) y
    if o != n then bad := bad + 1
    if o then trues := trues + 1
  return #[⟨"KZG verify, old = new", count, bad, s!"{trues} accepted"⟩]

/-! ### Timing -/

@[noinline] def force (run : Unit → Nat) : IO Nat := pure (run ())

def sortNat (xs : Array Nat) : Array Nat := xs.qsort (· < ·)

/-- p50, p95 and max over `repeats` calls, in microseconds. -/
def measure (label : String) (repeats : Nat) (run : Unit → Nat) : IO Unit := do
  let mut times : Array Nat := #[]
  let mut digest := 0
  for _ in [0:repeats] do
    let start ← IO.monoNanosNow
    digest ← force run
    let stop ← IO.monoNanosNow
    times := times.push (stop - start)
  let sorted := sortNat times
  let pick (percent : Nat) := sorted[(sorted.size - 1) * percent / 100]! / 1000
  IO.println s!"TIMING {label}: p50 {pick 50} us, p95 {pick 95} us, max {pick 100} us (n={repeats}, check {digest})"

def resultDigest : Result → Nat
  | .success out left => out.size + left + (if out.size == 32 then out.data[31]!.toNat else 0)
  | .failure => 1
  | .refusal => 2

/-- `k` is a run-time value (zero in practice): every measured call depends on it, so the
    compiler cannot evaluate a measured call once at start-up. -/
def timings (k : Nat) : IO Unit := do
  -- alt_bn128: two finite pairs.
  let bnInput := bnEncode1 (bnMul1 (0x1234567890abcdef1234567890abcdef + k)) ++ bnEncode2 (bnMul2 (0xfedcba0987654321fedcba0987654321 + k) bnG2) ++
    bnEncode1 (bnMul1 0x1111111111111111222222222222222233333333) ++ bnEncode2 (bnMul2 0x4444444444444444555555555555555566666666 bnG2)
  let gas := 10000000 + k
  measure "alt_bn128 pairing, 2 pairs, OLD whole call" 9 fun _ => resultDigest (BN254.runPairing gas bnInput)
  measure "alt_bn128 pairing, 2 pairs, NEW whole call" 101 fun _ => resultDigest (BN254Pairing.runPairing gas bnInput)
  measure "alt_bn128 OLD decode (with [r]Q subgroup checks)" 9 fun _ =>
    ((BN254.decodePairs bnInput 2 0 []).map List.length).getD 99
  measure "alt_bn128 NEW decode (with endomorphism subgroup checks)" 101 fun _ =>
    ((BN254Pairing.decodePairs bnInput 2 0 []).map List.length).getD 99
  let bnOldPairs := (BN254.decodePairs bnInput 2 0 []).getD []
  let bnNewPairs := (BN254Pairing.decodePairs bnInput 2 0 []).getD []
  measure "alt_bn128 OLD Miller loops" 9 fun _ => (Pairing.millerProduct BN254.curve bnOldPairs Fp12.one).c0.c0
  measure "alt_bn128 NEW Miller loop (shared)" 101 fun _ => (BN254Pairing.millerProduct bnNewPairs).c0.c0.r0.toNat
  let bnOldM := Pairing.millerProduct BN254.curve bnOldPairs Fp12.one
  let bnNewM := BN254Pairing.millerProduct bnNewPairs
  measure "alt_bn128 OLD final exponentiation" 9 fun _ => (Pairing.finalExponentiation BN254.curve bnOldM).c0.c0
  measure "alt_bn128 NEW final exponentiation" 101 fun _ => (BN254Pairing.finalExponentiation bnNewM).c0.c0.r0.toNat
  -- The same loop without two of the steps, for the split: the generic Fq2 over the limb field
  -- (boxed coordinates, a reduction per base multiplication), and binary digits.
  let genQ (a : Fp2) : Fq2 U256 := Fq2.ofNat BN254.baseField.ofNat a
  let genPairs := bnOldPairs.map fun (a, b) =>
    FastPairing.pairState (Fq2.quadOps BN254.baseField.ops true) (genQ ⟨a.1, 0⟩) (genQ ⟨a.2, 0⟩) (genQ b.1) (genQ b.2)
  measure "alt_bn128 Miller loop on the generic Fq2 over the limb field (not routed)" 51 fun _ =>
    (FastPairing.millerProduct (Fq2.quadOps BN254.baseField.ops true) bnGenericCurve genPairs).c0.c0.c0.l0.toNat
  let genM := FastPairing.millerProduct (Fq2.quadOps BN254.baseField.ops true) bnGenericCurve genPairs
  measure "alt_bn128 final exponentiation on the generic Fq2 over the limb field (not routed)" 51 fun _ =>
    (FastPairing.finalExponentiation (Fq2.quadOps BN254.baseField.ops true) bnGenericCurve genM).c0.c0.c0.l0.toNat
  let binaryCurve : FastCurve Quad256 :=
    { BN254Pairing.fastCurve with loopDigits := signedDigits BN254Pairing.loopScalar 0 (Nat.log2 BN254Pairing.loopScalar) }
  measure "alt_bn128 Miller loop with binary digits (36 additions per pair; the signed digits have 21)" 51 fun _ =>
    (FastPairing.millerProduct (Quad256.ops BN254.baseField true) binaryCurve bnNewPairs).c0.c0.r0.toNat
  let q := (bnMul2 (0xfedcba0987654321fedcba0987654321 + k) bnG2).getD bnG2
  measure "alt_bn128 OLD one G2 subgroup check" 9 fun _ => if bnDefinitional q then 1 else 0
  measure "alt_bn128 NEW one G2 subgroup check, psi(Q) = [6x^2]Q" 101 fun _ => if BN254Pairing.inG2 q.1 q.2 then 1 else 0
  measure "alt_bn128 one G2 subgroup check by the short relation (not routed)" 101 fun _ => if BN254Pairing.inG2Short q.1 q.2 then 1 else 0
  -- BLS12-381: two finite pairs.
  let blsInput := blsEncode1 (blsMul1 (0x1234567890abcdef1234567890abcdef + k)) ++ blsEncode2 (blsMul2 (0xfedcba0987654321fedcba0987654321 + k)) ++
    blsEncode1 (blsMul1 0x1111111111111111222222222222222233333333) ++ blsEncode2 (blsMul2 0x4444444444444444555555555555555566666666)
  measure "bls12-381 pairing, 2 pairs, OLD whole call" 9 fun _ => resultDigest (BLS12381.runPairing gas blsInput)
  measure "bls12-381 pairing, 2 pairs, NEW whole call" 51 fun _ => resultDigest (BLS12381Pairing.runPairing gas blsInput)
  measure "bls12-381 decode (definitional subgroup checks, old and new alike)" 9 fun _ =>
    ((BLS12381Pairing.decodePairs blsInput 2 0 []).map List.length).getD 99
  let blsOldPairs := (BLS12381.decodePairs blsInput 2 0 []).getD []
  let blsNewPairs := (BLS12381Pairing.decodePairs blsInput 2 0 []).getD []
  measure "bls12-381 OLD Miller loops" 9 fun _ => (Pairing.millerProduct BLS12381.curve blsOldPairs Fp12.one).c0.c0
  measure "bls12-381 NEW Miller loop (shared)" 101 fun _ => (BLS12381Pairing.millerProduct blsNewPairs).c0.c0.r0.toNat
  let blsOldM := Pairing.millerProduct BLS12381.curve blsOldPairs Fp12.one
  let blsNewM := BLS12381Pairing.millerProduct blsNewPairs
  measure "bls12-381 OLD final exponentiation" 9 fun _ => (Pairing.finalExponentiation BLS12381.curve blsOldM).c0.c0
  measure "bls12-381 NEW final exponentiation" 101 fun _ => (BLS12381Pairing.finalExponentiation blsNewM).c0.c0.r0.toNat
  -- KZG: the verification equation only (two scalar multiplications and the product), no decompression.
  let commitment := blsMul1 (0x1234567890abcdef + k)
  let proof := blsMul1 0xfedcba0987654321
  measure "KZG OLD verify (2 scalar multiplications + product)" 9 fun _ => if KZG.verify commitment proof 12345 67890 then 1 else 0
  measure "KZG NEW verify (2 scalar multiplications + product)" 51 fun _ => if KZGPairing.verify commitment proof 12345 67890 then 1 else 0

/-! ### The old path in the format of `evm-precompile --bench` -/

def oldRun (address gas : Nat) (input : ByteArray) : Option Result :=
  match address with
  | 8 => some (BN254.runPairing gas input)
  | 10 => some (KZG.run gas input)
  | 15 => some (BLS12381.runPairing gas input)
  | _ => none

@[noinline] def oldUsed (address gas : Nat) (input : ByteArray) : IO Nat :=
  match oldRun address gas input with
  | some (.success _ left) => pure (gas - left)
  | _ => pure gas

def benchOld (path : String) (repeats : Nat) : IO UInt32 := do
  let lines ← IO.FS.lines path
  for line in lines do
    match (line.splitOn " ").filter (· ≠ "") with
    | [_, address, gas, hexInput] =>
      match address.toNat?, gas.toNat?, ofHex? (if hexInput == "-" then "" else hexInput) with
      | some address, some gas, some input =>
        if address == 8 || address == 10 || address == 15 then
          let mut times : Array Nat := #[]
          let mut used := 0
          for _ in [0:repeats] do
            let start ← IO.monoNanosNow
            used ← oldUsed address gas input
            let stop ← IO.monoNanosNow
            times := times.push (stop - start)
          let sorted := sortNat times
          let pick (percent : Nat) := sorted[(sorted.size - 1) * percent / 100]!
          IO.println s!"{address} {input.size} {used} {pick 0} {pick 50} {pick 95} {pick 100}"
      | _, _, _ => pure ()
    | _ => pure ()
  return 0

def main (args : List String) : IO UInt32 := do
  let args := match args with
    | "--dangerously-enable-unverified-keccak" :: rest => rest
    | rest => rest
  match args with
  | ["--bench", path, repeats] =>
    match repeats.toNat? with
    | some n => if n == 0 then return 2 else benchOld path n
    | none => return 2
  | _ =>
    let scale := (args.head?.bind String.toNat?).getD 100
    let n (base : Nat) := max 1 (base * scale / 100)
    let checks :=
      checkTower "alt_bn128" (Quad256.ops BN254.baseField true) BN254Pairing.fastCurve BN254Pairing.ofLimbs
          BN254Pairing.toLimbs BN254.curve BN254Pairing.hardPower (n 200)
        ++ checkTower "alt_bn128 (generic Fq2 over the limb field)" (Fq2.quadOps BN254.baseField.ops true) bnGenericCurve
          (Fq2.toNat BN254.baseField.toNat) (Fq2.ofNat BN254.baseField.ofNat) BN254.curve BN254Pairing.hardPower (n 40)
        ++ checkBnSubgroup (n 400) ++ checkBnPairs (n 60) ++ checkBnBody (n 60)
        ++ checkTower "bls12-381" (Quad384.ops BLS12381.baseField false) BLS12381Pairing.fastCurve BLS12381Pairing.ofLimbs
          BLS12381Pairing.toLimbs BLS12381.curve BLS12381Pairing.hardPower (n 100)
        ++ checkBlsPairs (n 30) ++ checkBlsBody (n 20) ++ checkKzg (n 12)
    let mut bad := 0
    let mut total := 0
    for c in checks do
      let verdict := if c.failures == 0 then "ok" else s!"{c.failures} FAILURES"
      let note := if c.note == "" then "" else s!" [{c.note}]"
      IO.println s!"check {c.name}: {verdict} ({c.cases} cases){note}"
      bad := bad + c.failures
      total := total + c.cases
    IO.println s!"RESULT pairing differential: {total} cases, {bad} failures"
    timings (scale / 1000000)
    return (if bad == 0 then 0 else 1)

end EVMCleanroom.PairingPerf

def main (args : List String) : IO UInt32 := EVMCleanroom.PairingPerf.main args
