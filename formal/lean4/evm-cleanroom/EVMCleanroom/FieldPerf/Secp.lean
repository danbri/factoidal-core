import EVMCleanroom.Precompiles.Secp256k1Fast
import EVMCleanroom.Precompiles.Ecrecover

/-!
# `evm-secpperf`: the secp256k1 fast paths against the old ones, and time per step

    evm-secpperf [COUNT]            differential check, then timings (default COUNT 2000)
    evm-secpperf --emit-valid COUNT one `shanghaiPlus 1 3000 HEX` line per valid signature

The differential check compares, on edge values and `COUNT` pseudo-random inputs each:
the inlined limb field with the `Nat` field; `scalarInvFast` with `scalarInv`;
`mulBaseFast`, `mulAddFast`, `recoverFast` with `mulBase`, `mulAdd`, `recover`; and the
ECRECOVER precompile with a copy of its previous body (`oldRun`, which calls
`Secp256k1.recover`). Valid signatures are made from a random key and nonce with the old
functions, so the recovered key is also compared with the known one. Any difference, any
use of a fall-back, and any recoding longer than 130 digits makes the exit status 1.

The timings put the old and the new step side by side in one process. This is a test and
a measurement, not a proof.
-/

namespace EVMCleanroom.SecpPerf

open EVMCleanroom.Precompiles
open EVMCleanroom.Precompiles.Secp256k1
open EVMCleanroom.Precompiles.Secp256k1.Fast

/-- SplitMix64 (Steele, Lea and Flood 2014): the next state and an output word. -/
def mix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> (30 : UInt64))) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> (27 : UInt64))) * 0x94d049bb133111eb
  (s, z ^^^ (z >>> (31 : UInt64)))

/-- A pseudo-random number below `2^256`. -/
def rand256 (s : UInt64) : UInt64 × Nat :=
  let (s, a) := mix s
  let (s, b) := mix s
  let (s, c) := mix s
  let (s, d) := mix s
  (s, a.toNat + b.toNat * 2 ^ 64 + c.toNat * 2 ^ 128 + d.toNat * 2 ^ 192)

/-- `count` pseudo-random numbers below `2^256`; every eighth is short or has long runs. -/
def randoms (seed : UInt64) (count : Nat) : Array Nat := Id.run do
  let mut s := seed
  let mut out : Array Nat := Array.mkEmpty count
  for i in [0:count] do
    let (s', x) := rand256 s
    s := s'
    let x := match i % 8 with
      | 5 => x % 2 ^ 64
      | 6 => x % 2 ^ 128
      | 7 => x ||| (2 ^ 200 - 2 ^ 72)
      | _ => x
    out := out.push x
  return out

def edgeScalars : Array Nat :=
  #[0, 1, 2, 3, n - 1, n - 2, n, n + 1, 2 * n, lam, n - lam, lam + 1, lam - 1, 2 ^ 64, 2 ^ 127, 2 ^ 128 - 1, 2 ^ 128,
    2 ^ 129, 2 ^ 255, 2 ^ 256 - 1, n / 2, n / 2 + 1, n / 3, glvA1, glvB1, glvA2, p, p - 1]

structure Sig where
  z : Nat
  parity : Nat
  r : Nat
  s : Nat
  key : Option (Nat × Nat)

/-- A valid signature made with the old functions: key `d`, nonce `k`, hash `z`. -/
def makeSig (d k z : Nat) : Option Sig :=
  match mulBase k with
  | none => none
  | some (rx, ry) =>
    let r := rx % n
    let s := scalarInv k * ((z + r * d) % n) % n
    if r = 0 ∨ s = 0 ∨ rx ≠ r then none else some ⟨z, ry % 2, r, s, mulBase d⟩

def validSigs (count : Nat) : Array Sig := Id.run do
  let xs := randoms 0x5ec9256b1 (3 * count)
  let mut out : Array Sig := Array.mkEmpty count
  for i in [0:count] do
    match makeSig (xs[3 * i]! % (n - 1) + 1) (xs[3 * i + 1]! % (n - 1) + 1) xs[3 * i + 2]! with
    | some sig => out := out.push sig
    | none => pure ()
  return out

def sigInput (sig : Sig) : ByteArray :=
  natToBE 32 sig.z ++ natToBE 32 (27 + sig.parity) ++ natToBE 32 sig.r ++ natToBE 32 sig.s

/-- The body of ECRECOVER before the fast path: `Secp256k1.recover`. -/
def oldBody (data : ByteArray) : Body :=
  let v := beNat data 32 32
  if v ≠ 27 ∧ v ≠ 28 then .output ByteArray.empty
  else
    match recover (beNat data 0 32) (v - 27) (beNat data 64 32) (beNat data 96 32) with
    | none => .output ByteArray.empty
    | some (x, y) => .output (Ecrecover.addressBytes x y)

def oldRun (gas : Nat) (input : ByteArray) : Result :=
  charge gas Ecrecover.gasCost fun _ => oldBody (readPadded input 0 128)

def showResult : Result → String
  | .success out left => toHex out ++ ":" ++ toString left
  | .failure => "failure"
  | .refusal => "refusal"

def accept : Keccak.Acceptance := Keccak.dangerouslyAcceptUnverified

/-! ### Differential checks -/

def fieldSamples (count : Nat) : Array Nat :=
  (#[0, 1, 2, p - 1, p - 2, (p - 1) / 2, 2 ^ 64, 2 ^ 64 - 1, 2 ^ 128, 2 ^ 192 - 1, 2 ^ 255, 2 ^ 256 - 1,
    2 ^ 32, 977, 2 ^ 256 - 2 ^ 32, 2 ^ 256] ++ randoms 0xf1e1d count).map (· % p)

def checkField (count : Nat) : Nat := Id.run do
  let xs := fieldSamples count
  let mut bad := 0
  for a in xs do
    let fa := U256.ofNat a
    if (Ff.sqr fa).toNat != a * a % p then bad := bad + 1
    if (Ff.neg fa).toNat != Fp.neg p a then bad := bad + 1
    if (Ff.cneg true fa).toNat != Fp.neg p a || (Ff.cneg false fa).toNat != a then bad := bad + 1
    if (Ff.mulSmall fa 3).toNat != a * 3 % p || (Ff.mulSmall fa 4).toNat != a * 4 % p
        || (Ff.mulSmall fa 8).toNat != a * 8 % p then bad := bad + 1
    for b in xs.extract 0 48 do
      let fb := U256.ofNat b
      if (Ff.mul fa fb).toNat != a * b % p then bad := bad + 1
      if (Ff.add fa fb).toNat != Fp.add p a b then bad := bad + 1
      if (Ff.sub fa fb).toNat != Fp.sub p a b then bad := bad + 1
  for a in xs.extract 0 200 do
    let fa := U256.ofNat a
    if (Ff.inv fa).toNat != Fp.inv p a then bad := bad + 1
    if (Ff.xgcd Fe.P fa).toNat != Fp.inv p a then bad := bad + 1
    let expect := Fp.sqrt? p a
    let root := Ff.sqrtCandidate fa
    let got := if U256.beq (Ff.sqr root) fa then some root.toNat else none
    if expect != got then bad := bad + 1
  return bad

def checkScalarInv (xs : Array Nat) : Nat := Id.run do
  let mut bad := 0
  for a in xs do
    let a := a % n
    if scalarInvFast a != scalarInv a then bad := bad + 1
    if a != 0 && scalarInvCandidate a != scalarInv a then bad := bad + 1
  return bad

/-- Decomposition and recoding: no fall-back, short halves, digits that reconstruct them. -/
def checkSplit (xs : Array Nat) : Nat × Nat := Id.run do
  let mut bad := 0
  let mut longest := 0
  for k in xs do
    let k := k % n
    let c := glvCandidate k
    if glvSplit k != c then bad := bad + 1
    if !(c.1.natAbs < 2 ^ 128 && c.2.natAbs < 2 ^ 128) then bad := bad + 1
    let d1 := ScalarMul.wnaf 128 c.1.natAbs
    let d2 := ScalarMul.wnaf 16 c.2.natAbs
    if ScalarMul.evalArr d1 != (c.1.natAbs : Int) || ScalarMul.evalArr d2 != (c.2.natAbs : Int) then bad := bad + 1
    longest := max longest (max d1.size d2.size)
  return (bad, longest)

def checkMulBase (xs : Array Nat) : Nat := Id.run do
  let mut bad := 0
  for k in xs do
    if mulBaseFast k != mulBase k then bad := bad + 1
    if (mulBasePt (k % n)).isNone then bad := bad + 1
  return bad

def checkMulAdd (count : Nat) : Nat := Id.run do
  let xs := randoms 0xadd2 (3 * count)
  let g1 : Nat × Nat := (gx, gy)
  let gNeg : Nat × Nat := (gx, p - gy)
  let mut bad := 0
  for u1 in edgeScalars.extract 0 14 do
    for u2 in edgeScalars.extract 0 14 do
      if mulAddFast u1 u2 g1 != mulAdd u1 u2 g1 then bad := bad + 1
      if mulAddFast u1 u2 gNeg != mulAdd u1 u2 gNeg then bad := bad + 1
  for i in [0:count] do
    let qk := xs[3 * i]! % (n - 1) + 1
    match mulBase qk with
    | none => bad := bad + 1
    | some q =>
      let u2 := xs[3 * i + 1]! % n
      -- every fourth case sums to the point at infinity, every fourth has a tiny `u1`
      let u1 := match i % 4 with
        | 0 => (n - u2 * qk % n) % n
        | 1 => xs[3 * i + 2]! % 4
        | _ => xs[3 * i + 2]! % n
      let fast := mulAddFast u1 u2 q
      if fast != mulAdd u1 u2 q then bad := bad + 1
      if i % 4 == 0 && fast.isSome then bad := bad + 1
      if (mulAddPt u1 u2 (Pt.ofXYZ (U256.ofNat q.1) (U256.ofNat q.2) Ff.one)).isNone then bad := bad + 1
  return bad

def checkRecover (sigs : Array Sig) (count : Nat) : Nat := Id.run do
  let mut bad := 0
  for sig in sigs do
    let fast := recoverFast sig.z sig.parity sig.r sig.s
    if fast != recover sig.z sig.parity sig.r sig.s || fast != sig.key || fast.isNone then bad := bad + 1
    -- the other parity, and the high-`s` twin, against the old path
    if recoverFast sig.z (1 - sig.parity) sig.r sig.s != recover sig.z (1 - sig.parity) sig.r sig.s then bad := bad + 1
    if recoverFast sig.z (1 - sig.parity) sig.r (n - sig.s) != sig.key then bad := bad + 1
  let xs := randoms 0x9a2ba9e (3 * count)
  for i in [0:count] do
    let z := xs[3 * i]!
    let r := if i % 16 == 0 then edgeScalars[i / 16 % edgeScalars.size]! else xs[3 * i + 1]! % n
    let s := if i % 16 == 8 then edgeScalars[i / 16 % edgeScalars.size]! else xs[3 * i + 2]! % n
    let v := if i % 32 == 31 then 2 else i % 2
    if recoverFast z v r s != recover z v r s then bad := bad + 1
  return bad

def checkPrecompile (sigs : Array Sig) (count : Nat) : Nat := Id.run do
  let mut bad := 0
  for sig in sigs do
    let input := sigInput sig
    let fast := showResult (Ecrecover.run accept 3000 input)
    if fast != showResult (oldRun 3000 input) || fast.length != 66 then bad := bad + 1
  let xs := randoms 0x9ec0de (4 * count)
  for i in [0:count / 4] do
    let v := if i % 5 == 0 then xs[4 * i + 3]! else 27 + i % 2
    let input := natToBE 32 xs[4 * i]! ++ natToBE 32 v ++ natToBE 32 (xs[4 * i + 1]! % n) ++ natToBE 32 (xs[4 * i + 2]! % n)
    let input := if i % 7 == 0 then input.extract 0 (i % 128) else input
    if showResult (Ecrecover.run accept 3000 input) != showResult (oldRun 3000 input) then bad := bad + 1
  if showResult (Ecrecover.run accept 2999 (sigInput sigs[0]!)) != "failure" then bad := bad + 1
  return bad

/-! ### Timing -/

@[noinline] def runIO {α : Type} (f : Unit → α) : IO α := pure (f ())

def timeIt (label : String) (count : Nat) (run : Unit → Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  let digest ← runIO run
  let stop ← IO.monoNanosNow
  let per := (stop - start) / count
  IO.println s!"{label}: {per} ns/op (check {digest % 1000003})"
  return per

@[noinline] def loopDbl : Nat → Pt → Pt
  | 0, x => x
  | k+1, x => loopDbl k (dbl x)

@[noinline] def loopMadd (q : Aff) : Nat → Pt → Pt
  | 0, x => x
  | k+1, x => loopMadd q k (madd x q false)

@[noinline] def loopPadd (q : Pt) : Nat → Pt → Pt
  | 0, x => x
  | k+1, x => loopPadd q k (padd x q false)

@[noinline] def loopDblDict : Nat → JPoint U256 → JPoint U256
  | 0, x => x
  | k+1, x => loopDblDict k (Curve.double Fe.ops x)

@[noinline] def loopAddDict (q : JPoint U256) : Nat → JPoint U256 → JPoint U256
  | 0, x => x
  | k+1, x => loopAddDict q k (Curve.add Fe.ops x q)

@[noinline] def loopDblNat : Nat → JPoint Nat → JPoint Nat
  | 0, x => x
  | k+1, x => loopDblNat k (Curve.double field x)

@[noinline] def loopAddNat (q : JPoint Nat) : Nat → JPoint Nat → JPoint Nat
  | 0, x => x
  | k+1, x => loopAddNat q k (Curve.add field x q)

@[noinline] def loopMulO (y : U256) : Nat → U256 → U256
  | 0, x => x
  | k+1, x => loopMulO y k (Ff.mulO x y)

@[noinline] def loopFeMul (y : U256) : Nat → U256 → U256
  | 0, x => x
  | k+1, x => loopFeMul y k (Fe.mul x y)

@[noinline] def loopFeSqr : Nat → U256 → U256
  | 0, x => x
  | k+1, x => loopFeSqr k (Fe.sqr x)

def percentile (sorted : Array Nat) (percent : Nat) : Nat :=
  sorted[(sorted.size - 1) * percent / 100]!

/-- Time each call once; print p50, p95 and max. Returns the p50. -/
def spread {α : Type} (label : String) (inputs : Array α) (run : α → Nat) : IO Nat := do
  let mut times : Array Nat := Array.mkEmpty inputs.size
  let mut digest := 0
  for x in inputs do
    let start ← IO.monoNanosNow
    let r ← runIO fun _ => run x
    let stop ← IO.monoNanosNow
    times := times.push (stop - start)
    digest := (digest + r) % 1000003
  let sorted := times.qsort (· < ·)
  IO.println s!"{label}: p50 {percentile sorted 50} ns, p95 {percentile sorted 95} ns, max {percentile sorted 100} ns over {inputs.size} calls (check {digest})"
  return percentile sorted 50

def optNat : Option (Nat × Nat) → Nat
  | some (x, y) => x + y
  | none => 0

def timings (sigs : Array Sig) : IO Unit := do
  let m := sigs.size
  let reps := 20
  let g : Pt := gPt
  let g2 := dbl g
  let gA : Aff := gTable.getD 1 affZero
  let gj : JPoint U256 := ⟨U256.ofNat gx, U256.ofNat gy, Ff.one⟩
  let gj2 := Curve.double Fe.ops gj
  let gn : JPoint Nat := ⟨gx, gy, 1⟩
  let gn2 := Curve.double field gn
  IO.println "--- field and point operations (old Nat | generic limb | fast)"
  let _ ← timeIt "field mul, limb (Fe.mul)" 2000000 fun _ => (loopFeMul (U256.ofNat gy) 2000000 (U256.ofNat gx)).toNat
  let _ ← timeIt "field mul, fast out of line (Ff.mulO)" 2000000 fun _ => (loopMulO (U256.ofNat gy) 2000000 (U256.ofNat gx)).toNat
  let _ ← timeIt "field sqr, limb (Fe.sqr)" 2000000 fun _ => (loopFeSqr 2000000 (U256.ofNat gx)).toNat
  let _ ← timeIt "field sqr, fast in a register loop (Ff.sqrN)" 2000000 fun _ => (Ff.sqrN (U256.ofNat gx) 2000000).toNat
  let _ ← timeIt "point double, Nat" 100000 fun _ => (loopDblNat 100000 gn).x
  let _ ← timeIt "point double, generic limb" 400000 fun _ => (loopDblDict 400000 gj).x.toNat
  let _ ← timeIt "point double, fast" 400000 fun _ => (loopDbl 400000 g).x.toNat
  let _ ← timeIt "point add, Nat" 100000 fun _ => (loopAddNat gn2 100000 gn).x
  let _ ← timeIt "point add, generic limb" 400000 fun _ => (loopAddDict gj2 400000 gj).x.toNat
  let _ ← timeIt "point add, fast Jacobian" 400000 fun _ => (loopPadd g2 400000 g).x.toNat
  let _ ← timeIt "point add, fast mixed" 400000 fun _ => (loopMadd gA 400000 g).x.toNat
  IO.println "--- steps of one recovery, averaged over the valid signatures (old | new)"
  let total := m * reps
  let _ ← timeIt "TIMING square root: old Fp.sqrt? on Nat" m fun _ => Id.run do
    let mut acc := 0
    for sig in sigs do
      acc := acc + (Fp.sqrt? p ((sig.r * sig.r % p * sig.r + 7) % p)).getD 0
    return acc
  let _ ← timeIt "TIMING square root: new liftY on limbs" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + ((liftY (U256.ofNat sig.r) sig.parity).getD U256.zero).l0.toNat
    return acc
  let _ ← timeIt "TIMING scalar inverse: old Euclid on Nat" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + scalarInv sig.r
    return acc
  let _ ← timeIt "TIMING scalar inverse: new binary GCD on limbs, checked" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + scalarInvFast sig.r
    return acc
  let _ ← timeIt "TIMING field inverse: old Euclid on Nat" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + Fp.inv p sig.r
    return acc
  let _ ← timeIt "TIMING field inverse: limb addition chain (Fe.inv)" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + (Fe.inv (U256.ofNat sig.r)).l0.toNat
    return acc
  let _ ← timeIt "TIMING field inverse: new addition chain (Ff.inv)" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + (Ff.inv (U256.ofNat sig.r)).l0.toNat
    return acc
  let _ ← timeIt "TIMING field inverse: binary GCD on limbs (Ff.xgcd, not used)" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + (Ff.xgcd Fe.P (U256.ofNat sig.r)).l0.toNat
    return acc
  let _ ← timeIt "TIMING split and recode both scalars (new only)" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + (plan (sig.z % n) sig.s).len
    return acc
  let _ ← timeIt "TIMING table of Q and of phi(Q), 8 points each (new only)" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        let t := oddTable (Pt.ofXYZ (U256.ofNat sig.r) (U256.ofNat sig.s) Ff.one) 8
        acc := acc + ((t.map lamPt).getD 7 infinity).x0.toNat
    return acc
  let keys := sigs.map fun sig => sig.key.getD (gx, gy)
  let _ ← timeIt "TIMING double multiplication: old Curve.mul2 on Nat" m fun _ => Id.run do
    let mut acc := 0
    for i in [0:m] do
      let sig := sigs[i]!
      let q := keys[i]!
      acc := acc + (Curve.mul2 field sig.z generator sig.s (Curve.ofAffine field q.1 q.2)).x
    return acc
  let _ ← timeIt "TIMING double multiplication: new split, recode, tables and chain" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for i in [0:m] do
        let sig := sigs[i]!
        let q := keys[i]!
        acc := acc + ((mulAddPt (sig.z % n) sig.s (Pt.ofXYZ (U256.ofNat q.1) (U256.ofNat q.2) Ff.one)).getD infinity).x0.toNat
    return acc
  let jn := Curve.mul field 0xdeadbeef generator
  let jf := (mulBasePt 0xdeadbeef).getD infinity
  let _ ← timeIt "TIMING to affine and curve check: old checkedAffine" 2000 fun _ => Id.run do
    let mut acc := 0
    for _ in [0:2000] do
      acc := acc + optNat (checkedAffine jn)
    return acc
  let _ ← timeIt "TIMING to affine and curve check: new checkedAffineFast" 20000 fun _ => Id.run do
    let mut acc := 0
    for _ in [0:20000] do
      acc := acc + optNat (checkedAffineFast jf)
    return acc
  let _ ← timeIt "TIMING address from key (Keccak, unchanged)" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for q in keys do
        acc := acc + (Ecrecover.addressBytes q.1 q.2).size
    return acc
  let _ ← timeIt "TIMING fixed base: old mulBase" m fun _ => Id.run do
    let mut acc := 0
    for sig in sigs do
      acc := acc + optNat (mulBase sig.s)
    return acc
  let _ ← timeIt "TIMING fixed base: new mulBaseFast" total fun _ => Id.run do
    let mut acc := 0
    for _ in [0:reps] do
      for sig in sigs do
        acc := acc + optNat (mulBaseFast sig.s)
    return acc
  IO.println "--- whole calls on valid signatures, each call timed once"
  let old ← spread "TIMING recover: old Secp256k1.recover" sigs fun sig => optNat (recover sig.z sig.parity sig.r sig.s)
  let new ← spread "TIMING recover: new recoverFast" sigs fun sig => optNat (recoverFast sig.z sig.parity sig.r sig.s)
  let new2 ← spread "TIMING recover: new recoverFast, second pass" sigs fun sig => optNat (recoverFast sig.z sig.parity sig.r sig.s)
  let inputs := sigs.map sigInput
  let oldP ← spread "TIMING ECRECOVER precompile: old body" inputs fun input => (showResult (oldRun 3000 input)).length
  let newP ← spread "TIMING ECRECOVER precompile: new body" inputs fun input => (showResult (Ecrecover.run accept 3000 input)).length
  IO.println s!"RESULT recover p50 {old} ns -> {min new new2} ns; ECRECOVER precompile p50 {oldP} ns -> {newP} ns"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--emit-valid", count] =>
    for sig in validSigs (count.toNat?.getD 100) do
      IO.println s!"shanghaiPlus 1 3000 {toHex (sigInput sig)}"
    return 0
  | _ =>
    let count := (args.head?.bind String.toNat?).getD 2000
    let sigs := validSigs count
    let scalars := edgeScalars ++ randoms 0x5ca1a2 count
    let (splitBad, longest) := checkSplit (edgeScalars ++ randoms 0x91f (10 * count))
    let checks : Array (String × Nat) := #[
      ("inlined limb field against the Nat field", checkField 300),
      ("scalarInvFast against scalarInv, candidate never replaced", checkScalarInv scalars),
      ("decomposition and recoding, no fall-back", splitBad),
      ("recoding at most 130 digits", if longest ≤ 130 then 0 else 1),
      ("mulBaseFast against mulBase, fast path taken", checkMulBase scalars),
      ("mulAddFast against mulAdd, fast path taken", checkMulAdd count),
      ("valid signatures made", if sigs.size == count then 0 else 1),
      ("recoverFast against recover and the known key", checkRecover sigs count),
      ("ECRECOVER against its old body", checkPrecompile sigs count)]
    let mut bad := 0
    for (name, failures) in checks do
      IO.println s!"check {name}: {if failures == 0 then "ok" else s!"{failures} FAILURES"}"
      bad := bad + failures
    IO.println s!"RESULT differential: {count} valid signatures, {scalars.size} scalars, longest recoding {longest} digits, {bad} failures"
    if bad != 0 then return 1
    timings (sigs.extract 0 (min count 2000))
    return 0

end EVMCleanroom.SecpPerf

def main (args : List String) : IO UInt32 := EVMCleanroom.SecpPerf.main args
