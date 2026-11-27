import EVMCleanroom.Precompiles.BN254Fast
import EVMCleanroom.Precompiles.BLS12381Msm
import EVMCleanroom.Precompiles.BLS12381Map
import EVMCleanroom.Precompiles.KZGFast

/-!
# `evm-blsops`: the group-operation precompiles on limbs against their definitions

    evm-blsops [SCALE]

For alt_bn128 addition and multiplication (0x06, 0x07), BLS12-381 G1 and G2
addition (0x0b, 0x0d), the two multi-scalar multiplications (0x0c, 0x0e), the two maps to the curve
(0x10, 0x11), the two subgroup checks, the square root in `Fp2`, the cofactor
clearing of `G2` and the KZG helpers (decompression, fixed-base
multiplication), the limb implementation is run beside the `Nat`
definition on deterministic pseudo-random inputs: valid points, the edge cases
(infinity, equal and inverse points, scalars `0, 1, r − 1, r, 2^256 − 1`),
points outside the subgroup, points of small order, and invalid encodings.
Results must be equal byte for byte; any difference makes the exit status 1.
`SCALE` (default 1) multiplies the number of cases.

Then both are timed on the same valid inputs in this one process, and the
spread over inputs of the best of three calls is printed per operation.

This is a test beside the modules, not a proof.
-/

namespace EVMCleanroom.BlsOps

open EVMCleanroom.Precompiles

/-! ### Deterministic pseudo-random values -/

def walk (x : Nat) : Nat :=
  (x * x + 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89) % (2 ^ 521 - 1)

/-- `count` values below `2^521`, a different sequence per seed. -/
def randoms (seed count : Nat) : Array Nat := Id.run do
  let mut x := seed * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95 + 12345
  let mut out : Array Nat := #[]
  for _ in [0:count] do
    x := walk x
    out := out.push x
  return out

def pick {α : Type} (pool : Array α) (index : Nat) (fallback : α) : α :=
  pool.getD (index % (if pool.size == 0 then 1 else pool.size)) fallback

/-- A scalar for item `i` from the random value `v`: edge values and full-width ones. -/
def scalarOf (order v i : Nat) : Nat :=
  match i % 11 with
  | 0 => 0
  | 1 => 1
  | 2 => order - 1
  | 3 => order
  | 4 => 2 ^ 256 - 1
  | 5 => v % 2 ^ 64
  | 6 => order + 1 + v % 2 ^ 32
  | _ => v % 2 ^ 256

/-! ### alt_bn128 -/

namespace Bn

def affine (point : JPoint Nat) : Nat × Nat := (Curve.toAffine BN254.field point).getD (0, 0)
def multiple (k : Nat) (point : Nat × Nat) : Nat × Nat :=
  affine (Curve.mul BN254.field k (Curve.ofAffine BN254.field point.1 point.2))
def bytes (point : Nat × Nat) : ByteArray := natToBE 32 point.1 ++ natToBE 32 point.2

def pool (count : Nat) : Array (Nat × Nat) :=
  (randoms 1 count).map fun k => multiple (k % 2 ^ 256) (1, 2)

def addCases (points : Array (Nat × Nat)) (count : Nat) : Array ByteArray := Id.run do
  let rs := randoms 2 (2 * count)
  let mut out : Array ByteArray := #[]
  for i in [0:count] do
    let v := rs.getD (2 * i) 0
    let a := pick points v (0, 0)
    let b := pick points (rs.getD (2 * i + 1) 0) (0, 0)
    let full := bytes a ++ bytes b
    let input :=
      match i % 14 with
      | 0 => bytes a ++ bytes a
      | 1 => bytes a ++ bytes (a.1, BN254.p - a.2)
      | 2 => bytes a ++ bytes (0, 0)
      | 3 => bytes (0, 0) ++ bytes b
      | 4 => bytes a ++ bytes (b.1, (b.2 + 1) % BN254.p)
      | 5 => bytes (a.1 + BN254.p, a.2) ++ bytes b
      | 6 => bytes a ++ bytes (b.1, b.2 + BN254.p)
      | 7 => natToBE 128 (v * v)
      | 8 => full.extract 0 (v / 2 ^ 64 % 129)
      | 9 => full ++ natToBE 32 v
      | 10 => bytes (0, 0) ++ bytes (0, 0)
      | 11 => bytes (0, 2) ++ bytes b
      | _ => full
    out := out.push input
  return out

def mulCases (points : Array (Nat × Nat)) (count : Nat) : Array ByteArray := Id.run do
  let rs := randoms 3 (2 * count)
  let mut out : Array ByteArray := #[]
  for i in [0:count] do
    let v := rs.getD (2 * i) 0
    let a := pick points (rs.getD (2 * i + 1) 0) (0, 0)
    let k := scalarOf BN254.r v i
    let full := bytes a ++ natToBE 32 k
    let input :=
      match i % 13 with
      | 0 => bytes (0, 0) ++ natToBE 32 k
      | 1 => bytes (a.1, (a.2 + 1) % BN254.p) ++ natToBE 32 k
      | 2 => bytes (a.1 + BN254.p, a.2) ++ natToBE 32 k
      | 3 => full.extract 0 (v / 2 ^ 64 % 97)
      | 4 => full ++ natToBE 32 v
      | _ => full
    out := out.push input
  return out

/-- Valid inputs with full-width scalars, for timing. -/
def mulTiming (points : Array (Nat × Nat)) (count : Nat) : Array ByteArray :=
  (randoms 4 count).mapIdx fun i v => bytes (pick points i (0, 0)) ++ natToBE 32 (v % 2 ^ 256)

def addTiming (points : Array (Nat × Nat)) (count : Nat) : Array ByteArray :=
  (randoms 5 count).mapIdx fun i v => bytes (pick points i (0, 0)) ++ bytes (pick points v (0, 0))

end Bn

/-! ### BLS12-381 -/

namespace Bls

open BLS12381 (p r field field2 g1Generator g2Generator)

def fe (n : Nat) : ByteArray := natToBE 64 n
def bytes1 (point : Nat × Nat) : ByteArray := fe point.1 ++ fe point.2
def bytes2 (point : Fp2 × Fp2) : ByteArray := fe point.1.c0 ++ fe point.1.c1 ++ fe point.2.c0 ++ fe point.2.c1
def zero2 : Fp2 × Fp2 := (Fp2.zero, Fp2.zero)

def affine1 (point : JPoint Nat) : Nat × Nat := (Curve.toAffine field point).getD (0, 0)
def affine2 (point : JPoint Fp2) : Fp2 × Fp2 := (Curve.toAffine field2 point).getD zero2
def jac1 (point : Nat × Nat) : JPoint Nat :=
  if point == (0, 0) then Curve.infinity field else Curve.ofAffine field point.1 point.2
def jac2 (point : Fp2 × Fp2) : JPoint Fp2 :=
  if point == zero2 then Curve.infinity field2 else Curve.ofAffine field2 point.1 point.2
def multiple1 (k : Nat) (point : Nat × Nat) : Nat × Nat := affine1 (Curve.mul field k (jac1 point))
def multiple2 (k : Nat) (point : Fp2 × Fp2) : Fp2 × Fp2 := affine2 (Curve.mul field2 k (jac2 point))
def sum1 (a b : Nat × Nat) : Nat × Nat := affine1 (Curve.add field (jac1 a) (jac1 b))
def sum2 (a b : Fp2 × Fp2) : Fp2 × Fp2 := affine2 (Curve.add field2 (jac2 a) (jac2 b))

/-- The curve point with this `x`, when `x³ + 4` is a square. -/
def lift1 (x : Nat) : Option (Nat × Nat) :=
  (Fp.sqrt? p ((x % p * (x % p) % p * (x % p) + 4) % p)).map fun y => (x % p, y)

def lift2 (x : Fp2) : Option (Fp2 × Fp2) :=
  (BLS12381.sqrt2? (Fp2.add p (Fp2.mul p (Fp2.sqr p x) x) BLS12381.twistB)).map fun y => (x, y)

/-- `count` curve points from pseudo-random `x`: outside the subgroup except with negligible probability. -/
def curvePool1 (seed count : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for v in randoms seed (4 * count + 16) do
    if out.size < count then
      match lift1 v with
      | some point => out := out.push point
      | none => pure ()
  return out

def curvePool2 (seed count : Nat) : Array (Fp2 × Fp2) := Id.run do
  let mut out : Array (Fp2 × Fp2) := #[]
  for v in randoms seed (4 * count + 16) do
    if out.size < count then
      match lift2 ⟨v % p, walk v % p⟩ with
      | some point => out := out.push point
      | none => pure ()
  return out

def groupPool1 (seed count : Nat) : Array (Nat × Nat) :=
  (randoms seed count).map fun k => multiple1 (k % r) g1Generator

def groupPool2 (seed count : Nat) : Array (Fp2 × Fp2) :=
  (randoms seed count).map fun k => multiple2 (k % r) g2Generator

/-- Points of small order: cofactor multiples of curve points, for each small prime factor
    of the cofactor (the power is the exponent of the prime in the cofactor). -/
def torsion1 (points : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let order := BLS12381.Fast.h1 * r
  let mut out : Array (Nat × Nat) := #[]
  for power in [3, 11 ^ 2, 10177 ^ 2, 859267 ^ 2, 52437899 ^ 2] do
    for point in points do
      let t := multiple1 (order / power) point
      if t != (0, 0) then out := out.push t
  return out

def torsion2 (points : Array (Fp2 × Fp2)) : Array (Fp2 × Fp2) := Id.run do
  let order := BLS12381.Fast.h2 * r
  let mut out : Array (Fp2 × Fp2) := #[]
  for power in [13 ^ 2, 23 ^ 2, 2713, 11953, 262069] do
    for point in points do
      let t := multiple2 (order / power) point
      if t != zero2 then out := out.push t
  return out

/-- Subgroup points, curve points, small-order points, sums of a subgroup and a small-order
    point, points of the cofactor group `[r]P`, and cofactor-cleared points `[h]P`. -/
def subgroupCases1 (scale : Nat) : Array (Nat × Nat) := Id.run do
  let inside := groupPool1 11 (40 * scale)
  let outside := curvePool1 12 (200 * scale)
  let small := torsion1 (outside.extract 0 (6 * scale))
  let mut out := inside ++ outside ++ small
  for i in [0:small.size] do
    out := out.push (sum1 (pick inside i (0, 0)) (pick small i (0, 0)))
  for point in outside.extract 0 (10 * scale) do
    out := out.push (multiple1 r point)
    out := out.push (multiple1 BLS12381.Fast.h1 point)
    out := out.push (multiple1 (BLS12381.Fast.h1 * 3) point)
  return out.filter fun point => point != (0, 0)

def subgroupCases2 (scale : Nat) : Array (Fp2 × Fp2) := Id.run do
  let inside := groupPool2 13 (20 * scale)
  let outside := curvePool2 14 (100 * scale)
  let small := torsion2 (outside.extract 0 (4 * scale))
  let mut out := inside ++ outside ++ small
  for i in [0:small.size] do
    out := out.push (sum2 (pick inside i zero2) (pick small i zero2))
  for point in outside.extract 0 (6 * scale) do
    out := out.push (multiple2 r point)
    out := out.push (multiple2 BLS12381.Fast.h2 point)
  return out.filter fun point => point != zero2

def addCases1 (points : Array (Nat × Nat)) (count : Nat) : Array ByteArray := Id.run do
  let rs := randoms 21 (2 * count)
  let mut out : Array ByteArray := #[]
  for i in [0:count] do
    let v := rs.getD (2 * i) 0
    let a := pick points v (0, 0)
    let b := pick points (rs.getD (2 * i + 1) 0) (0, 0)
    let full := bytes1 a ++ bytes1 b
    let input :=
      match i % 16 with
      | 0 => bytes1 a ++ bytes1 a
      | 1 => bytes1 a ++ bytes1 (a.1, p - a.2)
      | 2 => bytes1 a ++ bytes1 (0, 0)
      | 3 => bytes1 (0, 0) ++ bytes1 b
      | 4 => bytes1 a ++ bytes1 (b.1, (b.2 + 1) % p)
      | 5 => bytes1 (a.1 + p, a.2) ++ bytes1 b
      | 6 => fe (a.1 + 2 ^ (384 + v % 128)) ++ fe a.2 ++ bytes1 b
      | 7 => natToBE 256 (v * v * v * v % 2 ^ (8 * 256))
      | 8 => full.extract 0 (v / 2 ^ 64 % 257)
      | 9 => full ++ natToBE 32 v
      | 10 => bytes1 (0, 0) ++ bytes1 (0, 0)
      | 11 => bytes1 a ++ fe b.1 ++ fe (b.2 + p)
      | _ => full
    out := out.push input
  return out

def addCases2 (points : Array (Fp2 × Fp2)) (count : Nat) : Array ByteArray := Id.run do
  let rs := randoms 22 (2 * count)
  let mut out : Array ByteArray := #[]
  for i in [0:count] do
    let v := rs.getD (2 * i) 0
    let a := pick points v zero2
    let b := pick points (rs.getD (2 * i + 1) 0) zero2
    let full := bytes2 a ++ bytes2 b
    let input :=
      match i % 16 with
      | 0 => bytes2 a ++ bytes2 a
      | 1 => bytes2 a ++ bytes2 (a.1, Fp2.neg p a.2)
      | 2 => bytes2 a ++ bytes2 zero2
      | 3 => bytes2 zero2 ++ bytes2 b
      | 4 => bytes2 a ++ bytes2 (b.1, ⟨b.2.c0, (b.2.c1 + 1) % p⟩)
      | 5 => bytes2 (⟨a.1.c0 + p, a.1.c1⟩, a.2) ++ bytes2 b
      | 6 => bytes2 a ++ bytes2 (b.1, ⟨b.2.c0, b.2.c1 + 2 ^ (384 + v % 128)⟩)
      | 7 => natToBE 512 (v * v * v * v * v * v * v * v % 2 ^ (8 * 512))
      | 8 => full.extract 0 (v / 2 ^ 64 % 513)
      | 9 => full ++ natToBE 32 v
      | 10 => bytes2 zero2 ++ bytes2 zero2
      | 11 => bytes2 (⟨a.1.c0, a.1.c1 + p⟩, a.2) ++ bytes2 b
      | _ => full
    out := out.push input
  return out

/-- `count` items over subgroup points; `mode` 0 gives the scalar mix of `scalarOf`,
    1 full-width scalars, 2 scalars below `2^64`. -/
def msmInput1 (points : Array (Nat × Nat)) (seed count mode : Nat) : ByteArray := Id.run do
  let rs := randoms seed (2 * count)
  let mut out := ByteArray.empty
  for i in [0:count] do
    let v := rs.getD (2 * i) 0
    let point := if mode == 0 && i % 17 == 5 then (0, 0) else pick points (rs.getD (2 * i + 1) 0) (0, 0)
    let k := if mode == 0 then scalarOf r v i else if mode == 1 then v % 2 ^ 256 else v % 2 ^ 64
    out := out ++ bytes1 point ++ natToBE 32 k
  return out

def msmInput2 (points : Array (Fp2 × Fp2)) (seed count mode : Nat) : ByteArray := Id.run do
  let rs := randoms seed (2 * count)
  let mut out := ByteArray.empty
  for i in [0:count] do
    let v := rs.getD (2 * i) 0
    let point := if mode == 0 && i % 17 == 5 then zero2 else pick points (rs.getD (2 * i + 1) 0) zero2
    let k := if mode == 0 then scalarOf r v i else if mode == 1 then v % 2 ^ 256 else v % 2 ^ 64
    out := out ++ bytes2 point ++ natToBE 32 k
  return out


/-- Inputs of the map of a field element to `G1`: random, edge and invalid values. -/
def mapCases1 (count : Nat) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[fe 0, fe 1, fe 2, fe (p - 1), fe p, fe (p + 1), fe (2 ^ 384), fe (2 ^ 511),
    fe 1 ++ fe 1, ByteArray.empty, natToBE 63 1, fe 11, fe (p - 11)]
  for v in randoms 41 count do
    out := out.push (fe (v % p))
  return out

def mapCases2 (count : Nat) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[fe 0 ++ fe 0, fe 1 ++ fe 0, fe 0 ++ fe 1, fe (p - 1) ++ fe (p - 1), fe p ++ fe 0,
    fe 0 ++ fe p, fe (2 ^ 384) ++ fe 1, fe 1, fe 1 ++ fe 1 ++ fe 1, ByteArray.empty]
  let rs := randoms 42 (2 * count)
  for i in [0:count] do
    let a := rs.getD (2 * i) 0 % p
    let b := rs.getD (2 * i + 1) 0 % p
    out := out.push (match i % 8 with
      | 0 => fe a ++ fe 0
      | 1 => fe 0 ++ fe b
      | _ => fe a ++ fe b)
  return out

/-- Values for the square root in `Fp2`: random ones (half are squares), squares, real and imaginary ones. -/
def rootCases (count : Nat) : Array Fp2 := Id.run do
  let mut out : Array Fp2 := #[⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨p - 1, 0⟩, ⟨0, p - 1⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨0, 4⟩, ⟨0, 5⟩]
  let rs := randoms 43 (2 * count)
  for i in [0:count] do
    let a : Fp2 := ⟨rs.getD (2 * i) 0 % p, rs.getD (2 * i + 1) 0 % p⟩
    out := out.push (match i % 12 with
      | 0 => Fp2.sqr p a
      | 1 => ⟨a.c0, 0⟩
      | 2 => ⟨0, a.c1⟩
      | 3 => Fp2.sqr p ⟨a.c0, 0⟩
      | _ => a)
  return out

/-- The 48-byte compressed form of `x` with the three flag bits (4: compressed, 2: infinity, 1: larger root). -/
def compressed (x flags : Nat) : ByteArray := natToBE 48 (x % 2 ^ 381 + flags * 2 ^ 381)

def compress1 (point : Nat × Nat) : ByteArray :=
  compressed point.1 (if point.2 > (p - 1) / 2 then 5 else 4)

/-- Compressed encodings: subgroup points with either root, points outside the subgroup, `x` off the
    curve, the infinity encodings, every flag combination, non-canonical `x`. -/
def decompressCases (inside outside : Array (Nat × Nat)) (count : Nat) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[compressed 0 6, compressed 0 7, compressed 0 2, compressed 0 4, compressed 1 6,
    compressed p 4, compressed (p + 3) 4, compressed (2 ^ 381 - 1) 4, compressed 0 5, compressed 0 0]
  let rs := randoms 44 count
  for i in [0:count] do
    let v := rs.getD i 0
    let a := pick inside v (0, 0)
    let b := pick outside v (0, 0)
    out := out.push (match i % 10 with
      | 0 => compressed a.1 ((if a.2 > (p - 1) / 2 then 5 else 4) ^^^ 1)
      | 1 => compress1 b
      | 2 => compressed (v % p) 4
      | 3 => compressed a.1 (v % 8)
      | 4 => compressed (v % p) 5
      | 5 => (compress1 a).extract 0 (v / 2 ^ 64 % 49)
      | _ => compress1 a)
  return out

/-- Replace the point of item `index` (items of `itemBytes` bytes, the point first). -/
def replacePoint (input : ByteArray) (itemBytes index : Nat) (point : ByteArray) : ByteArray :=
  input.extract 0 (itemBytes * index) ++ point ++
    input.extract (itemBytes * index + point.size) input.size

end Bls

/-! ### Comparison and timing -/

def compare (name : String) (inputs : Array ByteArray) (old new : ByteArray → Result) : IO Nat := do
  let mut bad := 0
  let mut valid := 0
  for input in inputs do
    let a := old input
    let b := new input
    if !(a.same b) then
      bad := bad + 1
      if bad ≤ 3 then IO.println s!"DIFF {name}: {input.size} bytes {toHex (input.extract 0 600)}"
    match a with
    | .success _ _ => valid := valid + 1
    | _ => pure ()
  IO.println s!"RESULT blsops {name}: {inputs.size} cases ({valid} valid), {if bad == 0 then "no differences" else s!"{bad} FAILURES"}"
  return bad

/-- One call. Not inlined, so the work happens between the two clock reads. -/
@[noinline] def runOnce (f : ByteArray → Result) (input : ByteArray) : IO Nat :=
  match f input with
  | .success out left => pure (out.size + left)
  | _ => pure 0

def micros (ns : Nat) : String := s!"{ns / 1000}.{ns % 1000 / 100}"

def timeBoth (name : String) (inputs : Array ByteArray) (old new : ByteArray → Result) : IO Unit := do
  let mut olds : Array Nat := #[]
  let mut news : Array Nat := #[]
  for input in inputs do
    let mut bestOld := 0
    let mut bestNew := 0
    for rep in [0:3] do
      let t0 ← IO.monoNanosNow
      let _ ← runOnce old input
      let t1 ← IO.monoNanosNow
      let _ ← runOnce new input
      let t2 ← IO.monoNanosNow
      bestOld := if rep == 0 then t1 - t0 else min bestOld (t1 - t0)
      bestNew := if rep == 0 then t2 - t1 else min bestNew (t2 - t1)
    olds := olds.push bestOld
    news := news.push bestNew
  let so := olds.qsort (· < ·)
  let sn := news.qsort (· < ·)
  let nth (xs : Array Nat) (percent : Nat) : Nat := xs.getD ((xs.size - 1) * percent / 100) 0
  IO.println s!"TIMING {name} ({inputs.size} inputs, us): old p50 {micros (nth so 50)} p95 {micros (nth so 95)} max {micros (nth so 100)}; new p50 {micros (nth sn 50)} p95 {micros (nth sn 95)} max {micros (nth sn 100)}; old/new at p50 {micros (nth so 50 * 1000 / (nth sn 50 + 1))}"

/-! ### The limb inverse -/

@[noinline] def invChain256 (f : U256 → U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => invChain256 f n (f x)

@[noinline] def invChain384 (f : U384 → U384) : Nat → U384 → U384
  | 0, x => x
  | n+1, x => invChain384 f n (f x)

@[noinline] def force (run : Unit → Nat) : IO Nat := pure (run ())

def timeChain (label : String) (count : Nat) (run : Unit → Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  let digest ← force run
  let stop ← IO.monoNanosNow
  IO.println s!"{label}: {(stop - start) / count} ns/op (check {digest % 1000003})"
  return digest

def boolResult (ok : Bool) : Result := if ok then .success ByteArray.empty 1 else .failure

def main (args : List String) : IO UInt32 := do
  let scale := (args.head?.bind String.toNat?).getD 1
  let gas := 1000000000000
  let mut bad := 0
  -- alt_bn128
  let bnPoints := Bn.pool 48
  bad := bad + (← compare "alt_bn128 add (0x06)" (Bn.addCases bnPoints (700 * scale)) (BN254.runAdd gas) (BN254.Fast.runAdd gas))
  bad := bad + (← compare "alt_bn128 mul (0x07)" (Bn.mulCases bnPoints (520 * scale)) (BN254.runMul gas) (BN254.Fast.runMul gas))
  -- BLS12-381 subgroup checks
  let cases1 := Bls.subgroupCases1 scale
  let mut in1 := 0
  let mut bad1 := 0
  for point in cases1 do
    let want := BLS12381.inSubgroup1 point.1 point.2
    let got := BLS12381.Fast.inSubgroup1 (BLS12381.Fast.M.ofNat point.1) (BLS12381.Fast.M.ofNat point.2)
    let decodedOld := (BLS12381.decodeG1 (Bls.bytes1 point) 0 true).isSome
    let decodedNew := (BLS12381.Fast.decodeG1 (Bls.bytes1 point) 0 true).isSome
    if want then in1 := in1 + 1
    if want != got || decodedOld != decodedNew || decodedOld != want then bad1 := bad1 + 1
  IO.println s!"RESULT blsops G1 subgroup check: {cases1.size} points ({in1} in the subgroup, {cases1.size - in1} outside), {if bad1 == 0 then "no differences" else s!"{bad1} FAILURES"}"
  let cases2 := Bls.subgroupCases2 scale
  let mut in2 := 0
  let mut bad2 := 0
  for point in cases2 do
    let want := BLS12381.inSubgroup2 point.1 point.2
    let got := BLS12381.Fast.inSubgroup2 (BLS12381.Fast.toLimbs2 point.1) (BLS12381.Fast.toLimbs2 point.2)
    let decodedOld := (BLS12381.decodeG2 (Bls.bytes2 point) 0 true).isSome
    let decodedNew := (BLS12381.Fast.decodeG2 (Bls.bytes2 point) 0 true).isSome
    if want then in2 := in2 + 1
    if want != got || decodedOld != decodedNew || decodedOld != want then bad2 := bad2 + 1
  IO.println s!"RESULT blsops G2 subgroup check: {cases2.size} points ({in2} in the subgroup, {cases2.size - in2} outside), {if bad2 == 0 then "no differences" else s!"{bad2} FAILURES"}"
  bad := bad + bad1 + bad2
  if in1 < 40 || cases1.size - in1 < 200 || in2 < 20 || cases2.size - in2 < 100 then
    IO.println "RESULT blsops subgroup check: too few points on one side, FAILURES"
    bad := bad + 1
  -- BLS12-381 addition: subgroup points and curve points outside the subgroup
  let group1 := Bls.groupPool1 31 64
  let curve1 := Bls.curvePool1 32 32
  let group2 := Bls.groupPool2 33 32
  let curve2 := Bls.curvePool2 34 16
  bad := bad + (← compare "BLS12-381 G1 add (0x0b)" (Bls.addCases1 (group1 ++ curve1) (800 * scale))
    (BLS12381.runG1Add gas) (BLS12381.Fast.runG1Add gas))
  bad := bad + (← compare "BLS12-381 G2 add (0x0d)" (Bls.addCases2 (group2 ++ curve2) (640 * scale))
    (BLS12381.runG2Add gas) (BLS12381.Fast.runG2Add gas))
  -- BLS12-381 multi-scalar multiplication: counts on both sides of the method switch, wide windows with
  -- short scalars, invalid items
  let mut msm1 : Array ByteArray := #[]
  for count in [1, 1, 1, 2, 3, 5, 8, 16, 33, 79, 80, 81, 128, 129, 300] do
    msm1 := msm1.push (Bls.msmInput1 group1 (100 + msm1.size) count 0)
    msm1 := msm1.push (Bls.msmInput1 group1 (200 + msm1.size) count 1)
  for count in [700, 1600, 3700] do
    msm1 := msm1.push (Bls.msmInput1 group1 (300 + msm1.size) count 2)
  for index in [0, 2, 89] do
    let valid := Bls.msmInput1 group1 (400 + index) 90 1
    msm1 := msm1.push (Bls.replacePoint valid 160 index (Bls.bytes1 (pick curve1 index (0, 0))))
    msm1 := msm1.push (Bls.replacePoint valid 160 index (Bls.bytes1 (5, 6)))
    msm1 := msm1.push (valid.extract 0 (160 * index + 159))
  bad := bad + (← compare "BLS12-381 G1 MSM (0x0c)" msm1 (BLS12381.runG1Msm gas) (BLS12381.Fast.runG1Msm gas))
  let mut msm2 : Array ByteArray := #[]
  for count in [1, 1, 2, 3, 7, 16, 40, 79, 80, 81, 130] do
    msm2 := msm2.push (Bls.msmInput2 group2 (500 + msm2.size) count 0)
    msm2 := msm2.push (Bls.msmInput2 group2 (600 + msm2.size) count 1)
  for count in [300, 700, 1600] do
    msm2 := msm2.push (Bls.msmInput2 group2 (700 + msm2.size) count 2)
  for index in [0, 2, 84] do
    let valid := Bls.msmInput2 group2 (800 + index) 85 1
    msm2 := msm2.push (Bls.replacePoint valid 288 index (Bls.bytes2 (pick curve2 index Bls.zero2)))
    msm2 := msm2.push (valid.extract 0 (288 * index + 287))
  bad := bad + (← compare "BLS12-381 G2 MSM (0x0e)" msm2 (BLS12381.runG2Msm gas) (BLS12381.Fast.runG2Msm gas))
  -- BLS12-381 maps to the curve, the square root in Fp2, the cofactor clearing of G2
  bad := bad + (← compare "BLS12-381 map Fp to G1 (0x10)" (Bls.mapCases1 (600 * scale))
    (BLS12381.runMapG1 gas) (BLS12381.Fast.runMapG1 gas))
  bad := bad + (← compare "BLS12-381 map Fp2 to G2 (0x11)" (Bls.mapCases2 (160 * scale))
    (BLS12381.runMapG2 gas) (BLS12381.Fast.runMapG2 gas))
  let roots := Bls.rootCases (400 * scale)
  let mut squares := 0
  let mut badRoots := 0
  for a in roots do
    let want := BLS12381.sqrt2? a
    let got := BLS12381.Fast.sqrt2? (BLS12381.Fast.toLimbs2 a)
    if want.isSome then squares := squares + 1
    let ok := match want, got with
      | some _, some root => BLS12381.Fast.ofLimbs2 (Q2.sqr BLS12381.Fast.fp root) == a
      | none, none => true
      | _, _ => false
    if !ok then badRoots := badRoots + 1
  IO.println s!"RESULT blsops Fp2 square root: {roots.size} values ({squares} squares), {if badRoots == 0 then "no differences" else s!"{badRoots} FAILURES"}"
  let mut badClear := 0
  let clearPoints := curve2 ++ group2.extract 0 4
  for point in clearPoints do
    let want := Curve.toAffine BLS12381.field2 (Curve.mul BLS12381.field2 BLS12381.cofactor2 (Bls.jac2 point))
    let got := (Curve.toAffineFast BLS12381.Fast.fp2 (BLS12381.Fast.clearCofactor2
      (Curve.ofAffine BLS12381.Fast.fp2 (BLS12381.Fast.toLimbs2 point.1) (BLS12381.Fast.toLimbs2 point.2)))).map
        fun a => (BLS12381.Fast.ofLimbs2 a.1, BLS12381.Fast.ofLimbs2 a.2)
    if want != got then badClear := badClear + 1
  IO.println s!"RESULT blsops G2 cofactor clearing by endomorphisms against the multiplication by h_eff: {clearPoints.size} points, {if badClear == 0 then "no differences" else s!"{badClear} FAILURES"}"
  -- KZG helpers: decompression and the two fixed-base multiplications
  let packed := Bls.decompressCases group1 curve1 (500 * scale)
  let mut validPacked := 0
  let mut badPacked := 0
  for input in packed do
    let want := KZG.decompressG1 input 0
    let got := (KZG.Fast.decompressG1 input 0).map fun inner =>
      inner.map fun a => (BLS12381.Fast.M.toNat a.1, BLS12381.Fast.M.toNat a.2)
    if want.isSome then validPacked := validPacked + 1
    if want != got then badPacked := badPacked + 1
  IO.println s!"RESULT blsops KZG G1 decompression: {packed.size} encodings ({validPacked} valid), {if badPacked == 0 then "no differences" else s!"{badPacked} FAILURES"}"
  let mut badFixed := 0
  let scalars := #[0, 1, 2, 15, 16, BLS12381.r - 1, BLS12381.r, 2 ^ 255, 2 ^ 256 - 1, 2 ^ 256, 2 ^ 300 + 5] ++
    (randoms 45 (60 * scale)).mapIdx fun i v => if i % 2 == 0 then v % BLS12381.r else v % 2 ^ 256
  for k in scalars do
    let want1 := Curve.toAffine BLS12381.field (Curve.mul BLS12381.field k (Bls.jac1 BLS12381.g1Generator))
    let got1 := (Curve.toAffineFast BLS12381.Fast.fp (KZG.Fast.mulG1 k)).map fun a =>
      (BLS12381.Fast.M.toNat a.1, BLS12381.Fast.M.toNat a.2)
    if want1 != got1 then badFixed := badFixed + 1
  for k in scalars.extract 0 (11 + 24 * scale) do
    let want2 := Curve.toAffine BLS12381.field2 (Curve.mul BLS12381.field2 k (Bls.jac2 BLS12381.g2Generator))
    let got2 := (Curve.toAffineFast BLS12381.Fast.fp2 (KZG.Fast.mulG2 k)).map fun a =>
      (BLS12381.Fast.ofLimbs2 a.1, BLS12381.Fast.ofLimbs2 a.2)
    if want2 != got2 then badFixed := badFixed + 1
  IO.println s!"RESULT blsops KZG fixed-base multiplication: {scalars.size} scalars on G1, {min scalars.size (11 + 24 * scale)} on G2, {if badFixed == 0 then "no differences" else s!"{badFixed} FAILURES"}"
  bad := bad + badRoots + badClear + badPacked + badFixed
  if squares < 100 || roots.size - squares < 100 || validPacked < 100 || packed.size - validPacked < 100 then
    IO.println "RESULT blsops: too few cases on one side of a square-root or decompression check, FAILURES"
    bad := bad + 1
  -- The limb inverse against the Euclid of the definition: the unverified candidate must already agree
  let mut badInv := 0
  let bnP := BN254.p
  let blsP := BLS12381.p
  for v in #[1, 2, 3, bnP - 1, bnP - 2, (bnP - 1) / 2, 2 ^ 64, 2 ^ 128 + 1, 2 ^ 253] ++ (randoms 51 (3000 * scale)) do
    let a := v % bnP
    if a != 0 then
      if BN254.baseField.toNat (BN254.baseField.invCandidate (BN254.baseField.ofNat a)) != Fp.inv bnP a then badInv := badInv + 1
      if BN254.baseField.toNat (BN254.Fast.finv (BN254.baseField.ofNat a)) != Fp.inv bnP a then badInv := badInv + 1
  for v in #[1, 2, 3, blsP - 1, blsP - 2, (blsP - 1) / 2, 2 ^ 64, 2 ^ 128 + 1, 2 ^ 380] ++ (randoms 52 (3000 * scale)) do
    let a := v % blsP
    if a != 0 then
      if BLS12381.baseField.toNat (BLS12381.baseField.invCandidate (BLS12381.baseField.ofNat a)) != Fp.inv blsP a then badInv := badInv + 1
      if BLS12381.baseField.toNat (BLS12381.Fast.finv (BLS12381.baseField.ofNat a)) != Fp.inv blsP a then badInv := badInv + 1
  if !(BN254.Fast.finv U256.zero).isZero || !(BLS12381.Fast.finv U384.zero).isZero then badInv := badInv + 1
  IO.println s!"RESULT blsops limb inverse (Kaliski candidate, unverified, against Fp.inv): {2 * (3009 * scale)} values, {if badInv == 0 then "no differences" else s!"{badInv} FAILURES"}"
  bad := bad + badInv
  let chain := 20000
  let x256 := BN254.baseField.ofNat 0x123456789abcdef0123456789abcdef0123456789abcdef
  let x384 := BLS12381.baseField.ofNat (2 ^ 370 + 0x123456789abcdef0123456789abcdef0123456789abcdef)
  let d1 ← timeChain "TIMING alt_bn128 field inverse, Nat Euclid (Mont256.inv)" chain fun _ => (invChain256 BN254.baseField.inv chain x256).toNat
  let d2 ← timeChain "TIMING alt_bn128 field inverse, limbs (Mont256.invFast)" chain fun _ => (invChain256 BN254.baseField.invFast chain x256).toNat
  let d3 ← timeChain "TIMING BLS12-381 field inverse, Nat Euclid (Mont384.inv)" chain fun _ => (invChain384 BLS12381.baseField.inv chain x384).toNat
  let d4 ← timeChain "TIMING BLS12-381 field inverse, limbs (Mont384.invFast)" chain fun _ => (invChain384 BLS12381.baseField.invFast chain x384).toNat
  if d1 != d2 || d3 != d4 then
    IO.println "RESULT blsops limb inverse chains differ, FAILURES"
    bad := bad + 1
  -- Timing, old and new on the same inputs
  timeBoth "alt_bn128 add" (Bn.addTiming bnPoints 60) (BN254.runAdd gas) (BN254.Fast.runAdd gas)
  timeBoth "alt_bn128 mul" (Bn.mulTiming bnPoints 60) (BN254.runMul gas) (BN254.Fast.runMul gas)
  timeBoth "BLS12-381 G1 add" ((Bls.addCases1 group1 64).filter fun input => input.size == 256)
    (BLS12381.runG1Add gas) (BLS12381.Fast.runG1Add gas)
  timeBoth "BLS12-381 G2 add" ((Bls.addCases2 group2 64).filter fun input => input.size == 512)
    (BLS12381.runG2Add gas) (BLS12381.Fast.runG2Add gas)
  timeBoth "BLS12-381 G1 decode with subgroup check" (group1.map Bls.bytes1)
    (fun input => boolResult (BLS12381.decodeG1 input 0 true).isSome)
    (fun input => boolResult (BLS12381.Fast.decodeG1 input 0 true).isSome)
  timeBoth "BLS12-381 G2 decode with subgroup check" (group2.map Bls.bytes2)
    (fun input => boolResult (BLS12381.decodeG2 input 0 true).isSome)
    (fun input => boolResult (BLS12381.Fast.decodeG2 input 0 true).isSome)
  for count in [1, 2, 8, 32, 128] do
    let inputs := (List.range (if count < 8 then 16 else 3)).toArray.map fun i => Bls.msmInput1 group1 (900 + i) count 1
    timeBoth s!"BLS12-381 G1 MSM, {count} items" inputs (BLS12381.runG1Msm gas) (BLS12381.Fast.runG1Msm gas)
  for count in [1, 2, 8, 32, 128] do
    let inputs := (List.range (if count < 8 then 12 else 2)).toArray.map fun i => Bls.msmInput2 group2 (950 + i) count 1
    timeBoth s!"BLS12-381 G2 MSM, {count} items" inputs (BLS12381.runG2Msm gas) (BLS12381.Fast.runG2Msm gas)
  timeBoth "BLS12-381 map Fp to G1" ((Bls.mapCases1 48).extract 13 61) (BLS12381.runMapG1 gas) (BLS12381.Fast.runMapG1 gas)
  timeBoth "BLS12-381 map Fp2 to G2" ((Bls.mapCases2 32).extract 10 42) (BLS12381.runMapG2 gas) (BLS12381.Fast.runMapG2 gas)
  timeBoth "KZG G1 decompression" (group1.map Bls.compress1)
    (fun input => boolResult (KZG.decompressG1 input 0).isSome)
    (fun input => boolResult (KZG.Fast.decompressG1 input 0).isSome)
  let scalarBytes := (randoms 46 24).map fun v => natToBE 32 (v % BLS12381.r)
  timeBoth "KZG [k]G1 for a scalar below r" scalarBytes
    (fun input => boolResult (Curve.isInfinity BLS12381.field
      (Curve.mul BLS12381.field (beNat input 0 32) (Bls.jac1 BLS12381.g1Generator)) == false))
    (fun input => boolResult (!U384.isZero (KZG.Fast.mulG1 (beNat input 0 32)).z))
  timeBoth "KZG [k]G2 for a scalar below r" scalarBytes
    (fun input => boolResult (Curve.isInfinity BLS12381.field2
      (Curve.mul BLS12381.field2 (beNat input 0 32) (Bls.jac2 BLS12381.g2Generator)) == false))
    (fun input => boolResult (!Q2.isZero BLS12381.Fast.fp (KZG.Fast.mulG2 (beNat input 0 32)).z))
  if bad == 0 then
    IO.println "RESULT blsops: all differential checks agree"
    return 0
  else
    IO.println s!"RESULT blsops: {bad} FAILURES"
    return 1

end EVMCleanroom.BlsOps

def main (args : List String) : IO UInt32 := EVMCleanroom.BlsOps.main args
