import EVMCleanroom.Precompiles.Secp256k1Field
import EVMCleanroom.Precompiles.BN254Field
import EVMCleanroom.Precompiles.BLS12381Field
import EVMCleanroom.Precompiles.Secp256k1

/-!
# `evm-fieldperf`: the limb fields against the `Nat` definitions, and time per operation

    evm-fieldperf [COUNT]

First an executable differential guard: for each of the four limb fields (secp256k1 base and
scalar field, alt_bn128 base field, BLS12-381 base field) every operation is compared with the
`Nat` definition of `Field.lean` on edge values and a deterministic walk. Any difference makes
the exit status 1. Then time per operation over `COUNT` calls (default 2,000,000), for both
representations. The refinement theorems are in the `…Proofs` modules; this tool is the test
beside them, and the source of the per-operation numbers in `PRECOMPILES.md`.
-/

namespace EVMCleanroom.FieldPerf

open EVMCleanroom.Precompiles

def secP : Nat := Secp256k1.p
def secN : Nat := Secp256k1.n
def bnP : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def blsP : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- Deterministic test values below `p`: edge cases, then a multiplicative walk. -/
def samples (p count : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[0, 1, 2, p - 1, p - 2, (p - 1) / 2, (p + 1) / 2, 2 ^ 64 % p, (2 ^ 64 - 1) % p,
    2 ^ 128 % p, (2 ^ 192 - 1) % p, (2 ^ 255) % p, (2 ^ 256 - 1) % p, 2 ^ 32 % p, 977 % p, (2 ^ 256 - 2 ^ 32) % p]
  let mut x : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95 % p
  for _ in [0:count] do
    x := (x * x + 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89) % p
    out := out.push x
  return out

structure Check where
  name : String
  failures : Nat

def checkField256 (name : String) (p : Nat) (ofNat : Nat → U256) (toNat : U256 → Nat) (O : FieldOps U256) :
    Array Check := Id.run do
  let xs := samples p 300
  let mut add := 0
  let mut sub := 0
  let mut mul := 0
  let mut sqr := 0
  let mut neg := 0
  let mut inv := 0
  let mut rt := 0
  for a in xs do
    let fa := ofNat a
    if toNat fa != a then rt := rt + 1
    if toNat (O.neg fa) != Fp.neg p a then neg := neg + 1
    if toNat (O.sqr fa) != a * a % p then sqr := sqr + 1
    if O.isZero fa != (a == 0) then rt := rt + 1
    for b in xs.extract 0 40 do
      let fb := ofNat b
      if toNat (O.add fa fb) != Fp.add p a b then add := add + 1
      if toNat (O.sub fa fb) != Fp.sub p a b then sub := sub + 1
      if toNat (O.mul fa fb) != Fp.mul p a b then mul := mul + 1
      if O.eq fa fb != (a == b) then rt := rt + 1
  for a in xs.extract 0 60 do
    if toNat (O.inv (ofNat a)) != Fp.inv p a then inv := inv + 1
  return #[⟨name ++ " add", add⟩, ⟨name ++ " sub", sub⟩, ⟨name ++ " mul", mul⟩, ⟨name ++ " sqr", sqr⟩,
    ⟨name ++ " neg", neg⟩, ⟨name ++ " inv", inv⟩, ⟨name ++ " round trip, isZero, eq", rt⟩]

def checkField384 (name : String) (p : Nat) (M : Mont384) : Array Check := Id.run do
  let xs := samples p 300
  let O := M.ops
  let mut add := 0
  let mut sub := 0
  let mut mul := 0
  let mut sqr := 0
  let mut neg := 0
  let mut inv := 0
  let mut rt := 0
  for a in xs do
    let fa := M.ofNat a
    if M.toNat fa != a then rt := rt + 1
    if M.toNat (O.neg fa) != Fp.neg p a then neg := neg + 1
    if M.toNat (O.sqr fa) != a * a % p then sqr := sqr + 1
    if O.isZero fa != (a == 0) then rt := rt + 1
    for b in xs.extract 0 40 do
      let fb := M.ofNat b
      if M.toNat (O.add fa fb) != Fp.add p a b then add := add + 1
      if M.toNat (O.sub fa fb) != Fp.sub p a b then sub := sub + 1
      if M.toNat (O.mul fa fb) != Fp.mul p a b then mul := mul + 1
      if O.eq fa fb != (a == b) then rt := rt + 1
  for a in xs.extract 0 60 do
    if M.toNat (O.inv (M.ofNat a)) != Fp.inv p a then inv := inv + 1
  return #[⟨name ++ " add", add⟩, ⟨name ++ " sub", sub⟩, ⟨name ++ " mul", mul⟩, ⟨name ++ " sqr", sqr⟩,
    ⟨name ++ " neg", neg⟩, ⟨name ++ " inv", inv⟩, ⟨name ++ " round trip, isZero, eq", rt⟩]

/-! Timing loops. -/

@[noinline] def loopSecMul (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopSecMul y n (Secp256k1.Fe.mul x y)

@[noinline] def loopSecSqr : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopSecSqr n (Secp256k1.Fe.sqr x)

@[noinline] def loopSecAdd (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopSecAdd y n (Secp256k1.Fe.add x y)

@[noinline] def loopSecSub (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopSecSub y n (Secp256k1.Fe.sub x y)

@[noinline] def loopBnMul (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopBnMul y n (BN254.baseField.mul x y)

@[noinline] def loopBnAdd (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopBnAdd y n (BN254.baseField.add x y)

@[noinline] def loopBlsMul (y : U384) : Nat → U384 → U384
  | 0, x => x
  | n+1, x => loopBlsMul y n (BLS12381.baseField.mul x y)

@[noinline] def loopBlsAdd (y : U384) : Nat → U384 → U384
  | 0, x => x
  | n+1, x => loopBlsAdd y n (BLS12381.baseField.add x y)

@[noinline] def loopNatMul (p y : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => loopNatMul p y n (Fp.mul p x y)

@[noinline] def loopNatAdd (p y : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => loopNatAdd p y n (Fp.add p x y)

/-- The generic curve code over the limb field. -/
@[noinline] def loopDoubleDict : Nat → JPoint U256 → JPoint U256
  | 0, x => x
  | n+1, x => loopDoubleDict n (Curve.double Secp256k1.Fe.ops x)

@[noinline] def loopAddDict (q : JPoint U256) : Nat → JPoint U256 → JPoint U256
  | 0, x => x
  | n+1, x => loopAddDict q n (Curve.add Secp256k1.Fe.ops x q)

@[noinline] def loopDoubleNat : Nat → JPoint Nat → JPoint Nat
  | 0, x => x
  | n+1, x => loopDoubleNat n (Curve.double Secp256k1.field x)

@[noinline] def loopAddNat (q : JPoint Nat) : Nat → JPoint Nat → JPoint Nat
  | 0, x => x
  | n+1, x => loopAddNat q n (Curve.add Secp256k1.field x q)

@[noinline] def force (run : Unit → Nat) : IO Nat := pure (run () % 1000003)

def timeIt (label : String) (count : Nat) (run : Unit → Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let digest ← force run
  let stop ← IO.monoNanosNow
  IO.println s!"{label}: {(stop - start) / count} ns/op (check {digest})"

def main (args : List String) : IO UInt32 := do
  let count := (args.head?.bind String.toNat?).getD 2000000
  let checks := checkField256 "secp256k1 p" secP Secp256k1.Fe.ofNat Secp256k1.Fe.toNat Secp256k1.Fe.ops
    ++ checkField256 "secp256k1 n" secN Secp256k1.scalarField.ofNat Secp256k1.scalarField.toNat Secp256k1.scalarField.ops
    ++ checkField256 "alt_bn128 p" bnP BN254.baseField.ofNat BN254.baseField.toNat BN254.baseField.ops
    ++ checkField384 "bls12-381 p" blsP BLS12381.baseField
  let mut bad := 0
  for c in checks do
    IO.println s!"check {c.name}: {if c.failures == 0 then "ok" else s!"{c.failures} FAILURES"}"
    bad := bad + c.failures
  -- square roots on secp256k1
  let mut rootBad := 0
  for a in samples secP 100 do
    let expect := Fp.sqrt? secP a
    let got := (Secp256k1.Fe.sqrt? (Secp256k1.Fe.ofNat a)).map Secp256k1.Fe.toNat
    if expect != got then rootBad := rootBad + 1
  IO.println s!"check secp256k1 sqrt: {if rootBad == 0 then "ok" else s!"{rootBad} FAILURES"}"
  let x : Nat := Secp256k1.gx
  let y : Nat := Secp256k1.gy
  let xb := x % bnP
  let yb := y % bnP
  let xl : Nat := x * y % blsP + 2 ^ 370
  let yl : Nat := (x * x * y) % blsP
  timeIt "nat secp mul" count fun _ => loopNatMul secP y count x
  timeIt "nat bls mul" count fun _ => loopNatMul blsP yl count xl
  timeIt "nat secp add" count fun _ => loopNatAdd secP y count x
  timeIt "limb secp mul" count fun _ => (loopSecMul (.ofNat y) count (.ofNat x)).toNat
  timeIt "limb secp sqr" count fun _ => (loopSecSqr count (.ofNat x)).toNat
  timeIt "limb secp add" count fun _ => (loopSecAdd (.ofNat y) count (.ofNat x)).toNat
  timeIt "limb secp sub" count fun _ => (loopSecSub (.ofNat y) count (.ofNat x)).toNat
  timeIt "limb bn mul" count fun _ => (loopBnMul (.ofNat yb) count (.ofNat xb)).toNat
  timeIt "limb bn add" count fun _ => (loopBnAdd (.ofNat yb) count (.ofNat xb)).toNat
  timeIt "limb bls mul" count fun _ => (loopBlsMul (.ofNat yl) count (.ofNat xl)).toNat
  timeIt "limb bls add" count fun _ => (loopBlsAdd (.ofNat yl) count (.ofNat xl)).toNat
  let small := count / 20
  let g : JPoint U256 := ⟨.ofNat x, .ofNat y, Secp256k1.Fe.one⟩
  let g2 := Curve.double Secp256k1.Fe.ops g
  let gn : JPoint Nat := ⟨x, y, 1⟩
  let gn2 := Curve.double Secp256k1.field gn
  timeIt "nat secp point double" small fun _ => (loopDoubleNat small gn).x
  timeIt "nat secp point add" small fun _ => (loopAddNat gn2 small gn).x
  timeIt "limb secp point double" small fun _ => (loopDoubleDict small g).x.toNat
  timeIt "limb secp point add" small fun _ => (loopAddDict g2 small g).x.toNat
  timeIt "limb secp inverse" (small / 100) fun _ => Id.run do
    let mut acc := U256.ofNat x
    for _ in [0:small / 100] do acc := Secp256k1.Fe.inv acc
    return acc.toNat
  timeIt "limb secp scalar inverse (Euclid on Nat)" (small / 100) fun _ => Id.run do
    let mut acc := U256.ofNat x
    for _ in [0:small / 100] do acc := Secp256k1.scalarField.inv acc
    return acc.toNat
  timeIt "nat secp inverse (Euclid)" (small / 100) fun _ => Id.run do
    let mut acc := x
    for _ in [0:small / 100] do acc := Fp.inv secP acc
    return acc
  timeIt "nat bls inverse (Euclid)" (small / 100) fun _ => Id.run do
    let mut acc := xl
    for _ in [0:small / 100] do acc := Fp.inv blsP acc
    return acc
  timeIt "limb bls inverse (Euclid on Nat)" (small / 100) fun _ => Id.run do
    let mut acc := U384.ofNat xl
    for _ in [0:small / 100] do acc := BLS12381.baseField.inv acc
    return acc.toNat
  return (if bad + rootBad == 0 then 0 else 1)

end EVMCleanroom.FieldPerf

def main (args : List String) : IO UInt32 := EVMCleanroom.FieldPerf.main args
