import EVMCleanroom.Precompiles.Field

/-! Scratch experiment (not for main): cost of fixed-width limb arithmetic in compiled Lean
    against the `Nat` path. -/

namespace EVMCleanroom.FieldPerf.Exp

open EVMCleanroom.Precompiles

@[inline] def mask32 : UInt64 := 0xffffffff

/-- `(hi, lo)` of `a * b + c + d`. -/
@[inline] def mac (a b c d : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& mask32
  let a1 := a >>> 32
  let b0 := b &&& mask32
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& mask32) + (p10 &&& mask32)
  let lo0 := (p00 &&& mask32) ||| (mid <<< 32)
  let hi0 := p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)
  let lo1 := lo0 + c
  let hi1 := hi0 + (if lo1 < lo0 then 1 else 0)
  let lo2 := lo1 + d
  let hi2 := hi1 + (if lo2 < lo1 then 1 else 0)
  (hi2, lo2)

@[inline] def adc (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a + b
  let c1 : UInt64 := if s < a then 1 else 0
  let t := s + c
  let c2 : UInt64 := if t < s then 1 else 0
  (c1 + c2, t)

@[inline] def sbb (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a - b
  let c1 : UInt64 := if a < b then 1 else 0
  let t := s - c
  let c2 : UInt64 := if s < c then 1 else 0
  (c1 + c2, t)

structure U256 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64

def U256.toNat (a : U256) : Nat :=
  a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192

def U256.ofNat (n : Nat) : U256 :=
  ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64), UInt64.ofNat (n >>> 128), UInt64.ofNat (n >>> 192)⟩

/-- secp256k1: `2^256 ≡ c (mod p)`. -/
@[inline] def secC : UInt64 := 0x1000003D1

/-- `a - p` if `a ≥ p` (given as limbs), else `a`. `p = 2^256 - c`: `a ≥ p` iff `a + c` carries. -/
@[inline] def secCondSub (r0 r1 r2 r3 : UInt64) : U256 :=
  let (c, s0) := adc r0 secC 0
  let (c, s1) := adc r1 0 c
  let (c, s2) := adc r2 0 c
  let (c, s3) := adc r3 0 c
  if c != 0 then ⟨s0, s1, s2, s3⟩ else ⟨r0, r1, r2, r3⟩

def secMul (a b : U256) : U256 :=
  let (c, t0) := mac a.l0 b.l0 0 0
  let (c, t1) := mac a.l0 b.l1 0 c
  let (c, t2) := mac a.l0 b.l2 0 c
  let (t4, t3) := mac a.l0 b.l3 0 c
  let (c, t1) := mac a.l1 b.l0 t1 0
  let (c, t2) := mac a.l1 b.l1 t2 c
  let (c, t3) := mac a.l1 b.l2 t3 c
  let (t5, t4) := mac a.l1 b.l3 t4 c
  let (c, t2) := mac a.l2 b.l0 t2 0
  let (c, t3) := mac a.l2 b.l1 t3 c
  let (c, t4) := mac a.l2 b.l2 t4 c
  let (t6, t5) := mac a.l2 b.l3 t5 c
  let (c, t3) := mac a.l3 b.l0 t3 0
  let (c, t4) := mac a.l3 b.l1 t4 c
  let (c, t5) := mac a.l3 b.l2 t5 c
  let (t7, t6) := mac a.l3 b.l3 t6 c
  -- fold the high half: lo + hi * c
  let (c, r0) := mac t4 secC t0 0
  let (c, r1) := mac t5 secC t1 c
  let (c, r2) := mac t6 secC t2 c
  let (k, r3) := mac t7 secC t3 c
  -- fold the carry limb
  let (c, r0) := mac k secC r0 0
  let (c, r1) := adc r1 0 c
  let (c, r2) := adc r2 0 c
  let (c, r3) := adc r3 0 c
  -- a last carry stands for 2^256 ≡ c; the sum is then tiny, so no further carry
  let (c2, r0) := adc r0 (if c != 0 then secC else 0) 0
  let (c2, r1) := adc r1 0 c2
  let (c2, r2) := adc r2 0 c2
  let (_, r3) := adc r3 0 c2
  secCondSub r0 r1 r2 r3

def secAdd (a b : U256) : U256 :=
  let (c, r0) := adc a.l0 b.l0 0
  let (c, r1) := adc a.l1 b.l1 c
  let (c, r2) := adc a.l2 b.l2 c
  let (c, r3) := adc a.l3 b.l3 c
  if c != 0 then
    let (c2, r0) := adc r0 secC 0
    let (c2, r1) := adc r1 0 c2
    let (c2, r2) := adc r2 0 c2
    let (_, r3) := adc r3 0 c2
    ⟨r0, r1, r2, r3⟩
  else secCondSub r0 r1 r2 r3

/-! Montgomery (CIOS) for the alt_bn128 prime. -/
@[inline] def bn0 : UInt64 := 0x3c208c16d87cfd47
@[inline] def bn1 : UInt64 := 0x97816a916871ca8d
@[inline] def bn2 : UInt64 := 0xb85045b68181585d
@[inline] def bn3 : UInt64 := 0x30644e72e131a029
@[inline] def bnInv : UInt64 := 0x87d20782e4866389

@[inline] def montRow (t0 t1 t2 t3 t4 : UInt64) (a : U256) (bi : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (c, t0) := mac a.l0 bi t0 0
  let (c, t1) := mac a.l1 bi t1 c
  let (c, t2) := mac a.l2 bi t2 c
  let (c, t3) := mac a.l3 bi t3 c
  let (t5, t4) := adc t4 c 0
  let m := t0 * bnInv
  let (c, _) := mac m bn0 t0 0
  let (c, t0) := mac m bn1 t1 c
  let (c, t1) := mac m bn2 t2 c
  let (c, t2) := mac m bn3 t3 c
  let (c, t3) := adc t4 c 0
  (t0, t1, t2, t3, t5 + c)

def bnMul (a b : U256) : U256 :=
  let (t0, t1, t2, t3, t4) := montRow 0 0 0 0 0 a b.l0
  let (t0, t1, t2, t3, t4) := montRow t0 t1 t2 t3 t4 a b.l1
  let (t0, t1, t2, t3, t4) := montRow t0 t1 t2 t3 t4 a b.l2
  let (t0, t1, t2, t3, _) := montRow t0 t1 t2 t3 t4 a b.l3
  let (c, s0) := sbb t0 bn0 0
  let (c, s1) := sbb t1 bn1 c
  let (c, s2) := sbb t2 bn2 c
  let (c, s3) := sbb t3 bn3 c
  if c != 0 then ⟨t0, t1, t2, t3⟩ else ⟨s0, s1, s2, s3⟩

def secP : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def bnP : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def blsP : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

@[noinline] def loopLimb (f : U256 → U256 → U256) (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopLimb f y n (f x y)

@[noinline] def loopSecMul (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopSecMul y n (secMul x y)

@[noinline] def loopSecAdd (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopSecAdd y n (secAdd x y)

@[noinline] def loopBnMul (y : U256) : Nat → U256 → U256
  | 0, x => x
  | n+1, x => loopBnMul y n (bnMul x y)

@[noinline] def loopNatMul (p y : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => loopNatMul p y n (Fp.mul p x y)

@[noinline] def loopNatAdd (p y : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => loopNatAdd p y n (Fp.add p x y)

@[noinline] def loopNatSub (p y : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => loopNatSub p y n (Fp.sub p x y)

@[noinline] def loopNatMulOnly (y : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n+1, x, acc => loopNatMulOnly y n x (acc ^^^ (x * y))

def timeIt (label : String) (count : Nat) (run : Unit → Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let value := run ()
  let digest := value % 1000003
  let stop ← IO.monoNanosNow
  IO.println s!"{label}: {(stop - start) / count} ns/op (check {digest})"

def main (args : List String) : IO UInt32 := do
  let count := (args.head?.bind String.toNat?).getD 2000000
  let x : Nat := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  let y : Nat := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
  let xb := x % bnP
  let yb := y % bnP
  let xl : Nat := x * y % blsP + 2 ^ 370
  let yl : Nat := (x * x * y) % blsP
  -- correctness spot checks
  IO.println s!"secMul agrees: {(secMul (.ofNat x) (.ofNat y)).toNat == Fp.mul secP x y}"
  IO.println s!"secAdd agrees: {(secAdd (.ofNat x) (.ofNat y)).toNat == Fp.add secP x y}"
  IO.println s!"secMul chain agrees: {(loopSecMul (.ofNat y) 1000 (.ofNat x)).toNat == loopNatMul secP y 1000 x}"
  IO.println s!"secAdd chain agrees: {(loopSecAdd (.ofNat y) 1000 (.ofNat x)).toNat == loopNatAdd secP y 1000 x}"
  let rInv := Fp.inv bnP (2 ^ 256 % bnP)
  IO.println s!"bnMul agrees: {(bnMul (.ofNat xb) (.ofNat yb)).toNat == xb * yb % bnP * rInv % bnP}"
  timeIt "nat256 mul+mod (secp)" count fun _ => loopNatMul secP y count x
  timeIt "nat256 mul+mod (bn)" count fun _ => loopNatMul bnP yb count xb
  timeIt "nat381 mul+mod (bls)" count fun _ => loopNatMul blsP yl count xl
  timeIt "nat256 add" count fun _ => loopNatAdd secP y count x
  timeIt "nat256 sub" count fun _ => loopNatSub secP y count x
  timeIt "nat381 add" count fun _ => loopNatAdd blsP yl count xl
  timeIt "nat256 mul only" count fun _ => loopNatMulOnly y count x 0
  timeIt "nat381 mul only" count fun _ => loopNatMulOnly yl count xl 0
  timeIt "limb secp mul" count fun _ => (loopSecMul (.ofNat y) count (.ofNat x)).toNat
  timeIt "limb secp add" count fun _ => (loopSecAdd (.ofNat y) count (.ofNat x)).toNat
  timeIt "limb bn montgomery mul" count fun _ => (loopBnMul (.ofNat yb) count (.ofNat xb)).toNat
  return 0

end EVMCleanroom.FieldPerf.Exp

def main (args : List String) : IO UInt32 := EVMCleanroom.FieldPerf.Exp.main args
