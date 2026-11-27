import EVMCleanroom.Precompiles.Montgomery

/-!
# The two secp256k1 fields on limbs

Base field: `p = 2^256 − 2^32 − 977`, so `2^256 ≡ c (mod p)` with
`c = 2^32 + 977`. A 512-bit product `hi · 2^256 + lo` is reduced by folding
`hi · c` into `lo` twice (SEC 2 gives the prime; the folding is the standard
reduction for a modulus of the form `2^k − c`). Values are plain canonical
residues, not in Montgomery form.

Inverse and square root are fixed exponentiations (`a^(p−2)` and
`a^((p+1)/4)`): the exponents consist of a run of 223 one bits, a zero, a run
of 22 one bits and a short tail, so the powers `a^(2^k − 1)` for
`k = 2, 3, 6, 9, 11, 22, 44, 88, 176, 220, 223` are built by repeated squaring
and the tails appended (255 squarings and 15 or 13 multiplications).

Scalar field: the group order `n`, in Montgomery form (`Mont256`).

Nothing here is constant-time.
-/

namespace EVMCleanroom.Precompiles.Secp256k1.Fe

open Limb

def pNat : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

@[inline] def P : U256 := ⟨0xfffffffefffffc2f, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩

/-- `2^256 mod p`. -/
@[inline] def C : UInt64 := 0x1000003D1

/-- Reduce an eight-limb value modulo `p`. -/
@[inline] def reduce (t : U512) : U256 :=
  let r := mac t.l4 C t.l0 0; let r0 := r.2; let c := r.1
  let r := mac t.l5 C t.l1 c; let r1 := r.2; let c := r.1
  let r := mac t.l6 C t.l2 c; let r2 := r.2; let c := r.1
  let r := mac t.l7 C t.l3 c; let r3 := r.2; let k := r.1
  let r := mac k C r0 0; let r0 := r.2; let c := r.1
  let r := adc r1 c 0; let r1 := r.2; let c := r.1
  let r := adc r2 0 c; let r2 := r.2; let c := r.1
  let r := adc r3 0 c; let r3 := r.2; let c := r.1
  -- A carry here stands for `2^256 ≡ c`; the four limbs are then small, so adding `c` cannot carry again.
  let r := adc r0 (c * C) 0; let r0 := r.2; let c := r.1
  let r := adc r1 0 c; let r1 := r.2; let c := r.1
  let r := adc r2 0 c; let r2 := r.2; let c := r.1
  let r := adc r3 0 c; let r3 := r.2
  U256.condSub P 0 ⟨r0, r1, r2, r3⟩

def mul (a b : U256) : U256 := reduce (U256.mulWide a b)
def sqr (a : U256) : U256 := reduce (U256.mulWide a a)
def add (a b : U256) : U256 := U256.addMod P a b
def sub (a b : U256) : U256 := U256.subMod P a b
def neg (a : U256) : U256 := U256.negMod P a

/-- `a^(2^k)`. -/
def sqrN (a : U256) : Nat → U256
  | 0 => a
  | k+1 => sqrN (sqr a) k

/-- `a^(2^223 − 1)` together with `a^(2^22 − 1)` and `a^3`. -/
def chain (a : U256) : U256 × U256 × U256 :=
  let x2 := mul (sqr a) a
  let x3 := mul (sqr x2) a
  let x6 := mul (sqrN x3 3) x3
  let x9 := mul (sqrN x6 3) x3
  let x11 := mul (sqrN x9 2) x2
  let x22 := mul (sqrN x11 11) x11
  let x44 := mul (sqrN x22 22) x22
  let x88 := mul (sqrN x44 44) x44
  let x176 := mul (sqrN x88 88) x88
  let x220 := mul (sqrN x176 44) x44
  let x223 := mul (sqrN x220 3) x3
  (x223, x22, x2)

/-- `a^(p − 2)`: the inverse for non-zero `a`, zero for zero. -/
def inv (a : U256) : U256 :=
  let (x223, x22, x2) := chain a
  let t := mul (sqrN x223 23) x22
  let t := mul (sqrN t 5) a
  let t := mul (sqrN t 3) x2
  mul (sqrN t 2) a

/-- `a^((p + 1)/4)`: a square root of `a` when `a` is a square. -/
def sqrtCandidate (a : U256) : U256 :=
  let (x223, x22, x2) := chain a
  let t := mul (sqrN x223 23) x22
  let t := mul (sqrN t 6) x2
  sqrN t 2

/-- A checked square root: `none` when `a` is not a square. -/
def sqrt? (a : U256) : Option U256 :=
  let root := sqrtCandidate a
  if U256.beq (sqr root) a then some root else none

/-- Limbs of any natural number, reduced modulo `p` first. -/
def ofNat (x : Nat) : U256 := U256.ofNat (x % pNat)
def toNat (a : U256) : Nat := a.toNat
@[inline] def one : U256 := ⟨1, 0, 0, 0⟩

def ops : FieldOps U256 where
  zero := U256.zero
  one := one
  add := add
  sub := sub
  mul := mul
  sqr := sqr
  neg := neg
  inv := inv
  isZero := U256.isZero
  eq := U256.beq

end EVMCleanroom.Precompiles.Secp256k1.Fe

namespace EVMCleanroom.Precompiles.Secp256k1

/-- The scalar field (integers modulo the group order) in Montgomery form. -/
def scalarField : Mont256 where
  n := ⟨0xbfd25e8cd0364141, 0xbaaedce6af48a03b, 0xfffffffffffffffe, 0xffffffffffffffff⟩
  inv := 0x4b0dff665588b13f
  one := ⟨0x402da1732fc9bebf, 0x4551231950b75fc4, 0x1, 0x0⟩
  r2 := ⟨0x896cf21467d7d140, 0x741496c20e7cf878, 0xe697f5e45bcd07c6, 0x9d671cd581c69bc5⟩

end EVMCleanroom.Precompiles.Secp256k1
