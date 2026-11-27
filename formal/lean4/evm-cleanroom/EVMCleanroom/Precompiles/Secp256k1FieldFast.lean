import EVMCleanroom.Precompiles.Secp256k1Field

/-!
# The secp256k1 base field, written to be inlined into point formulas

A second implementation of the field of `Secp256k1Field.lean` (same
representation: canonical residues modulo `p = 2^256 − 2^32 − 977` in four
64-bit limbs, same folding reduction), with three differences that matter for
speed when a whole point formula is compiled as one function:

* every operation is `@[inline]` and straight-line: carries and borrows are
  `(decide (a < b)).toUInt64` and the final conditional subtraction is a
  limb-wise select under a mask, so no operation ends in a branch that would
  force its four limbs into a heap object. Inside a point formula the
  intermediate field values are then plain machine words;
* squaring has its own product (`sqrWide`): the six cross products once,
  doubled, plus the four squares (10 limb products where the general product
  has 16);
* `mulSmall` multiplies by a small constant in one pass (4 limb products).

Also here: the fixed addition chains for the inverse and the square root on
these operations (the same chains as `Secp256k1.Fe`), and a binary extended
GCD (Stein 1967; the extended form is Algorithm 2.22 of Hankerson, Menezes and
Vanstone, "Guide to Elliptic Curve Cryptography", 2004) on four limbs for an
odd modulus, used for the inverse modulo the group order.

Nothing in this module is proved. It is tested: `evm-fieldperf` compares every
operation with the `Nat` definitions of `Field.lean` on edge values and a
deterministic walk, and the guards at the end do the same at build time on a
few values. Callers do not rely on it for correctness of what they return:
`Secp256k1Fast` checks every returned point against the curve equation in the
`Nat` field, and checks the result of `xgcd` by a multiplication.

Timing: the field operations here have no branch on their operands (the
selects are masks). That is a property of this source, not a claim about the
machine code, and nothing checks it. `xgcd` branches on its operands at every
step, and `sqrtCandidate`/`inv` run a fixed sequence of field operations.
-/

namespace EVMCleanroom.Precompiles.Secp256k1.Ff

open EVMCleanroom.Precompiles.Secp256k1.Fe (P C)

/-- `1` when `a < b`, else `0`, without a branch. -/
@[inline] def lt64 (a b : UInt64) : UInt64 := (decide (a < b)).toUInt64

/-- `(high, low)` of `a * b + c + d` (always below `2^128`), from four 32-bit products. -/
@[inline] def mac (a b c d : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& 0xffffffff
  let a1 := a >>> 32
  let b0 := b &&& 0xffffffff
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& 0xffffffff) + (p10 &&& 0xffffffff)
  let lo0 := (p00 &&& 0xffffffff) ||| (mid <<< 32)
  let hi0 := p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)
  let lo1 := lo0 + c
  let hi1 := hi0 + lt64 lo1 lo0
  let lo2 := lo1 + d
  let hi2 := hi1 + lt64 lo2 lo1
  (hi2, lo2)

/-- `(carry, low)` of `a + b + c`. -/
@[inline] def adc (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a + b
  let t := s + c
  (lt64 s a + lt64 t s, t)

/-- `(borrow, low)` of `a - b - c`. -/
@[inline] def sbb (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a - b
  (lt64 a b + lt64 s c, s - c)

@[inline] def addCarry (a b : U256) : UInt64 × U256 :=
  let r := adc a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := adc a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := adc a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := adc a.l3 b.l3 c; let s3 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3⟩)

@[inline] def subBorrow (a b : U256) : UInt64 × U256 :=
  let r := sbb a.l0 b.l0 0; let s0 := r.2; let c := r.1
  let r := sbb a.l1 b.l1 c; let s1 := r.2; let c := r.1
  let r := sbb a.l2 b.l2 c; let s2 := r.2; let c := r.1
  let r := sbb a.l3 b.l3 c; let s3 := r.2; let c := r.1
  (c, ⟨s0, s1, s2, s3⟩)

/-- `a` where the mask is all ones, `b` where it is zero. -/
@[inline] def select (mask : UInt64) (a b : U256) : U256 :=
  let inv := ~~~mask
  ⟨(a.l0 &&& mask) ||| (b.l0 &&& inv), (a.l1 &&& mask) ||| (b.l1 &&& inv),
   (a.l2 &&& mask) ||| (b.l2 &&& inv), (a.l3 &&& mask) ||| (b.l3 &&& inv)⟩

/-- `a &&& mask` on every limb. -/
@[inline] def masked (mask : UInt64) (a : U256) : U256 :=
  ⟨a.l0 &&& mask, a.l1 &&& mask, a.l2 &&& mask, a.l3 &&& mask⟩

/-- `e · 2^256 + a` (with `e` 0 or 1) reduced once modulo `N`: `N` is subtracted when the value is at least `N`. -/
@[inline] def condSub (N : U256) (e : UInt64) (a : U256) : U256 :=
  let r := subBorrow a N
  select (0 - (e ||| (1 - r.1))) r.2 a

/-- The full product, 8 limbs. -/
@[inline] def mulWide (a b : U256) : U512 :=
  let r := mac a.l0 b.l0 0 0; let t0 := r.2; let c := r.1
  let r := mac a.l0 b.l1 0 c; let t1 := r.2; let c := r.1
  let r := mac a.l0 b.l2 0 c; let t2 := r.2; let c := r.1
  let r := mac a.l0 b.l3 0 c; let t3 := r.2; let t4 := r.1
  let r := mac a.l1 b.l0 t1 0; let t1 := r.2; let c := r.1
  let r := mac a.l1 b.l1 t2 c; let t2 := r.2; let c := r.1
  let r := mac a.l1 b.l2 t3 c; let t3 := r.2; let c := r.1
  let r := mac a.l1 b.l3 t4 c; let t4 := r.2; let t5 := r.1
  let r := mac a.l2 b.l0 t2 0; let t2 := r.2; let c := r.1
  let r := mac a.l2 b.l1 t3 c; let t3 := r.2; let c := r.1
  let r := mac a.l2 b.l2 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l2 b.l3 t5 c; let t5 := r.2; let t6 := r.1
  let r := mac a.l3 b.l0 t3 0; let t3 := r.2; let c := r.1
  let r := mac a.l3 b.l1 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l3 b.l2 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l3 b.l3 t6 c; let t6 := r.2; let t7 := r.1
  ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩

/-- The square, 8 limbs: the six cross products, doubled by a one-bit shift, then the four squares. -/
@[inline] def sqrWide (a : U256) : U512 :=
  let r := mac a.l0 a.l1 0 0; let t1 := r.2; let c := r.1
  let r := mac a.l0 a.l2 0 c; let t2 := r.2; let c := r.1
  let r := mac a.l0 a.l3 0 c; let t3 := r.2; let t4 := r.1
  let r := mac a.l1 a.l2 t3 0; let t3 := r.2; let c := r.1
  let r := mac a.l1 a.l3 t4 c; let t4 := r.2; let t5 := r.1
  let r := mac a.l2 a.l3 t5 0; let t5 := r.2; let t6 := r.1
  let t7 := t6 >>> 63
  let t6 := (t6 <<< 1) ||| (t5 >>> 63)
  let t5 := (t5 <<< 1) ||| (t4 >>> 63)
  let t4 := (t4 <<< 1) ||| (t3 >>> 63)
  let t3 := (t3 <<< 1) ||| (t2 >>> 63)
  let t2 := (t2 <<< 1) ||| (t1 >>> 63)
  let t1 := t1 <<< 1
  let r := mac a.l0 a.l0 0 0; let r0 := r.2; let c := r.1
  let r := adc t1 c 0; let r1 := r.2; let k := r.1
  let r := mac a.l1 a.l1 t2 k; let r2 := r.2; let c := r.1
  let r := adc t3 c 0; let r3 := r.2; let k := r.1
  let r := mac a.l2 a.l2 t4 k; let r4 := r.2; let c := r.1
  let r := adc t5 c 0; let r5 := r.2; let k := r.1
  let r := mac a.l3 a.l3 t6 k; let r6 := r.2; let c := r.1
  let r7 := t7 + c
  ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩

/-- `k · 2^256 + r` reduced modulo `p`: fold `k · C` into the low limbs, fold the possible
    carry once more (the limbs are then small, so this cannot carry again), subtract `p` once. -/
@[inline] def fold (r0 r1 r2 r3 k : UInt64) : U256 :=
  let r := mac k C r0 0; let r0 := r.2; let c := r.1
  let r := adc r1 c 0; let r1 := r.2; let c := r.1
  let r := adc r2 0 c; let r2 := r.2; let c := r.1
  let r := adc r3 0 c; let r3 := r.2; let c := r.1
  let r := adc r0 (c * C) 0; let r0 := r.2; let c := r.1
  let r := adc r1 0 c; let r1 := r.2; let c := r.1
  let r := adc r2 0 c; let r2 := r.2; let c := r.1
  let r3 := r3 + c
  condSub P 0 ⟨r0, r1, r2, r3⟩

/-- Reduce an eight-limb value modulo `p`. -/
@[inline] def reduce (t : U512) : U256 :=
  let r := mac t.l4 C t.l0 0; let r0 := r.2; let c := r.1
  let r := mac t.l5 C t.l1 c; let r1 := r.2; let c := r.1
  let r := mac t.l6 C t.l2 c; let r2 := r.2; let c := r.1
  let r := mac t.l7 C t.l3 c; let r3 := r.2; let k := r.1
  fold r0 r1 r2 r3 k

@[inline] def mul (a b : U256) : U256 := reduce (mulWide a b)
@[inline] def sqr (a : U256) : U256 := reduce (sqrWide a)

@[inline] def add (a b : U256) : U256 :=
  let r := addCarry a b
  condSub P r.1 r.2

@[inline] def sub (a b : U256) : U256 :=
  let r := subBorrow a b
  (addCarry r.2 (masked (0 - r.1) P)).2

@[inline] def neg (a : U256) : U256 := sub U256.zero a

/-- `−a` when the flag is set, `a` otherwise, without a branch. -/
@[inline] def cneg (flag : Bool) (a : U256) : U256 := select (0 - flag.toUInt64) (neg a) a

/-- `a · k` for a small constant `k` (any 64-bit value is accepted). -/
@[inline] def mulSmall (a : U256) (k : UInt64) : U256 :=
  let r := mac a.l0 k 0 0; let r0 := r.2; let c := r.1
  let r := mac a.l1 k 0 c; let r1 := r.2; let c := r.1
  let r := mac a.l2 k 0 c; let r2 := r.2; let c := r.1
  let r := mac a.l3 k 0 c; let r3 := r.2; let c := r.1
  fold r0 r1 r2 r3 c

@[inline] def one : U256 := ⟨1, 0, 0, 0⟩

/-! ### Out-of-line copies, for code that is not a point formula -/

def mulO (a b : U256) : U256 := mul a b
def sqrO (a : U256) : U256 := sqr a

/-- `a^(2^k)`, the four limbs kept in registers across the loop. -/
def sqrLoop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → U256
  | 0, a0, a1, a2, a3 => ⟨a0, a1, a2, a3⟩
  | k+1, a0, a1, a2, a3 =>
    let r := sqr ⟨a0, a1, a2, a3⟩
    sqrLoop k r.l0 r.l1 r.l2 r.l3

def sqrN (a : U256) (k : Nat) : U256 := sqrLoop k a.l0 a.l1 a.l2 a.l3

/-- `a^(2^223 − 1)` together with `a^(2^22 − 1)` and `a^3` (the chain of `Secp256k1.Fe.chain`). -/
def chain (a : U256) : U256 × U256 × U256 :=
  let x2 := mulO (sqrO a) a
  let x3 := mulO (sqrO x2) a
  let x6 := mulO (sqrN x3 3) x3
  let x9 := mulO (sqrN x6 3) x3
  let x11 := mulO (sqrN x9 2) x2
  let x22 := mulO (sqrN x11 11) x11
  let x44 := mulO (sqrN x22 22) x22
  let x88 := mulO (sqrN x44 44) x44
  let x176 := mulO (sqrN x88 88) x88
  let x220 := mulO (sqrN x176 44) x44
  let x223 := mulO (sqrN x220 3) x3
  (x223, x22, x2)

/-- `a^(p − 2)`: the inverse for non-zero `a`, zero for zero. A fixed sequence of field operations. -/
def inv (a : U256) : U256 :=
  let (x223, x22, x2) := chain a
  let t := mulO (sqrN x223 23) x22
  let t := mulO (sqrN t 5) a
  let t := mulO (sqrN t 3) x2
  mulO (sqrN t 2) a

/-- `a^((p + 1)/4)`: a square root of `a` when `a` is a square. A fixed sequence of field operations. -/
def sqrtCandidate (a : U256) : U256 :=
  let (x223, x22, x2) := chain a
  let t := mulO (sqrN x223 23) x22
  let t := mulO (sqrN t 6) x2
  sqrN t 2

def ops : FieldOps U256 where
  zero := U256.zero
  one := one
  add := fun a b => add a b
  sub := fun a b => sub a b
  mul := mulO
  sqr := sqrO
  neg := fun a => neg a
  inv := inv
  isZero := U256.isZero
  eq := U256.beq

/-! ### Binary extended GCD on four limbs -/

/-- `x / 2` modulo an odd `N`, for `x < N`: `x` or `x + N`, whichever is even, shifted right. -/
@[inline] def halfMod (N x : U256) : U256 :=
  let r := addCarry x (masked (0 - (x.l0 &&& 1)) N)
  let s := r.2
  ⟨(s.l0 >>> 1) ||| (s.l1 <<< 63), (s.l1 >>> 1) ||| (s.l2 <<< 63), (s.l2 >>> 1) ||| (s.l3 <<< 63),
   (s.l3 >>> 1) ||| (r.1 <<< 63)⟩

/-- `a − b` modulo `N` for `a, b < N`. -/
@[inline] def subMod (N a b : U256) : U256 :=
  let r := subBorrow a b
  (addCarry r.2 (masked (0 - r.1) N)).2

/-- State: `u`, `v` (the two numbers being reduced) and `a`, `b` with `a·x ≡ u`, `b·x ≡ v (mod N)`
    for the input `x`. Each step halves an even one of `u`, `v`, or replaces the larger of two
    odd ones by half their difference; the coefficient follows. Ends when `u` or `v` is 1.
    Returns zero when the count runs out (then `x` was not invertible). -/
def xgcdLoop (N : U256) : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → U256
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => U256.zero
  | fuel+1, u0, u1, u2, u3, v0, v1, v2, v3, a0, a1, a2, a3, b0, b1, b2, b3 =>
    if u0 == 1 && (u1 ||| u2 ||| u3) == 0 then ⟨a0, a1, a2, a3⟩
    else if v0 == 1 && (v1 ||| v2 ||| v3) == 0 then ⟨b0, b1, b2, b3⟩
    else if (u0 &&& 1) == 0 then
      let a := halfMod N ⟨a0, a1, a2, a3⟩
      xgcdLoop N fuel ((u0 >>> 1) ||| (u1 <<< 63)) ((u1 >>> 1) ||| (u2 <<< 63)) ((u2 >>> 1) ||| (u3 <<< 63))
        (u3 >>> 1) v0 v1 v2 v3 a.l0 a.l1 a.l2 a.l3 b0 b1 b2 b3
    else if (v0 &&& 1) == 0 then
      let b := halfMod N ⟨b0, b1, b2, b3⟩
      xgcdLoop N fuel u0 u1 u2 u3 ((v0 >>> 1) ||| (v1 <<< 63)) ((v1 >>> 1) ||| (v2 <<< 63))
        ((v2 >>> 1) ||| (v3 <<< 63)) (v3 >>> 1) a0 a1 a2 a3 b.l0 b.l1 b.l2 b.l3
    else
      let d := subBorrow ⟨u0, u1, u2, u3⟩ ⟨v0, v1, v2, v3⟩
      if d.1 == 0 then
        let w := d.2
        let a := halfMod N (subMod N ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩)
        xgcdLoop N fuel ((w.l0 >>> 1) ||| (w.l1 <<< 63)) ((w.l1 >>> 1) ||| (w.l2 <<< 63))
          ((w.l2 >>> 1) ||| (w.l3 <<< 63)) (w.l3 >>> 1) v0 v1 v2 v3 a.l0 a.l1 a.l2 a.l3 b0 b1 b2 b3
      else
        let w := (subBorrow ⟨v0, v1, v2, v3⟩ ⟨u0, u1, u2, u3⟩).2
        let b := halfMod N (subMod N ⟨b0, b1, b2, b3⟩ ⟨a0, a1, a2, a3⟩)
        xgcdLoop N fuel u0 u1 u2 u3 ((w.l0 >>> 1) ||| (w.l1 <<< 63)) ((w.l1 >>> 1) ||| (w.l2 <<< 63))
          ((w.l2 >>> 1) ||| (w.l3 <<< 63)) (w.l3 >>> 1) a0 a1 a2 a3 b.l0 b.l1 b.l2 b.l3

/-- A candidate for `x⁻¹` modulo an odd `N` (for `0 < x < N` and `gcd(x, N) = 1`); the caller
    checks it by a multiplication. At most 600 steps: each step removes at least one bit from
    `u` and `v` together, which start with at most 512. Variable-time. -/
def xgcd (N x : U256) : U256 :=
  xgcdLoop N 600 x.l0 x.l1 x.l2 x.l3 N.l0 N.l1 N.l2 N.l3 1 0 0 0 0 0 0 0

/-! ### Guards (tests) against the `Nat` field -/

private def pN : Nat := Fe.pNat
private def vals : List Nat :=
  [0, 1, 2, pN - 1, pN - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 128 - 1, 2 ^ 192, 2 ^ 255, 2 ^ 256 - 1 - 2 ^ 32,
   0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
   0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e,
   0xffffffffffffffff0000000000000000ffffffffffffffff00000000ffffffff]
private def L (x : Nat) : U256 := U256.ofNat (x % pN)

#guard vals.all fun a => vals.all fun b =>
  (mul (L a) (L b)).toNat == a * b % pN && (add (L a) (L b)).toNat == (a + b) % pN
    && (sub (L a) (L b)).toNat == (a % pN + pN - b % pN) % pN
#guard vals.all fun a =>
  (sqr (L a)).toNat == a * a % pN && (neg (L a)).toNat == (pN - a % pN) % pN
    && (cneg true (L a)).toNat == (pN - a % pN) % pN && (cneg false (L a)).toNat == a % pN
    && (mulSmall (L a) 3).toNat == a * 3 % pN && (mulSmall (L a) 8).toNat == a * 8 % pN
    && (mulSmall (L a) 0xffffffffffffffff).toNat == a * (2 ^ 64 - 1) % pN
#guard [1, 2, 3, pN - 1, 2 ^ 200 + 12345].all fun a =>
  (mul (inv (L a)) (L a)).toNat == 1 && (mul (xgcd P (L a)) (L a)).toNat == 1
    && (sqr (sqrtCandidate (sqr (L a)))).toNat == a * a % pN
#guard (inv U256.zero).toNat == 0 && (xgcd P U256.zero).toNat == 0

end EVMCleanroom.Precompiles.Secp256k1.Ff
