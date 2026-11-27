import EVMCleanroom.Precompiles.Montgomery

/-!
# Squaring on limbs

`Mont256.sqr` and `Mont384.sqr` square with the general product `mulWide a a`
(16 and 36 `mac` steps). In a square every product of two different limbs
occurs twice, so `sqrWide` computes those products once (6 and 15 `mac`
steps), doubles their sum with a one-bit shift, and adds the squares of the
limbs along the diagonal (4 and 6 `mac` steps): the textbook squaring
(Menezes, van Oorschot, Vanstone, "Handbook of Applied Cryptography",
algorithm 14.16, in its shift-then-add form). `sqrFast` is the Montgomery
square on top of it.

Not proved: `sqrWide a = mulWide a a`. It is tested: the guards below, and
`evm-blsops` compares the two on every combination of extreme limb values
(all zero bits, all one bits, a single top or bottom bit, half-full limbs)
and on a pseudo-random walk. The statement for the proof modules would be
`(sqrWide a).toNat = a.toNat ^ 2`, as for `mulWide_spec`.

Nothing here is constant-time beyond what the limb primitives are.
-/

set_option linter.unusedVariables false

namespace EVMCleanroom.Precompiles

open Limb

/-- The square, 8 limbs: each product of two different limbs once (6 `mac`), the sum
    doubled by a one-bit shift, then the 4 squares of the limbs added along the diagonal. -/
@[inline] def U256.sqrWide (a : U256) : U512 :=
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
  let r := mac a.l0 a.l0 0 0; let t0 := r.2; let h := r.1
  let r := adc t1 h 0; let t1 := r.2; let c := r.1
  let r := mac a.l1 a.l1 t2 c; let t2 := r.2; let h := r.1
  let r := adc t3 h 0; let t3 := r.2; let c := r.1
  let r := mac a.l2 a.l2 t4 c; let t4 := r.2; let h := r.1
  let r := adc t5 h 0; let t5 := r.2; let c := r.1
  let r := mac a.l3 a.l3 t6 c; let t6 := r.2; let h := r.1
  let r := adc t7 h 0; let t7 := r.2; let c := r.1
  ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩

/-- The square, 12 limbs: each product of two different limbs once (15 `mac`), the sum
    doubled by a one-bit shift, then the 6 squares of the limbs added along the diagonal. -/
@[inline] def U384.sqrWide (a : U384) : U768 :=
  let r := mac a.l0 a.l1 0 0; let t1 := r.2; let c := r.1
  let r := mac a.l0 a.l2 0 c; let t2 := r.2; let c := r.1
  let r := mac a.l0 a.l3 0 c; let t3 := r.2; let c := r.1
  let r := mac a.l0 a.l4 0 c; let t4 := r.2; let c := r.1
  let r := mac a.l0 a.l5 0 c; let t5 := r.2; let t6 := r.1
  let r := mac a.l1 a.l2 t3 0; let t3 := r.2; let c := r.1
  let r := mac a.l1 a.l3 t4 c; let t4 := r.2; let c := r.1
  let r := mac a.l1 a.l4 t5 c; let t5 := r.2; let c := r.1
  let r := mac a.l1 a.l5 t6 c; let t6 := r.2; let t7 := r.1
  let r := mac a.l2 a.l3 t5 0; let t5 := r.2; let c := r.1
  let r := mac a.l2 a.l4 t6 c; let t6 := r.2; let c := r.1
  let r := mac a.l2 a.l5 t7 c; let t7 := r.2; let t8 := r.1
  let r := mac a.l3 a.l4 t7 0; let t7 := r.2; let c := r.1
  let r := mac a.l3 a.l5 t8 c; let t8 := r.2; let t9 := r.1
  let r := mac a.l4 a.l5 t9 0; let t9 := r.2; let t10 := r.1
  let t11 := t10 >>> 63
  let t10 := (t10 <<< 1) ||| (t9 >>> 63)
  let t9 := (t9 <<< 1) ||| (t8 >>> 63)
  let t8 := (t8 <<< 1) ||| (t7 >>> 63)
  let t7 := (t7 <<< 1) ||| (t6 >>> 63)
  let t6 := (t6 <<< 1) ||| (t5 >>> 63)
  let t5 := (t5 <<< 1) ||| (t4 >>> 63)
  let t4 := (t4 <<< 1) ||| (t3 >>> 63)
  let t3 := (t3 <<< 1) ||| (t2 >>> 63)
  let t2 := (t2 <<< 1) ||| (t1 >>> 63)
  let t1 := t1 <<< 1
  let r := mac a.l0 a.l0 0 0; let t0 := r.2; let h := r.1
  let r := adc t1 h 0; let t1 := r.2; let c := r.1
  let r := mac a.l1 a.l1 t2 c; let t2 := r.2; let h := r.1
  let r := adc t3 h 0; let t3 := r.2; let c := r.1
  let r := mac a.l2 a.l2 t4 c; let t4 := r.2; let h := r.1
  let r := adc t5 h 0; let t5 := r.2; let c := r.1
  let r := mac a.l3 a.l3 t6 c; let t6 := r.2; let h := r.1
  let r := adc t7 h 0; let t7 := r.2; let c := r.1
  let r := mac a.l4 a.l4 t8 c; let t8 := r.2; let h := r.1
  let r := adc t9 h 0; let t9 := r.2; let c := r.1
  let r := mac a.l5 a.l5 t10 c; let t10 := r.2; let h := r.1
  let r := adc t11 h 0; let t11 := r.2; let c := r.1
  ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩

/-- The Montgomery square through `sqrWide`. -/
@[inline] def Mont256.sqrFast (M : Mont256) (a : U256) : U256 := U256.redc M.n M.n0inv (U256.sqrWide a)

/-- The Montgomery square through `sqrWide`. -/
@[inline] def Mont384.sqrFast (M : Mont384) (a : U384) : U384 := U384.redc M.n M.n0inv (U384.sqrWide a)

private def agrees256 (n : Nat) : Bool :=
  (U256.sqrWide (U256.ofNat n)).toNat == (U256.mulWide (U256.ofNat n) (U256.ofNat n)).toNat &&
    (U256.sqrWide (U256.ofNat n)).toNat == (n % 2 ^ 256) ^ 2
private def agrees384 (n : Nat) : Bool :=
  (U384.sqrWide (U384.ofNat n)).toNat == (U384.mulWide (U384.ofNat n) (U384.ofNat n)).toNat &&
    (U384.sqrWide (U384.ofNat n)).toNat == (n % 2 ^ 384) ^ 2
private def edges (bits : Nat) : List Nat :=
  [0, 1, 2, 3, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 127, 2 ^ 128 - 1, 2 ^ (bits - 1), 2 ^ bits - 1, 2 ^ bits - 2,
   2 ^ bits - 2 ^ 64, 2 ^ bits - 2 ^ (bits - 64) + 1, 2 ^ (bits - 1) + 2 ^ 63,
   0xfedcba9876543210f0e1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdeffedcba9876543210a5a5a5a55a5a5a5a]

#guard (edges 256).all agrees256
#guard (edges 384).all agrees384
#guard (List.range 200).all fun i => agrees256 ((i * i + 7) * (2 ^ 250 - 2 ^ (i % 250) + i)) &&
  agrees384 ((i * i + 7) * (2 ^ 378 - 2 ^ (i % 378) + i))

end EVMCleanroom.Precompiles
