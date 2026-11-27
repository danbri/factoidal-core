import EVMCleanroom.Precompiles.Limb256B
import EVMCleanroom.Precompiles.Limb384Proofs

/-!
# Montgomery reduction on four and six limbs

`U256.redc N n0inv t` and `U384.redc N n0inv t` (Montgomery, "Modular
multiplication without trial division", Mathematics of Computation 44, 1985)
are proved against the natural numbers: for a modulus `N` with the `n0inv`
property (`n0inv · N ≡ −1 (mod 2^64)`) and an input `t < N · R`, the result is
below `N` and, times `R`, congruent to `t` modulo `N` (`R = 2^256` or `2^384`).

Structure: `redc_row` is one row (it adds `m · N` to a window of limbs, clears
the low limb and passes a carry of at most 1 up); `redc_rows` chains the rows
of the routine and exposes the final conditional subtraction; `redc_spec`
closes with `condSub_spec`. The rows use only the equations of `mac` and `adc`
(`mac_spec`, `adc_spec`); the arithmetic is in `MontgomeryMath.lean`.

Proved for all inputs satisfying the stated hypotheses. Nothing is said about
timing; the final subtraction branches on data.
-/

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

namespace EVMCleanroom.Precompiles

open Limb LimbB

private theorem zero_toNat' : (0 : UInt64).toNat = 0 := rfl

variable [LimbB.MacOK]

/-- Kind: functional correctness (one row of Montgomery reduction on 4 limbs).
    Says: given the equations of the row's `mac` steps and its final `adc`, with the multiplier
    `m = a0 * inv` (wrapping) and `inv · N₀ ≡ −1 (mod 2^64)`: the window of 5 limbs plus the
    carry coming in plus `m · N` equals `2^64` times the next window, and the carry going out
    is at most 1 when the carry coming in is.
    Does not say: anything about a row whose equations do not hold; `redc_rows` supplies them. -/
theorem U256.redc_row (N : U256) (inv a0 a1 a2 a3 a4 e : UInt64) (r0 r1 r2 r3 r4 : UInt64 × UInt64)
    (hinv : (inv.toNat * N.l0.toNat + 1) % 2 ^ 64 = 0)
    (h0 : r0.1.toNat * 2 ^ 64 + r0.2.toNat = (a0 * inv).toNat * N.l0.toNat + a0.toNat + (0 : UInt64).toNat)
    (h1 : r1.1.toNat * 2 ^ 64 + r1.2.toNat = (a0 * inv).toNat * N.l1.toNat + a1.toNat + r0.1.toNat)
    (h2 : r2.1.toNat * 2 ^ 64 + r2.2.toNat = (a0 * inv).toNat * N.l2.toNat + a2.toNat + r1.1.toNat)
    (h3 : r3.1.toNat * 2 ^ 64 + r3.2.toNat = (a0 * inv).toNat * N.l3.toNat + a3.toNat + r2.1.toNat)
    (h4 : r4.1.toNat * 2 ^ 64 + r4.2.toNat = a4.toNat + r3.1.toNat + e.toNat)
    (he : e.toNat ≤ 1) :
    r4.1.toNat ≤ 1 ∧
    a0.toNat + a1.toNat * 2 ^ 64 + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192 + a4.toNat * 2 ^ 256 + e.toNat * 2 ^ 256 + (a0 * inv).toNat * N.toNat =
      (r1.2.toNat + r2.2.toNat * 2 ^ 64 + r3.2.toNat * 2 ^ 128 + r4.2.toNat * 2 ^ 192 + r4.1.toNat * 2 ^ 256) * 2 ^ 64 := by
  rw [zero_toNat', Nat.add_zero] at h0
  exact MontMath.redc_row4 inv.toNat N.l0.toNat N.l1.toNat N.l2.toNat N.l3.toNat a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat e.toNat
    (a0 * inv).toNat r0.1.toNat r1.1.toNat r2.1.toNat r3.1.toNat r0.2.toNat r1.2.toNat r2.2.toNat r3.2.toNat r4.2.toNat r4.1.toNat
    hinv (UInt64.toNat_mul a0 inv) h0 h1 h2 h3 h4
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) he

/-- Kind: functional correctness (the 4 rows of Montgomery reduction).
    Says: for a modulus with the `n0inv` property, `redc N inv t` is the conditional subtraction
    `condSub N e q` of a carry `e` and 4 limbs `q` such that `t + M · N = (e · 2^256 + q) · 2^256`
    for some `M < 2^256`.
    Does not say: that the result is below `N`; that needs `t < N · 2^256` (`redc_spec`). -/
theorem U256.redc_rows (N : U256) (inv : UInt64) (t : U512)
    (hinv : (inv.toNat * (N.toNat % 2 ^ 64) + 1) % 2 ^ 64 = 0) :
    ∃ (e : UInt64) (q : U256) (M : Nat), U256.redc N inv t = U256.condSub N e q ∧ M < 2 ^ 256 ∧
      t.toNat + M * N.toNat = (e.toNat * 2 ^ 256 + q.toNat) * 2 ^ 256 := by
  rw [U256.toNat_mod N] at hinv
  have he0 : (0 : UInt64).toNat ≤ 1 := Nat.le_trans (Nat.le_of_eq zero_toNat') (Nat.zero_le 1)
  simp only [U256.redc]
  have h00 := mac_spec (t.l0 * inv) N.l0 t.l0 0
  generalize mac (t.l0 * inv) N.l0 t.l0 0 = r00 at h00 ⊢
  have h01 := mac_spec (t.l0 * inv) N.l1 t.l1 r00.1
  generalize mac (t.l0 * inv) N.l1 t.l1 r00.1 = r01 at h01 ⊢
  have h02 := mac_spec (t.l0 * inv) N.l2 t.l2 r01.1
  generalize mac (t.l0 * inv) N.l2 t.l2 r01.1 = r02 at h02 ⊢
  have h03 := mac_spec (t.l0 * inv) N.l3 t.l3 r02.1
  generalize mac (t.l0 * inv) N.l3 t.l3 r02.1 = r03 at h03 ⊢
  have h04 := adc_spec t.l4 r03.1 0
  generalize adc t.l4 r03.1 0 = r04 at h04 ⊢
  obtain ⟨he1, E0⟩ := U256.redc_row N inv t.l0 t.l1 t.l2 t.l3 t.l4 0 r00 r01 r02 r03 r04
    hinv h00 h01 h02 h03 h04 he0
  have h10 := mac_spec (r01.2 * inv) N.l0 r01.2 0
  generalize mac (r01.2 * inv) N.l0 r01.2 0 = r10 at h10 ⊢
  have h11 := mac_spec (r01.2 * inv) N.l1 r02.2 r10.1
  generalize mac (r01.2 * inv) N.l1 r02.2 r10.1 = r11 at h11 ⊢
  have h12 := mac_spec (r01.2 * inv) N.l2 r03.2 r11.1
  generalize mac (r01.2 * inv) N.l2 r03.2 r11.1 = r12 at h12 ⊢
  have h13 := mac_spec (r01.2 * inv) N.l3 r04.2 r12.1
  generalize mac (r01.2 * inv) N.l3 r04.2 r12.1 = r13 at h13 ⊢
  have h14 := adc_spec t.l5 r13.1 r04.1
  generalize adc t.l5 r13.1 r04.1 = r14 at h14 ⊢
  obtain ⟨he2, E1⟩ := U256.redc_row N inv r01.2 r02.2 r03.2 r04.2 t.l5 r04.1 r10 r11 r12 r13 r14
    hinv h10 h11 h12 h13 h14 he1
  have h20 := mac_spec (r11.2 * inv) N.l0 r11.2 0
  generalize mac (r11.2 * inv) N.l0 r11.2 0 = r20 at h20 ⊢
  have h21 := mac_spec (r11.2 * inv) N.l1 r12.2 r20.1
  generalize mac (r11.2 * inv) N.l1 r12.2 r20.1 = r21 at h21 ⊢
  have h22 := mac_spec (r11.2 * inv) N.l2 r13.2 r21.1
  generalize mac (r11.2 * inv) N.l2 r13.2 r21.1 = r22 at h22 ⊢
  have h23 := mac_spec (r11.2 * inv) N.l3 r14.2 r22.1
  generalize mac (r11.2 * inv) N.l3 r14.2 r22.1 = r23 at h23 ⊢
  have h24 := adc_spec t.l6 r23.1 r14.1
  generalize adc t.l6 r23.1 r14.1 = r24 at h24 ⊢
  obtain ⟨he3, E2⟩ := U256.redc_row N inv r11.2 r12.2 r13.2 r14.2 t.l6 r14.1 r20 r21 r22 r23 r24
    hinv h20 h21 h22 h23 h24 he2
  have h30 := mac_spec (r21.2 * inv) N.l0 r21.2 0
  generalize mac (r21.2 * inv) N.l0 r21.2 0 = r30 at h30 ⊢
  have h31 := mac_spec (r21.2 * inv) N.l1 r22.2 r30.1
  generalize mac (r21.2 * inv) N.l1 r22.2 r30.1 = r31 at h31 ⊢
  have h32 := mac_spec (r21.2 * inv) N.l2 r23.2 r31.1
  generalize mac (r21.2 * inv) N.l2 r23.2 r31.1 = r32 at h32 ⊢
  have h33 := mac_spec (r21.2 * inv) N.l3 r24.2 r32.1
  generalize mac (r21.2 * inv) N.l3 r24.2 r32.1 = r33 at h33 ⊢
  have h34 := adc_spec t.l7 r33.1 r24.1
  generalize adc t.l7 r33.1 r24.1 = r34 at h34 ⊢
  obtain ⟨he4, E3⟩ := U256.redc_row N inv r21.2 r22.2 r23.2 r24.2 t.l7 r24.1 r30 r31 r32 r33 r34
    hinv h30 h31 h32 h33 h34 he3
  have C := MontMath.redc_chain4 E0 E1 E2 E3 zero_toNat'
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  exact ⟨r34.1, ⟨r31.2, r32.2, r33.2, r34.2⟩, _, rfl, C.1, C.2⟩

/-- Kind: functional correctness (Montgomery reduction on 4 limbs).
    Says: for a modulus `N` with `n0inv · N ≡ −1 (mod 2^64)` and an input `t < N · 2^256`, the
    result of `redc` is below `N` and, times `2^256`, congruent to `t` modulo `N`.
    Does not say: anything for `t ≥ N · 2^256`, that `N` is prime, or anything about timing. -/
theorem U256.redc_spec (N : U256) (inv : UInt64) (t : U512)
    (hinv : (inv.toNat * (N.toNat % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    (ht : t.toNat < N.toNat * 2 ^ 256) :
    (U256.redc N inv t).toNat < N.toNat ∧
      (U256.redc N inv t).toNat * 2 ^ 256 % N.toNat = t.toNat % N.toNat := by
  obtain ⟨e, q, M, hEq, hM, hC⟩ := U256.redc_rows N inv t hinv
  have hq := MontMath.redc_lt_two N.toNat (2 ^ 256) t.toNat M (e.toNat * 2 ^ 256 + q.toNat) hC ht hM
  obtain ⟨hval, hlt⟩ := U256.condSub_spec N e q hq
  rw [hEq]
  refine ⟨hlt, ?_⟩
  rw [hval]
  exact MontMath.redc_mod N.toNat (2 ^ 256) t.toNat M (e.toNat * 2 ^ 256 + q.toNat) hC

/-- Kind: functional correctness (one row of Montgomery reduction on 6 limbs).
    Says: given the equations of the row's `mac` steps and its final `adc`, with the multiplier
    `m = a0 * inv` (wrapping) and `inv · N₀ ≡ −1 (mod 2^64)`: the window of 7 limbs plus the
    carry coming in plus `m · N` equals `2^64` times the next window, and the carry going out
    is at most 1 when the carry coming in is.
    Does not say: anything about a row whose equations do not hold; `redc_rows` supplies them. -/
theorem U384.redc_row (N : U384) (inv a0 a1 a2 a3 a4 a5 a6 e : UInt64) (r0 r1 r2 r3 r4 r5 r6 : UInt64 × UInt64)
    (hinv : (inv.toNat * N.l0.toNat + 1) % 2 ^ 64 = 0)
    (h0 : r0.1.toNat * 2 ^ 64 + r0.2.toNat = (a0 * inv).toNat * N.l0.toNat + a0.toNat + (0 : UInt64).toNat)
    (h1 : r1.1.toNat * 2 ^ 64 + r1.2.toNat = (a0 * inv).toNat * N.l1.toNat + a1.toNat + r0.1.toNat)
    (h2 : r2.1.toNat * 2 ^ 64 + r2.2.toNat = (a0 * inv).toNat * N.l2.toNat + a2.toNat + r1.1.toNat)
    (h3 : r3.1.toNat * 2 ^ 64 + r3.2.toNat = (a0 * inv).toNat * N.l3.toNat + a3.toNat + r2.1.toNat)
    (h4 : r4.1.toNat * 2 ^ 64 + r4.2.toNat = (a0 * inv).toNat * N.l4.toNat + a4.toNat + r3.1.toNat)
    (h5 : r5.1.toNat * 2 ^ 64 + r5.2.toNat = (a0 * inv).toNat * N.l5.toNat + a5.toNat + r4.1.toNat)
    (h6 : r6.1.toNat * 2 ^ 64 + r6.2.toNat = a6.toNat + r5.1.toNat + e.toNat)
    (he : e.toNat ≤ 1) :
    r6.1.toNat ≤ 1 ∧
    a0.toNat + a1.toNat * 2 ^ 64 + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192 + a4.toNat * 2 ^ 256 + a5.toNat * 2 ^ 320 + a6.toNat * 2 ^ 384 + e.toNat * 2 ^ 384 + (a0 * inv).toNat * N.toNat =
      (r1.2.toNat + r2.2.toNat * 2 ^ 64 + r3.2.toNat * 2 ^ 128 + r4.2.toNat * 2 ^ 192 + r5.2.toNat * 2 ^ 256 + r6.2.toNat * 2 ^ 320 + r6.1.toNat * 2 ^ 384) * 2 ^ 64 := by
  rw [zero_toNat', Nat.add_zero] at h0
  exact MontMath.redc_row6 inv.toNat N.l0.toNat N.l1.toNat N.l2.toNat N.l3.toNat N.l4.toNat N.l5.toNat a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat a5.toNat a6.toNat e.toNat
    (a0 * inv).toNat r0.1.toNat r1.1.toNat r2.1.toNat r3.1.toNat r4.1.toNat r5.1.toNat r0.2.toNat r1.2.toNat r2.2.toNat r3.2.toNat r4.2.toNat r5.2.toNat r6.2.toNat r6.1.toNat
    hinv (UInt64.toNat_mul a0 inv) h0 h1 h2 h3 h4 h5 h6
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) he

/-- Kind: functional correctness (the 6 rows of Montgomery reduction).
    Says: for a modulus with the `n0inv` property, `redc N inv t` is the conditional subtraction
    `condSub N e q` of a carry `e` and 6 limbs `q` such that `t + M · N = (e · 2^384 + q) · 2^384`
    for some `M < 2^384`.
    Does not say: that the result is below `N`; that needs `t < N · 2^384` (`redc_spec`). -/
theorem U384.redc_rows (N : U384) (inv : UInt64) (t : U768)
    (hinv : (inv.toNat * (N.toNat % 2 ^ 64) + 1) % 2 ^ 64 = 0) :
    ∃ (e : UInt64) (q : U384) (M : Nat), U384.redc N inv t = U384.condSub N e q ∧ M < 2 ^ 384 ∧
      t.toNat + M * N.toNat = (e.toNat * 2 ^ 384 + q.toNat) * 2 ^ 384 := by
  rw [U384.toNat_mod N] at hinv
  have he0 : (0 : UInt64).toNat ≤ 1 := Nat.le_trans (Nat.le_of_eq zero_toNat') (Nat.zero_le 1)
  simp only [U384.redc]
  have h00 := mac_spec (t.l0 * inv) N.l0 t.l0 0
  generalize mac (t.l0 * inv) N.l0 t.l0 0 = r00 at h00 ⊢
  have h01 := mac_spec (t.l0 * inv) N.l1 t.l1 r00.1
  generalize mac (t.l0 * inv) N.l1 t.l1 r00.1 = r01 at h01 ⊢
  have h02 := mac_spec (t.l0 * inv) N.l2 t.l2 r01.1
  generalize mac (t.l0 * inv) N.l2 t.l2 r01.1 = r02 at h02 ⊢
  have h03 := mac_spec (t.l0 * inv) N.l3 t.l3 r02.1
  generalize mac (t.l0 * inv) N.l3 t.l3 r02.1 = r03 at h03 ⊢
  have h04 := mac_spec (t.l0 * inv) N.l4 t.l4 r03.1
  generalize mac (t.l0 * inv) N.l4 t.l4 r03.1 = r04 at h04 ⊢
  have h05 := mac_spec (t.l0 * inv) N.l5 t.l5 r04.1
  generalize mac (t.l0 * inv) N.l5 t.l5 r04.1 = r05 at h05 ⊢
  have h06 := adc_spec t.l6 r05.1 0
  generalize adc t.l6 r05.1 0 = r06 at h06 ⊢
  obtain ⟨he1, E0⟩ := U384.redc_row N inv t.l0 t.l1 t.l2 t.l3 t.l4 t.l5 t.l6 0 r00 r01 r02 r03 r04 r05 r06
    hinv h00 h01 h02 h03 h04 h05 h06 he0
  have h10 := mac_spec (r01.2 * inv) N.l0 r01.2 0
  generalize mac (r01.2 * inv) N.l0 r01.2 0 = r10 at h10 ⊢
  have h11 := mac_spec (r01.2 * inv) N.l1 r02.2 r10.1
  generalize mac (r01.2 * inv) N.l1 r02.2 r10.1 = r11 at h11 ⊢
  have h12 := mac_spec (r01.2 * inv) N.l2 r03.2 r11.1
  generalize mac (r01.2 * inv) N.l2 r03.2 r11.1 = r12 at h12 ⊢
  have h13 := mac_spec (r01.2 * inv) N.l3 r04.2 r12.1
  generalize mac (r01.2 * inv) N.l3 r04.2 r12.1 = r13 at h13 ⊢
  have h14 := mac_spec (r01.2 * inv) N.l4 r05.2 r13.1
  generalize mac (r01.2 * inv) N.l4 r05.2 r13.1 = r14 at h14 ⊢
  have h15 := mac_spec (r01.2 * inv) N.l5 r06.2 r14.1
  generalize mac (r01.2 * inv) N.l5 r06.2 r14.1 = r15 at h15 ⊢
  have h16 := adc_spec t.l7 r15.1 r06.1
  generalize adc t.l7 r15.1 r06.1 = r16 at h16 ⊢
  obtain ⟨he2, E1⟩ := U384.redc_row N inv r01.2 r02.2 r03.2 r04.2 r05.2 r06.2 t.l7 r06.1 r10 r11 r12 r13 r14 r15 r16
    hinv h10 h11 h12 h13 h14 h15 h16 he1
  have h20 := mac_spec (r11.2 * inv) N.l0 r11.2 0
  generalize mac (r11.2 * inv) N.l0 r11.2 0 = r20 at h20 ⊢
  have h21 := mac_spec (r11.2 * inv) N.l1 r12.2 r20.1
  generalize mac (r11.2 * inv) N.l1 r12.2 r20.1 = r21 at h21 ⊢
  have h22 := mac_spec (r11.2 * inv) N.l2 r13.2 r21.1
  generalize mac (r11.2 * inv) N.l2 r13.2 r21.1 = r22 at h22 ⊢
  have h23 := mac_spec (r11.2 * inv) N.l3 r14.2 r22.1
  generalize mac (r11.2 * inv) N.l3 r14.2 r22.1 = r23 at h23 ⊢
  have h24 := mac_spec (r11.2 * inv) N.l4 r15.2 r23.1
  generalize mac (r11.2 * inv) N.l4 r15.2 r23.1 = r24 at h24 ⊢
  have h25 := mac_spec (r11.2 * inv) N.l5 r16.2 r24.1
  generalize mac (r11.2 * inv) N.l5 r16.2 r24.1 = r25 at h25 ⊢
  have h26 := adc_spec t.l8 r25.1 r16.1
  generalize adc t.l8 r25.1 r16.1 = r26 at h26 ⊢
  obtain ⟨he3, E2⟩ := U384.redc_row N inv r11.2 r12.2 r13.2 r14.2 r15.2 r16.2 t.l8 r16.1 r20 r21 r22 r23 r24 r25 r26
    hinv h20 h21 h22 h23 h24 h25 h26 he2
  have h30 := mac_spec (r21.2 * inv) N.l0 r21.2 0
  generalize mac (r21.2 * inv) N.l0 r21.2 0 = r30 at h30 ⊢
  have h31 := mac_spec (r21.2 * inv) N.l1 r22.2 r30.1
  generalize mac (r21.2 * inv) N.l1 r22.2 r30.1 = r31 at h31 ⊢
  have h32 := mac_spec (r21.2 * inv) N.l2 r23.2 r31.1
  generalize mac (r21.2 * inv) N.l2 r23.2 r31.1 = r32 at h32 ⊢
  have h33 := mac_spec (r21.2 * inv) N.l3 r24.2 r32.1
  generalize mac (r21.2 * inv) N.l3 r24.2 r32.1 = r33 at h33 ⊢
  have h34 := mac_spec (r21.2 * inv) N.l4 r25.2 r33.1
  generalize mac (r21.2 * inv) N.l4 r25.2 r33.1 = r34 at h34 ⊢
  have h35 := mac_spec (r21.2 * inv) N.l5 r26.2 r34.1
  generalize mac (r21.2 * inv) N.l5 r26.2 r34.1 = r35 at h35 ⊢
  have h36 := adc_spec t.l9 r35.1 r26.1
  generalize adc t.l9 r35.1 r26.1 = r36 at h36 ⊢
  obtain ⟨he4, E3⟩ := U384.redc_row N inv r21.2 r22.2 r23.2 r24.2 r25.2 r26.2 t.l9 r26.1 r30 r31 r32 r33 r34 r35 r36
    hinv h30 h31 h32 h33 h34 h35 h36 he3
  have h40 := mac_spec (r31.2 * inv) N.l0 r31.2 0
  generalize mac (r31.2 * inv) N.l0 r31.2 0 = r40 at h40 ⊢
  have h41 := mac_spec (r31.2 * inv) N.l1 r32.2 r40.1
  generalize mac (r31.2 * inv) N.l1 r32.2 r40.1 = r41 at h41 ⊢
  have h42 := mac_spec (r31.2 * inv) N.l2 r33.2 r41.1
  generalize mac (r31.2 * inv) N.l2 r33.2 r41.1 = r42 at h42 ⊢
  have h43 := mac_spec (r31.2 * inv) N.l3 r34.2 r42.1
  generalize mac (r31.2 * inv) N.l3 r34.2 r42.1 = r43 at h43 ⊢
  have h44 := mac_spec (r31.2 * inv) N.l4 r35.2 r43.1
  generalize mac (r31.2 * inv) N.l4 r35.2 r43.1 = r44 at h44 ⊢
  have h45 := mac_spec (r31.2 * inv) N.l5 r36.2 r44.1
  generalize mac (r31.2 * inv) N.l5 r36.2 r44.1 = r45 at h45 ⊢
  have h46 := adc_spec t.l10 r45.1 r36.1
  generalize adc t.l10 r45.1 r36.1 = r46 at h46 ⊢
  obtain ⟨he5, E4⟩ := U384.redc_row N inv r31.2 r32.2 r33.2 r34.2 r35.2 r36.2 t.l10 r36.1 r40 r41 r42 r43 r44 r45 r46
    hinv h40 h41 h42 h43 h44 h45 h46 he4
  have h50 := mac_spec (r41.2 * inv) N.l0 r41.2 0
  generalize mac (r41.2 * inv) N.l0 r41.2 0 = r50 at h50 ⊢
  have h51 := mac_spec (r41.2 * inv) N.l1 r42.2 r50.1
  generalize mac (r41.2 * inv) N.l1 r42.2 r50.1 = r51 at h51 ⊢
  have h52 := mac_spec (r41.2 * inv) N.l2 r43.2 r51.1
  generalize mac (r41.2 * inv) N.l2 r43.2 r51.1 = r52 at h52 ⊢
  have h53 := mac_spec (r41.2 * inv) N.l3 r44.2 r52.1
  generalize mac (r41.2 * inv) N.l3 r44.2 r52.1 = r53 at h53 ⊢
  have h54 := mac_spec (r41.2 * inv) N.l4 r45.2 r53.1
  generalize mac (r41.2 * inv) N.l4 r45.2 r53.1 = r54 at h54 ⊢
  have h55 := mac_spec (r41.2 * inv) N.l5 r46.2 r54.1
  generalize mac (r41.2 * inv) N.l5 r46.2 r54.1 = r55 at h55 ⊢
  have h56 := adc_spec t.l11 r55.1 r46.1
  generalize adc t.l11 r55.1 r46.1 = r56 at h56 ⊢
  obtain ⟨he6, E5⟩ := U384.redc_row N inv r41.2 r42.2 r43.2 r44.2 r45.2 r46.2 t.l11 r46.1 r50 r51 r52 r53 r54 r55 r56
    hinv h50 h51 h52 h53 h54 h55 h56 he5
  have C := MontMath.redc_chain6 E0 E1 E2 E3 E4 E5 zero_toNat'
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  exact ⟨r56.1, ⟨r51.2, r52.2, r53.2, r54.2, r55.2, r56.2⟩, _, rfl, C.1, C.2⟩

/-- Kind: functional correctness (Montgomery reduction on 6 limbs).
    Says: for a modulus `N` with `n0inv · N ≡ −1 (mod 2^64)` and an input `t < N · 2^384`, the
    result of `redc` is below `N` and, times `2^384`, congruent to `t` modulo `N`.
    Does not say: anything for `t ≥ N · 2^384`, that `N` is prime, or anything about timing. -/
theorem U384.redc_spec (N : U384) (inv : UInt64) (t : U768)
    (hinv : (inv.toNat * (N.toNat % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    (ht : t.toNat < N.toNat * 2 ^ 384) :
    (U384.redc N inv t).toNat < N.toNat ∧
      (U384.redc N inv t).toNat * 2 ^ 384 % N.toNat = t.toNat % N.toNat := by
  obtain ⟨e, q, M, hEq, hM, hC⟩ := U384.redc_rows N inv t hinv
  have hq := MontMath.redc_lt_two N.toNat (2 ^ 384) t.toNat M (e.toNat * 2 ^ 384 + q.toNat) hC ht hM
  obtain ⟨hval, hlt⟩ := U384.condSub_spec N e q hq
  rw [hEq]
  refine ⟨hlt, ?_⟩
  rw [hval]
  exact MontMath.redc_mod N.toNat (2 ^ 384) t.toNat M (e.toNat * 2 ^ 384 + q.toNat) hC

#print axioms U256.redc_row
#print axioms U256.redc_rows
#print axioms U256.redc_spec
#print axioms U384.redc_row
#print axioms U384.redc_rows
#print axioms U384.redc_spec

end EVMCleanroom.Precompiles
