import EVMCleanroom.Precompiles.LimbProofs
import EVMCleanroom.Precompiles.Field

/-!
# The four-limb routines compute the `Nat` definitions

`U256` values are read through `U256.toNat` (limbs least significant first).
Proved here, for all inputs unless a hypothesis is shown: the range of
`toNat`, `ofNat` as the low 256 bits, injectivity of `toNat`, the full
addition and subtraction with their carry and borrow, the conditional
subtraction, the modular sum, difference and negation against `Fp.add`,
`Fp.sub` and `Fp.neg`, the zero and equality tests, and the full 512-bit
product.

The proofs chain the equations of `LimbProofs.lean` (`mac_spec`, `adc_spec`,
`sbb_spec`); the products of limbs are opaque to the linear arithmetic.
Montgomery reduction (`U256.redc`) is not covered in this module.
-/

namespace EVMCleanroom.Precompiles.U256

open Limb

private theorem zero_toNat : (0 : UInt64).toNat = 0 := rfl

private theorem u64_eq_zero_iff (x : UInt64) : x = 0 ↔ x.toNat = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UInt64.toNat_inj.1 (h.trans zero_toNat.symm)⟩

private theorem beq_zero_iff (x : UInt64) : (x == 0) = true ↔ x.toNat = 0 := by
  rw [beq_iff_eq, u64_eq_zero_iff]

private theorem bne_zero_iff (x : UInt64) : (x != 0) = true ↔ x.toNat ≠ 0 := by
  rw [bne_iff_ne, ne_eq, u64_eq_zero_iff]

/-- Kind: range.
    Says: a four-limb value is below `2^256`.
    Does not say: that it is below any modulus. -/
theorem toNat_lt (a : U256) : a.toNat < 2 ^ 256 := by
  have h0 := UInt64.toNat_lt a.l0
  have h1 := UInt64.toNat_lt a.l1
  have h2 := UInt64.toNat_lt a.l2
  have h3 := UInt64.toNat_lt a.l3
  simp only [U256.toNat]
  limb_omega

/-- Kind: functional correctness (conversion).
    Says: the limbs of a natural number are its low 256 bits.
    Does not say: anything about a modulus; `ofNat` does not reduce. -/
theorem toNat_ofNat (n : Nat) : (U256.ofNat n).toNat = n % 2 ^ 256 := by
  simp only [U256.ofNat, U256.toNat, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have e2 : n / 2 ^ 128 = n / 2 ^ 64 / 2 ^ 64 := by
    simp only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul]
  have e3 : n / 2 ^ 192 = n / 2 ^ 64 / 2 ^ 64 / 2 ^ 64 := by
    simp only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul]
  have e4 : n / 2 ^ 256 = n / 2 ^ 64 / 2 ^ 64 / 2 ^ 64 / 2 ^ 64 := by
    simp only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul]
  rw [e2, e3]
  limb_omega

/-- Kind: representation.
    Says: two four-limb values with the same number are the same limbs.
    Does not say: anything about residues modulo a field prime. -/
theorem toNat_inj {a b : U256} : a.toNat = b.toNat ↔ a = b := by
  constructor
  · intro h
    obtain ⟨a0, a1, a2, a3⟩ := a
    obtain ⟨b0, b1, b2, b3⟩ := b
    simp only [U256.toNat] at h
    have ha0 := UInt64.toNat_lt a0
    have ha1 := UInt64.toNat_lt a1
    have ha2 := UInt64.toNat_lt a2
    have ha3 := UInt64.toNat_lt a3
    have hb0 := UInt64.toNat_lt b0
    have hb1 := UInt64.toNat_lt b1
    have hb2 := UInt64.toNat_lt b2
    have hb3 := UInt64.toNat_lt b3
    have e0 : a0 = b0 := UInt64.toNat_inj.1 (by limb_omega)
    have e1 : a1 = b1 := UInt64.toNat_inj.1 (by limb_omega)
    have e2 : a2 = b2 := UInt64.toNat_inj.1 (by limb_omega)
    have e3 : a3 = b3 := UInt64.toNat_inj.1 (by limb_omega)
    subst e0 e1 e2 e3
    rfl
  · intro h
    rw [h]

/-- Kind: functional correctness (four-limb addition).
    Says: for all inputs `addCarry a b = (carry, sum)` with
    `carry · 2^256 + sum = a + b` on natural numbers and `carry ≤ 1`.
    Does not say: anything modulo a prime. -/
theorem addCarry_spec (a b : U256) :
    (U256.addCarry a b).1.toNat * 2 ^ 256 + (U256.addCarry a b).2.toNat = a.toNat + b.toNat ∧
      (U256.addCarry a b).1.toNat ≤ 1 := by
  have z := zero_toNat
  simp only [U256.addCarry, U256.toNat]
  have s0 := adc_spec a.l0 b.l0 0
  have k0 := adc_carry_le a.l0 b.l0 0 (by limb_omega)
  generalize adc a.l0 b.l0 0 = r0 at s0 k0 ⊢
  have s1 := adc_spec a.l1 b.l1 r0.1
  have k1 := adc_carry_le a.l1 b.l1 r0.1 (by limb_omega)
  generalize adc a.l1 b.l1 r0.1 = r1 at s1 k1 ⊢
  have s2 := adc_spec a.l2 b.l2 r1.1
  have k2 := adc_carry_le a.l2 b.l2 r1.1 (by limb_omega)
  generalize adc a.l2 b.l2 r1.1 = r2 at s2 k2 ⊢
  have s3 := adc_spec a.l3 b.l3 r2.1
  have k3 := adc_carry_le a.l3 b.l3 r2.1 (by limb_omega)
  generalize adc a.l3 b.l3 r2.1 = r3 at s3 k3 ⊢
  limb_omega

/-- Kind: functional correctness (four-limb subtraction).
    Says: for all inputs `subBorrow a b = (borrow, diff)` with
    `a + borrow · 2^256 = diff + b` on natural numbers and `borrow ≤ 1`.
    Does not say: anything modulo a prime. -/
theorem subBorrow_spec (a b : U256) :
    a.toNat + (U256.subBorrow a b).1.toNat * 2 ^ 256 = (U256.subBorrow a b).2.toNat + b.toNat ∧
      (U256.subBorrow a b).1.toNat ≤ 1 := by
  have z := zero_toNat
  simp only [U256.subBorrow, U256.toNat]
  have s0 := sbb_spec a.l0 b.l0 0
  have k0 := sbb_borrow_le a.l0 b.l0 0 (by limb_omega)
  generalize sbb a.l0 b.l0 0 = r0 at s0 k0 ⊢
  have s1 := sbb_spec a.l1 b.l1 r0.1
  have k1 := sbb_borrow_le a.l1 b.l1 r0.1 (by limb_omega)
  generalize sbb a.l1 b.l1 r0.1 = r1 at s1 k1 ⊢
  have s2 := sbb_spec a.l2 b.l2 r1.1
  have k2 := sbb_borrow_le a.l2 b.l2 r1.1 (by limb_omega)
  generalize sbb a.l2 b.l2 r1.1 = r2 at s2 k2 ⊢
  have s3 := sbb_spec a.l3 b.l3 r2.1
  have k3 := sbb_borrow_le a.l3 b.l3 r2.1 (by limb_omega)
  generalize sbb a.l3 b.l3 r2.1 = r3 at s3 k3 ⊢
  limb_omega

/-- Kind: functional correctness (one conditional subtraction).
    Says: when the value `e · 2^256 + a` is below `2N`, `condSub N e a` is that value if it is
    below `N` and that value minus `N` otherwise.
    Does not say: anything when the value is `2N` or more. -/
theorem condSub_eq (N : U256) (e : UInt64) (a : U256)
    (h : e.toNat * 2 ^ 256 + a.toNat < 2 * N.toNat) :
    (U256.condSub N e a).toNat =
      if e.toNat * 2 ^ 256 + a.toNat < N.toNat then e.toNat * 2 ^ 256 + a.toNat
      else e.toNat * 2 ^ 256 + a.toNat - N.toNat := by
  obtain ⟨hs, hb⟩ := subBorrow_spec a N
  have h1 := toNat_lt (U256.subBorrow a N).2
  have h2 := toNat_lt a
  have h3 := toNat_lt N
  show (if (e != 0 || (U256.subBorrow a N).1 == 0) = true then (U256.subBorrow a N).2 else a).toNat = _
  by_cases hc : (e != 0 || (U256.subBorrow a N).1 == 0) = true
  · rw [if_pos hc]
    simp only [Bool.or_eq_true, bne_zero_iff, beq_zero_iff] at hc
    split <;> limb_omega
  · rw [if_neg hc]
    simp only [Bool.or_eq_true, bne_zero_iff, beq_zero_iff] at hc
    split <;> limb_omega

private theorem mod_of_lt_two (v n : Nat) (h : v < 2 * n) :
    (if v < n then v else v - n) = v % n := by
  split
  · rename_i hlt; exact (Nat.mod_eq_of_lt hlt).symm
  · rename_i hge
    rw [Nat.mod_eq_sub_mod (by limb_omega), Nat.mod_eq_of_lt (by limb_omega)]

/-- Kind: functional correctness (one conditional subtraction).
    Says: when the value `e · 2^256 + a` is below `2N`, `condSub N e a` is its residue modulo
    `N`, and so is below `N`.
    Does not say: anything when the value is `2N` or more. -/
theorem condSub_spec (N : U256) (e : UInt64) (a : U256)
    (h : e.toNat * 2 ^ 256 + a.toNat < 2 * N.toNat) :
    (U256.condSub N e a).toNat = (e.toNat * 2 ^ 256 + a.toNat) % N.toNat ∧
      (U256.condSub N e a).toNat < N.toNat := by
  have e1 := condSub_eq N e a h
  rw [mod_of_lt_two _ _ h] at e1
  refine ⟨e1, ?_⟩
  rw [e1]
  exact Nat.mod_lt _ (by limb_omega)

/-- Kind: refinement (modular addition).
    Says: on values below the modulus, `addMod` on limbs is `Fp.add` on natural numbers.
    Does not say: anything for a non-canonical argument, or that the modulus is prime. -/
theorem addMod_spec (N a b : U256) (ha : a.toNat < N.toNat) (hb : b.toNat < N.toNat) :
    (U256.addMod N a b).toNat = Fp.add N.toNat a.toNat b.toNat := by
  obtain ⟨hs, hc⟩ := addCarry_spec a b
  have hcs := condSub_eq N (U256.addCarry a b).1 (U256.addCarry a b).2 (by limb_omega)
  show (U256.condSub N (U256.addCarry a b).1 (U256.addCarry a b).2).toNat = _
  rw [hcs]
  unfold Fp.add
  split <;> split <;> limb_omega

/-- Kind: refinement (modular subtraction).
    Says: on values below the modulus, `subMod` on limbs is `Fp.sub` on natural numbers.
    Does not say: anything for a non-canonical argument, or that the modulus is prime. -/
theorem subMod_spec (N a b : U256) (ha : a.toNat < N.toNat) (hb : b.toNat < N.toNat) :
    (U256.subMod N a b).toNat = Fp.sub N.toNat a.toNat b.toNat := by
  obtain ⟨hs, hbw⟩ := subBorrow_spec a b
  obtain ⟨hs2, hc2⟩ := addCarry_spec (U256.subBorrow a b).2 N
  have h1 := toNat_lt (U256.subBorrow a b).2
  have h2 := toNat_lt (U256.addCarry (U256.subBorrow a b).2 N).2
  have h3 := toNat_lt a
  have h4 := toNat_lt b
  have h5 := toNat_lt N
  show (if ((U256.subBorrow a b).1 != 0) = true then (U256.addCarry (U256.subBorrow a b).2 N).2
    else (U256.subBorrow a b).2).toNat = _
  unfold Fp.sub
  by_cases hc : ((U256.subBorrow a b).1 != 0) = true
  · rw [if_pos hc]
    rw [bne_zero_iff] at hc
    split <;> limb_omega
  · rw [if_neg hc]
    rw [bne_zero_iff] at hc
    split <;> limb_omega

/-- Kind: functional correctness (zero test).
    Says: `isZero` holds exactly for the limbs of the number zero.
    Does not say: anything about zero modulo a prime for non-canonical values. -/
theorem isZero_iff (a : U256) : a.isZero = true ↔ a.toNat = 0 := by
  simp only [U256.isZero, beq_iff_eq, UInt64.or_eq_zero_iff]
  simp only [u64_eq_zero_iff, U256.toNat]
  limb_omega

/-- Kind: functional correctness (equality test).
    Says: `beq` holds exactly when the two values are the same number.
    Does not say: equality of residues for non-canonical values. -/
theorem beq_iff (a b : U256) : U256.beq a b = true ↔ a.toNat = b.toNat := by
  rw [toNat_inj]
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [U256.beq, beq_iff_eq, UInt64.or_eq_zero_iff, UInt64.xor_eq_zero_iff, U256.mk.injEq,
    and_assoc]

/-- Kind: refinement (modular negation).
    Says: on a value below the modulus, `negMod` on limbs is `Fp.neg` on natural numbers.
    Does not say: anything for a non-canonical argument, or that the modulus is prime. -/
theorem negMod_spec (N a : U256) (ha : a.toNat < N.toNat) :
    (U256.negMod N a).toNat = Fp.neg N.toNat a.toNat := by
  obtain ⟨hs, hbw⟩ := subBorrow_spec N a
  have h1 := toNat_lt (U256.subBorrow N a).2
  have h2 := toNat_lt N
  show (if a.isZero = true then a else (U256.subBorrow N a).2).toNat = _
  unfold Fp.neg
  by_cases hz : a.isZero = true
  · rw [if_pos hz, if_pos ((isZero_iff a).1 hz)]
    exact (isZero_iff a).1 hz
  · have hne : ¬ a.toNat = 0 := fun h0 => hz ((isZero_iff a).2 h0)
    rw [if_neg hz, if_neg hne]
    limb_omega

/-- The product of two four-digit numbers, digit by digit. -/
private theorem mul_expand4 (a0 a1 a2 a3 b0 b1 b2 b3 w1 w2 w3 : Nat) :
    (a0 + a1 * w1 + a2 * w2 + a3 * w3) * (b0 + b1 * w1 + b2 * w2 + b3 * w3) =
      a0 * b0 + a0 * b1 * w1 + a0 * b2 * w2 + a0 * b3 * w3 +
        a1 * b0 * w1 + a1 * b1 * (w1 * w1) + a1 * b2 * (w1 * w2) + a1 * b3 * (w1 * w3) +
        a2 * b0 * w2 + a2 * b1 * (w2 * w1) + a2 * b2 * (w2 * w2) + a2 * b3 * (w2 * w3) +
        a3 * b0 * w3 + a3 * b1 * (w3 * w1) + a3 * b2 * (w3 * w2) + a3 * b3 * (w3 * w3) := by
  first
    | grind
    | simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Kind: functional correctness (full product).
    Says: for all inputs the eight limbs of `mulWide a b` are exactly the product of the two
    numbers; nothing is lost.
    Does not say: anything about reduction modulo a prime, or about running time. -/
theorem mulWide_spec (a b : U256) : (U256.mulWide a b).toNat = a.toNat * b.toNat := by
  have z := zero_toNat
  have hexp := mul_expand4 a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat
    b.l0.toNat b.l1.toNat b.l2.toNat b.l3.toNat (2 ^ 64) (2 ^ 128) (2 ^ 192)
  simp only [U256.mulWide, U512.toNat, U256.toNat]
  have s00 := mac_spec a.l0 b.l0 0 0
  generalize mac a.l0 b.l0 0 0 = r00 at s00 ⊢
  have s01 := mac_spec a.l0 b.l1 0 r00.1
  generalize mac a.l0 b.l1 0 r00.1 = r01 at s01 ⊢
  have s02 := mac_spec a.l0 b.l2 0 r01.1
  generalize mac a.l0 b.l2 0 r01.1 = r02 at s02 ⊢
  have s03 := mac_spec a.l0 b.l3 0 r02.1
  generalize mac a.l0 b.l3 0 r02.1 = r03 at s03 ⊢
  have s10 := mac_spec a.l1 b.l0 r01.2 0
  generalize mac a.l1 b.l0 r01.2 0 = r10 at s10 ⊢
  have s11 := mac_spec a.l1 b.l1 r02.2 r10.1
  generalize mac a.l1 b.l1 r02.2 r10.1 = r11 at s11 ⊢
  have s12 := mac_spec a.l1 b.l2 r03.2 r11.1
  generalize mac a.l1 b.l2 r03.2 r11.1 = r12 at s12 ⊢
  have s13 := mac_spec a.l1 b.l3 r03.1 r12.1
  generalize mac a.l1 b.l3 r03.1 r12.1 = r13 at s13 ⊢
  have s20 := mac_spec a.l2 b.l0 r11.2 0
  generalize mac a.l2 b.l0 r11.2 0 = r20 at s20 ⊢
  have s21 := mac_spec a.l2 b.l1 r12.2 r20.1
  generalize mac a.l2 b.l1 r12.2 r20.1 = r21 at s21 ⊢
  have s22 := mac_spec a.l2 b.l2 r13.2 r21.1
  generalize mac a.l2 b.l2 r13.2 r21.1 = r22 at s22 ⊢
  have s23 := mac_spec a.l2 b.l3 r13.1 r22.1
  generalize mac a.l2 b.l3 r13.1 r22.1 = r23 at s23 ⊢
  have s30 := mac_spec a.l3 b.l0 r21.2 0
  generalize mac a.l3 b.l0 r21.2 0 = r30 at s30 ⊢
  have s31 := mac_spec a.l3 b.l1 r22.2 r30.1
  generalize mac a.l3 b.l1 r22.2 r30.1 = r31 at s31 ⊢
  have s32 := mac_spec a.l3 b.l2 r23.2 r31.1
  generalize mac a.l3 b.l2 r23.2 r31.1 = r32 at s32 ⊢
  have s33 := mac_spec a.l3 b.l3 r23.1 r32.1
  generalize mac a.l3 b.l3 r23.1 r32.1 = r33 at s33 ⊢
  limb_omega

#print axioms toNat_lt
#print axioms toNat_ofNat
#print axioms toNat_inj
#print axioms addCarry_spec
#print axioms subBorrow_spec
#print axioms condSub_eq
#print axioms condSub_spec
#print axioms addMod_spec
#print axioms subMod_spec
#print axioms negMod_spec
#print axioms isZero_iff
#print axioms beq_iff
#print axioms mulWide_spec

end EVMCleanroom.Precompiles.U256
