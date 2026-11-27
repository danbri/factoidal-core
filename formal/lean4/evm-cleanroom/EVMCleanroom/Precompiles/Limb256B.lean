import EVMCleanroom.Precompiles.LimbSpecsB
import EVMCleanroom.Precompiles.MontgomeryMath

/-!
# The four-limb routines compute the `Nat` definitions

`U256` values are read through `U256.toNat` (limbs least significant first).
Proved here, for all inputs unless a hypothesis is shown: the range of
`toNat`, `ofNat` as the low 256 bits, injectivity of `toNat`, the full
addition and subtraction with their carry and borrow, the conditional
subtraction, the modular sum, difference and negation against `Fp.add`,
`Fp.sub` and `Fp.neg`, the zero and equality tests, and the full 512-bit
product.

The proofs chain the equations of the limb primitives (`mac_spec`, `adc_spec`,
`sbb_spec`); every piece of linear arithmetic is a lemma about natural-number
variables, and the limb theorems only supply the equations.
Montgomery reduction (`U256.redc`) is in `MontgomeryRedcProofs.lean`.
Nothing is said about timing.
-/

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

namespace EVMCleanroom.Precompiles.U256

open Limb LimbB

private theorem zero_toNat : (0 : UInt64).toNat = 0 := rfl

private theorem u64_eq_zero_iff (x : UInt64) : x = 0 ↔ x.toNat = 0 :=
  ⟨fun h => by subst h; exact zero_toNat, fun h => UInt64.toNat_inj.1 (h.trans zero_toNat.symm)⟩

private theorem beq_zero_iff (x : UInt64) : (x == 0) = true ↔ x.toNat = 0 :=
  ⟨fun h => (u64_eq_zero_iff x).1 (beq_iff_eq.1 h), fun h => beq_iff_eq.2 ((u64_eq_zero_iff x).2 h)⟩

private theorem bne_zero_iff (x : UInt64) : (x != 0) = true ↔ ¬ x.toNat = 0 :=
  ⟨fun h h0 => (bne_iff_ne.1 h) ((u64_eq_zero_iff x).2 h0),
   fun h => bne_iff_ne.2 (fun hx => h ((u64_eq_zero_iff x).1 hx))⟩

private theorem cond_iff (e c : UInt64) :
    (e != 0 || c == 0) = true ↔ (¬ e.toNat = 0 ∨ c.toNat = 0) := by
  rw [Bool.or_eq_true]
  exact ⟨fun h => h.elim (fun h1 => Or.inl ((bne_zero_iff e).1 h1)) (fun h2 => Or.inr ((beq_zero_iff c).1 h2)),
    fun h => h.elim (fun h1 => Or.inl ((bne_zero_iff e).2 h1)) (fun h2 => Or.inr ((beq_zero_iff c).2 h2))⟩

private theorem or_zero (x y : UInt64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  first
    | exact UInt64.or_eq_zero_iff
    | simp [← UInt64.toBitVec_inj, BitVec.or_eq_zero_iff]

private theorem xor_zero (x y : UInt64) : x ^^^ y = 0 ↔ x = y := by
  first
    | exact UInt64.xor_eq_zero_iff
    | simp [← UInt64.toBitVec_inj, BitVec.xor_eq_zero_iff]

private theorem pos_of_lt_two {v n : Nat} (h : v < 2 * n) : 0 < n := by omega

private theorem toU64 (n : Nat) : n.toUInt64.toNat = n % 2 ^ 64 := by
  first
    | rfl
    | simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    | simp [Nat.toUInt64]

/-! ### Linear arithmetic on natural-number variables -/

private theorem lt_nat (a0 a1 a2 a3 : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64) :
    a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 < 2 ^ 256 := by omega

private theorem low_nat (a0 a1 a2 a3 : Nat) (h0 : a0 < 2 ^ 64) :
    (a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192) % 2 ^ 64 = a0 := by omega

private theorem limbs_nat (n : Nat) :
    n % 2 ^ 64 + n / 2 ^ 64 % 2 ^ 64 * 2 ^ 64 + n / 2 ^ 128 % 2 ^ 64 * 2 ^ 128 + n / 2 ^ 192 % 2 ^ 64 * 2 ^ 192 = n % 2 ^ 256 := by
  have e2 : n / 2 ^ 128 = n / 2 ^ 64 / 2 ^ 64 := by
    first
      | simp only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul]
      | omega
  have e3 : n / 2 ^ 192 = n / 2 ^ 64 / 2 ^ 64 / 2 ^ 64 := by
    first
      | simp only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul]
      | omega
  rw [e2, e3]
  omega

private theorem inj_nat (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64)
    (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64)
    (h : a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 = b0 + b1 * 2 ^ 64 + b2 * 2 ^ 128 + b3 * 2 ^ 192) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

private theorem zero_nat (a0 a1 a2 a3 : Nat) :
    (((a0 = 0 ∧ a1 = 0) ∧ a2 = 0) ∧ a3 = 0) ↔ a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 = 0 := by
  constructor
  · intro h
    omega
  · intro h
    have h0 : a0 = 0 := by omega
    have h1 : a1 = 0 := by omega
    have h2 : a2 = 0 := by omega
    have h3 : a3 = 0 := by omega
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩

private theorem add_chain {a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 r0 r1 r2 r3 z : Nat}
    (s0 : c0 * 2 ^ 64 + r0 = a0 + b0 + z)
    (s1 : c1 * 2 ^ 64 + r1 = a1 + b1 + c0)
    (s2 : c2 * 2 ^ 64 + r2 = a2 + b2 + c1)
    (s3 : c3 * 2 ^ 64 + r3 = a3 + b3 + c2)
    (hz : z = 0) :
    c3 * 2 ^ 256 + (r0 + r1 * 2 ^ 64 + r2 * 2 ^ 128 + r3 * 2 ^ 192) = a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 + (b0 + b1 * 2 ^ 64 + b2 * 2 ^ 128 + b3 * 2 ^ 192) := by omega

private theorem sub_chain {a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 r0 r1 r2 r3 z : Nat}
    (s0 : a0 + c0 * 2 ^ 64 = r0 + b0 + z)
    (s1 : a1 + c1 * 2 ^ 64 = r1 + b1 + c0)
    (s2 : a2 + c2 * 2 ^ 64 = r2 + b2 + c1)
    (s3 : a3 + c3 * 2 ^ 64 = r3 + b3 + c2)
    (hz : z = 0) :
    a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 + c3 * 2 ^ 256 = r0 + r1 * 2 ^ 64 + r2 * 2 ^ 128 + r3 * 2 ^ 192 + (b0 + b1 * 2 ^ 64 + b2 * 2 ^ 128 + b3 * 2 ^ 192) := by omega

private theorem condSub_nat (N a e bw r : Nat) (hs : a + bw * 2 ^ 256 = r + N) (hbw : bw ≤ 1)
    (hr : r < 2 ^ 256) (ha : a < 2 ^ 256) (hN : N < 2 ^ 256) (h : e * 2 ^ 256 + a < 2 * N) :
    ((¬ e = 0 ∨ bw = 0) → r = if e * 2 ^ 256 + a < N then e * 2 ^ 256 + a else e * 2 ^ 256 + a - N) ∧
    (¬ (¬ e = 0 ∨ bw = 0) → a = if e * 2 ^ 256 + a < N then e * 2 ^ 256 + a else e * 2 ^ 256 + a - N) := by
  constructor
  · intro hc
    split <;> omega
  · intro hc
    split <;> omega

private theorem subMod_nat (N a b bw r c s : Nat) (hs : a + bw * 2 ^ 256 = r + b) (hbw : bw ≤ 1)
    (hs2 : c * 2 ^ 256 + s = r + N) (hr : r < 2 ^ 256) (hsR : s < 2 ^ 256) (ha : a < N) (hb : b < N)
    (hN : N < 2 ^ 256) :
    (¬ bw = 0 → s = Fp.sub N a b) ∧ (bw = 0 → r = Fp.sub N a b) := by
  unfold Fp.sub
  constructor
  · intro h
    split <;> omega
  · intro h
    split <;> omega

private theorem negMod_nat (N a bw r : Nat) (hs : N + bw * 2 ^ 256 = r + a) (hr : r < 2 ^ 256)
    (ha : a < N) (hN : N < 2 ^ 256) (h0 : ¬ a = 0) : r = N - a := by omega

private theorem mul_row {x b0 b1 b2 b3 w0 w1 w2 w3 c0 c1 c2 c3 r0 r1 r2 r3 z : Nat}
    (h0 : c0 * 2 ^ 64 + r0 = x * b0 + w0 + z)
    (h1 : c1 * 2 ^ 64 + r1 = x * b1 + w1 + c0)
    (h2 : c2 * 2 ^ 64 + r2 = x * b2 + w2 + c1)
    (h3 : c3 * 2 ^ 64 + r3 = x * b3 + w3 + c2)
    (hz : z = 0) :
    w0 + w1 * 2 ^ 64 + w2 * 2 ^ 128 + w3 * 2 ^ 192 + x * (b0 + b1 * 2 ^ 64 + b2 * 2 ^ 128 + b3 * 2 ^ 192) = r0 + r1 * 2 ^ 64 + r2 * 2 ^ 128 + r3 * 2 ^ 192 + c3 * 2 ^ 256 := by
  rw [MontMath.mul_sum4 x b0 b1 b2 b3]
  omega

private theorem mul_chain {a0 a1 a2 a3 B z r0_0 r0_1 r0_2 r0_3 r1_0 r1_1 r1_2 r1_3 r2_0 r2_1 r2_2 r2_3 r3_0 r3_1 r3_2 r3_3 c0 c1 c2 c3 : Nat}
    (E0 : z + z * 2 ^ 64 + z * 2 ^ 128 + z * 2 ^ 192 + a0 * B =
      r0_0 + r0_1 * 2 ^ 64 + r0_2 * 2 ^ 128 + r0_3 * 2 ^ 192 + c0 * 2 ^ 256)
    (E1 : r0_1 + r0_2 * 2 ^ 64 + r0_3 * 2 ^ 128 + c0 * 2 ^ 192 + a1 * B =
      r1_0 + r1_1 * 2 ^ 64 + r1_2 * 2 ^ 128 + r1_3 * 2 ^ 192 + c1 * 2 ^ 256)
    (E2 : r1_1 + r1_2 * 2 ^ 64 + r1_3 * 2 ^ 128 + c1 * 2 ^ 192 + a2 * B =
      r2_0 + r2_1 * 2 ^ 64 + r2_2 * 2 ^ 128 + r2_3 * 2 ^ 192 + c2 * 2 ^ 256)
    (E3 : r2_1 + r2_2 * 2 ^ 64 + r2_3 * 2 ^ 128 + c2 * 2 ^ 192 + a3 * B =
      r3_0 + r3_1 * 2 ^ 64 + r3_2 * 2 ^ 128 + r3_3 * 2 ^ 192 + c3 * 2 ^ 256)
    (hz : z = 0) :
    (a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192) * B =
      r0_0 + r1_0 * 2 ^ 64 + r2_0 * 2 ^ 128 + r3_0 * 2 ^ 192 + r3_1 * 2 ^ 256 + r3_2 * 2 ^ 320 + r3_3 * 2 ^ 384 + c3 * 2 ^ 448 := by
  rw [MontMath.sum_mul4 a0 a1 a2 a3 B]
  omega

/-! ### The limb routines -/

/-- Kind: range.
    Says: a 4-limb value is below `2^256`.
    Does not say: that it is below any modulus. -/
theorem toNat_lt (a : U256) : a.toNat < 2 ^ 256 :=
  lt_nat a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat (UInt64.toNat_lt a.l0) (UInt64.toNat_lt a.l1) (UInt64.toNat_lt a.l2) (UInt64.toNat_lt a.l3)

/-- Kind: representation.
    Says: the low 64 bits of a 4-limb value are its first limb.
    Does not say: anything about the other limbs. -/
theorem toNat_mod (a : U256) : a.toNat % 2 ^ 64 = a.l0.toNat :=
  low_nat a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat (UInt64.toNat_lt a.l0)

/-- Kind: functional correctness (conversion).
    Says: the limbs of a natural number are its low 256 bits.
    Does not say: anything about a modulus; `ofNat` does not reduce. -/
theorem toNat_ofNat (n : Nat) : (U256.ofNat n).toNat = n % 2 ^ 256 := by
  simp only [U256.ofNat, U256.toNat, toU64, Nat.shiftRight_eq_div_pow]
  exact limbs_nat n

/-- Kind: representation.
    Says: two 4-limb values with the same number are the same limbs.
    Does not say: anything about residues modulo a field prime. -/
theorem toNat_inj {a b : U256} : a.toNat = b.toNat ↔ a = b := by
  constructor
  · intro h
    obtain ⟨a0, a1, a2, a3⟩ := a
    obtain ⟨b0, b1, b2, b3⟩ := b
    obtain ⟨e0, e1, e2, e3⟩ := inj_nat a0.toNat a1.toNat a2.toNat a3.toNat b0.toNat b1.toNat b2.toNat b3.toNat
      (UInt64.toNat_lt a0) (UInt64.toNat_lt a1) (UInt64.toNat_lt a2) (UInt64.toNat_lt a3)
      (UInt64.toNat_lt b0) (UInt64.toNat_lt b1) (UInt64.toNat_lt b2) (UInt64.toNat_lt b3) h
    rw [UInt64.toNat_inj.1 e0, UInt64.toNat_inj.1 e1, UInt64.toNat_inj.1 e2, UInt64.toNat_inj.1 e3]
  · intro h
    rw [h]

/-- Kind: functional correctness (4-limb addition).
    Says: for all inputs `addCarry a b = (carry, sum)` with
    `carry · 2^256 + sum = a + b` on natural numbers and `carry ≤ 1`.
    Does not say: anything modulo a prime. -/
theorem addCarry_spec (a b : U256) :
    (U256.addCarry a b).1.toNat * 2 ^ 256 + (U256.addCarry a b).2.toNat = a.toNat + b.toNat ∧
      (U256.addCarry a b).1.toNat ≤ 1 := by
  simp only [U256.addCarry, U256.toNat]
  have s0 := adc_spec a.l0 b.l0 0
  have k0 := adc_carry_le a.l0 b.l0 0 (Nat.le_trans (Nat.le_of_eq zero_toNat) (Nat.zero_le 1))
  generalize adc a.l0 b.l0 0 = r0 at s0 k0 ⊢
  have s1 := adc_spec a.l1 b.l1 r0.1
  have k1 := adc_carry_le a.l1 b.l1 r0.1 k0
  generalize adc a.l1 b.l1 r0.1 = r1 at s1 k1 ⊢
  have s2 := adc_spec a.l2 b.l2 r1.1
  have k2 := adc_carry_le a.l2 b.l2 r1.1 k1
  generalize adc a.l2 b.l2 r1.1 = r2 at s2 k2 ⊢
  have s3 := adc_spec a.l3 b.l3 r2.1
  have k3 := adc_carry_le a.l3 b.l3 r2.1 k2
  generalize adc a.l3 b.l3 r2.1 = r3 at s3 k3 ⊢
  exact ⟨add_chain s0 s1 s2 s3 zero_toNat, k3⟩

/-- Kind: functional correctness (4-limb subtraction).
    Says: for all inputs `subBorrow a b = (borrow, diff)` with
    `a + borrow · 2^256 = diff + b` on natural numbers and `borrow ≤ 1`.
    Does not say: anything modulo a prime. -/
theorem subBorrow_spec (a b : U256) :
    a.toNat + (U256.subBorrow a b).1.toNat * 2 ^ 256 = (U256.subBorrow a b).2.toNat + b.toNat ∧
      (U256.subBorrow a b).1.toNat ≤ 1 := by
  simp only [U256.subBorrow, U256.toNat]
  have s0 := sbb_spec a.l0 b.l0 0
  have k0 := sbb_borrow_le a.l0 b.l0 0 (Nat.le_trans (Nat.le_of_eq zero_toNat) (Nat.zero_le 1))
  generalize sbb a.l0 b.l0 0 = r0 at s0 k0 ⊢
  have s1 := sbb_spec a.l1 b.l1 r0.1
  have k1 := sbb_borrow_le a.l1 b.l1 r0.1 k0
  generalize sbb a.l1 b.l1 r0.1 = r1 at s1 k1 ⊢
  have s2 := sbb_spec a.l2 b.l2 r1.1
  have k2 := sbb_borrow_le a.l2 b.l2 r1.1 k1
  generalize sbb a.l2 b.l2 r1.1 = r2 at s2 k2 ⊢
  have s3 := sbb_spec a.l3 b.l3 r2.1
  have k3 := sbb_borrow_le a.l3 b.l3 r2.1 k2
  generalize sbb a.l3 b.l3 r2.1 = r3 at s3 k3 ⊢
  exact ⟨sub_chain s0 s1 s2 s3 zero_toNat, k3⟩

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
  have hn := condSub_nat N.toNat a.toNat e.toNat (U256.subBorrow a N).1.toNat
    (U256.subBorrow a N).2.toNat hs hb (toNat_lt _) (toNat_lt a) (toNat_lt N) h
  show (if (e != 0 || (U256.subBorrow a N).1 == 0) = true then (U256.subBorrow a N).2 else a).toNat = _
  by_cases hc : (e != 0 || (U256.subBorrow a N).1 == 0) = true
  · rw [if_pos hc]
    exact hn.1 ((cond_iff e _).1 hc)
  · rw [if_neg hc]
    exact hn.2 (fun h' => hc ((cond_iff e _).2 h'))

/-- Kind: functional correctness (one conditional subtraction).
    Says: when the value `e · 2^256 + a` is below `2N`, `condSub N e a` is its residue modulo
    `N`, and so is below `N`.
    Does not say: anything when the value is `2N` or more. -/
theorem condSub_spec (N : U256) (e : UInt64) (a : U256)
    (h : e.toNat * 2 ^ 256 + a.toNat < 2 * N.toNat) :
    (U256.condSub N e a).toNat = (e.toNat * 2 ^ 256 + a.toNat) % N.toNat ∧
      (U256.condSub N e a).toNat < N.toNat := by
  have e1 := condSub_eq N e a h
  rw [MontMath.mod_of_lt_two _ _ h] at e1
  have hN : 0 < N.toNat := pos_of_lt_two h
  refine ⟨e1, ?_⟩
  rw [e1]
  exact Nat.mod_lt _ hN

/-- Kind: refinement (modular addition).
    Says: on values below the modulus, `addMod` on limbs is `Fp.add` on natural numbers.
    Does not say: anything for a non-canonical argument, or that the modulus is prime. -/
theorem addMod_spec (N a b : U256) (ha : a.toNat < N.toNat) (hb : b.toNat < N.toNat) :
    (U256.addMod N a b).toNat = Fp.add N.toNat a.toNat b.toNat := by
  obtain ⟨hs, hc⟩ := addCarry_spec a b
  have hlt : (U256.addCarry a b).1.toNat * 2 ^ 256 + (U256.addCarry a b).2.toNat < 2 * N.toNat := by
    rw [hs, Nat.two_mul]
    exact Nat.add_lt_add ha hb
  have hcs := condSub_eq N (U256.addCarry a b).1 (U256.addCarry a b).2 hlt
  rw [hs] at hcs
  exact hcs

/-- Kind: refinement (modular subtraction).
    Says: on values below the modulus, `subMod` on limbs is `Fp.sub` on natural numbers.
    Does not say: anything for a non-canonical argument, or that the modulus is prime. -/
theorem subMod_spec (N a b : U256) (ha : a.toNat < N.toNat) (hb : b.toNat < N.toNat) :
    (U256.subMod N a b).toNat = Fp.sub N.toNat a.toNat b.toNat := by
  obtain ⟨hs, hbw⟩ := subBorrow_spec a b
  obtain ⟨hs2, hc2⟩ := addCarry_spec (U256.subBorrow a b).2 N
  have hn := subMod_nat N.toNat a.toNat b.toNat (U256.subBorrow a b).1.toNat
    (U256.subBorrow a b).2.toNat (U256.addCarry (U256.subBorrow a b).2 N).1.toNat
    (U256.addCarry (U256.subBorrow a b).2 N).2.toNat hs hbw hs2 (toNat_lt _) (toNat_lt _) ha hb
    (toNat_lt N)
  show (if ((U256.subBorrow a b).1 != 0) = true then (U256.addCarry (U256.subBorrow a b).2 N).2
    else (U256.subBorrow a b).2).toNat = _
  by_cases hc : ((U256.subBorrow a b).1 != 0) = true
  · rw [if_pos hc]
    exact hn.1 ((bne_zero_iff _).1 hc)
  · rw [if_neg hc]
    exact hn.2 (Decidable.byContradiction (fun h0 => hc ((bne_zero_iff _).2 h0)))

/-- Kind: functional correctness (zero test).
    Says: `isZero` holds exactly for the limbs of the number zero.
    Does not say: anything about zero modulo a prime for non-canonical values. -/
theorem isZero_iff (a : U256) : a.isZero = true ↔ a.toNat = 0 := by
  show ((a.l0 ||| a.l1 ||| a.l2 ||| a.l3) == 0) = true ↔ _
  rw [beq_iff_eq, or_zero, or_zero, or_zero,
    u64_eq_zero_iff a.l0, u64_eq_zero_iff a.l1, u64_eq_zero_iff a.l2, u64_eq_zero_iff a.l3]
  exact zero_nat a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat

/-- Kind: functional correctness (equality test).
    Says: `beq` holds exactly when the two values are the same number.
    Does not say: equality of residues for non-canonical values. -/
theorem beq_iff (a b : U256) : U256.beq a b = true ↔ a.toNat = b.toNat := by
  rw [toNat_inj]
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  show (((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3)) == 0) = true ↔ _
  rw [beq_iff_eq, or_zero, or_zero, or_zero,
    xor_zero a0 b0, xor_zero a1 b1, xor_zero a2 b2, xor_zero a3 b3]
  constructor
  · intro h
    obtain ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩ := h
    rw [e0, e1, e2, e3]
  · intro h
    cases h
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Kind: refinement (modular negation).
    Says: on a value below the modulus, `negMod` on limbs is `Fp.neg` on natural numbers.
    Does not say: anything for a non-canonical argument, or that the modulus is prime. -/
theorem negMod_spec (N a : U256) (ha : a.toNat < N.toNat) :
    (U256.negMod N a).toNat = Fp.neg N.toNat a.toNat := by
  obtain ⟨hs, hbw⟩ := subBorrow_spec N a
  show (if a.isZero = true then a else (U256.subBorrow N a).2).toNat = _
  unfold Fp.neg
  by_cases hz : a.isZero = true
  · rw [if_pos hz, if_pos ((isZero_iff a).1 hz)]
    exact (isZero_iff a).1 hz
  · have hne : ¬ a.toNat = 0 := fun h0 => hz ((isZero_iff a).2 h0)
    rw [if_neg hz, if_neg hne]
    exact negMod_nat N.toNat a.toNat _ _ hs (toNat_lt _) ha (toNat_lt N) hne

variable [LimbB.MacOK]

/-- Kind: functional correctness (full product).
    Says: for all inputs the 8 limbs of `mulWide a b` are exactly the product of the two
    numbers; nothing is lost.
    Does not say: anything about reduction modulo a prime, or about running time. -/
theorem mulWide_spec (a b : U256) : (U256.mulWide a b).toNat = a.toNat * b.toNat := by
  simp only [U256.mulWide]
  have s00 := mac_spec a.l0 b.l0 0 0
  generalize mac a.l0 b.l0 0 0 = r00 at s00 ⊢
  have s01 := mac_spec a.l0 b.l1 0 r00.1
  generalize mac a.l0 b.l1 0 r00.1 = r01 at s01 ⊢
  have s02 := mac_spec a.l0 b.l2 0 r01.1
  generalize mac a.l0 b.l2 0 r01.1 = r02 at s02 ⊢
  have s03 := mac_spec a.l0 b.l3 0 r02.1
  generalize mac a.l0 b.l3 0 r02.1 = r03 at s03 ⊢
  have E0 := mul_row s00 s01 s02 s03 zero_toNat
  have s10 := mac_spec a.l1 b.l0 r01.2 0
  generalize mac a.l1 b.l0 r01.2 0 = r10 at s10 ⊢
  have s11 := mac_spec a.l1 b.l1 r02.2 r10.1
  generalize mac a.l1 b.l1 r02.2 r10.1 = r11 at s11 ⊢
  have s12 := mac_spec a.l1 b.l2 r03.2 r11.1
  generalize mac a.l1 b.l2 r03.2 r11.1 = r12 at s12 ⊢
  have s13 := mac_spec a.l1 b.l3 r03.1 r12.1
  generalize mac a.l1 b.l3 r03.1 r12.1 = r13 at s13 ⊢
  have E1 := mul_row s10 s11 s12 s13 zero_toNat
  have s20 := mac_spec a.l2 b.l0 r11.2 0
  generalize mac a.l2 b.l0 r11.2 0 = r20 at s20 ⊢
  have s21 := mac_spec a.l2 b.l1 r12.2 r20.1
  generalize mac a.l2 b.l1 r12.2 r20.1 = r21 at s21 ⊢
  have s22 := mac_spec a.l2 b.l2 r13.2 r21.1
  generalize mac a.l2 b.l2 r13.2 r21.1 = r22 at s22 ⊢
  have s23 := mac_spec a.l2 b.l3 r13.1 r22.1
  generalize mac a.l2 b.l3 r13.1 r22.1 = r23 at s23 ⊢
  have E2 := mul_row s20 s21 s22 s23 zero_toNat
  have s30 := mac_spec a.l3 b.l0 r21.2 0
  generalize mac a.l3 b.l0 r21.2 0 = r30 at s30 ⊢
  have s31 := mac_spec a.l3 b.l1 r22.2 r30.1
  generalize mac a.l3 b.l1 r22.2 r30.1 = r31 at s31 ⊢
  have s32 := mac_spec a.l3 b.l2 r23.2 r31.1
  generalize mac a.l3 b.l2 r23.2 r31.1 = r32 at s32 ⊢
  have s33 := mac_spec a.l3 b.l3 r23.1 r32.1
  generalize mac a.l3 b.l3 r23.1 r32.1 = r33 at s33 ⊢
  have E3 := mul_row s30 s31 s32 s33 zero_toNat
  exact (mul_chain E0 E1 E2 E3 zero_toNat).symm

#print axioms toNat_lt
#print axioms toNat_mod
#print axioms toNat_ofNat
#print axioms toNat_inj
#print axioms addCarry_spec
#print axioms subBorrow_spec
#print axioms condSub_eq
#print axioms condSub_spec
#print axioms addMod_spec
#print axioms subMod_spec
#print axioms isZero_iff
#print axioms beq_iff
#print axioms negMod_spec
#print axioms mulWide_spec

end EVMCleanroom.Precompiles.U256
