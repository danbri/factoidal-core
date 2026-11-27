import EVMCleanroom.Precompiles.Limb

/-!
# The limb primitives compute what they say, on natural numbers

`Limb.mac`, `Limb.adc` and `Limb.sbb` are stated against `UInt64.toNat`:
`mac a b c d` is the two-limb value of `a * b + c + d`, `adc a b c` the
two-limb value of `a + b + c`, and `sbb a b c` the difference `a - b - c`
with its borrow. These are the only places where wrapping 64-bit arithmetic
is reasoned about; the multi-limb theorems (`LimbU256Proofs.lean`, the
Montgomery proofs) chain these equations and never unfold the primitives.

Everything here is proved for all inputs. Nothing is said about timing.
-/

namespace EVMCleanroom.Precompiles.Limb

/-- `omega` with the goal moved into the context first. The `omega` tactic begins with
`assumption`, which compares the goal with every hypothesis; for two different sums with
weights such as `2^64` (or `2^64` against `2^128`) that comparison unfolds the numerals and
runs into the recursion limit. With the goal `False` the comparison is immediate. -/
macro "limb_omega" : tactic => `(tactic| (apply Classical.byContradiction; intro _; omega))

/-- The product of two numbers split at a base `h`. -/
private theorem mul_split (a0 a1 b0 b1 h : Nat) :
    (a1 * h + a0) * (b1 * h + b0) = a1 * b1 * (h * h) + (a1 * b0 + a0 * b1) * h + a0 * b0 := by
  first
    | grind
    | simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem toNat_carry (x y : UInt64) :
    (if x < y then (1 : UInt64) else 0).toNat = if x.toNat < y.toNat then 1 else 0 := by
  by_cases h : x < y
  · rw [if_pos h, if_pos (UInt64.lt_iff_toNat_lt.1 h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (UInt64.lt_iff_toNat_lt.2 h'))]; rfl

private theorem toNat_lo (a : UInt64) : (a % half).toNat = a.toNat % 4294967296 :=
  (UInt64.toNat_mod a half).trans rfl

private theorem toNat_hi (a : UInt64) : (a / half).toNat = a.toNat / 4294967296 :=
  (UInt64.toNat_div a half).trans rfl

/-- A product of two 32-bit values does not wrap. -/
private theorem toNat_mul_small (x y : UInt64) (hx : x.toNat ≤ 4294967295) (hy : y.toNat ≤ 4294967295) :
    (x * y).toNat = x.toNat * y.toNat ∧ (x * y).toNat ≤ 18446744065119617025 := by
  have h : x.toNat * y.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul hx hy
  rw [UInt64.toNat_mul]
  limb_omega

/-- The second half of `mac`: the four half products put together. -/
private def combine (p00 p01 p10 p11 : UInt64) : UInt64 × UInt64 :=
  let mid := p00 / half + p01 % half + p10 % half
  (p11 + p01 / half + p10 / half + mid / half, p00 % half + mid * half)

/-- The last part of `mac`: two additions into the low limb, carries into the high limb. -/
private def addTwo (r : UInt64 × UInt64) (c d : UInt64) : UInt64 × UInt64 :=
  let lo1 := r.2 + c
  let hi1 := r.1 + (if lo1 < r.2 then 1 else 0)
  let lo2 := lo1 + d
  let hi2 := hi1 + (if lo2 < lo1 then 1 else 0)
  (hi2, lo2)

private theorem mac_eq (a b c d : UInt64) :
    mac a b c d =
      addTwo (combine ((a % half) * (b % half)) ((a % half) * (b / half))
        ((a / half) * (b % half)) ((a / half) * (b / half))) c d := rfl

private theorem combine_spec (p00 p01 p10 p11 : UInt64)
    (h00 : p00.toNat ≤ 18446744065119617025) (h01 : p01.toNat ≤ 18446744065119617025)
    (h10 : p10.toNat ≤ 18446744065119617025) (h11 : p11.toNat ≤ 18446744065119617025) :
    (combine p00 p01 p10 p11).1.toNat * 2 ^ 64 + (combine p00 p01 p10 p11).2.toNat =
      p11.toNat * 2 ^ 64 + (p01.toNat + p10.toNat) * 2 ^ 32 + p00.toNat := by
  simp only [combine, half, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  limb_omega

private theorem addTwo_spec (hi lo c d : UInt64)
    (hb : hi.toNat * 18446744073709551616 + lo.toNat + c.toNat + d.toNat <
      340282366920938463463374607431768211456) :
    (addTwo (hi, lo) c d).1.toNat * 2 ^ 64 + (addTwo (hi, lo) c d).2.toNat =
      hi.toNat * 2 ^ 64 + lo.toNat + c.toNat + d.toNat := by
  have hhi := UInt64.toNat_lt hi
  have hlo := UInt64.toNat_lt lo
  have hc := UInt64.toNat_lt c
  have hd := UInt64.toNat_lt d
  simp only [addTwo, toNat_carry, UInt64.toNat_add, Nat.reducePow] at hhi hlo hc hd ⊢
  split <;> split <;> limb_omega

/-- Kind: functional correctness (multiply-accumulate step).
    Says: for all inputs the pair returned by `mac a b c d`, read as `high · 2^64 + low`, is
    exactly `a · b + c + d` on natural numbers; nothing is lost to wrapping.
    Does not say: anything about running time or about the compiled code. -/
theorem mac_spec (a b c d : UInt64) :
    (mac a b c d).1.toNat * 2 ^ 64 + (mac a b c d).2.toNat =
      a.toNat * b.toNat + c.toNat + d.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hd := UInt64.toNat_lt d
  have hA : a.toNat / 4294967296 * 4294967296 + a.toNat % 4294967296 = a.toNat :=
    Nat.div_add_mod' _ _
  have hB : b.toNat / 4294967296 * 4294967296 + b.toNat % 4294967296 = b.toNat :=
    Nat.div_add_mod' _ _
  have a0 : (a % half).toNat ≤ 4294967295 := by rw [toNat_lo]; limb_omega
  have a1 : (a / half).toNat ≤ 4294967295 := by rw [toNat_hi]; limb_omega
  have b0 : (b % half).toNat ≤ 4294967295 := by rw [toNat_lo]; limb_omega
  have b1 : (b / half).toNat ≤ 4294967295 := by rw [toNat_hi]; limb_omega
  have ha' : a.toNat ≤ 18446744073709551615 := by limb_omega
  have hb' : b.toNat ≤ 18446744073709551615 := by limb_omega
  have hc' : c.toNat ≤ 18446744073709551615 := by limb_omega
  have hd' : d.toNat ≤ 18446744073709551615 := by limb_omega
  have hab : a.toNat * b.toNat ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul ha' hb'
  have hsum : a.toNat * b.toNat + c.toNat + d.toNat < 340282366920938463463374607431768211456 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add hab hc') hd') (by decide)
  have hsplit := mul_split (a.toNat % 4294967296) (a.toNat / 4294967296)
    (b.toNat % 4294967296) (b.toNat / 4294967296) 4294967296
  rw [hA, hB] at hsplit
  obtain ⟨e00, k00⟩ := toNat_mul_small (a % half) (b % half) a0 b0
  obtain ⟨e01, k01⟩ := toNat_mul_small (a % half) (b / half) a0 b1
  obtain ⟨e10, k10⟩ := toNat_mul_small (a / half) (b % half) a1 b0
  obtain ⟨e11, k11⟩ := toNat_mul_small (a / half) (b / half) a1 b1
  have hcomb := combine_spec _ _ _ _ k00 k01 k10 k11
  rw [e00, e01, e10, e11, toNat_lo a, toNat_hi a, toNat_lo b, toNat_hi b] at hcomb
  clear ha hb hc hd hA hB a0 a1 b0 b1 ha' hb' hc' hd' hab e00 e01 e10 e11 k00 k01 k10 k11
  have hval : (combine ((a % half) * (b % half)) ((a % half) * (b / half))
      ((a / half) * (b % half)) ((a / half) * (b / half))).1.toNat * 2 ^ 64 +
      (combine ((a % half) * (b % half)) ((a % half) * (b / half))
      ((a / half) * (b % half)) ((a / half) * (b / half))).2.toNat = a.toNat * b.toNat := by
    clear hsum
    limb_omega
  clear hcomb hsplit
  rw [mac_eq]
  generalize combine ((a % half) * (b % half)) ((a % half) * (b / half))
      ((a / half) * (b % half)) ((a / half) * (b / half)) = r at hval ⊢
  obtain ⟨hi, lo⟩ := r
  rw [← hval]
  refine addTwo_spec hi lo c d ?_
  have hval' : hi.toNat * 18446744073709551616 + lo.toNat = a.toNat * b.toNat := hval
  rw [hval']
  exact hsum

/-- Kind: functional correctness (add with carry).
    Says: for all inputs `adc a b c`, read as `carry · 2^64 + low`, is exactly `a + b + c`.
    Does not say: that the carry is at most 1 (see `adc_carry_le`; it can be 2 for a large `c`). -/
theorem adc_spec (a b c : UInt64) :
    (adc a b c).1.toNat * 2 ^ 64 + (adc a b c).2.toNat = a.toNat + b.toNat + c.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  simp only [adc, toNat_carry, UInt64.toNat_add, Nat.reducePow] at ha hb hc ⊢
  split <;> split <;> limb_omega

/-- Kind: bound.
    Says: with a carry-in of 0 or 1 the carry-out of `adc` is 0 or 1.
    Does not say: anything for a larger third argument. -/
theorem adc_carry_le (a b c : UInt64) (hc : c.toNat ≤ 1) : (adc a b c).1.toNat ≤ 1 := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  simp only [adc, toNat_carry, UInt64.toNat_add, Nat.reducePow] at ha hb ⊢
  split <;> split <;> limb_omega

/-- Kind: functional correctness (subtract with borrow).
    Says: for all inputs `sbb a b c = (borrow, low)` satisfies
    `a + borrow · 2^64 = low + b + c` on natural numbers.
    Does not say: that the borrow is at most 1 (see `sbb_borrow_le`). -/
theorem sbb_spec (a b c : UInt64) :
    a.toNat + (sbb a b c).1.toNat * 2 ^ 64 = (sbb a b c).2.toNat + b.toNat + c.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  simp only [sbb, toNat_carry, UInt64.toNat_add, UInt64.toNat_sub, Nat.reducePow] at ha hb hc ⊢
  split <;> split <;> limb_omega

/-- Kind: bound.
    Says: with a borrow-in of 0 or 1 the borrow-out of `sbb` is 0 or 1.
    Does not say: anything for a larger third argument. -/
theorem sbb_borrow_le (a b c : UInt64) (hc : c.toNat ≤ 1) : (sbb a b c).1.toNat ≤ 1 := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  simp only [sbb, toNat_carry, UInt64.toNat_add, UInt64.toNat_sub, Nat.reducePow] at ha hb ⊢
  split <;> split <;> limb_omega

#print axioms mac_spec
#print axioms adc_spec
#print axioms adc_carry_le
#print axioms sbb_spec
#print axioms sbb_borrow_le

end EVMCleanroom.Precompiles.Limb
