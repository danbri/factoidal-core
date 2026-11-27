import EVMCleanroom.Precompiles.LimbSpecsB

/-!
# Temporary: the equation of `mac`, with the arithmetic on natural-number variables

A second route to `mac_spec` while `LimbProofs.lean` does not build: the same
decomposition as there (half products, `combine`, `addTwo`), but every `omega`
call is a lemma about natural-number variables, applied to the limb values.
Removed at the merge with `proofs-a` if theirs builds.
-/

set_option maxRecDepth 8192

namespace EVMCleanroom.Precompiles.LimbB

open Limb

theorem mul_split (a0 a1 b0 b1 h : Nat) :
    (a1 * h + a0) * (b1 * h + b0) = a1 * b1 * (h * h) + (a1 * b0 + a0 * b1) * h + a0 * b0 := by
  first
    | grind
    | simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem toNat_lo (a : UInt64) : (a % half).toNat = a.toNat % 4294967296 :=
  (UInt64.toNat_mod a half).trans rfl

theorem toNat_hi (a : UInt64) : (a / half).toNat = a.toNat / 4294967296 :=
  (UInt64.toNat_div a half).trans rfl

theorem small_nat (x y p : Nat) (hx : x ≤ 4294967295) (hy : y ≤ 4294967295)
    (hxy : x * y ≤ 4294967295 * 4294967295) (hp : p = x * y % 2 ^ 64) :
    p = x * y ∧ p ≤ 18446744065119617025 := by
  omega

theorem toNat_mul_small (x y : UInt64) (hx : x.toNat ≤ 4294967295) (hy : y.toNat ≤ 4294967295) :
    (x * y).toNat = x.toNat * y.toNat ∧ (x * y).toNat ≤ 18446744065119617025 :=
  small_nat x.toNat y.toNat (x * y).toNat hx hy (Nat.mul_le_mul hx hy) (UInt64.toNat_mul x y)

def combine (p00 p01 p10 p11 : UInt64) : UInt64 × UInt64 :=
  let mid := p00 / half + p01 % half + p10 % half
  (p11 + p01 / half + p10 / half + mid / half, p00 % half + mid * half)

def addTwo (r : UInt64 × UInt64) (c d : UInt64) : UInt64 × UInt64 :=
  let lo1 := r.2 + c
  let hi1 := r.1 + (if lo1 < r.2 then 1 else 0)
  let lo2 := lo1 + d
  let hi2 := hi1 + (if lo2 < lo1 then 1 else 0)
  (hi2, lo2)

theorem mac_eq (a b c d : UInt64) :
    mac a b c d =
      addTwo (combine ((a % half) * (b % half)) ((a % half) * (b / half))
        ((a / half) * (b % half)) ((a / half) * (b / half))) c d := rfl

theorem combine_spec (p00 p01 p10 p11 : UInt64)
    (h00 : p00.toNat ≤ 18446744065119617025) (h01 : p01.toNat ≤ 18446744065119617025)
    (h10 : p10.toNat ≤ 18446744065119617025) (h11 : p11.toNat ≤ 18446744065119617025) :
    (combine p00 p01 p10 p11).1.toNat * 2 ^ 64 + (combine p00 p01 p10 p11).2.toNat =
      p11.toNat * 2 ^ 64 + (p01.toNat + p10.toNat) * 2 ^ 32 + p00.toNat := by
  simp only [combine, half, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem carry_nat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (x + y) % 2 ^ 64 + (if (x + y) % 2 ^ 64 < x then 1 else 0) * 2 ^ 64 = x + y := by
  split <;> omega

theorem addTwo_tot (hi lo c d x l1 l2 k1 k2 : Nat) (h1 : l1 + k1 * 2 ^ 64 = lo + c)
    (h2 : l2 + k2 * 2 ^ 64 = l1 + d) (hx : hi * 2 ^ 64 + lo = x) :
    (hi + k1 + k2) * 2 ^ 64 + l2 = x + c + d :=
  Nat.le_antisymm (by omega) (by omega)

theorem addTwo_lt (hi k1 k2 l2 v : Nat) (tot : (hi + k1 + k2) * 2 ^ 64 + l2 = v)
    (hb : v < 2 ^ 128) : hi + k1 + k2 < 2 ^ 64 := by
  omega

theorem addTwo_nat (hi lo c d x : Nat) (hlo : lo < 2 ^ 64) (hc : c < 2 ^ 64) (hd : d < 2 ^ 64)
    (hx : hi * 2 ^ 64 + lo = x) (hb : x + c + d < 2 ^ 128) :
    ((hi + if (lo + c) % 2 ^ 64 < lo then 1 else 0) % 2 ^ 64 +
        if ((lo + c) % 2 ^ 64 + d) % 2 ^ 64 < (lo + c) % 2 ^ 64 then 1 else 0) % 2 ^ 64 * 2 ^ 64 +
      ((lo + c) % 2 ^ 64 + d) % 2 ^ 64 = x + c + d := by
  have h1 := carry_nat lo c hlo hc
  have hl1 : (lo + c) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  have h2 := carry_nat ((lo + c) % 2 ^ 64) d hl1 hd
  generalize (if (lo + c) % 2 ^ 64 < lo then 1 else 0 : Nat) = k1 at h1 ⊢
  generalize (if ((lo + c) % 2 ^ 64 + d) % 2 ^ 64 < (lo + c) % 2 ^ 64 then 1 else 0 : Nat) = k2 at h2 ⊢
  generalize ((lo + c) % 2 ^ 64 + d) % 2 ^ 64 = l2 at h2 ⊢
  generalize (lo + c) % 2 ^ 64 = l1 at h1 h2 hl1 ⊢
  have tot := addTwo_tot hi lo c d x l1 l2 k1 k2 h1 h2 hx
  have hlt := addTwo_lt hi k1 k2 l2 _ tot hb
  have m1 : (hi + k1) % 2 ^ 64 = hi + k1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt)
  rw [m1, Nat.mod_eq_of_lt hlt]
  exact tot

theorem addTwo_spec (r : UInt64 × UInt64) (c d : UInt64) (x : Nat)
    (hx : r.1.toNat * 2 ^ 64 + r.2.toNat = x)
    (hb : x + c.toNat + d.toNat < 2 ^ 128) :
    (addTwo r c d).1.toNat * 2 ^ 64 + (addTwo r c d).2.toNat = x + c.toNat + d.toNat := by
  obtain ⟨hi, lo⟩ := r
  simp only [addTwo, toNat_carry, UInt64.toNat_add]
  exact addTwo_nat hi.toNat lo.toNat c.toNat d.toNat x (UInt64.toNat_lt lo) (UInt64.toNat_lt c)
    (UInt64.toNat_lt d) hx hb

theorem mac_final_nat (ab p00 p01 p10 p11 hi lo : Nat)
    (hsplit : ab = p11 * (4294967296 * 4294967296) + (p10 + p01) * 4294967296 + p00)
    (hcomb : hi * 2 ^ 64 + lo = p11 * 2 ^ 64 + (p01 + p10) * 2 ^ 32 + p00) :
    hi * 2 ^ 64 + lo = ab := by
  omega

theorem mac_bound_nat (ab a b c d : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64)
    (hd : d < 2 ^ 64) (hab : ab ≤ 18446744073709551615 * 18446744073709551615) :
    ab + c + d < 2 ^ 128 := by
  omega

theorem half_bound_nat (a : Nat) (ha : a < 2 ^ 64) :
    a % 4294967296 ≤ 4294967295 ∧ a / 4294967296 ≤ 4294967295 ∧ a ≤ 18446744073709551615 := by
  omega

/-- Kind: functional correctness (multiply-accumulate step).
    Says: for all inputs the pair returned by `mac a b c d`, read as `high · 2^64 + low`, is
    exactly `a · b + c + d` on natural numbers; nothing is lost to wrapping.
    Does not say: anything about running time or about the compiled code. -/
theorem mac_spec_proved (a b c d : UInt64) :
    (mac a b c d).1.toNat * 2 ^ 64 + (mac a b c d).2.toNat =
      a.toNat * b.toNat + c.toNat + d.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hd := UInt64.toNat_lt d
  obtain ⟨a0', a1', ale⟩ := half_bound_nat a.toNat ha
  obtain ⟨b0', b1', ble⟩ := half_bound_nat b.toNat hb
  have hA : a.toNat / 4294967296 * 4294967296 + a.toNat % 4294967296 = a.toNat :=
    by first | exact Nat.div_add_mod' _ _ | omega
  have hB : b.toNat / 4294967296 * 4294967296 + b.toNat % 4294967296 = b.toNat :=
    by first | exact Nat.div_add_mod' _ _ | omega
  have hsplit := mul_split (a.toNat % 4294967296) (a.toNat / 4294967296)
    (b.toNat % 4294967296) (b.toNat / 4294967296) 4294967296
  rw [hA, hB] at hsplit
  have hab : a.toNat * b.toNat ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul ale ble
  have a0 : (a % half).toNat ≤ 4294967295 := by rw [toNat_lo]; exact a0'
  have a1 : (a / half).toNat ≤ 4294967295 := by rw [toNat_hi]; exact a1'
  have b0 : (b % half).toNat ≤ 4294967295 := by rw [toNat_lo]; exact b0'
  have b1 : (b / half).toNat ≤ 4294967295 := by rw [toNat_hi]; exact b1'
  obtain ⟨e00, k00⟩ := toNat_mul_small (a % half) (b % half) a0 b0
  obtain ⟨e01, k01⟩ := toNat_mul_small (a % half) (b / half) a0 b1
  obtain ⟨e10, k10⟩ := toNat_mul_small (a / half) (b % half) a1 b0
  obtain ⟨e11, k11⟩ := toNat_mul_small (a / half) (b / half) a1 b1
  have hcomb := combine_spec _ _ _ _ k00 k01 k10 k11
  rw [e00, e01, e10, e11, toNat_lo a, toNat_hi a, toNat_lo b, toNat_hi b] at hcomb
  rw [mac_eq]
  refine addTwo_spec _ c d (a.toNat * b.toNat) ?_ ?_
  · exact mac_final_nat _ _ _ _ _ _ _ hsplit hcomb
  · exact mac_bound_nat _ a.toNat b.toNat _ _ ha hb hc hd hab

instance : MacOK := ⟨mac_spec_proved⟩

#print axioms mac_spec_proved

end EVMCleanroom.Precompiles.LimbB
