import EVMCleanroom.Precompiles.Limb

/-!
# Temporary: the equations of the limb primitives, for the Montgomery proofs

A stand-in used on the `proofs-b` branch while `LimbProofs.lean` (owned by
`proofs-a`) does not build: `adc_spec`, `sbb_spec` and their carry bounds are
proved here; `mac_spec` is taken through the class `MacOK`, which
`LimbMacB.lean` instantiates. This module is removed at the merge with
`proofs-a`.
-/

set_option maxRecDepth 8192

namespace EVMCleanroom.Precompiles.LimbB

open Limb

theorem toNat_carry (x y : UInt64) :
    (if x < y then (1 : UInt64) else 0).toNat = if x.toNat < y.toNat then 1 else 0 := by
  by_cases h : x < y
  · rw [if_pos h, if_pos (UInt64.lt_iff_toNat_lt.1 h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (UInt64.lt_iff_toNat_lt.2 h'))]; rfl

theorem adc_spec (a b c : UInt64) :
    (adc a b c).1.toNat * 2 ^ 64 + (adc a b c).2.toNat = a.toNat + b.toNat + c.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  simp only [adc, toNat_carry, UInt64.toNat_add, Nat.reducePow] at ha hb hc ⊢
  split <;> split <;> omega

theorem adc_carry_le (a b c : UInt64) (hc : c.toNat ≤ 1) : (adc a b c).1.toNat ≤ 1 := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  simp only [adc, toNat_carry, UInt64.toNat_add, Nat.reducePow] at ha hb ⊢
  split <;> split <;> omega

theorem sbb_spec (a b c : UInt64) :
    a.toNat + (sbb a b c).1.toNat * 2 ^ 64 = (sbb a b c).2.toNat + b.toNat + c.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  simp only [sbb, toNat_carry, UInt64.toNat_add, UInt64.toNat_sub, Nat.reducePow] at ha hb hc ⊢
  split <;> split <;> omega

theorem sbb_borrow_le (a b c : UInt64) (hc : c.toNat ≤ 1) : (sbb a b c).1.toNat ≤ 1 := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  simp only [sbb, toNat_carry, UInt64.toNat_add, UInt64.toNat_sub, Nat.reducePow] at ha hb ⊢
  split <;> split <;> omega

/-- The equation of `mac`, as a class so the dependent proofs can be checked before it is proved. -/
class MacOK : Prop where
  spec : ∀ a b c d : UInt64,
    (mac a b c d).1.toNat * 2 ^ 64 + (mac a b c d).2.toNat = a.toNat * b.toNat + c.toNat + d.toNat

theorem mac_spec [MacOK] (a b c d : UInt64) :
    (mac a b c d).1.toNat * 2 ^ 64 + (mac a b c d).2.toNat = a.toNat * b.toNat + c.toNat + d.toNat :=
  MacOK.spec a b c d

end EVMCleanroom.Precompiles.LimbB
