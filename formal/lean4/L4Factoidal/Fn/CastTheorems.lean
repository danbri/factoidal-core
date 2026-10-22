import L4Factoidal.Fn.Cast

namespace L4Factoidal.Fn.Cast
open XSD

/-- A successful conversion has passed the target value-space check. -/
theorem cast_target_valid (ed : Edition) (b : Builtin) (v r : Val)
    (h : cast ed b v = some r) : (valueInBuiltin b r).getD false = true := by
  unfold cast at h
  split at h
  · simp at h
  · cases hc : convert ed b v with
    | none => simp [hc] at h
    | some c =>
      simp [hc] at h
      rcases h with ⟨valid, rfl⟩
      exact valid

/-- Unsupported target kinds never acquire a fabricated converted value. -/
theorem cast_unsupported_target (ed : Edition) (b : Builtin) (v : Val)
    (h : valueMembershipSupported b = false) : cast ed b v = none := by
  simp [cast, h]

/-- Non-finite IEEE values cannot be cast to a decimal value. -/
theorem floatingDecimal_infinity (neg : Bool) :
    floatingDecimal ⟨neg, .inf⟩ = none := rfl

theorem floatingDecimal_nan (neg : Bool) :
    floatingDecimal ⟨neg, .nan⟩ = none := rfl

/-- Source-aware conversion cannot bypass the target check. This proves
membership, not full source-to-target semantic adequacy. -/
theorem castFrom_target_valid (ed : Edition) (source target : Builtin) (v r : Val)
    (h : castFrom ed source target v = some r) :
    (valueInBuiltin target r).getD false = true := by
  unfold castFrom at h
  split at h
  · simp at h
  · split at h
    · cases v <;> simp only at h
      all_goals first | (cases h) | exact cast_target_valid _ _ _ _ h
    · exact cast_target_valid _ _ _ _ h

/-- The source subtype selects zero's string spelling; no original lexical
spelling is reused to establish this value-conversion result. -/
theorem zero_yearMonthDuration_string :
    castFrom .xsd11 .yearMonthDuration .string (.dur ⟨0, Dec.zero⟩) =
      some (.str .string "P0M") := by rfl

#print axioms castFrom_target_valid
#print axioms zero_yearMonthDuration_string

#print axioms cast_target_valid
#print axioms cast_unsupported_target
#print axioms floatingDecimal_infinity
#print axioms floatingDecimal_nan

end L4Factoidal.Fn.Cast
