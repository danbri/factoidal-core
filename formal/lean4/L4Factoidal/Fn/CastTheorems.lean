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

#print axioms cast_target_valid
#print axioms cast_unsupported_target
#print axioms floatingDecimal_infinity
#print axioms floatingDecimal_nan

end L4Factoidal.Fn.Cast
