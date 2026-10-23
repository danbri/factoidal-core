/- F&O §§6.2.1–6.2.4 special-value and promotion laws.
   The finite rounding algorithm is exercised separately by oracle vectors. -/
import L4Factoidal.Fn.Arithmetic

namespace L4Factoidal.Fn.Arithmetic
open XSD

theorem calculate_nan_left (double : Bool) (op : Op) (b : Fval) :
    calculate double op nan b = nan := by
  cases op <;> rfl

theorem calculate_nan_right (double : Bool) (op : Op) (a : Fval) :
    calculate double op a nan = nan := by
  rcases a with ⟨neg, cls⟩
  cases op <;> cases cls <;> rfl

theorem divide_zeros (double sa sb : Bool) :
    divide double ⟨sa, .zero⟩ ⟨sb, .zero⟩ = nan := rfl

theorem multiply_zero_infinity (double sa sb : Bool) :
    multiply double ⟨sa, .zero⟩ ⟨sb, .inf⟩ = nan := rfl

theorem add_opposite_infinities (double neg : Bool) :
    add double ⟨neg, .inf⟩ ⟨!neg, .inf⟩ = nan := by cases neg <;> rfl

theorem floating_float_result (op : Op) (a b : Fval) :
    floating op (.flt a) (.flt b) = some (.flt (calculate false op a b)) := rfl

theorem floating_mixed_result (op : Op) (a b : Fval) :
    floating op (.flt a) (.dbl b) = some (.dbl (calculate true op a b)) := rfl

#print axioms calculate_nan_left
#print axioms calculate_nan_right
#print axioms divide_zeros
#print axioms multiply_zero_infinity
#print axioms add_opposite_infinities
#print axioms floating_float_result
#print axioms floating_mixed_result

end L4Factoidal.Fn.Arithmetic
