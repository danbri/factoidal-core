/- Integral rounding laws and the explicit XPath exact-decimal reuse boundary.
   These do not prove complete IEEE rounding or XPath numeric conformance. -/
import L4Factoidal.Fn.NumericUnary
import L4Factoidal.XPath.Number

namespace L4Factoidal.Fn
open XSD

theorem Rounding.integral_integer (mode : Mode) (n : Int) :
    integral mode n 1 = n := by
  cases mode
  all_goals simp only [integral]
  case floor => rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 1 by decide)]; omega
  case ceiling => rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 1 by decide)]; omega
  case nearest => rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 * 1 by decide)]; omega

theorem Rounding.nearest_half_toward_positive (n : Int) :
    integral .nearest (2 * n + 1) 2 = n + 1 := by
  simp only [integral]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 * 2 by decide)]
  omega

theorem Rounding.ceiling_neg_floor (n d : Int) :
    integral .ceiling n d = -(integral .floor (-n) d) := rfl

theorem NumericUnary.integral_zero (double neg : Bool) (mode : Rounding.Mode) :
    integralFloating double mode ⟨neg, .zero⟩ = ⟨neg, .zero⟩ := rfl

theorem NumericUnary.integral_nan (double neg : Bool) (mode : Rounding.Mode) :
    integralFloating double mode ⟨neg, .nan⟩ = ⟨neg, .nan⟩ := rfl

theorem NumericUnary.integral_infinity (double neg : Bool) (mode : Rounding.Mode) :
    integralFloating double mode ⟨neg, .inf⟩ = ⟨neg, .inf⟩ := rfl

theorem NumericUnary.abs_positive_zero (double neg : Bool) :
    floating double .abs ⟨neg, .zero⟩ = ⟨false, .zero⟩ := rfl

theorem NumericUnary.float_type (op : Op) (v : Fval) :
    apply op (.flt v) = some (.flt (floating false op v)) := rfl

theorem NumericUnary.double_type (op : Op) (v : Fval) :
    apply op (.dbl v) = some (.dbl (floating true op v)) := rfl

private theorem xpath_pow10 (s : Nat) : XPath.Num.pow10 s = (10 : Int) ^ s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [XPath.Num.pow10, ih, Int.pow_succ, Int.mul_comm]

/-- Agreement of the two decimal adapters for arbitrary mantissas/scales.
    This deliberately does not identify XPath decimals with IEEE doubles. -/
theorem xpath_decimal_integral (mode : Rounding.Mode) (m : Int) (s : Nat) :
    XPath.Num.integralN mode (.finite m s) =
      .finite (NumericUnary.decimal (.integral mode) ⟨m, s⟩).mantissa 0 := by
  simp [XPath.Num.integralN, xpath_pow10, NumericUnary.decimal, Dec.ofInt]

#print axioms Rounding.integral_integer
#print axioms Rounding.nearest_half_toward_positive
#print axioms Rounding.ceiling_neg_floor
#print axioms NumericUnary.integral_zero
#print axioms NumericUnary.integral_nan
#print axioms NumericUnary.integral_infinity
#print axioms NumericUnary.abs_positive_zero
#print axioms NumericUnary.float_type
#print axioms NumericUnary.double_type
#print axioms xpath_decimal_integral

end L4Factoidal.Fn
