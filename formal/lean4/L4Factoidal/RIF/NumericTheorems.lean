import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF

/-- Decoded numeric comparison shares F&O's decision, including unordered NaN. -/
theorem numeric_compare_shared (a b : GTerm) (x y : XSD.Val) (op : Fn.Comparison.Op)
    (ha : numericValue? a = some x) (hb : numericValue? b = some y) :
    cmpNum a b op = match Fn.Comparison.numericCompare x y op with
      | some true => .yes | some false => .no | none => .unknown := by
  cases h : Fn.Comparison.numericCompare x y op with
  | none => simp [cmpNum, ha, hb, h]
  | some v => cases v <;> simp [cmpNum, ha, hb, h]

/-- An undecoded operand cannot become an arithmetic answer. -/
theorem numeric_arithmetic_invalid_left (a b : GTerm) (op : Fn.Arithmetic.Op)
    (h : numericValue? a = none) : numericArithmetic op a b = none := by
  simp [numericArithmetic, h]

theorem decimal_idiv_zero (a : XSD.Dec) :
    Fn.Arithmetic.decimalIntegerDivide a XSD.Dec.zero = none := by
  simp [Fn.Arithmetic.decimalIntegerDivide, XSD.Dec.zero]

theorem decimal_mod_zero (a : XSD.Dec) :
    Fn.Arithmetic.decimalMod a XSD.Dec.zero = none := by
  simp [Fn.Arithmetic.decimalMod, decimal_idiv_zero]

#print axioms numeric_compare_shared
#print axioms numeric_arithmetic_invalid_left
#print axioms decimal_idiv_zero
#print axioms decimal_mod_zero

end L4Factoidal.RIF
