/- F&O §6.2 numeric equality: reflexivity excludes NaN. -/
import L4Factoidal.Fn.Comparison

namespace L4Factoidal.Fn.Comparison
open XSD

theorem numericDatatype_string : numericDatatype RDF.xsdString = false := by decide +kernel

theorem numericCompare_dec_refl (d : Dec) : numericCompare (.dec d) (.dec d) .eq = some true := by
  simp [numericCompare, Dec.cmp, Op.apply]

theorem fvalCmp_refl (f : Fval) (h : f.cls ≠ .nan) : fvalCmp f f = some .eq := by
  rcases f with ⟨neg, cls⟩
  cases cls <;> cases neg <;> simp_all [fvalCmp, cmpDyadic]

theorem numericCompare_dbl_refl (f : Fval) (h : f.cls ≠ .nan) :
    numericCompare (.dbl f) (.dbl f) .eq = some true := by
  simp [numericCompare, Numeric.floatingValue, fvalCmp_refl f h, Op.apply]

#print axioms numericCompare_dec_refl
#print axioms fvalCmp_refl
#print axioms numericCompare_dbl_refl

end L4Factoidal.Fn.Comparison
