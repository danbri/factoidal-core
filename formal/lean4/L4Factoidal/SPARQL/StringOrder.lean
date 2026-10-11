import L4Factoidal.SPARQL.Expr
import Init.Data.List.Lex

namespace L4Factoidal.SPARQL

/-- Use Lean's native string ordering without allocating character lists.
    The standard string order is lexicographic Unicode codepoint order. -/
def strCompareFast (left right : String) : Int :=
  if left < right then -1 else if right < left then 1 else 0

private theorem listCharCompare_eq_order (left right : List Char) :
    listCharCompare left right = if left < right then -1 else if right < left then 1 else 0 := by
  induction left generalizing right with
  | nil => cases right <;> simp [listCharCompare]
  | cons a rest ih =>
      cases right with
      | nil => simp [listCharCompare]
      | cons b tail =>
          by_cases less : a.toNat < b.toNat
          · have charLess : a < b := less
            have ne : a ≠ b := by intro h; subst b; omega
            have intLess : (a.toNat : Int) < (b.toNat : Int) := by omega
            simp [listCharCompare, intCompare, intLess, List.cons_lt_cons_iff,
              charLess, ne]
          · by_cases greater : b.toNat < a.toNat
            · have charGreater : b < a := greater
              have notLess : ¬ a < b := less
              have ne : a ≠ b := by intro h; subst b; omega
              have intNotLess : ¬ (a.toNat : Int) < (b.toNat : Int) := by omega
              have intNe : (a.toNat : Int) ≠ (b.toNat : Int) := by omega
              simp [listCharCompare, intCompare, intNotLess, intNe,
                List.cons_lt_cons_iff, charGreater, notLess, ne, Ne.symm ne]
            · have natEq : a.toNat = b.toNat := by omega
              have equal : a = b := Char.ext (UInt32.toNat.inj natEq)
              subst b
              simp [listCharCompare, intCompare, ih]

/-- All strings, including embedded NUL and non-ASCII codepoints, retain the
    exact existing three-way comparison result. -/
theorem strCompareFast_eq (left right : String) :
    strCompareFast left right = strCompare left right := by
  exact (listCharCompare_eq_order left.toList right.toList).symm

@[csimp] theorem strCompare_csimp : strCompare = strCompareFast := by
  funext left right
  exact (strCompareFast_eq left right).symm

#print axioms strCompareFast_eq
#print axioms strCompare_csimp

end L4Factoidal.SPARQL
