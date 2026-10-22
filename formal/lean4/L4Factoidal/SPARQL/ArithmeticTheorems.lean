/- SPARQL §18.5.1.3–4 aggregate integration with §17.3 arithmetic. -/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

theorem evalArithmetic_integers (op : ArithOp) (a b : Int) :
    evalArithmetic op (.num a) (.num b) = evalArithInt op a b := rfl

/-- The streaming bag-enumeration contract appends one input value.
No reassociation of rounded arithmetic is used. -/
theorem sumNumeric_append_single (x : EvalResult) (xs : List EvalResult) :
    sumNumeric (xs ++ [x]) = evalArithmetic .add x (sumNumeric xs) := by
  simp [sumNumeric, List.foldl_append]

theorem avgNumeric_nonempty (x : EvalResult) (xs : List EvalResult) :
    avgNumeric (x :: xs) = evalArithmetic .div (sumNumeric (x :: xs))
      (.num (Int.ofNat (xs.length + 1))) := rfl

#print axioms evalArithmetic_integers
#print axioms sumNumeric_append_single
#print axioms sumNumeric_reverse_enumeration
#print axioms avgNumeric_nonempty

end L4Factoidal.SPARQL
