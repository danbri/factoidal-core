/- SPARQL §18.5.1.3–4 aggregate integration with §17.3 arithmetic. -/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

theorem evalArithmetic_integers (op : ArithOp) (a b : Int) :
    evalArithmetic op (.num a) (.num b) = evalArithInt op a b := rfl

theorem sumNumeric_cons (x : EvalResult) (xs : List EvalResult) :
    sumNumeric (x :: xs) = evalArithmetic .add x (sumNumeric xs) := rfl

theorem avgNumeric_nonempty (x : EvalResult) (xs : List EvalResult) :
    avgNumeric (x :: xs) = evalArithmetic .div (sumNumeric (x :: xs))
      (.num (Int.ofNat (xs.length + 1))) := rfl

#print axioms evalArithmetic_integers
#print axioms sumNumeric_cons
#print axioms avgNumeric_nonempty

end L4Factoidal.SPARQL
