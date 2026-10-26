/- Exact integral rounding shared by XPath 1.0 §4.4 and F&O 2007 §6.4.
   This layer has no datatype, lexical, NaN or signed-zero policy. Callers
   supply an exact numerator and a strictly positive denominator. -/
namespace L4Factoidal.Fn.Rounding

inductive Mode where
  | floor | ceiling | nearest
  deriving DecidableEq, Repr

/-- F&O §6.4.2–4 / XPath §4.4: nearest ties go toward positive infinity.
    The half-addition is exact integer arithmetic, never floating addition;
    IEEE rounding-to-nearest-even remains a separate operation. -/
def integral (mode : Mode) (numerator denominator : Int) : Int :=
  match mode with
  | .floor => Int.fdiv numerator denominator
  | .ceiling => -(Int.fdiv (-numerator) denominator)
  | .nearest => Int.fdiv (2 * numerator + denominator) (2 * denominator)

end L4Factoidal.Fn.Rounding
