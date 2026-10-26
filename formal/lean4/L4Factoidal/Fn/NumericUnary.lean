/- F&O 2007 §§6.2.7–8 and 6.4: unary numeric value operations.
   The shared XSD parser validates operands; callers select integer versus
   decimal result types and serialize results. Finite floating inputs are
   canonical binary32/64 values; exact integral rounding shares XPath's core. -/
import L4Factoidal.Fn.Arithmetic
import L4Factoidal.Fn.Rounding

namespace L4Factoidal.Fn.NumericUnary
open XSD

inductive Op where
  | plus | minus | abs | integral (mode : Rounding.Mode)
  deriving DecidableEq, Repr

/-- F&O §6.4, on a finite decimal value. -/
def decimal (op : Op) (v : Dec) : Dec := match op with
  | .plus => v
  | .minus => v.neg
  | .abs => ⟨v.mantissa.natAbs, v.scale⟩
  | .integral mode => Dec.ofInt (Rounding.integral mode v.mantissa ((10 : Int) ^ v.scale))

/-- F&O §6.4.2–4: preserve NaN, infinities and both zero signs. A finite
    negative input rounded to zero retains its sign. -/
def integralFloating (double : Bool) (mode : Rounding.Mode) (v : Fval) : Fval :=
  match v.cls with
  | .nan | .inf | .zero => v
  | .finite _ _ =>
      let (num, den) := Arithmetic.magnitude v
      let n : Int := if v.neg then -(num : Int) else num
      let result := Rounding.integral mode n den
      Arithmetic.rounded double (if result == 0 then v.neg else result < 0) result.natAbs 1

/-- F&O §§6.2.7–8, 6.4: sign operations and integral rounding. ABS clears
    the sign of zero and infinity; unary minus flips the sign of zero. -/
def floating (double : Bool) (op : Op) (v : Fval) : Fval := match op with
  | .plus => v
  | .minus => Arithmetic.negate v
  | .abs => { v with neg := false }
  | .integral mode => integralFloating double mode v

/-- Preserve the primitive numeric type. Non-numeric XSD values fail. -/
def apply (op : Op) : Val → Option Val
  | .dec v => some (.dec (decimal op v))
  | .flt v => some (.flt (floating false op v))
  | .dbl v => some (.dbl (floating true op v))
  | _ => none

end L4Factoidal.Fn.NumericUnary
