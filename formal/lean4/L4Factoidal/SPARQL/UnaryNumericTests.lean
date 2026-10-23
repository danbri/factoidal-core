/- SPARQL §17.3/§17.4.4, F&O 2007 §6.4: value-based unary boundaries. -/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL.UnaryNumericTests
open RDF

private def flt (s : String) : Expr := .lit (mkTypedLiteral s xsdFloat)
private def numericEq (v : EvalResult) (s : String) (dt : WfIri) : Bool :=
  fnDatatype v == .term (.iri dt) &&
    valueCompare v (.term (.literal (mkTypedLiteral s dt))) .eq == some true
private def negativeZero (v : EvalResult) : Bool := match v.numericValue? with
  | some (.flt f) | some (.dbl f) => f.neg && f.cls == .zero
  | _ => false
private def isNaN (v : EvalResult) : Bool := match v.numericValue? with
  | some (.flt f) | some (.dbl f) => f.cls == .nan
  | _ => false

-- Halfway cases go toward positive infinity, including negative operands.
#guard (Expr.round (.decimalLit "-1.5")).eval [] == .dec "-1"
#guard (Expr.round (.decimalLit "-0.5")).eval [] == .dec "0"
#guard (Expr.floor (.decimalLit "-0.1")).eval [] == .dec "-1"
#guard (Expr.ceil (.decimalLit "-0.1")).eval [] == .dec "0"
#guard (Expr.floor (.decimalLit "-.9")).eval [] == .dec "-1"
#guard (Expr.unaryMinus (.decimalLit "+1.5")).eval [] == .dec "-1.5"
#guard numericEq ((Expr.round (.doubleLit "-25e-1")).eval []) "-2" xsdDouble
#guard numericEq ((Expr.ceil (.doubleLit "15e-1")).eval []) "2" xsdDouble
#guard numericEq ((Expr.floor (.doubleLit "-1e-1")).eval []) "-1" xsdDouble
-- Test source binary32 rounding before the integral operation, and result type.
#guard numericEq ((Expr.round (flt "0.499999999")).eval []) "1" xsdFloat
#guard numericEq ((Expr.abs (flt "-1.5")).eval []) "1.5" xsdFloat
#guard numericEq ((Expr.unaryMinus (flt "1.5")).eval []) "-1.5" xsdFloat
#guard numericEq ((Expr.floor (flt "1.5")).eval []) "1" xsdFloat
#guard numericEq ((Expr.ceil (flt "1.5")).eval []) "2" xsdFloat
#guard numericEq ((Expr.unaryPlus (flt "1.5")).eval []) "1.5" xsdFloat
-- The representable double immediately below .5 must round down.
#guard numericEq ((Expr.round (.doubleLit "0.49999999999999994")).eval []) "0" xsdDouble
#guard negativeZero ((Expr.round (.doubleLit "-0.5")).eval [])
#guard negativeZero ((Expr.ceil (flt "-0.1")).eval [])
#guard negativeZero ((Expr.floor (.doubleLit "-0")).eval [])
#guard negativeZero ((Expr.unaryMinus (flt "0")).eval [])
#guard !negativeZero ((Expr.abs (flt "-0")).eval [])
#guard numericEq ((Expr.abs (.doubleLit "-INF")).eval []) "INF" xsdDouble
#guard numericEq ((Expr.floor (.doubleLit "INF")).eval []) "INF" xsdDouble
#guard numericEq ((Expr.ceil (flt "-INF")).eval []) "-INF" xsdFloat
#guard isNaN ((Expr.round (.doubleLit "NaN")).eval [])
#guard isNaN ((Expr.unaryMinus (flt "NaN")).eval [])
-- Numeric unary plus validates its argument even though it is a value no-op.
#guard (Expr.unaryPlus (.boolLit true)).eval [] == .error
#guard (Expr.unaryPlus (.lit (mkTypedLiteral "12" xsdString))).eval [] == .error
#guard (Expr.unaryPlus (.decimalLit "bad")).eval [] == .error
#guard (Expr.unaryMinus (.doubleLit "bad")).eval [] == .error
#guard (Expr.abs (.decimalLit "bad")).eval [] == .error
#guard (Expr.floor (.doubleLit "bad")).eval [] == .error
#guard (Expr.ceil (.decimalLit "bad")).eval [] == .error
#guard (Expr.round (flt "bad")).eval [] == .error

private def byte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩
-- Derived integer validation precedes promotion to the base result type.
#guard (Expr.abs (.lit (mkTypedLiteral "-128" byte))).eval [] == .num 128
#guard (Expr.round (.lit (mkTypedLiteral "127" byte))).eval [] == .num 127
#guard (Expr.unaryMinus (.lit (mkTypedLiteral "-128" byte))).eval [] == .num 128
#guard (Expr.unaryPlus (.lit (mkTypedLiteral "128" byte))).eval [] == .error
#guard (Expr.unaryPlus (.lit (mkTypedLiteral "01" byte))).eval [] ==
  .num 1

end L4Factoidal.SPARQL.UnaryNumericTests
