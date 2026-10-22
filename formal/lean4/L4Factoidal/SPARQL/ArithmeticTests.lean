/- SPARQL §17.3 / F&O §6.2 arithmetic boundary regressions. -/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL.ArithmeticTests
open RDF

private def flt (s : String) : Expr := .lit (mkTypedLiteral s xsdFloat)
private def dbl (s : String) : Expr := .doubleLit s
private def runOp (op : ArithOp) (a b : Expr) := (Expr.arith op a b).eval []
private def floatEq (v : EvalResult) (s : String) :=
  fnDatatype v == .term (.iri xsdFloat) &&
    valueCompare v (.term (.literal (mkTypedLiteral s xsdFloat))) .eq == some true
private def doubleEq (v : EvalResult) (s : String) :=
  fnDatatype v == .term (.iri xsdDouble) && valueCompare v (.dbl s) .eq == some true
private def isNaN (v : EvalResult) : Bool := match v.numericValue? with
  | some (.flt f) | some (.dbl f) => f.cls == .nan
  | _ => false
private def negativeZero (v : EvalResult) : Bool := match v.numericValue? with
  | some (.flt f) | some (.dbl f) => f.neg && f.cls == .zero
  | _ => false

#guard floatEq (runOp .add (flt "16777216") (.numericLit 1)) "16777216"
#guard floatEq (runOp .add (flt "16777216") (.numericLit 3)) "16777220"
#guard doubleEq (runOp .add (flt "16777216") (dbl "1")) "16777217"
#guard doubleEq (runOp .add (dbl "9007199254740992") (.numericLit 1)) "9007199254740992"
#guard doubleEq (runOp .add (dbl "0.1") (dbl "0.2")) "0.30000000000000004"
#guard floatEq (runOp .mul (flt "3.4e38") (flt "2")) "INF"
#guard doubleEq (runOp .mul (dbl "1e308") (dbl "2")) "INF"
#guard floatEq (runOp .div (flt "1") (.numericLit 0)) "INF"
#guard doubleEq (runOp .div (dbl "-1") (dbl "0")) "-INF"
#guard doubleEq (runOp .div (dbl "1") (dbl "-0")) "-INF"
#guard isNaN (runOp .div (dbl "0") (dbl "0"))
#guard isNaN (runOp .div (dbl "INF") (dbl "INF"))
#guard isNaN (runOp .mul (dbl "0") (dbl "INF"))
#guard isNaN (runOp .add (dbl "INF") (dbl "-INF"))
#guard isNaN (runOp .sub (dbl "INF") (dbl "INF"))
#guard isNaN (runOp .add (dbl "NaN") (.numericLit 1))
#guard doubleEq (runOp .sub (dbl "INF") (dbl "-INF")) "INF"
#guard negativeZero (runOp .mul (dbl "-0") (dbl "2"))
#guard negativeZero (runOp .div (dbl "1") (dbl "-INF"))
#guard negativeZero (runOp .add (dbl "-0") (dbl "-0"))
#guard !negativeZero (runOp .add (dbl "-0") (dbl "0"))
#guard !negativeZero (runOp .sub (dbl "-0") (dbl "-0"))
#guard floatEq (runOp .div (flt "1e-45") (flt "2")) "0"
#guard doubleEq (runOp .div (dbl "5e-324") (dbl "2")) "0"
#guard runOp .div (.numericLit 1) (.numericLit 0) == .error
#guard runOp .div (.decimalLit "1") (.decimalLit "0") == .error
#guard runOp .add (flt "bad") (.numericLit 1) == .error
#guard runOp .add (.lit (mkTypedLiteral "12" ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩))
  (.numericLit 1) == .num 13
#guard runOp .add (.lit (mkTypedLiteral "128" ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩))
  (.numericLit 1) == .error

-- SUM and AVG must retain the arithmetic value model and result types.
private def fv (s : String) := (flt s).eval []
#guard floatEq (sumNumeric [fv "16777216", .num 1]) "16777216"
#guard floatEq (avgNumeric [fv "2", fv "4"]) "3"
#guard doubleEq (sumNumeric [.dbl "0.1", .dbl "0.2"]) "0.30000000000000004"
#guard isNaN (sumNumeric [.dbl "INF", .dbl "-INF"])
#guard isNaN (avgNumeric [.dbl "NaN", .num 1])
#guard sumNumeric [.num 1, erString "bad"] == .error
#guard sumNumeric [] == .num 0
#guard avgNumeric [] == .num 0

private def group : SolutionGroup :=
  { key := [], solutions := [[("x", .literal (mkTypedLiteral "INF" xsdFloat))],
      [("x", .literal (mkTypedLiteral "1" xsdFloat))]] }
#guard floatEq (evalAggregate emptyEnv .sum false (.var "x") group) "INF"
#guard floatEq (evalAggregate emptyEnv .avg false (.var "x") group) "INF"

end L4Factoidal.SPARQL.ArithmeticTests
