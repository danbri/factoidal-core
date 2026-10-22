/- SPARQL §17.3 numeric promotion and F&O numeric equality.
   Authored boundary regressions; these are not a conformance corpus. -/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL.NumericTests
open RDF

private def lit (s : String) (dt : WfIri) : EvalResult :=
  .term (.literal (mkTypedLiteral s dt))
private def byte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩

-- Equality and relational comparisons must use the same promoted value.
#guard valueCompare (lit "16777217" xsdFloat) (.num 16777216) .eq == some true
#guard valueCompare (lit "16777216" xsdFloat) (.num 16777217) .eq == some true
#guard valueCompare (lit "16777216" xsdFloat) (.dbl "16777217") .eq == some false
#guard valueCompare (.dbl "9007199254740993") (.num 9007199254740992) .eq == some true
#guard valueCompare (.dbl "NaN") (.dbl "NaN") .eq == some false
#guard valueCompare (.dbl "NaN") (.dbl "NaN") .ne == some true
#guard valueCompare (.dbl "NaN") (.num 1) .lt == some false
#guard valueCompare (.dbl "INF") (.dbl "INF") .eq == some true
#guard valueCompare (.dbl "-INF") (.dbl "INF") .ne == some true
#guard valueCompare (.dbl "-0") (.dbl "0") .eq == some true
#guard valueCompare (.dbl "1e-999") (.num 0) .eq == some true
#guard valueCompare (lit "127" byte) (.num 127) .eq == some true
#guard valueCompare (lit "128" byte) (lit "128" byte) .eq == some true
#guard valueCompare (lit "bad" RDF.xsdInteger) (lit "bad" RDF.xsdInteger) .eq == some true
#guard valueCompare (lit "bad" RDF.xsdInteger) (lit "bad" RDF.xsdInteger) .ne == some false
#guard valueCompare (lit "bad" RDF.xsdInteger) (lit "other" RDF.xsdInteger) .eq == none
#guard valueCompare (lit "128" byte) (lit "0128" byte) .eq == none
#guard valueCompare (lit "NaN" xsdDouble) (lit "NaN" xsdDouble) .eq == some false
#guard valueCompare (.dec "1.x") (.num 1) .eq == none
#guard valueCompare (.dbl "+INF") (.dbl "+INF") .eq == none
#guard valueCompare (.dec ".5") (.dec "0.50") .eq == some true
#guard valueCompare (.dec "+1") (.num 1) .eq == some true
#guard valueCompare (.num 1) (.bool true) .eq == none
#guard literalValueEqNumeric (mkTypedLiteral "16777217" xsdFloat)
  (mkTypedLiteral "16777216" RDF.xsdInteger)

-- The remaining scaled-arithmetic adapter must reject invalid input too.
#guard parseIntString "-" == none
#guard parseIntString "+1" == some 1
#guard parseToScaled "1.x" == none
#guard parseToScaled "1.-2" == none
#guard parseToScaled ".5" == some ⟨5, 1⟩
#guard parseDoubleToScaled "1e+2" == some ⟨100, 0⟩
#guard parseDoubleToScaled "1e-" == none
#guard (Expr.arith .add (.decimalLit "1.x") (.numericLit 1)).eval [] == .error

end L4Factoidal.SPARQL.NumericTests
