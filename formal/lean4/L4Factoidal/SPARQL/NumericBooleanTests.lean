/- SPARQL §17.4.2.4 isNumeric, numeric EBV and F&O Boolean casts.
   The evaluator currently uses SPARQL 1.2's malformed-EBV error policy. -/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL.NumericBooleanTests
open RDF

private def byte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩
private def unknown : WfIri := ⟨"urn:unknown", rfl⟩
private def lit (s : String) (dt : WfIri) : EvalResult :=
  .term (.literal (mkTypedLiteral s dt))
private def cast (v : EvalResult) := evalXsdCast v "boolean" xsdBoolean

#guard fnIsNumeric (lit "127" byte) == .bool true
#guard fnIsNumeric (lit "128" byte) == .bool false
#guard fnIsNumeric (lit "bad" xsdInteger) == .bool false
#guard fnIsNumeric (.dec "1.x") == .bool false
#guard fnIsNumeric (.dbl "NaN") == .bool true
#guard fnIsNumeric (.dbl "INF") == .bool true
#guard fnIsNumeric (lit "1e-50" xsdFloat) == .bool true
#guard fnIsNumeric (lit "1" unknown) == .bool false
#guard fnIsNumeric .error == .error
#guard ebv (lit "127" byte) == some true
#guard ebv (lit "0" byte) == some false
#guard ebv (lit "128" byte) == none
#guard ebv (lit "1e-50" xsdFloat) == some false
#guard ebv (.dbl "1e-999") == some false
#guard ebv (.dbl "1e-50") == some true
#guard ebv (.dbl "NaN") == some false
#guard ebv (.dbl "INF") == some true
#guard ebv (.dbl "-0") == some false
#guard ebv (.dbl "+INF") == none
#guard ebv (lit "bad" xsdInteger) == none
#guard ebv (lit "bad" xsdBoolean) == none
#guard cast (lit "127" byte) == .bool true
#guard cast (lit "128" byte) == .error
#guard cast (lit "1e-50" xsdFloat) == .bool false
#guard cast (.dbl "NaN") == .bool false
#guard cast (.dbl "INF") == .bool true
#guard cast (.dbl "-INF") == .bool true
#guard cast (.dbl "1e-999") == .bool false
#guard cast (.dbl "1e-50") == .bool true
#guard cast (.num 0) == .bool false
#guard cast (.dec "-0.00") == .bool false
#guard cast (.term (.literal (Literal.string "true"))) == .bool true
#guard cast (.term (.literal (Literal.string " \ttrue\r\n"))) == .bool true
#guard cast (.term (.literal (Literal.string "tr ue"))) == .error
#guard cast (.term (.literal (Literal.string "\u00a0true\u00a0"))) == .error
#guard cast (.term (.literal (Literal.string "NaN"))) == .error
#guard cast (lit "true" unknown) == .error
#guard cast (.term (.literal (Literal.langString "true" "en"))) == .error
#guard cast (.term (.bnode "b")) == .error
#guard (Expr.not (.var "x")).eval [("x", .literal (mkTypedLiteral "1e-50" xsdFloat))] == .bool true

end L4Factoidal.SPARQL.NumericBooleanTests
