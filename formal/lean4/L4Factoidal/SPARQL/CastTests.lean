import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL.CastTests
open RDF

private def lit (s : String) (dt : WfIri) := EvalResult.term (.literal (mkTypedLiteral s dt))
private def cast (dt : WfIri) (v : EvalResult) :=
  evalXsdCast v (String.ofList (dt.val.toList.drop xsdNamespace.length)) dt
private def byte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩

#guard cast xsdInteger (lit "16777217" xsdFloat) == .num 16777216
#guard cast xsdInteger (lit "128" byte) == .error
#guard cast xsdInteger (lit "127" byte) == .num 127
#guard cast xsdInteger (lit "  +12\t" xsdString) == .num 12
#guard cast xsdInteger (lit "1.9" xsdString) == .error
#guard cast xsdInteger (.dec "-1.9") == .num (-1)
#guard cast xsdInteger (.dbl "9007199254740993") == .num 9007199254740992
#guard cast xsdInteger (lit "1" ⟨"http://www.w3.org/2001/XMLSchema#anyURI", rfl⟩) == .error
#guard cast xsdInteger (lit "1" ⟨"urn:unknown", rfl⟩) == .error
#guard cast xsdInteger (.term (.literal (Literal.langString "1" "en"))) == .error
#guard cast xsdInteger (.dbl "NaN") == .error
#guard cast xsdDecimal (.dbl "INF") == .error
#guard cast xsdDecimal (.dbl "0.1") ==
  .dec "0.1000000000000000055511151231257827021181583404541015625"
#guard cast xsdDecimal (.bool true) == .dec "1.0"
#guard (cast xsdDouble (lit "16777217" xsdFloat)).numericValue? == (EvalResult.dbl "16777216").numericValue?
#guard (cast xsdFloat (.dbl "16777219")).numericValue? == (lit "16777218" xsdFloat).numericValue?
#guard (cast xsdFloat (lit "16777219" xsdString)).numericValue? == (lit "16777220" xsdFloat).numericValue?
#guard (cast xsdFloat (.dbl "-0")).numericValue? == (lit "-0" xsdFloat).numericValue?
#guard (cast xsdDouble (lit "+INF" xsdString)).numericValue? == (EvalResult.dbl "INF").numericValue?

end L4Factoidal.SPARQL.CastTests
