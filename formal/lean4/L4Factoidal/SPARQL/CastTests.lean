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

/-! ### Other XSD constructors: the XPath F&O 3.1 §19 cast, or a type error
(https://github.com/danbri/factoidal/issues/1041). Before the fix each of
these relabelled the argument. -/
private def x_short : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#short", rfl⟩
private def x_int : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩
private def x_unsignedInt : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedInt", rfl⟩
private def x_negativeInteger : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#negativeInteger", rfl⟩
private def x_date : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#date", rfl⟩
private def x_time : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#time", rfl⟩
private def x_gYear : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#gYear", rfl⟩
private def x_gYearMonth : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#gYearMonth", rfl⟩
private def x_gMonthDay : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#gMonthDay", rfl⟩
private def x_gMonth : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#gMonth", rfl⟩
private def x_gDay : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#gDay", rfl⟩
private def x_duration : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#duration", rfl⟩
private def x_dayTimeDuration : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dayTimeDuration", rfl⟩
private def x_yearMonthDuration : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#yearMonthDuration", rfl⟩
private def x_token : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#token", rfl⟩
private def x_QName : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#QName", rfl⟩
private def x_dateTimeStamp : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTimeStamp", rfl⟩
private def is (dt : WfIri) (lex : String) : EvalResult := lit lex dt

-- From xs:string (§19.2): the lexical form, after the whitespace facet.
#guard cast x_short (lit "x" xsdString) == .error
#guard cast x_short (lit " 12 " xsdString) == is x_short "12"
#guard cast byte (lit "+007" xsdString) == is byte "7"
#guard cast x_date (lit "2015-10-12" xsdString) == is x_date "2015-10-12"
#guard cast x_date (lit "2015-13-12" xsdString) == .error
#guard cast x_gYear (lit "HaHa" xsdString) == .error
#guard cast x_token (lit "  a   b " xsdString) == is x_token "a b"
-- Numeric and boolean sources (§19.1.2, §19.1.3), with the facets (§19.3).
#guard cast byte (.num 300) == .error
#guard cast byte (.dec "1.5") == is byte "1"
#guard cast byte (lit "01.0" xsdDecimal) == is byte "1"
#guard cast byte (lit "1e0" xsdDouble) == is byte "1"
#guard cast byte (lit "HaHa" xsdDouble) == .error
#guard cast byte (lit "HaHa" xsdInteger) == .error
#guard cast byte (lit "500" xsdFloat) == .error
#guard cast x_unsignedInt (lit "-1" xsdInteger) == .error
#guard cast x_negativeInteger (lit "1000" x_int) == .error
#guard cast x_int (lit "false" xsdBoolean) == is x_int "0"
-- Date and time (§19.1.4, §19.1.5).
#guard cast x_date (lit "2015-10-12T15:00:24" xsdDateTime) == is x_date "2015-10-12"
#guard cast x_date (lit "2015-10-12T15:00:24+01:00" xsdDateTime) == is x_date "2015-10-12+01:00"
#guard cast x_time (lit "2010-03-22T20:31:54.5Z" xsdDateTime) == is x_time "20:31:54.5Z"
#guard cast x_gYear (lit "2015-10-12" x_date) == is x_gYear "2015"
#guard cast x_gMonthDay (lit "2010-03-22" x_date) == is x_gMonthDay "--03-22"
#guard cast x_gDay (lit "2010-03-22T20:31:54.5" xsdDateTime) == is x_gDay "---22"
-- A pair the casting table does not allow is a type error (XPTY0004).
#guard cast x_date (lit "2010" x_gYear) == .error
#guard cast x_date (lit "---22" x_gDay) == .error
#guard cast x_date (.num 2010) == .error
#guard cast x_gYear (.bool true) == .error
#guard cast x_date (.term (.iri ⟨"http://example/x", rfl⟩)) == .error
-- Durations (§19.1.6).
#guard cast x_dayTimeDuration (lit "P1Y2M3DT1H2M3S" x_duration) == is x_dayTimeDuration "P3DT1H2M3S"
#guard cast x_dayTimeDuration (lit "P1Y" x_duration) == is x_dayTimeDuration "PT0S"
#guard cast x_yearMonthDuration (lit "P1Y2M3DT1H2M3S" x_duration) == is x_yearMonthDuration "P1Y2M"
#guard cast x_yearMonthDuration (lit "P1DT10H" x_dayTimeDuration) == is x_yearMonthDuration "P0M"
-- A datatype with no value-space implementation, or no XSD built-in of that
-- name: a type error, not a relabelled literal.
#guard cast x_QName (lit "a:b" xsdString) == .error
#guard cast ⟨"http://www.w3.org/2001/XMLSchema#noSuchType", rfl⟩ (lit "1" xsdString) == .error
-- The result is never ill-typed: it is in the lexical space of its datatype.
#guard [cast byte (lit "1e0" xsdDouble), cast x_gYear (lit "2015-10-12" x_date),
        cast x_dayTimeDuration (lit "P1Y" x_duration)].all (fun r => match r with
  | .term (.literal l) => (XSD.builtinOfIri? l.val.datatype.val).any (fun b =>
      (XSD.checkedLexicalValue .xsd10 b l.val.lexicalForm).isSome)
  | _ => false)

end L4Factoidal.SPARQL.CastTests
