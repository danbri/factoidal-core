/- Cross-consumer regressions for the edition-aware shared datatype boundary.
   These are authored tests, not a W3C conformance suite. -/
import L4Factoidal.XSD.Lexical
import L4Factoidal.XSD.Facets
import L4Factoidal.SPARQL.Expr
import L4Factoidal.SHACL.Validation
import L4Factoidal.CSVW.Formats
import L4Factoidal.ShEx.XsdLexical
import L4Factoidal.RDF.Datatypes
import L4Factoidal.XForms.Bind

namespace L4Factoidal.XSD.InteropTests

open L4Factoidal

private def acceptedEverywhere (s : String) : Bool :=
  (SPARQL.dtValue s).isSome &&
  !(SHACL.literalIllFormed SHACL.xsdDateTime s) &&
  CSVW.parseCanonicalDate "dateTime" s == .valid s &&
  ShEx.inXsdLexicalSpace "http://www.w3.org/2001/XMLSchema#dateTime" s == some true

#guard acceptedEverywhere "12345-02-03T04:05:06.123456789012345Z"
#guard acceptedEverywhere "-0004-02-03T04:05:06-05:30"
#guard acceptedEverywhere "2010-02-03T04:05:06"
#guard SPARQL.dtYear "-0001-12-31T24:00:00Z" == some 1
#guard SPARQL.dtMonth "12345-02-03T04:05:06Z" == some 2
#guard SPARQL.dtYear "-0004-02-03T04:05:06Z" == some (-4)
#guard SPARQL.dtSeconds "12345-02-03T04:05:06.123456789012345Z" == some "6.123456789012345"
#guard SPARQL.dtTimezone "2010-02-03T04:05:06+14:01" == none
#guard SPARQL.dtTimezone "2010-02-03T04:05:06" == some ""
#guard SHACL.dtCmp "2000-01-01T00:00:00.0001Z" "2000-01-01T00:00:00.0002Z" == some (-1)
#guard SHACL.dtCmp "2000-01-01T00:00:00+01:00" "1999-12-31T23:00:00Z" == some 0
#guard SHACL.dtCmp "2000-01-01T00:00:00" "2000-01-01T00:00:00Z" == none
-- Shared XSD uncertainty differs deliberately from SHACL's mixed-zone policy.
#guard (do
  let a ← parseDateTimeFor .xsd11 .dateTime "2000-01-01T00:00:00"
  let b ← parseDateTimeFor .xsd11 .dateTime "2000-01-03T00:00:00Z"
  dtCompare a b) == some .lt
#guard (do
  let a ← parseDateTimeFor .xsd11 .dateTime "2000-01-01T00:00:00"
  let b ← parseDateTimeFor .xsd11 .dateTime "2000-01-01T00:00:00Z"
  dtCompare a b) == none

private def invalidDates := ["2001-02-29T00:00:00Z", "2000-01-01T24:01:00Z",
  "2000/01/01T00:00:00Z", "2000-01-01T00:00:00+14:01", "2000-01-01T00:00:00junk"]
#guard invalidDates.all (fun s => (SPARQL.dtValue s).isNone &&
  SHACL.literalIllFormed SHACL.xsdDateTime s &&
  CSVW.parseCanonicalDate "dateTime" s == .invalid &&
  ShEx.inXsdLexicalSpace "http://www.w3.org/2001/XMLSchema#dateTime" s == some false)
-- Edition differences are policies, not duplicated parsers.
#guard (SPARQL.dtValue "0000-01-01T00:00:00Z").isNone
#guard CSVW.parseCanonicalDate "dateTime" "0000-01-01T00:00:00Z" == .valid "0000-01-01T00:00:00Z"
#guard CSVW.isXsdNumericLexical "float" "+INF"
#guard ShEx.inXsdLexicalSpace "http://www.w3.org/2001/XMLSchema#float" "+INF" == some false
#guard ShEx.inXsdLexicalSpace "urn:unknown" "x" == none
#guard CSVW.parseCanonicalDate "dateTimeStamp" "2000-01-01T00:00:00" == .invalid
#guard CSVW.satisfiesFacetsFor "dateTime"
  { minInclusive := some "2000-01-01T00:00:00Z" } "2000-01-01T02:00:00+02:00"
#guard !CSVW.satisfiesFacetsFor "dateTime"
  { minInclusive := some "2000-01-01T00:00:00Z" } "2000-01-01T00:00:00+02:00"
#guard RDF.parseDecimalLexical "001.2300" == some ⟨123, 2⟩
#guard CSVW.decimalCompare "-0" "0" == some .eq
#guard (decimalOrScientific "1.23e2").map Dec.canonical == some "123"

#guard dtParseUtcMs "2000-01-01T00:00:00.0001Z" == none
#guard (dtParseUtcMs "-0001-01-01T00:00:00Z").isSome

-- Decode values before counting bytes; malformed padding is not a value.
#guard ShEx.inXsdLexicalSpace (Builtin.base64Binary.iri) "TQ==" == some true
#guard ShEx.inXsdLexicalSpace (Builtin.base64Binary.iri) "TR==" == some false
#guard CSVW.satisfiesFacetsFor "base64Binary" { length := some 1 } "T  Q  =  ="
#guard CSVW.satisfiesFacetsFor "binary" { length := some 1 } "TQ=="
#guard !CSVW.satisfiesFacetsFor "base64Binary" {} "TR=="
#guard !CSVW.satisfiesFacetsFor "hexBinary" { length := some 2 } "abc"

-- Every integer subtype shares both endpoints across the validation adapters.
private def integerAgreement (b : Builtin) (n : Int) : Bool :=
  let s := toString n
  let iri : RDF.WfIri := ⟨b.iri, by cases b <;> rfl⟩
  let expected := inIntBounds b n
  SHACL.literalIllFormed iri s == !expected &&
  ShEx.inXsdLexicalSpace b.iri s == some expected &&
  CSVW.isXsdNumericLexical b.localName s == expected

#guard allBuiltins.all fun b => match intBounds b with
  | none => true
  | some (lo, hi) =>
      ([-1, 0, 1] ++ lo.toList.flatMap (fun n => [n-1, n, n+1]) ++
        hi.toList.flatMap (fun n => [n-1, n, n+1])).all (integerAgreement b)
#guard !SHACL.literalIllFormed RDF.xsdString "unconstrained"
#guard !SHACL.literalIllFormed ⟨"urn:unmodelled", rfl⟩ "anything"
#guard ShEx.fractionDigitsOf "000.0001200" == some 5
#guard ShEx.fractionDigitsOf "1e2" == none

private def lexicalCases := ["", "+", "-", ".", "+0", "-0", "1.", ".1",
  "001.200", " 1 ", "1e2", "1e", "1e+2", "1.2.3", "INF", "+INF", "NaN", "１２"]
#guard lexicalCases.all fun s =>
  SPARQL.isIntegerLexical s == XForms.isIntegerLexical s &&
  SPARQL.isDecimalLexical s == XForms.isDecimalLexical s &&
  XForms.isFloatLexical s == SHACL.isFloatLexical s
#guard SPARQL.isDoubleLexical "+INF" && !XForms.isFloatLexical "+INF"
#guard XForms.typeWellformed .boolean "0" && !XForms.typeWellformed .boolean "TRUE"
#guard !XForms.typeWellformed .unsupported "anything"
#guard CSVW.facetLength "base64Binary" "" == some 0
#guard CSVW.facetLength "base64Binary" "TQ==\u00a0" == none
#guard !XML.isXmlSpace '\u00a0' && !isXmlSpace '\u00a0'

/-- The RDF adapter delegates integer parsing without changing its decision. -/
theorem rdf_integer_shared (s : String) : RDF.parseIntegerLexical s = parseIntegerLex s := rfl
#print axioms rdf_integer_shared
#print axioms parseDateTimeFor
end L4Factoidal.XSD.InteropTests
