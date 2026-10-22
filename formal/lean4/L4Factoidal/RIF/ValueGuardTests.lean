import L4Factoidal.RIF.Builtins
import L4Factoidal.RDF.Entailment

namespace L4Factoidal.RIF.ValueGuardTests

private def check (target lexical source : String) : Ans :=
  isLiteralOf target (gLit lexical (xsdNs ++ source))

#guard check "integer" "1.0" "decimal" == .yes
#guard check "byte" "127.00" "decimal" == .yes
#guard check "byte" "128.0" "decimal" == .no
#guard check "integer" "1.5" "decimal" == .no
#guard check "dayTimeDuration" "P0M1D" "duration" == .yes
#guard check "yearMonthDuration" "P1MT0S" "duration" == .yes
#guard check "dayTimeDuration" "P1M" "duration" == .no
#guard check "yearMonthDuration" "PT0S" "dayTimeDuration" == .yes
#guard check "dayTimeDuration" "P0M" "yearMonthDuration" == .yes
#guard check "token" "two  words" "string" == .no
#guard check "normalizedString" "two\nwords" "string" == .no
#guard check "language" "Hello world" "string" == .no
#guard isLiteralOf "language" (.const "Hello world@" (rdfNs ++ "PlainLiteral")) == .no
#guard isLiteralOf "PlainLiteral" (gStr "hello") == .yes
#guard evalPred "is-literal-not-string" [.list []] == .no
#guard evalPred "is-literal-not-string" [gIri "https://example.org/"] == .unknown

private def rdfDecimal (s : String) : RDF.Literal :=
  { lexicalForm := s, datatype := RDF.xsdDecimal, langTag := none, direction := none }

#guard RDF.valueInSpace (rdfDecimal "1.0") RDF.xsdInteger
#guard RDF.valueInSpace (rdfDecimal "2147483647.0") RDF.xsdInt
#guard !RDF.valueInSpace (rdfDecimal "2147483648.0") RDF.xsdInt
#guard !RDF.valueInSpace (rdfDecimal "1.5") RDF.xsdInteger

-- Source validation happens before membership or negation. These constants
-- are outside the RIF datatype lexical space; no logical verdict is claimed.
#guard check "integer" "1.0" "integer" == .unknown
#guard check "integer" "128" "byte" == .unknown
#guard check "string" "two  words" "token" == .unknown
#guard evalPred "is-literal-not-string" [gLit "garbage" (xsdNs ++ "integer")] == .unknown
#guard check "unknown" "1" "integer" == .unknown
#guard check "integer" "1" "unknown" == .unknown
#guard check "QName" "a" "string" == .unknown
#guard check "string" "a" "QName" == .unknown
#guard check "double" "1" "integer" == .no
#guard check "float" "1" "double" == .no
#guard check "base64Binary" "41" "hexBinary" == .no
#guard check "string" "https://example.org/" "anyURI" == .no
#guard check "dateTimeStamp" "2000-01-01T00:00:00Z" "dateTime" == .yes
#guard check "dateTimeStamp" "2000-01-01T00:00:00" "dateTime" == .no
#guard check "dateTime" "2000-01-01" "date" == .no
#guard check "token" "two words" "string" == .yes
#guard check "NCName" "a:b" "Name" == .no
#guard check "language" "en-US" "string" == .yes
#guard isLiteralOf "string" (.const "a@b@" (rdfNs ++ "PlainLiteral")) == .yes
#guard isLiteralOf "token" (.const "two  words@" (rdfNs ++ "PlainLiteral")) == .no
#guard isLiteralOf "PlainLiteral" (gLit "en" (xsdNs ++ "language")) == .yes
#guard isLiteralOf "PlainLiteral" (.const "missing-delimiter" (rdfNs ++ "PlainLiteral")) == .unknown
#guard isLiteralOf "string" (gIri "https://example.org/") == .unknown
#guard isLiteralOf "string" (.list []) == .no
#guard isLiteralNotOf "string" (.const "x" localSpace) == .unknown
#guard isLiteralNotOf "string" (.fapp "f" iriSpace []) == .unknown
#guard isLiteralNotOf "string" (gLit "1" (xsdNs ++ "integer")) == .yes
#guard isLiteralNotOf "integer" (gLit "1.0" (xsdNs ++ "decimal")) == .no
#guard isLiteralNotOf "PlainLiteral" (gStr "hello") == .no

-- This error reached inference: an integral decimal in an integer range
-- previously caused an inconsistency verdict (and hence arbitrary entailment).
private def subject : RDF.WfIri := ⟨"https://example.org/s", rfl⟩
private def property : RDF.WfIri := ⟨"https://example.org/p", rfl⟩
private def decimalTerm (s : String) : RDF.Term :=
  let l := rdfDecimal s
  if h : RDF.literalWf l = true then .literal ⟨l, h⟩ else .iri RDF.xsdDecimal
private def rangeGraph (s : String) : RDF.Graph :=
  [⟨.iri subject, property, decimalTerm s⟩,
   ⟨.iri property, RDFS.rdfsRange, .iri RDF.xsdInteger⟩]

#guard !RDF.hasRangeClash [RDF.xsdDecimal, RDF.xsdInteger] (rangeGraph "1.0")
#guard RDF.hasRangeClash [RDF.xsdDecimal, RDF.xsdInteger] (rangeGraph "1.5")
#guard !RDF.hasRangeClash [RDF.xsdDecimal] (rangeGraph "1.5")

-- Both public consumers agree on the same values, including invalid source
-- forms (RIF unknown; RDF's Boolean adapter cannot establish membership).
#guard ["-2147483649.0", "-2147483648.0", "-1.0", "0.0", "+1.000", "1.5",
    "2147483647.00", "2147483648.0", "1e0", " 1", "garbage"].all (fun s =>
  RDF.valueInSpace (rdfDecimal s) RDF.xsdInt == (check "int" s "decimal" == .yes))

end L4Factoidal.RIF.ValueGuardTests
