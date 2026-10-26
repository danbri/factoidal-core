/- SHACL §§4.3, 4.5 use the SPARQL §17.3 relational operator table.
   Distinguish value comparisons from term identity and lexical ordering. -/
import L4Factoidal.SHACL.ShaclTests

namespace L4Factoidal.SHACL.ComparisonTests
open L4Factoidal.RDF

private def lit (s : String) (dt : WfIri) : Term :=
  .literal (SPARQL.mkTypedLiteral s dt)
private def num (s : String) := lit s xsdInteger
private def dec (s : String) := lit s xsdDecimal
private def flt (s : String) := lit s SPARQL.xsdFloat
private def dbl (s : String) := lit s xsdDouble
private def dt (s : String) := lit s xsdDateTime
private def str (s : String) : Term := .literal (Literal.string s)
private def iri : WfIri := ⟨"urn:unsupported", rfl⟩

#guard termLe (num "01") (num "1")
#guard termLe (num "1") (dec "1.0")
#guard termLt (flt "2") (flt "10")
#guard termLe (dbl "-0") (dbl "0")
#guard termLe (dbl "INF") (dbl "INF")
#guard !termLt (dbl "NaN") (dbl "INF")
#guard !termLe (dbl "NaN") (dbl "NaN")
#guard termLe (flt "16777217") (num "16777216")
#guard !termLt (flt "16777216") (num "16777217")
#guard termLe (num "+1") (dec "+1.0")
#guard !termLe (dec "1.x") (dec "2")
#guard termLe (dt "2000-01-01T01:00:00+01:00") (dt "2000-01-01T00:00:00Z")
#guard !termLt (dt "2000-01-01T00:30:00Z") (dt "2000-01-01T01:00:00+01:00")
#guard !termLe (dt "invalid") (dt "invalid")
#guard !termLe (dt "2000-01-01T00:00:00Z") (dt "2000-01-01T00:00:00")
#guard termLt (dt "2000-01-01T00:00:00Z") (dt "2000-01-03T00:00:00")
#guard termLt (dt "2000-01-01T00:00:00") (dt "2000-01-03T00:00:00Z")
#guard !termLe (dt "2000-01-03T00:00:00") (dt "2000-01-01T00:00:00Z")
#guard Fn.Comparison.calendarOrder .date "2006-08-23Z" "2006-08-22" == some .gt
#guard !termLe (.iri iri) (.iri iri)
#guard !termLe (.bnode "b") (.bnode "b")
#guard !termLe (lit "a" iri) (lit "b" iri)
#guard !termLe (lit "same" iri) (lit "same" iri)
#guard !termLt (.literal (Literal.langString "a" "en"))
  (.literal (Literal.langString "b" "en"))
#guard termLe (lit "1" xsdBoolean) (lit "true" xsdBoolean)
#guard termLt (lit "false" xsdBoolean) (lit "1" xsdBoolean)
#guard !termLe (lit "bad" xsdBoolean) (lit "bad" xsdBoolean)
#guard termLt (str "a") (str "b")
#guard numericCmpLe (Literal.string "a") (Literal.string "b") == some true

-- The same RDF arguments must give the same answer at the SPARQL boundary.
#guard SPARQL.valueCompare (.term (.iri iri)) (.term (.iri iri)) .le == none
#guard SPARQL.valueCompare (.term (lit "a" iri)) (.term (lit "b" iri)) .lt == none
#guard SPARQL.valueCompare (.term (flt "16777217")) (.num 16777216) .le == some true
#guard SPARQL.valueCompare (.term (dbl "NaN")) (.term (dbl "INF")) .lt == some false
#guard SPARQL.valueCompare (.term (dt "2000-01-01T01:00:00+01:00"))
  (.term (dt "2000-01-01T00:00:00Z")) .le == some true

private def leDoc : String :=
  "ex:S a sh:PropertyShape ; sh:targetNode ex:a ; sh:path ex:p ; sh:lessThanOrEquals ex:q . " ++
  "ex:a ex:p \"01\"^^xsd:integer ; ex:q 1.0 ."
#guard (Tests.run leDoc).conforms
private def incomparableDoc : String :=
  "ex:S a sh:PropertyShape ; sh:targetNode ex:a ; sh:path ex:p ; sh:lessThanOrEquals ex:q . " ++
  "ex:a ex:p ex:b ; ex:q ex:b ."
#guard Tests.components (Tests.run incomparableDoc) == [shLessThanOrEqualsCC]
private def stringRangeDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"a\", \"b\", \"c\" ; sh:minInclusive \"b\" ."
#guard (Tests.run stringRangeDoc).results.map (·.value) == [some (str "a")]

/-- Every SHACL property-pair less-than check uses the SPARQL operator,
    including its error result. No duplicated comparison table is assumed. -/
theorem termLt_agrees_with_sparql (a b : Term) :
    termLt a b = (SPARQL.valueCompare (.term a) (.term b) .lt == some true) := rfl

theorem termLe_agrees_with_sparql (a b : Term) :
    termLe a b = (SPARQL.valueCompare (.term a) (.term b) .le == some true) := rfl

/-- SHACL §4.3.2 and §4.5.4 share the same inclusive comparison. -/
theorem minInclusive_agrees_with_sparql (g : Graph) (minimum value : WfLiteral) :
    simpleValueCheck g (.minInclusive (.literal minimum)) (.literal value) =
      some (SPARQL.valueCompare (.term (.literal minimum))
        (.term (.literal value)) .le == some true) := rfl

#print axioms termLt_agrees_with_sparql
#print axioms termLe_agrees_with_sparql
#print axioms minInclusive_agrees_with_sparql

end L4Factoidal.SHACL.ComparisonTests
