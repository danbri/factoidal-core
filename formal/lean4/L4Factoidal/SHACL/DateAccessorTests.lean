/- SPARQL §17.4.5 / SHACL node-expression date accessor integration.
   Test exact decimal fractions and error behavior through bound RDF terms. -/
import L4Factoidal.SHACL.NodeExpr

namespace L4Factoidal.SHACL.DateAccessorTests
open RDF SPARQL

private def dt (s : String) : Term := .literal (mkTypedLiteral s xsdDateTime)
private def sec (s : String) : List Term := [.literal (mkTypedLiteral s xsdDecimal)]

#guard sparqlApply "seconds" [dt "2023-12-25T10:30:00.1234567890123456789Z"] ==
  sec "00.1234567890123456789"
#guard sparqlApply "seconds" [dt "2010-12-21T15:38:02.5-08:00"] == sec "02.5"
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:00.000Z"] == sec "00"
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:59.9999999999999999999+14:00"] ==
  sec "59.9999999999999999999"
#guard sparqlApply "seconds" [dt "-0001-12-31T24:00:00Z"] == sec "00"
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:06"] == sec "06"
#guard sparqlApply "seconds" [dt "bad"] == []
#guard sparqlApply "seconds" [dt "2023-02-29T10:30:06Z"] == []
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:60Z"] == []
#guard sparqlApply "seconds" [dt "2023-12-25T24:00:00.1Z"] == []
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:06+14:01"] == []
#guard sparqlApply "seconds" [dt "0000-12-25T10:30:06Z"] == []
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:06Zjunk"] == []
#guard sparqlApply "seconds" [.literal (Literal.string "2023-12-25T10:30:06Z")] == []
#guard sparqlApply "seconds" [.literal (mkTypedLiteral "2023-12-25T10:30:06Z" xsdInteger)] == []
#guard sparqlApply "seconds" [.bnode "date"] == []
#guard sparqlApply "seconds" [] == []
#guard sparqlApply "seconds" [dt "2023-12-25T10:30:06Z", dt "2023-12-25T10:30:06Z"] == []

-- Other date accessors already use the shared calendar and caller error policy.
#guard sparqlApply "year" [dt "-0001-12-31T24:00:00Z"] ==
  [.literal (mkTypedLiteral "1" xsdInteger)]
#guard sparqlApply "timezone" [dt "2023-12-25T10:30:06"] == []
#guard sparqlApply "tz" [dt "2023-12-25T10:30:06"] == [.literal (Literal.string "")]
#guard sparqlApply "tz" [dt "2023-12-25T10:30:06-00:00"] ==
  [.literal (Literal.string "-00:00")]

end L4Factoidal.SHACL.DateAccessorTests
