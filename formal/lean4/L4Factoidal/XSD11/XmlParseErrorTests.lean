import L4Factoidal.XSD11.XPathBridge

namespace L4Factoidal.XSD11.XmlParseErrorTests
open L4Factoidal.XML

private def root (text : String) : Node := .element "root" [] [.text text]
private def code (r : Except XPath4.Err XPath4.Doc) : String :=
  match r with
  | .ok _ => "ok"
  | .error e => e.code
private def integerMode := "type Q{http://www.w3.org/2001/XMLSchema}integer"

-- F&O 4.0 parse-xml cases 438/439: malformed or unknown requested types.
#guard code (validateXmlFor .builtinsFn "type ?????" (root "1") "") == "FODC0008"
#guard code (validateXmlFor .builtinsFn "type xs:superString" (root "1") "") == "FODC0008"
#guard code (validateXmlFor .builtinsFn "type Q{urn:missing}T" (root "1") "") == "FODC0008"
-- Same validation engine, different error contracts for parse-xml and XQuery/XProc.
#guard code (validateXmlFor .builtinsFn integerMode (root "invalid") "") == "FODC0014"
#guard code (validateFor .builtinsFn integerMode (root "invalid") "") == "FODC0007"
#guard code (validateXmlFor .builtinsFn "strict" (root "1") "") == "FODC0014"
#guard code (validateFor .builtinsFn "strict" (root "1") "") == "XQDY0084"
#guard code (validateXmlFor .builtinsFn integerMode (root "42") "") == "ok"
#guard code (XPath4.docOfKids { baseUri := "" } { baseUri := "", xsd := "strict" } [root "1"] "") == "FODC0009"

#print axioms validateXmlFor_ok_iff
#print axioms parseXml_validate
end L4Factoidal.XSD11.XmlParseErrorTests
