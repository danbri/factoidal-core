/-
L4Factoidal.XSD11.FnSchemas — the schemas of the `fn` namespace
(`http://www.w3.org/2005/xpath-functions`) that F&O 4.0 defines for the
results of `fn:analyze-string` (§6.6.3, C.1) and `fn:json-to-xml`
(§17.5.4, C.2). A schema-aware processor knows them without
`schemaLocation` (XQuery 4.0 §5.11: `import schema` of the `fn` namespace,
and the typed results of the two functions).

The texts are the copies in qt4tests `b1616b79`
(`fn/analyze-string/analyze-string.xsd`, `fn/json-to-xml/schema-for-json.xsd`),
unchanged.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.SchemaForSchemas

namespace L4Factoidal.XSD11

open L4Factoidal.XML

def fnNamespace : String := "http://www.w3.org/2005/xpath-functions"

def analyzeStringSchemaText : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<xs:schema xmlns:xs=\"http://www.w3.org/2001/XMLSchema\"\n    targetNamespace=\"http://www.w3.org/2005/xpath-functions\"\n    xmlns:fn=\"http://www.w3.org/2005/xpath-functions\"\n    elementFormDefault=\"qualified\"> \n\n    <xs:element name=\"analyze-string-result\" type=\"fn:analyze-string-result-type\"/>\n    <xs:element name=\"match\" type=\"fn:match-type\"/>\n    <xs:element name=\"non-match\" type=\"xs:string\"/>\n    <xs:element name=\"group\" type=\"fn:group-type\"/>\n    \n    <xs:complexType name=\"analyze-string-result-type\" mixed=\"true\">\n        <xs:choice minOccurs=\"0\" maxOccurs=\"unbounded\">\n            <xs:element ref=\"fn:match\"/>\n            <xs:element ref=\"fn:non-match\"/>\n        </xs:choice>\n    </xs:complexType>\n        \n    <xs:complexType name=\"match-type\" mixed=\"true\">\n        <xs:sequence>\n            <xs:element ref=\"fn:group\" minOccurs=\"0\" maxOccurs=\"unbounded\"/>\n        </xs:sequence>\n    </xs:complexType>\n    \n    <xs:complexType name=\"group-type\" mixed=\"true\">\n        <xs:sequence>\n            <xs:element ref=\"fn:group\" minOccurs=\"0\" maxOccurs=\"unbounded\"/>\n        </xs:sequence>\n        <xs:attribute name=\"nr\" type=\"xs:positiveInteger\"/>\n    </xs:complexType>    \n \n</xs:schema>\n"

def jsonSchemaText : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<xs:schema xmlns:xs=\"http://www.w3.org/2001/XMLSchema\"\n    elementFormDefault=\"qualified\"\n    targetNamespace=\"http://www.w3.org/2005/xpath-functions\"\n    xmlns:j=\"http://www.w3.org/2005/xpath-functions\">\n    \n    <!-- \n     * This is a schema for the XML representation of JSON used as the target for the\n     * function fn:json-to-xml()\n     *\n     * The schema is made available under the terms of the W3C software notice and license\n     * at http://www.w3.org/Consortium/Legal/copyright-software-19980720\n     *\n    -->\n    \n    <xs:element name=\"map\" type=\"j:mapType\">\n        <xs:unique name=\"unique-key\">\n            <xs:selector xpath=\"*\"/>\n            <xs:field xpath=\"@key\"/>\n        </xs:unique>\n    </xs:element>\n    \n    <xs:element name=\"array\" type=\"j:arrayType\"/>\n    \n    <xs:element name=\"string\" type=\"j:stringType\"/>\n    \n    <xs:element name=\"number\" type=\"j:numberType\"/>\n    \n    <xs:element name=\"boolean\" type=\"j:booleanType\"/>\n    \n    <xs:element name=\"null\" type=\"j:nullType\"/>\n    \n    <xs:complexType name=\"nullType\">\n        <xs:sequence/>\n        <xs:anyAttribute processContents=\"skip\" namespace=\"##other\"/>\n    </xs:complexType>\n    \n    <xs:complexType name=\"booleanType\">\n        <xs:simpleContent>\n            <xs:extension base=\"xs:boolean\">\n                <xs:anyAttribute processContents=\"skip\" namespace=\"##other\"/>\n            </xs:extension>\n        </xs:simpleContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"stringType\">\n        <xs:simpleContent>\n            <xs:extension base=\"xs:string\">\n                <xs:attribute name=\"escaped\" type=\"xs:boolean\" use=\"optional\" default=\"false\"/>\n                <xs:anyAttribute processContents=\"skip\" namespace=\"##other\"/>\n            </xs:extension>\n        </xs:simpleContent>\n    </xs:complexType>\n    \n    <xs:simpleType name=\"finiteNumberType\">\n        <xs:restriction base=\"xs:double\">\n            <!-- exclude positive and negative infinity, and NaN -->\n            <xs:minExclusive value=\"-INF\"/>\n            <xs:maxExclusive value=\"INF\"/>\n        </xs:restriction>\n    </xs:simpleType>\n    \n    <xs:complexType name=\"numberType\">\n        <xs:simpleContent>\n            <xs:extension base=\"j:finiteNumberType\">\n                <xs:anyAttribute processContents=\"skip\" namespace=\"##other\"/>\n            </xs:extension>\n        </xs:simpleContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"arrayType\">\n        <xs:choice minOccurs=\"0\" maxOccurs=\"unbounded\">\n            <xs:element ref=\"j:map\"/>\n            <xs:element ref=\"j:array\"/>\n            <xs:element ref=\"j:string\"/>\n            <xs:element ref=\"j:number\"/>\n            <xs:element ref=\"j:boolean\"/>\n            <xs:element ref=\"j:null\"/>\n        </xs:choice>\n        <xs:anyAttribute processContents=\"skip\" namespace=\"##other\"/>\n    </xs:complexType>\n    \n    <xs:complexType name=\"mapWithinMapType\">\n        <xs:complexContent>\n            <xs:extension base=\"j:mapType\">\n                <xs:attributeGroup ref=\"j:key-group\"/>\n            </xs:extension>\n        </xs:complexContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"arrayWithinMapType\">\n        <xs:complexContent>\n            <xs:extension base=\"j:arrayType\">\n                <xs:attributeGroup ref=\"j:key-group\"/>\n            </xs:extension>\n        </xs:complexContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"stringWithinMapType\">\n        <xs:simpleContent>\n            <xs:extension base=\"j:stringType\">\n                <xs:attributeGroup ref=\"j:key-group\"/>\n            </xs:extension>\n        </xs:simpleContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"numberWithinMapType\">\n        <xs:simpleContent>\n            <xs:extension base=\"j:numberType\">\n                <xs:attributeGroup ref=\"j:key-group\"/>\n            </xs:extension>\n        </xs:simpleContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"booleanWithinMapType\">\n        <xs:simpleContent>\n            <xs:extension base=\"j:booleanType\">\n                <xs:attributeGroup ref=\"j:key-group\"/>\n            </xs:extension>\n        </xs:simpleContent>\n    </xs:complexType>\n    \n    <xs:complexType name=\"nullWithinMapType\">\n        <xs:attributeGroup ref=\"j:key-group\"/>\n    </xs:complexType>\n    \n    <xs:complexType name=\"mapType\">\n        <xs:choice minOccurs=\"0\" maxOccurs=\"unbounded\">\n            <xs:element name=\"map\" type=\"j:mapWithinMapType\">\n                <xs:unique name=\"unique-key-2\">\n                    <xs:selector xpath=\"*\"/>\n                    <xs:field xpath=\"@key\"/>\n                </xs:unique>\n            </xs:element>\n            <xs:element name=\"array\" type=\"j:arrayWithinMapType\"/>            \n            <xs:element name=\"string\" type=\"j:stringWithinMapType\"/>   \n            <xs:element name=\"number\" type=\"j:numberWithinMapType\"/>\n            <xs:element name=\"boolean\" type=\"j:booleanWithinMapType\"/>\n            <xs:element name=\"null\" type=\"j:nullWithinMapType\"/>\n        </xs:choice>\n        <xs:anyAttribute processContents=\"skip\" namespace=\"##other\"/>\n    </xs:complexType>\n    \n    <xs:attributeGroup name=\"key-group\">\n        <xs:attribute name=\"key\" type=\"xs:string\"/>\n        <xs:attribute name=\"escaped-key\" type=\"xs:boolean\" use=\"optional\" default=\"false\"/>\n    </xs:attributeGroup>\n    \n</xs:schema>\n"

/-- The two schema documents of the `fn` namespace, at locations that no
    file has. -/
def fnSchemaDocs : List LoadedDoc :=
  [("\u0000builtin:analyze-string.xsd", analyzeStringSchemaText),
   ("\u0000builtin:schema-for-json.xsd", jsonSchemaText)].filterMap (fun (loc, txt) =>
    match parseXML txt with
    | .ok d => some { loc, doc := d }
    | .error _ => none)

/-- Is the document a schema document for the `fn` namespace? -/
def isFnSchemaDoc (d : LoadedDoc) : Bool :=
  match d.doc.root with
  | .element _ ats _ => ats.any (fun a => a.name == "targetNamespace" && a.value == fnNamespace)
  | _ => false

/-- The schema documents with the `fn` schemas added, when none of them is
    a schema document for the `fn` namespace already. -/
def withFnSchemas (docs : List LoadedDoc) (roots : List String) : List LoadedDoc × List String :=
  if docs.any isFnSchemaDoc then (docs, roots)
  else (docs ++ fnSchemaDocs, roots ++ fnSchemaDocs.map (·.loc))

#guard fnSchemaDocs.length == 2

end L4Factoidal.XSD11
