/-
L4Factoidal.XSD11.FnSchemas — the schemas of the XML results of F&O 4.0
functions in the namespace `http://www.w3.org/2005/xpath-functions`: the
schema for the XML representation of JSON (`fn:json-to-xml`) and the
schema for the result of `fn:analyze-string`. A schema-aware processor
validates those results against them, and has them as in-scope schema
definitions when a test environment imports that namespace.

The texts are the copies in the QT4 CG test suite
(`third_party/testing/qt4tests/fn/json-to-xml/schema-for-json.xsd` and
`fn/analyze-string/analyze-string.xsd`), unchanged, under the W3C software
notice and license that the first states.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.SchemaForSchemas

namespace L4Factoidal.XSD11

open L4Factoidal.XML

def schemaForJsonText : String := r###"<?xml version="1.0" encoding="UTF-8"?>
<xs:schema xmlns:xs="http://www.w3.org/2001/XMLSchema"
    elementFormDefault="qualified"
    targetNamespace="http://www.w3.org/2005/xpath-functions"
    xmlns:j="http://www.w3.org/2005/xpath-functions">
    
    <!-- 
     * This is a schema for the XML representation of JSON used as the target for the
     * function fn:json-to-xml()
     *
     * The schema is made available under the terms of the W3C software notice and license
     * at http://www.w3.org/Consortium/Legal/copyright-software-19980720
     *
    -->
    
    <xs:element name="map" type="j:mapType">
        <xs:unique name="unique-key">
            <xs:selector xpath="*"/>
            <xs:field xpath="@key"/>
        </xs:unique>
    </xs:element>
    
    <xs:element name="array" type="j:arrayType"/>
    
    <xs:element name="string" type="j:stringType"/>
    
    <xs:element name="number" type="j:numberType"/>
    
    <xs:element name="boolean" type="j:booleanType"/>
    
    <xs:element name="null" type="j:nullType"/>
    
    <xs:complexType name="nullType">
        <xs:sequence/>
        <xs:anyAttribute processContents="skip" namespace="##other"/>
    </xs:complexType>
    
    <xs:complexType name="booleanType">
        <xs:simpleContent>
            <xs:extension base="xs:boolean">
                <xs:anyAttribute processContents="skip" namespace="##other"/>
            </xs:extension>
        </xs:simpleContent>
    </xs:complexType>
    
    <xs:complexType name="stringType">
        <xs:simpleContent>
            <xs:extension base="xs:string">
                <xs:attribute name="escaped" type="xs:boolean" use="optional" default="false"/>
                <xs:anyAttribute processContents="skip" namespace="##other"/>
            </xs:extension>
        </xs:simpleContent>
    </xs:complexType>
    
    <xs:simpleType name="finiteNumberType">
        <xs:restriction base="xs:double">
            <!-- exclude positive and negative infinity, and NaN -->
            <xs:minExclusive value="-INF"/>
            <xs:maxExclusive value="INF"/>
        </xs:restriction>
    </xs:simpleType>
    
    <xs:complexType name="numberType">
        <xs:simpleContent>
            <xs:extension base="j:finiteNumberType">
                <xs:anyAttribute processContents="skip" namespace="##other"/>
            </xs:extension>
        </xs:simpleContent>
    </xs:complexType>
    
    <xs:complexType name="arrayType">
        <xs:choice minOccurs="0" maxOccurs="unbounded">
            <xs:element ref="j:map"/>
            <xs:element ref="j:array"/>
            <xs:element ref="j:string"/>
            <xs:element ref="j:number"/>
            <xs:element ref="j:boolean"/>
            <xs:element ref="j:null"/>
        </xs:choice>
        <xs:anyAttribute processContents="skip" namespace="##other"/>
    </xs:complexType>
    
    <xs:complexType name="mapWithinMapType">
        <xs:complexContent>
            <xs:extension base="j:mapType">
                <xs:attributeGroup ref="j:key-group"/>
            </xs:extension>
        </xs:complexContent>
    </xs:complexType>
    
    <xs:complexType name="arrayWithinMapType">
        <xs:complexContent>
            <xs:extension base="j:arrayType">
                <xs:attributeGroup ref="j:key-group"/>
            </xs:extension>
        </xs:complexContent>
    </xs:complexType>
    
    <xs:complexType name="stringWithinMapType">
        <xs:simpleContent>
            <xs:extension base="j:stringType">
                <xs:attributeGroup ref="j:key-group"/>
            </xs:extension>
        </xs:simpleContent>
    </xs:complexType>
    
    <xs:complexType name="numberWithinMapType">
        <xs:simpleContent>
            <xs:extension base="j:numberType">
                <xs:attributeGroup ref="j:key-group"/>
            </xs:extension>
        </xs:simpleContent>
    </xs:complexType>
    
    <xs:complexType name="booleanWithinMapType">
        <xs:simpleContent>
            <xs:extension base="j:booleanType">
                <xs:attributeGroup ref="j:key-group"/>
            </xs:extension>
        </xs:simpleContent>
    </xs:complexType>
    
    <xs:complexType name="nullWithinMapType">
        <xs:attributeGroup ref="j:key-group"/>
    </xs:complexType>
    
    <xs:complexType name="mapType">
        <xs:choice minOccurs="0" maxOccurs="unbounded">
            <xs:element name="map" type="j:mapWithinMapType">
                <xs:unique name="unique-key-2">
                    <xs:selector xpath="*"/>
                    <xs:field xpath="@key"/>
                </xs:unique>
            </xs:element>
            <xs:element name="array" type="j:arrayWithinMapType"/>            
            <xs:element name="string" type="j:stringWithinMapType"/>   
            <xs:element name="number" type="j:numberWithinMapType"/>
            <xs:element name="boolean" type="j:booleanWithinMapType"/>
            <xs:element name="null" type="j:nullWithinMapType"/>
        </xs:choice>
        <xs:anyAttribute processContents="skip" namespace="##other"/>
    </xs:complexType>
    
    <xs:attributeGroup name="key-group">
        <xs:attribute name="key" type="xs:string"/>
        <xs:attribute name="escaped-key" type="xs:boolean" use="optional" default="false"/>
    </xs:attributeGroup>
    
</xs:schema>
"###

def analyzeStringSchemaText : String := r###"<?xml version="1.0" encoding="UTF-8"?>
<xs:schema xmlns:xs="http://www.w3.org/2001/XMLSchema"
    targetNamespace="http://www.w3.org/2005/xpath-functions"
    xmlns:fn="http://www.w3.org/2005/xpath-functions"
    elementFormDefault="qualified"> 

    <xs:element name="analyze-string-result" type="fn:analyze-string-result-type"/>
    <xs:element name="match" type="fn:match-type"/>
    <xs:element name="non-match" type="xs:string"/>
    <xs:element name="group" type="fn:group-type"/>
    
    <xs:complexType name="analyze-string-result-type" mixed="true">
        <xs:choice minOccurs="0" maxOccurs="unbounded">
            <xs:element ref="fn:match"/>
            <xs:element ref="fn:non-match"/>
        </xs:choice>
    </xs:complexType>
        
    <xs:complexType name="match-type" mixed="true">
        <xs:sequence>
            <xs:element ref="fn:group" minOccurs="0" maxOccurs="unbounded"/>
        </xs:sequence>
    </xs:complexType>
    
    <xs:complexType name="group-type" mixed="true">
        <xs:sequence>
            <xs:element ref="fn:group" minOccurs="0" maxOccurs="unbounded"/>
        </xs:sequence>
        <xs:attribute name="nr" type="xs:positiveInteger"/>
    </xs:complexType>    
 
</xs:schema>
"###

/-- The schema documents of the F&O 4.0 result schemas. -/
def fnSchemaDocs : List LoadedDoc :=
  [("#fn-schema-for-json", schemaForJsonText), ("#fn-analyze-string", analyzeStringSchemaText)].filterMap
    (fun (loc, txt) => match parseXML txt with
      | .ok d => some { loc, doc := d }
      | .error _ => none)

end L4Factoidal.XSD11
