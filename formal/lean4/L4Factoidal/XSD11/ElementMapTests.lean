/-
Public schema-aware element conversion regressions (F&O 4.0 §14.6.6–9).
https://qt4cg.org/specifications/xpath-functions-40/Overview.html
Tracking: https://github.com/danbri/factoidal/issues/1101.
-/
import L4Factoidal.XSD11.Load
import L4Factoidal.XQuery4.Module

namespace L4Factoidal.XSD11.ElementMapTests

open L4Factoidal.XPath4

private def source : String := r#"<xs:schema xmlns:xs='http://www.w3.org/2001/XMLSchema' xmlns:c='urn:e2m' targetNamespace='urn:e2m' elementFormDefault='qualified'>
  <xs:element name='EmptyPlus'><xs:complexType><xs:attribute name='flag' type='xs:boolean'/><xs:attribute name='nums' type='c:Numbers'/><xs:attribute name='float' type='xs:float'/></xs:complexType></xs:element>
  <xs:element name='Boolean' type='xs:boolean' nillable='true'/>
  <xs:element name='Number' type='xs:integer'/>
  <xs:element name='Date' type='xs:date'/>
  <xs:element name='Float' type='xs:float'/>
  <xs:element name='List'><xs:complexType><xs:sequence><xs:element ref='c:Date' minOccurs='0' maxOccurs='unbounded'/></xs:sequence></xs:complexType></xs:element>
  <xs:element name='Mixed'><xs:complexType mixed='true'><xs:sequence><xs:element ref='c:Number'/><xs:element ref='c:Date'/></xs:sequence></xs:complexType></xs:element>
  <xs:element name='Sequence'><xs:complexType><xs:sequence><xs:element ref='c:Boolean'/><xs:element ref='c:Number' maxOccurs='2'/></xs:sequence></xs:complexType></xs:element>
  <xs:element name='Wild'><xs:complexType><xs:sequence><xs:any processContents='lax'/></xs:sequence></xs:complexType></xs:element>
  <xs:simpleType name='Nothing'><xs:restriction base='xs:string'><xs:length value='0'/></xs:restriction></xs:simpleType>
  <xs:element name='Zero' type='c:Nothing'/>
  <xs:simpleType name='Numbers'><xs:list itemType='xs:integer'/></xs:simpleType>
  <xs:simpleType name='EmptyNumbers'><xs:restriction base='c:Numbers'><xs:length value='0'/></xs:restriction></xs:simpleType>
  <xs:element name='Numbers' type='c:Numbers'/>
  <xs:element name='EmptyNumbers' type='c:EmptyNumbers'/>
  <xs:simpleType name='Base'><xs:restriction base='xs:integer'><xs:minInclusive value='0'/></xs:restriction></xs:simpleType>
  <xs:simpleType name='Derived'><xs:restriction base='c:Base'><xs:maxInclusive value='10'/></xs:restriction></xs:simpleType>
  <xs:element name='Derived' type='c:Derived'/>
  <xs:element name='NestedList'><xs:complexType><xs:sequence maxOccurs='2'><xs:element ref='c:Date'/></xs:sequence></xs:complexType></xs:element>
  <xs:element name='Record' nillable='true'><xs:complexType><xs:all><xs:element ref='c:Number' minOccurs='0'/><xs:element ref='c:Date' minOccurs='0'/></xs:all><xs:attribute name='flag' type='xs:boolean'/></xs:complexType></xs:element>
</xs:schema>"#

private def schema : Schema :=
  match L4Factoidal.XML.parseXML source with
  | .ok d => buildSchema none xpathHooks [{ loc := "schema.xsd", doc := d }] ["schema.xsd"]
  | .error _ => default

#guard schema.errors.isEmpty

private def answer (src : String) (componentInfo : Bool := true) : String :=
  let hook := schemaHookOf schema
  let hook := if componentInfo then hook else { hook with contentInfo := fun _ => none }
  let env : Env := { schema := hook }
  match L4Factoidal.XQuery4.evalQuery ("declare namespace c='urn:e2m'; " ++ src) env with
  | .ok s => showSeq s
  | .error e => e.code

-- Schema properties, rather than attributes or children actually present.
#guard answer "deep-equal(element-to-map(validate strict {<c:EmptyPlus/>}), {'Q{urn:e2m}EmptyPlus':{}})" == "true"
#guard answer "element-to-map(validate strict {<c:EmptyPlus flag='0'/>})?*?('@flag') instance of xs:boolean" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Boolean>0</c:Boolean>}), {'Q{urn:e2m}Boolean':false()})" == "true"
#guard answer "element-to-map(validate strict {<c:Date>1966-07-03</c:Date>})?* instance of xs:date" == "true"
#guard answer "element-to-map(validate strict {<c:List><c:Date>1966-07-03</c:Date></c:List>})?* instance of array(*)" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Zero/>}), {'Q{urn:e2m}Zero':''})" == "true"
#guard answer "declare boundary-space preserve; deep-equal(element-to-map(validate strict {<c:Mixed>A<c:Number>2</c:Number> <c:Date>1966-07-03</c:Date>Z</c:Mixed>}), {'Q{urn:e2m}Mixed':['A', {'Number':2}, ' ', {'Date':xs:date('1966-07-03')}, 'Z']})" == "true"
#guard answer "element-to-map(validate strict {<c:Wild><c:Number>2</c:Number></c:Wild>})?* instance of array(*)" == "true"
#guard answer "element-to-map(validate strict {<c:NestedList><c:Date>1966-07-03</c:Date></c:NestedList>})?* instance of array(*)" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Derived>4</c:Derived>})?*, 4)" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Numbers>4</c:Numbers>})?*, [4])" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Numbers/>})?*, [])" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:EmptyNumbers/>})?*, '')" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:EmptyPlus nums='4'/>})?*?('@nums'), [4])" == "true"

-- Schema inference does not prescribe a conversion-plan cast. In
-- particular xs:float must not silently become xs:double without a plan.
#guard answer "element-to-map(validate strict {<c:Float>4</c:Float>})?* instance of xs:float" == "true"
#guard answer "element-to-map(validate strict {<c:Float>4</c:Float>}, {'plan':{'Q{urn:e2m}Float':{'layout':'simple','type':'double'}}})?* instance of xs:double" == "true"
#guard answer "element-to-map(validate strict {<c:EmptyPlus float='4'/>})?*?('@float') instance of xs:float" == "true"
#guard answer "element-to-map(validate strict {<c:EmptyPlus float='4'/>}, {'plan':{'@float':{'type':'double'}}})?*?('@float') instance of xs:double" == "true"
#guard answer "element-to-map(validate strict {<c:Float>4</c:Float>})?* instance of xs:float" false == "true"

-- An explicit layout wins; typed descendants still participate after fallback.
#guard answer "element-to-map(validate strict {<c:List><c:Date>1966-07-03</c:Date></c:List>}, {'plan': {'Q{urn:e2m}List':{'layout':'record'}}})?* instance of map(*)" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Sequence><c:Boolean>1</c:Boolean><c:Number>2</c:Number></c:Sequence>}, {'plan': {'Q{urn:e2m}Sequence':{'layout':'simple'}, '*':{'layout':'record'}}, 'name-format':'local'}), {'Sequence':{'Boolean':true(), 'Number':2}})" == "true"

-- A wildcard fallback does not replace a schema-determined layout.
#guard answer "deep-equal(element-to-map(validate strict {<c:Boolean>0</c:Boolean>}, {'plan': {'*': {'layout':'xml'}}}), {'Q{urn:e2m}Boolean':false()})" == "true"
#guard answer "element-to-map(validate strict {<c:Boolean xmlns:xsi='http://www.w3.org/2001/XMLSchema-instance' xsi:nil='true'/>})?* eq #fn:null" == "true"

-- §14.6.1.7 requires the null marker here. QT4 334/335 instead expect
-- an empty sequence; leave that fixture disagreement visible in the corpus.
#guard answer "deep-equal(element-to-map(validate strict {<c:Record xmlns:xsi='http://www.w3.org/2001/XMLSchema-instance' xsi:nil='true'/>}), {'Q{urn:e2m}Record': {'#content': #fn:null}})" == "true"
#guard answer "deep-equal(element-to-map(validate strict {<c:Record xmlns:xsi='http://www.w3.org/2001/XMLSchema-instance' xsi:nil='true' flag='0'/>}), {'Q{urn:e2m}Record': {'@flag':false(), '#content': #fn:null}})" == "true"

-- Untyped explicit conversion stays untyped; plan cast failures stay errors.
#guard answer "element-to-map(<a>0</a>, {'plan':{'a':{'layout':'simple'}}})?a instance of xs:untypedAtomic" == "true"
#guard answer "element-to-map(<a>bad</a>, {'plan':{'a':{'layout':'simple','type':'boolean'}}})" == "FOJS0010"
#guard answer "element-to-map(validate strict {<c:Date>1966-07-03</c:Date>}, {'plan': {'Q{urn:e2m}Date':{'layout':'simple','type':'boolean'}}})" == "FOJS0010"
#guard answer "element-to-map(validate strict {<c:Date>1966-07-03</c:Date>}, {'plan': {'Q{urn:e2m}Date':{'layout':'simple','type':'boolean'}}, 'liberal':true()})?* instance of xs:date" == "true"

end L4Factoidal.XSD11.ElementMapTests
