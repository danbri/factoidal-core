/-
L4Factoidal.OWL.OwlXmlTests — build-time checks for the OWL 2 XML
Serialization reader.

The XML serialization is "a notational variant of the functional syntax"
(OWL 2 XML Serialization, section 1), so every check pairs an OWL/XML
document with its functional-style twin and requires the two RDF graphs
(OWL 2 Mapping to RDF Graphs section 2) to be isomorphic. Each pair has
negative twins: a perturbed XML document whose graph must differ, and
documents the schema rejects.
-/
import L4Factoidal.OWL.OwlXml
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.OWL.OwlXml

open L4Factoidal.RDF

private def xmlOnt (body : String) : String :=
  "<Ontology xmlns=\"http://www.w3.org/2002/07/owl#\" xml:base=\"http://e/\">" ++ body ++
  "</Ontology>"

private def fsOnt (body : String) : String :=
  "Prefix( : = <http://e/> )\nPrefix( xsd: = <http://www.w3.org/2001/XMLSchema#> )\n" ++
  "Ontology(\n" ++ body ++ "\n)"

/-- Do the two documents denote isomorphic graphs? -/
private def twin (fs xml : String) : Bool :=
  match L4Factoidal.OWL.FS.parseFunctionalSyntax fs, parseOwlXmlGraph xml with
  | some a, some b => Graph.isomorphic? a b
  | _, _ => false

private def readable (xml : String) : Bool := (parseOwlXml xml).isSome

/-! ## Declarations and assertions -/

#guard twin (fsOnt "Declaration(Class(:A)) ClassAssertion(:A :a)")
  (xmlOnt "<Declaration><Class IRI=\"A\"/></Declaration>\n\
           <ClassAssertion><Class IRI=\"A\"/><NamedIndividual IRI=\"a\"/></ClassAssertion>")
-- negative: a different class
#guard !(twin (fsOnt "Declaration(Class(:A)) ClassAssertion(:A :a)")
  (xmlOnt "<Declaration><Class IRI=\"A\"/></Declaration>\n\
           <ClassAssertion><Class IRI=\"B\"/><NamedIndividual IRI=\"a\"/></ClassAssertion>"))
-- negative: a missing axiom
#guard !(twin (fsOnt "Declaration(Class(:A)) ClassAssertion(:A :a)")
  (xmlOnt "<Declaration><Class IRI=\"A\"/></Declaration>"))

#guard twin (fsOnt "Declaration(Datatype(:D)) Declaration(ObjectProperty(:p)) \
Declaration(DataProperty(:q)) Declaration(AnnotationProperty(:r)) Declaration(NamedIndividual(:a))")
  (xmlOnt "<Declaration><Datatype IRI=\"D\"/></Declaration>\
<Declaration><ObjectProperty IRI=\"p\"/></Declaration>\
<Declaration><DataProperty IRI=\"q\"/></Declaration>\
<Declaration><AnnotationProperty IRI=\"r\"/></Declaration>\
<Declaration><NamedIndividual IRI=\"a\"/></Declaration>")

/-! ## Abbreviated IRIs, prefixes, base -/

#guard twin (fsOnt "ClassAssertion(:A :a)")
  (xmlOnt "<Prefix name=\"ex\" IRI=\"http://e/\"/>\
<ClassAssertion><Class abbreviatedIRI=\"ex:A\"/><NamedIndividual abbreviatedIRI=\"ex:a\"/></ClassAssertion>")
-- the default prefixes are implicit
#guard twin (fsOnt "SubClassOf(:A owl:Thing)")
  (xmlOnt "<SubClassOf><Class IRI=\"A\"/><Class abbreviatedIRI=\"owl:Thing\"/></SubClassOf>")
-- an absolute IRI is not resolved against the base
#guard twin (fsOnt "ClassAssertion(<http://x/A> :a)")
  (xmlOnt "<ClassAssertion><Class IRI=\"http://x/A\"/><NamedIndividual IRI=\"a\"/></ClassAssertion>")
-- negative: exactly one of IRI and abbreviatedIRI (section 3.1)
#guard !(readable (xmlOnt "<ClassAssertion><Class IRI=\"A\" abbreviatedIRI=\"owl:Thing\"/>\
<NamedIndividual IRI=\"a\"/></ClassAssertion>"))
#guard !(readable (xmlOnt "<ClassAssertion><Class/><NamedIndividual IRI=\"a\"/></ClassAssertion>"))
-- negative: an undeclared prefix
#guard !(readable (xmlOnt "<ClassAssertion><Class abbreviatedIRI=\"zz:A\"/>\
<NamedIndividual IRI=\"a\"/></ClassAssertion>"))

/-! ## The ontology element -/

#guard twin "Ontology(<http://e/o> <http://e/o/1> Import(<http://e/i>))"
  ("<Ontology xmlns=\"http://www.w3.org/2002/07/owl#\" ontologyIRI=\"http://e/o\" \
versionIRI=\"http://e/o/1\"><Import>http://e/i</Import></Ontology>")
-- negative: a different import
#guard !(twin "Ontology(<http://e/o> <http://e/o/1> Import(<http://e/i>))"
  ("<Ontology xmlns=\"http://www.w3.org/2002/07/owl#\" ontologyIRI=\"http://e/o\" \
versionIRI=\"http://e/o/1\"><Import>http://e/j</Import></Ontology>"))
-- negative: a version IRI without an ontology IRI
#guard !(readable "<Ontology xmlns=\"http://www.w3.org/2002/07/owl#\" versionIRI=\"http://e/o/1\"/>")
-- negative: the root must be an Ontology
#guard !(readable "<Class xmlns=\"http://www.w3.org/2002/07/owl#\" IRI=\"http://e/A\"/>")
-- negative: not XML
#guard !(readable "Ontology( )")

/-! ## Class expressions -/

#guard twin (fsOnt "ClassAssertion(ObjectIntersectionOf(:A :B) :a)")
  (xmlOnt "<ClassAssertion><ObjectIntersectionOf><Class IRI=\"A\"/><Class IRI=\"B\"/>\
</ObjectIntersectionOf><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectUnionOf(:A :B :C) :a)")
  (xmlOnt "<ClassAssertion><ObjectUnionOf><Class IRI=\"A\"/><Class IRI=\"B\"/><Class IRI=\"C\"/>\
</ObjectUnionOf><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectComplementOf(:A) :a)")
  (xmlOnt "<ClassAssertion><ObjectComplementOf><Class IRI=\"A\"/></ObjectComplementOf>\
<NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectOneOf(:x :y) :a)")
  (xmlOnt "<ClassAssertion><ObjectOneOf><NamedIndividual IRI=\"x\"/><NamedIndividual IRI=\"y\"/>\
</ObjectOneOf><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectSomeValuesFrom(ObjectInverseOf(:p) :A) :a)")
  (xmlOnt "<ClassAssertion><ObjectSomeValuesFrom><ObjectInverseOf><ObjectProperty IRI=\"p\"/>\
</ObjectInverseOf><Class IRI=\"A\"/></ObjectSomeValuesFrom><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectAllValuesFrom(:p :A) :a)")
  (xmlOnt "<ClassAssertion><ObjectAllValuesFrom><ObjectProperty IRI=\"p\"/><Class IRI=\"A\"/>\
</ObjectAllValuesFrom><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectHasValue(:p :b) :a)")
  (xmlOnt "<ClassAssertion><ObjectHasValue><ObjectProperty IRI=\"p\"/><NamedIndividual IRI=\"b\"/>\
</ObjectHasValue><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectHasSelf(:p) :a)")
  (xmlOnt "<ClassAssertion><ObjectHasSelf><ObjectProperty IRI=\"p\"/></ObjectHasSelf>\
<NamedIndividual IRI=\"a\"/></ClassAssertion>")
-- cardinalities, unqualified and qualified
#guard twin (fsOnt "ClassAssertion(ObjectMinCardinality(2 :p) :a)")
  (xmlOnt "<ClassAssertion><ObjectMinCardinality cardinality=\"2\"><ObjectProperty IRI=\"p\"/>\
</ObjectMinCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectMaxCardinality(2 :p :A) :a)")
  (xmlOnt "<ClassAssertion><ObjectMaxCardinality cardinality=\"2\"><ObjectProperty IRI=\"p\"/>\
<Class IRI=\"A\"/></ObjectMaxCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(ObjectExactCardinality(1 :p :A) :a)")
  (xmlOnt "<ClassAssertion><ObjectExactCardinality cardinality=\"1\"><ObjectProperty IRI=\"p\"/>\
<Class IRI=\"A\"/></ObjectExactCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>")
-- negative: qualified and unqualified differ
#guard !(twin (fsOnt "ClassAssertion(ObjectMaxCardinality(2 :p :A) :a)")
  (xmlOnt "<ClassAssertion><ObjectMaxCardinality cardinality=\"2\"><ObjectProperty IRI=\"p\"/>\
</ObjectMaxCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>"))
-- negative: the cardinality is a natural number
#guard !(readable (xmlOnt "<ClassAssertion><ObjectMinCardinality cardinality=\"two\">\
<ObjectProperty IRI=\"p\"/></ObjectMinCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>"))
#guard !(readable (xmlOnt "<ClassAssertion><ObjectMinCardinality><ObjectProperty IRI=\"p\"/>\
</ObjectMinCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>"))
-- negative: one-operand intersection
#guard !(readable (xmlOnt "<ClassAssertion><ObjectIntersectionOf><Class IRI=\"A\"/>\
</ObjectIntersectionOf><NamedIndividual IRI=\"a\"/></ClassAssertion>"))
-- data class expressions
#guard twin (fsOnt "ClassAssertion(DataSomeValuesFrom(:p :q xsd:integer) :a)")
  (xmlOnt "<ClassAssertion><DataSomeValuesFrom><DataProperty IRI=\"p\"/><DataProperty IRI=\"q\"/>\
<Datatype abbreviatedIRI=\"xsd:integer\"/></DataSomeValuesFrom><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(DataAllValuesFrom(:p xsd:integer) :a)")
  (xmlOnt "<ClassAssertion><DataAllValuesFrom><DataProperty IRI=\"p\"/>\
<Datatype abbreviatedIRI=\"xsd:integer\"/></DataAllValuesFrom><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(DataHasValue(:p \"v\"^^xsd:string) :a)")
  (xmlOnt "<ClassAssertion><DataHasValue><DataProperty IRI=\"p\"/>\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#string\">v</Literal></DataHasValue>\
<NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(DataMinCardinality(3 :p xsd:integer) :a)")
  (xmlOnt "<ClassAssertion><DataMinCardinality cardinality=\"3\"><DataProperty IRI=\"p\"/>\
<Datatype abbreviatedIRI=\"xsd:integer\"/></DataMinCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(DataMaxCardinality(3 :p) :a)")
  (xmlOnt "<ClassAssertion><DataMaxCardinality cardinality=\"3\"><DataProperty IRI=\"p\"/>\
</DataMaxCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>")
#guard twin (fsOnt "ClassAssertion(DataExactCardinality(3 :p xsd:integer) :a)")
  (xmlOnt "<ClassAssertion><DataExactCardinality cardinality=\"3\"><DataProperty IRI=\"p\"/>\
<Datatype abbreviatedIRI=\"xsd:integer\"/></DataExactCardinality><NamedIndividual IRI=\"a\"/></ClassAssertion>")

/-! ## Data ranges and literals -/

#guard twin (fsOnt "DataPropertyRange(:p DatatypeRestriction(xsd:integer \
xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"9\"^^xsd:integer))")
  (xmlOnt "<DataPropertyRange><DataProperty IRI=\"p\"/><DatatypeRestriction>\
<Datatype abbreviatedIRI=\"xsd:integer\"/>\
<FacetRestriction facet=\"http://www.w3.org/2001/XMLSchema#minInclusive\">\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#integer\">1</Literal></FacetRestriction>\
<FacetRestriction facet=\"http://www.w3.org/2001/XMLSchema#maxInclusive\">\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#integer\">9</Literal></FacetRestriction>\
</DatatypeRestriction></DataPropertyRange>")
-- negative: a different bound
#guard !(twin (fsOnt "DataPropertyRange(:p DatatypeRestriction(xsd:integer \
xsd:minInclusive \"1\"^^xsd:integer))")
  (xmlOnt "<DataPropertyRange><DataProperty IRI=\"p\"/><DatatypeRestriction>\
<Datatype abbreviatedIRI=\"xsd:integer\"/>\
<FacetRestriction facet=\"http://www.w3.org/2001/XMLSchema#minInclusive\">\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#integer\">2</Literal></FacetRestriction>\
</DatatypeRestriction></DataPropertyRange>"))
-- negative: a restriction with no facet
#guard !(readable (xmlOnt "<DataPropertyRange><DataProperty IRI=\"p\"/><DatatypeRestriction>\
<Datatype abbreviatedIRI=\"xsd:integer\"/></DatatypeRestriction></DataPropertyRange>"))
#guard twin (fsOnt "DataPropertyRange(:p DataComplementOf(xsd:integer))")
  (xmlOnt "<DataPropertyRange><DataProperty IRI=\"p\"/><DataComplementOf>\
<Datatype abbreviatedIRI=\"xsd:integer\"/></DataComplementOf></DataPropertyRange>")
#guard twin (fsOnt "DataPropertyRange(:p DataOneOf(\"1\"^^xsd:integer \"x\"@en))")
  (xmlOnt "<DataPropertyRange><DataProperty IRI=\"p\"/><DataOneOf>\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#integer\">1</Literal>\
<Literal xml:lang=\"en\">x</Literal></DataOneOf></DataPropertyRange>")
#guard twin (fsOnt "DataPropertyRange(:p DataUnionOf(xsd:integer xsd:string))")
  (xmlOnt "<DataPropertyRange><DataProperty IRI=\"p\"/><DataUnionOf>\
<Datatype abbreviatedIRI=\"xsd:integer\"/><Datatype abbreviatedIRI=\"xsd:string\"/>\
</DataUnionOf></DataPropertyRange>")
-- a literal with neither datatype nor language is an xsd:string
#guard twin (fsOnt "DataPropertyAssertion(:p :a \"plain\")")
  (xmlOnt "<DataPropertyAssertion><DataProperty IRI=\"p\"/><NamedIndividual IRI=\"a\"/>\
<Literal>plain</Literal></DataPropertyAssertion>")
#guard !(twin (fsOnt "DataPropertyAssertion(:p :a \"plain\")")
  (xmlOnt "<DataPropertyAssertion><DataProperty IRI=\"p\"/><NamedIndividual IRI=\"a\"/>\
<Literal xml:lang=\"en\">plain</Literal></DataPropertyAssertion>"))

/-! ## Axioms: classes, properties, assertions -/

#guard twin (fsOnt "EquivalentClasses(:A :B :C) DisjointClasses(:A :B) DisjointClasses(:A :B :C) \
DisjointUnion(:A :B :C)")
  (xmlOnt "<EquivalentClasses><Class IRI=\"A\"/><Class IRI=\"B\"/><Class IRI=\"C\"/></EquivalentClasses>\
<DisjointClasses><Class IRI=\"A\"/><Class IRI=\"B\"/></DisjointClasses>\
<DisjointClasses><Class IRI=\"A\"/><Class IRI=\"B\"/><Class IRI=\"C\"/></DisjointClasses>\
<DisjointUnion><Class IRI=\"A\"/><Class IRI=\"B\"/><Class IRI=\"C\"/></DisjointUnion>")
#guard twin (fsOnt "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) SubObjectPropertyOf(:p :q) \
InverseObjectProperties(:p :q) ObjectPropertyDomain(:p :A) ObjectPropertyRange(:p :A) \
EquivalentObjectProperties(:p :q) DisjointObjectProperties(:p :q :r)")
  (xmlOnt "<SubObjectPropertyOf><ObjectPropertyChain><ObjectProperty IRI=\"p\"/>\
<ObjectProperty IRI=\"q\"/></ObjectPropertyChain><ObjectProperty IRI=\"r\"/></SubObjectPropertyOf>\
<SubObjectPropertyOf><ObjectProperty IRI=\"p\"/><ObjectProperty IRI=\"q\"/></SubObjectPropertyOf>\
<InverseObjectProperties><ObjectProperty IRI=\"p\"/><ObjectProperty IRI=\"q\"/></InverseObjectProperties>\
<ObjectPropertyDomain><ObjectProperty IRI=\"p\"/><Class IRI=\"A\"/></ObjectPropertyDomain>\
<ObjectPropertyRange><ObjectProperty IRI=\"p\"/><Class IRI=\"A\"/></ObjectPropertyRange>\
<EquivalentObjectProperties><ObjectProperty IRI=\"p\"/><ObjectProperty IRI=\"q\"/></EquivalentObjectProperties>\
<DisjointObjectProperties><ObjectProperty IRI=\"p\"/><ObjectProperty IRI=\"q\"/>\
<ObjectProperty IRI=\"r\"/></DisjointObjectProperties>")
-- negative: a chain of one property
#guard !(readable (xmlOnt "<SubObjectPropertyOf><ObjectPropertyChain><ObjectProperty IRI=\"p\"/>\
</ObjectPropertyChain><ObjectProperty IRI=\"r\"/></SubObjectPropertyOf>"))
#guard twin (fsOnt "FunctionalObjectProperty(:p) InverseFunctionalObjectProperty(:p) \
ReflexiveObjectProperty(:p) IrreflexiveObjectProperty(:p) SymmetricObjectProperty(:p) \
AsymmetricObjectProperty(:p) TransitiveObjectProperty(:p)")
  (xmlOnt "<FunctionalObjectProperty><ObjectProperty IRI=\"p\"/></FunctionalObjectProperty>\
<InverseFunctionalObjectProperty><ObjectProperty IRI=\"p\"/></InverseFunctionalObjectProperty>\
<ReflexiveObjectProperty><ObjectProperty IRI=\"p\"/></ReflexiveObjectProperty>\
<IrreflexiveObjectProperty><ObjectProperty IRI=\"p\"/></IrreflexiveObjectProperty>\
<SymmetricObjectProperty><ObjectProperty IRI=\"p\"/></SymmetricObjectProperty>\
<AsymmetricObjectProperty><ObjectProperty IRI=\"p\"/></AsymmetricObjectProperty>\
<TransitiveObjectProperty><ObjectProperty IRI=\"p\"/></TransitiveObjectProperty>")
#guard twin (fsOnt "SubDataPropertyOf(:p :q) EquivalentDataProperties(:p :q) DisjointDataProperties(:p :q) \
DataPropertyDomain(:p :A) DataPropertyRange(:p xsd:integer) FunctionalDataProperty(:p) \
DatatypeDefinition(:D xsd:integer)")
  (xmlOnt "<SubDataPropertyOf><DataProperty IRI=\"p\"/><DataProperty IRI=\"q\"/></SubDataPropertyOf>\
<EquivalentDataProperties><DataProperty IRI=\"p\"/><DataProperty IRI=\"q\"/></EquivalentDataProperties>\
<DisjointDataProperties><DataProperty IRI=\"p\"/><DataProperty IRI=\"q\"/></DisjointDataProperties>\
<DataPropertyDomain><DataProperty IRI=\"p\"/><Class IRI=\"A\"/></DataPropertyDomain>\
<DataPropertyRange><DataProperty IRI=\"p\"/><Datatype abbreviatedIRI=\"xsd:integer\"/></DataPropertyRange>\
<FunctionalDataProperty><DataProperty IRI=\"p\"/></FunctionalDataProperty>\
<DatatypeDefinition><Datatype IRI=\"D\"/><Datatype abbreviatedIRI=\"xsd:integer\"/></DatatypeDefinition>")
-- HasKey: object properties first, then data properties
#guard twin (fsOnt "HasKey(:C (:p ObjectInverseOf(:q)) (:d))")
  (xmlOnt "<HasKey><Class IRI=\"C\"/><ObjectProperty IRI=\"p\"/><ObjectInverseOf>\
<ObjectProperty IRI=\"q\"/></ObjectInverseOf><DataProperty IRI=\"d\"/></HasKey>")
#guard twin (fsOnt "SameIndividual(:a :b :c) DifferentIndividuals(:a :b) DifferentIndividuals(:a :b :c) \
ObjectPropertyAssertion(:p :a :b) ObjectPropertyAssertion(ObjectInverseOf(:p) :a :b) \
NegativeObjectPropertyAssertion(:p :a :b) DataPropertyAssertion(:d :a \"1\"^^xsd:integer) \
NegativeDataPropertyAssertion(:d :a \"1\"^^xsd:integer) ClassAssertion(:A _:n)")
  (xmlOnt "<SameIndividual><NamedIndividual IRI=\"a\"/><NamedIndividual IRI=\"b\"/>\
<NamedIndividual IRI=\"c\"/></SameIndividual>\
<DifferentIndividuals><NamedIndividual IRI=\"a\"/><NamedIndividual IRI=\"b\"/></DifferentIndividuals>\
<DifferentIndividuals><NamedIndividual IRI=\"a\"/><NamedIndividual IRI=\"b\"/>\
<NamedIndividual IRI=\"c\"/></DifferentIndividuals>\
<ObjectPropertyAssertion><ObjectProperty IRI=\"p\"/><NamedIndividual IRI=\"a\"/>\
<NamedIndividual IRI=\"b\"/></ObjectPropertyAssertion>\
<ObjectPropertyAssertion><ObjectInverseOf><ObjectProperty IRI=\"p\"/></ObjectInverseOf>\
<NamedIndividual IRI=\"a\"/><NamedIndividual IRI=\"b\"/></ObjectPropertyAssertion>\
<NegativeObjectPropertyAssertion><ObjectProperty IRI=\"p\"/><NamedIndividual IRI=\"a\"/>\
<NamedIndividual IRI=\"b\"/></NegativeObjectPropertyAssertion>\
<DataPropertyAssertion><DataProperty IRI=\"d\"/><NamedIndividual IRI=\"a\"/>\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#integer\">1</Literal></DataPropertyAssertion>\
<NegativeDataPropertyAssertion><DataProperty IRI=\"d\"/><NamedIndividual IRI=\"a\"/>\
<Literal datatypeIRI=\"http://www.w3.org/2001/XMLSchema#integer\">1</Literal></NegativeDataPropertyAssertion>\
<ClassAssertion><Class IRI=\"A\"/><AnonymousIndividual nodeID=\"n\"/></ClassAssertion>")
-- negative: wrong arity
#guard !(readable (xmlOnt "<SameIndividual><NamedIndividual IRI=\"a\"/></SameIndividual>"))
#guard !(readable (xmlOnt "<ObjectPropertyAssertion><ObjectProperty IRI=\"p\"/>\
<NamedIndividual IRI=\"a\"/></ObjectPropertyAssertion>"))
-- negative: an unknown element
#guard !(readable (xmlOnt "<Frobnicate><Class IRI=\"A\"/></Frobnicate>"))

/-! ## Annotations -/

private def commentXml : String :=
  "<Annotation><AnnotationProperty abbreviatedIRI=\"rdfs:comment\"/><Literal>c</Literal></Annotation>"
private def commentFs : String := "Annotation(rdfs:comment \"c\")"

-- an annotated axiom is reified (section 2.3.1)
#guard twin (fsOnt ("SubClassOf(" ++ commentFs ++ " :A :B)"))
  (xmlOnt ("<SubClassOf>" ++ commentXml ++ "<Class IRI=\"A\"/><Class IRI=\"B\"/></SubClassOf>"))
-- an annotation of an annotation
#guard twin (fsOnt "SubClassOf(Annotation(Annotation(:src :s) rdfs:label \"l\") :A :B)")
  (xmlOnt ("<SubClassOf><Annotation><Annotation><AnnotationProperty IRI=\"src\"/><IRI>s</IRI></Annotation>\
<AnnotationProperty abbreviatedIRI=\"rdfs:label\"/><Literal>l</Literal></Annotation>\
<Class IRI=\"A\"/><Class IRI=\"B\"/></SubClassOf>"))
-- negative: the annotation is missing
#guard !(twin (fsOnt ("SubClassOf(" ++ commentFs ++ " :A :B)"))
  (xmlOnt "<SubClassOf><Class IRI=\"A\"/><Class IRI=\"B\"/></SubClassOf>"))
-- ontology annotations hang on the header; annotation axioms
#guard twin (fsOnt (commentFs ++ " AnnotationAssertion(rdfs:label :a \"x\") \
AnnotationAssertion(rdfs:seeAlso :a :b) SubAnnotationPropertyOf(:p :q) \
AnnotationPropertyDomain(:p :A) AnnotationPropertyRange(:p :A)"))
  (xmlOnt (commentXml ++ "<AnnotationAssertion><AnnotationProperty abbreviatedIRI=\"rdfs:label\"/>\
<IRI>a</IRI><Literal>x</Literal></AnnotationAssertion>\
<AnnotationAssertion><AnnotationProperty abbreviatedIRI=\"rdfs:seeAlso\"/><IRI>a</IRI><IRI>b</IRI></AnnotationAssertion>\
<SubAnnotationPropertyOf><AnnotationProperty IRI=\"p\"/><AnnotationProperty IRI=\"q\"/></SubAnnotationPropertyOf>\
<AnnotationPropertyDomain><AnnotationProperty IRI=\"p\"/><IRI>A</IRI></AnnotationPropertyDomain>\
<AnnotationPropertyRange><AnnotationProperty IRI=\"p\"/><IRI>A</IRI></AnnotationPropertyRange>"))
-- negative: an annotation needs a property and a value
#guard !(readable (xmlOnt "<SubClassOf><Annotation><AnnotationProperty IRI=\"p\"/></Annotation>\
<Class IRI=\"A\"/><Class IRI=\"B\"/></SubClassOf>"))

/-! ## The example ontology of the specification, section 2 -/

private def specExample : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<Ontology xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"\n\
    xsi:schemaLocation=\"http://www.w3.org/2002/07/owl# http://www.w3.org/2009/09/owl2-xml.xsd\"\n\
    xmlns=\"http://www.w3.org/2002/07/owl#\"\n\
    xml:base=\"http://example.com/myOntology\"\n\
    ontologyIRI=\"http://example.com/myOntology\">\n\
    <Prefix name=\"myOnt\" IRI=\"http://example.com/myOntology#\"/>\n\
    <Import>http://example.com/someOtherOntology</Import>\n\
    <Declaration><Class IRI=\"#Animal\"/></Declaration>\n\
    <Declaration><Class abbreviatedIRI=\"myOnt:Tabloid\"/></Declaration>\n\
    <Declaration><ObjectProperty IRI=\"#eats\"/></Declaration>\n\
    <Declaration><ObjectProperty IRI=\"#reads\"/></Declaration>\n\
    <SubClassOf>\n\
        <Class abbreviatedIRI=\"myOnt:Animal\"/>\n\
        <ObjectAllValuesFrom>\n\
            <ObjectProperty IRI=\"#reads\"/>\n\
            <Class IRI=\"#Tabloid\"/>\n\
        </ObjectAllValuesFrom>\n\
    </SubClassOf>\n\
</Ontology>"

private def specFs : String :=
  "Prefix( myOnt: = <http://example.com/myOntology#> )\n\
Ontology( <http://example.com/myOntology>\n\
  Import( <http://example.com/someOtherOntology> )\n\
  Declaration( Class( myOnt:Animal ) ) Declaration( Class( myOnt:Tabloid ) )\n\
  Declaration( ObjectProperty( myOnt:eats ) ) Declaration( ObjectProperty( myOnt:reads ) )\n\
  SubClassOf( myOnt:Animal ObjectAllValuesFrom( myOnt:reads myOnt:Tabloid ) ) )"

#guard readable specExample
#guard twin specFs specExample
-- negative: the example with one declaration removed
#guard !(twin specFs ((specExample.replace "<Declaration><ObjectProperty IRI=\"#eats\"/></Declaration>" "")))

end L4Factoidal.OWL.OwlXml
