/-
L4Factoidal.RDF.VocabularyTable — the namespaces and terms of the core RDF
vocabularies, and the container membership properties `rdf:_n`.

https://github.com/danbri/factoidal/issues/1051 item 5 (vocabulary table:
Jena `PrefixMapping.Standard`, `RDF`, `RDFS`, `OWL`, `XSD`; RDFLib `RDF`,
`RDFS`, `OWL`, `XSD` namespace objects).

## The table

`vocabularyTable` holds one row per namespace: the prefix label, the
namespace IRI and the local names of its terms. The prefixes and namespaces
are those of the Turtle writer (`Syntax.wellKnownPrefixes`, the same table; a
`#guard` below keeps them equal). The terms come from:

  * `rdf`: RDF 1.2 Concepts and RDF 1.2 Schema, section 5 (the RDF
    vocabulary), with `rdf:reifies`, `rdf:dirLangString`, `rdf:JSON` and
    `rdf:CompoundLiteral` of RDF 1.2;
  * `rdfs`: RDF 1.2 Schema, sections 2 to 5, with `rdfs:Proposition`;
  * `xsd`: the built-in datatypes of XSD 1.1 Part 2, section 3 (primitive and
    other built-in datatypes) with `xsd:anyType`;
  * `owl`: OWL 2 Mapping to RDF Graphs, Table 1 (the reserved vocabulary of
    OWL 2), with `owl:real` and `owl:rational` of OWL 2 Structural
    Specification section 4.1;
  * the other rows (`foaf`, `dcterms`, `dc`, `schema`) give the namespace only:
    their vocabularies are open and versioned outside the W3C.

A term of a row is the IRI `namespace ++ localName`. The container membership
properties `rdf:_1`, `rdf:_2`, ... are an infinite family (RDF 1.2 Schema,
section 5.1.6) and are not rows of the table: `memberIri n` and
`memberOrdinal? iri` map between `n ≥ 1` and the IRI.
-/
import L4Factoidal.Syntax.TurtleSerialize

namespace L4Factoidal.RDF

/-- One namespace of the table. -/
structure VocabularyRow where
  prefixLabel : String
  namespaceIri : String
  terms : List String
  deriving Repr

def rdfNamespace : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

def rdfTerms : List String :=
  [ "type", "Property", "Statement", "subject", "predicate", "object"
  , "Bag", "Seq", "Alt", "value", "List", "first", "rest", "nil"
  , "XMLLiteral", "HTML", "langString", "dirLangString", "JSON", "PlainLiteral"
  , "CompoundLiteral", "language", "direction", "reifies" ]

def rdfsTerms : List String :=
  [ "Resource", "Class", "Literal", "Datatype", "Container", "ContainerMembershipProperty"
  , "subClassOf", "subPropertyOf", "domain", "range", "label", "comment", "member"
  , "seeAlso", "isDefinedBy", "Proposition" ]

def xsdTerms : List String :=
  [ "anyType", "anySimpleType", "anyAtomicType"
  , "string", "boolean", "decimal", "float", "double", "duration", "dateTime", "time", "date"
  , "gYearMonth", "gYear", "gMonthDay", "gDay", "gMonth", "hexBinary", "base64Binary"
  , "anyURI", "QName", "NOTATION"
  , "normalizedString", "token", "language", "NMTOKEN", "NMTOKENS", "Name", "NCName"
  , "ID", "IDREF", "IDREFS", "ENTITY", "ENTITIES"
  , "integer", "nonPositiveInteger", "negativeInteger", "long", "int", "short", "byte"
  , "nonNegativeInteger", "unsignedLong", "unsignedInt", "unsignedShort", "unsignedByte"
  , "positiveInteger", "yearMonthDuration", "dayTimeDuration", "dateTimeStamp" ]

def owlTerms : List String :=
  [ "AllDifferent", "AllDisjointClasses", "AllDisjointProperties", "allValuesFrom"
  , "annotatedProperty", "annotatedSource", "annotatedTarget", "Annotation"
  , "AnnotationProperty", "assertionProperty", "AsymmetricProperty", "Axiom"
  , "backwardCompatibleWith", "bottomDataProperty", "bottomObjectProperty", "cardinality"
  , "Class", "complementOf", "DataRange", "datatypeComplementOf", "DatatypeProperty"
  , "deprecated", "DeprecatedClass", "DeprecatedProperty", "differentFrom"
  , "disjointUnionOf", "disjointWith", "distinctMembers", "equivalentClass"
  , "equivalentProperty", "FunctionalProperty", "hasKey", "hasSelf", "hasValue"
  , "imports", "incompatibleWith", "intersectionOf", "InverseFunctionalProperty"
  , "inverseOf", "IrreflexiveProperty", "maxCardinality", "maxQualifiedCardinality"
  , "members", "minCardinality", "minQualifiedCardinality", "NamedIndividual"
  , "NegativePropertyAssertion", "Nothing", "ObjectProperty", "onClass", "onDataRange"
  , "onDatatype", "oneOf", "onProperties", "onProperty", "Ontology", "OntologyProperty"
  , "priorVersion", "propertyChainAxiom", "propertyDisjointWith", "qualifiedCardinality"
  , "rational", "real", "ReflexiveProperty", "Restriction", "sameAs", "someValuesFrom"
  , "sourceIndividual", "SymmetricProperty", "targetIndividual", "targetValue", "Thing"
  , "topDataProperty", "topObjectProperty", "TransitiveProperty", "unionOf"
  , "versionInfo", "versionIRI", "withRestrictions" ]

/-- The terms of a namespace of `Syntax.wellKnownPrefixes`, by prefix label. -/
def termsOfPrefix : String → List String
  | "rdf" => rdfTerms
  | "rdfs" => rdfsTerms
  | "xsd" => xsdTerms
  | "owl" => owlTerms
  | _ => []

/-- The table: the rows of `Syntax.wellKnownPrefixes`, in its order. -/
def vocabularyTable : List VocabularyRow :=
  L4Factoidal.Syntax.wellKnownPrefixes.map fun (ns, label) =>
    let pfx := String.ofList (label.toList.filter (· != ':'))
    { prefixLabel := pfx, namespaceIri := ns, terms := termsOfPrefix pfx }

/-! ### Container membership properties -/

/-- `rdf:_n`. -/
def memberIri (n : Nat) : String := rdfNamespace ++ "_" ++ toString n

/-- The `n` of `rdf:_n`: a decimal numeral with no leading zero, `n ≥ 1`
(RDF 1.2 Schema, section 5.1.6). `none` for any other IRI. -/
def memberOrdinal? (iri : String) : Option Nat :=
  if iri.startsWith (rdfNamespace ++ "_") then
    let digits := (iri.drop (rdfNamespace.length + 1)).toString
    match digits.toList with
    | [] => none
    | c :: _ =>
        if c == '0' || !digits.all Char.isDigit then none else digits.toNat?
  else none

#guard vocabularyTable.map (·.prefixLabel) == ["rdf", "rdfs", "xsd", "owl", "foaf", "dcterms", "dc", "schema"]
#guard (vocabularyTable.find? (·.prefixLabel == "rdf")).map (·.namespaceIri) == some rdfNamespace
#guard vocabularyTable.all fun r => r.terms.all fun t => (r.terms.filter (· == t)).length == 1
#guard rdfTerms.length == 24 && rdfsTerms.length == 16 && owlTerms.length == 79
#guard xsdTerms.length == 50
#guard memberIri 3 == "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"
#guard memberOrdinal? (memberIri 1) == some 1
#guard memberOrdinal? (memberIri 120) == some 120
#guard memberOrdinal? "http://www.w3.org/1999/02/22-rdf-syntax-ns#_0" == none
#guard memberOrdinal? "http://www.w3.org/1999/02/22-rdf-syntax-ns#_01" == none
#guard memberOrdinal? "http://www.w3.org/1999/02/22-rdf-syntax-ns#_" == none
#guard memberOrdinal? "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1a" == none
#guard memberOrdinal? "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" == none
#guard memberOrdinal? "http://e/_1" == none

end L4Factoidal.RDF
