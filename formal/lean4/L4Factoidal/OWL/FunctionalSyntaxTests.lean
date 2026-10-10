/-
L4Factoidal.OWL.FunctionalSyntaxTests — build-time checks for the
functional-style syntax reader and the mapping to RDF graphs.

Each check shows one construct and the triples OWL 2 Mapping to RDF
Graphs section 2 (Table 1, Table 2, section 2.3) turns it into. Every
positive check has a negative twin: an input the reader must reject, or
a perturbed input whose graph must differ.

History. Until 2026-10-10 the reader was a subset parser and four of
these checks stated its limits: `DataPropertyRange` with a
`DatatypeRestriction` was "outside the subset", `ObjectPropertyDomain`
was "outside the subset", a literal without a datatype was "declined",
and every triple count excluded the ontology header. The reader now
covers the whole grammar of the Structural Specification, so those four
checks were false and are replaced by the positive statements below. The
triple counts include the header triple `_:x rdf:type owl:Ontology`
(Table 1, first rows), which the subset parser omitted.
-/
import L4Factoidal.OWL.FunctionalSyntax
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.OWL.FS

open L4Factoidal.RDF

private def mk (s : String) : WfIri := (mkIri s).getD ⟨"http://invalid.example/x", rfl⟩

private def nsOwlT  : String := "http://www.w3.org/2002/07/owl#"
private def nsRdfT  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
private def nsRdfsT : String := "http://www.w3.org/2000/01/rdf-schema#"
private def nsXsdT  : String := "http://www.w3.org/2001/XMLSchema#"

private def rdfTypeI : WfIri := mk (nsRdfT ++ "type")
private def rdfFirstI : WfIri := mk (nsRdfT ++ "first")

private def bnRestriction (n : Nat) : Subject := .bnode ("owlfs_restr" ++ toString n)
private def bnChain (n : Nat) : Subject := .bnode ("owlfs_chain" ++ toString n)
private def headerAnon : Subject := .bnode "owlfs_ontology"

/-- The graph of a document, empty when the reader declines it. -/
private def gOf (doc : String) : List Triple := (parseFunctionalSyntax doc).getD []

private def countOf (doc : String) : Nat := (gOf doc).length

private def readable (doc : String) : Bool := (parseFunctionalSyntax doc).isSome

private def hasT (doc : String) (t : Triple) : Bool := (gOf doc).any (fun u => u == t)

/-- An all-IRI triple from full IRIs. -/
private def tr (s p o : String) : Triple := ⟨.iri (mk s), mk p, .iri (mk o)⟩

/-- The number of triples of the document with predicate `p`. -/
private def countP (doc : String) (p : String) : Nat :=
  ((gOf doc).filter (fun t => t.p.val == p)).length

private def pre : String :=
  "Prefix( : = <http://e/> )\nPrefix( xsd: = <http://www.w3.org/2001/XMLSchema#> )\n"

private def ont (body : String) : String := pre ++ "Ontology(\n" ++ body ++ "\n)"

private def exA : WfIri := mk "http://e/a"
private def exC : WfIri := mk "http://e/C"
private def exP : WfIri := mk "http://e/p"

/-! ## The ontology header — Table 1, first two rows -/

-- An anonymous ontology: `_:x rdf:type owl:Ontology`.
#guard hasT (ont "") ⟨headerAnon, rdfTypeI, .iri (mk (nsOwlT ++ "Ontology"))⟩
#guard countOf (ont "") == 1
-- A named one: the IRI is the header node; the version IRI and imports follow.
private def docNamed : String :=
  pre ++ "Ontology( <http://e/o> <http://e/o/1> Import(<http://e/i1>) Import(:i2) )"
#guard hasT docNamed (tr "http://e/o" (nsRdfT ++ "type") (nsOwlT ++ "Ontology"))
#guard hasT docNamed (tr "http://e/o" (nsOwlT ++ "versionIRI") "http://e/o/1")
#guard hasT docNamed (tr "http://e/o" (nsOwlT ++ "imports") "http://e/i1")
#guard hasT docNamed (tr "http://e/o" (nsOwlT ++ "imports") "http://e/i2")
#guard countOf docNamed == 4
-- negative: the header triple is absent from a document the reader declines
#guard (gOf "Ontology( ").isEmpty

/-! ## Prefixes: implicit, explicit, shadowing -/

-- owl:, rdf:, rdfs:, xsd: need no declaration
#guard hasT "Ontology( SubClassOf(<http://e/a> owl:Thing) )"
  (tr "http://e/a" (nsRdfsT ++ "subClassOf") (nsOwlT ++ "Thing"))
-- an explicit declaration replaces the implicit one
#guard hasT "Prefix(owl:=<http://x/>)\nOntology( SubClassOf(<http://e/a> owl:Thing) )"
  (tr "http://e/a" (nsRdfsT ++ "subClassOf") "http://x/Thing")
-- negative: an undeclared prefix is a failure, not a guess
#guard !(readable "Ontology( SubClassOf(<http://e/a> zzz:Thing) )")
-- the empty prefix needs a declaration too
#guard !(readable "Ontology( SubClassOf(<http://e/a> :Thing) )")

/-! ## Declarations — Table 1 -/

private def docDecl : String := ont "Declaration(Class(:C))"
#guard hasT docDecl ⟨.iri exC, rdfTypeI, .iri (mk (nsOwlT ++ "Class"))⟩
#guard countOf docDecl == 2

private def docFull : String :=
  "Ontology( Declaration(NamedIndividual(<http://e/a>)) )"
#guard hasT docFull ⟨.iri exA, rdfTypeI, .iri (mk (nsOwlT ++ "NamedIndividual"))⟩

#guard hasT (ont "Declaration(Datatype(:C))") (tr "http://e/C" (nsRdfT ++ "type") (nsRdfsT ++ "Datatype"))
#guard hasT (ont "Declaration(ObjectProperty(:p))")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "ObjectProperty"))
#guard hasT (ont "Declaration(DataProperty(:p))")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "DatatypeProperty"))
#guard hasT (ont "Declaration(AnnotationProperty(:p))")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "AnnotationProperty"))
-- negative: an unknown entity kind
#guard !(readable (ont "Declaration(Individual(:a))"))
-- negative: a declaration needs both closing parentheses
#guard !(readable (ont "Declaration(Class(:C)"))

/-! ## `ClassAssertion(DataHasValue(p "v"^^xsd:string) a)`

The restriction gets its own blank node carrying the three triples the
mapping table names, and the individual is typed with it. -/

private def docHasValue : String :=
  ont "ClassAssertion(DataHasValue(:p \"v\"^^xsd:string) :a)"

#guard countOf docHasValue == 5
#guard hasT docHasValue ⟨bnRestriction 0, rdfTypeI, .iri (mk (nsOwlT ++ "Restriction"))⟩
#guard hasT docHasValue ⟨bnRestriction 0, mk (nsOwlT ++ "onProperty"), .iri exP⟩
#guard hasT docHasValue ⟨.iri exA, rdfTypeI, .bnode "owlfs_restr0"⟩
-- negative: a literal as the individual is not an individual
#guard !(readable (ont "ClassAssertion(DataHasValue(:p \"v\"^^xsd:string) \"x\")"))

/-! ## Object property characteristics and `DataPropertyRange` -/

private def docTrans : String := ont "TransitiveObjectProperty(:p)"
#guard hasT docTrans ⟨.iri exP, rdfTypeI, .iri (mk (nsOwlT ++ "TransitiveProperty"))⟩
#guard hasT (ont "FunctionalObjectProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "FunctionalProperty"))
#guard hasT (ont "InverseFunctionalObjectProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "InverseFunctionalProperty"))
#guard hasT (ont "ReflexiveObjectProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "ReflexiveProperty"))
#guard hasT (ont "IrreflexiveObjectProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "IrreflexiveProperty"))
#guard hasT (ont "SymmetricObjectProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "SymmetricProperty"))
#guard hasT (ont "AsymmetricObjectProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "AsymmetricProperty"))
#guard hasT (ont "FunctionalDataProperty(:p)")
  (tr "http://e/p" (nsRdfT ++ "type") (nsOwlT ++ "FunctionalProperty"))

private def docRange : String := ont "DataPropertyRange(:p xsd:integer)"
#guard hasT docRange (tr "http://e/p" (nsRdfsT ++ "range") (nsXsdT ++ "integer"))
#guard countOf docRange == 2

/-! ## `SubObjectPropertyOf(ObjectPropertyChain(p q) r)`

The chain becomes an `rdf:first`/`rdf:rest` list bound to the
super-property: two cells (four triples) and one `owl:propertyChainAxiom`,
plus the header. -/

private def docChain : String := ont "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)"
#guard countOf docChain == 6
#guard hasT docChain ⟨bnChain 0, rdfFirstI, .iri exP⟩
#guard countP docChain (nsOwlT ++ "propertyChainAxiom") == 1
-- negative: a chain of one property is not a chain
#guard !(readable (ont "SubObjectPropertyOf(ObjectPropertyChain(:p) :r)"))
-- the plain form is a single rdfs:subPropertyOf triple
#guard hasT (ont "SubObjectPropertyOf(:p :r)") (tr "http://e/p" (nsRdfsT ++ "subPropertyOf") "http://e/r")

/-! ## `DatatypeRestriction` — each facet pair is its OWN blank node

The mapping specification says a facet-restriction node carries exactly
one triple, so a two-facet restriction needs two facet nodes and two
list cells. -/

-- `DataPropertyRange` takes a data range, so a restriction is readable
-- there: header, one facet triple, two list-cell triples, three
-- datatype triples, the range triple.
private def docFacet : String :=
  ont "DataPropertyRange(:p DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer))"
#guard readable docFacet
#guard countOf docFacet == 8

private def docFacetSome : String :=
  ont ("ClassAssertion(DataSomeValuesFrom(:p " ++
    "DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer)) :a)")
#guard readable docFacetSome
-- 1 header + 1 facet + 2 list cell + 3 datatype + 3 restriction + 1 assertion
#guard countOf docFacetSome == 11

private def docTwoFacets : String :=
  ont ("DataPropertyRange(:p DatatypeRestriction(xsd:integer " ++
    "xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"9\"^^xsd:integer))")
-- two facet nodes, two list cells (four triples)
#guard countP docTwoFacets (nsXsdT ++ "minInclusive") == 1
#guard countP docTwoFacets (nsXsdT ++ "maxInclusive") == 1
#guard countP docTwoFacets (nsRdfT ++ "first") == 2
-- negative: a restriction with no facet
#guard !(readable (ont "DataPropertyRange(:p DatatypeRestriction(xsd:integer))"))

/-! ## Data ranges: the other constructors -/

#guard countP (ont "DataPropertyRange(:p DataComplementOf(xsd:integer))")
  (nsOwlT ++ "datatypeComplementOf") == 1
#guard countP (ont "DataPropertyRange(:p DataIntersectionOf(xsd:integer xsd:short))")
  (nsOwlT ++ "intersectionOf") == 1
#guard countP (ont "DataPropertyRange(:p DataUnionOf(xsd:integer xsd:short))")
  (nsOwlT ++ "unionOf") == 1
#guard countP (ont "DataPropertyRange(:p DataOneOf(\"1\"^^xsd:integer \"2\"^^xsd:integer))")
  (nsOwlT ++ "oneOf") == 1
-- negative: a one-operand intersection / an empty enumeration
#guard !(readable (ont "DataPropertyRange(:p DataIntersectionOf(xsd:integer))"))
#guard !(readable (ont "DataPropertyRange(:p DataUnionOf(xsd:integer))"))
#guard !(readable (ont "DataPropertyRange(:p DataOneOf())"))

/-! ## Class expressions -/

private def clsT (body : String) : String := ont ("ClassAssertion(" ++ body ++ " :a)")

#guard countP (clsT "ObjectIntersectionOf(:A :B)") (nsOwlT ++ "intersectionOf") == 1
#guard countP (clsT "ObjectUnionOf(:A :B :C)") (nsOwlT ++ "unionOf") == 1
#guard countP (clsT "ObjectComplementOf(:A)") (nsOwlT ++ "complementOf") == 1
#guard countP (clsT "ObjectOneOf(:x :y)") (nsOwlT ++ "oneOf") == 1
#guard countP (clsT "ObjectSomeValuesFrom(:p :A)") (nsOwlT ++ "someValuesFrom") == 1
#guard countP (clsT "ObjectAllValuesFrom(:p :A)") (nsOwlT ++ "allValuesFrom") == 1
#guard countP (clsT "ObjectHasValue(:p :b)") (nsOwlT ++ "hasValue") == 1
-- `ObjectHasSelf` carries "true"^^xsd:boolean
#guard (gOf (clsT "ObjectHasSelf(:p)")).any (fun t =>
  t.p.val == nsOwlT ++ "hasSelf" &&
  (match t.o with | .literal l => l.val.lexicalForm == "true" | _ => false))
-- the inverse of a property is a node `_:x owl:inverseOf p`
#guard countP (clsT "ObjectSomeValuesFrom(ObjectInverseOf(:p) :A)") (nsOwlT ++ "inverseOf") == 1
-- negative: one-operand intersections and unions, empty enumerations
#guard !(readable (clsT "ObjectIntersectionOf(:A)"))
#guard !(readable (clsT "ObjectUnionOf(:A)"))
#guard !(readable (clsT "ObjectOneOf()"))
-- negative: an unknown class expression keyword
#guard !(readable (clsT "ObjectFrobnicate(:p :A)"))

/-! ### Cardinalities: unqualified and qualified rows differ -/

#guard countP (clsT "ObjectMinCardinality(2 :p)") (nsOwlT ++ "minCardinality") == 1
#guard countP (clsT "ObjectMinCardinality(2 :p)") (nsOwlT ++ "minQualifiedCardinality") == 0
#guard countP (clsT "ObjectMinCardinality(2 :p :A)") (nsOwlT ++ "minQualifiedCardinality") == 1
#guard countP (clsT "ObjectMinCardinality(2 :p :A)") (nsOwlT ++ "onClass") == 1
#guard countP (clsT "ObjectMaxCardinality(1 :p)") (nsOwlT ++ "maxCardinality") == 1
#guard countP (clsT "ObjectMaxCardinality(1 :p :A)") (nsOwlT ++ "maxQualifiedCardinality") == 1
#guard countP (clsT "ObjectExactCardinality(1 :p)") (nsOwlT ++ "cardinality") == 1
#guard countP (clsT "ObjectExactCardinality(1 :p :A)") (nsOwlT ++ "qualifiedCardinality") == 1
-- the cardinality literal is "n"^^xsd:nonNegativeInteger
#guard (gOf (clsT "ObjectMinCardinality(12 :p)")).any (fun t =>
  t.p.val == nsOwlT ++ "minCardinality" &&
  (match t.o with
   | .literal l => l.val.lexicalForm == "12" && l.val.datatype.val == nsXsdT ++ "nonNegativeInteger"
   | _ => false))
#guard countP (clsT "DataMinCardinality(2 :p)") (nsOwlT ++ "minCardinality") == 1
#guard countP (clsT "DataMinCardinality(2 :p xsd:integer)") (nsOwlT ++ "onDataRange") == 1
#guard countP (clsT "DataMaxCardinality(2 :p xsd:integer)") (nsOwlT ++ "maxQualifiedCardinality") == 1
#guard countP (clsT "DataExactCardinality(2 :p xsd:integer)") (nsOwlT ++ "qualifiedCardinality") == 1
-- negative: the cardinality is a natural number
#guard !(readable (clsT "ObjectMinCardinality(two :p)"))
#guard !(readable (clsT "ObjectMinCardinality(-1 :p)"))

/-! ### `DataSomeValuesFrom` with several properties uses `owl:onProperties` -/

#guard countP (clsT "DataSomeValuesFrom(:p xsd:integer)") (nsOwlT ++ "onProperty") == 1
#guard countP (clsT "DataSomeValuesFrom(:p xsd:integer)") (nsOwlT ++ "onProperties") == 0
#guard countP (clsT "DataSomeValuesFrom(:p :q xsd:integer)") (nsOwlT ++ "onProperties") == 1
#guard countP (clsT "DataSomeValuesFrom(:p :q xsd:integer)") (nsOwlT ++ "onProperty") == 0
#guard countP (clsT "DataAllValuesFrom(:p :q xsd:integer)") (nsOwlT ++ "allValuesFrom") == 1
-- negative: no data range after the properties / a compound among the properties
#guard !(readable (clsT "DataSomeValuesFrom(:p)"))
#guard !(readable (clsT "DataSomeValuesFrom(DataComplementOf(xsd:integer) :p xsd:integer)"))

/-! ## Class axioms -/

#guard hasT (ont "SubClassOf(:A :B)") (tr "http://e/A" (nsRdfsT ++ "subClassOf") "http://e/B")
-- `EquivalentClasses` of n classes gives n-1 adjacent pairs
#guard countP (ont "EquivalentClasses(:A :B :C)") (nsOwlT ++ "equivalentClass") == 2
-- `DisjointClasses` of two is a triple; of three an `AllDisjointClasses` node
#guard hasT (ont "DisjointClasses(:A :B)") (tr "http://e/A" (nsOwlT ++ "disjointWith") "http://e/B")
#guard countP (ont "DisjointClasses(:A :B :C)") (nsOwlT ++ "members") == 1
#guard countP (ont "DisjointClasses(:A :B :C)") (nsOwlT ++ "disjointWith") == 0
#guard countP (ont "DisjointClasses(:A :B)") (nsOwlT ++ "members") == 0
#guard countP (ont "DisjointUnion(:A :B :C)") (nsOwlT ++ "disjointUnionOf") == 1
-- negative: arity
#guard !(readable (ont "EquivalentClasses(:A)"))
#guard !(readable (ont "DisjointClasses(:A)"))
#guard !(readable (ont "DisjointUnion(:A :B)"))

/-! ## Object property axioms -/

#guard countP (ont "EquivalentObjectProperties(:p :q :r)") (nsOwlT ++ "equivalentProperty") == 2
#guard hasT (ont "DisjointObjectProperties(:p :q)")
  (tr "http://e/p" (nsOwlT ++ "propertyDisjointWith") "http://e/q")
#guard countP (ont "DisjointObjectProperties(:p :q :r)") (nsOwlT ++ "members") == 1
#guard hasT (ont "InverseObjectProperties(:p :q)") (tr "http://e/p" (nsOwlT ++ "inverseOf") "http://e/q")
#guard hasT (ont "ObjectPropertyDomain(:p :C)") (tr "http://e/p" (nsRdfsT ++ "domain") "http://e/C")
#guard hasT (ont "ObjectPropertyRange(:p :C)") (tr "http://e/p" (nsRdfsT ++ "range") "http://e/C")
#guard !(readable (ont "EquivalentObjectProperties(:p)"))
#guard !(readable (ont "InverseObjectProperties(:p)"))

/-! ## Data property axioms and datatype definitions -/

#guard hasT (ont "SubDataPropertyOf(:p :q)") (tr "http://e/p" (nsRdfsT ++ "subPropertyOf") "http://e/q")
#guard countP (ont "EquivalentDataProperties(:p :q :r)") (nsOwlT ++ "equivalentProperty") == 2
#guard hasT (ont "DisjointDataProperties(:p :q)")
  (tr "http://e/p" (nsOwlT ++ "propertyDisjointWith") "http://e/q")
#guard countP (ont "DisjointDataProperties(:p :q :r)") (nsOwlT ++ "members") == 1
#guard hasT (ont "DataPropertyDomain(:p :C)") (tr "http://e/p" (nsRdfsT ++ "domain") "http://e/C")
#guard hasT (ont "DatatypeDefinition(:D xsd:integer)")
  (tr "http://e/D" (nsOwlT ++ "equivalentClass") (nsXsdT ++ "integer"))
#guard !(readable (ont "DisjointDataProperties(:p)"))

/-! ## `HasKey` — a sequence of the object then the data properties -/

private def docKey : String := ont "HasKey(:C (:p :q) (:d))"
#guard countP docKey (nsOwlT ++ "hasKey") == 1
#guard countP docKey (nsRdfT ++ "first") == 3
#guard countOf docKey == 8
-- negative: both property lists are required
#guard !(readable (ont "HasKey(:C (:p))"))
#guard countP (ont "HasKey(:C () ())") (nsOwlT ++ "hasKey") == 1

/-! ## Assertions -/

#guard countP (ont "SameIndividual(:a :b :c)") (nsOwlT ++ "sameAs") == 2
#guard hasT (ont "DifferentIndividuals(:a :b)") (tr "http://e/a" (nsOwlT ++ "differentFrom") "http://e/b")
-- three individuals: an `AllDifferent` node with `owl:members`
#guard countP (ont "DifferentIndividuals(:a :b :c)") (nsOwlT ++ "members") == 1
#guard countP (ont "DifferentIndividuals(:a :b :c)") (nsOwlT ++ "differentFrom") == 0
#guard hasT (ont "ObjectPropertyAssertion(:p :a :b)") (tr "http://e/a" "http://e/p" "http://e/b")
-- the inverse form swaps the individuals and creates no node
#guard hasT (ont "ObjectPropertyAssertion(ObjectInverseOf(:p) :a :b)")
  (tr "http://e/b" "http://e/p" "http://e/a")
#guard countP (ont "ObjectPropertyAssertion(ObjectInverseOf(:p) :a :b)") (nsOwlT ++ "inverseOf") == 0
#guard countP (ont "NegativeObjectPropertyAssertion(:p :a :b)") (nsOwlT ++ "targetIndividual") == 1
#guard countP (ont "NegativeDataPropertyAssertion(:p :a \"1\"^^xsd:integer)")
  (nsOwlT ++ "targetValue") == 1
-- `ClassAssertion` reads (class, individual): the order matters
#guard hasT (ont "ClassAssertion(:C :a)") (tr "http://e/a" (nsRdfT ++ "type") "http://e/C")
#guard !(hasT (ont "ClassAssertion(:C :a)") (tr "http://e/C" (nsRdfT ++ "type") "http://e/a"))
-- an anonymous individual keeps its node ID
#guard hasT (ont "ClassAssertion(:C _:n1)") ⟨.bnode "owlfs_anon_n1", rdfTypeI, .iri exC⟩
#guard !(readable (ont "SameIndividual(:a)"))
#guard !(readable (ont "ObjectPropertyAssertion(:p :a)"))

/-! ## Literals -/

private def litDoc (lit : String) : String := ont ("DataPropertyAssertion(:p :a " ++ lit ++ ")")

private def litOf (doc : String) : Option Literal :=
  ((gOf doc).find? (fun t => t.p.val == "http://e/p")).bind (fun t =>
    match t.o with | .literal l => some l.val | _ => none)

-- a literal with no datatype is an xsd:string (RDF 1.1)
#guard (litOf (litDoc "\"v\"")).map (·.datatype.val) == some (nsXsdT ++ "string")
-- a tagged literal is rdf:langString
#guard (litOf (litDoc "\"v\"@en")).map (fun l => (l.datatype.val, l.langTag)) ==
  some (nsRdfT ++ "langString", some "en")
-- a typed literal keeps its datatype
#guard (litOf (litDoc "\"1\"^^xsd:integer")).map (·.datatype.val) == some (nsXsdT ++ "integer")
-- escapes
#guard (litOf (litDoc "\"a\\\"b\\\\c\"")).map (·.lexicalForm) == some "a\"b\\c"
-- rdf:PlainLiteral: "abc@en" is "abc"@en; "abc@" is "abc"
#guard (litOf (litDoc "\"abc@en\"^^rdf:PlainLiteral")).map (fun l => (l.lexicalForm, l.langTag)) ==
  some ("abc", some "en")
#guard (litOf (litDoc "\"abc@\"^^rdf:PlainLiteral")).map (fun l => (l.lexicalForm, l.langTag)) ==
  some ("abc", none)
-- negative: an unterminated string, a bad escape, a datatype that is not an IRI
#guard !(readable (litDoc "\"v"))
#guard !(readable (litDoc "\"a\\nb\""))
#guard !(readable (litDoc "\"v\"^^nonsense"))

/-! ## Annotations — Table 2 and section 2.3 -/

private def comment : String := "Annotation(<http://www.w3.org/2000/01/rdf-schema#comment> \"c\")"

-- 2.3.1: an annotated single-triple axiom is followed by an owl:Axiom node
private def docAnnSub : String := ont ("SubClassOf(" ++ comment ++ " :A :B)")
#guard countP docAnnSub (nsOwlT ++ "annotatedSource") == 1
#guard countP docAnnSub (nsOwlT ++ "annotatedProperty") == 1
#guard countP docAnnSub (nsOwlT ++ "annotatedTarget") == 1
#guard hasT docAnnSub (tr "http://e/A" (nsRdfsT ++ "subClassOf") "http://e/B")
#guard countP docAnnSub (nsRdfsT ++ "comment") == 1
-- the unannotated twin has no reification
#guard countP (ont "SubClassOf(:A :B)") (nsOwlT ++ "annotatedSource") == 0
-- 2.3.2: EquivalentClasses of three: two pairs, two nodes, annotation repeated
private def docAnnEq : String := ont ("EquivalentClasses(" ++ comment ++ " :A :B :C)")
#guard countP docAnnEq (nsOwlT ++ "annotatedSource") == 2
#guard countP docAnnEq (nsRdfsT ++ "comment") == 2
-- 2.3.3: DisjointClasses of three is a node; the annotation sits ON it
private def docAnnDisj : String := ont ("DisjointClasses(" ++ comment ++ " :A :B :C)")
#guard countP docAnnDisj (nsOwlT ++ "annotatedSource") == 0
#guard countP docAnnDisj (nsRdfsT ++ "comment") == 1
-- 2.3.3 again: a negative property assertion carries its annotation
#guard countP (ont ("NegativeObjectPropertyAssertion(" ++ comment ++ " :p :a :b)"))
  (nsRdfsT ++ "comment") == 1
-- a declaration is annotated through the rdf:type triple
private def docAnnDecl : String := ont ("Declaration(" ++ comment ++ " Class(:C))")
#guard (gOf docAnnDecl).any (fun t =>
  t.p.val == nsOwlT ++ "annotatedProperty" && t.o == .iri (mk (nsRdfT ++ "type")))
-- a chain: the annotation reifies `owl:propertyChainAxiom`, the list is unchanged
private def docAnnChain : String :=
  ont ("SubObjectPropertyOf(" ++ comment ++ " ObjectPropertyChain(:p :q) :r)")
#guard (gOf docAnnChain).any (fun t =>
  t.p.val == nsOwlT ++ "annotatedProperty" && t.o == .iri (mk (nsOwlT ++ "propertyChainAxiom")))
#guard countP docAnnChain (nsRdfT ++ "first") == 2
-- an annotation OF an annotation: an owl:Annotation node (Table 2)
private def docAnnAnn : String :=
  ont ("AnnotationAssertion(Annotation(Annotation(:src :s) <http://www.w3.org/2000/01/rdf-schema#label> \"l\")" ++
       " <http://www.w3.org/2000/01/rdf-schema#comment> :a \"c\")")
#guard (gOf docAnnAnn).any (fun t =>
  t.p.val == rdfTypeI.val && t.o == .iri (mk (nsOwlT ++ "Annotation")))
#guard (gOf docAnnAnn).any (fun t =>
  t.p.val == rdfTypeI.val && t.o == .iri (mk (nsOwlT ++ "Axiom")))
-- ontology annotations hang on the header node
#guard hasT (pre ++ "Ontology(<http://e/o> Annotation(:src :s))")
  (tr "http://e/o" "http://e/src" "http://e/s")
-- negative: an annotation needs a property and a value
#guard !(readable (ont "SubClassOf(Annotation(:src) :A :B)"))
-- negative: annotations come before the operands, not after
#guard !(readable (ont ("SubClassOf(:A :B " ++ comment ++ ")")))

/-! ## Annotation axioms -/

#guard hasT (ont "AnnotationAssertion(:ap :a :b)") (tr "http://e/a" "http://e/ap" "http://e/b")
#guard hasT (ont "SubAnnotationPropertyOf(:p :q)") (tr "http://e/p" (nsRdfsT ++ "subPropertyOf") "http://e/q")
#guard hasT (ont "AnnotationPropertyDomain(:p :C)") (tr "http://e/p" (nsRdfsT ++ "domain") "http://e/C")
#guard hasT (ont "AnnotationPropertyRange(:p :C)") (tr "http://e/p" (nsRdfsT ++ "range") "http://e/C")
-- a literal is not an annotation subject
#guard !(readable (ont "AnnotationAssertion(:ap \"s\" :b)"))

/-! ## What the reader declines

A construct outside the grammar is a CLEAN failure, never a graph with
the axiom silently missing — a missing axiom makes an inconsistent
ontology look consistent. -/

-- `ObjectPropertyDomain` is part of the grammar and is read
#guard readable "Ontology( ObjectPropertyDomain(<http://e/p> <http://e/C>) )"
-- an unknown axiom keyword
#guard !(readable "Ontology( Frobnicate(<http://e/p> <http://e/C>) )")
-- unbalanced parentheses
#guard !(readable "Prefix( : = <http://e/> )\nOntology( Declaration(Class(:C))")
#guard !(readable "Prefix( : = <http://e/> )\nOntology( Declaration(Class(:C))))")
-- no Ontology
#guard !(readable "Declaration(Class(<http://e/C>))")
-- trailing tokens after the document
#guard !(readable "Ontology( ) Ontology( )")
-- a malformed Prefix
#guard !(readable "Prefix( : <http://e/> )\nOntology( )")
-- a bare name where an IRI is required
#guard !(readable "Ontology( SubClassOf(Thing Nothing) )")
-- the empty document
#guard !(readable "")

/-! ## Cross-syntax: a functional-style document and its RDF/XML twin

OWL 2 Conformance section 2 requires the syntaxes of one test case to
express the same ontology. The mapped graph of the first document is
isomorphic (RDF 1.1 Concepts section 3.6) to the graph of the second. The
pair is `DisjointClasses-001` from the OWL 2 test catalog, shortened. -/

private def twinFs : String :=
  "Prefix( : = <http://example.org/> )\n" ++
  "Ontology( Declaration( Class( :Boy ) ) Declaration( Class( :Girl ) )\n" ++
  "  DisjointClasses( :Boy :Girl ) ClassAssertion( :Boy :Stewie ) )"

private def twinXml (disjoint : String) : String :=
  "<rdf:RDF xml:base=\"http://example.org/\" xmlns=\"http://example.org/\"\n" ++
  "  xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "  xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
  "<owl:Ontology/>\n<owl:Class rdf:about=\"Boy\"/>\n<owl:Class rdf:about=\"Girl\"/>\n" ++
  "<rdf:Description rdf:about=\"Boy\"><owl:disjointWith rdf:resource=\"" ++ disjoint ++ "\"/>\n" ++
  "</rdf:Description>\n<Boy rdf:about=\"Stewie\"/>\n</rdf:RDF>"

private def twinIso (xml : String) : Bool :=
  match parseFunctionalSyntax twinFs,
        L4Factoidal.Syntax.RdfXml.parseRdfXml xml (some "http://example.org/") with
  | some a, .ok b => Graph.isomorphic? a b
  | _, _ => false

#guard twinIso (twinXml "Girl")
-- negative: the same document with a different disjoint class is not isomorphic
#guard !(twinIso (twinXml "Boy"))
#guard !(twinIso (twinXml "Dog"))

end L4Factoidal.OWL.FS
