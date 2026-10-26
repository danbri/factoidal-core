/- SHACL 2017 §§2.3.1, 4.5, 4.8: constraints compare RDF nodes,
   not XMLLiteral values. Also exercise the node-expression SPARQL bridge
   with terms that cannot be faithfully represented as literal AST nodes. -/
import L4Factoidal.SHACL.NodeExpr
import L4Factoidal.SHACL.ShaclTests

namespace L4Factoidal.SHACL.IdentityTests

open L4Factoidal.RDF

private def shortXml : Term := .literal (SPARQL.mkTypedLiteral "<e/>" rdfXMLLiteral)
private def longXml : Term := .literal (SPARQL.mkTypedLiteral "<e></e>" rdfXMLLiteral)
private def p : WfIri := ⟨"urn:p", rfl⟩
private def q : WfIri := ⟨"urn:q", rfl⟩
private def a : WfIri := ⟨"urn:a", rfl⟩
private def b : WfIri := ⟨"urn:b", rfl⟩
private def graph : Graph :=
  [⟨.iri a, p, shortXml⟩, ⟨.iri b, p, longXml⟩, ⟨.iri a, q, longXml⟩]
private def shape : Shape :=
  { id := "urn:shape", isProperty := true, path := some (.pred p),
    targets := [.node (.iri a)], severity := .violation, message := none,
    constraints := [], propertyRefs := [] }

-- Two RDF terms with one XML value: the engine term equality separates them
-- too since https://github.com/danbri/factoidal/issues/963.
#guard !shortXml.eqb longXml
#guard !shortXml.sameTerm longXml
#guard !termMem shortXml [longXml]
#guard dedupTerms [shortXml, longXml, shortXml] == [shortXml, longXml]
-- Main's newer list and subset components also compare RDF nodes.
#guard dupMembers [shortXml, longXml] == []
#guard dupMembers [shortXml, longXml, shortXml] == [shortXml, shortXml]
#guard subjectsOf graph p shortXml == [.iri a]
#guard evalPath graph shortXml (.inverse (.pred p)) == [.iri a]
#guard evalPath graph (.iri a) (.alt [.pred p, .pred q]) == [shortXml, longXml]
#guard simpleValueCheck graph (.inSet [shortXml]) longXml == some false
#guard (evalAggregateNonRec (({} : ValidationConfig).envFor graph []) graph [] (.iri a) shape [shortXml] (.hasValue longXml)).length == 1
#guard (evalAggregateNonRec (({} : ValidationConfig).envFor graph []) graph [] (.iri a) shape [shortXml] (.equals (.pred q))).length == 2
#guard (evalAggregateNonRec (({} : ValidationConfig).envFor graph []) graph [] (.iri a) shape [shortXml] (.disjoint (.pred q))).isEmpty
#guard termMem (.literal (Literal.langString "colour" "EN"))
  [.literal (Literal.langString "colour" "en")]
#guard !termMem (.literal (Literal.dirLangString "word" "en" .ltr))
  [.literal (Literal.dirLangString "word" "en" .rtl)]
#guard !termMem (.literal (SPARQL.mkTypedLiteral "01" xsdInteger))
  [.literal (SPARQL.mkTypedLiteral "1" xsdInteger)]

-- Parsed shapes/data exercise decoding, path deduplication and report values.
private def doc : String :=
  "ex:a ex:p \"<e/>\"^^rdf:XMLLiteral ; ex:q \"<e></e>\"^^rdf:XMLLiteral . " ++
  "ex:S a sh:PropertyShape ; sh:targetNode ex:a ; " ++
  "sh:path [ sh:alternativePath ( ex:p ex:q ) ] ; sh:maxCount 1 ."
#guard (Tests.run doc).results.length == 1
#guard Tests.components (Tests.run doc) == [shMaxCountCC]

-- The SPARQL bridge must retain literal spelling, node kinds and blank IDs.
#guard sparqlApply "str" [.literal (SPARQL.mkTypedLiteral "01" xsdInteger)] ==
  [.literal (Literal.string "01")]
#guard sparqlApply "sameTerm" [.bnode "a", .bnode "b"] == [mkBoolLit false]
#guard sparqlApply "sameTerm" [.bnode "a", .bnode "a"] == [mkBoolLit true]
#guard sparqlApply "isLiteral" [.bnode "a"] == [mkBoolLit false]
#guard sparqlApply "coalesce" [.bnode "a"] == [.bnode "a"]
#guard sparqlApply "subject" [.tripleTerm (.bnode "a") p longXml] == [.bnode "a"]
#guard sparqlApply "object" [.tripleTerm (.bnode "a") p longXml] == [longXml]
#guard sparqlApply "coalesce" [.literal (SPARQL.mkTypedLiteral "1" xsdDecimal)] ==
  [.literal (SPARQL.mkTypedLiteral "1" xsdDecimal)]
#guard sparqlApply "logical-not" [.literal (SPARQL.mkTypedLiteral "1" xsdBoolean)] == [mkBoolLit false]
#guard sparqlApply "logical-not" [.literal (SPARQL.mkTypedLiteral "invalid" xsdBoolean)] == []
#guard sparqlApply "isNumeric" [.literal (SPARQL.mkTypedLiteral "invalid" xsdInteger)] == [mkBoolLit false]
#guard sparqlApply "isNumeric" [.literal (SPARQL.mkTypedLiteral "12"
  ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩)] == [mkBoolLit true]
#guard sparqlApply "logical-not" [.literal (SPARQL.mkTypedLiteral "1e-50" SPARQL.xsdFloat)] == [mkBoolLit true]
#guard sparqlApply "plus" [.literal (SPARQL.mkTypedLiteral "01" xsdInteger),
  .literal (SPARQL.mkTypedLiteral "2" xsdInteger)] == [.literal (SPARQL.mkTypedLiteral "3" xsdInteger)]

-- Node expressions inherit F&O unary fixes through the actual bound-term bridge.
#guard sparqlApply "round" [.literal (SPARQL.mkTypedLiteral "-1.5" xsdDecimal)] ==
  [.literal (SPARQL.mkTypedLiteral "-1.0" xsdDecimal)]
#guard sparqlApply "floor" [.literal (SPARQL.mkTypedLiteral "-0.1" xsdDecimal)] ==
  [.literal (SPARQL.mkTypedLiteral "-1.0" xsdDecimal)]
#guard sparqlApply "ceil" [.literal (SPARQL.mkTypedLiteral "-0.1" SPARQL.xsdFloat)] ==
  [.literal (SPARQL.mkTypedLiteral "-0.0E0" SPARQL.xsdFloat)]
#guard sparqlApply "round" [.literal (SPARQL.mkTypedLiteral "NaN" SPARQL.xsdFloat)] ==
  [.literal (SPARQL.mkTypedLiteral "NaN" SPARQL.xsdFloat)]
#guard sparqlApply "abs" [.literal (SPARQL.mkTypedLiteral "bad" xsdDecimal)] == []

end L4Factoidal.SHACL.IdentityTests
