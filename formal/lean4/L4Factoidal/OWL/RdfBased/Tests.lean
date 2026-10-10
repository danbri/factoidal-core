/-
L4Factoidal.OWL.RdfBased.Tests — `#guard` cases for the OWL 2
RDF-Based Semantics rules (`RdfBased/Engine.lean`).

Every rule has a POSITIVE case (the rule derives the triple from a
graph that licenses it) and a NEGATIVE case (a graph that differs from
the positive one in the premise the rule's soundness proof reads, from
which the triple is not derived). An engine that derived everything
fails the negative half; one that derived nothing fails the positive
half (skill `measuring-inference` § 3).

The end-to-end cases run `rbSaturate` (OWL 2 RL/RDF closure and the
rules, alternating) on the shapes of three W3C cases
(`WebOnt-Class-003`, `WebOnt-imports-010`, `WebOnt-I5.3-015`); the W3C
documents themselves are judged by `l4owl-probe --rdf-based`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RdfBased.Engine

namespace L4Factoidal.OWL.RdfBased.Tests

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.OWL.RdfBased
open L4Factoidal.RDFS (rdfsClass rdfsLiteral rdfProperty rdfsResource rdfList)

private def cA : WfIri := ⟨"http://ex/A", rfl⟩
private def cB : WfIri := ⟨"http://ex/B", rfl⟩
private def cY : WfIri := ⟨"http://ex/Y", rfl⟩
private def pP : WfIri := ⟨"http://ex/p", rfl⟩
private def pQ : WfIri := ⟨"http://ex/q", rfl⟩
private def iX : WfIri := ⟨"http://ex/x", rfl⟩
private def iA : WfIri := ⟨"http://ex/a", rfl⟩
private def iB : WfIri := ⟨"http://ex/b", rfl⟩
private def iC : WfIri := ⟨"http://ex/c", rfl⟩

private def S (i : WfIri) : Subject := Subject.iri i
private def O (i : WfIri) : Term := Term.iri i
private def B (l : String) : Subject := Subject.bnode l
private def Bt (l : String) : Term := Term.bnode l

private def has (g goal : Graph) (t : Triple) : Bool := memB (rbConclusions g goal) t

/-! ## Axiomatic triples (Tables 5.2, 5.3, 5.5), goal-directed -/

private def goalImports : Graph := [⟨S owlImports, rdfType, O rdfProperty⟩]
#guard has [] goalImports ⟨S owlImports, rdfsDomain, O owlOntology⟩
#guard has [] goalImports ⟨S owlImports, rdfsRange, O owlOntology⟩
#guard has [] goalImports ⟨S owlImports, rdfType, O owlOntologyProperty⟩
-- not asked for: the goal does not name owl:imports
#guard !has [] [⟨S iX, rdfType, O cA⟩] ⟨S owlImports, rdfsDomain, O owlOntology⟩
-- Table 5.2 "= IC" both ways gives the equivalence; "⊆ IP" gives no equivalence
#guard has [] [⟨S rdfsClass, owlEquivalentClass, O owlClass⟩]
  ⟨S rdfsClass, owlEquivalentClass, O owlClass⟩
#guard !has [] [⟨S owlFunctionalProperty, owlEquivalentClass, O rdfProperty⟩]
  ⟨S owlFunctionalProperty, owlEquivalentClass, O rdfProperty⟩
#guard has [] [⟨B "x", owlOneOf, O rdfNil⟩, ⟨B "x", owlEquivalentClass, O owlNothing⟩]
  ⟨S owlNothing, owlOneOf, O rdfNil⟩
#guard !has [] [⟨S owlThing, owlOneOf, O rdfNil⟩] ⟨S owlThing, owlOneOf, O rdfNil⟩

/-! ## vocabType (Tables 5.1, 5.2) -/

#guard has [⟨S iX, rdfType, O owlClass⟩] [] ⟨S iX, rdfType, O rdfsClass⟩
#guard has [⟨S iX, rdfType, O owlSymmetricProperty⟩] [] ⟨S iX, rdfType, O rdfProperty⟩
#guard !has [⟨S iX, rdfType, O cA⟩] [] ⟨S iX, rdfType, O rdfsClass⟩
-- ⊆ IP is one direction: a property is not thereby symmetric
#guard !has [⟨S iX, rdfType, O rdfProperty⟩] [] ⟨S iX, rdfType, O owlSymmetricProperty⟩

/-! ## universal (Table 5.2) -/

#guard has [] [⟨S iX, rdfType, O owlThing⟩] ⟨S iX, rdfType, O owlThing⟩
#guard has [⟨S iA, pP, O iB⟩] [⟨B "w", rdfType, O owlThing⟩] ⟨S iA, rdfType, O owlThing⟩
#guard !has [] [⟨S iX, rdfType, O cA⟩] ⟨S iX, rdfType, O owlThing⟩
#guard !has [] [⟨S iX, rdfType, O owlNothing⟩] ⟨S iX, rdfType, O owlNothing⟩

/-! ## compSym (Table 5.4) -/

#guard has [⟨S cA, owlComplementOf, O cB⟩] [] ⟨S cB, owlComplementOf, O cA⟩
#guard !has [⟨S cA, owlDisjointWith, O cB⟩] [] ⟨S cB, owlComplementOf, O cA⟩

/-! ## allDiff (Tables 5.9, 5.10) -/

private def listABC : Graph :=
  [ ⟨B "l1", rdfFirst, O iA⟩, ⟨B "l1", rdfRest, Bt "l2"⟩,
    ⟨B "l2", rdfFirst, O iB⟩, ⟨B "l2", rdfRest, Bt "l3"⟩,
    ⟨B "l3", rdfFirst, O iC⟩, ⟨B "l3", rdfRest, O rdfNil⟩ ]
private def gAdf : Graph :=
  listABC ++ [⟨B "z", rdfType, O owlAllDifferent⟩, ⟨B "z", owlDistinctMembers, Bt "l1"⟩]
#guard has gAdf [] ⟨S iA, owlDifferentFrom, O iC⟩
#guard has gAdf [] ⟨S iC, owlDifferentFrom, O iB⟩
#guard !has gAdf [] ⟨S iA, owlDifferentFrom, O iA⟩
-- the node is not typed owl:AllDifferent
#guard !has (listABC ++ [⟨B "z", owlDistinctMembers, Bt "l1"⟩]) [] ⟨S iA, owlDifferentFrom, O iC⟩

/-! ## funSingleton, ifpSingleton (Tables 5.5, 5.8, 5.13) -/

private def oneA : Graph := [⟨B "m1", rdfFirst, O iA⟩, ⟨B "m1", rdfRest, O rdfNil⟩]
private def oneAB : Graph :=
  [ ⟨B "m1", rdfFirst, O iA⟩, ⟨B "m1", rdfRest, Bt "m2"⟩,
    ⟨B "m2", rdfFirst, O iB⟩, ⟨B "m2", rdfRest, O rdfNil⟩ ]
#guard has (oneA ++ [⟨S pP, rdfsRange, O cA⟩, ⟨S cA, owlOneOf, Bt "m1"⟩]) []
  ⟨S pP, rdfType, O owlFunctionalProperty⟩
#guard !has (oneAB ++ [⟨S pP, rdfsRange, O cA⟩, ⟨S cA, owlOneOf, Bt "m1"⟩]) []
  ⟨S pP, rdfType, O owlFunctionalProperty⟩
#guard has (oneA ++ [⟨S pP, rdfsDomain, O cA⟩, ⟨S cA, owlOneOf, Bt "m1"⟩]) []
  ⟨S pP, rdfType, O owlInverseFunctionalProperty⟩
-- a singleton RANGE does not make the property inverse functional
#guard !has (oneA ++ [⟨S pP, rdfsRange, O cA⟩, ⟨S cA, owlOneOf, Bt "m1"⟩]) []
  ⟨S pP, rdfType, O owlInverseFunctionalProperty⟩

/-! ## typeDomainSub (Table 5.8) -/

#guard has [⟨S rdfType, rdfsDomain, O cY⟩, ⟨S iX, rdfType, O rdfsClass⟩] []
  ⟨S iX, rdfsSubClassOf, O cY⟩
#guard !has [⟨S pP, rdfsDomain, O cY⟩, ⟨S iX, rdfType, O rdfsClass⟩] []
  ⟨S iX, rdfsSubClassOf, O cY⟩

/-! ## avfRange, svfDomain (Tables 5.2, 5.3, 5.6, 5.8) -/

#guard has [⟨S owlThing, rdfsSubClassOf, Bt "r"⟩, ⟨B "r", owlOnProperty, O pP⟩,
            ⟨B "r", owlAllValuesFrom, O cA⟩] [] ⟨S pP, rdfsRange, O cA⟩
#guard !has [⟨S cB, rdfsSubClassOf, Bt "r"⟩, ⟨B "r", owlOnProperty, O pP⟩,
             ⟨B "r", owlAllValuesFrom, O cA⟩] [] ⟨S pP, rdfsRange, O cA⟩
#guard has [⟨B "r", owlSomeValuesFrom, O owlThing⟩, ⟨B "r", owlOnProperty, O pP⟩,
            ⟨B "r", rdfsSubClassOf, O cA⟩] [] ⟨S pP, rdfsDomain, O cA⟩
#guard !has [⟨B "r", owlSomeValuesFrom, O cB⟩, ⟨B "r", owlOnProperty, O pP⟩,
             ⟨B "r", rdfsSubClassOf, O cA⟩] [] ⟨S pP, rdfsDomain, O cA⟩

/-! ## emptySubProp (Table 5.8, the datatype map) -/

#guard has [⟨S pP, rdfsRange, O xsdInteger⟩, ⟨S pP, rdfsRange, O xsdString⟩,
            ⟨S pQ, rdfType, O rdfProperty⟩] [] ⟨S pP, rdfsSubPropertyOf, O pQ⟩
-- xsd:integer and xsd:decimal share a value-space family: no emptiness
#guard !has [⟨S pP, rdfsRange, O xsdInteger⟩, ⟨S pP, rdfsRange, O xsdDecimal⟩,
             ⟨S pQ, rdfType, O rdfProperty⟩] [] ⟨S pP, rdfsSubPropertyOf, O pQ⟩

/-! ## oneOfSub, unionSub, interSub (Tables 5.4, 5.5, 5.8) -/

private def listBA : Graph :=
  [ ⟨B "n1", rdfFirst, O iB⟩, ⟨B "n1", rdfRest, Bt "n2"⟩,
    ⟨B "n2", rdfFirst, O iA⟩, ⟨B "n2", rdfRest, O rdfNil⟩ ]
private def listAB : Graph :=
  [ ⟨B "k1", rdfFirst, O iA⟩, ⟨B "k1", rdfRest, Bt "k2"⟩,
    ⟨B "k2", rdfFirst, O iB⟩, ⟨B "k2", rdfRest, O rdfNil⟩ ]
-- the same members in another order: subclass both ways
#guard has (listAB ++ listBA ++ [⟨S cA, owlOneOf, Bt "k1"⟩, ⟨S cB, owlOneOf, Bt "n1"⟩]) []
  ⟨S cA, rdfsSubClassOf, O cB⟩
#guard has (listAB ++ oneA ++ [⟨S cA, owlOneOf, Bt "m1"⟩, ⟨S cB, owlOneOf, Bt "k1"⟩]) []
  ⟨S cA, rdfsSubClassOf, O cB⟩
-- a larger enumeration is not a subclass of a smaller one
#guard !has (listAB ++ oneA ++ [⟨S cA, owlOneOf, Bt "m1"⟩, ⟨S cB, owlOneOf, Bt "k1"⟩]) []
  ⟨S cB, rdfsSubClassOf, O cA⟩
#guard has (listAB ++ oneA ++ [⟨S cA, owlUnionOf, Bt "m1"⟩, ⟨S cB, owlUnionOf, Bt "k1"⟩]) []
  ⟨S cA, rdfsSubClassOf, O cB⟩
#guard !has (listAB ++ oneA ++ [⟨S cA, owlUnionOf, Bt "m1"⟩, ⟨S cB, owlUnionOf, Bt "k1"⟩]) []
  ⟨S cB, rdfsSubClassOf, O cA⟩
-- intersection: the direction is reversed
#guard has (listAB ++ oneA ++ [⟨S cA, owlIntersectionOf, Bt "m1"⟩,
            ⟨S cB, owlIntersectionOf, Bt "k1"⟩]) [] ⟨S cB, rdfsSubClassOf, O cA⟩
#guard !has (listAB ++ oneA ++ [⟨S cA, owlIntersectionOf, Bt "m1"⟩,
             ⟨S cB, owlIntersectionOf, Bt "k1"⟩]) [] ⟨S cA, rdfsSubClassOf, O cB⟩

/-! ## End to end: RL closure and the rules, alternating -/

private def sat (g goal : Graph) (t : Triple) : Bool := memB (rbSaturate g goal 8 2) t

-- WebOnt-Class-003 shape: owl:Class membership gives rdfs:Class membership
#guard sat [⟨S iX, rdfType, O owlClass⟩] [⟨S iX, rdfType, O rdfsClass⟩]
  ⟨S iX, rdfType, O rdfsClass⟩
#guard !sat [⟨S iX, rdfType, O cA⟩] [⟨S iX, rdfType, O rdfsClass⟩]
  ⟨S iX, rdfType, O rdfsClass⟩
-- WebOnt-imports-010 shape, from the empty graph
#guard sat [] goalImports ⟨S owlImports, rdfType, O rdfProperty⟩
#guard sat [] goalImports ⟨S owlImports, rdfsRange, O owlOntology⟩
#guard !sat [] goalImports ⟨S owlImports, rdfsRange, O owlClass⟩
-- WebOnt-I5.3-015 shape
#guard sat [⟨S pP, rdfType, O rdfProperty⟩, ⟨S pP, rdfsRange, O xsdInteger⟩,
            ⟨S pP, rdfsRange, O xsdString⟩, ⟨S pQ, rdfType, O rdfProperty⟩]
  [⟨S pP, rdfsSubPropertyOf, O pQ⟩] ⟨S pP, rdfsSubPropertyOf, O pQ⟩
#guard !sat [⟨S pP, rdfType, O rdfProperty⟩, ⟨S pP, rdfsRange, O xsdInteger⟩,
             ⟨S pQ, rdfType, O rdfProperty⟩]
  [⟨S pP, rdfsSubPropertyOf, O pQ⟩] ⟨S pP, rdfsSubPropertyOf, O pQ⟩

end L4Factoidal.OWL.RdfBased.Tests
