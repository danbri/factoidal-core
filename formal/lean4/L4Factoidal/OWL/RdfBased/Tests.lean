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
import L4Factoidal.OWL.RdfBased.Clash

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
-- an empty union or intersection is not read (Table 5.4 for n ≥ 1 only)
#guard !has (listAB ++ [⟨S cA, owlUnionOf, O rdfNil⟩, ⟨S cB, owlUnionOf, Bt "k1"⟩]) []
  ⟨S cA, rdfsSubClassOf, O cB⟩
#guard !has (listAB ++ [⟨S cA, owlIntersectionOf, Bt "k1"⟩, ⟨S cB, owlIntersectionOf, O rdfNil⟩]) []
  ⟨S cA, rdfsSubClassOf, O cB⟩
-- intersection: the direction is reversed
#guard has (listAB ++ oneA ++ [⟨S cA, owlIntersectionOf, Bt "m1"⟩,
            ⟨S cB, owlIntersectionOf, Bt "k1"⟩]) [] ⟨S cB, rdfsSubClassOf, O cA⟩
#guard !has (listAB ++ oneA ++ [⟨S cA, owlIntersectionOf, Bt "m1"⟩,
             ⟨S cB, owlIntersectionOf, Bt "k1"⟩]) [] ⟨S cA, rdfsSubClassOf, O cB⟩

/-! ## hvEqProp (Tables 5.6, 5.8, 5.9, 5.13) -/

private def iV : WfIri := ⟨"http://ex/v", rfl⟩
-- WebOnt-equivalentProperty-005 shape: one restriction with two onProperty values
private def gHv (qFunctional : Bool) : Graph :=
  [ ⟨S pP, rdfType, O owlFunctionalProperty⟩, ⟨S pP, rdfsDomain, Bt "d"⟩,
    ⟨S pQ, rdfsDomain, Bt "d"⟩, ⟨B "d", rdfsSubClassOf, Bt "d"⟩,
    ⟨B "d", owlOnProperty, O pP⟩, ⟨B "d", owlOnProperty, O pQ⟩,
    ⟨B "d", owlHasValue, O iV⟩ ] ++
  (if qFunctional then [⟨S pQ, rdfType, O owlFunctionalProperty⟩] else [])
#guard has (gHv true) [] ⟨S pP, owlEquivalentProperty, O pQ⟩
#guard has (gHv true) [] ⟨S pQ, owlEquivalentProperty, O pP⟩
-- q not functional: no equivalence
#guard !has (gHv false) [] ⟨S pP, owlEquivalentProperty, O pQ⟩

/-! ## literalValue (§ 4.2, Table 5.9) -/

-- the decimal lexical space and value equality (XSD 1.1 Part 2 § 3.3.3)
#guard sameDecimalValue xsdDecimal "01" "1"
#guard sameDecimalValue xsdDecimal "1.50" "+1.5"
#guard sameDecimalValue xsdDecimal "-0" "0.0"
#guard sameDecimalValue xsdDecimal ".5" "0.5"
#guard !sameDecimalValue xsdDecimal "1" "2"
#guard !sameDecimalValue xsdDecimal "1e0" "1"
#guard !sameDecimalValue xsdDecimal "" ""
-- "1.0" is not in the lexical space of xsd:integer
#guard !sameDecimalValue xsdInteger "1.0" "1"
#guard sameDecimalValue xsdInteger "007" "7"

private def bar : WfIri := ⟨"http://ex/bar", rfl⟩
private def lit (s : String) (d : WfIri) : Term :=
  if h : literalWf ⟨s, d, none, none⟩ then .literal ⟨⟨s, d, none, none⟩, h⟩ else .iri d
-- WebOnt-I5.8-017 shape: a datatype IRI that is owl:sameAs xsd:decimal
#guard has [⟨S iX, pP, lit "01" bar⟩, ⟨S bar, owlSameAs, O xsdDecimal⟩]
  [⟨S iX, pP, lit "1" xsdDecimal⟩] ⟨S iX, pP, lit "1" xsdDecimal⟩
-- without the alias the two literals need not denote one value
#guard !has [⟨S iX, pP, lit "01" bar⟩] [⟨S iX, pP, lit "1" xsdDecimal⟩]
  ⟨S iX, pP, lit "1" xsdDecimal⟩
-- with the alias but a different value
#guard !has [⟨S iX, pP, lit "02" bar⟩, ⟨S bar, owlSameAs, O xsdDecimal⟩]
  [⟨S iX, pP, lit "1" xsdDecimal⟩] ⟨S iX, pP, lit "1" xsdDecimal⟩

/-! ## Existential witnesses (Table 5.6, `Witness.lean`) -/

private def gSvf : Graph :=
  [⟨S iA, rdfType, Bt "r"⟩, ⟨B "r", owlSomeValuesFrom, O cA⟩, ⟨B "r", owlOnProperty, O pP⟩]
private def witHas (g goal : Graph) (s : Subject) (p : WfIri) : Bool :=
  (svfWitTriples g goal).any (fun t => t.s == s && t.p == p)
-- the goal asks for a p-successor of a
#guard witHas gSvf [⟨S iA, pP, Bt "w"⟩] (S iA) pP
#guard (svfWitTriples gSvf [⟨S iA, pP, Bt "w"⟩]).length == 2
-- not asked for: no witness
#guard !witHas gSvf [⟨S iA, pQ, Bt "w"⟩] (S iA) pP
-- a is not typed with the restriction: no witness
#guard (svfWitTriples [⟨B "r", owlSomeValuesFrom, O cA⟩, ⟨B "r", owlOnProperty, O pP⟩]
  [⟨S iA, pP, Bt "w"⟩]).isEmpty
-- a label already used in the graph is not fresh: no witness
#guard (svfWitTriples (gSvf ++ [⟨B (svfWitLabel (S iA) (B "r")), rdfType, O cA⟩])
  [⟨S iA, pP, Bt "w"⟩]).isEmpty
-- two classes behind one label: the label does not name one witness, so none is added
#guard (svfWitTriples (gSvf ++ [⟨B "r", owlSomeValuesFrom, O cB⟩]) [⟨S iA, pP, Bt "w"⟩]).isEmpty

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
-- WebOnt-someValuesFrom-003 shape: two successors deep, through the RL closure
private def gPerson : Graph :=
  [ ⟨S cA, owlEquivalentClass, Bt "r"⟩, ⟨B "r", owlOnProperty, O pP⟩,
    ⟨B "r", owlSomeValuesFrom, O cA⟩, ⟨S iA, rdfType, O cA⟩ ]
private def chain2 (g : Graph) : Bool :=
  let c := rbSaturate g [⟨S iA, pP, Bt "u"⟩, ⟨B "u", pP, Bt "v"⟩] 8 3
  c.any (fun t1 => t1.s == S iA && t1.p == pP &&
    (match t1.o.toSubject? with
     | some m => c.any (fun t2 => t2.s == m && t2.p == pP)
     | none => false))
#guard chain2 gPerson
#guard !chain2 [⟨S cA, owlEquivalentClass, Bt "r"⟩, ⟨B "r", owlOnProperty, O pP⟩,
                ⟨B "r", owlSomeValuesFrom, O cA⟩]
-- WebOnt-I5.3-015 shape
#guard sat [⟨S pP, rdfType, O rdfProperty⟩, ⟨S pP, rdfsRange, O xsdInteger⟩,
            ⟨S pP, rdfsRange, O xsdString⟩, ⟨S pQ, rdfType, O rdfProperty⟩]
  [⟨S pP, rdfsSubPropertyOf, O pQ⟩] ⟨S pP, rdfsSubPropertyOf, O pQ⟩
#guard !sat [⟨S pP, rdfType, O rdfProperty⟩, ⟨S pP, rdfsRange, O xsdInteger⟩,
             ⟨S pQ, rdfType, O rdfProperty⟩]
  [⟨S pP, rdfsSubPropertyOf, O pQ⟩] ⟨S pP, rdfsSubPropertyOf, O pQ⟩

/-! ## Clash rows (`Clash.lean`)

Each row has a POSITIVE case (a graph the row's soundness proof reads
as inconsistent) and NEGATIVE cases that change the premise the proof
reads; a clash check that fired on every graph fails the negative half. -/

private def clashes (g : Graph) : Bool := rbClashAny g

-- thingEnum. WebOnt-Thing-005 shape: owl:Thing owl:oneOf ( s ).
#guard clashes (oneA ++ [⟨S owlThing, owlOneOf, Bt "m1"⟩])
#guard clashes (oneA ++ [⟨S rdfsResource, owlOneOf, Bt "m1"⟩])
#guard clashes [⟨S owlThing, owlOneOf, O rdfNil⟩]
-- a class owl:Thing is a subclass of
#guard clashes (oneA ++ [⟨S cA, owlOneOf, Bt "m1"⟩, ⟨S owlThing, rdfsSubClassOf, O cA⟩])
-- two members: IR may have two elements, so no clash from this row
#guard !clashes (oneAB ++ [⟨S owlThing, owlOneOf, Bt "m1"⟩])
-- one member, but of a class owl:Thing is not stated to be under
#guard !clashes (oneA ++ [⟨S cA, owlOneOf, Bt "m1"⟩])
#guard !clashes (oneA ++ [⟨S cA, owlOneOf, Bt "m1"⟩, ⟨S cA, rdfsSubClassOf, O owlThing⟩])
-- end to end: the RL closure and the rules, then the row
#guard clashes (rbSaturate (oneA ++ [⟨S owlThing, owlOneOf, Bt "m1"⟩]) [] 8 1)
#guard !clashes (rbSaturate (oneAB ++ [⟨S owlThing, owlOneOf, Bt "m1"⟩]) [] 8 1)

-- svfAvfDt. inconsistent_datatypes shape: ∃p.integer and ∀p.string on one subject.
private def gSvfAvf (d2 : WfIri) (p2 : WfIri) : Graph :=
  [ ⟨S iA, rdfType, Bt "r1"⟩, ⟨B "r1", owlSomeValuesFrom, O xsdInteger⟩,
    ⟨B "r1", owlOnProperty, O pP⟩, ⟨S iA, rdfType, Bt "r2"⟩,
    ⟨B "r2", owlAllValuesFrom, O d2⟩, ⟨B "r2", owlOnProperty, O p2⟩ ]
#guard clashes (gSvfAvf xsdString pP)
#guard clashes (gSvfAvf xsdBoolean pP)
-- xsd:decimal contains the integers: no clash
#guard !clashes (gSvfAvf xsdDecimal pP)
-- the universal restriction is on another property
#guard !clashes (gSvfAvf xsdString pQ)
-- the subject is not a member of the existential restriction
#guard !clashes ((gSvfAvf xsdString pP).filter (fun t => t != ⟨S iA, rdfType, Bt "r1"⟩))
-- end to end: class A under both restrictions, a in A
#guard clashes (rbSaturate
  [ ⟨S cA, rdfsSubClassOf, Bt "r1"⟩, ⟨B "r1", owlSomeValuesFrom, O xsdInteger⟩,
    ⟨B "r1", owlOnProperty, O pP⟩, ⟨S cA, rdfsSubClassOf, Bt "r2"⟩,
    ⟨B "r2", owlAllValuesFrom, O xsdString⟩, ⟨B "r2", owlOnProperty, O pP⟩,
    ⟨S iA, rdfType, O cA⟩ ] [] 8 1)
#guard !clashes (rbSaturate
  [ ⟨S cA, rdfsSubClassOf, Bt "r1"⟩, ⟨B "r1", owlSomeValuesFrom, O xsdInteger⟩,
    ⟨B "r1", owlOnProperty, O pP⟩, ⟨S cA, rdfsSubClassOf, Bt "r2"⟩,
    ⟨B "r2", owlAllValuesFrom, O xsdString⟩, ⟨B "r2", owlOnProperty, O pP⟩,
    ⟨S iA, rdfType, O cB⟩ ] [] 8 1)

-- Data successors. A one- or two-member list of literals at label `n`.
private def lits1 (n : String) (a : Term) : Graph :=
  [⟨B n, rdfFirst, a⟩, ⟨B n, rdfRest, O rdfNil⟩]
private def lits2 (n : String) (a b : Term) : Graph :=
  [⟨B n, rdfFirst, a⟩, ⟨B n, rdfRest, Bt (n ++ "'")⟩,
   ⟨B (n ++ "'"), rdfFirst, b⟩, ⟨B (n ++ "'"), rdfRest, O rdfNil⟩]
/-- `iA` is in `∃pP.sv` and in `∀pP.d` for each `d` of `avfs`. -/
private def succG (sv : Term) (avfs : List Term) : Graph :=
  [⟨S iA, rdfType, Bt "rs"⟩, ⟨B "rs", owlSomeValuesFrom, sv⟩, ⟨B "rs", owlOnProperty, O pP⟩] ++
  (avfs.zip (List.range avfs.length)).flatMap (fun (d, n) =>
    [⟨S iA, rdfType, Bt s!"ra{n}"⟩, ⟨B s!"ra{n}", owlAllValuesFrom, d⟩,
     ⟨B s!"ra{n}", owlOnProperty, O pP⟩])
/-- An integer restriction at label `n` with one facet. -/
private def restr1 (n : String) (e : WfIri) (f : WfIri) (v : Term) : Graph :=
  [⟨B n, owlOnDatatype, O e⟩, ⟨B n, owlWithRestrictions, Bt (n ++ "l")⟩,
   ⟨B (n ++ "l"), rdfFirst, Bt (n ++ "f")⟩, ⟨B (n ++ "l"), rdfRest, O rdfNil⟩,
   ⟨B (n ++ "f"), f, v⟩]

-- litSucc, exclusion by a datatype. Inconsistent Byte Filler shape.
#guard clashes (succG (Bt "e") [O xsdByte] ++ lits1 "el" (lit "6542145" xsdInteger) ++
  [⟨B "e", owlOneOf, Bt "el"⟩])
#guard !clashes (succG (Bt "e") [O xsdByte] ++ lits1 "el" (lit "100" xsdInteger) ++
  [⟨B "e", owlOneOf, Bt "el"⟩])
-- the range of the property excludes it as well
#guard clashes (succG (Bt "e") [] ++ lits1 "el" (lit "6542145" xsdInteger) ++
  [⟨B "e", owlOneOf, Bt "el"⟩, ⟨S pP, rdfsRange, O xsdByte⟩])
#guard !clashes (succG (Bt "e") [] ++ lits1 "el" (lit "6542145" xsdInteger) ++
  [⟨B "e", owlOneOf, Bt "el"⟩, ⟨S pQ, rdfsRange, O xsdByte⟩])
-- litSucc, exclusion by an integer restriction and an enumeration.
-- Contradicting datatype Restrictions shape: ∃p.integer[≥ 4], ∀p.{3, 4}, ∀p.{2, 3}.
private def gContra (second : Term) : Graph :=
  succG (Bt "d0") [Bt "e1", Bt "e2"] ++ restr1 "d0" xsdInteger xsdFacetMinInclusive (lit "4" xsdInteger) ++
  lits2 "l1" (lit "3" xsdInteger) (lit "4" xsdInteger) ++ lits2 "l2" (lit "2" xsdInteger) second ++
  [⟨B "e1", owlOneOf, Bt "l1"⟩, ⟨B "e2", owlOneOf, Bt "l2"⟩]
#guard clashes (gContra (lit "3" xsdInteger))
-- {2, 4} in place of {2, 3}: 4 is in all three classes
#guard !clashes (gContra (lit "4" xsdInteger))
-- the same value written with another integer datatype is the same value
#guard !clashes (gContra (lit "4" xsdShort))
-- litSucc, exclusion by a datatype complement.
-- Inconsistent Data Complement shape: ∀p.{3, 4}, ∀p.{2, 3}, ∃p.(complement of {3}).
private def gCompl (excluded : Term) : Graph :=
  succG (Bt "c") [Bt "e1", Bt "e2"] ++ lits2 "l1" (lit "3" xsdInteger) (lit "4" xsdIntIri) ++
  lits2 "l2" (lit "2" xsdShort) (lit "3" xsdInteger) ++ lits1 "l3" excluded ++
  [⟨B "e1", owlOneOf, Bt "l1"⟩, ⟨B "e2", owlOneOf, Bt "l2"⟩,
   ⟨B "c", owlDatatypeComplementOf, Bt "e3"⟩, ⟨B "e3", owlOneOf, Bt "l3"⟩]
#guard clashes (gCompl (lit "3" xsdInteger))
#guard clashes (gCompl (lit "03" xsdByte))
#guard !clashes (gCompl (lit "5" xsdInteger))
-- intSucc. datatype-restriction-min-max-inconsistency shape:
-- ∃p.integer[≥ 18], ∀p.integer[≤ 10].
private def gMinMax (hi : String) : Graph :=
  succG (Bt "d0") [Bt "d1"] ++
  restr1 "d0" xsdInteger xsdFacetMinInclusive (lit "18" xsdInteger) ++
  restr1 "d1" xsdInteger xsdFacetMaxInclusive (lit hi xsdInteger)
#guard clashes (gMinMax "10")
#guard clashes (gMinMax "17")
#guard !clashes (gMinMax "18")
-- an exclusive bound: integer[< 18] and integer[≥ 18]
#guard clashes (succG (Bt "d0") [Bt "d1"] ++
  restr1 "d0" xsdInteger xsdFacetMinInclusive (lit "18" xsdInteger) ++
  restr1 "d1" xsdInteger xsdFacetMaxExclusive (lit "18" xsdInteger))
-- intSucc against a datatype's bounds: byte[≥ 200] is empty, byte holds 100
#guard clashes (succG (Bt "d0") [O xsdByte] ++
  restr1 "d0" xsdInteger xsdFacetMinInclusive (lit "200" xsdInteger))
#guard !clashes (succG (Bt "d0") [O xsdByte] ++
  restr1 "d0" xsdInteger xsdFacetMinInclusive (lit "100" xsdInteger))
-- the restriction is on xsd:decimal, which this row does not read
#guard !clashes (succG (Bt "d0") [Bt "d1"] ++
  restr1 "d0" xsdDecimal xsdFacetMinInclusive (lit "18" xsdInteger) ++
  restr1 "d1" xsdInteger xsdFacetMaxInclusive (lit "10" xsdInteger))
-- no existential restriction: no successor is asked for
#guard !clashes ((gMinMax "10").filter (fun t => t.p != owlSomeValuesFrom))

-- every facet node of the restriction must carry a facet pair (Table 5.7
-- reads one pair per member of the list): a second, bare node blocks the row
private def gBareFacet : Graph :=
  (gMinMax "10").filter (fun t => t != (⟨B "d0l", rdfRest, O rdfNil⟩ : Triple)) ++
  [⟨B "d0l", rdfRest, Bt "d0m"⟩, ⟨B "d0m", rdfFirst, Bt "bare"⟩, ⟨B "d0m", rdfRest, O rdfNil⟩]
#guard !clashes gBareFacet
-- the same list with the facet on the second node as well: the row fires
#guard clashes (gBareFacet ++ [⟨B "bare", xsdFacetMinInclusive, lit "18" xsdInteger⟩])

-- Literal values (§ 4.2, XSD 1.1 Part 2 § 3.3.1, § 3.4).
private def wl (s : String) (d : WfIri) : WfLiteral :=
  if h : literalWf ⟨s, d, none, none⟩ then ⟨_, h⟩ else ⟨⟨"", xsdString, none, none⟩, by decide⟩
#guard intLitValue (wl "-0" xsdNonNegativeInteger) == some 0
#guard intLitValue (wl "+007" xsdByte) == some 7
-- outside the bounds of xsd:byte: ill-typed, no value
#guard intLitValue (wl "300" xsdByte) == none
#guard intLitValue (wl "0" xsdPositiveInteger) == none
#guard intLitValue (wl "1.0" xsdInteger) == none
#guard litSame (wl "-0" xsdInteger) (wl "0" xsdUnsignedInt)
#guard !litSame (wl "300" xsdByte) (wl "300" xsdShort)
#guard litDistinct (wl "4" xsdIntIri) (wl "3" xsdInteger)
#guard !litDistinct (wl "4" xsdIntIri) (wl "04" xsdInteger)
#guard litDistinct (wl "ab" xsdString) (wl "ac" xsdString)
-- U+0000 is not in the lexical space of xsd:string: no value, so not distinct
#guard !litDistinct (wl "a\x00" xsdString) (wl "ac" xsdString)
#guard litOutsideDt (wl "6542145" xsdInteger) xsdByte
#guard !litOutsideDt (wl "127" xsdInteger) xsdByte
#guard litOutsideDt (wl "3" xsdInteger) xsdString
#guard !litOutsideDt (wl "3" xsdInteger) xsdDecimal

/-! ## minCardSucc (Table 5.6, `owl:minCardinality` 0 or 1) -/

private def gMinCard (n : Term) (onP : WfIri) : Graph :=
  [⟨B "z", owlMinCardinality, n⟩, ⟨B "z", owlOnProperty, O onP⟩, ⟨S iA, pP, O iB⟩]
#guard has (gMinCard (lit "1" xsdIntIri) pP) [] ⟨S iA, rdfType, Bt "z"⟩
#guard has (gMinCard (lit "0" xsdNonNegativeInteger) pP) [] ⟨S iA, rdfType, Bt "z"⟩
-- two successors are needed for a minimum of 2
#guard !has (gMinCard (lit "2" xsdNonNegativeInteger) pP) [] ⟨S iA, rdfType, Bt "z"⟩
-- the restriction is on another property
#guard !has (gMinCard (lit "1" xsdIntIri) pQ) [] ⟨S iA, rdfType, Bt "z"⟩
-- the object of the subject's edge is not a member
#guard !has (gMinCard (lit "1" xsdIntIri) pP) [] ⟨S iB, rdfType, Bt "z"⟩
-- a comprehension witness of the RL closure is not read (§ 8 is not normative)
#guard !has [⟨B "__rl_minc1__http://ex/p", owlMinCardinality, lit "1" xsdNonNegativeInteger⟩,
  ⟨B "__rl_minc1__http://ex/p", owlOnProperty, O pP⟩, ⟨S iA, pP, O iB⟩] []
  ⟨S iA, rdfType, Bt "__rl_minc1__http://ex/p"⟩
-- WebOnt-disjointWith-010 shape: the RL closure then has `a rdf:type _:z`
-- next to `_:z owl:disjointWith _:z`, which the RL clash row cax-dw reads
#guard memB (rbSaturate (gMinCard (lit "1" xsdIntIri) pP ++
  [⟨B "z", owlDisjointWith, Bt "z"⟩]) [] 8 1) ⟨S iA, rdfType, Bt "z"⟩

/-! ## Exclusions of a pair (Tables 5.9, 5.15) -/

private def dp1 : WfIri := ⟨"http://ex/dp1", rfl⟩
private def dp2 : WfIri := ⟨"http://ex/dp2", rfl⟩
-- intOneSucc. Inconsistent Disjoint Dataproperties shape: a dp1 10,
-- a ∈ ∃dp2.integer[≥ 10, ≤ 10], dp1 and dp2 disjoint.
private def gDisjDp (v : String) (hi : String) : Graph :=
  [ ⟨S iA, dp1, lit v xsdInteger⟩, ⟨S dp1, owlPropertyDisjointWith, O dp2⟩,
    ⟨S iA, rdfType, Bt "r"⟩, ⟨B "r", owlSomeValuesFrom, Bt "d"⟩, ⟨B "r", owlOnProperty, O dp2⟩,
    ⟨B "d", owlOnDatatype, O xsdInteger⟩, ⟨B "d", owlWithRestrictions, Bt "l"⟩,
    ⟨B "l", rdfFirst, Bt "f1"⟩, ⟨B "l", rdfRest, Bt "l2"⟩,
    ⟨B "l2", rdfFirst, Bt "f2"⟩, ⟨B "l2", rdfRest, O rdfNil⟩,
    ⟨B "f1", xsdFacetMinInclusive, lit "10" xsdInteger⟩,
    ⟨B "f2", xsdFacetMaxInclusive, lit hi xsdInteger⟩ ]
#guard clashes (gDisjDp "10" "10")
#guard clashes (gDisjDp "+010" "10")
-- the restriction holds 10 and 11: no clash from one value
#guard !clashes (gDisjDp "10" "11")
-- the asserted value is 9
#guard !clashes (gDisjDp "9" "10")
-- the disjointness stated the other way round
#guard clashes ((gDisjDp "10" "10").map (fun t =>
  if t.p == owlPropertyDisjointWith then ⟨S dp2, owlPropertyDisjointWith, O dp1⟩ else t))
-- litSucc with a negative property assertion and owl:real.
-- Minus Infinity is not in owl:real shape: ∀dp.owl:real, ∃dp.{-INF^^float, -0},
-- and the negative assertion (a, dp, 0^^unsignedInt).
private def gMinusInf (npaValue : Term) : Graph :=
  succG (Bt "e") [O XSD.owlReal] ++ lits2 "l1" (lit "-INF" XSD.xsdFloat) (lit "-0" xsdInteger) ++
  [⟨B "e", owlOneOf, Bt "l1"⟩, ⟨B "n", rdfType, O owlNegativePropertyAssertion⟩,
   ⟨B "n", owlSourceIndividual, O iA⟩, ⟨B "n", owlAssertionProperty, O pP⟩,
   ⟨B "n", owlTargetValue, npaValue⟩]
#guard clashes (gMinusInf (lit "0" xsdUnsignedInt))
#guard !clashes (gMinusInf (lit "1" xsdUnsignedInt))
-- the negative assertion is about another subject
#guard !clashes ((gMinusInf (lit "0" xsdUnsignedInt)).map (fun t =>
  if t.p == owlSourceIndividual then ⟨B "n", owlSourceIndividual, O iB⟩ else t))
#guard litOutsideDt (wl "-INF" XSD.xsdFloat) XSD.owlReal
#guard litOutsideDt (wl "1.0" xsdDouble) xsdIntIri
#guard !litOutsideDt (wl "-INF" XSD.xsdFloat) XSD.xsdFloat

end L4Factoidal.OWL.RdfBased.Tests
