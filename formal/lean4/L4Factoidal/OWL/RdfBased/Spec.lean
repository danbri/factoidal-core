/-
L4Factoidal.OWL.RdfBased.Spec — the OWL 2 RDF-Based Semantics: an
interpretation, the semantic conditions the regime's rules read, and
entailment.

Source: OWL 2 Web Ontology Language RDF-Based Semantics (Second
Edition), W3C Recommendation 11 December 2012,
https://www.w3.org/TR/owl2-rdf-based-semantics/. Section numbers below
are that document's. Design record:
`docs/designissues/2026-10-10-owl2-rdf-based-semantics.md`; tracking
issue https://github.com/danbri/factoidal/issues/721.

## The interpretation

§4.2 defines an OWL 2 RDF-Based interpretation as a D-interpretation
`I = (IR, IP, IEXT, IS, IL, LV)` that meets every condition of §5. This
module uses the record `L4Factoidal.RDF.Interp` (domain `idom` = IR,
`iIri` = IS, `iLit` = IL, `iext` = IEXT totalised over the domain), and
the class extension `icext` (§4.5: `ICEXT(c) = {x | (x, c) ∈
IEXT(I(rdf:type))}`). The parts of the universe (§4.4, Table 4.1) are
class extensions of vocabulary classes: IC is `ICEXT(I(rdfs:Class))`, IP
is `ICEXT(I(rdf:Property))`.

## A SUBSET of the conditions, and why that is the safe direction

`RdfBasedConditions` collects the §5 conditions the rules of
`RdfBased/Rules.lean` read, each transcribed from its table row and
cited. Where a table states an "iff" and a rule reads one half only, only
that half is stated. Every OWL 2 RDF-Based interpretation meets every
condition here, so the class of interpretations this bundle admits
CONTAINS the class §4.2 defines. `RbEntails g1 g2` (every interpretation
of the bundle that satisfies `g1` satisfies `g2`) therefore implies
OWL 2 RDF-Based entailment (Definition 4.5). The converse does not hold
and is not claimed: the bundle is not the whole semantics.

Entailment under the full semantics is undecidable (§1, "the OWL 2
RDF-Based Semantics ... is undecidable"; OWL 2 Conformance §2.2.2), so
this tree proves entailments and never refutes one: see the design
record for the verdict buckets.

## The bundle is satisfiable, and does not entail everything

A bundle no interpretation meets would make every `RbEntails` statement
true (skill `measuring-inference` § 4). `witnessInterp` below meets
every condition and does not satisfy `owl:Thing rdfs:subClassOf
owl:Nothing`, so `RbEntails [] [that triple]` is false
(`rbEntails_not_everything`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.Semantics
import L4Factoidal.OWL.RLRules

namespace L4Factoidal.OWL.RdfBased

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.RDFS (rdfsClass rdfsLiteral rdfProperty rdfsResource rdfList)

/-! ## Vocabulary the OWL 2 RL tree does not name -/

def owlOntology : WfIri := ⟨"http://www.w3.org/2002/07/owl#Ontology", rfl⟩
def owlOntologyProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#OntologyProperty", rfl⟩
def owlDataRange : WfIri := ⟨"http://www.w3.org/2002/07/owl#DataRange", rfl⟩
def owlDeprecatedClass : WfIri := ⟨"http://www.w3.org/2002/07/owl#DeprecatedClass", rfl⟩
def owlDeprecatedProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#DeprecatedProperty", rfl⟩
def owlNamedIndividual : WfIri := ⟨"http://www.w3.org/2002/07/owl#NamedIndividual", rfl⟩
def owlNegativePropertyAssertion : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#NegativePropertyAssertion", rfl⟩
def owlAxiom : WfIri := ⟨"http://www.w3.org/2002/07/owl#Axiom", rfl⟩
def owlAnnotation : WfIri := ⟨"http://www.w3.org/2002/07/owl#Annotation", rfl⟩
def owlImports : WfIri := ⟨"http://www.w3.org/2002/07/owl#imports", rfl⟩
def owlVersionIRI : WfIri := ⟨"http://www.w3.org/2002/07/owl#versionIRI", rfl⟩
def owlDisjointUnionOf : WfIri := ⟨"http://www.w3.org/2002/07/owl#disjointUnionOf", rfl⟩
def owlOnDataRange : WfIri := ⟨"http://www.w3.org/2002/07/owl#onDataRange", rfl⟩
def owlOnDatatype : WfIri := ⟨"http://www.w3.org/2002/07/owl#onDatatype", rfl⟩
def owlOnProperties : WfIri := ⟨"http://www.w3.org/2002/07/owl#onProperties", rfl⟩
def owlWithRestrictions : WfIri := ⟨"http://www.w3.org/2002/07/owl#withRestrictions", rfl⟩
def owlDatatypeComplementOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#datatypeComplementOf", rfl⟩
def owlAnnotatedSource : WfIri := ⟨"http://www.w3.org/2002/07/owl#annotatedSource", rfl⟩
def owlAnnotatedProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#annotatedProperty", rfl⟩
def owlAnnotatedTarget : WfIri := ⟨"http://www.w3.org/2002/07/owl#annotatedTarget", rfl⟩

/-! ## Tables -/

/-- The classes `I(E) ∈ IC` names. Table 5.2, column 2 ("I(E) ∈ IC";
`rdfs:Literal` is "∈ IDC", and IDC ⊆ IC by Table 5.1), and the RDFS
axiomatic triple `rdf:List rdf:type rdfs:Class` (RDF 1.1 Semantics §9.1,
retained by §5 of the RDF-Based Semantics). -/
def vocabClasses : List WfIri :=
  [ owlAllDifferent, owlAllDisjointClasses, owlAllDisjointProperties, owlAnnotation,
    owlAnnotationProperty, owlAsymmetricProperty, owlAxiom, rdfsClass, owlClass,
    owlDataRange, rdfsDatatype, owlDatatypeProperty, owlDeprecatedClass,
    owlDeprecatedProperty, owlFunctionalProperty, owlInverseFunctionalProperty,
    owlIrreflexiveProperty, rdfsLiteral, owlNamedIndividual, owlNegativePropertyAssertion,
    owlNothing, owlObjectProperty, owlOntology, owlOntologyProperty, rdfProperty,
    owlReflexiveProperty, rdfsResource, owlRestriction, owlSymmetricProperty, owlThing,
    owlTransitiveProperty, rdfList ]

/-- `(E1, E2)`: `ICEXT(I(E1)) ⊆ ICEXT(I(E2))`. Table 5.2, column 3
("⊆ IP", "⊆ IC", and each "= S" row in both directions with the class
whose extension is S), and Table 5.1 ("IDC ⊆ IC", "IODP ⊆ IP",
"IOXP ⊆ IP", "IOAP ⊆ IP"). -/
def extSubTable : List (WfIri × WfIri) :=
  [ -- Table 5.2 "⊆ IP"
    (owlAsymmetricProperty, rdfProperty), (owlDeprecatedProperty, rdfProperty),
    (owlFunctionalProperty, rdfProperty), (owlInverseFunctionalProperty, rdfProperty),
    (owlIrreflexiveProperty, rdfProperty), (owlReflexiveProperty, rdfProperty),
    (owlSymmetricProperty, rdfProperty), (owlTransitiveProperty, rdfProperty),
    -- Table 5.2 "⊆ IC"
    (owlDeprecatedClass, rdfsClass), (owlRestriction, rdfsClass),
    -- Table 5.2 "= IC", "= IDC", "= IP", "= IR", both directions
    (owlClass, rdfsClass), (rdfsClass, owlClass),
    (owlDataRange, rdfsDatatype), (rdfsDatatype, owlDataRange),
    (owlObjectProperty, rdfProperty), (rdfProperty, owlObjectProperty),
    (owlThing, rdfsResource), (rdfsResource, owlThing),
    -- Table 5.1
    (rdfsDatatype, rdfsClass), (owlDatatypeProperty, rdfProperty),
    (owlOntologyProperty, rdfProperty), (owlAnnotationProperty, rdfProperty) ]

/-- One row of Table 5.3: `I(E) ∈ part` and `IEXT(I(E)) ⊆ dom × rng`,
each part written as the vocabulary class whose extension it is (IP =
`rdf:Property`, IOXP = `owl:OntologyProperty`, IOAP =
`owl:AnnotationProperty`, IR = `rdfs:Resource`, IC = `rdfs:Class`, IDC =
`rdfs:Datatype`, IX = `owl:Ontology`, LV = `rdfs:Literal`, ISEQ =
`rdf:List` (§5, "Set names"), `ICEXT(I(owl:Restriction))` =
`owl:Restriction`). A row whose IRI is in two parts appears twice. Rows
with "= ∅" or "= IR × IR" and rows whose range is INNI are not
transcribed. -/
structure PropRow where
  e : WfIri
  part : WfIri
  dom : WfIri
  rng : WfIri
deriving DecidableEq, Repr

/-- Table 5.3, transcribed row by row (subset named above). -/
def vocabPropTable : List PropRow :=
  [ ⟨owlAllValuesFrom, rdfProperty, owlRestriction, rdfsClass⟩,
    ⟨owlAnnotatedProperty, rdfProperty, rdfsResource, rdfsResource⟩,
    ⟨owlAnnotatedSource, rdfProperty, rdfsResource, rdfsResource⟩,
    ⟨owlAnnotatedTarget, rdfProperty, rdfsResource, rdfsResource⟩,
    ⟨owlAssertionProperty, rdfProperty, owlNegativePropertyAssertion, rdfProperty⟩,
    ⟨owlBackwardCompatibleWith, owlOntologyProperty, owlOntology, owlOntology⟩,
    ⟨owlBackwardCompatibleWith, owlAnnotationProperty, owlOntology, owlOntology⟩,
    ⟨rdfsComment, owlAnnotationProperty, rdfsResource, rdfsLiteral⟩,
    ⟨owlComplementOf, rdfProperty, rdfsClass, rdfsClass⟩,
    ⟨owlDatatypeComplementOf, rdfProperty, rdfsDatatype, rdfsDatatype⟩,
    ⟨owlDeprecated, owlAnnotationProperty, rdfsResource, rdfsResource⟩,
    ⟨owlDifferentFrom, rdfProperty, rdfsResource, rdfsResource⟩,
    ⟨owlDisjointUnionOf, rdfProperty, rdfsClass, rdfList⟩,
    ⟨owlDisjointWith, rdfProperty, rdfsClass, rdfsClass⟩,
    ⟨owlDistinctMembers, rdfProperty, owlAllDifferent, rdfList⟩,
    ⟨owlEquivalentClass, rdfProperty, rdfsClass, rdfsClass⟩,
    ⟨owlEquivalentProperty, rdfProperty, rdfProperty, rdfProperty⟩,
    ⟨owlHasKey, rdfProperty, rdfsClass, rdfList⟩,
    ⟨owlHasSelf, rdfProperty, owlRestriction, rdfsResource⟩,
    ⟨owlHasValue, rdfProperty, owlRestriction, rdfsResource⟩,
    ⟨owlImports, owlOntologyProperty, owlOntology, owlOntology⟩,
    ⟨owlIncompatibleWith, owlOntologyProperty, owlOntology, owlOntology⟩,
    ⟨owlIncompatibleWith, owlAnnotationProperty, owlOntology, owlOntology⟩,
    ⟨owlIntersectionOf, rdfProperty, rdfsClass, rdfList⟩,
    ⟨owlInverseOf, rdfProperty, rdfProperty, rdfProperty⟩,
    ⟨rdfsIsDefinedBy, owlAnnotationProperty, rdfsResource, rdfsResource⟩,
    ⟨rdfsLabel, owlAnnotationProperty, rdfsResource, rdfsLiteral⟩,
    ⟨owlMembers, rdfProperty, rdfsResource, rdfList⟩,
    ⟨owlOnClass, rdfProperty, owlRestriction, rdfsClass⟩,
    ⟨owlOnDataRange, rdfProperty, owlRestriction, rdfsDatatype⟩,
    ⟨owlOnDatatype, rdfProperty, rdfsDatatype, rdfsDatatype⟩,
    ⟨owlOneOf, rdfProperty, rdfsClass, rdfList⟩,
    ⟨owlOnProperty, rdfProperty, owlRestriction, rdfProperty⟩,
    ⟨owlOnProperties, rdfProperty, owlRestriction, rdfList⟩,
    ⟨owlPriorVersion, owlOntologyProperty, owlOntology, owlOntology⟩,
    ⟨owlPriorVersion, owlAnnotationProperty, owlOntology, owlOntology⟩,
    ⟨owlPropertyChainAxiom, rdfProperty, rdfProperty, rdfList⟩,
    ⟨owlPropertyDisjointWith, rdfProperty, rdfProperty, rdfProperty⟩,
    ⟨owlSameAs, rdfProperty, rdfsResource, rdfsResource⟩,
    ⟨rdfsSeeAlso, owlAnnotationProperty, rdfsResource, rdfsResource⟩,
    ⟨owlSomeValuesFrom, rdfProperty, owlRestriction, rdfsClass⟩,
    ⟨owlSourceIndividual, rdfProperty, owlNegativePropertyAssertion, rdfsResource⟩,
    ⟨owlTargetIndividual, rdfProperty, owlNegativePropertyAssertion, rdfsResource⟩,
    ⟨owlTargetValue, rdfProperty, owlNegativePropertyAssertion, rdfsLiteral⟩,
    ⟨owlUnionOf, rdfProperty, rdfsClass, rdfList⟩,
    ⟨owlVersionInfo, owlAnnotationProperty, rdfsResource, rdfsResource⟩,
    ⟨owlVersionIRI, owlOntologyProperty, owlOntology, owlOntology⟩,
    ⟨owlWithRestrictions, rdfProperty, rdfsDatatype, rdfList⟩ ]

/-- The classes whose extension is the whole universe: Table 5.2,
`ICEXT(I(owl:Thing)) = IR` and `ICEXT(I(rdfs:Resource)) = IR`. -/
def universalClasses : List WfIri := [owlThing, rdfsResource]

/-! ## The semantic conditions -/

section Conditions

variable (i : Interp)

/-- IC, the classes: `ICEXT(I(rdfs:Class))` (Table 4.1). -/
def IC (x : i.idom) : Prop := icext i x (i.iIri rdfsClass)

/-- IP, the properties: `ICEXT(I(rdf:Property))` (Table 4.1). -/
def IP (x : i.idom) : Prop := icext i x (i.iIri rdfProperty)

/-- Table 5.2, column 2: every listed vocabulary class is a class. -/
def CondVocabClasses : Prop := ∀ e ∈ vocabClasses, IC i (i.iIri e)

/-- Table 5.2, column 3, and Table 5.1: the listed extension inclusions. -/
def CondExtSub : Prop :=
  ∀ e ∈ extSubTable, ∀ x : i.idom, icext i x (i.iIri e.1) → icext i x (i.iIri e.2)

/-- Table 5.2: `ICEXT(I(owl:Thing)) = IR`, `ICEXT(I(rdfs:Resource)) = IR`. -/
def CondUniversal : Prop := ∀ c ∈ universalClasses, ∀ x : i.idom, icext i x (i.iIri c)

/-- Table 5.2: `ICEXT(I(owl:Nothing)) = ∅`. -/
def CondNothing : Prop := ∀ x : i.idom, ¬ icext i x (i.iIri owlNothing)

/-- Table 5.3, the transcribed rows: `I(E) ∈ part` and
`IEXT(I(E)) ⊆ dom × rng`. -/
def CondVocabProps : Prop :=
  ∀ r ∈ vocabPropTable, icext i (i.iIri r.e) (i.iIri r.part) ∧
    ∀ x y : i.idom, i.iext (i.iIri r.e) x y →
      icext i x (i.iIri r.dom) ∧ icext i y (i.iIri r.rng)

/-- Table 5.8, `rdfs:subClassOf`, the full iff. -/
def CondSubClassOf : Prop :=
  ∀ c1 c2 : i.idom, i.iext (i.iIri rdfsSubClassOf) c1 c2 ↔
    (IC i c1 ∧ IC i c2 ∧ ∀ x, icext i x c1 → icext i x c2)

/-- Table 5.8, `rdfs:subPropertyOf`: the right-to-left half of the iff. -/
def CondSubPropertyOfIf : Prop :=
  ∀ p1 p2 : i.idom, IP i p1 → IP i p2 → (∀ x y, i.iext p1 x y → i.iext p2 x y) →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2

/-- Table 5.8, `rdfs:domain`, the full iff. -/
def CondDomain : Prop :=
  ∀ p c : i.idom, i.iext (i.iIri rdfsDomain) p c ↔
    (IP i p ∧ IC i c ∧ ∀ x y, i.iext p x y → icext i x c)

/-- Table 5.8, `rdfs:range`, the full iff. -/
def CondRange : Prop :=
  ∀ p c : i.idom, i.iext (i.iIri rdfsRange) p c ↔
    (IP i p ∧ IC i c ∧ ∀ x y, i.iext p x y → icext i y c)

/-- Table 5.9, `owl:equivalentClass`: the right-to-left half. -/
def CondEquivalentClassIf : Prop :=
  ∀ c1 c2 : i.idom, IC i c1 → IC i c2 → (∀ x, icext i x c1 ↔ icext i x c2) →
    i.iext (i.iIri owlEquivalentClass) c1 c2

/-- Table 5.9, `owl:differentFrom`: the right-to-left half. -/
def CondDifferentFromIf : Prop :=
  ∀ a1 a2 : i.idom, a1 ≠ a2 → i.iext (i.iIri owlDifferentFrom) a1 a2

/-- Table 5.4, `owl:complementOf`, the full iff. -/
def CondComplementOf : Prop :=
  ∀ z c : i.idom, i.iext (i.iIri owlComplementOf) z c ↔
    (IC i z ∧ IC i c ∧ ∀ x, icext i x z ↔ ¬ icext i x c)

/-- Table 5.5, `owl:oneOf`: "if s sequence of a1, …, an ∈ IR then
(z, s) ∈ IEXT(I(owl:oneOf)) iff z ∈ IC, ICEXT(z) = {a1, …, an}".
`SeqIs` is the §5 sequence condition (`OWL/Semantics.lean`). -/
def CondOneOf : Prop :=
  ∀ (z s : i.idom) (as : List i.idom), SeqIs i s as →
    (i.iext (i.iIri owlOneOf) z s ↔ (IC i z ∧ ∀ x, icext i x z ↔ x ∈ as))

/-- Table 5.4, `owl:unionOf`: "if s sequence of c1, …, cn ∈ IR then
(z, s) ∈ IEXT(I(owl:unionOf)) iff z, c1, …, cn ∈ IC, ICEXT(z) = ICEXT(c1)
∪ … ∪ ICEXT(cn)" — the left-to-right half. -/
def CondUnionOfOnly : Prop :=
  ∀ (z s : i.idom) (cs : List i.idom), SeqIs i s cs → i.iext (i.iIri owlUnionOf) z s →
    IC i z ∧ ∀ x, icext i x z ↔ ∃ c ∈ cs, icext i x c

/-- Table 5.4, `owl:intersectionOf`, the left-to-right half:
`ICEXT(z) = ICEXT(c1) ∩ … ∩ ICEXT(cn)`. -/
def CondIntersectionOfOnly : Prop :=
  ∀ (z s : i.idom) (cs : List i.idom), SeqIs i s cs →
    i.iext (i.iIri owlIntersectionOf) z s →
    IC i z ∧ ∀ x, icext i x z ↔ ∀ c ∈ cs, icext i x c

/-- Table 5.10, `owl:AllDifferent` with `owl:members` and with
`owl:distinctMembers`: the two left-to-right conditions. -/
def CondAllDifferent : Prop :=
  ∀ (mp : WfIri), (mp = owlMembers ∨ mp = owlDistinctMembers) →
    ∀ (z s : i.idom) (as : List i.idom), SeqIs i s as →
      icext i z (i.iIri owlAllDifferent) → i.iext (i.iIri mp) z s →
      ∀ (j k : Nat) (aj ak : i.idom), j ≠ k → as[j]? = some aj → as[k]? = some ak →
        aj ≠ ak

/-- Table 5.13, `owl:FunctionalProperty`: the right-to-left half. -/
def CondFunctionalIf : Prop :=
  ∀ p : i.idom, IP i p → (∀ x y1 y2, i.iext p x y1 → i.iext p x y2 → y1 = y2) →
    icext i p (i.iIri owlFunctionalProperty)

/-- Table 5.13, `owl:InverseFunctionalProperty`: the right-to-left half. -/
def CondInverseFunctionalIf : Prop :=
  ∀ p : i.idom, IP i p → (∀ x1 x2 y, i.iext p x1 y → i.iext p x2 y → x1 = x2) →
    icext i p (i.iIri owlInverseFunctionalProperty)

/-- Table 5.6, `owl:allValuesFrom`: "if (x, c) ∈ IEXT(I(owl:allValuesFrom)),
(x, p) ∈ IEXT(I(owl:onProperty)) then ICEXT(x) = {y | ∀ z : (y, z) ∈
IEXT(p) implies z ∈ ICEXT(c)}" — the ⊆ half. -/
def CondAllValuesFromSub : Prop :=
  ∀ x c p y z : i.idom, i.iext (i.iIri owlAllValuesFrom) x c →
    i.iext (i.iIri owlOnProperty) x p → icext i y x → i.iext p y z → icext i z c

/-- Table 5.6, `owl:someValuesFrom`: "… then ICEXT(x) = {y | ∃ z : (y,
z) ∈ IEXT(p) and z ∈ ICEXT(c)}" — the ⊇ half. -/
def CondSomeValuesFromSup : Prop :=
  ∀ x c p y z : i.idom, i.iext (i.iIri owlSomeValuesFrom) x c →
    i.iext (i.iIri owlOnProperty) x p → i.iext p y z → icext i z c → icext i y x

/-- Table 5.6, `owl:hasValue`: "if (x, a) ∈ IEXT(I(owl:hasValue)),
(x, p) ∈ IEXT(I(owl:onProperty)) then ICEXT(x) = {y | (y, a) ∈
IEXT(p)}" — the ⊆ half. -/
def CondHasValueSub : Prop :=
  ∀ x a p y : i.idom, i.iext (i.iIri owlHasValue) x a → i.iext (i.iIri owlOnProperty) x p →
    icext i y x → i.iext p y a

/-- Table 5.13, `owl:FunctionalProperty`: the left-to-right half. -/
def CondFunctionalOnly : Prop :=
  ∀ p x y1 y2 : i.idom, icext i p (i.iIri owlFunctionalProperty) →
    i.iext p x y1 → i.iext p x y2 → y1 = y2

/-- Table 5.9, `owl:equivalentProperty`: the right-to-left half. -/
def CondEquivalentPropertyIf : Prop :=
  ∀ p1 p2 : i.idom, IP i p1 → IP i p2 → (∀ x y, i.iext p1 x y ↔ i.iext p2 x y) →
    i.iext (i.iIri owlEquivalentProperty) p1 p2

/-- Datatype value spaces that are disjoint have disjoint class
extensions. RDF 1.1 Semantics §9 (D-interpretations: `ICEXT(I(u))` is
the value space of the datatype `I(u)` for every recognised `u`), §4.1
of the RDF-Based Semantics (the datatype map), and XSD 1.1 Part 2 §3.3
(the value spaces of the primitive datatypes `xsd:string`,
`xsd:boolean` and `xsd:decimal` are disjoint). Which pairs are disjoint
is `RL.xsdValueSpacesDisjoint`, which answers `true` only across those
three families. -/
def CondDisjointDatatypes : Prop :=
  ∀ d1 d2 : WfIri, xsdValueSpacesDisjoint d1 d2 = true →
    ∀ y : i.idom, ¬ (icext i y (i.iIri d1) ∧ icext i y (i.iIri d2))

end Conditions

/-- The bundle. Every OWL 2 RDF-Based interpretation (Definition 4.2)
meets every field. -/
structure RdfBasedConditions (i : Interp) : Prop where
  vocabClasses : CondVocabClasses i
  extSub : CondExtSub i
  universal : CondUniversal i
  nothing : CondNothing i
  vocabProps : CondVocabProps i
  subClassOf : CondSubClassOf i
  subPropertyOfIf : CondSubPropertyOfIf i
  domain : CondDomain i
  range : CondRange i
  equivalentClassIf : CondEquivalentClassIf i
  differentFromIf : CondDifferentFromIf i
  complementOf : CondComplementOf i
  oneOf : CondOneOf i
  unionOfOnly : CondUnionOfOnly i
  intersectionOfOnly : CondIntersectionOfOnly i
  allDifferent : CondAllDifferent i
  functionalIf : CondFunctionalIf i
  inverseFunctionalIf : CondInverseFunctionalIf i
  allValuesFromSub : CondAllValuesFromSub i
  someValuesFromSup : CondSomeValuesFromSup i
  disjointDatatypes : CondDisjointDatatypes i
  hasValueSub : CondHasValueSub i
  functionalOnly : CondFunctionalOnly i
  equivalentPropertyIf : CondEquivalentPropertyIf i

/-- Entailment over the bundle (Definition 4.5, with the bundle in place
of "OWL 2 RDF-Based interpretation"; see the header for why this
implies OWL 2 RDF-Based entailment). -/
def RbEntails (g1 g2 : Graph) : Prop := EntailsUnder RdfBasedConditions g1 g2

/-! ## Witness: the bundle is satisfiable and does not entail everything

Domain: `Sum (Option WfIri) Nat`. An IRI denotes itself (`inl (some w)`);
literals and triple terms denote `inl none`; `inr f` is a member of
the class extension of every datatype of value-space family `f`
(`RL.xsdFamily`). Every element is in the extension of every class
except `owl:Nothing` (empty), the datatypes (one element per family) and
`owl:FunctionalProperty` (exactly `rdf:first` and `rdf:rest`, the two
functional properties of the witness, `w_nonfunctional`). Each vocabulary property the bundle constrains gets the
extension the bundle demands; `rdf:first` is empty, so the only
sequence is `rdf:nil`. -/

abbrev WDom := Sum (Option WfIri) Nat

def wI (w : WfIri) : WDom := .inl (some w)

/-- The class extension of the witness. -/
def wExt (x c : WDom) : Prop :=
  c ≠ wI owlNothing ∧
    (if c = wI owlFunctionalProperty then x = wI rdfFirst ∨ x = wI rdfRest
     else
       match c with
       | .inl (some w) => (match xsdFamily w with
                           | some f => x = .inr f
                           | none => True)
       | _ => True)

/-- The extension of every property other than `rdfs:domain` and
`rdfs:range`. -/
def wBase (p x y : WDom) : Prop :=
  if p = wI rdfType then wExt x y
  else if p = wI rdfsSubClassOf then ∀ z, wExt z x → wExt z y
  else if p = wI owlComplementOf then ∀ z, wExt z x ↔ ¬ wExt z y
  else if p = wI owlDifferentFrom then x ≠ y
  else if p = wI owlOneOf then (y = wI rdfNil → ∀ z, ¬ wExt z x)
  else if p = wI owlUnionOf then (y = wI rdfNil → ∀ z, ¬ wExt z x)
  else if p = wI owlIntersectionOf then (y = wI rdfNil → ∀ z, wExt z x)
  else if p = wI rdfFirst then False
  else if p = wI rdfRest then y = wI rdfNil
  else if p = wI owlAllValuesFrom then (∀ z, ¬ wExt z x) ∨ (∀ z, wExt z y)
  else if p = wI owlSomeValuesFrom then (∀ z, wExt z x) ∨ (∀ z, ¬ wExt z y)
  else if p = wI owlHasValue then ∀ z, ¬ wExt z x
  else True

abbrev wIsDomRng (p : WDom) : Prop := p = wI rdfsDomain ∨ p = wI rdfsRange

/-- The full extension. `rdfs:domain` and `rdfs:range` are defined from
`wBase`; on themselves, from the fact that their domain and range are
the whole universe. -/
def wIext (p x y : WDom) : Prop :=
  if p = wI rdfsDomain then
    (if wIsDomRng x then ∀ z, wExt z y else ∀ u v, wBase x u v → wExt u y)
  else if p = wI rdfsRange then
    (if wIsDomRng x then ∀ z, wExt z y else ∀ u v, wBase x u v → wExt v y)
  else wBase p x y

abbrev witnessInterp : Interp :=
  { idom := WDom, idomWit := .inl none, iIri := wI, iLit := fun _ => .inl none,
    iTt := fun _ _ _ => .inl none, iext := wIext }

/-! ### Basic facts about the witness -/

theorem wI_ne {a b : WfIri} (h : a ≠ b) : wI a ≠ wI b := by
  intro h'; apply h; simp only [wI, Sum.inl.injEq, Option.some.injEq] at h'; exact h'

theorem w_icext (x c : WDom) : icext witnessInterp x c = wExt x c := by
  show wIext (wI L4Factoidal.RDFS.rdfType) x c = wExt x c
  have h1 : wI L4Factoidal.RDFS.rdfType ≠ wI rdfsDomain := wI_ne (by decide)
  have h2 : wI L4Factoidal.RDFS.rdfType ≠ wI rdfsRange := wI_ne (by decide)
  simp only [wIext, h1, h2, if_false, wBase]
  simp

/-- `wExt x c` holds for every `x` when `c` is a non-datatype class other
than `owl:Nothing`. -/
theorem wExt_plain {w : WfIri} (hn : w ≠ owlNothing) (hfn : w ≠ owlFunctionalProperty)
    (hf : xsdFamily w = none) (x : WDom) : wExt x (wI w) := by
  refine ⟨wI_ne hn, ?_⟩
  rw [if_neg (wI_ne hfn)]
  simp only [wI, hf]

theorem wIext_base {p : WDom} (h1 : p ≠ wI rdfsDomain) (h2 : p ≠ wI rdfsRange) (x y : WDom) :
    wIext p x y = wBase p x y := by
  simp only [wIext, h1, h2, if_false]

theorem wI_inj {a b : WfIri} : wI a = wI b ↔ a = b := by
  constructor
  · intro h; simp only [wI, Sum.inl.injEq, Option.some.injEq] at h; exact h
  · intro h; rw [h]

/-- `icext` of the witness, as an `Iff` over its own domain. -/
theorem w_ic (x c : witnessInterp.idom) : icext witnessInterp x c ↔ wExt x c := by
  rw [w_icext]

/-- A vocabulary IRI the witness treats as a plain class: not
`owl:Nothing`, no datatype family. -/
def wPlain (w : WfIri) : Bool :=
  w != owlNothing && w != owlFunctionalProperty && (xsdFamily w).isNone

theorem wExt_of_plain {w : WfIri} (h : wPlain w = true) (x : WDom) : wExt x (wI w) := by
  simp only [wPlain, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at h
  exact wExt_plain h.1.1 h.1.2 h.2 x

theorem w_ic_plain {w : WfIri} (h : wPlain w = true) (x : witnessInterp.idom) :
    icext witnessInterp x (witnessInterp.iIri w) :=
  (w_ic _ _).mpr (wExt_of_plain h x)

/-- `wIext` at a vocabulary property other than `rdfs:domain` and
`rdfs:range` is `wBase`. -/
theorem w_iext {p : WfIri} (h1 : p ≠ rdfsDomain) (h2 : p ≠ rdfsRange)
    (x y : witnessInterp.idom) :
    witnessInterp.iext (witnessInterp.iIri p) x y ↔ wBase (wI p) x y := by
  show wIext (wI p) x y ↔ _
  rw [wIext_base (fun h => h1 (wI_inj.mp h)) (fun h => h2 (wI_inj.mp h))]

theorem wBase_default {p : WfIri}
    (h : (p != rdfType && p != rdfsSubClassOf && p != owlComplementOf && p != owlDifferentFrom &&
          p != owlOneOf && p != owlUnionOf && p != owlIntersectionOf && p != rdfFirst &&
          p != rdfRest && p != owlAllValuesFrom && p != owlSomeValuesFrom &&
          p != owlHasValue) = true)
    (x y : WDom) : wBase (wI p) x y := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  simp only [wBase, wI_inj, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, if_false]

theorem wBase_sub (x y : WDom) :
    wBase (wI rdfsSubClassOf) x y ↔ ∀ z, wExt z x → wExt z y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_comp (x y : WDom) :
    wBase (wI owlComplementOf) x y ↔ ∀ z, wExt z x ↔ ¬ wExt z y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_diff (x y : WDom) : wBase (wI owlDifferentFrom) x y ↔ x ≠ y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_oneOf (x y : WDom) :
    wBase (wI owlOneOf) x y ↔ (y = wI rdfNil → ∀ z, ¬ wExt z x) := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_union (x y : WDom) :
    wBase (wI owlUnionOf) x y ↔ (y = wI rdfNil → ∀ z, ¬ wExt z x) := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_inter (x y : WDom) :
    wBase (wI owlIntersectionOf) x y ↔ (y = wI rdfNil → ∀ z, wExt z x) := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_first (x y : WDom) : ¬ wBase (wI rdfFirst) x y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false, not_false_eq_true]

theorem wBase_avf (x y : WDom) :
    wBase (wI owlAllValuesFrom) x y ↔ (∀ z, ¬ wExt z x) ∨ (∀ z, wExt z y) := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_svf (x y : WDom) :
    wBase (wI owlSomeValuesFrom) x y ↔ (∀ z, wExt z x) ∨ (∀ z, ¬ wExt z y) := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_hv (x y : WDom) : wBase (wI owlHasValue) x y ↔ ∀ z, ¬ wExt z x := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_type (x y : WDom) : wBase (wI rdfType) x y ↔ wExt x y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_rest (x y : WDom) : wBase (wI rdfRest) x y ↔ y = wI rdfNil := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

/-- The IRIs `wBase` gives an extension of its own. -/
def wSpecial : List WfIri :=
  [ rdfType, rdfsSubClassOf, owlComplementOf, owlDifferentFrom, owlOneOf, owlUnionOf,
    owlIntersectionOf, rdfFirst, rdfRest, owlAllValuesFrom, owlSomeValuesFrom, owlHasValue ]

theorem wBase_other {p : WDom} (h : ∀ w ∈ wSpecial, p ≠ wI w) (x y : WDom) : wBase p x y := by
  unfold wBase
  rw [if_neg (h rdfType (by decide)), if_neg (h rdfsSubClassOf (by decide)),
    if_neg (h owlComplementOf (by decide)), if_neg (h owlDifferentFrom (by decide)),
    if_neg (h owlOneOf (by decide)), if_neg (h owlUnionOf (by decide)),
    if_neg (h owlIntersectionOf (by decide)), if_neg (h rdfFirst (by decide)),
    if_neg (h rdfRest (by decide)), if_neg (h owlAllValuesFrom (by decide)),
    if_neg (h owlSomeValuesFrom (by decide)), if_neg (h owlHasValue (by decide))]
  trivial

/-- `owl:Nothing` is related to every full-extension element other than
`rdf:nil` by every property except `rdf:first`, `rdf:rest` and
`owl:someValuesFrom`. -/
theorem w_rel_nothing (p : WDom) (h1 : p ≠ wI rdfFirst) (h2 : p ≠ wI rdfRest)
    (h3 : p ≠ wI owlSomeValuesFrom) (y : WDom) (hy : ∀ u, wExt u y) (hyn : y ≠ wI rdfNil) :
    wIext p (wI owlNothing) y := by
  have hN : ∀ u, ¬ wExt u (wI owlNothing) := fun u h => h.1 rfl
  have hNdr : ¬ wIsDomRng (wI owlNothing) := by
    rintro (h | h) <;> exact absurd (wI_inj.mp h) (by decide)
  by_cases hd : p = wI rdfsDomain
  · subst hd
    simp only [wIext, if_true, hNdr, if_false]
    exact fun u _ _ => hy u
  by_cases hr : p = wI rdfsRange
  · subst hr
    have hrd : wI rdfsRange ≠ wI rdfsDomain := wI_ne (by decide)
    simp only [wIext, hrd, if_true, if_false, hNdr]
    exact fun _ v _ => hy v
  rw [wIext_base hd hr]
  by_cases e1 : p = wI rdfType
  · subst e1; exact (wBase_type _ _).mpr (hy _)
  by_cases e2 : p = wI rdfsSubClassOf
  · subst e2; exact (wBase_sub _ _).mpr (fun z hz => absurd hz (hN z))
  by_cases e3 : p = wI owlComplementOf
  · subst e3
    exact (wBase_comp _ _).mpr (fun z => ⟨fun h => absurd h (hN z), fun h => absurd (hy z) h⟩)
  by_cases e4 : p = wI owlDifferentFrom
  · subst e4; exact (wBase_diff _ _).mpr (fun h => (hy (wI owlNothing)).1 h.symm)
  by_cases e5 : p = wI owlOneOf
  · subst e5; exact (wBase_oneOf _ _).mpr (fun h => absurd h hyn)
  by_cases e6 : p = wI owlUnionOf
  · subst e6; exact (wBase_union _ _).mpr (fun h => absurd h hyn)
  by_cases e7 : p = wI owlIntersectionOf
  · subst e7; exact (wBase_inter _ _).mpr (fun h => absurd h hyn)
  by_cases e8 : p = wI owlAllValuesFrom
  · subst e8; exact (wBase_avf _ _).mpr (Or.inl hN)
  by_cases e9 : p = wI owlHasValue
  · subst e9; exact (wBase_hv _ _).mpr hN
  refine wBase_other ?_ _ _
  intro w hw
  simp only [wSpecial, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- Every property of the witness other than `rdf:first` and `rdf:rest`
relates one element to two different ones. -/
theorem w_nonfunctional (p : WDom) (h1 : p ≠ wI rdfFirst) (h2 : p ≠ wI rdfRest) :
    ∃ x y1 y2 : WDom, wIext p x y1 ∧ wIext p x y2 ∧ y1 ≠ y2 := by
  have hT : ∀ u, wExt u (wI owlThing) := wExt_of_plain (by decide)
  have hR : ∀ u, wExt u (wI rdfsResource) := wExt_of_plain (by decide)
  have hTR : wI owlThing ≠ wI rdfsResource := wI_ne (by decide)
  by_cases hs : p = wI owlSomeValuesFrom
  · subst hs
    have hb : ∀ y, wIext (wI owlSomeValuesFrom) (wI owlThing) y := fun y => by
      rw [wIext_base (wI_ne (by decide)) (wI_ne (by decide))]
      exact (wBase_svf _ _).mpr (Or.inl hT)
    exact ⟨_, _, _, hb (wI owlThing), hb (wI rdfsResource), hTR⟩
  · exact ⟨wI owlNothing, wI owlThing, wI rdfsResource,
      w_rel_nothing p h1 h2 hs _ hT (wI_ne (by decide)),
      w_rel_nothing p h1 h2 hs _ hR (wI_ne (by decide)), hTR⟩

theorem w_IC (x : witnessInterp.idom) : IC witnessInterp x := w_ic_plain (by decide) x

theorem w_IP (x : witnessInterp.idom) : IP witnessInterp x := w_ic_plain (by decide) x

theorem w_seq_nil {s : witnessInterp.idom} {as : List witnessInterp.idom}
    (h : SeqIs witnessInterp s as) : as = [] ∧ s = wI rdfNil := by
  cases as with
  | nil => exact ⟨rfl, h⟩
  | cons a rest =>
      obtain ⟨_, hf, _, _⟩ := h
      exact absurd ((w_iext (by decide) (by decide) _ _).mp hf) (wBase_first _ _)

theorem witness_conditions : RdfBasedConditions witnessInterp where
  vocabClasses := by
    intro e _
    exact w_ic_plain (by decide) _
  extSub := by
    intro e he x _
    have hp : ∀ e ∈ extSubTable, wPlain e.2 = true := by decide
    exact w_ic_plain (hp e he) x
  universal := by
    intro c hc x
    have hp : ∀ c ∈ universalClasses, wPlain c = true := by decide
    exact w_ic_plain (hp c hc) x
  nothing := by
    intro x h
    exact ((w_ic _ _).mp h).1 rfl
  vocabProps := by
    intro r hr
    have hp : ∀ r ∈ vocabPropTable,
        wPlain r.part = true ∧ wPlain r.dom = true ∧ wPlain r.rng = true := by decide
    obtain ⟨hpa, hdo, hrn⟩ := hp r hr
    exact ⟨w_ic_plain hpa _, fun x y _ => ⟨w_ic_plain hdo x, w_ic_plain hrn y⟩⟩
  subClassOf := by
    intro c1 c2
    rw [w_iext (by decide) (by decide), wBase_sub]
    constructor
    · intro h
      exact ⟨w_IC c1, w_IC c2, fun x hx => (w_ic _ _).mpr (h x ((w_ic _ _).mp hx))⟩
    · intro h z hz
      exact (w_ic _ _).mp (h.2.2 z ((w_ic _ _).mpr hz))
  subPropertyOfIf := by
    intro p1 p2 _ _ _
    exact (w_iext (by decide) (by decide) _ _).mpr (wBase_default (by decide) _ _)
  domain := by
    intro p c
    show wIext (wI rdfsDomain) p c ↔ _
    simp only [wIext, if_true]
    by_cases hd : wIsDomRng p
    · simp only [hd, if_true]
      constructor
      · intro h; exact ⟨w_IP p, w_IC c, fun x _ _ => (w_ic _ _).mpr (h x)⟩
      · intro h z
        have hz : wIext p z (wI owlThing) := by
          have hth : ∀ u : WDom, wExt u (wI owlThing) := wExt_of_plain (by decide)
          rcases hd with hp | hp <;> subst hp
          · show wIext (wI rdfsDomain) z (wI owlThing)
            simp only [wIext, if_true]
            split
            · exact hth
            · exact fun u _ _ => hth u
          · have hrd : wI rdfsRange ≠ wI rdfsDomain := fun h => absurd (wI_inj.mp h) (by decide)
            show wIext (wI rdfsRange) z (wI owlThing)
            simp only [wIext, hrd, if_true, if_false]
            split
            · exact hth
            · exact fun _ v _ => hth v
        exact (w_ic _ _).mp (h.2.2 z (wI owlThing) hz)
    · simp only [hd, if_false]
      have hp1 : p ≠ wI rdfsDomain := fun h => hd (Or.inl h)
      have hp2 : p ≠ wI rdfsRange := fun h => hd (Or.inr h)
      constructor
      · intro h
        refine ⟨w_IP p, w_IC c, fun x y hxy => (w_ic _ _).mpr (h x y ?_)⟩
        have := hxy; show wBase p x y; rw [← wIext_base hp1 hp2]; exact this
      · intro h u v huv
        refine (w_ic _ _).mp (h.2.2 u v ?_)
        show wIext p u v; rw [wIext_base hp1 hp2]; exact huv
  range := by
    intro p c
    have hrd : wI rdfsRange ≠ wI rdfsDomain := fun h => absurd (wI_inj.mp h) (by decide)
    show wIext (wI rdfsRange) p c ↔ _
    simp only [wIext, hrd, if_false, if_true]
    by_cases hd : wIsDomRng p
    · simp only [hd, if_true]
      constructor
      · intro h; exact ⟨w_IP p, w_IC c, fun _ y _ => (w_ic _ _).mpr (h y)⟩
      · intro h z
        have hf : ¬ wIsDomRng (wI rdfFirst) := by
          rintro (h | h) <;> exact absurd (wI_inj.mp h) (by decide)
        have hz : wIext p (wI rdfFirst) z := by
          rcases hd with hp | hp <;> subst hp
          · show wIext (wI rdfsDomain) (wI rdfFirst) z
            simp only [wIext, hf, if_true, if_false]
            intro u v hb; exact absurd hb (wBase_first u v)
          · show wIext (wI rdfsRange) (wI rdfFirst) z
            simp only [wIext, hrd, hf, if_true, if_false]
            intro u v hb; exact absurd hb (wBase_first u v)
        exact (w_ic _ _).mp (h.2.2 (wI rdfFirst) z hz)
    · simp only [hd, if_false]
      have hp1 : p ≠ wI rdfsDomain := fun h => hd (Or.inl h)
      have hp2 : p ≠ wI rdfsRange := fun h => hd (Or.inr h)
      constructor
      · intro h
        refine ⟨w_IP p, w_IC c, fun x y hxy => (w_ic _ _).mpr (h x y ?_)⟩
        have := hxy; show wBase p x y; rw [← wIext_base hp1 hp2]; exact this
      · intro h u v huv
        refine (w_ic _ _).mp (h.2.2 u v ?_)
        show wIext p u v; rw [wIext_base hp1 hp2]; exact huv
  equivalentClassIf := by
    intro c1 c2 _ _ _
    exact (w_iext (by decide) (by decide) _ _).mpr (wBase_default (by decide) _ _)
  differentFromIf := by
    intro a1 a2 hne
    exact (w_iext (by decide) (by decide) _ _).mpr ((wBase_diff _ _).mpr hne)
  complementOf := by
    intro z c
    rw [w_iext (by decide) (by decide), wBase_comp]
    constructor
    · intro h
      refine ⟨w_IC z, w_IC c, fun x => ?_⟩
      rw [w_ic, w_ic]; exact h x
    · intro h w
      have := h.2.2 w
      rw [w_ic, w_ic] at this; exact this
  oneOf := by
    intro z s as hs
    obtain ⟨rfl, rfl⟩ := w_seq_nil hs
    rw [w_iext (by decide) (by decide), wBase_oneOf]
    constructor
    · intro h
      refine ⟨w_IC z, fun x => ?_⟩
      rw [w_ic]
      exact ⟨fun hx => absurd hx (h rfl x), fun hx => absurd hx (List.not_mem_nil)⟩
    · intro h _ w hw
      exact List.not_mem_nil ((h.2 w).mp ((w_ic _ _).mpr hw))
  unionOfOnly := by
    intro z s cs hs hu
    obtain ⟨rfl, rfl⟩ := w_seq_nil hs
    have h := (wBase_union _ _).mp ((w_iext (by decide) (by decide) _ _).mp hu) rfl
    refine ⟨w_IC z, fun x => ⟨fun hx => absurd ((w_ic _ _).mp hx) (h x), ?_⟩⟩
    rintro ⟨c, hc, _⟩; exact absurd hc List.not_mem_nil
  intersectionOfOnly := by
    intro z s cs hs hi
    obtain ⟨rfl, rfl⟩ := w_seq_nil hs
    have h := (wBase_inter _ _).mp ((w_iext (by decide) (by decide) _ _).mp hi) rfl
    exact ⟨w_IC z, fun x => ⟨fun _ c hc => absurd hc List.not_mem_nil,
      fun _ => (w_ic _ _).mpr (h x)⟩⟩
  allDifferent := by
    intro mp _ z s as hs _ _ j k aj ak _ hj _
    obtain ⟨rfl, _⟩ := w_seq_nil hs
    simp at hj
  functionalIf := by
    intro p _ hfun
    have hpw : p = wI rdfFirst ∨ p = wI rdfRest := by
      rcases Classical.em (p = wI rdfFirst ∨ p = wI rdfRest) with h | h
      · exact h
      · obtain ⟨n1, n2⟩ := not_or.mp h
        obtain ⟨x, y1, y2, e1, e2, hne⟩ := w_nonfunctional p n1 n2
        exact absurd (hfun x y1 y2 e1 e2) hne
    refine (w_ic _ _).mpr ⟨wI_ne (by decide), ?_⟩
    show (if wI owlFunctionalProperty = wI owlFunctionalProperty then
        p = wI rdfFirst ∨ p = wI rdfRest else _)
    rw [if_pos rfl]; exact hpw
  inverseFunctionalIf := by
    intro p _ _
    exact w_ic_plain (by decide) _
  allValuesFromSub := by
    intro x c p y z hav _ hy _
    rw [w_iext (by decide) (by decide), wBase_avf] at hav
    rcases hav with h | h
    · exact absurd ((w_ic _ _).mp hy) (h y)
    · exact (w_ic _ _).mpr (h z)
  someValuesFromSup := by
    intro x c p y z hsv _ _ hz
    rw [w_iext (by decide) (by decide), wBase_svf] at hsv
    rcases hsv with h | h
    · exact (w_ic _ _).mpr (h y)
    · exact absurd ((w_ic _ _).mp hz) (h z)
  disjointDatatypes := by
    intro d1 d2 hd y hy
    obtain ⟨h1, h2⟩ := hy
    have e1 := (w_ic _ _).mp h1
    have e2 := (w_ic _ _).mp h2
    unfold xsdValueSpacesDisjoint at hd
    unfold wExt at e1 e2
    cases hf1 : xsdFamily d1 with
    | none => rw [hf1] at hd; simp at hd
    | some f1 =>
      cases hf2 : xsdFamily d2 with
      | none => rw [hf1, hf2] at hd; simp at hd
      | some f2 =>
        rw [hf1, hf2] at hd
        have hF : xsdFamily owlFunctionalProperty = none := by decide
        have n1 : wI d1 ≠ wI owlFunctionalProperty := fun h => by
          rw [wI_inj.mp h, hF] at hf1; cases hf1
        have n2 : wI d2 ≠ wI owlFunctionalProperty := fun h => by
          rw [wI_inj.mp h, hF] at hf2; cases hf2
        have e1' : y = Sum.inr f1 := by
          have := e1.2; rw [if_neg n1] at this; simp only [wI, hf1] at this; exact this
        have e2' : y = Sum.inr f2 := by
          have := e2.2; rw [if_neg n2] at this; simp only [wI, hf2] at this; exact this
        have : f1 = f2 := by
          exact Sum.inr.inj (e1'.symm.trans e2')
        subst this
        simp at hd
  hasValueSub := by
    intro x a p y hv _ hy
    have h := (wBase_hv _ _).mp ((w_iext (by decide) (by decide) _ _).mp hv)
    exact absurd ((w_ic _ _).mp hy) (h y)
  functionalOnly := by
    intro p x y1 y2 hp h1 h2
    have hp' := ((w_ic _ _).mp hp).2
    rw [if_pos rfl] at hp'
    rcases hp' with rfl | rfl
    · exact absurd ((w_iext (by decide) (by decide) _ _).mp h1) (wBase_first _ _)
    · have e1 := (wBase_rest _ _).mp ((w_iext (by decide) (by decide) _ _).mp h1)
      have e2 := (wBase_rest _ _).mp ((w_iext (by decide) (by decide) _ _).mp h2)
      rw [e1, e2]
  equivalentPropertyIf := by
    intro p1 p2 _ _ _
    exact (w_iext (by decide) (by decide) _ _).mpr (wBase_default (by decide) _ _)

/-- The one-triple graph `owl:Thing rdfs:subClassOf owl:Nothing`. -/
def thingSubNothing : Triple := ⟨.iri owlThing, rdfsSubClassOf, .iri owlNothing⟩

theorem witness_rejects : ¬ Satisfies witnessInterp [thingSubNothing] := by
  rintro ⟨a, ha⟩
  have h := ha thingSubNothing (List.mem_singleton.mpr rfl)
  simp only [TripleHolds, thingSubNothing, denotSubject, denotTerm] at h
  have h' := (wBase_sub _ _).mp ((w_iext (by decide) (by decide) _ _).mp h)
  exact (h' (.inl none) (wExt_of_plain (by decide) _)).1 rfl

/-- `RbEntails` is not the everything-relation. -/
theorem rbEntails_not_everything : ¬ RbEntails [] [thingSubNothing] := by
  intro h
  exact witness_rejects
    (h witnessInterp witness_conditions ⟨fun _ => .inl none, fun _ hm => absurd hm (by simp)⟩)

end L4Factoidal.OWL.RdfBased
