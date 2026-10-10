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
import L4Factoidal.XSD.Facets

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

/-! ## Decimal lexical forms

XSD 1.1 Part 2 § 3.3.3: the lexical space of `xsd:decimal` is
`(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)`; § 3.4.13: that of `xsd:integer`
is `[\-+]?[0-9]+`. `decimalCanon` maps a lexical form in the decimal
lexical space to (negative, integer digits without leading zeros,
fraction digits without trailing zeros), with zero always non-negative;
two lexical forms denote the same decimal value exactly when their
canonical forms are equal. -/

def decimalCanon (s : String) : Option (Bool × List Char × List Char) :=
  let cs := s.toList
  let (neg, body) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let intPart := body.takeWhile (· != '.')
  let rest := body.dropWhile (· != '.')
  let (dot, frac) := match rest with
    | '.' :: f => (true, f)
    | _ => (false, [])
  let digits := fun (l : List Char) => l.all Char.isDigit
  if digits intPart && digits frac && (!intPart.isEmpty || (dot && !frac.isEmpty)) then
    let i' := intPart.dropWhile (· == '0')
    let f' := (frac.reverse.dropWhile (· == '0')).reverse
    some (if i'.isEmpty && f'.isEmpty then false else neg, i', f')
  else none

/-- `s` is in the lexical space of `d` (`xsd:decimal` or `xsd:integer`). -/
def decimalLexOk (d : WfIri) (s : String) : Bool :=
  (decimalCanon s).isSome && (d == xsdDecimal || (d == xsdInteger && !s.toList.contains '.'))

/-- `d` is `xsd:decimal` or `xsd:integer`, both lexical forms are in its
lexical space, and they denote one value. -/
def sameDecimalValue (d : WfIri) (s1 s2 : String) : Bool :=
  (d == xsdDecimal || d == xsdInteger) && decimalLexOk d s1 && decimalLexOk d s2 &&
  decimalCanon s1 == decimalCanon s2

/-! ## Integer values of typed literals

XSD 1.1 Part 2 § 3.4: the integer datatypes of the OWL 2 RDF-Based
datatype map (§ 3.3) and the inclusive bounds of their value spaces;
their lexical space is `[\-+]?[0-9]+` within the bounds (§ 3.4.13 and
the derived types). The value spaces are subsets of the `xsd:decimal`
value space, so equal integers of two of these datatypes are one value
(OWL 2 Structural Specification § 4.2). -/

/-- `(datatype, (lower bound, upper bound))`, `none` for unbounded. -/
def intDtTable : List (WfIri × (Option Int × Option Int)) :=
  [ (xsdInteger, (none, none)),
    (xsdNonNegativeInteger, (some 0, none)),
    (xsdPositiveInteger, (some 1, none)),
    (xsdNonPositiveInteger, (none, some 0)),
    (xsdNegativeInteger, (none, some (-1))),
    (xsdLong, (some (-9223372036854775808), some 9223372036854775807)),
    (xsdIntIri, (some (-2147483648), some 2147483647)),
    (xsdShort, (some (-32768), some 32767)),
    (xsdByte, (some (-128), some 127)),
    (xsdUnsignedLong, (some 0, some 18446744073709551615)),
    (xsdUnsignedInt, (some 0, some 4294967295)),
    (xsdUnsignedShort, (some 0, some 65535)),
    (xsdUnsignedByte, (some 0, some 255)) ]

def intDtBounds (d : WfIri) : Option (Option Int × Option Int) :=
  (intDtTable.find? (fun e => e.1 == d)).map (·.2)

/-- `k` lies within the bounds. -/
def inBounds (k : Int) (b : Option Int × Option Int) : Bool :=
  b.1.all (fun lo => decide (lo ≤ k)) && b.2.all (fun hi => decide (k ≤ hi))

/-- The integer a typed literal denotes, when its datatype is an integer
datatype and its lexical form is in that datatype's lexical space. -/
def intLitValue (l : WfLiteral) : Option Int :=
  match intDtBounds l.val.datatype, XSD.parseFacetInt l.val.lexicalForm with
  | some b, some k => if inBounds k b then some k else none
  | _, _ => none

/-- `xsd:float` or `xsd:double`. -/
def isFloatingDt (d : WfIri) : Bool := d == XSD.xsdFloat || d == xsdDouble

/-- A datatype whose value space is part of the value space of
`owl:real`: `owl:real`, `owl:rational`, `xsd:decimal` and the integer
datatypes. OWL 2 Structural Specification § 4.2: "the value spaces of
xsd:double, xsd:float, and xsd:decimal are pairwise disjoint. In
accordance with this principle, the value space of owl:real is defined
as being disjoint with the value spaces of xsd:double and xsd:float". -/
def onRealLine (e : WfIri) : Bool :=
  e == XSD.owlReal || e == XSD.owlRational || e == xsdDecimal || (intDtBounds e).isSome

/-- The literal is provably not in the value space of the datatype `e`:
an integer outside the bounds of the integer datatype `e`, a literal
of a datatype whose value space is disjoint from that of `e`
(`RL.xsdValueSpacesDisjoint`), or an `xsd:float` / `xsd:double` literal
against a datatype on the `owl:real` line (`onRealLine`). An ill-typed literal denotes no data
value (§ 4.2), so it is not in the value space of `e` either. -/
def litOutsideDt (l : WfLiteral) (e : WfIri) : Bool :=
  (match intLitValue l, intDtBounds e with
   | some k, some b => !inBounds k b
   | _, _ => false) ||
  xsdValueSpacesDisjoint l.val.datatype e ||
  (isFloatingDt l.val.datatype && onRealLine e)

/-- `s` is in the lexical space of `xsd:string` (XSD 1.1 Part 2 § 3.3.1:
the sequences of characters that match the `Char` production of XML 1.0
or XML 1.1; a Lean `Char` is never a surrogate, so the excluded code
points are U+0000, U+FFFE and U+FFFF). -/
def xsdStringLexOk (s : String) : Bool :=
  s.toList.all (fun c => c.toNat != 0 && c.toNat != 0xFFFE && c.toNat != 0xFFFF)

/-- The two literals provably denote different values: two integers that
differ, or two `xsd:string` literals in the lexical space with different
lexical forms (the lexical-to-value mapping of `xsd:string` is the
identity). An ill-typed literal is never read here: its denotation is
not in LV (§ 4.2) and nothing says which element it is. -/
def litDistinct (l m : WfLiteral) : Bool :=
  (match intLitValue l, intLitValue m with
   | some a, some b => a != b
   | _, _ => false) ||
  (l.val.datatype == xsdString && m.val.datatype == xsdString &&
   xsdStringLexOk l.val.lexicalForm && xsdStringLexOk m.val.lexicalForm &&
   l.val.lexicalForm != m.val.lexicalForm)

/-- The two literals provably denote one value: the same literal, or two
integers that are equal. -/
def litSame (l m : WfLiteral) : Bool :=
  l.val == m.val ||
  (match intLitValue l, intLitValue m with
   | some a, some b => a == b
   | _, _ => false)

/-! ## Integer datatype restrictions (Table 5.7)

XSD 1.1 Part 2 § 4.3.7 – § 4.3.10: `xsd:minInclusive v` keeps the values
`≥ v`, `xsd:minExclusive v` those `> v`, `xsd:maxInclusive v` those
`≤ v`, `xsd:maxExclusive v` those `< v`. `intRestrBounds e fv` is the
bounds of `e` tightened by every pair of `fv` whose facet is one of the
four and whose value is an integer literal; any other pair leaves the
bounds as they are, so the bounds CONTAIN the restriction's value
space. -/

def xsdFacetMinInclusive : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#minInclusive", rfl⟩
def xsdFacetMinExclusive : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#minExclusive", rfl⟩
def xsdFacetMaxInclusive : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#maxInclusive", rfl⟩
def xsdFacetMaxExclusive : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#maxExclusive", rfl⟩

def maxLo (a : Option Int) (v : Int) : Option Int :=
  match a with | some x => some (max x v) | none => some v

def minHi (a : Option Int) (v : Int) : Option Int :=
  match a with | some x => some (min x v) | none => some v

/-- One facet pair tightens the bounds. -/
def tightenBounds (b : Option Int × Option Int) (f : WfIri × WfLiteral) :
    Option Int × Option Int :=
  match intLitValue f.2 with
  | some v =>
      if f.1 == xsdFacetMinInclusive then (maxLo b.1 v, b.2)
      else if f.1 == xsdFacetMinExclusive then (maxLo b.1 (v + 1), b.2)
      else if f.1 == xsdFacetMaxInclusive then (b.1, minHi b.2 v)
      else if f.1 == xsdFacetMaxExclusive then (b.1, minHi b.2 (v - 1))
      else b
  | none => b

/-- The bounds of the restriction of `e` by the facet pairs `fv`. -/
def intRestrBounds (e : WfIri) (fv : List (WfIri × WfLiteral)) : Option Int × Option Int :=
  fv.foldl tightenBounds ((intDtBounds e).getD (none, none))

/-- Two bounds pairs with no integer in common. -/
def boundsDisjoint (a b : Option Int × Option Int) : Bool :=
  (match a.1, b.2 with | some lo, some hi => decide (hi < lo) | _, _ => false) ||
  (match b.1, a.2 with | some lo, some hi => decide (hi < lo) | _, _ => false)

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
∪ … ∪ ICEXT(cn)" — the left-to-right half, for n ≥ 1 only. A sequence
may have n = 0 (§ 5, "Sequence expressions"), and what the table's
formula means then is not stated; the condition is not read there. -/
def CondUnionOfOnly : Prop :=
  ∀ (z s : i.idom) (cs : List i.idom), cs ≠ [] → SeqIs i s cs →
    i.iext (i.iIri owlUnionOf) z s →
    IC i z ∧ ∀ x, icext i x z ↔ ∃ c ∈ cs, icext i x c

/-- Table 5.4, `owl:intersectionOf`, the left-to-right half, for n ≥ 1
only (the empty intersection is the same open question as above):
`ICEXT(z) = ICEXT(c1) ∩ … ∩ ICEXT(cn)`. -/
def CondIntersectionOfOnly : Prop :=
  ∀ (z s : i.idom) (cs : List i.idom), cs ≠ [] → SeqIs i s cs →
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

/-- Table 5.9, `owl:sameAs`: the left-to-right half. -/
def CondSameAsOnly : Prop :=
  ∀ a1 a2 : i.idom, i.iext (i.iIri owlSameAs) a1 a2 → a1 = a2

/-- § 4.2: "IL("s"^^u) = L2V(d)(s), provided that d is a datatype of D,
IS(u) = d, and s is in the lexical space LS(d)". For `d` = `xsd:decimal`
or `xsd:integer` (both in every OWL 2 RDF-Based datatype map, § 3.3):
when `IS(u) = IS(d)` and `s1`, `s2` are lexical forms of `d` with one
value, `"s1"^^u` and `"s2"^^d` denote that value. -/
def CondTypedLiteralValue : Prop :=
  ∀ l1 l2 : WfLiteral, l1.val.langTag = none →
    sameDecimalValue l2.val.datatype l1.val.lexicalForm l2.val.lexicalForm = true →
    i.iIri l1.val.datatype = i.iIri l2.val.datatype → i.iLit l1 = i.iLit l2

/-- Table 5.6, `owl:someValuesFrom`: "… then ICEXT(z) = {x | ∃ y : (x, y)
∈ IEXT(p) and y ∈ ICEXT(c)}" — the ⊆ half: a member has a successor in
`c`. -/
def CondSomeValuesFromSub : Prop :=
  ∀ x c p y : i.idom, i.iext (i.iIri owlSomeValuesFrom) x c →
    i.iext (i.iIri owlOnProperty) x p → icext i y x → ∃ z, i.iext p y z ∧ icext i z c

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

/-- D-interpretations (§ 4.2, and the "general semantic conditions for
datatypes" of the RDF Semantics that § 4.2 retains): for a datatype `e`
of the datatype map, ICEXT(I(e)) is the value space of `e`, a subset of
LV; IL("s"^^u) is L2V(u)(s) when s is in the lexical space of `u`, and is
not in LV otherwise. So a literal that `litOutsideDt` places outside the
value space of `e` is not in ICEXT(I(e)). -/
def CondLitOutsideDt : Prop :=
  ∀ (l : WfLiteral) (e : WfIri), litOutsideDt l e = true → ¬ icext i (i.iLit l) (i.iIri e)

/-- Table 5.5 with § 4.2: an enumeration of literals has exactly their
denotations as members ("ICEXT(z) = {a1, …, an}"), and IL maps two
literals with different values to different elements (L2V). So a
literal whose value differs from that of every listed literal is not a
member. -/
def CondOneOfLitExcl : Prop :=
  ∀ (z s : i.idom) (as : List i.idom) (l : WfLiteral), SeqIs i s as →
    i.iext (i.iIri owlOneOf) z s →
    (∀ a ∈ as, ∃ m : WfLiteral, a = i.iLit m ∧ litDistinct l m = true) →
    ¬ icext i (i.iLit l) z

/-- § 4.2: IL("s"^^u) = L2V(u)(s); two literals `litSame` relates denote
one value. -/
def CondLitSame : Prop := ∀ l m : WfLiteral, litSame l m = true → i.iLit l = i.iLit m

/-- Table 5.4, `owl:datatypeComplementOf`: "if (z, d) ∈
IEXT(I(owl:datatypeComplementOf)) then ICEXT(z) = LV \ ICEXT(d)" — the
part of the ⊆ half that says a member of `z` is not a member of `d`. -/
def CondDatatypeComplementSub : Prop :=
  ∀ z d y : i.idom, i.iext (i.iIri owlDatatypeComplementOf) z d → icext i y z → ¬ icext i y d

/-- The premise of Table 5.7 for an integer datatype `e`: `(z, I(e)) ∈
IEXT(I(owl:onDatatype))`, `(z, s) ∈ IEXT(I(owl:withRestrictions))`, `s`
a sequence of `z1, …, zn` with n ≥ 1, each pair `(F, v)` of `fv` an
assertion `(zk, IL(v)) ∈ IEXT(I(F))` of one of the `zk`, and every `zk`
the subject of at least one pair of `fv`. Table 5.7 reads "(z1, v1) ∈
IEXT(f1), …, (zn, vn) ∈ IEXT(fn)" with one pair per `zk`; the last
clause lets every pair of `fv` be part of such a choice. -/
def RestrictionFacets (z : i.idom) (e : WfIri) (fv : List (WfIri × WfLiteral)) : Prop :=
  (intDtBounds e).isSome = true ∧ i.iext (i.iIri owlOnDatatype) z (i.iIri e) ∧
  ∃ (s : i.idom) (zs : List i.idom), zs ≠ [] ∧ i.iext (i.iIri owlWithRestrictions) z s ∧
    SeqIs i s zs ∧ (∀ f ∈ fv, ∃ zk ∈ zs, i.iext (i.iIri f.1) zk (i.iLit f.2)) ∧
    (∀ zk ∈ zs, ∃ f ∈ fv, i.iext (i.iIri f.1) zk (i.iLit f.2))

/-- Table 5.7: "ICEXT(z) = ICEXT(d) ∩ IF2V(d)((f1, v1)) ∩ … ∩
IF2V(d)((fn, vn))", over an integer datatype (the bounds of § 3.4, the
facets of § 4.3.7 – § 4.3.10). Every member is an integer `k` within
`intRestrBounds e fv`, and `k` is IL of every literal whose integer value
is `k` (for example `"k"^^xsd:integer`). -/
def CondIntRestrMembers : Prop :=
  ∀ (z : i.idom) (e : WfIri) (fv : List (WfIri × WfLiteral)), RestrictionFacets i z e fv →
    ∀ y, icext i y z → ∃ (l : WfLiteral) (k : Int), intLitValue l = some k ∧
      inBounds k (intRestrBounds e fv) = true ∧ y = i.iLit l

/-- Table 5.7, the same reading: a literal whose integer value is outside
`intRestrBounds e fv` is not a member. -/
def CondIntRestrExcl : Prop :=
  ∀ (z : i.idom) (e : WfIri) (fv : List (WfIri × WfLiteral)) (l : WfLiteral) (k : Int),
    RestrictionFacets i z e fv → intLitValue l = some k →
    inBounds k (intRestrBounds e fv) = false → ¬ icext i (i.iLit l) z

/-- Table 5.6, `owl:minCardinality`: "if (z, n) ∈
IEXT(I(owl:minCardinality)), (z, p) ∈ IEXT(I(owl:onProperty)) then
ICEXT(z) = {x | #{y | (x, y) ∈ IEXT(p)} ≥ n}" — the ⊇ half for n = 0
and n = 1, with n = IL(l) for an integer literal `l` (§ 4.2): a subject
with a `p`-successor is a member. -/
def CondMinCardLe1Sup : Prop :=
  ∀ (z p x y : i.idom) (l : WfLiteral) (k : Int), intLitValue l = some k → 0 ≤ k → k ≤ 1 →
    i.iext (i.iIri owlMinCardinality) z (i.iLit l) → i.iext (i.iIri owlOnProperty) z p →
    i.iext p x y → icext i x z

/-- Table 5.9, `owl:propertyDisjointWith`: the left-to-right half,
"IEXT(p1) ∩ IEXT(p2) = ∅". -/
def CondPropertyDisjointOnly : Prop :=
  ∀ p1 p2 x y : i.idom, i.iext (i.iIri owlPropertyDisjointWith) p1 p2 →
    i.iext p1 x y → ¬ i.iext p2 x y

/-- Table 5.15, the `owl:targetValue` form: "if (z, a1) ∈
IEXT(I(owl:sourceIndividual)), (z, p) ∈ IEXT(I(owl:assertionProperty)),
(z, v) ∈ IEXT(I(owl:targetValue)) then … (a1, v) ∉ IEXT(p)", for a target
value `v` = IL(m) of a literal `m`. -/
def CondNpaTargetValue : Prop :=
  ∀ (z a1 p : i.idom) (m : WfLiteral), i.iext (i.iIri owlSourceIndividual) z a1 →
    i.iext (i.iIri owlAssertionProperty) z p → i.iext (i.iIri owlTargetValue) z (i.iLit m) →
    ¬ i.iext p a1 (i.iLit m)

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
  sameAsOnly : CondSameAsOnly i
  typedLiteralValue : CondTypedLiteralValue i
  someValuesFromSub : CondSomeValuesFromSub i
  litOutsideDt : CondLitOutsideDt i
  oneOfLitExcl : CondOneOfLitExcl i
  litSame : CondLitSame i
  datatypeComplementSub : CondDatatypeComplementSub i
  intRestrMembers : CondIntRestrMembers i
  intRestrExcl : CondIntRestrExcl i
  minCardLe1Sup : CondMinCardLe1Sup i
  propertyDisjointOnly : CondPropertyDisjointOnly i
  npaTargetValue : CondNpaTargetValue i

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
`owl:FunctionalProperty` (exactly `rdf:first`, `rdf:rest`, `owl:sameAs`
and `owl:someValuesFrom`, the functional properties of the witness,
`w_nonfunctional`). Every literal denotes one element, so
`CondTypedLiteralValue` holds trivially. Each vocabulary property the bundle constrains gets the
extension the bundle demands; `rdf:first` is empty, so the only
sequence is `rdf:nil`. -/

abbrev WDom := Sum (Option WfIri) Nat

/-- The value-space family the witness gives a datatype IRI:
`RL.xsdFamily`, and `owl:real` and `owl:rational` in the numeric family. -/
def wFamily (w : WfIri) : Option Nat :=
  match xsdFamily w with
  | some f => some f
  | none => if w == XSD.owlReal || w == XSD.owlRational then some 2 else none

theorem wFamily_of_xsd {w : WfIri} {f : Nat} (h : xsdFamily w = some f) : wFamily w = some f := by
  simp [wFamily, h]

def wI (w : WfIri) : WDom := .inl (some w)

/-- The class extension of the witness. -/
def wExt (x c : WDom) : Prop :=
  c ≠ wI owlNothing ∧
    (if c = wI owlFunctionalProperty then
       x = wI rdfFirst ∨ x = wI rdfRest ∨ x = wI owlSameAs ∨ x = wI owlSomeValuesFrom
     else
       match c with
       | .inl (some w) => (match wFamily w with
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
  else if p = wI owlSomeValuesFrom then (∀ z, ¬ wExt z x) ∧ (∀ z, ¬ wExt z y)
  else if p = wI owlHasValue then ∀ z, ¬ wExt z x
  else if p = wI owlSameAs then x = y
  else if p = wI owlDatatypeComplementOf then ∀ z, wExt z x → ¬ wExt z y
  else if p = wI owlMinCardinality then y ≠ .inl none
  else if p = wI owlTargetValue then y ≠ .inl none
  else if p = wI owlPropertyDisjointWith then x = wI rdfFirst ∨ y = wI rdfFirst
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
    (hf : wFamily w = none) (x : WDom) : wExt x (wI w) := by
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
  w != owlNothing && w != owlFunctionalProperty && (wFamily w).isNone

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
          p != owlHasValue && p != owlSameAs && p != owlDatatypeComplementOf &&
          p != owlMinCardinality && p != owlTargetValue && p != owlPropertyDisjointWith) = true)
    (x y : WDom) : wBase (wI p) x y := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩ := h
  simp only [wBase, wI_inj, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, if_false]

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
    wBase (wI owlSomeValuesFrom) x y ↔ (∀ z, ¬ wExt z x) ∧ (∀ z, ¬ wExt z y) := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_hv (x y : WDom) : wBase (wI owlHasValue) x y ↔ ∀ z, ¬ wExt z x := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_type (x y : WDom) : wBase (wI rdfType) x y ↔ wExt x y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_rest (x y : WDom) : wBase (wI rdfRest) x y ↔ y = wI rdfNil := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_sameAs (x y : WDom) : wBase (wI owlSameAs) x y ↔ x = y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_dcomp (x y : WDom) :
    wBase (wI owlDatatypeComplementOf) x y ↔ ∀ z, wExt z x → ¬ wExt z y := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_minc (x y : WDom) : wBase (wI owlMinCardinality) x y ↔ y ≠ .inl none := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_tv (x y : WDom) : wBase (wI owlTargetValue) x y ↔ y ≠ .inl none := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

theorem wBase_pdw (x y : WDom) :
    wBase (wI owlPropertyDisjointWith) x y ↔ x = wI rdfFirst ∨ y = wI rdfFirst := by
  simp (config := { decide := true }) only [wBase, if_true, if_false]

/-- The IRIs `wBase` gives an extension of its own. -/
def wSpecial : List WfIri :=
  [ rdfType, rdfsSubClassOf, owlComplementOf, owlDifferentFrom, owlOneOf, owlUnionOf,
    owlIntersectionOf, rdfFirst, rdfRest, owlAllValuesFrom, owlSomeValuesFrom, owlHasValue,
    owlSameAs, owlDatatypeComplementOf, owlMinCardinality, owlTargetValue,
    owlPropertyDisjointWith ]

theorem wBase_other {p : WDom} (h : ∀ w ∈ wSpecial, p ≠ wI w) (x y : WDom) : wBase p x y := by
  unfold wBase
  rw [if_neg (h rdfType (by decide)), if_neg (h rdfsSubClassOf (by decide)),
    if_neg (h owlComplementOf (by decide)), if_neg (h owlDifferentFrom (by decide)),
    if_neg (h owlOneOf (by decide)), if_neg (h owlUnionOf (by decide)),
    if_neg (h owlIntersectionOf (by decide)), if_neg (h rdfFirst (by decide)),
    if_neg (h rdfRest (by decide)), if_neg (h owlAllValuesFrom (by decide)),
    if_neg (h owlSomeValuesFrom (by decide)), if_neg (h owlHasValue (by decide)),
    if_neg (h owlSameAs (by decide)), if_neg (h owlDatatypeComplementOf (by decide)),
    if_neg (h owlMinCardinality (by decide)), if_neg (h owlTargetValue (by decide)),
    if_neg (h owlPropertyDisjointWith (by decide))]
  trivial

/-- `owl:Nothing` is related to every full-extension element other than
`rdf:nil` by every property except `rdf:first`, `rdf:rest`,
`owl:sameAs` and `owl:someValuesFrom`. -/
theorem w_rel_nothing (p : WDom) (h1 : p ≠ wI rdfFirst) (h2 : p ≠ wI rdfRest)
    (h4 : p ≠ wI owlSameAs)
    (h3 : p ≠ wI owlSomeValuesFrom) (h5 : p ≠ wI owlPropertyDisjointWith) (y : WDom)
    (hy : ∀ u, wExt u y) (hyn : y ≠ wI rdfNil) (hy0 : y ≠ .inl none) :
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
  by_cases e10 : p = wI owlDatatypeComplementOf
  · subst e10; exact (wBase_dcomp _ _).mpr (fun z hz => absurd hz (hN z))
  by_cases e11 : p = wI owlMinCardinality
  · subst e11; exact (wBase_minc _ _).mpr hy0
  by_cases e12 : p = wI owlTargetValue
  · subst e12; exact (wBase_tv _ _).mpr hy0
  refine wBase_other ?_ _ _
  intro w hw
  simp only [wSpecial, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> assumption

/-- Every property of the witness other than `rdf:first`, `rdf:rest`,
`owl:sameAs` and `owl:someValuesFrom` relates one element to two
different ones. -/
theorem w_nonfunctional (p : WDom) (h1 : p ≠ wI rdfFirst) (h2 : p ≠ wI rdfRest)
    (h4 : p ≠ wI owlSameAs) (h5 : p ≠ wI owlSomeValuesFrom)
    (h6 : p ≠ wI owlPropertyDisjointWith) :
    ∃ x y1 y2 : WDom, wIext p x y1 ∧ wIext p x y2 ∧ y1 ≠ y2 := by
  have hT : ∀ u, wExt u (wI owlThing) := wExt_of_plain (by decide)
  have hR : ∀ u, wExt u (wI rdfsResource) := wExt_of_plain (by decide)
  have hTR : wI owlThing ≠ wI rdfsResource := wI_ne (by decide)
  have n0 : ∀ w : WfIri, wI w ≠ (.inl none : WDom) := fun w h => by
    simp only [wI, Sum.inl.injEq, reduceCtorEq] at h
  exact ⟨wI owlNothing, wI owlThing, wI rdfsResource,
    w_rel_nothing p h1 h2 h4 h5 h6 _ hT (wI_ne (by decide)) (n0 _),
    w_rel_nothing p h1 h2 h4 h5 h6 _ hR (wI_ne (by decide)) (n0 _), hTR⟩

/-- `owl:propertyDisjointWith` relates `rdf:first` to every element. -/
theorem w_pdw_nonfunctional :
    wIext (wI owlPropertyDisjointWith) (wI rdfFirst) (wI owlThing) ∧
    wIext (wI owlPropertyDisjointWith) (wI rdfFirst) (wI rdfsResource) := by
  have h1 : wI owlPropertyDisjointWith ≠ wI rdfsDomain := wI_ne (by decide)
  have h2 : wI owlPropertyDisjointWith ≠ wI rdfsRange := wI_ne (by decide)
  rw [wIext_base h1 h2, wIext_base h1 h2]
  exact ⟨(wBase_pdw _ _).mpr (Or.inl rfl), (wBase_pdw _ _).mpr (Or.inl rfl)⟩

/-- `owl:Nothing` is the only element of the witness whose class
extension is empty. -/
theorem w_empty_is_nothing (c : WDom) (h : ∀ z, ¬ wExt z c) : c = wI owlNothing := by
  rcases Classical.em (c = wI owlNothing) with hn | hn
  · exact hn
  · exfalso
    by_cases hf : c = wI owlFunctionalProperty
    · subst hf
      exact h (wI rdfFirst) ⟨hn, by rw [if_pos rfl]; exact Or.inl rfl⟩
    · match c, hn, hf, h with
      | .inl (some w), hn, hf, h =>
          cases hfam : wFamily w with
          | none => exact h (.inl none) ⟨hn, by rw [if_neg hf]; simp [hfam]⟩
          | some f => exact h (.inr f) ⟨hn, by rw [if_neg hf]; simp [hfam]⟩
      | .inl none, hn, hf, h => exact h (.inl none) ⟨hn, by rw [if_neg hf]; trivial⟩
      | .inr n, hn, hf, h => exact h (.inl none) ⟨hn, by rw [if_neg hf]; trivial⟩

theorem w_IC (x : witnessInterp.idom) : IC witnessInterp x := w_ic_plain (by decide) x

theorem w_IP (x : witnessInterp.idom) : IP witnessInterp x := w_ic_plain (by decide) x

theorem w_seq_nil {s : witnessInterp.idom} {as : List witnessInterp.idom}
    (h : SeqIs witnessInterp s as) : as = [] ∧ s = wI rdfNil := by
  cases as with
  | nil => exact ⟨rfl, h⟩
  | cons a rest =>
      obtain ⟨_, hf, _, _⟩ := h
      exact absurd ((w_iext (by decide) (by decide) _ _).mp hf) (wBase_first _ _)

theorem intDtTable_family : ∀ e ∈ intDtTable, xsdFamily e.1 = some 2 := by decide

theorem intDtBounds_family {e : WfIri} {b : Option Int × Option Int}
    (h : intDtBounds e = some b) : xsdFamily e = some 2 := by
  simp only [intDtBounds, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, _⟩ := h
  have hmem := List.mem_of_find?_eq_some hp
  have heq : p.1 = e := Subtype.ext (by simpa using List.find?_some hp)
  rw [← heq]
  exact intDtTable_family p hmem

theorem w_litOutside_family {l : WfLiteral} {e : WfIri} (h : litOutsideDt l e = true) :
    ∃ f, wFamily e = some f := by
  simp only [litOutsideDt, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · split at h
    · rename_i b _ hb
      exact ⟨2, wFamily_of_xsd (intDtBounds_family hb)⟩
    · simp at h
  · unfold xsdValueSpacesDisjoint at h
    split at h
    · rename_i f1 f2 _ h2
      exact ⟨f2, wFamily_of_xsd h2⟩
    · simp at h
  · simp only [Bool.and_eq_true, onRealLine, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨_, ((hr | hr) | hd) | hi⟩ := h
    · subst hr; exact ⟨2, by decide⟩
    · subst hr; exact ⟨2, by decide⟩
    · subst hd; exact ⟨2, by decide⟩
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hi
      exact ⟨2, wFamily_of_xsd (intDtBounds_family hb)⟩

/-- A literal of the witness denotes `inl none`, which is in no datatype
extension. -/
theorem w_lit_not_dt {e : WfIri} {f : Nat} (hf : wFamily e = some f) {l : WfLiteral}
    (h : wExt (witnessInterp.iLit l) (wI e)) : False := by
  have hF : wFamily owlFunctionalProperty = none := by decide
  have hn : wI e ≠ wI owlFunctionalProperty := fun h' => by
    rw [wI_inj.mp h', hF] at hf; cases hf
  have h2 := h.2
  rw [if_neg hn] at h2
  simp only [wI, hf] at h2
  cases h2

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
    intro z s cs hne hs _
    exact absurd (w_seq_nil hs).1 hne
  intersectionOfOnly := by
    intro z s cs hne hs _
    exact absurd (w_seq_nil hs).1 hne
  allDifferent := by
    intro mp _ z s as hs _ _ j k aj ak _ hj _
    obtain ⟨rfl, _⟩ := w_seq_nil hs
    simp at hj
  functionalIf := by
    intro p _ hfun
    have hpdw : p ≠ wI owlPropertyDisjointWith := by
      intro hp
      subst hp
      exact absurd (hfun _ _ _ w_pdw_nonfunctional.1 w_pdw_nonfunctional.2) (wI_ne (by decide))
    have hpw : p = wI rdfFirst ∨ p = wI rdfRest ∨ p = wI owlSameAs ∨
        p = wI owlSomeValuesFrom := by
      rcases Classical.em (p = wI rdfFirst ∨ p = wI rdfRest ∨ p = wI owlSameAs ∨
          p = wI owlSomeValuesFrom) with h | h
      · exact h
      · obtain ⟨n1, n234⟩ := not_or.mp h
        obtain ⟨n2, n34⟩ := not_or.mp n234
        obtain ⟨n3, n4⟩ := not_or.mp n34
        obtain ⟨x, y1, y2, e1, e2, hne⟩ := w_nonfunctional p n1 n2 n3 n4 hpdw
        exact absurd (hfun x y1 y2 e1 e2) hne
    refine (w_ic _ _).mpr ⟨wI_ne (by decide), ?_⟩
    show (if wI owlFunctionalProperty = wI owlFunctionalProperty then
        p = wI rdfFirst ∨ p = wI rdfRest ∨ p = wI owlSameAs ∨ p = wI owlSomeValuesFrom else _)
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
    exact absurd ((w_ic _ _).mp hz) (hsv.2 z)
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
          have := e1.2; rw [if_neg n1] at this
          simp only [wI, wFamily_of_xsd hf1] at this; exact this
        have e2' : y = Sum.inr f2 := by
          have := e2.2; rw [if_neg n2] at this
          simp only [wI, wFamily_of_xsd hf2] at this; exact this
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
    rcases hp' with rfl | rfl | rfl | rfl
    · exact absurd ((w_iext (by decide) (by decide) _ _).mp h1) (wBase_first _ _)
    · have e1 := (wBase_rest _ _).mp ((w_iext (by decide) (by decide) _ _).mp h1)
      have e2 := (wBase_rest _ _).mp ((w_iext (by decide) (by decide) _ _).mp h2)
      rw [e1, e2]
    · have e1 := (wBase_sameAs _ _).mp ((w_iext (by decide) (by decide) _ _).mp h1)
      have e2 := (wBase_sameAs _ _).mp ((w_iext (by decide) (by decide) _ _).mp h2)
      rw [← e1, ← e2]
    · have e1 := (wBase_svf _ _).mp ((w_iext (by decide) (by decide) _ _).mp h1)
      have e2 := (wBase_svf _ _).mp ((w_iext (by decide) (by decide) _ _).mp h2)
      rw [w_empty_is_nothing _ e1.2, w_empty_is_nothing _ e2.2]
  equivalentPropertyIf := by
    intro p1 p2 _ _ _
    exact (w_iext (by decide) (by decide) _ _).mpr (wBase_default (by decide) _ _)
  sameAsOnly := by
    intro a1 a2 h
    exact (wBase_sameAs _ _).mp ((w_iext (by decide) (by decide) _ _).mp h)
  typedLiteralValue := by
    intro _ _ _ _ _
    rfl
  someValuesFromSub := by
    intro x c p y hsv _ hy
    rw [w_iext (by decide) (by decide), wBase_svf] at hsv
    exact absurd ((w_ic _ _).mp hy) (hsv.1 y)
  litOutsideDt := by
    intro l e h hm
    have hf : ∃ f, wFamily e = some f := w_litOutside_family h
    obtain ⟨f, hf⟩ := hf
    have hm' := (w_ic _ _).mp hm
    exact w_lit_not_dt hf hm'
  oneOfLitExcl := by
    intro z s as l hs ho _ hm
    obtain ⟨_, rfl⟩ := w_seq_nil hs
    have h := (wBase_oneOf _ _).mp ((w_iext (by decide) (by decide) _ _).mp ho) rfl
    exact h _ ((w_ic _ _).mp hm)
  litSame := by
    intro _ _ _
    rfl
  datatypeComplementSub := by
    intro z d y hzd hy hd
    have h := (wBase_dcomp _ _).mp ((w_iext (by decide) (by decide) _ _).mp hzd)
    exact h y ((w_ic _ _).mp hy) ((w_ic _ _).mp hd)
  intRestrMembers := by
    intro z e fv hr
    obtain ⟨_, _, s, zs, hne, _, hs, _, _⟩ := hr
    exact absurd (w_seq_nil hs).1 hne
  intRestrExcl := by
    intro z e fv l k hr
    obtain ⟨_, _, s, zs, hne, _, hs, _, _⟩ := hr
    exact absurd (w_seq_nil hs).1 hne
  minCardLe1Sup := by
    intro z p x y l k _ _ _ hm
    exact absurd rfl ((wBase_minc _ _).mp ((w_iext (by decide) (by decide) _ _).mp hm))
  propertyDisjointOnly := by
    intro p1 p2 x y hd h1 h2
    rcases (wBase_pdw _ _).mp ((w_iext (by decide) (by decide) _ _).mp hd) with rfl | rfl
    · exact (wBase_first _ _) ((w_iext (by decide) (by decide) _ _).mp h1)
    · exact (wBase_first _ _) ((w_iext (by decide) (by decide) _ _).mp h2)
  npaTargetValue := by
    intro z a1 p m _ _ ht
    exact absurd rfl ((wBase_tv _ _).mp ((w_iext (by decide) (by decide) _ _).mp ht))

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
