/-
L4Factoidal.OWL.NegationGoals — entailment by refutation: negate a
PositiveEntailment conclusion graph into clash-seeking refutation
goals.

Port of `formal/fstar/Tableau.Refute.fst` §11a/11b (`negation_goals`
and its builders), step 2 of
https://github.com/danbri/factoidal/issues/586 .

## The soundness contract

For a premise `P` and a conclusion graph `C`, under OWL 2 Direct
Semantics:

    P ⊨ C   ⟺   P ∪ ¬C is UNSATISFIABLE.

A conclusion graph is the conjunction of its content assertions
`A₁ ⊓ … ⊓ Aₙ`, and `P ⊨ (A₁ ⊓ … ⊓ Aₙ)` iff `P ⊨ Aₖ` for every `k`.
So each conjunct is refuted SEPARATELY: goal `k` augments `P` with
`¬Aₖ` alone — never with the other conjuncts, because assuming an
unproven `Aⱼ` while proving `Aₖ` is the unsound direction. An
equivalence conclusion `C ≡ D` expands to the two subsumption goals
`C ⊑ D` and `D ⊑ C`, both required; likewise `P ≡ Q` for properties.
One unsupported conjunct collapses the whole conclusion to `none`
(conservative — the caller keeps its closure verdict).

`negationGoals` returns the CONJUNCTION of goals: the caller proves
the entailment iff `tableauConsistent (closure ++ goal) fuel` answers
`some false` for EVERY goal; a `some true` on any goal is a
countermodel (not entailed); otherwise the answer is indeterminate.

## The ¬p(x,y) encoding

The sound negation of a property assertion `s p o` (and the witness
half of a property subsumption `P ⊑ Q`) needs "x has no p-successor
equal to y" as a clash target the tableau can consume. It is encoded
as

    x rdf:type ObjectMaxCardinality(0, p, ObjectOneOf(y))

i.e. `x : ≤0 p.{y}`. In every model `{y}` denotes `{den(y)}`, so
`≤0 p.{y}` denotes exactly the individuals with no p-successor equal
to `y` — precisely `¬(⟨x,y⟩ ∈ EXT(p))`, nothing stronger (a bare
`≤0 p` would forbid ALL p-successors, which is unsound). The
tautology `y ∈ {y}` is asserted alongside so the filler filter
recognises `y`. A literal object is out of this encoding
(`owl:oneOf` of a literal is a data range) — such a conclusion falls
to `none`.

## Structural vs content triples

Class-expression scaffolding (restriction/list/declaration triples)
constrains nothing on its own; it is kept verbatim in EVERY goal so a
goal refuting a subsumption still has the defining structure of both
classes available. A named-subject `owl:complementOf` / `owl:unionOf`
/ `owl:intersectionOf` / `owl:oneOf` marker is an ASSERTED CLASS AXIOM,
not scaffolding (F* 2026-07-28 note: `WebOnt-I5.2-004`'s conclusion is
exactly `notA owl:complementOf A`); a bnode-subject marker builds an
anonymous expression and stays structural. Any predicate NOT
classified structural is treated as content — the safe
over-approximation, since a misclassification toward content can only
push the conclusion to `none`, never hide an assertion.
-/
import L4Factoidal.OWL.Refute

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Vocabulary this module needs and `OWL/Vocabulary.lean` /
`OWL/Refute.lean` do not carry -/

def owlDatatypeProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#DatatypeProperty", rfl⟩
def owlAnnotationProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AnnotationProperty", rfl⟩
def owlNamedIndividual : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#NamedIndividual", rfl⟩
def owlOntology : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#Ontology", rfl⟩
def owlDataRange : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#DataRange", rfl⟩
def rdfsClass : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#Class", rfl⟩
def rdfProperty : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Property", rfl⟩
def owlDatatypeComplementOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#datatypeComplementOf", rfl⟩
def owlWithRestrictions : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#withRestrictions", rfl⟩
def owlOnProperties : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onProperties", rfl⟩
def owlOnDataRange : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#onDataRange", rfl⟩

/-! ## Structural / content classification -/

/-- `rdf:type` objects that DECLARE rather than assert: membership in
    one of these is never the fact a PositiveEntailment conclusion is
    testing. `owl:Nothing` is deliberately absent — an
    `i rdf:type owl:Nothing` conclusion is a real, if degenerate,
    claim. Port of `is_meta_type_iri`. -/
def isMetaTypeIri (i : WfIri) : Bool :=
  i == owlClass || i == owlObjectProperty || i == owlDatatypeProperty
  || i == owlAnnotationProperty || i == owlNamedIndividual
  || i == owlRestriction || i == rdfsClass || i == rdfProperty
  || i == rdfsDatatype || i == owlDataRange || i == owlThing
  || i == owlOntology
  || i == owlFunctionalProperty || i == owlInverseFunctionalProperty
  || i == owlTransitiveProperty || i == owlSymmetricProperty
  || i == owlAsymmetricProperty || i == owlIrreflexiveProperty
  || i == owlReflexiveProperty

/-- A predicate that BUILDS a class expression / list / restriction,
    or wires a declaration — never itself the asserted fact of a PE
    conclusion. Port of `is_structural_predicate`. -/
def isStructuralPredicate (p : WfIri) : Bool :=
  p == owlOnProperty || p == owlSomeValuesFrom || p == owlAllValuesFrom
  || p == owlHasValue || p == owlOnClass || p == owlOnDataRange
  || p == owlCardinality || p == owlMinCardinality || p == owlMaxCardinality
  || p == owlQualifiedCardinality || p == owlMinQualifiedCardinality
  || p == owlMaxQualifiedCardinality || p == owlIntersectionOf
  || p == owlUnionOf || p == owlComplementOf || p == owlDatatypeComplementOf
  || p == owlOneOf || p == owlHasSelf || p == owlInverseOf
  || p == owlDistinctMembers || p == owlMembers
  || p == owlWithRestrictions || p == owlOnProperties
  || p == rdfFirst || p == rdfRest

/-- The property characteristics: `rdf:type` objects that ASSERT an
    axiom (OWL 2 Syntax §9.2.4 – §9.2.10, `FunctionalObjectProperty`
    and its siblings), not a declaration. -/
def isCharacteristicIri (i : WfIri) : Bool :=
  i == owlFunctionalProperty || i == owlInverseFunctionalProperty
  || i == owlTransitiveProperty || i == owlSymmetricProperty
  || i == owlAsymmetricProperty || i == owlIrreflexiveProperty
  || i == owlReflexiveProperty

/-- A conclusion triple that is an AXIOM about named properties even
    though its predicate or object is OWL vocabulary: a property
    characteristic on an IRI, or `owl:inverseOf` between two IRIs (OWL
    2 Syntax §9.2.3, `InverseObjectProperties`). Read as scaffolding,
    such a triple was KEPT in every refutation goal, which assumes the
    conclusion's own claim while proving its other conjuncts — the
    direction the module header names unsound. It is content, and gets
    a goal of its own. -/
def isPropertyAxiomTriple (t : Triple) : Bool :=
  (match t.s with | .iri _ => true | .bnode _ => false) &&
  ((t.p == rdfType && (match t.o with
      | .iri c => isCharacteristicIri c
      | _      => false)) ||
   (t.p == owlInverseOf && (match t.o with
      | .iri _ => true
      | _      => false)))

/-- Port of `is_structural_triple`, including the named-subject
    boolean-marker exception (module header), less the property axioms
    of `isPropertyAxiomTriple`. -/
def isStructuralTriple (t : Triple) : Bool :=
  !isPropertyAxiomTriple t &&
  ((t.p == rdfType &&
    (match t.o with
     | .iri c => isMetaTypeIri c
     | _      => false))
  || (if t.p == owlComplementOf || t.p == owlUnionOf || t.p == owlIntersectionOf
         || t.p == owlOneOf
      then (match t.s with | .bnode _ => true | .iri _ => false)
      else isStructuralPredicate t.p))

/-- The content assertions of a conclusion graph. -/
def contentTriples (g : Graph) : List Triple :=
  g.filter (fun t => !isStructuralTriple t)

/-- The scaffolding — kept verbatim in every refutation goal. -/
def structuralTriples (g : Graph) : List Triple :=
  g.filter isStructuralTriple

/-- A single class-membership assertion of a NAMED individual in a
    non-meta class (IRI or anonymous class-expression bnode). -/
def isClassMembership (t : Triple) : Bool :=
  t.p == rdfType
  && (match t.s with | .iri _ => true | .bnode _ => false)
  && (match t.o with
      | .iri c   => !isMetaTypeIri c
      | .bnode _ => true
      | _        => false)

/-- OWL/RDFS axiom and equality/nominal vocabulary — never a plain
    object-property assertion whose ¬p(s,o) encoding would be
    meaningful. Port of `is_axiom_or_special_predicate`. -/
def isAxiomOrSpecialPredicate (p : WfIri) : Bool :=
  p == rdfType || p == rdfsSubClassOf || p == rdfsSubPropertyOf
  || p == owlEquivalentClass || p == owlEquivalentProperty
  || p == owlDisjointWith || p == owlSameAs || p == owlDifferentFrom
  || p == owlPropertyDisjointWith || p == rdfsDomain || p == rdfsRange

/-- A plain object-property assertion `s p o` (s an IRI, o a
    resource, p not axiom/nominal vocabulary): its sound negation is
    ¬p(s,o). -/
def isNegatablePropertyAssertion (t : Triple) : Bool :=
  (match t.s with | .iri _ => true | .bnode _ => false)
  && (match t.o with | .iri _ => true | .bnode _ => true | _ => false)
  && !isAxiomOrSpecialPredicate t.p

/-! ## Fresh bnode ids

The `__factoidal_` prefix is illegal in W3C fixtures / parser output,
so these never collide with premise or closure bnodes. Each
refutation goal is a SEPARATE graph handed to the refuter on its own,
so reusing one fixed id set across goals is safe. -/

def peNegClassBNode  : BNodeId := "__factoidal_pe_neg_class"
def peSubFreshBNode  : BNodeId := "__factoidal_pe_sub_witness"
def pePropABNode     : BNodeId := "__factoidal_pe_prop_a"
def pePropBBNode     : BNodeId := "__factoidal_pe_prop_b"
def pePropRestrBNode : BNodeId := "__factoidal_pe_prop_restr"
def pePropOneofBNode : BNodeId := "__factoidal_pe_prop_oneof"
def pePropListBNode  : BNodeId := "__factoidal_pe_prop_list"
def peNegClassBNodeB : BNodeId := "__factoidal_pe_neg_class_b"
def peBoolCeBNode    : BNodeId := "__factoidal_pe_bool_ce"

/-! ## Goal builders -/

/-- The triples encoding `sub rdf:type ObjectMaxCardinality(0, p,
    ObjectOneOf(m))` plus the tautology `m ∈ {m}`. Together they
    assert exactly ¬p(sub, m) — see the module header. `none` when
    `m` is a literal or triple term. The `"0"` bound is
    `Vocabulary.litNni0` (`"0"^^xsd:nonNegativeInteger`), the same
    literal the F* builder uses. -/
def negPairTriples (sub : Subject) (p : WfIri) (m : Term)
    : Option (List Triple) :=
  match termAsSubject m with
  | none => none
  | some mSubj =>
    let restr : Subject := .bnode pePropRestrBNode
    let oneof : Subject := .bnode pePropOneofBNode
    let lcell : Subject := .bnode pePropListBNode
    some [
      ⟨sub,   rdfType,                    .bnode pePropRestrBNode⟩,
      ⟨restr, rdfType,                    .iri owlRestriction⟩,
      ⟨restr, owlOnProperty,              .iri p⟩,
      ⟨restr, owlMaxQualifiedCardinality, .literal litNni0⟩,
      ⟨restr, owlOnClass,                 .bnode pePropOneofBNode⟩,
      ⟨oneof, rdfType,                    .iri owlClass⟩,
      ⟨oneof, owlOneOf,                   .bnode pePropListBNode⟩,
      ⟨lcell, rdfFirst,                   m⟩,
      ⟨lcell, rdfRest,                    .iri rdfNil⟩,
      ⟨mSubj, rdfType,                    .bnode pePropOneofBNode⟩ ]

/-- Refutation goal for a property SUBSUMPTION `P ⊑ Q`: a fresh pair
    ⟨a,b⟩ with `P(a,b)` and `a : ≤0 Q.{b}` (= ¬Q(a,b)). `b` is a
    bnode, so `negPairTriples` is always `some` here (the `none` arm
    is unreachable and degrades to the bare edge). -/
def propInclusionGoal (base : Graph) (p q : WfIri) : Graph :=
  let a : Subject := .bnode pePropABNode
  let b : Term := .bnode pePropBBNode
  let edge : Triple := ⟨a, p, b⟩
  match negPairTriples a q b with
  | some ts => (edge :: ts) ++ base
  | none    => edge :: base

/-! ### Axiom conclusions whose negation is a fresh-witness assertion
(2026-09-07)

Six conclusion predicates fell through `negateContentTriple` to `none`
before this landing, which made `negationGoals` answer `none` for the
whole conclusion and left the tableau unasked
(`docs/designissues/2026-09-07-lean-owl-corpus-gap.md` § 10.1a). Each
builder below negates one OWL 2 Direct Semantics axiom (Table 6 of
https://www.w3.org/TR/owl2-direct-semantics/) into an assertion on
FRESH names, and the law it rests on is proved in
`OWL/TableauTheorems.lean`:

| conclusion | goal | law |
|---|---|---|
| `C owl:disjointWith D` | fresh `x : C`, `x : D` | `disjointGoal_iff` |
| `P owl:propertyDisjointWith Q` | fresh `a P b`, `a Q b` | `propDisjointGoal_iff` |
| `p rdfs:range C` | fresh `a p b`, `b : ¬C` | `rangeGoal_iff` |
| `p rdfs:domain C` | fresh `a p b`, `a : ¬C` | `domainGoal_iff` |
| `a owl:differentFrom b` | `a owl:sameAs b` | `diffGoal_iff` |
| `a owl:sameAs b` | `a owl:differentFrom b` | `sameGoal_iff` |

The two equality builders emit no fresh name: the negation of a claim
about two NAMED individuals is a claim about the same two. -/

/-- Refutation goal for `C owl:disjointWith D`: a fresh individual in
    both class expressions. -/
def disjointClassesGoal (base : Graph) (c d : Term) : Graph :=
  let x : Subject := .bnode peSubFreshBNode
  [ ⟨x, rdfType, c⟩, ⟨x, rdfType, d⟩ ] ++ base

/-- Refutation goal for `P owl:propertyDisjointWith Q`: a fresh pair
    in both role extensions. -/
def disjointPropertiesGoal (base : Graph) (p q : WfIri) : Graph :=
  let a : Subject := .bnode pePropABNode
  let b : Term := .bnode pePropBBNode
  [ ⟨a, p, b⟩, ⟨a, q, b⟩ ] ++ base

/-- Refutation goal for `p rdfs:domain C` (`onSubject = true`) and
    `p rdfs:range C` (`onSubject = false`): a fresh `p`-edge whose
    subject (resp. object) is in the complement of `C`. -/
def propertyDomainRangeGoal (base : Graph) (p : WfIri) (c : Term)
    (onSubject : Bool) : Graph :=
  let a : Subject := .bnode pePropABNode
  let b : Subject := .bnode pePropBBNode
  let neg : Subject := .bnode peNegClassBNode
  [ ⟨a, p, b.toTerm⟩, ⟨neg, owlComplementOf, c⟩,
    ⟨if onSubject then a else b, rdfType, .bnode peNegClassBNode⟩ ] ++ base

/-! ### Property axioms and data assertions (2026-10-10)

Each builder writes the negation of one OWL 2 Direct Semantics
property axiom (Table 6 of https://www.w3.org/TR/owl2-direct-semantics/)
on FRESH names:

| conclusion | goal |
|---|---|
| `p rdf:type owl:FunctionalProperty` | fresh `a p b₁`, `a p b₂`, `b₁ ≠ b₂` |
| `p rdf:type owl:InverseFunctionalProperty` | fresh `a₁ p b`, `a₂ p b`, `a₁ ≠ a₂` |
| `p rdf:type owl:TransitiveProperty` | fresh `a p b`, `b p c`, `¬p(a, c)` |
| `p rdf:type owl:SymmetricProperty` | fresh `a p b`, `¬p(b, a)` |
| `p rdf:type owl:AsymmetricProperty` | fresh `a p b`, `b p a` |
| `p rdf:type owl:IrreflexiveProperty` | fresh `a p a` |
| `p rdf:type owl:ReflexiveProperty` | fresh `a` with `¬p(a, a)` |
| `p owl:inverseOf q` | fresh `a p b` with `¬q(b, a)`; and `a q b` with `¬p(b, a)` |
| `s p "v"` (a literal) | `NegativePropertyAssertion(p s "v")` |

Each goal is the negated axiom's condition read off the table row: the
axiom fails in a model exactly when some elements witness it, and the
goal asserts such witnesses on fresh names. `≠` is
`owl:differentFrom`; `¬p(x, y)` is the `negPairTriples` encoding. The
data-assertion goal is the negative assertion's RDF form
(`owl:sourceIndividual` / `owl:assertionProperty` /
`owl:targetValue`, OWL 2 Mapping to RDF Table 16), which the refuter
reads as an excluded value (`Refute.excludedValues`). -/

def pePropCBNode  : BNodeId := "__factoidal_pe_prop_c"
def pePropA2BNode : BNodeId := "__factoidal_pe_prop_a2"
def pePropB2BNode : BNodeId := "__factoidal_pe_prop_b2"
def peNpaBNode    : BNodeId := "__factoidal_pe_npa"

/-- The goals negating `p rdf:type <characteristic>`. -/
def characteristicGoals (base : Graph) (p c : WfIri) : Option (List Graph) :=
  let a : Subject := .bnode pePropABNode
  let b : Subject := .bnode pePropBBNode
  let a2 : Subject := .bnode pePropA2BNode
  let b2 : Subject := .bnode pePropB2BNode
  let c3 : Subject := .bnode pePropCBNode
  if c == owlFunctionalProperty then
    some [[⟨a, p, b.toTerm⟩, ⟨a, p, b2.toTerm⟩, ⟨b, owlDifferentFrom, b2.toTerm⟩] ++ base]
  else if c == owlInverseFunctionalProperty then
    some [[⟨a, p, b.toTerm⟩, ⟨a2, p, b.toTerm⟩, ⟨a, owlDifferentFrom, a2.toTerm⟩] ++ base]
  else if c == owlTransitiveProperty then
    (negPairTriples a p c3.toTerm).map (fun ts =>
      [[⟨a, p, b.toTerm⟩, ⟨b, p, c3.toTerm⟩] ++ ts ++ base])
  else if c == owlSymmetricProperty then
    (negPairTriples b p a.toTerm).map (fun ts => [[⟨a, p, b.toTerm⟩] ++ ts ++ base])
  else if c == owlAsymmetricProperty then
    some [[⟨a, p, b.toTerm⟩, ⟨b, p, a.toTerm⟩] ++ base]
  else if c == owlIrreflexiveProperty then
    some [[⟨a, p, a.toTerm⟩] ++ base]
  else if c == owlReflexiveProperty then
    (negPairTriples a p a.toTerm).map (fun ts => [ts ++ base])
  else none

/-- The goals negating `p owl:inverseOf q`: `p ⊑ inv(q)` and
    `q ⊑ inv(p)`, both required. -/
def inverseGoals (base : Graph) (p q : WfIri) : Option (List Graph) :=
  let a : Subject := .bnode pePropABNode
  let b : Subject := .bnode pePropBBNode
  match negPairTriples b q a.toTerm, negPairTriples b p a.toTerm with
  | some t1, some t2 =>
      some [[⟨a, p, b.toTerm⟩] ++ t1 ++ base, [⟨a, q, b.toTerm⟩] ++ t2 ++ base]
  | _, _ => none

/-- The goal negating a data assertion `s p "v"`. -/
def negativeDataGoal (base : Graph) (s : Subject) (p : WfIri) (v : Term) : Graph :=
  let n : Subject := .bnode peNpaBNode
  [⟨n, owlSourceIndividual, s.toTerm⟩, ⟨n, owlAssertionProperty, .iri p⟩,
   ⟨n, owlTargetValue, v⟩] ++ base

/-- One content assertion → the refutation goals it expands to (a
    conjunction — every goal required). `none` = unsupported shape.
    Port of `negate_content_triple`; each arm's Direct Semantics
    soundness argument is in the F* original and summarised here. -/
def negateContentTriple (base : Graph) (t : Triple)
    : Option (List Graph) :=
  if isPropertyAxiomTriple t then
    match t.s, t.o with
    | .iri p, .iri c =>
        if t.p == owlInverseOf then inverseGoals base p c
        else characteristicGoals base p c
    | _, _ => none
  else if isClassMembership t then
    -- (a) `i rdf:type C` → `i rdf:type ¬C`.
    let comp : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.o⟩
    let member : Triple := ⟨t.s, rdfType, .bnode peNegClassBNode⟩
    some [comp :: member :: base]
  else if t.p == rdfsSubClassOf then
    -- (b) `C rdfs:subClassOf D` → fresh _:x with x ∈ C ⊓ ¬D.
    match termAsSubject t.o with
    | none   => none
    | some _ =>
      let x : Subject := .bnode peSubFreshBNode
      let inC : Triple := ⟨x, rdfType, t.s.toTerm⟩
      let comp : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.o⟩
      let inNegD : Triple := ⟨x, rdfType, .bnode peNegClassBNode⟩
      some [inC :: comp :: inNegD :: base]
  else if t.p == owlEquivalentClass then
    -- `C ≡ D` → refute C ⊑ D and D ⊑ C, both required.
    match termAsSubject t.o with
    | none   => none
    | some _ =>
      let x : Subject := .bnode peSubFreshBNode
      let compD : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.o⟩
      let g1 : Graph :=
        [ ⟨x, rdfType, t.s.toTerm⟩, compD,
          ⟨x, rdfType, .bnode peNegClassBNode⟩ ] ++ base
      let compC : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.s.toTerm⟩
      let g2 : Graph :=
        [ ⟨x, rdfType, t.o⟩, compC,
          ⟨x, rdfType, .bnode peNegClassBNode⟩ ] ++ base
      some [g1, g2]
  else if t.p == rdfsSubPropertyOf then
    -- `P ⊑ Q` → one property-subsumption refutation goal.
    match t.s, t.o with
    | .iri p, .iri q => some [propInclusionGoal base p q]
    | _, _           => none
  else if t.p == owlEquivalentProperty then
    -- `P ≡ Q` → refute P ⊑ Q and Q ⊑ P.
    match t.s, t.o with
    | .iri p, .iri q =>
        some [propInclusionGoal base p q, propInclusionGoal base q p]
    | _, _           => none
  else if t.p == owlComplementOf then
    -- Named-subject `X owl:complementOf Y`: CEXT(X) = Δ \ CEXT(Y) —
    -- disjointness AND coverage. Negation is the disjunction
    -- ∃x.(x ∈ X ⊓ Y) ∨ ∃x.(x ∈ ¬X ⊓ ¬Y), and P ∪ (A ∨ B) is
    -- unsatisfiable iff P ∪ A and P ∪ B each are — two goals, both
    -- required, each asserting exactly its disjunct on a fresh
    -- individual.
    match termAsSubject t.o with
    | none   => none
    | some _ =>
      let x : Subject := .bnode peSubFreshBNode
      let g1 : Graph :=
        [ ⟨x, rdfType, t.s.toTerm⟩, ⟨x, rdfType, t.o⟩ ] ++ base
      let compS : Triple := ⟨.bnode peNegClassBNode, owlComplementOf, t.s.toTerm⟩
      let compO : Triple := ⟨.bnode peNegClassBNodeB, owlComplementOf, t.o⟩
      let g2 : Graph :=
        [ compS, ⟨x, rdfType, .bnode peNegClassBNode⟩,
          compO, ⟨x, rdfType, .bnode peNegClassBNodeB⟩ ] ++ base
      some [g1, g2]
  else if t.p == owlUnionOf || t.p == owlIntersectionOf || t.p == owlOneOf then
    -- Named-subject boolean marker: the OWL 2 RDF mapping reads
    -- `S owl:unionOf (L)` as the class EQUALITY S ≡ CE(L) — refute
    -- S ⊑ CE(L) and CE(L) ⊑ S. A fresh bnode carrying the SAME
    -- marker over the SAME list stands for CE(L); the list cells are
    -- structural and already kept in `base`.
    match t.s with
    | .bnode _ => none  -- unreachable given the structural split
    | .iri _ =>
      let x : Subject := .bnode peSubFreshBNode
      let ce : Triple := ⟨.bnode peBoolCeBNode, t.p, t.o⟩
      let compCe : Triple :=
        ⟨.bnode peNegClassBNode, owlComplementOf, .bnode peBoolCeBNode⟩
      let g1 : Graph :=
        [ ce, ⟨x, rdfType, t.s.toTerm⟩,
          compCe, ⟨x, rdfType, .bnode peNegClassBNode⟩ ] ++ base
      let compS : Triple :=
        ⟨.bnode peNegClassBNodeB, owlComplementOf, t.s.toTerm⟩
      let g2 : Graph :=
        [ ce, ⟨x, rdfType, .bnode peBoolCeBNode⟩,
          compS, ⟨x, rdfType, .bnode peNegClassBNodeB⟩ ] ++ base
      some [g1, g2]
  else if t.p == owlDisjointWith then
    -- `C ⊓ D ⊑ ⊥` fails iff some individual is in both.
    some [disjointClassesGoal base t.s.toTerm t.o]
  else if t.p == owlPropertyDisjointWith then
    match t.s, t.o with
    | .iri p, .iri q => some [disjointPropertiesGoal base p q]
    | _, _           => none
  else if t.p == rdfsDomain || t.p == rdfsRange then
    -- The fresh object of the goal edge is a bnode INDIVIDUAL, so a
    -- data range as `C` is out of the encoding and falls to `none`.
    match t.s, t.o with
    | .iri p, .iri c => some [propertyDomainRangeGoal base p (.iri c)
                                (t.p == rdfsDomain)]
    | .iri p, .bnode b => some [propertyDomainRangeGoal base p (.bnode b)
                                  (t.p == rdfsDomain)]
    | _, _           => none
  else if t.p == owlDifferentFrom then
    -- Its negation is the identity of the same two names.
    some [⟨t.s, owlSameAs, t.o⟩ :: base]
  else if t.p == owlSameAs then
    some [⟨t.s, owlDifferentFrom, t.o⟩ :: base]
  else if isNegatablePropertyAssertion t then
    -- `s p o` → ¬p(s,o) on the existing named terms.
    match negPairTriples t.s t.p t.o with
    | none    => none
    | some ts => some [ts ++ base]
  else if (match t.s, t.o with
           | .iri _, .literal _ => !isAxiomOrSpecialPredicate t.p
           | _, _ => false) then
    -- `s p "v"` → NegativeDataPropertyAssertion(p s "v").
    some [negativeDataGoal base t.s t.p t.o]
  else none

def negateContentList (base : Graph) : List Triple → Option (List Graph)
  | []      => some []
  | t :: tl =>
    match negateContentTriple base t with
    | none    => none
    | some gs =>
      match negateContentList base tl with
      | none      => none
      | some rest => some (gs ++ rest)

/-! ## Conclusions with blank-node individuals: rolling up

A blank node in a conclusion graph is existentially quantified (RDF
1.1 Semantics §5.1: `G ⊨ E` iff some mapping of `E`'s blank nodes
satisfies it). `fred parent _:a . _:a parent _:b` claims
`∃a, b. parent(fred, a) ∧ parent(a, b)`, which is the class membership
`fred : ∃parent.∃parent.⊤`. Reading `_:a` as a fixed individual and
negating `parent(fred, _:a)` asks for `∀a. parent(fred, a)`, a
different and much stronger claim.

When the blank-node part of the conclusion is a FOREST whose trees
each hang off at most one named individual by one edge, every tree
ROLLS UP into one class expression (Horrocks and Tessaris, "A
conjunctive query language for description logic ABoxes", AAAI 2000,
§4): a blank node `x` becomes

    C(x) = ⊓ {D | x rdf:type D} ⊓ ⊓ {∃p.C(y) | x p y, y a blank node}
           ⊓ ⊓ {∋p.v | x p v, v named or a literal}

The tree's claim is then `c : ∃p.C(x)` when a named `c` has the edge
`c p x` to its root `x`, and `∃x. C(x)` when nothing named points
into it. The negations are `c : ¬∃p.C(x)` and `owl:Thing ⊑ ¬C(x)`;
each tree is one goal, and the goals are a conjunction like every
other (each tree is a conjunct of the conclusion; a tree shares no
blank node with another).

The shapes this does not read — a cycle, a blank node with two
parents, two named individuals pointing into one tree, an edge from a
blank node to a named individual's tree root in the other direction,
`owl:sameAs` on a blank node — need inverse roles or are not tree
shaped; they answer `none`, which leaves the closure verdict. -/

def peRollBNode (k : Nat) : BNodeId := s!"__factoidal_pe_roll_{k}"

/-- The blank nodes that stand for INDIVIDUALS of a conclusion: those
    in subject position of a content triple, or in object position of
    a content triple whose predicate is not `rdf:type` or axiom
    vocabulary, and that build no class expression. -/
def conclusionVariables (gC : Graph) (cs : List Triple) : List BNodeId :=
  let builds (b : BNodeId) : Bool := gC.any (fun t =>
    t.s == .bnode b && isStructuralTriple t && t.p != rdfType)
  let subj := cs.filterMap (fun t => match t.s with
    | .bnode b => some b
    | .iri _   => none)
  let obj := cs.filterMap (fun t =>
    if t.p == rdfType || isAxiomOrSpecialPredicate t.p then none
    else match t.o with
      | .bnode b => some b
      | _        => none)
  ((subj ++ obj).eraseDups).filter (fun b => !builds b)

def mentionsVariable (vs : List BNodeId) (t : Triple) : Bool :=
  (match t.s with | .bnode b => vs.contains b | .iri _ => false) ||
  (match t.o with | .bnode b => vs.contains b | _ => false)

/-- The triples writing one rolled-up class expression for the
    variable `x`, with fresh blank nodes numbered from `k`. Returns
    the term naming the expression, the triples, and the next free
    number. Fuel bounds the depth (a tree's depth is at most its size).
    `none` on an atom the roll-up does not read. -/
def rollUp (cs : List Triple) (vs : List BNodeId) : Nat → BNodeId → Nat →
    Option (Term × List Triple × Nat)
  | 0, _, _ => none
  | fuel + 1, x, k =>
    let mine := cs.filter (fun t => t.s == .bnode x)
    -- Conjuncts: the types, then one per out-edge.
    let step (acc : Option (List Term × List Triple × Nat)) (t : Triple)
        : Option (List Term × List Triple × Nat) :=
      match acc with
      | none => none
      | some (cjs, ts, k0) =>
        if t.p == rdfType then
          match t.o with
          | .literal _ => none
          | o          => some (cjs ++ [o], ts, k0)
        else if isAxiomOrSpecialPredicate t.p then none
        else
          match t.o with
          | .bnode y =>
            if vs.contains y then
              match rollUp cs vs fuel y (k0 + 1) with
              | none => none
              | some (cy, tsy, k1) =>
                let r : Subject := .bnode (peRollBNode k0)
                some (cjs ++ [.bnode (peRollBNode k0)],
                      ts ++ tsy ++ [⟨r, owlOnProperty, .iri t.p⟩,
                                    ⟨r, owlSomeValuesFrom, cy⟩], k1)
            else none
          | v =>
            let r : Subject := .bnode (peRollBNode k0)
            some (cjs ++ [.bnode (peRollBNode k0)],
                  ts ++ [⟨r, owlOnProperty, .iri t.p⟩, ⟨r, owlHasValue, v⟩], k0 + 1)
    match mine.foldl step (some ([], [], k)) with
    | none => none
    | some ([], ts, k1)  => some (.iri owlThing, ts, k1)
    | some ([c], ts, k1) => some (c, ts, k1)
    | some (cjs, ts, k1) =>
      -- `owl:intersectionOf` over an RDF list of the conjuncts.
      let n := cjs.length
      let cells := (List.range n).map (fun j => peRollBNode (k1 + 1 + j))
      let listTs := (List.range n).flatMap (fun j =>
        let cell : Subject := .bnode (peRollBNode (k1 + 1 + j))
        let next : Term := if j + 1 < n then .bnode (peRollBNode (k1 + 2 + j)) else .iri rdfNil
        [⟨cell, rdfFirst, cjs.getD j (.iri owlThing)⟩, ⟨cell, rdfRest, next⟩])
      let headT : Term := match cells.head? with
        | some c => .bnode c
        | none   => .iri rdfNil
      some (.bnode (peRollBNode k1),
            ts ++ [⟨.bnode (peRollBNode k1), owlIntersectionOf, headT⟩] ++ listTs,
            k1 + 1 + n)

/-- The variables with an edge INTO them from another variable. -/
def varParents (cs : List Triple) (vs : List BNodeId) (y : BNodeId) : List Triple :=
  cs.filter (fun t => t.o == .bnode y && t.p != rdfType &&
    (match t.s with | .bnode b => vs.contains b | .iri _ => false))

/-- The variables reachable from `frontier` along variable-to-variable
    edges, `seen` included. Fuel bounds the walk by the variable count. -/
def reachableVars (cs : List Triple) (vs : List BNodeId)
    : Nat → List BNodeId → List BNodeId → List BNodeId
  | 0,     _,        seen => seen
  | n + 1, frontier, seen =>
    let next := (frontier.flatMap (fun x => cs.filterMap (fun t =>
      if t.s == .bnode x && t.p != rdfType then
        match t.o with
        | .bnode y => if vs.contains y && !seen.contains y then some y else none
        | _        => none
      else none))).eraseDups
    if next.isEmpty then seen else reachableVars cs vs n next (seen ++ next)

/-- Every triple that mentions a variable is one the roll-up reads:
    a type or an edge with a variable subject, or an edge from a named
    individual into a variable. Anything else (a variable as the
    object of `rdf:type`, `owl:sameAs` on a variable, an axiom
    predicate) is not read, and DROPPING it would claim the rest of the
    conclusion for the whole. -/
def rollableTriple (vs : List BNodeId) (t : Triple) : Bool :=
  match t.s with
  | .bnode b => vs.contains b && (t.p == rdfType || !isAxiomOrSpecialPredicate t.p)
  | .iri _ =>
      t.p != rdfType && !isAxiomOrSpecialPredicate t.p &&
      (match t.o with | .bnode b => vs.contains b | _ => false)

/-- The rolled-up refutation goals for the content triples that
    mention a conclusion variable, or `none` when they are not a
    forest of the readable shape (section header). -/
def rolledUpGoals (base : Graph) (cs : List Triple) (vs : List BNodeId)
    : Option (List Graph) :=
  if vs.isEmpty then some []
  else if !cs.all (rollableTriple vs) then none
  else
    -- Every edge between a named subject and a variable object.
    let fromNamed := cs.filter (fun t => t.p != rdfType &&
      (match t.s with | .iri _ => true | .bnode _ => false) &&
      (match t.o with | .bnode b => vs.contains b | _ => false))
    -- Tree shape: at most one parent for every variable, counting
    -- both variable and named parents.
    let parents (y : BNodeId) : Nat :=
      (varParents cs vs y).length + (fromNamed.filter (·.o == .bnode y)).length
    if vs.any (fun y => parents y > 1) then none
    else
      -- An edge into a NAMED individual from a variable is read as
      -- `∋p.c` (handled in `rollUp`); every other triple mentioning a
      -- variable must be a type or an edge.
      let roots := vs.filter (fun y => (varParents cs vs y).isEmpty)
      -- Every variable must be reachable from a root (no cycle):
      -- a forest on `n` variables with `r` roots has `n - r` edges.
      let varEdges := cs.filter (fun t => t.p != rdfType &&
        (match t.s, t.o with
         | .bnode a, .bnode b => vs.contains a && vs.contains b
         | _, _ => false))
      -- A cycle has no root, so its variables are unreachable from
      -- the roots; every variable must be reached.
      if varEdges.length + roots.length != vs.length then none
      else if (reachableVars cs vs (vs.length + 1) roots roots).eraseDups.length
              != vs.length then none
      else
        let fuel := vs.length + 1
        roots.foldl (fun (acc : Option (List Graph)) x =>
          match acc with
          | none => none
          | some gs =>
            match rollUp cs vs fuel x 0 with
            | none => none
            | some (cx, ts, k) =>
              let neg : Subject := .bnode (peRollBNode k)
              match fromNamed.find? (·.o == .bnode x) with
              | some e =>
                -- `c : ¬∃p.C(x)`.
                let r : Subject := .bnode (peRollBNode (k + 1))
                some (gs ++ [ts ++ [⟨r, owlOnProperty, .iri e.p⟩,
                                    ⟨r, owlSomeValuesFrom, cx⟩,
                                    ⟨neg, owlComplementOf, r.toTerm⟩,
                                    ⟨e.s, rdfType, neg.toTerm⟩] ++ base])
              | none =>
                -- `owl:Thing ⊑ ¬C(x)`.
                some (gs ++ [ts ++ [⟨neg, owlComplementOf, cx⟩,
                                    ⟨.iri owlThing, rdfsSubClassOf, neg.toTerm⟩] ++ base]))
          (some [])

/-- The conjunction of refutation goals for a conclusion graph, or
    `none` when any content assertion is an unsupported shape
    (conservative: the caller keeps its closure verdict). The caller
    ANDs the refuter over the returned list — the entailment is
    proven iff EVERY goal refutes. Port of `negation_goals`, with the
    blank-node conclusions rolled up (section above). -/
def negationGoals (gC : Graph) : Option (List Graph) :=
  match contentTriples gC with
  | []  => none
  | cs  =>
    let vs := conclusionVariables gC cs
    let (withVars, plain) := cs.partition (mentionsVariable vs)
    let base := structuralTriples gC
    match negateContentList base plain, rolledUpGoals base withVars vs with
    | some gs1, some gs2 =>
      match gs1 ++ gs2 with
      | []     => none
      | g :: t => some (g :: t)
    | _, _ => none

end L4Factoidal.OWL.Refute
