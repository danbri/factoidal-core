/-
L4Factoidal.RIF.OwlDirect — RIF-OWL Direct entailment for a RIF Core
document that imports an RDF graph under the OWL Direct profile.

Spec: RIF RDF and OWL Compatibility (Second Edition),
<https://www.w3.org/TR/rif-rdf-owl/>:

* §4.2.2 — the semantics. A common-RIF-OWL Direct-interpretation
  relates an OWL 2 Direct interpretation to a RIF dl-semantic
  structure: the extension of a class `c` is the set of `k` with
  `k[rdf:type -> c]`, the extension of an object or data property `p`
  is the set of pairs `(k, l)` with `k[p -> l]`, and `IR ∪ LV` is the
  RIF domain `Dind`.
* §5.2 — an `Import(<g> <…/entailment/OWL-Direct>)` makes the
  combination `<R, {O}>` with `O` the OWL 2 DL ontology whose RDF
  representation `g` is, interpreted under RIF-OWL Direct-entailment.
* §9.2 — the reduction this module executes. For an OWL 2 RL ontology,
  RIF-OWL Direct-entailment of a DL-condition `φ` holds iff the RIF
  document `merge({R, ROWL-Direct(V,R), trO(trN(O))})` entails `φ`
  (the Theorem at the end of §9.2.2.2). `trN` normalises the axioms,
  `trO` writes each one as RIF rules over frames, and `ROWL-Direct`
  axiomatises the parts of the Direct Semantics that the rules need:
  `owl:Nothing` is empty, `owl:Thing` and `rdfs:Literal` are disjoint,
  every class, property subject, object-property value and named
  individual is in `owl:Thing`, and every data value is in
  `rdfs:Literal`.

## Which axioms are embedded

`readOntology` reads the graph by the reverse direction of OWL 2
Mapping to RDF Graphs (<https://www.w3.org/TR/owl2-mapping-to-rdf/>)
§3, for the axioms whose `trO` image is a RIF Core rule over NAMED
entities without equality and without disjunction:

| OWL 2 axiom (named entities) | RIF Core rule (`trO`, §9.2.2.2 row) |
|---|---|
| SubClassOf(A B), EquivalentClasses(A B) | `?x[rdf:type->B] :- ?x[rdf:type->A]` (rows 2, 6) |
| DisjointClasses(A B) | `rif:error :- And(?x[rdf:type->A] ?x[rdf:type->B])` (trN row 6, trO row 4a) |
| Sub/EquivalentObjectProperties, Sub/EquivalentDataProperties | `?x[q->?y] :- ?x[p->?y]` (row 15) |
| InverseObjectProperties(p q) | two rules (row 17) |
| ObjectPropertyDomain, DataPropertyDomain (named class) | `?x[rdf:type->A] :- ?x[p->?y]` (trN rows 14-15) |
| ObjectPropertyRange (named class) | `?y[rdf:type->A] :- ?x[p->?y]` (trN row 17) |
| Symmetric / Transitive ObjectProperty | rows 21, 23 |
| Irreflexive / Asymmetric ObjectProperty, DisjointObjectProperties | `rif:error` rules, rows 20, 22, 16 |
| ClassAssertion, ObjectPropertyAssertion, DataPropertyAssertion | ground frames (trN rows 30-31, 33) |

Declarations, the ontology header, annotation assertions (on an
annotation property, built-in or declared, including the OWL 1
`owl:OntologyProperty` of Mapping Table 5) and annotation-property
axioms carry no Direct-Semantics content and are DROPPED — which is
what the corpus's `Non-Annotation_Entailment` tests.

Every other triple — a blank node (an anonymous individual or a class
expression), an axiom that needs equality (functional and
inverse-functional properties, `owl:sameAs`, keys; §9.2 says those
leave RIF Core), `owl:imports`, a data property range, an undeclared
predicate or class — is kept in `Reading.outside` with its reason.

## Which verdicts are sound, and why

* `holds` from a SUBSET of the axioms is sound: every model of
  `<R, {O}>` is a model of `<R, {O'}>` for `O' ⊆ O`, so an entailment
  of the smaller combination is one of the larger. An inconsistency of
  the smaller combination is one of the larger, and an inconsistent
  combination entails every formula (§9.2, ROWL-Direct row (xi)).
* `doesNotHold` is given ONLY when the reverse mapping embedded every
  logical axiom (`outside` is empty), the forward chain reached its
  fixed point with no built-in blocked, the document is a RIF-BLD
  DL-document formula and the goal a DL-condition (§4.1), and no
  datatype IRI is used as a class (see `ROWL-Direct (viii)` below).
  Under those conditions the §9.2 Theorem applies.
* Anything else is `undecided`, naming the first triple outside the
  embedded subset.

## The two parts of ROWL-Direct(V,R) handled by a check, not by rules

* (viii)/(ix) assert, for every literal and every datatype in `V`,
  whether the literal's value is in that datatype's value space.
  This module asserts it for the literal's OWN datatype only, and in
  exchange refuses `doesNotHold` when any datatype IRI occurs in a
  class position of `R`, the goal or the embedded ontology rules: then
  no rule body can read a cross-datatype membership, and the only
  datatype memberships in the closure are the ones asserted here,
  which are true.
* (ii) — `owl:Thing` and `rdfs:Literal` are disjoint — is also applied
  to the CLOSURE: a literal of a known datatype that ends up typed
  `owl:Thing` makes the combination inconsistent even when the literal
  was computed by a built-in and so is not in `V`.

## Scope of the vocabulary `V`

(vii) asserts `i[rdf:type -> owl:Thing]` for "every IRI i in V", and
§9.2.2.2 assumes `V` includes every constant of `R` and `φ`. `V` is
read here as the IRIs the embedded axioms and declarations name plus
every `rif:iri` constant of `R` and `φ`, as written.

Tracking: https://github.com/danbri/factoidal/issues/698 (RIF Core
residue, earlier https://github.com/danbri/factoidal/issues/622).
-/
import L4Factoidal.RIF.Engine
import L4Factoidal.RIF.Saturate

namespace L4Factoidal.RIF.OwlDirect

open L4Factoidal.RDF
open L4Factoidal.RIF

/-! ## Vocabulary -/

def owlNs : String := "http://www.w3.org/2002/07/owl#"
def rdfsNs : String := "http://www.w3.org/2000/01/rdf-schema#"
def rdfTypeIri : String := rdfNs ++ "type"
def owlThing : String := owlNs ++ "Thing"
def owlNothing : String := owlNs ++ "Nothing"
def rdfsLiteral : String := rdfsNs ++ "Literal"

/-- `rif:error`, the 0-ary predicate whose truth makes a document
    inconsistent (RIF-RDF-OWL §9.2.2.2, ROWL-Direct row (xi)). -/
def rifError : String := "http://www.w3.org/2007/rif#error"

/-- The built-in annotation properties of OWL 2 Structural
    Specification §5.5, which need no declaration. -/
def builtinAnnotationProperties : List String :=
  [rdfsNs ++ "label", rdfsNs ++ "comment", rdfsNs ++ "seeAlso",
   rdfsNs ++ "isDefinedBy", owlNs ++ "deprecated", owlNs ++ "versionInfo",
   owlNs ++ "priorVersion", owlNs ++ "backwardCompatibleWith",
   owlNs ++ "incompatibleWith"]

/-- Is this IRI a datatype of the OWL 2 datatype map (OWL 2 Structural
    Specification §4) or a RIF-required datatype (RIF-DTB §2.3)? The
    XSD namespace covers both lists' XSD members. -/
def isBuiltinDatatype (iri : String) : Bool :=
  iri.startsWith xsdNs ||
  [owlNs ++ "real", owlNs ++ "rational", rdfNs ++ "PlainLiteral",
   rdfNs ++ "XMLLiteral", rdfsLiteral].contains iri

/-- The `rdf:type` objects that DECLARE an entity (OWL 2 Mapping
    Table 7, with `owl:OntologyProperty` from Table 5) or mark the
    ontology header. They carry no Direct-Semantics content. -/
def declarationTypes : List String :=
  [owlNs ++ "Class", owlNs ++ "ObjectProperty", owlNs ++ "DatatypeProperty",
   owlNs ++ "AnnotationProperty", owlNs ++ "OntologyProperty",
   rdfsNs ++ "Datatype", owlNs ++ "NamedIndividual", owlNs ++ "Ontology"]

/-- Property-characteristic types that make their subject an object
    property (Mapping Tables 5 and 7). -/
def objectPropertyTypes : List String :=
  [owlNs ++ "ObjectProperty", owlNs ++ "SymmetricProperty",
   owlNs ++ "TransitiveProperty", owlNs ++ "InverseFunctionalProperty",
   owlNs ++ "IrreflexiveProperty", owlNs ++ "AsymmetricProperty",
   owlNs ++ "ReflexiveProperty"]

/-! ## Entity typing: what the graph declares -/

structure Typing where
  classes     : List String := []
  objectProps : List String := []
  dataProps   : List String := []
  annProps    : List String := []
  datatypes   : List String := []
  /-- The ontology header subjects (IRI or blank node). -/
  headers     : List Subject := []
deriving Inhabited

def subjectIri? : Subject → Option String
  | .iri i => some i.val
  | .bnode _ => none

def termIri? : Term → Option String
  | .iri i => some i.val
  | _ => none

/-- Fold the declarations of a graph into a `Typing`. `owl:Thing` and
    `owl:Nothing` are classes and the built-in annotation properties
    and datatypes are declared implicitly (OWL 2 Structural
    Specification §5.8.1). -/
def typingOf (g : Graph) : Typing :=
  let base : Typing :=
    { classes := [owlThing, owlNothing], annProps := builtinAnnotationProperties }
  g.foldl (fun ty t =>
    if t.p.val != rdfTypeIri then ty else
    match termIri? t.o with
    | none => ty
    | some c =>
      if c == owlNs ++ "Ontology" then { ty with headers := ty.headers ++ [t.s] } else
      match subjectIri? t.s with
      | none => ty
      | some s =>
        if c == owlNs ++ "Class" then { ty with classes := ty.classes ++ [s] }
        else if objectPropertyTypes.contains c then { ty with objectProps := ty.objectProps ++ [s] }
        else if c == owlNs ++ "DatatypeProperty" then { ty with dataProps := ty.dataProps ++ [s] }
        else if c == owlNs ++ "AnnotationProperty" || c == owlNs ++ "OntologyProperty" then
          { ty with annProps := ty.annProps ++ [s] }
        else if c == rdfsNs ++ "Datatype" then { ty with datatypes := ty.datatypes ++ [s] }
        else ty) base

def Typing.isClass (ty : Typing) (c : String) : Bool := ty.classes.contains c
def Typing.isObjectProp (ty : Typing) (p : String) : Bool := ty.objectProps.contains p
def Typing.isDataProp (ty : Typing) (p : String) : Bool := ty.dataProps.contains p
def Typing.isAnnProp (ty : Typing) (p : String) : Bool := ty.annProps.contains p
def Typing.isDatatype (ty : Typing) (d : String) : Bool :=
  isBuiltinDatatype d || ty.datatypes.contains d

/-! ## The axioms this module embeds -/

/-- An OWL 2 axiom over named entities, after `trN` (RIF-RDF-OWL
    §9.2.2.1): equivalences are already split into two inclusions. -/
inductive Axiom where
  | subClass        (a b : String)
  | disjointClasses (a b : String)
  | subProp         (p q : String)
  | inverse         (p q : String)
  | domain          (p a : String)
  | range           (p a : String)
  | symmetric       (p : String)
  | transitive      (p : String)
  | irreflexive     (p : String)
  | asymmetric      (p : String)
  | disjointProps   (p q : String)
  | classAssertion  (c a : String)
  | propAssertion   (p a : String) (v : GTerm)
deriving Repr, DecidableEq, Inhabited

/-- How one triple reads under the reverse mapping. -/
inductive TripleReading where
  /-- A declaration, the ontology header, or an annotation. -/
  | noContent
  | axioms (as : List Axiom)
  /-- Logical content outside the embedded subset, with the reason. -/
  | outside (why : String)
deriving Repr, Inhabited

/-- Read one triple. Spec: OWL 2 Mapping to RDF Graphs §3.2 (Tables
    16 and 17 for axioms, 7 for declarations) restricted to named
    entities; `trN` (RIF-RDF-OWL §9.2.2.1) splits equivalences. -/
def readTriple (ty : Typing) (t : Triple) : TripleReading :=
  let p := t.p.val
  let isHeader := ty.headers.contains t.s
  match t.s with
  | .bnode _ =>
      if isHeader && (p == rdfTypeIri || ty.isAnnProp p || p == owlNs ++ "versionIRI")
      then .noContent
      else if isHeader && p == owlNs ++ "imports" then
        .outside "owl:imports names an ontology whose axioms are not loaded"
      else .outside "a blank-node subject (an anonymous individual or a class expression)"
  | .iri si =>
    let s := si.val
    if isHeader && p == owlNs ++ "imports" then
      .outside "owl:imports names an ontology whose axioms are not loaded"
    else if isHeader && p == owlNs ++ "versionIRI" then .noContent
    else if ty.isAnnProp p then .noContent
    else if p == rdfTypeIri then
      match termIri? t.o with
      | none => .outside "rdf:type with a blank-node or literal object"
      | some c =>
        if declarationTypes.contains c then .noContent
        else if c == owlNs ++ "SymmetricProperty" then .axioms [.symmetric s]
        else if c == owlNs ++ "TransitiveProperty" then .axioms [.transitive s]
        else if c == owlNs ++ "IrreflexiveProperty" then .axioms [.irreflexive s]
        else if c == owlNs ++ "AsymmetricProperty" then .axioms [.asymmetric s]
        else if c == owlNs ++ "FunctionalProperty" || c == owlNs ++ "InverseFunctionalProperty" then
          .outside "a functional or inverse-functional property needs equality, which RIF Core does not have (RIF-RDF-OWL §9.2)"
        else if ty.isClass c then .axioms [.classAssertion c s]
        else .outside s!"rdf:type object {c} is not declared as a class"
    else
      let o? := termIri? t.o
      let bothClasses := match o? with | some o => ty.isClass s && ty.isClass o | none => false
      let bothObj := match o? with | some o => ty.isObjectProp s && ty.isObjectProp o | none => false
      let bothData := match o? with | some o => ty.isDataProp s && ty.isDataProp o | none => false
      let bothAnn := match o? with | some o => ty.isAnnProp s && ty.isAnnProp o | none => false
      let o := o?.getD ""
      if p == rdfsNs ++ "subClassOf" then
        if bothClasses then .axioms [.subClass s o]
        else .outside "rdfs:subClassOf between expressions that are not both declared classes"
      else if p == owlNs ++ "equivalentClass" then
        if bothClasses then .axioms [.subClass s o, .subClass o s]
        else .outside "owl:equivalentClass between expressions that are not both declared classes"
      else if p == owlNs ++ "disjointWith" then
        if bothClasses then .axioms [.disjointClasses s o]
        else .outside "owl:disjointWith between expressions that are not both declared classes"
      else if p == rdfsNs ++ "subPropertyOf" then
        if bothObj || bothData then .axioms [.subProp s o]
        else if bothAnn then .noContent
        else .outside "rdfs:subPropertyOf between properties of different or undeclared kinds"
      else if p == owlNs ++ "equivalentProperty" then
        if bothObj || bothData then .axioms [.subProp s o, .subProp o s]
        else .outside "owl:equivalentProperty between properties of different or undeclared kinds"
      else if p == owlNs ++ "propertyDisjointWith" then
        if bothObj || bothData then .axioms [.disjointProps s o]
        else .outside "owl:propertyDisjointWith between properties of different or undeclared kinds"
      else if p == owlNs ++ "inverseOf" then
        if bothObj then .axioms [.inverse s o]
        else .outside "owl:inverseOf on an expression that is not a declared object property"
      else if p == rdfsNs ++ "domain" then
        if ty.isAnnProp s then .noContent
        else if (ty.isObjectProp s || ty.isDataProp s) && o?.isSome && ty.isClass o then
          .axioms [.domain s o]
        else .outside "rdfs:domain whose class is not a declared class"
      else if p == rdfsNs ++ "range" then
        if ty.isAnnProp s then .noContent
        else if ty.isObjectProp s && o?.isSome && ty.isClass o then .axioms [.range s o]
        else if ty.isDataProp s then
          .outside "a data property range asserts datatype membership, outside the embedded slice"
        else .outside "rdfs:range whose class is not a declared class"
      else if ty.isObjectProp p then
        if o?.isSome then .axioms [.propAssertion p s (gIri o)]
        else .outside "an object property valued by a literal or a blank node"
      else if ty.isDataProp p then
        match t.o with
        | .literal _ =>
            (match L4Factoidal.RIF.Saturate.gOfTerm t.o with
             | some v => .axioms [.propAssertion p s v]
             | none   => .outside "a literal with no RIF constant")
        | _ => .outside "a data property valued by an IRI or a blank node"
      else .outside s!"predicate {p} is not declared as an object, data or annotation property"

/-- The reading of a whole graph. -/
structure Reading where
  typing  : Typing
  axioms  : List Axiom
  outside : List (Triple × String)
deriving Inhabited

def readOntology (g : Graph) : Reading :=
  let ty := typingOf g
  let (ax, out) := g.foldl (fun (ax, out) t =>
    match readTriple ty t with
    | .noContent => (ax, out)
    | .axioms as => (ax ++ as, out)
    | .outside why => (ax, out ++ [(t, why)])) (([] : List Axiom), ([] : List (Triple × String)))
  { typing := ty, axioms := ax, outside := out }

/-! ## `trO`: the axioms as RIF rules (RIF-RDF-OWL §9.2.2.2) -/

def vx : Tm := .var "x"
def vy : Tm := .var "y"
def vz : Tm := .var "z"
def cI (s : String) : Tm := .const s iriSpace
def typeAtom (o : Tm) (c : String) : Atom := .frame o (cI rdfTypeIri) (cI c)
def propAtom (o : Tm) (p : String) (v : Tm) : Atom := .frame o (cI p) v
def errorAtom : Atom := .pos rifError iriSpace []

def tmOfG : GTerm → Tm
  | .const l sp   => .const l sp
  | .list xs      => .list (xs.map tmOfG)
  | .fapp f sp xs => .fapp f sp (xs.map tmOfG)

def rulesOfAxiom : Axiom → List Rule
  | .subClass a b =>
      [{ vars := ["x"], head := typeAtom vx b, body := some (.atom (typeAtom vx a)) }]
  | .disjointClasses a b =>
      [{ vars := ["x"], head := errorAtom,
         body := some (.and [.atom (typeAtom vx a), .atom (typeAtom vx b)]) }]
  | .subProp p q =>
      [{ vars := ["x", "y"], head := propAtom vx q vy, body := some (.atom (propAtom vx p vy)) }]
  | .inverse p q =>
      [{ vars := ["x", "y"], head := propAtom vy q vx, body := some (.atom (propAtom vx p vy)) },
       { vars := ["x", "y"], head := propAtom vy p vx, body := some (.atom (propAtom vx q vy)) }]
  | .domain p a =>
      [{ vars := ["x", "y"], head := typeAtom vx a, body := some (.atom (propAtom vx p vy)) }]
  | .range p a =>
      [{ vars := ["x", "y"], head := typeAtom vy a, body := some (.atom (propAtom vx p vy)) }]
  | .symmetric p =>
      [{ vars := ["x", "y"], head := propAtom vy p vx, body := some (.atom (propAtom vx p vy)) }]
  | .transitive p =>
      [{ vars := ["x", "y", "z"], head := propAtom vx p vz,
         body := some (.and [.atom (propAtom vx p vy), .atom (propAtom vy p vz)]) }]
  | .irreflexive p =>
      [{ vars := ["x"], head := errorAtom, body := some (.atom (propAtom vx p vx)) }]
  | .asymmetric p =>
      [{ vars := ["x", "y"], head := errorAtom,
         body := some (.and [.atom (propAtom vx p vy), .atom (propAtom vy p vx)]) }]
  | .disjointProps p q =>
      [{ vars := ["x", "y"], head := errorAtom,
         body := some (.and [.atom (propAtom vx p vy), .atom (propAtom vx q vy)]) }]
  | .classAssertion c a => [{ head := typeAtom (cI a) c }]
  | .propAssertion p a v => [{ head := propAtom (cI a) p (tmOfG v) }]

/-! ## R': membership as frames, subclass facts as rules

§9.2.2.2 replaces every `a # b` of `R` by `a[rdf:type -> b]`, and
§9.2.1 embeds a DL-subclass FACT `b ## c` as the rule
`Forall ?x (?x[rdf:type -> c] :- ?x[rdf:type -> b])`. -/

def memberAsFrameAtom : Atom → Atom
  | .member o c => .frame o (cI rdfTypeIri) c
  | a => a

def memberAsFrame : Formula → Formula
  | .atom a      => .atom (memberAsFrameAtom a)
  | .and fs      => .and (fs.map memberAsFrame)
  | .or fs       => .or (fs.map memberAsFrame)
  | .exists vs f => .exists vs (memberAsFrame f)

def dlRule (r : Rule) : Rule :=
  match r.head, r.body with
  | .sub (.const b bs) (.const c cs), none =>
      if bs == iriSpace && cs == iriSpace then
        { vars := ["owlDirectSubclassVar"],
          head := typeAtom (.var "owlDirectSubclassVar") c,
          body := some (.atom (typeAtom (.var "owlDirectSubclassVar") b)) }
      else { r with head := memberAsFrameAtom r.head, body := r.body.map memberAsFrame }
  | _, _ => { r with head := memberAsFrameAtom r.head, body := r.body.map memberAsFrame }

/-! ## DL-document formulas and DL-conditions (§4.1)

A DL-frame has a CONSTANT property and, for `rdf:type`, a constant
class; a DL-membership a constant class; a subclass formula may only
be a FACT with two constants, and never occurs in a condition. -/

def dlAtom : Atom → Bool
  | .frame _ (.const p _) v =>
      if p == rdfTypeIri then (match v with | .const _ _ => true | _ => false) else true
  | .frame _ _ _ => false
  | .member _ (.const _ _) => true
  | .member _ _ => false
  | .sub _ _ => false
  | _ => true

def dlFormula : Formula → Bool
  | .atom a      => dlAtom a
  | .and fs      => (fs.map dlFormula).all id
  | .or fs       => (fs.map dlFormula).all id
  | .exists _ f  => dlFormula f

def dlRuleOk (r : Rule) : Bool :=
  match r.head, r.body with
  | .sub (.const _ _) (.const _ _), none => true
  | h, none => dlAtom h
  | h, some b => dlAtom h && dlFormula b

/-! ## Constants of a document, for the vocabulary `V` -/

def constsOfTm : Tm → List GTerm
  | .var _         => []
  | .const l sp    => [.const l sp]
  | .list xs       => xs.flatMap constsOfTm
  | .fapp _ _ xs   => xs.flatMap constsOfTm
  | .external _ xs => xs.flatMap constsOfTm

def constsOfAtom : Atom → List GTerm
  | .pos _ _ args     => args.flatMap constsOfTm
  | .frame o p v      => constsOfTm o ++ constsOfTm p ++ constsOfTm v
  | .member o c       => constsOfTm o ++ constsOfTm c
  | .sub c d          => constsOfTm c ++ constsOfTm d
  | .equal a b        => constsOfTm a ++ constsOfTm b
  | .externalPred _ a => a.flatMap constsOfTm

def constsOfFormula : Formula → List GTerm
  | .atom a      => constsOfAtom a
  | .and fs      => fs.flatMap constsOfFormula
  | .or fs       => fs.flatMap constsOfFormula
  | .exists _ f  => constsOfFormula f

def constsOfRule (r : Rule) : List GTerm :=
  constsOfAtom r.head ++ (match r.body with | none => [] | some b => constsOfFormula b)

/-- The constants in class position, `?[rdf:type -> c]`. -/
def typeClassesOfAtom : Atom → List String
  | .frame _ (.const p _) (.const c _) => if p == rdfTypeIri then [c] else []
  | _ => []

def typeClassesOfFormula : Formula → List String
  | .atom a      => typeClassesOfAtom a
  | .and fs      => fs.flatMap typeClassesOfFormula
  | .or fs       => fs.flatMap typeClassesOfFormula
  | .exists _ f  => typeClassesOfFormula f

def typeClassesOfRule (r : Rule) : List String :=
  typeClassesOfAtom r.head ++ (match r.body with | none => [] | some b => typeClassesOfFormula b)

def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- A constant whose symbol space is a datatype known to the
    combination is a DATA VALUE: RIF-DTB gives it the value its
    lexical form maps to, and §4.2.2.2 puts value spaces in `LV`. -/
def isDataValue (ty : Typing) : GTerm → Bool
  | .const _ sp => sp != iriSpace && sp != localSpace && ty.isDatatype sp
  | _ => false

/-- A literal constant whose symbol space is neither `rif:iri`,
    `rif:local` nor a known datatype. The combination does not say
    whether it is a data value, so no negative verdict is read off a
    closure that contains one. -/
def isUnknownLiteral (ty : Typing) : GTerm → Bool
  | .const _ sp => sp != iriSpace && sp != localSpace && !ty.isDatatype sp
  | _ => false

/-- Is the literal in the value space of its own datatype?
    ROWL-Direct (viii) for `u' = u`, decided by RIF-DTB's
    `pred:is-literal-T` (`RIF/Builtins.lean`). -/
def ownDatatypeMember (g : GTerm) : Bool :=
  match g with
  | .const _ sp =>
      if sp == rdfNs ++ "PlainLiteral" then isLiteralOf "PlainLiteral" g == .yes
      else if sp == rdfNs ++ "XMLLiteral" then isLiteralOf "XMLLiteral" g == .yes
      else match xsdLocal sp with
        | some b => isLiteralOf b g == .yes
        | none   => false
  | _ => false

/-! ## ROWL-Direct(V,R) (§9.2.2.2) -/

structure Vocab where
  classes     : List String
  objectProps : List String
  dataProps   : List String
  datatypes   : List String
  iris        : List String
  literals    : List GTerm

def axiomClasses : Axiom → List String
  | .subClass a b | .disjointClasses a b => [a, b]
  | .domain _ a | .range _ a => [a]
  | .classAssertion c _ => [c]
  | _ => []

def axiomIris : Axiom → List String
  | .subClass a b | .disjointClasses a b => [a, b]
  | .subProp p q | .inverse p q | .disjointProps p q => [p, q]
  | .domain p a | .range p a => [p, a]
  | .symmetric p | .transitive p | .irreflexive p | .asymmetric p => [p]
  | .classAssertion c a => [c, a]
  | .propAssertion p a v =>
      [p, a] ++ (match v with | .const l sp => if sp == iriSpace then [l] else [] | _ => [])

def axiomLiterals : Axiom → List GTerm
  | .propAssertion _ _ v@(.const _ sp) => if sp == iriSpace then [] else [v]
  | _ => []

def vocabOf (rd : Reading) (rules : List Rule) (goal : Formula) : Vocab :=
  let ty := rd.typing
  let docConsts := rules.flatMap constsOfRule ++ constsOfFormula goal
  let docTypeClasses := rules.flatMap typeClassesOfRule ++ typeClassesOfFormula goal
  let docIris := docConsts.filterMap (fun g => match g with
    | .const l sp => if sp == iriSpace then some l else none
    | _ => none)
  let docLits := docConsts.filter (fun g => match g with
    | .const _ sp => sp != iriSpace && sp != localSpace
    | _ => false)
  let lits := docLits ++ rd.axioms.flatMap axiomLiterals
  let litTypes := lits.filterMap (fun g => match g with
    | .const _ sp => if ty.isDatatype sp then some sp else none
    | _ => none)
  let allTypeNames := ty.classes ++ rd.axioms.flatMap axiomClasses ++ docTypeClasses
  { classes     := dedup (allTypeNames.filter (fun c => !ty.isDatatype c))
    objectProps := dedup ty.objectProps
    dataProps   := dedup ty.dataProps
    datatypes   := dedup (ty.datatypes ++ litTypes ++ allTypeNames.filter ty.isDatatype)
    iris        := dedup (ty.classes ++ ty.objectProps ++ ty.dataProps ++
                          rd.axioms.flatMap axiomIris ++ docIris)
    literals    := lits.foldl (fun acc g => if acc.contains g then acc else acc ++ [g]) [] }

/-- ROWL-Direct(V,R), rows (i)-(viii) and (x). Row (ix) is replaced
    by the `doesNotHold` precondition described in the module header,
    and row (xi) by reading `rif:error` as inconsistency. -/
def rowlDirect (v : Vocab) : List Rule :=
  -- (i) owl:Nothing is empty.
  [{ vars := ["x"], head := errorAtom, body := some (.atom (typeAtom vx owlNothing)) },
  -- (ii) the object and data domains are disjoint.
   { vars := ["x"], head := errorAtom,
     body := some (.and [.atom (typeAtom vx rdfsLiteral), .atom (typeAtom vx owlThing)]) }] ++
  -- (iii) every member of a class is an individual.
  (v.classes.filter (· != owlThing)).map (fun c =>
    { vars := ["x"], head := typeAtom vx owlThing, body := some (.atom (typeAtom vx c)) }) ++
  -- (iv) the subject of any property is an individual.
  (v.objectProps ++ v.dataProps).map (fun p =>
    { vars := ["x", "y"], head := typeAtom vx owlThing, body := some (.atom (propAtom vx p vy)) }) ++
  -- (v) the value of an object property is an individual.
  v.objectProps.map (fun p =>
    { vars := ["x", "y"], head := typeAtom vy owlThing, body := some (.atom (propAtom vx p vy)) }) ++
  -- (vi) the value of a data property is a data value.
  v.dataProps.map (fun p =>
    { vars := ["x", "y"], head := typeAtom vy rdfsLiteral, body := some (.atom (propAtom vx p vy)) }) ++
  -- (vii) every IRI of V names an individual.
  v.iris.map (fun i => { head := typeAtom (cI i) owlThing }) ++
  -- (viii) for the literal's own datatype.
  (v.literals.filter ownDatatypeMember).filterMap (fun g => match g with
    | .const _ sp => some { head := typeAtom (tmOfG g) sp }
    | _ => none) ++
  -- (x) every datatype is contained in rdfs:Literal.
  (v.datatypes.filter (· != rdfsLiteral)).map (fun d =>
    { vars := ["x"], head := typeAtom vx rdfsLiteral, body := some (.atom (typeAtom vx d)) })

/-! ## The verdict -/

/-- The (ii) disjointness applied to the closure itself: a constant of
    a known datatype typed `owl:Thing`. -/
def dataValueAsIndividual (ty : Typing) (fs : Facts) : Bool :=
  fs.any (fun f => match f with
    | .frame o (.const p _) (.const c _) => p == rdfTypeIri && c == owlThing && isDataValue ty o
    | _ => false)

def errorDerived (fs : Facts) : Bool :=
  fs.any (fun f => match f with
    | .pos fn sp [] => fn == rifError && sp == iriSpace
    | _ => false)

/-- Every constant in the closure facts. -/
def factConsts : GAtom → List GTerm
  | .pos _ _ args => args
  | .frame o p v  => [o, p, v]
  | .member o c   => [o, c]
  | .sub c d      => [c, d]

/-- Describe a triple for an `undecided` message. -/
def showTerm : Term → String
  | .iri i => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal l => "\"" ++ l.val.lexicalForm ++ "\""
  | .tripleTerm _ _ _ => "<<triple term>>"

def showTriple (t : Triple) : String :=
  (match t.s with | .iri i => "<" ++ i.val ++ ">" | .bnode b => "_:" ++ b) ++
  " <" ++ t.p.val ++ "> " ++ showTerm t.o

/-- RIF-OWL Direct-entailment of `goal` by the combination of `rules`
    (the premise, local constants already qualified) with the OWL 2 DL
    ontology whose RDF representation is `g` (RIF-RDF-OWL §4.2.2,
    §5.2, decided through §9.2). See the module header for which
    verdicts are given when. -/
def entailsOwlDirect (rules : List Rule) (g : Graph) (goal : Formula) (rounds : Nat)
    : Verdict :=
  -- §5.2: under a DL profile a premise that is not a DL-document
  -- formula must be rejected, so there is no combination to ask.
  if !(rules.all dlRuleOk) then
    .undecided "the premise is not a RIF-BLD DL-document formula (RIF-RDF-OWL §4.1, §5.2)"
  else if !(dlFormula goal) then
    .undecided "the conclusion is not a DL-condition (RIF-RDF-OWL §4.1)"
  else
  let rd := readOntology g
  let ty := rd.typing
  let rules' := rules.map dlRule
  let goal' := memberAsFrame goal
  let v := vocabOf rd rules' goal'
  let ontologyRules := rd.axioms.flatMap rulesOfAxiom
  let program := rules' ++ ontologyRules ++ rowlDirect v
  let (fs, blocked, capped) := closure program [] rounds
  if errorDerived fs || dataValueAsIndividual ty fs then .holds
  else
    let (ss, gblocked) := matchFormula fs [] goal'
    if !ss.isEmpty then .holds
    else if blocked || gblocked then
      .undecided "a built-in outside this port's slice blocked a rule or the goal"
    else if capped then .undecided "the forward chain reached its round bound"
    else
      match rd.outside with
      | (t, why) :: rest =>
          .undecided s!"the imported ontology has {rest.length + 1} triples outside the embedded OWL 2 RL subset; first: {showTriple t} — {why}"
      | [] =>
        let typeClasses := rules'.flatMap typeClassesOfRule ++ typeClassesOfFormula goal' ++
                           ontologyRules.flatMap typeClassesOfRule
        if typeClasses.any ty.isDatatype then
          .undecided "a datatype is used as a class; ROWL-Direct (viii)/(ix) are implemented for a literal's own datatype only"
        else if (fs.flatMap factConsts).any (isUnknownLiteral ty) then
          .undecided "a literal of a datatype the combination does not know is in the closure"
        else .doesNotHold

end L4Factoidal.RIF.OwlDirect
