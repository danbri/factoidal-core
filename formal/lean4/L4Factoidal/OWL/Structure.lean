/-
L4Factoidal.OWL.Structure — the OWL 2 structural specification as data.

Spec: OWL 2 Web Ontology Language Structural Specification and
Functional-Style Syntax (Second Edition),
https://www.w3.org/TR/owl2-syntax/ — sections 2 to 10 give the
constructs, section 3 the ontology, section 10 the annotations.

The types follow the abstract syntax of the specification, not any one
concrete syntax: the functional-style parser
(`L4Factoidal.OWL.FunctionalSyntax`) produces `Ontology`, and the
mapping to RDF graphs (`L4Factoidal.OWL.StructureRdf`, OWL 2 Mapping to
RDF Graphs section 2) consumes it. An OWL/XML reader (OWL 2 XML
Serialization) would produce the same type, so the two syntaxes are
compared as structures and as RDF graphs from one definition.

The type carries no side conditions. The typing constraints of
Structural Specification section 5.8.1 (an IRI used as both a class and
a datatype) and the global restrictions of section 11 are decided over
the RDF graph of a structure by `L4Factoidal.OWL.SyntaxDL`.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.OWL.Struct

open L4Factoidal.RDF

/-! ## Individuals, property expressions, data ranges -/

/-- Structural Specification section 5.6: a named individual is an
IRI; an anonymous individual is a node ID (`_:label`). -/
inductive Individual where
  | named (i : WfIri)
  | anon  (label : String)

/-- Section 6.1: an object property, or the inverse of one. -/
inductive ObjPropExpr where
  | prop    (p : WfIri)
  | inverse (p : WfIri)

/-- Section 7: data ranges. A datatype is an IRI. -/
inductive DataRange where
  | datatype     (dt : WfIri)
  | intersection (drs : List DataRange)
  | union        (drs : List DataRange)
  | complement   (dr : DataRange)
  | oneOf        (lits : List WfLiteral)
  /-- `DatatypeRestriction( DT F1 lt1 ... Fn ltn )`. -/
  | restriction  (dt : WfIri) (facets : List (WfIri × WfLiteral))

/-! ## Class expressions — section 8 -/

inductive ClassExpr where
  | cls          (c : WfIri)
  | intersection (ces : List ClassExpr)
  | union        (ces : List ClassExpr)
  | complement   (ce : ClassExpr)
  | oneOf        (inds : List Individual)
  | someValuesFrom (ope : ObjPropExpr) (ce : ClassExpr)
  | allValuesFrom  (ope : ObjPropExpr) (ce : ClassExpr)
  | hasValue       (ope : ObjPropExpr) (ind : Individual)
  | hasSelf        (ope : ObjPropExpr)
  /-- `ObjectMinCardinality( n OPE [CE] )`; `none` is the unqualified form. -/
  | minCard   (n : Nat) (ope : ObjPropExpr) (ce : Option ClassExpr)
  | maxCard   (n : Nat) (ope : ObjPropExpr) (ce : Option ClassExpr)
  | exactCard (n : Nat) (ope : ObjPropExpr) (ce : Option ClassExpr)
  /-- `DataSomeValuesFrom( DPE1 ... DPEn DR )`; n may exceed one. -/
  | dataSomeValuesFrom (dpes : List WfIri) (dr : DataRange)
  | dataAllValuesFrom  (dpes : List WfIri) (dr : DataRange)
  | dataHasValue       (dp : WfIri) (lit : WfLiteral)
  | dataMinCard   (n : Nat) (dp : WfIri) (dr : Option DataRange)
  | dataMaxCard   (n : Nat) (dp : WfIri) (dr : Option DataRange)
  | dataExactCard (n : Nat) (dp : WfIri) (dr : Option DataRange)

/-! ## Annotations — section 10 -/

/-- An annotation value: an IRI, an anonymous individual or a literal. -/
inductive AnnValue where
  | iri  (i : WfIri)
  | anon (label : String)
  | lit  (l : WfLiteral)

/-- `Annotation( annotationAnnotations AP av )`: the annotations OF the
annotation come first. -/
inductive Annotation where
  | mk (anns : List Annotation) (prop : WfIri) (value : AnnValue)

/-! ## Axioms — sections 9 and 10 -/

/-- The entity kinds a declaration introduces (section 5.8). -/
inductive EntityKind where
  | cls | datatype | objectProperty | dataProperty | annotationProperty
  | namedIndividual
deriving DecidableEq

/-- The seven characteristics of an object property (section 9.2). -/
inductive ObjPropChar where
  | functional | inverseFunctional | reflexive | irreflexive
  | symmetric | asymmetric | transitive
deriving DecidableEq

/-- The sub-property side of `SubObjectPropertyOf`. -/
inductive SubObjProp where
  | single (ope : ObjPropExpr)
  | chain  (opes : List ObjPropExpr)

/-- Every axiom carries the annotations written inside it (the
`axiomAnnotations` production). -/
inductive Axiom where
  | declaration (anns : List Annotation) (kind : EntityKind) (iri : WfIri)
  | subClassOf (anns : List Annotation) (sub sup : ClassExpr)
  | equivalentClasses (anns : List Annotation) (ces : List ClassExpr)
  | disjointClasses (anns : List Annotation) (ces : List ClassExpr)
  | disjointUnion (anns : List Annotation) (c : WfIri) (ces : List ClassExpr)
  | subObjectPropertyOf (anns : List Annotation) (sub : SubObjProp) (sup : ObjPropExpr)
  | equivalentObjectProperties (anns : List Annotation) (opes : List ObjPropExpr)
  | disjointObjectProperties (anns : List Annotation) (opes : List ObjPropExpr)
  | inverseObjectProperties (anns : List Annotation) (a b : ObjPropExpr)
  | objectPropertyDomain (anns : List Annotation) (ope : ObjPropExpr) (ce : ClassExpr)
  | objectPropertyRange (anns : List Annotation) (ope : ObjPropExpr) (ce : ClassExpr)
  | objectPropertyCharacteristic (anns : List Annotation) (ch : ObjPropChar)
      (ope : ObjPropExpr)
  | subDataPropertyOf (anns : List Annotation) (sub sup : WfIri)
  | equivalentDataProperties (anns : List Annotation) (dps : List WfIri)
  | disjointDataProperties (anns : List Annotation) (dps : List WfIri)
  | dataPropertyDomain (anns : List Annotation) (dp : WfIri) (ce : ClassExpr)
  | dataPropertyRange (anns : List Annotation) (dp : WfIri) (dr : DataRange)
  | functionalDataProperty (anns : List Annotation) (dp : WfIri)
  | datatypeDefinition (anns : List Annotation) (dt : WfIri) (dr : DataRange)
  | hasKey (anns : List Annotation) (ce : ClassExpr) (opes : List ObjPropExpr)
      (dps : List WfIri)
  | sameIndividual (anns : List Annotation) (inds : List Individual)
  | differentIndividuals (anns : List Annotation) (inds : List Individual)
  | classAssertion (anns : List Annotation) (ce : ClassExpr) (ind : Individual)
  | objectPropertyAssertion (anns : List Annotation) (ope : ObjPropExpr)
      (src tgt : Individual)
  | negativeObjectPropertyAssertion (anns : List Annotation) (ope : ObjPropExpr)
      (src tgt : Individual)
  | dataPropertyAssertion (anns : List Annotation) (dp : WfIri) (src : Individual)
      (lit : WfLiteral)
  | negativeDataPropertyAssertion (anns : List Annotation) (dp : WfIri)
      (src : Individual) (lit : WfLiteral)
  /-- The subject of an annotation assertion is an IRI or an anonymous
  individual (`AnnotationSubject`, section 10.2.1). -/
  | annotationAssertion (anns : List Annotation) (prop : WfIri)
      (subject : Individual) (value : AnnValue)
  | subAnnotationPropertyOf (anns : List Annotation) (sub sup : WfIri)
  | annotationPropertyDomain (anns : List Annotation) (prop : WfIri) (dom : WfIri)
  | annotationPropertyRange (anns : List Annotation) (prop : WfIri) (rng : WfIri)

/-! ## The ontology — section 3 -/

structure Ontology where
  /-- `Ontology( [ ontologyIRI [ versionIRI ] ] ...`; a version IRI
  requires an ontology IRI (section 3.1). -/
  iri         : Option WfIri := none
  versionIri  : Option WfIri := none
  /-- `Import( IRI )`. -/
  imports     : List WfIri := []
  annotations : List Annotation := []
  axioms      : List Axiom := []

end L4Factoidal.OWL.Struct
