/-
Restricted RDF-to-Direct mapping with a proved source-model bridge.

Scope: named atomic classes, Thing/Nothing, SubClassOf, class assertions,
SameIndividual/DifferentIndividuals, ObjectSomeValuesFrom(p C) with p an object
property IRI and C an atomic class, used as the super-class of SubClassOf or as
the class of a ClassAssertion, TransitiveObjectProperty(p), and the
declarations/annotations below: the nine built-in annotation properties
(Structural Specification section 5.5), declared annotation properties on IRIs
and blank nodes, SubAnnotationPropertyOf, annotated axioms (Mapping section
3.2.5, Table 17) and `owl:versionIRI` in the ontology header.
OWL 2 Mapping to RDF Graphs (2012), Tables 7, 13 and 16 and section 3.2.2 supply the syntax;
Direct Semantics (2012), Tables 4, 5 and 10 supply the logical conditions.
Annotations have no logical effect (Direct Semantics section 1).

Two readings are wider than the Mapping (https://github.com/danbri/factoidal/issues/960):
the `_:x rdf:type owl:Restriction` triple of Table 13 is optional, and the
property of `owl:onProperty` needs no `owl:ObjectProperty` declaration (the reader
admits no data property, so the only reading of the restriction is the object
one). The reader refuses a restriction node that has more than one
`owl:onProperty` or `owl:someValuesFrom` triple, or none of either, and an IRI
that is both an annotation property and an object property
(`restrictionsWellFormed`).

MapsTo and axiomHolds state the scoped source contract independently of the
reader and compiler. This is not all OWL, an imports processor, RDF-Based
Semantics, or a proof about the existing public API. Unsupported syntax is
rejected for the whole supplied Graph; there is no dataset projection.
-/
import L4Factoidal.OWL.CertifiedDecision
import L4Factoidal.RDF.Graph

namespace L4Factoidal.OWL.AtomicDirect

open L4Factoidal.RDF

def rdfType : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
def subClassOf : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#subClassOf", rfl⟩
def domain : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#domain", rfl⟩
def range : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#range", rfl⟩
def owlClass : WfIri := ⟨"http://www.w3.org/2002/07/owl#Class", rfl⟩
def owlThing : WfIri := ⟨"http://www.w3.org/2002/07/owl#Thing", rfl⟩
def owlNothing : WfIri := ⟨"http://www.w3.org/2002/07/owl#Nothing", rfl⟩
def owlOntology : WfIri := ⟨"http://www.w3.org/2002/07/owl#Ontology", rfl⟩
def owlNamedIndividual : WfIri := ⟨"http://www.w3.org/2002/07/owl#NamedIndividual", rfl⟩
def owlAnnotationProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#AnnotationProperty", rfl⟩
def sameAs : WfIri := ⟨"http://www.w3.org/2002/07/owl#sameAs", rfl⟩
def differentFrom : WfIri := ⟨"http://www.w3.org/2002/07/owl#differentFrom", rfl⟩
def owlRestriction : WfIri := ⟨"http://www.w3.org/2002/07/owl#Restriction", rfl⟩
def owlObjectProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#ObjectProperty", rfl⟩
def onProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#onProperty", rfl⟩
def someValuesFrom : WfIri := ⟨"http://www.w3.org/2002/07/owl#someValuesFrom", rfl⟩
def owlTransitiveProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#TransitiveProperty", rfl⟩
def owlAxiom : WfIri := ⟨"http://www.w3.org/2002/07/owl#Axiom", rfl⟩
def annotatedSource : WfIri := ⟨"http://www.w3.org/2002/07/owl#annotatedSource", rfl⟩
def annotatedProperty : WfIri := ⟨"http://www.w3.org/2002/07/owl#annotatedProperty", rfl⟩
def annotatedTarget : WfIri := ⟨"http://www.w3.org/2002/07/owl#annotatedTarget", rfl⟩
def owlVersionIRI : WfIri := ⟨"http://www.w3.org/2002/07/owl#versionIRI", rfl⟩
def subPropertyOf : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#subPropertyOf", rfl⟩

def reserved (name : WfIri) : Bool :=
  name.val.startsWith "http://www.w3.org/2002/07/owl#" ||
  name.val.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
  name.val.startsWith "http://www.w3.org/2000/01/rdf-schema#" ||
  name.val.startsWith "http://www.w3.org/2001/XMLSchema#"

/-- The built-in annotation properties of the OWL 2 Structural Specification
section 5.5 (all nine). -/
def builtinAnnotationName (name : String) : Bool :=
  name == "http://www.w3.org/2000/01/rdf-schema#label" ||
  name == "http://www.w3.org/2000/01/rdf-schema#comment" ||
  name == "http://www.w3.org/2000/01/rdf-schema#seeAlso" ||
  name == "http://www.w3.org/2000/01/rdf-schema#isDefinedBy" ||
  name == "http://www.w3.org/2002/07/owl#deprecated" ||
  name == "http://www.w3.org/2002/07/owl#versionInfo" ||
  name == "http://www.w3.org/2002/07/owl#priorVersion" ||
  name == "http://www.w3.org/2002/07/owl#backwardCompatibleWith" ||
  name == "http://www.w3.org/2002/07/owl#incompatibleWith"

def builtinAnnotation (name : WfIri) : Bool := builtinAnnotationName name.val

def validAnnotationName (name : WfIri) : Bool := builtinAnnotation name || !reserved name

/-- Declarative source vocabulary, stated by membership in the original graph. -/
def AnnotationProperty (graph : Graph) (name : WfIri) : Prop :=
  builtinAnnotation name = true ∨ ∃ triple ∈ graph,
    triple = ⟨.iri name, rdfType, .iri owlAnnotationProperty⟩ ∧ validAnnotationName name = true

/-- The declared annotation properties of a graph, each with the proof of its
declaration. One pass; a lookup is one hash probe (until 2026-10-24 each
lookup scanned the graph, so reading was quadratic in the annotation triples;
issue 960 item 5). -/
abbrev AnnotationIndex (graph : Graph) := Std.HashMap String {name : WfIri // AnnotationProperty graph name}

def annotationIndex (graph : Graph) : AnnotationIndex graph :=
  graph.attach.foldl (fun index entry => match entry with
    | ⟨⟨.iri name, predicate, .iri value⟩, member⟩ =>
      if declared : predicate = rdfType ∧ value = owlAnnotationProperty ∧
          validAnnotationName name = true then
        index.insert name.val ⟨name, Or.inr ⟨_, member, by
          obtain ⟨rfl, rfl, _⟩ := declared; rfl, declared.2.2⟩⟩
      else index
    | _ => index) {}

/-- Declaration order independent lookup; every answer carries its proof. -/
def knownAnnotation (graph : Graph) (index : AnnotationIndex graph) (name : WfIri) :
    Option (PLift (AnnotationProperty graph name)) :=
  if builtin : builtinAnnotation name = true then some ⟨Or.inl builtin⟩
  -- A reserved name other than a built-in is never a declared annotation
  -- property (`validAnnotationName`); answering before the hash probe also
  -- keeps the lookup reducible by `decide` for such names.
  else if reserved name then none
  else match index.get? name.val with
    | some ⟨found, known⟩ => if same : found = name then some ⟨same ▸ known⟩ else none
    | none => none

def annotationValue (value : Term) : Bool :=
  match value with
  | .iri _ | .bnode _ => true
  | .literal literal => literal.val.direction.isNone
  | .tripleTerm _ _ _ => false

inductive AtomicClass where
  | named (name : String)
  | thing
  | nothing
  deriving Repr, DecidableEq

/-- An independent name-to-class mapping relation; user prefixes have no special meaning. -/
inductive MapsClass : WfIri → AtomicClass → Prop where
  | thing : MapsClass owlThing .thing
  | nothing : MapsClass owlNothing .nothing
  | named (name : WfIri) (ordinary : reserved name = false) : MapsClass name (.named name.val)

inductive Axiom where
  | noEffect
  | subClass (left right : AtomicClass)
  | classAssertion (individual : String) (className : AtomicClass)
  | same (left right : String)
  | different (left right : String)
  /-- `SubClassOf(left ObjectSomeValuesFrom(role filler))`. -/
  | subClassSome (left : AtomicClass) (role : String) (filler : AtomicClass)
  /-- `ClassAssertion(ObjectSomeValuesFrom(role filler) individual)`. -/
  | assertSome (individual : String) (role : String) (filler : AtomicClass)
  /-- `TransitiveObjectProperty(role)`. -/
  | transitive (role : String)
  deriving Repr, DecidableEq

/-- Logical interpretation of structural axioms, independently of their compilation. -/
def classHolds {δ : Type} (interpretation : Interp δ) : AtomicClass → δ → Prop
  | .named name, element => interpretation.concept name element
  | .thing, _ => True
  | .nothing, _ => False

def axiomHolds {δ : Type} (interpretation : Interp δ) (assignment : Ind → δ) : Axiom → Prop
  | .noEffect => True
  | .subClass left right => ∀ element,
      classHolds interpretation left element → classHolds interpretation right element
  | .classAssertion individual className => classHolds interpretation className (assignment individual)
  | .same left right => assignment left = assignment right
  | .different left right => assignment left ≠ assignment right
  | .subClassSome left role filler => ∀ element,
      classHolds interpretation left element →
        ∃ successor, interpretation.role role element successor ∧
          classHolds interpretation filler successor
  | .assertSome individual role filler =>
      ∃ successor, interpretation.role role (assignment individual) successor ∧
        classHolds interpretation filler successor
  | .transitive role => ∀ x y z,
      interpretation.role role x y → interpretation.role role y z → interpretation.role role x z

/-- Scoped RDF mapping rules. None of these rules mentions the reader or compiler. -/
inductive MapsTo (graph : Graph) : Triple → Axiom → Prop where
  | classDeclaration (name : WfIri) (className : AtomicClass) (mapped : MapsClass name className) :
      MapsTo graph ⟨.iri name, rdfType, .iri owlClass⟩ .noEffect
  | namedIndividual (name : WfIri) (ordinary : reserved name = false) :
      MapsTo graph ⟨.iri name, rdfType, .iri owlNamedIndividual⟩ .noEffect
  | ontologyHeader (subject : Subject) :
      MapsTo graph ⟨subject, rdfType, .iri owlOntology⟩ .noEffect
  | annotationDeclaration (name : WfIri) (valid : validAnnotationName name = true) :
      MapsTo graph ⟨.iri name, rdfType, .iri owlAnnotationProperty⟩ .noEffect
  | subClass (left right : WfIri) (leftClass rightClass : AtomicClass)
      (mappedLeft : MapsClass left leftClass) (mappedRight : MapsClass right rightClass) :
      MapsTo graph ⟨.iri left, subClassOf, .iri right⟩ (.subClass leftClass rightClass)
  | classAssertion (individual name : WfIri) (className : AtomicClass)
      (ordinary : reserved individual = false) (mapped : MapsClass name className) :
      MapsTo graph ⟨.iri individual, rdfType, .iri name⟩ (.classAssertion individual.val className)
  | same (left right : WfIri) (leftOrdinary : reserved left = false) (rightOrdinary : reserved right = false) :
      MapsTo graph ⟨.iri left, sameAs, .iri right⟩ (.same left.val right.val)
  | different (left right : WfIri) (leftOrdinary : reserved left = false) (rightOrdinary : reserved right = false) :
      MapsTo graph ⟨.iri left, differentFrom, .iri right⟩ (.different left.val right.val)
  | annotation (subject property : WfIri) (value : Term)
      (known : AnnotationProperty graph property) (allowed : annotationValue value = true) :
      MapsTo graph ⟨.iri subject, property, value⟩ .noEffect
  | annotationDomain (property target : WfIri) (known : AnnotationProperty graph property) :
      MapsTo graph ⟨.iri property, domain, .iri target⟩ .noEffect
  | annotationRange (property target : WfIri) (known : AnnotationProperty graph property) :
      MapsTo graph ⟨.iri property, range, .iri target⟩ .noEffect
  | objectPropertyDeclaration (name : WfIri) (ordinary : reserved name = false) :
      MapsTo graph ⟨.iri name, rdfType, .iri owlObjectProperty⟩ .noEffect
  /-- The triples of a restriction node have no effect of their own; the
  triple that uses the node carries the axiom (Mapping Table 13). -/
  | restrictionType (node : BNodeId) :
      MapsTo graph ⟨.bnode node, rdfType, .iri owlRestriction⟩ .noEffect
  | restrictionProperty (node : BNodeId) (property : WfIri) (ordinary : reserved property = false) :
      MapsTo graph ⟨.bnode node, onProperty, .iri property⟩ .noEffect
  | restrictionFiller (node : BNodeId) (filler : WfIri) (fillerClass : AtomicClass)
      (mapped : MapsClass filler fillerClass) :
      MapsTo graph ⟨.bnode node, someValuesFrom, .iri filler⟩ .noEffect
  /-- `left rdfs:subClassOf _:x` with `_:x owl:onProperty p` and
  `_:x owl:someValuesFrom C` in the graph. A node with several such triples
  gives one axiom for each pair; the reader refuses that graph. -/
  | subClassSome (left : WfIri) (node : BNodeId) (leftClass : AtomicClass)
      (property filler : WfIri) (fillerClass : AtomicClass)
      (mappedLeft : MapsClass left leftClass) (ordinary : reserved property = false)
      (propertyTriple : ⟨.bnode node, onProperty, .iri property⟩ ∈ graph)
      (fillerTriple : ⟨.bnode node, someValuesFrom, .iri filler⟩ ∈ graph)
      (mappedFiller : MapsClass filler fillerClass) :
      MapsTo graph ⟨.iri left, subClassOf, .bnode node⟩
        (.subClassSome leftClass property.val fillerClass)
  | assertSome (individual : WfIri) (node : BNodeId) (property filler : WfIri)
      (fillerClass : AtomicClass) (individualOrdinary : reserved individual = false)
      (ordinary : reserved property = false)
      (propertyTriple : ⟨.bnode node, onProperty, .iri property⟩ ∈ graph)
      (fillerTriple : ⟨.bnode node, someValuesFrom, .iri filler⟩ ∈ graph)
      (mappedFiller : MapsClass filler fillerClass) :
      MapsTo graph ⟨.iri individual, rdfType, .bnode node⟩
        (.assertSome individual.val property.val fillerClass)
  /-- `TransitiveObjectProperty(p)` (Mapping Table 16; Direct Semantics
  Table 6). As for `owl:onProperty`, the property needs no
  `owl:ObjectProperty` declaration: the reader admits no data property. -/
  | transitive (name : WfIri) (ordinary : reserved name = false) :
      MapsTo graph ⟨.iri name, rdfType, .iri owlTransitiveProperty⟩ (.transitive name.val)
  /-- `SubAnnotationPropertyOf(p q)` (Mapping Table 16): no logical effect. -/
  | subAnnotation (left right : WfIri) (knownLeft : AnnotationProperty graph left)
      (knownRight : AnnotationProperty graph right) :
      MapsTo graph ⟨.iri left, subPropertyOf, .iri right⟩ .noEffect
  /-- The version IRI of the ontology header (Mapping Table 4). -/
  | versionIRI (subject : Subject) (version : WfIri) :
      MapsTo graph ⟨subject, owlVersionIRI, .iri version⟩ .noEffect
  /-- The triples of an annotated axiom's `owl:Axiom` node (Mapping section
  3.2.5, Table 17): the axiom itself is its own triple; annotations have no
  logical effect (Direct Semantics section 1). -/
  | axiomNode (node : BNodeId) :
      MapsTo graph ⟨.bnode node, rdfType, .iri owlAxiom⟩ .noEffect
  | axiomPart (node : BNodeId) (predicate : WfIri) (value : Term)
      (part : predicate = annotatedSource ∨ predicate = annotatedProperty ∨
        predicate = annotatedTarget) :
      MapsTo graph ⟨.bnode node, predicate, value⟩ .noEffect
  /-- An annotation of a blank node: of an `owl:Axiom` node (Table 17), or an
  annotation assertion about an anonymous individual (Table 16). -/
  | blankAnnotation (node : BNodeId) (property : WfIri) (value : Term)
      (known : AnnotationProperty graph property) (allowed : annotationValue value = true) :
      MapsTo graph ⟨.bnode node, property, value⟩ .noEffect

/-- Every structurally mapped axiom in the original graph holds in this interpretation. -/
def SourceModel {δ : Type} (interpretation : Interp δ) (assignment : Ind → δ)
    (graph : Graph) : Prop :=
  ∀ triple ∈ graph, ∀ clause, MapsTo graph triple clause → axiomHolds interpretation assignment clause

def Satisfiable (graph : Graph) : Prop :=
  ∃ (δ : Type) (interpretation : Interp δ) (assignment : Ind → δ),
    SourceModel interpretation assignment graph

def readClass (name : WfIri) : Option {className // MapsClass name className} :=
  if isThing : name = owlThing then
    some ⟨.thing, isThing ▸ MapsClass.thing⟩
  else if isNothing : name = owlNothing then
    some ⟨.nothing, isNothing ▸ MapsClass.nothing⟩
  else if ordinary : reserved name = false then
    some ⟨.named name.val, .named name ordinary⟩
  else none

/-- The triples of each blank-node subject, each with its membership proof.
Lookups need no lemma about the hash map: every value carries its proof. -/
abbrev NodeIndex (graph : Graph) := Std.HashMap BNodeId (List {triple : Triple // triple ∈ graph})

/-- One pass over the graph. -/
def nodeIndex (graph : Graph) : NodeIndex graph :=
  graph.attach.foldl (fun index entry => match entry.val.s with
    | .bnode node => index.insert node (entry :: index.getD node [])
    | .iri _ => index) {}

/-- An `owl:onProperty` value of a restriction node, with its membership proof. -/
def findProperty (graph : Graph) (index : NodeIndex graph) (node : BNodeId) :
    Option {property : WfIri //
      (⟨.bnode node, onProperty, .iri property⟩ : Triple) ∈ graph ∧ reserved property = false} :=
  (index.getD node []).findSome? fun entry =>
    match entry with
    | ⟨⟨.bnode other, predicate, .iri property⟩, member⟩ =>
      if found : other = node ∧ predicate = onProperty ∧ reserved property = false then
        some ⟨property, by
          obtain ⟨rfl, rfl, ordinary⟩ := found
          exact ⟨member, ordinary⟩⟩
      else none
    | _ => none

/-- An `owl:someValuesFrom` value of a restriction node, read as a class. -/
def findFiller (graph : Graph) (index : NodeIndex graph) (node : BNodeId) :
    Option {pair : WfIri × AtomicClass //
      (⟨.bnode node, someValuesFrom, .iri pair.1⟩ : Triple) ∈ graph ∧ MapsClass pair.1 pair.2} :=
  (index.getD node []).findSome? fun entry =>
    match entry with
    | ⟨⟨.bnode other, predicate, .iri filler⟩, member⟩ =>
      if found : other = node ∧ predicate = someValuesFrom then
        match readClass filler with
        | some ⟨fillerClass, mapped⟩ =>
            some ⟨(filler, fillerClass), by
              obtain ⟨rfl, rfl⟩ := found
              exact ⟨member, mapped⟩⟩
        | none => none
      else none
    | _ => none

/-- Proof-bearing syntax decoding; no logical role is inferred without a source mapping rule. -/
def readTriple (graph : Graph) (index : NodeIndex graph) (annotations : AnnotationIndex graph) :
    (triple : Triple) → Option {clause // MapsTo graph triple clause}
  | ⟨subject, predicate, value⟩ =>
    if header : predicate = rdfType ∧ value = .iri owlOntology then
      some ⟨.noEffect, by rcases header with ⟨rfl, rfl⟩; exact .ontologyHeader subject⟩
    else if version : predicate = owlVersionIRI then
      match value with
      | .iri target => some ⟨.noEffect, by subst predicate; exact .versionIRI subject target⟩
      | _ => none
    else match subject with
    | .bnode node =>
      if restrictionTyped : predicate = rdfType ∧ value = .iri owlRestriction then
        some ⟨.noEffect, by rcases restrictionTyped with ⟨rfl, rfl⟩; exact .restrictionType node⟩
      else if propertyStatement : predicate = onProperty then
        match value with
        | .iri property =>
          if ordinary : reserved property = false then
            some ⟨.noEffect, by subst predicate; exact .restrictionProperty node property ordinary⟩
          else none
        | _ => none
      else if fillerStatement : predicate = someValuesFrom then
        match value with
        | .iri filler => do
          let ⟨fillerClass, mapped⟩ ← readClass filler
          pure ⟨.noEffect, by subst predicate; exact .restrictionFiller node filler fillerClass mapped⟩
        | _ => none
      else if axiomTyped : predicate = rdfType ∧ value = .iri owlAxiom then
        some ⟨.noEffect, by rcases axiomTyped with ⟨rfl, rfl⟩; exact .axiomNode node⟩
      else if part : predicate = annotatedSource ∨ predicate = annotatedProperty ∨
          predicate = annotatedTarget then
        some ⟨.noEffect, .axiomPart node predicate value part⟩
      else match knownAnnotation graph annotations predicate with
        | some ⟨known⟩ =>
          if allowed : annotationValue value = true then
            some ⟨.noEffect, .blankAnnotation node predicate value known allowed⟩
          else none
        | none => none
    | .iri name =>
      if typed : predicate = rdfType then
        if classDecl : value = .iri owlClass then do
          let ⟨className, mapped⟩ ← readClass name
          pure ⟨.noEffect, by subst predicate; subst value; exact .classDeclaration name className mapped⟩
        else if individualDecl : value = .iri owlNamedIndividual then
          if ordinary : reserved name = false then
            some ⟨.noEffect, by subst predicate; subst value; exact .namedIndividual name ordinary⟩
          else none
        else if annotationDecl : value = .iri owlAnnotationProperty then
          if valid : validAnnotationName name = true then
            some ⟨.noEffect, by subst predicate; subst value; exact .annotationDeclaration name valid⟩
          else none
        else if propertyDecl : value = .iri owlObjectProperty then
          if ordinary : reserved name = false then
            some ⟨.noEffect, by subst predicate; subst value; exact .objectPropertyDeclaration name ordinary⟩
          else none
        else if transitiveDecl : value = .iri owlTransitiveProperty then
          if ordinary : reserved name = false then
            some ⟨.transitive name.val, by subst predicate; subst value; exact .transitive name ordinary⟩
          else none
        else match value with
        | .iri classIri =>
          if ordinary : reserved name = false then do
            let ⟨className, mapped⟩ ← readClass classIri
            pure ⟨.classAssertion name.val className, by
              subst predicate; exact .classAssertion name classIri className ordinary mapped⟩
          else none
        | .bnode node =>
          if individualOrdinary : reserved name = false then do
            let ⟨property, propertyTriple, ordinary⟩ ← findProperty graph index node
            let ⟨⟨filler, fillerClass⟩, fillerTriple, mapped⟩ ← findFiller graph index node
            pure ⟨.assertSome name.val property.val fillerClass, by
              subst predicate
              exact .assertSome name node property filler fillerClass individualOrdinary ordinary
                propertyTriple fillerTriple mapped⟩
          else none
        | _ => none
      else if subclass : predicate = subClassOf then
        match value with
        | .iri target => do
          let ⟨leftClass, leftMapped⟩ ← readClass name
          let ⟨rightClass, rightMapped⟩ ← readClass target
          pure ⟨.subClass leftClass rightClass, by subst predicate; exact .subClass name target leftClass rightClass leftMapped rightMapped⟩
        | .bnode node => do
          let ⟨leftClass, leftMapped⟩ ← readClass name
          let ⟨property, propertyTriple, ordinary⟩ ← findProperty graph index node
          let ⟨⟨filler, fillerClass⟩, fillerTriple, mapped⟩ ← findFiller graph index node
          pure ⟨.subClassSome leftClass property.val fillerClass, by
            subst predicate
            exact .subClassSome name node leftClass property filler fillerClass leftMapped ordinary
              propertyTriple fillerTriple mapped⟩
        | _ => none
      else if same : predicate = sameAs then
        match value with
        | .iri target =>
          if leftOrdinary : reserved name = false then
            if rightOrdinary : reserved target = false then
              some ⟨.same name.val target.val, by subst predicate; exact .same name target leftOrdinary rightOrdinary⟩
            else none
          else none
        | _ => none
      else if different : predicate = differentFrom then
        match value with
        | .iri target =>
          if leftOrdinary : reserved name = false then
            if rightOrdinary : reserved target = false then
              some ⟨.different name.val target.val, by subst predicate; exact .different name target leftOrdinary rightOrdinary⟩
            else none
          else none
        | _ => none
      else if subProperty : predicate = subPropertyOf then
        match value with
        | .iri target =>
          match knownAnnotation graph annotations name, knownAnnotation graph annotations target with
          | some ⟨knownLeft⟩, some ⟨knownRight⟩ =>
            some ⟨.noEffect, by subst predicate; exact .subAnnotation name target knownLeft knownRight⟩
          | _, _ => none
        | _ => none
      else if domainStatement : predicate = domain then
        match value with
        | .iri target =>
          match knownAnnotation graph annotations name with
          | some ⟨known⟩ =>
            some ⟨.noEffect, by subst predicate; exact .annotationDomain name target known⟩
          | none => none
        | _ => none
      else if rangeStatement : predicate = range then
        match value with
        | .iri target =>
          match knownAnnotation graph annotations name with
          | some ⟨known⟩ =>
            some ⟨.noEffect, by subst predicate; exact .annotationRange name target known⟩
          | none => none
        | _ => none
      else match knownAnnotation graph annotations predicate with
        | some ⟨known⟩ =>
          if allowed : annotationValue value = true then
            some ⟨.noEffect, .annotation name predicate value known allowed⟩
          else none
        | none => none

abbrev MappedAxiom (graph : Graph) := {clause : Axiom // ∃ triple ∈ graph, MapsTo graph triple clause}

/-- List.mapM is total and tail based; one unsupported triple rejects the entire graph. -/
def readAxioms (graph : Graph) : Option (List (MappedAxiom graph)) :=
  let index := nodeIndex graph
  let annotations := annotationIndex graph
  graph.attach.mapM (fun ⟨triple, member⟩ => do
    let ⟨clause, mapped⟩ ← readTriple graph index annotations triple
    pure ⟨clause, triple, member, mapped⟩)

def compileClass : AtomicClass → Concept
  | .named name => .atom name
  | .thing => .top
  | .nothing => .bot

theorem compileClass_correct {δ : Type} (interpretation : Interp δ)
    (className : AtomicClass) (element : δ) :
    interpretation.sem (compileClass className) element ↔ classHolds interpretation className element := by
  cases className <;> rfl

def addAxiom (ontology : DlOntology) : Axiom → DlOntology
  | .noEffect => ontology
  | .subClass left right =>
      { ontology with tbox := (compileClass left, compileClass right) :: ontology.tbox }
  | .classAssertion individual className =>
      { ontology with abox := .inst individual (compileClass className) :: ontology.abox }
  | .same left right => { ontology with same := (left, right) :: ontology.same }
  | .different left right => { ontology with abox := .diff left right :: ontology.abox }
  | .subClassSome left role filler =>
      { ontology with tbox := (compileClass left, .ex role (compileClass filler)) :: ontology.tbox }
  | .assertSome individual role filler =>
      { ontology with abox := .inst individual (.ex role (compileClass filler)) :: ontology.abox }
  | .transitive role =>
      { ontology with rbox := { ontology.rbox with trans := role :: ontology.rbox.trans } }

theorem addAxiom_preserves_model {δ : Type} {interpretation : Interp δ} {assignment : Ind → δ}
    {ontology : DlOntology} (model : DirectModel interpretation assignment ontology)
    (clause : Axiom) (holds : axiomHolds interpretation assignment clause) :
    DirectModel interpretation assignment (addAxiom ontology clause) := by
  rcases model with ⟨roleBox, classBox, inverse, same, assertions⟩
  cases clause with
  | noEffect => exact ⟨roleBox, classBox, inverse, same, assertions⟩
  | subClass left right =>
      refine ⟨roleBox, ?_, inverse, same, assertions⟩
      intro pair member element hypothesis
      rcases List.mem_cons.mp member with head | tail
      · subst pair
        exact (compileClass_correct interpretation right element).mpr
          (holds element ((compileClass_correct interpretation left element).mp hypothesis))
      · exact classBox pair tail element hypothesis
  | classAssertion individual className =>
      refine ⟨roleBox, classBox, inverse, same, ?_⟩
      intro assertion member
      rcases List.mem_cons.mp member with head | tail
      · subst assertion
        exact (compileClass_correct interpretation className (assignment individual)).mpr holds
      · exact assertions assertion tail
  | same left right =>
      refine ⟨roleBox, classBox, inverse, ?_, assertions⟩
      intro pair member
      rcases List.mem_cons.mp member with head | tail
      · subst pair; exact holds
      · exact same pair tail
  | different left right =>
      refine ⟨roleBox, classBox, inverse, same, ?_⟩
      intro assertion member
      rcases List.mem_cons.mp member with head | tail
      · subst assertion; exact holds
      · exact assertions assertion tail
  | subClassSome left role filler =>
      refine ⟨roleBox, ?_, inverse, same, assertions⟩
      intro pair member element hypothesis
      rcases List.mem_cons.mp member with head | tail
      · subst pair
        obtain ⟨successor, edge, inFiller⟩ :=
          holds element ((compileClass_correct interpretation left element).mp hypothesis)
        exact ⟨successor, edge, (compileClass_correct interpretation filler successor).mpr inFiller⟩
      · exact classBox pair tail element hypothesis
  | assertSome individual role filler =>
      refine ⟨roleBox, classBox, inverse, same, ?_⟩
      intro assertion member
      rcases List.mem_cons.mp member with head | tail
      · subst assertion
        obtain ⟨successor, edge, inFiller⟩ := holds
        exact ⟨successor, edge, (compileClass_correct interpretation filler successor).mpr inFiller⟩
      · exact assertions assertion tail
  | transitive role =>
      refine ⟨⟨roleBox.1, ?_⟩, classBox, inverse, same, assertions⟩
      intro r member x y z first second
      rcases List.mem_cons.mp member with head | tail
      · subst r; exact holds x y z first second
      · exact roleBox.2 r tail x y z first second

/-- Universally true domain witness; its spelling requires no freshness assumption. -/
def initialOntology : DlOntology := { abox := [.inst "" .top] }

theorem initialOntology_model {δ : Type} (interpretation : Interp δ) (assignment : Ind → δ) :
    DirectModel interpretation assignment initialOntology := by
  refine ⟨respects_empty _, ?_, ?_, ?_, ?_⟩
  · intro _ absent; cases absent
  · intro _ absent; cases absent
  · intro _ absent; cases absent
  · intro assertion member
    have head := List.mem_singleton.mp member
    subst assertion
    exact True.intro

/-- Folding uses constant stack; logical clauses are added without normalization or closure. -/
def compileAxioms (clauses : List Axiom) : DlOntology := clauses.foldl addAxiom initialOntology

theorem compileAxioms_preserves_model {δ : Type} (interpretation : Interp δ)
    (assignment : Ind → δ) (clauses : List Axiom)
    (holds : ∀ clause ∈ clauses, axiomHolds interpretation assignment clause) :
    DirectModel interpretation assignment (compileAxioms clauses) := by
  have fold_preserves : ∀ (remaining : List Axiom) (ontology : DlOntology),
      DirectModel interpretation assignment ontology →
      (∀ clause ∈ remaining, axiomHolds interpretation assignment clause) →
      DirectModel interpretation assignment (remaining.foldl addAxiom ontology) := by
    intro remaining
    induction remaining with
    | nil => intro ontology model _; exact model
    | cons clause rest induction =>
        intro ontology model allHold
        exact induction (addAxiom ontology clause)
          (addAxiom_preserves_model model clause (allHold clause (List.Mem.head rest)))
          (fun next member => allHold next (List.Mem.tail clause member))
  exact fold_preserves clauses initialOntology (initialOntology_model interpretation assignment) holds

/-- Admission checks that are not needed for soundness, only for fidelity to
the Mapping (Table 13 and the OWL 2 DL typing restrictions): each restriction
node has exactly one `owl:onProperty` and one `owl:someValuesFrom` triple, and
no IRI is both an annotation property and an object property (declared, or
used by `owl:onProperty`). A refused graph is unsupported; it never changes a
verdict on an admitted graph. One pass with hash maps. -/
def restrictionsWellFormed (graph : Graph) : Bool :=
  let step := fun (state : Std.HashMap BNodeId (Nat × Nat) × Std.HashSet String ×
      Std.HashSet String) (triple : Triple) =>
    let (counts, objectProperties, annotations) := state
    match triple with
    | ⟨.bnode node, predicate, value⟩ =>
      let (properties, fillers) := counts.getD node (0, 0)
      if predicate.val == onProperty.val then
        let objectProperties := match value with
          | .iri property => objectProperties.insert property.val
          | _ => objectProperties
        (counts.insert node (properties + 1, fillers), objectProperties, annotations)
      else if predicate.val == someValuesFrom.val then
        (counts.insert node (properties, fillers + 1), objectProperties, annotations)
      else if predicate.val == rdfType.val && value == .iri owlRestriction then
        (counts.insert node (properties, fillers), objectProperties, annotations)
      else state
    | ⟨.iri name, predicate, value⟩ =>
      if predicate.val == rdfType.val &&
          (value == .iri owlObjectProperty || value == .iri owlTransitiveProperty) then
        (counts, objectProperties.insert name.val, annotations)
      else if predicate.val == rdfType.val && value == .iri owlAnnotationProperty then
        (counts, objectProperties, annotations.insert name.val)
      else state
  let (counts, objectProperties, annotations) :=
    graph.foldl step (({} : Std.HashMap BNodeId (Nat × Nat)), ({} : Std.HashSet String),
      ({} : Std.HashSet String))
  counts.toList.all (fun entry => entry.2 == (1, 1)) &&
  objectProperties.toList.all (fun name =>
    !annotations.contains name && !builtinAnnotationName name)

/-- Admission checks for the annotation syntax, not needed for soundness
(the triples involved map to `noEffect`), only for fidelity to the Mapping
(issue 960 item 5):
- an `owl:Axiom` node (section 3.2.5, Table 17) has exactly one
  `owl:annotatedSource`, `owl:annotatedProperty` and `owl:annotatedTarget`
  triple, its `rdf:type owl:Axiom` triple, and the annotated triple
  (source, property, target) is in the graph: a reified axiom without its
  axiom is not an OWL 2 ontology (a prefix that cut an axiom in half);
- a node with an `owl:annotatedSource`, `owl:annotatedProperty` or
  `owl:annotatedTarget` triple is an `owl:Axiom` node (checked above);
- a restriction node (with an `owl:onProperty`, `owl:someValuesFrom` or
  `rdf:type owl:Restriction` triple) has no other triple;
- the subject of an `owl:versionIRI` triple is typed `owl:Ontology`
  (Table 4).
One pass with hash maps, then one pass over the axiom nodes. -/
def annotationsWellFormed (graph : Graph) : Bool :=
  let isRestrictionTriple := fun (predicate : WfIri) (value : Term) =>
    predicate.val == onProperty.val || predicate.val == someValuesFrom.val ||
      (predicate.val == rdfType.val && value == .iri owlRestriction)
  -- Per blank node: typed owl:Axiom, its source, property and target values,
  -- whether it has restriction triples and whether it has other triples.
  let step := fun (state : Std.HashMap BNodeId (Bool × List Term × List Term × List Term × Bool × Bool) ×
      Std.HashSet Triple × Std.HashSet Subject × List Subject) (triple : Triple) =>
    let (nodes, triples, ontologies, versioned) := state
    let triples := triples.insert triple
    let ontologies :=
      if triple.p.val == rdfType.val && triple.o == .iri owlOntology then ontologies.insert triple.s
      else ontologies
    let versioned := if triple.p.val == owlVersionIRI.val then triple.s :: versioned else versioned
    match triple.s with
    | .bnode node =>
      let (typed, sources, properties, targets, restriction, other) :=
        nodes.getD node (false, [], [], [], false, false)
      let entry :=
        if triple.p.val == rdfType.val && triple.o == .iri owlAxiom then
          (true, sources, properties, targets, restriction, other)
        else if triple.p.val == annotatedSource.val then
          (typed, triple.o :: sources, properties, targets, restriction, other)
        else if triple.p.val == annotatedProperty.val then
          (typed, sources, triple.o :: properties, targets, restriction, other)
        else if triple.p.val == annotatedTarget.val then
          (typed, sources, properties, triple.o :: targets, restriction, other)
        else if isRestrictionTriple triple.p triple.o then
          (typed, sources, properties, targets, true, other)
        else (typed, sources, properties, targets, restriction, true)
      (nodes.insert node entry, triples, ontologies, versioned)
    | .iri _ => (nodes, triples, ontologies, versioned)
  let (nodes, triples, ontologies, versioned) :=
    graph.foldl step (({} : Std.HashMap BNodeId (Bool × List Term × List Term × List Term × Bool × Bool)),
      ({} : Std.HashSet Triple), ({} : Std.HashSet Subject), ([] : List Subject))
  let axiomOk := fun (entry : BNodeId × (Bool × List Term × List Term × List Term × Bool × Bool)) =>
    let (typed, sources, properties, targets, restriction, other) := entry.2
    let axiomNode := typed || !sources.isEmpty || !properties.isEmpty || !targets.isEmpty
    let restrictionOk := !restriction || (!axiomNode && !other)
    let reifiedOk := !axiomNode || match sources, properties, targets with
      | [source], [.iri property], [target] =>
        typed && match source with
          | .iri name => triples.contains ⟨.iri name, property, target⟩
          | .bnode name => triples.contains ⟨.bnode name, property, target⟩
          | _ => false
      | _, _, _ => false
    restrictionOk && reifiedOk
  nodes.toList.all axiomOk && versioned.all ontologies.contains

def readOntology (graph : Graph) : Option DlOntology := do
  let clauses ← readAxioms graph
  if restrictionsWellFormed graph && annotationsWellFormed graph then
    pure (compileAxioms (clauses.map Subtype.val))
  else none

/-- Admission is separate from source meaning. Unmapped triples must not
turn a vacuous partial SourceModel into a definitive supported verdict. -/
def Accepted (graph : Graph) : Prop := ∃ ontology, readOntology graph = some ontology

/-- Successful admission accounts for every original triple, not merely the emitted clauses. -/
theorem accepted_covers_triples {graph : Graph} (admitted : Accepted graph) :
    ∀ triple ∈ graph, ∃ clause, MapsTo graph triple clause := by
  have eachReturned : ∀ {α β : Type} (visit : α → Option β) (input : List α) (output : List β),
      input.mapM visit = some output →
      ∀ entry ∈ input, ∃ value, visit entry = some value := by
    intro α β visit input
    induction input with
    | nil => intro _ _ _ absent; cases absent
    | cons head tail induction =>
        intro output success entry member
        cases first : visit head with
        | none => simp [List.mapM_cons, first] at success
        | some value =>
            cases rest : tail.mapM visit with
            | none => simp [List.mapM_cons, first, rest] at success
            | some values =>
                rcases List.mem_cons.mp member with equal | inTail
                · subst entry; exact ⟨value, first⟩
                · exact induction values rest entry inTail
  obtain ⟨ontology, accepted⟩ := admitted
  cases parsed : readAxioms graph with
  | none => simp [readOntology, parsed] at accepted
  | some clauses =>
      let visit : {triple : Triple // triple ∈ graph} → Option (MappedAxiom graph) :=
        fun ⟨triple, member⟩ => do
          let ⟨clause, mapped⟩ ← readTriple graph (nodeIndex graph) (annotationIndex graph) triple
          pure ⟨clause, triple, member, mapped⟩
      have traversal : graph.attach.mapM visit = some clauses := by
        simpa only [readAxioms] using parsed
      intro triple member
      obtain ⟨_, returned⟩ := eachReturned visit graph.attach clauses traversal
        ⟨triple, member⟩ (List.mem_attach graph ⟨triple, member⟩)
      cases decoded : readTriple graph (nodeIndex graph) (annotationIndex graph) triple with
      | none => simp [visit, decoded] at returned
      | some mapped => exact ⟨mapped.val, mapped.property⟩

#print axioms accepted_covers_triples

/-- All accepted RDF inputs preserve each source model in the actual DirectModel predicate. -/
theorem readOntology_preserves_models {graph : Graph} {ontology : DlOntology} {δ : Type}
    {interpretation : Interp δ} {assignment : Ind → δ}
    (accepted : readOntology graph = some ontology)
    (model : SourceModel interpretation assignment graph) :
    DirectModel interpretation assignment ontology := by
  cases parsed : readAxioms graph with
  | none => simp [readOntology, parsed] at accepted
  | some clauses =>
      have compiled : compileAxioms (clauses.map Subtype.val) = ontology := by
        simp only [readOntology, parsed, Option.bind_eq_bind, Option.bind_some] at accepted
        split at accepted
        · simpa using accepted
        · cases accepted
      rw [← compiled]
      apply compileAxioms_preserves_model
      intro clause member
      obtain ⟨mapped, _, equal⟩ := List.mem_map.mp member
      obtain ⟨triple, inGraph, relation⟩ := mapped.property
      subst clause
      exact model triple inGraph mapped.val relation

theorem readOntology_hasModel {graph : Graph} {ontology : DlOntology}
    (accepted : readOntology graph = some ontology) (model : Satisfiable graph) :
    CertifiedDecision.HasModel ontology := by
  obtain ⟨δ, interpretation, assignment, source⟩ := model
  exact ⟨δ, interpretation, assignment, readOntology_preserves_models accepted source⟩

inductive CertifiedVerdict (graph : Graph) where
  | consistent (admitted : Accepted graph) (model : Satisfiable graph)
  | inconsistent (admitted : Accepted graph) (noModel : ¬ Satisfiable graph)
  | unknown (reason : CertifiedDecision.UnknownReason)

/-- The actual producer checks an untrusted certificate against the proved reader's result. -/
def checkedRefutation (graph : Graph) (certificate : Cert) : CertifiedVerdict graph :=
  match reading : readOntology graph with
  | none => .unknown .unsupported
  | some ontology =>
      if accepted : checkCert ontology certificate = true then
        .inconsistent ⟨ontology, reading⟩
          (fun model => checkCert_sound accepted (readOntology_hasModel reading model))
      else .unknown .certificateRejected

def erase {graph : Graph} : CertifiedVerdict graph → CertifiedDecision.WireVerdict
  | .consistent _ _ => ⟨some true, none⟩
  | .inconsistent _ _ => ⟨some false, none⟩
  | .unknown reason => ⟨none, some reason⟩

def Meaning (graph : Graph) : Option Bool → Prop
  | some true => Accepted graph ∧ Satisfiable graph
  | some false => Accepted graph ∧ ¬ Satisfiable graph
  | none => True

theorem erase_sound {graph : Graph} (verdict : CertifiedVerdict graph) :
    Meaning graph (erase verdict).consistent := by
  cases verdict with
  | consistent admitted model => exact ⟨admitted, model⟩
  | inconsistent admitted noModel => exact ⟨admitted, noModel⟩
  | unknown _ => exact True.intro

def decide (graph : Graph) (certificate : Cert) : CertifiedDecision.WireVerdict :=
  erase (checkedRefutation graph certificate)

/-- The actual exported decision function, with no caller-supplied reader preservation premise. -/
theorem decide_sound (graph : Graph) (certificate : Cert) :
    Meaning graph (decide graph certificate).consistent :=
  erase_sound (checkedRefutation graph certificate)

/-- Every definitive result, including externally constructed model verdicts,
is confined to inputs the entire reader admits. -/
theorem definitive_admitted {graph : Graph} (verdict : CertifiedVerdict graph)
    (answer : Bool) (reported : (erase verdict).consistent = some answer) :
    Accepted graph := by
  have meaningful := erase_sound verdict
  rw [reported] at meaningful
  cases answer <;> exact meaningful.1

theorem unsupported_is_unknown {graph : Graph} (unsupported : readOntology graph = none)
    (certificate : Cert) : decide graph certificate = ⟨none, some .unsupported⟩ := by
  unfold decide checkedRefutation
  split
  · rfl
  · rename_i ontology reading
    rw [unsupported] at reading
    cases reading

#print axioms knownAnnotation
#print axioms readOntology_preserves_models
#print axioms readOntology_hasModel
#print axioms decide_sound
#print axioms definitive_admitted
#print axioms unsupported_is_unknown

end L4Factoidal.OWL.AtomicDirect
