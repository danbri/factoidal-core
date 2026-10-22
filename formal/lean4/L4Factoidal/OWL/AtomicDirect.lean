/-
Restricted RDF-to-Direct mapping with a proved source-model bridge.

Scope: named atomic classes, Thing/Nothing, SubClassOf, class assertions,
SameIndividual/DifferentIndividuals, and the declarations/annotations below.
OWL 2 Mapping to RDF Graphs (2012), Tables 7 and 16 and section 3.2.2 supply the syntax;
Direct Semantics (2012), Tables 4, 5 and 10 supply the logical conditions.
Annotations have no logical effect (Direct Semantics section 1).

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

def reserved (name : WfIri) : Bool :=
  name.val.startsWith "http://www.w3.org/2002/07/owl#" ||
  name.val.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
  name.val.startsWith "http://www.w3.org/2000/01/rdf-schema#" ||
  name.val.startsWith "http://www.w3.org/2001/XMLSchema#"

def builtinAnnotation (name : WfIri) : Bool :=
  name.val == "http://www.w3.org/2000/01/rdf-schema#label" ||
  name.val == "http://www.w3.org/2000/01/rdf-schema#comment" ||
  name.val == "http://www.w3.org/2002/07/owl#versionInfo"

def validAnnotationName (name : WfIri) : Bool := builtinAnnotation name || !reserved name

/-- Declarative source vocabulary, stated by membership in the original graph. -/
def AnnotationProperty (graph : Graph) (name : WfIri) : Prop :=
  builtinAnnotation name = true ∨ ∃ triple ∈ graph,
    triple = ⟨.iri name, rdfType, .iri owlAnnotationProperty⟩ ∧ validAnnotationName name = true

/-- Initial total lookup: declaration order independent, quadratic worst case over a graph. -/
def isAnnotation (graph : Graph) (name : WfIri) : Bool :=
  builtinAnnotation name || graph.any (fun triple =>
    triple == ⟨.iri name, rdfType, .iri owlAnnotationProperty⟩ && validAnnotationName name)

theorem isAnnotation_sound {graph : Graph} {name : WfIri}
    (known : isAnnotation graph name = true) : AnnotationProperty graph name := by
  rcases Bool.or_eq_true_iff.mp known with builtin | declared
  · exact Or.inl builtin
  · obtain ⟨triple, member, recognized⟩ := List.any_eq_true.mp declared
    rcases Bool.and_eq_true_iff.mp recognized with ⟨same, valid⟩
    exact Or.inr ⟨triple, member, eq_of_beq same, valid⟩

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

/-- Proof-bearing syntax decoding; no logical role is inferred without a source mapping rule. -/
def readTriple (graph : Graph) :
    (triple : Triple) → Option {clause // MapsTo graph triple clause}
  | ⟨subject, predicate, value⟩ =>
    if header : predicate = rdfType ∧ value = .iri owlOntology then
      some ⟨.noEffect, by rcases header with ⟨rfl, rfl⟩; exact .ontologyHeader subject⟩
    else match subject with
    | .bnode _ => none
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
        else match value with
        | .iri classIri =>
          if ordinary : reserved name = false then do
            let ⟨className, mapped⟩ ← readClass classIri
            pure ⟨.classAssertion name.val className, by
              subst predicate; exact .classAssertion name classIri className ordinary mapped⟩
          else none
        | _ => none
      else if subclass : predicate = subClassOf then
        match value with
        | .iri target => do
          let ⟨leftClass, leftMapped⟩ ← readClass name
          let ⟨rightClass, rightMapped⟩ ← readClass target
          pure ⟨.subClass leftClass rightClass, by subst predicate; exact .subClass name target leftClass rightClass leftMapped rightMapped⟩
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
      else if domainStatement : predicate = domain then
        match value with
        | .iri target =>
          if known : isAnnotation graph name = true then
            some ⟨.noEffect, by
              subst predicate
              exact .annotationDomain name target (isAnnotation_sound known)⟩
          else none
        | _ => none
      else if rangeStatement : predicate = range then
        match value with
        | .iri target =>
          if known : isAnnotation graph name = true then
            some ⟨.noEffect, by
              subst predicate
              exact .annotationRange name target (isAnnotation_sound known)⟩
          else none
        | _ => none
      else if known : isAnnotation graph predicate = true then
        if allowed : annotationValue value = true then
          some ⟨.noEffect, .annotation name predicate value
            (isAnnotation_sound known) allowed⟩
        else none
      else none

abbrev MappedAxiom (graph : Graph) := {clause : Axiom // ∃ triple ∈ graph, MapsTo graph triple clause}

/-- List.mapM is total and tail based; one unsupported triple rejects the entire graph. -/
def readAxioms (graph : Graph) : Option (List (MappedAxiom graph)) :=
  graph.attach.mapM (fun ⟨triple, member⟩ => do
    let ⟨clause, mapped⟩ ← readTriple graph triple
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

def readOntology (graph : Graph) : Option DlOntology := do
  let clauses ← readAxioms graph
  pure (compileAxioms (clauses.map Subtype.val))

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
          let ⟨clause, mapped⟩ ← readTriple graph triple
          pure ⟨clause, triple, member, mapped⟩
      have traversal : graph.attach.mapM visit = some clauses := by
        simpa only [readAxioms] using parsed
      intro triple member
      obtain ⟨_, returned⟩ := eachReturned visit graph.attach clauses traversal
        ⟨triple, member⟩ (List.mem_attach graph ⟨triple, member⟩)
      cases decoded : readTriple graph triple with
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
        simpa [readOntology, parsed] using accepted
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

#print axioms isAnnotation_sound
#print axioms readOntology_preserves_models
#print axioms readOntology_hasModel
#print axioms decide_sound
#print axioms definitive_admitted
#print axioms unsupported_is_unknown

end L4Factoidal.OWL.AtomicDirect
