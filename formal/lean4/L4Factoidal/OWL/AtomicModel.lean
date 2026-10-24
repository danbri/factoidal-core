/-
Model certificates, countermodels and the fuel-bounded decision for the
AtomicDirect fragment (https://github.com/danbri/factoidal/issues/960).

A consistency verdict `true` needs a model. This module gives one as a finite
interpretation (`FinModel`) and checks it with `checkModel` against the
ORIGINAL graph's source contract (`AtomicDirect.MapsTo`, `axiomHolds`), not
against a compiled ontology. `checkModel_sound` proves: when the checker
accepts, the interpretation is a model of the graph (`SourceModel`). No
premise of that theorem mentions `SourceModel` or `Satisfiable`.

The model search (`search`) is not trusted. It is the completion of the
admitted fragment: atomic subsumption closes each element's label; a
requirement `∃p.C` of an element gets the p-successor `w_C`, the single
witness element of the filler C. A second element that needs a successor in
C reuses `w_C` (blocking by filler: a new element is not made when an element
with the same seed already exists). Every element made has a seed in the
finite set of fillers, so the search ends. Only the checker decides; a wrong
search gives `null`, never a wrong verdict.

When the search meets a clash, it emits a refutation certificate for the
existing checker (`DirectCert.checkCertFuel`): `.close` for a clash of a named
individual, and a chain of `.exWit` steps (the tableau ∃-rule, one fresh
witness name per step) for a clash of a generated element.

`fuel` bounds both the search (rounds of ∃-expansion) and the certificate
checker (saturation rounds at each certificate node).

`TransitiveObjectProperty(p)`: the model interprets p as the total relation
(`FinModel.full`), which is transitive; the checker tests that p is total
(`transOk`). With no ∀, no number restriction, no ∃ on a left-hand side and no
role disjointness, more pairs falsify no axiom of the fragment.

An entailment answer `false` needs a countermodel: a checked model of the
premise that is not a model of the conclusion (`checkCountermodel_sound`).
-/
import L4Factoidal.OWL.AtomicDirect
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.OWL.AtomicModel

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.AtomicDirect

/-! ## Finite interpretations -/

/-- The right-hand side of a subclass axiom of the fragment. -/
inductive Rhs where
  | cls (className : AtomicClass)
  | ex (role : String) (filler : AtomicClass)
  deriving Repr, DecidableEq

/-- A finite interpretation over `Nat` and the untrusted indexes its checker
reads. Element `x` with `x ≥ labels.size` behaves as element 0 (`norm`), so
the domain is all of `Nat` and the checker visits only `labels.size`
elements. -/
structure FinModel where
  labels : Array (List String)
  edges : Array (List (String × Nat))
  names : Std.HashMap String Nat
  /-- For a class name `A`: the right-hand sides of the axioms `A ⊑ rhs`. -/
  sub : Std.HashMap String (List Rhs)
  /-- The right-hand sides of the axioms `owl:Thing ⊑ rhs`. -/
  topSub : List Rhs
  /-- For a restriction node: its properties and filler classes. -/
  restr : Std.HashMap BNodeId (List String × List AtomicClass)
  /-- Roles interpreted as the total relation (every pair of elements): the
  transitive roles. A total relation is transitive, and in the fragment (no
  ∀, no number restriction, no ∃ on a left-hand side, no role disjointness)
  more pairs falsify no axiom. The checker then needs no transitive closure
  of the edges, which has n² pairs and costs n³ to check on a chain of n
  witnesses (measured: 134.7 s at n = 500, 2026-10-24). -/
  full : List String := []

namespace FinModel

def norm (M : FinModel) (x : Nat) : Nat := if x < M.labels.size then x else 0

theorem norm_norm (M : FinModel) (x : Nat) : M.norm (M.norm x) = M.norm x := by
  unfold norm
  by_cases h : x < M.labels.size <;> simp [h]

theorem norm_mem (M : FinModel) (x : Nat) : M.norm x ∈ 0 :: List.range M.labels.size := by
  unfold norm
  split
  · exact List.mem_cons_of_mem _ (List.mem_range.mpr ‹_›)
  · exact List.mem_cons_self

def labelAt (M : FinModel) (i : Nat) : List String := M.labels.getD i []

def edgesAt (M : FinModel) (i : Nat) : List (String × Nat) := M.edges.getD i []

/-- The interpretation: `·^C` and `·^OP` of Direct Semantics § 2.2. -/
def interp (M : FinModel) : Interp Nat where
  concept name x := name ∈ M.labelAt (M.norm x)
  role r x y := r ∈ M.full ∨ (r, y) ∈ M.edgesAt (M.norm x)

/-- The individual assignment `·^I`; a name with no element is element 0. -/
def assign (M : FinModel) (name : Ind) : Nat := M.names.getD name 0

def restrOf (M : FinModel) (node : BNodeId) : List String × List AtomicClass :=
  M.restr.getD node ([], [])

end FinModel

/-- What a right-hand side means at an element. -/
def rhsHolds {δ : Type} (I : Interp δ) (x : δ) : Rhs → Prop
  | .cls c => classHolds I c x
  | .ex r c => ∃ y, I.role r x y ∧ classHolds I c y

def classHoldsB (M : FinModel) (x : Nat) : AtomicClass → Bool
  | .named name => (M.labelAt (M.norm x)).contains name
  | .thing => true
  | .nothing => false

theorem classHoldsB_iff (M : FinModel) (x : Nat) (c : AtomicClass) :
    classHoldsB M x c = true ↔ classHolds M.interp c x := by
  cases c <;> simp [classHoldsB, classHolds, FinModel.interp]

theorem classHoldsB_norm (M : FinModel) (x : Nat) (c : AtomicClass) :
    classHoldsB M (M.norm x) c = classHoldsB M x c := by
  cases c <;> simp [classHoldsB, FinModel.norm_norm]

/-- An edge first; for a total role, any element of the filler. -/
def rhsHoldsB (M : FinModel) (x : Nat) : Rhs → Bool
  | .cls c => classHoldsB M x c
  | .ex r c => (M.edgesAt (M.norm x)).any (fun e => e.1 == r && classHoldsB M e.2 c) ||
      (M.full.contains r && (0 :: List.range M.labels.size).any (fun j => classHoldsB M j c))

theorem rhsHoldsB_iff (M : FinModel) (x : Nat) (rhs : Rhs) :
    rhsHoldsB M x rhs = true ↔ rhsHolds M.interp x rhs := by
  cases rhs with
  | cls c => exact classHoldsB_iff M x c
  | ex r c =>
      simp only [rhsHoldsB, rhsHolds, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
        beq_iff_eq, List.contains_iff_mem]
      constructor
      · rintro (⟨⟨r', y⟩, member, rfl, holds⟩ | ⟨total, j, _, holds⟩)
        · exact ⟨y, Or.inr member, (classHoldsB_iff M y c).mp holds⟩
        · exact ⟨j, Or.inl total, (classHoldsB_iff M j c).mp holds⟩
      · rintro ⟨y, total | member, holds⟩
        · refine Or.inr ⟨total, M.norm y, M.norm_mem y, ?_⟩
          rw [classHoldsB_norm]
          exact (classHoldsB_iff M y c).mpr holds
        · exact Or.inl ⟨(r, y), member, rfl, (classHoldsB_iff M y c).mpr holds⟩

theorem rhsHolds_norm (M : FinModel) (x : Nat) (rhs : Rhs) :
    rhsHolds M.interp (M.norm x) rhs ↔ rhsHolds M.interp x rhs := by
  cases rhs with
  | cls c => cases c <;> simp [rhsHolds, classHolds, FinModel.interp, FinModel.norm_norm]
  | ex r c => simp [rhsHolds, FinModel.interp, FinModel.norm_norm]

/-! ## The model checker -/

/-- `TransitiveObjectProperty(r)` holds: `r` is a total role (Direct
Semantics Table 6; a total relation is transitive). -/
def transOk (M : FinModel) (r : String) : Bool := M.full.contains r

theorem transOk_sound {M : FinModel} {r : String} (h : transOk M r = true) (x y z : Nat)
    (_first : M.interp.role r x y) (_second : M.interp.role r y z) : M.interp.role r x z :=
  Or.inl (List.contains_iff_mem.mp h)

/-- Element `i` satisfies every axiom whose left-hand side it is in. -/
def elementOk (M : FinModel) (i : Nat) : Bool :=
  (M.labelAt i).all (fun name => (M.sub.getD name []).all (rhsHoldsB M i)) &&
  M.topSub.all (rhsHoldsB M i)

/-- Every element `0 … labels.size - 1`, and element 0 when there is none. -/
def elementsOk (M : FinModel) : Bool :=
  elementOk M 0 && (List.range M.labels.size).all (elementOk M)

theorem elementOk_norm {M : FinModel} (ok : elementsOk M = true) (x : Nat) :
    elementOk M (M.norm x) = true := by
  simp only [elementsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ok
  unfold FinModel.norm
  split
  · exact ok.2 x ‹_›
  · exact ok.1

/-- The index records the axiom `left ⊑ rhs`. -/
def covered (M : FinModel) (left : AtomicClass) (rhs : Rhs) : Bool :=
  match left with
  | .nothing => true
  | .thing => M.topSub.contains rhs
  | .named name => (M.sub.getD name []).contains rhs

theorem covered_sound {M : FinModel} (ok : elementsOk M = true) {left : AtomicClass}
    {rhs : Rhs} (h : covered M left rhs = true) (x : Nat)
    (holds : classHolds M.interp left x) : rhsHolds M.interp x rhs := by
  have element := elementOk_norm ok x
  simp only [elementOk, Bool.and_eq_true, List.all_eq_true] at element
  rw [← rhsHolds_norm]
  apply (rhsHoldsB_iff M (M.norm x) rhs).mp
  cases left with
  | nothing => exact absurd holds (by simp [classHolds])
  | thing =>
      simp only [covered, List.contains_iff_mem] at h
      exact element.2 rhs h
  | named name =>
      simp only [covered, List.contains_iff_mem] at h
      exact element.1 name holds rhs h

/-- One source axiom, checked on the finite interpretation. -/
def clauseOk (M : FinModel) : Axiom → Bool
  | .noEffect => true
  | .subClass left right => covered M left (.cls right)
  | .subClassSome left role filler => covered M left (.ex role filler)
  | .classAssertion individual className => classHoldsB M (M.assign individual) className
  | .assertSome individual role filler => rhsHoldsB M (M.assign individual) (.ex role filler)
  | .same left right => M.assign left == M.assign right
  | .different left right => M.assign left != M.assign right
  | .transitive role => transOk M role

theorem clauseOk_sound {M : FinModel} (ok : elementsOk M = true) (clause : Axiom)
    (h : clauseOk M clause = true) : axiomHolds M.interp M.assign clause := by
  cases clause with
  | noEffect => trivial
  | subClass left right => exact fun x holds => covered_sound ok h x holds
  | subClassSome left role filler => exact fun x holds => covered_sound ok h x holds
  | classAssertion individual className =>
      exact (classHoldsB_iff M (M.assign individual) className).mp h
  | assertSome individual role filler =>
      exact (rhsHoldsB_iff M (M.assign individual) (.ex role filler)).mp h
  | same left right => simpa [clauseOk, axiomHolds] using h
  | different left right => simpa [clauseOk, axiomHolds] using h
  | transitive role => exact transOk_sound h

/-- Every class a name can map to (`MapsClass`). -/
def classesOf (name : WfIri) : List AtomicClass :=
  (if name.val == owlThing.val then [.thing] else []) ++
  (if name.val == owlNothing.val then [.nothing] else []) ++
  (if reserved name then [] else [.named name.val])

theorem mem_classesOf {name : WfIri} {c : AtomicClass} (mapped : MapsClass name c) :
    c ∈ classesOf name := by
  cases mapped with
  | thing => simp [classesOf]
  | nothing => simp [classesOf]
  | named _ ordinary => simp [classesOf, ordinary]

/-- The restriction index lists every property and filler of every node. -/
def restrIndexOk (M : FinModel) : Triple → Bool
  | ⟨.bnode node, predicate, .iri value⟩ =>
      (if predicate.val == onProperty.val then (M.restrOf node).1.contains value.val else true) &&
      (if predicate.val == someValuesFrom.val then
        (classesOf value).all (fun c => (M.restrOf node).2.contains c) else true)
  | _ => true

/-- Every axiom a triple can map to (an over-approximation of `MapsTo`). -/
def candidates (M : FinModel) : Triple → List Axiom
  | ⟨.iri subject, predicate, .iri value⟩ =>
      (if predicate.val == rdfType.val then
        (classesOf value).map (.classAssertion subject.val) else []) ++
      (if predicate.val == subClassOf.val then
        (classesOf subject).flatMap (fun left => (classesOf value).map (.subClass left)) else []) ++
      (if predicate.val == sameAs.val then [.same subject.val value.val] else []) ++
      (if predicate.val == differentFrom.val then [.different subject.val value.val] else [])
  | ⟨.iri subject, predicate, .bnode node⟩ =>
      (if predicate.val == subClassOf.val then
        (classesOf subject).flatMap (fun left => (M.restrOf node).1.flatMap (fun role =>
          (M.restrOf node).2.map (.subClassSome left role))) else []) ++
      (if predicate.val == rdfType.val then
        (M.restrOf node).1.flatMap (fun role =>
          (M.restrOf node).2.map (.assertSome subject.val role)) else [])
  | _ => []

/-- The role axioms a triple can map to. -/
def roleCandidates : Triple → List Axiom
  | ⟨.iri subject, predicate, .iri value⟩ =>
      if predicate.val == rdfType.val && value.val == owlTransitiveProperty.val then
        [.transitive subject.val] else []
  | _ => []

/-- Completeness of the candidates: every axiom of the source contract is
`noEffect` or a candidate, given a correct restriction index. -/
theorem candidates_complete {graph : Graph} {M : FinModel}
    (index : ∀ t ∈ graph, restrIndexOk M t = true)
    {triple : Triple} {clause : Axiom} (mapped : MapsTo graph triple clause) :
    clause = .noEffect ∨ clause ∈ candidates M triple ∨ clause ∈ roleCandidates triple := by
  cases mapped with
  | subClass left right leftClass rightClass mappedLeft mappedRight =>
      refine Or.inr (Or.inl ?_)
      simp only [candidates, List.mem_append, List.mem_flatMap, List.mem_map]
      refine Or.inl (Or.inl (Or.inr ?_))
      simp only [show (subClassOf.val == subClassOf.val) = true from by simp, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨leftClass, mem_classesOf mappedLeft, rightClass, mem_classesOf mappedRight, rfl⟩
  | classAssertion individual name className ordinary mappedClass =>
      refine Or.inr (Or.inl ?_)
      simp only [candidates, List.mem_append]
      refine Or.inl (Or.inl (Or.inl ?_))
      simp only [show (rdfType.val == rdfType.val) = true from by simp, if_true, List.mem_map]
      exact ⟨className, mem_classesOf mappedClass, rfl⟩
  | same left right _ _ =>
      refine Or.inr (Or.inl ?_)
      simp only [candidates, List.mem_append]
      refine Or.inl (Or.inr ?_)
      simp [sameAs]
  | different left right _ _ =>
      refine Or.inr (Or.inl ?_)
      simp only [candidates, List.mem_append]
      refine Or.inr ?_
      simp [differentFrom]
  | subClassSome left node leftClass property filler fillerClass mappedLeft _
      propertyTriple fillerTriple mappedFiller =>
      have propertyIndexed := index _ propertyTriple
      have fillerIndexed := index _ fillerTriple
      simp only [restrIndexOk, Bool.and_eq_true] at propertyIndexed fillerIndexed
      have propertyMember : property.val ∈ (M.restrOf node).1 := by
        have h := propertyIndexed.1
        simp only [show (onProperty.val == onProperty.val) = true from by simp, if_true,
          List.contains_iff_mem] at h
        exact h
      have fillerMember : fillerClass ∈ (M.restrOf node).2 := by
        have h := fillerIndexed.2
        simp only [show (someValuesFrom.val == someValuesFrom.val) = true from by simp, if_true,
          List.all_eq_true, List.contains_iff_mem] at h
        exact h fillerClass (mem_classesOf mappedFiller)
      refine Or.inr (Or.inl ?_)
      simp only [candidates, List.mem_append]
      refine Or.inl ?_
      simp only [show (subClassOf.val == subClassOf.val) = true from by simp, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨leftClass, mem_classesOf mappedLeft, property.val, propertyMember, fillerClass,
        fillerMember, rfl⟩
  | assertSome individual node property filler fillerClass _ _
      propertyTriple fillerTriple mappedFiller =>
      have propertyIndexed := index _ propertyTriple
      have fillerIndexed := index _ fillerTriple
      simp only [restrIndexOk, Bool.and_eq_true] at propertyIndexed fillerIndexed
      have propertyMember : property.val ∈ (M.restrOf node).1 := by
        have h := propertyIndexed.1
        simp only [show (onProperty.val == onProperty.val) = true from by simp, if_true,
          List.contains_iff_mem] at h
        exact h
      have fillerMember : fillerClass ∈ (M.restrOf node).2 := by
        have h := fillerIndexed.2
        simp only [show (someValuesFrom.val == someValuesFrom.val) = true from by simp, if_true,
          List.all_eq_true, List.contains_iff_mem] at h
        exact h fillerClass (mem_classesOf mappedFiller)
      refine Or.inr (Or.inl ?_)
      simp only [candidates, List.mem_append]
      refine Or.inr ?_
      simp only [show (rdfType.val == rdfType.val) = true from by simp, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨property.val, propertyMember, fillerClass, fillerMember, rfl⟩
  | transitive name _ =>
      exact Or.inr (Or.inr (by simp [roleCandidates]))
  | _ => exact Or.inl rfl

def tripleOk (M : FinModel) (triple : Triple) : Bool :=
  restrIndexOk M triple && (candidates M triple).all (clauseOk M) &&
    (roleCandidates triple).all (clauseOk M)

/-- THE MODEL CHECKER: total; one pass over the elements and one over the
triples of the original graph. -/
def checkModel (graph : Graph) (M : FinModel) : Bool :=
  elementsOk M && graph.all (tripleOk M)

/-- SOUNDNESS: an accepted finite interpretation is a model of the graph
under the source contract (`MapsTo`, `axiomHolds`: OWL 2 Direct Semantics
Tables 4, 5 and 10 for the admitted constructors). -/
theorem checkModel_sound {graph : Graph} {M : FinModel} (h : checkModel graph M = true) :
    SourceModel M.interp M.assign graph := by
  simp only [checkModel, tripleOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨ok, triples⟩ := h
  intro triple member clause mapped
  rcases candidates_complete (fun t m => (triples t m).1.1) mapped with equal | candidate | role
  · subst equal; trivial
  · exact clauseOk_sound ok clause ((triples triple member).1.2 clause candidate)
  · exact clauseOk_sound ok clause ((triples triple member).2 clause role)

theorem checkModel_satisfiable {graph : Graph} {M : FinModel} (h : checkModel graph M = true) :
    Satisfiable graph :=
  ⟨Nat, M.interp, M.assign, checkModel_sound h⟩

/-! ## Countermodels -/

/-- Entailment under the source contract: every model of the premise is a
model of the conclusion (Direct Semantics § 2.5, with one assignment of the
individual names for both). -/
def Entails (premise conclusion : Graph) : Prop :=
  ∀ (δ : Type) (interpretation : Interp δ) (assignment : Ind → δ),
    SourceModel interpretation assignment premise →
      SourceModel interpretation assignment conclusion

/-- The axiom is false in the finite interpretation. -/
def clauseFails (M : FinModel) : Axiom → Bool
  | .noEffect => false
  | .subClass left right => (List.range M.labels.size).any (fun i =>
      classHoldsB M i left && !classHoldsB M i right)
  | .subClassSome left role filler => (List.range M.labels.size).any (fun i =>
      classHoldsB M i left && !rhsHoldsB M i (.ex role filler))
  | .classAssertion individual className => !classHoldsB M (M.assign individual) className
  | .assertSome individual role filler => !rhsHoldsB M (M.assign individual) (.ex role filler)
  | .same left right => M.assign left != M.assign right
  | .different left right => M.assign left == M.assign right
  -- No countermodel is claimed from a transitivity axiom (sound: `false`
  -- claims nothing).
  | .transitive _ => false

theorem clauseFails_sound {M : FinModel} {clause : Axiom} (h : clauseFails M clause = true) :
    ¬ axiomHolds M.interp M.assign clause := by
  cases clause with
  | noEffect => cases h
  | subClass left right =>
      intro holds
      obtain ⟨i, _, witness⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at witness
      have inRight := holds i ((classHoldsB_iff M i left).mp witness.1)
      rw [← classHoldsB_iff] at inRight
      rw [inRight] at witness
      cases witness.2
  | subClassSome left role filler =>
      intro holds
      obtain ⟨i, _, witness⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at witness
      have successor := holds i ((classHoldsB_iff M i left).mp witness.1)
      have checked := (rhsHoldsB_iff M i (.ex role filler)).mpr successor
      rw [checked] at witness
      cases witness.2
  | classAssertion individual className =>
      intro holds
      have checked := (classHoldsB_iff M (M.assign individual) className).mpr holds
      simp [clauseFails, checked] at h
  | assertSome individual role filler =>
      intro holds
      have checked := (rhsHoldsB_iff M (M.assign individual) (.ex role filler)).mpr holds
      simp [clauseFails, checked] at h
  | same left right =>
      intro holds
      simp [clauseFails, axiomHolds] at h holds
      exact h holds
  | different left right =>
      intro holds
      simp [clauseFails, axiomHolds] at h holds
      exact holds h
  | transitive _ => simp [clauseFails] at h

/-- Some triple of the graph maps (by the reader's proof-bearing decoding)
to an axiom that is false in the finite interpretation. -/
def refutesGraph (graph : Graph) (M : FinModel) : Bool :=
  let index := nodeIndex graph
  let annotations := annotationIndex graph
  graph.any (fun triple => match readTriple graph index annotations triple with
    | some clause => clauseFails M clause.val
    | none => false)

theorem refutesGraph_sound {graph : Graph} {M : FinModel} (h : refutesGraph graph M = true) :
    ¬ SourceModel M.interp M.assign graph := by
  intro model
  obtain ⟨triple, member, fails⟩ := List.any_eq_true.mp h
  cases decoded : readTriple graph (nodeIndex graph) (annotationIndex graph) triple with
  | none => simp [decoded] at fails
  | some clause =>
      simp only [decoded] at fails
      exact clauseFails_sound fails (model triple member clause.val clause.property)

/-- THE COUNTERMODEL CHECKER: a checked model of the premise in which the
conclusion fails. -/
def checkCountermodel (premise conclusion : Graph) (M : FinModel) : Bool :=
  checkModel premise M && refutesGraph conclusion M

/-- SOUNDNESS: an accepted countermodel shows that the premise does not
entail the conclusion. -/
theorem checkCountermodel_sound {premise conclusion : Graph} {M : FinModel}
    (h : checkCountermodel premise conclusion M = true) : ¬ Entails premise conclusion := by
  simp only [checkCountermodel, Bool.and_eq_true] at h
  intro entails
  exact refutesGraph_sound h.2 (entails Nat M.interp M.assign (checkModel_sound h.1))

#print axioms checkModel_sound
#print axioms checkModel_satisfiable
#print axioms checkCountermodel_sound

/-! ## The model search (untrusted)

Nothing below is a soundness premise: its output is a `FinModel` for
`checkModel` or a `Cert` for `checkCertFuel`. -/

def atomicOf : Concept → Option AtomicClass
  | .atom name => some (.named name)
  | .top => some .thing
  | .bot => some .nothing
  | _ => none

def rhsOf : Concept → Option Rhs
  | .ex role filler => (atomicOf filler).map (.ex role)
  | other => (atomicOf other).map .cls

/-- The subclass index of a compiled ontology: per class name, and for `owl:Thing`. -/
def tboxIndex (ontology : DlOntology) : Option (Std.HashMap String (List Rhs) × List Rhs) :=
  ontology.tbox.foldlM (fun (state : Std.HashMap String (List Rhs) × List Rhs) axiomPair => do
    let rhs ← rhsOf axiomPair.2
    match axiomPair.1 with
    | .atom name => pure (state.1.insert name (rhs :: state.1.getD name []), state.2)
    | .top => pure (state.1, rhs :: state.2)
    | .bot => pure state
    | _ => none) ({}, [])

/-- The restriction index of a graph. -/
def restrIndex (graph : Graph) : Std.HashMap BNodeId (List String × List AtomicClass) :=
  graph.foldl (fun index triple => match triple with
    | ⟨.bnode node, predicate, .iri value⟩ =>
      let entry := index.getD node ([], [])
      if predicate.val == onProperty.val then index.insert node (value.val :: entry.1, entry.2)
      else if predicate.val == someValuesFrom.val then
        index.insert node (entry.1, classesOf value ++ entry.2)
      else index
    | _ => index) {}

/-- A label: its class names, its ∃-requirements, and whether it holds `owl:Nothing`. -/
structure Label where
  names : List String
  requirements : List (String × AtomicClass)
  bottom : Bool

/-- The atomic-subsumption closure of `seeds` and the `owl:Thing` axioms. A
loop: each name is pushed at most once, so `bound` rounds suffice for any
`bound` at least the number of names in the index plus the seeds. -/
def closeLabel (sub : Std.HashMap String (List Rhs)) (topSub : List Rhs)
    (seeds : List String) (bound : Nat) : Label := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut order : Array String := #[]
  let mut stack : Array String := #[]
  let mut requirements : Array (String × AtomicClass) := #[]
  let mut required : Std.HashSet (String × String) := {}
  let mut bottom := false
  let mut start : Array Rhs := #[]
  for rhs in topSub do start := start.push rhs
  for seed in seeds do start := start.push (.cls (.named seed))
  -- The seeds and the `owl:Thing` axioms first.
  for rhs in start do
    match rhs with
    | .cls (.named name) =>
        if !seen.contains name then
          seen := seen.insert name
          order := order.push name
          stack := stack.push name
    | .cls .nothing => bottom := true
    | .cls .thing => pure ()
    | .ex role filler =>
        let key := (role, reprStr filler)
        if !required.contains key then
          required := required.insert key
          requirements := requirements.push (role, filler)
  for _ in [0:bound] do
    match stack.back? with
    | none => break
    | some name =>
        stack := stack.pop
        for rhs in sub.getD name [] do
          match rhs with
          | .cls (.named next) =>
              if !seen.contains next then
                seen := seen.insert next
                order := order.push next
                stack := stack.push next
          | .cls .nothing => bottom := true
          | .cls .thing => pure ()
          | .ex role filler =>
              let key := (role, reprStr filler)
              if !required.contains key then
                required := required.insert key
                requirements := requirements.push (role, filler)
  pure { names := order.toList, requirements := requirements.toList, bottom := bottom }

/-- Where an element came from: a named individual, or the ∃-rule. -/
inductive Origin where
  | root (name : Ind)
  | child (parent : Nat) (role : String) (filler : AtomicClass)

structure Element where
  label : Label
  origin : Origin
  edges : List (String × Nat) := []

inductive SearchResult where
  /-- A complete, clash-free state, as a finite interpretation. -/
  | model (M : FinModel)
  /-- A clash, as a refutation certificate. -/
  | clash (certificate : Cert)
  /-- The rounds ran out with elements left to expand. -/
  | budget
  /-- The compiled ontology has a shape the search does not read. -/
  | failed

/-- The name an individual has after `DirectCert.mergeAll` applies the
`SameIndividual` pairs in order. -/
def finalName (pairs : List (Ind × Ind)) (name : Ind) : Ind :=
  match pairs with
  | [] => name
  | (b, c) :: rest =>
      finalName (rest.map fun q => (Ind.subst b c q.1, Ind.subst b c q.2)) (Ind.subst b c name)
termination_by pairs.length
decreasing_by simp

/-- A witness name no IRI and no name of the input can spell. -/
def witnessName (k : Nat) : Ind := s!"_:factoidal-witness-{k}"

/-- The ∃-steps from the root to an element, root first. -/
def pathOf (elements : Array Element) (e : Nat) : Ind × List (String × AtomicClass) := Id.run do
  let mut current := e
  let mut steps : List (String × AtomicClass) := []
  let mut root : Ind := ""
  for _ in [0:elements.size + 1] do
    match elements[current]? with
    | none => break
    | some element =>
        match element.origin with
        | .child parent role filler =>
            steps := (role, filler) :: steps
            current := parent
        | .root name =>
            root := name
            break
  pure (root, steps)

/-- The refutation of a clash at element `e`: a chain of `.exWit` steps from
its root individual, then `last`. -/
def clashCert (same : List (Ind × Ind)) (elements : Array Element) (e : Nat)
    (last : Cert) (extra : List (String × AtomicClass)) : Cert := Id.run do
  let (root, steps) := pathOf elements e
  let allSteps := steps ++ extra
  let names := (List.range (allSteps.length + 1)).map (fun k =>
    if k == 0 then finalName same root else witnessName k)
  let mut cert := last
  for k in (List.range allSteps.length).reverse do
    match allSteps[k]?, names[k]?, names[k + 1]? with
    | some (role, filler), some current, some fresh =>
        cert := .exWit current role (compileClass filler) fresh cert
    | _, _, _ => pure ()
  pure cert

/-- The individuals of a compiled ontology, first occurrence first. -/
def individualsOf (ontology : DlOntology) : Array Ind := Id.run do
  let mut seen : Std.HashSet Ind := {}
  let mut order : Array Ind := #[]
  let visit := fun (state : Std.HashSet Ind × Array Ind) (name : Ind) =>
    if state.1.contains name then state else (state.1.insert name, state.2.push name)
  let mut state := (seen, order)
  state := visit state ""
  for assertion in ontology.abox do
    match assertion with
    | .inst a _ => state := visit state a
    | .rel _ a b => state := visit (visit state a) b
    | .diff a b => state := visit (visit state a) b
  for pair in ontology.same do
    state := visit (visit state pair.1) pair.2
  seen := state.1
  order := state.2
  pure order

/-- Union-find over the `SameIndividual` pairs; `find` is a loop of at most
`bound` steps. -/
def ufFind (parent : Std.HashMap Ind Ind) (bound : Nat) (name : Ind) : Ind := Id.run do
  let mut current := name
  for _ in [0:bound] do
    match parent.get? current with
    | some next => if next == current then break else current := next
    | none => break
  pure current

/-- THE SEARCH: completion of the fragment with blocking by filler, at most
`fuel` rounds of ∃-expansion. -/
def search (graph : Graph) (ontology : DlOntology) (fuel : Nat) : SearchResult := Id.run do
  let some (sub, topSub) := tboxIndex ontology | return .failed
  let bound := ontology.tbox.length + 2
  -- Individuals and their equality classes.
  let individuals := individualsOf ontology
  let ufBound := ontology.same.length + 1
  let mut parent : Std.HashMap Ind Ind := {}
  for pair in ontology.same do
    let a := ufFind parent ufBound pair.1
    let b := ufFind parent ufBound pair.2
    if a != b then parent := parent.insert a b
  -- One element per class; "" (the anonymous owl:Thing member) is element 0.
  let mut elementOfRep : Std.HashMap Ind Nat := {}
  let mut names : Std.HashMap String Nat := {}
  let mut repOfElement : Array Ind := #[]
  for name in individuals do
    let rep := ufFind parent ufBound name
    match elementOfRep.get? rep with
    | some e => names := names.insert name e
    | none =>
        let e := repOfElement.size
        elementOfRep := elementOfRep.insert rep e
        repOfElement := repOfElement.push name
        names := names.insert name e
  -- Seeds from the ABox.
  let mut seeds : Array (List String) := Array.replicate repOfElement.size []
  let mut seedRequirements : Array (List (String × AtomicClass)) :=
    Array.replicate repOfElement.size []
  let mut seedBottom : Array Bool := Array.replicate repOfElement.size false
  for assertion in ontology.abox do
    match assertion with
    | .inst a concept =>
        let e := names.getD a 0
        match concept with
        | .atom name => seeds := seeds.modify e (name :: ·)
        | .top => pure ()
        | .bot => seedBottom := seedBottom.set! e true
        | .ex role filler =>
            match atomicOf filler with
            | some c => seedRequirements := seedRequirements.modify e ((role, c) :: ·)
            | none => return .failed
        | _ => return .failed
    | .diff a b =>
        if names.getD a 0 == names.getD b 0 then return .clash .close
    | .rel _ _ _ => return .failed
  -- The root elements.
  let mut elements : Array Element := #[]
  for e in [0:repOfElement.size] do
    let label := closeLabel sub topSub (seeds.getD e []) bound
    let label := { label with
      requirements := label.requirements ++ seedRequirements.getD e []
      bottom := label.bottom || seedBottom.getD e false }
    if label.bottom then return .clash .close
    elements := elements.push { label := label, origin := .root (repOfElement.getD e "") }
  -- ∃-expansion, one round per layer, blocking by filler.
  let mut witnessOf : Std.HashMap String Nat := {}
  let mut frontier : Array Nat := #[]
  for e in [0:elements.size] do
    if !(elements.getD e { label := ⟨[], [], false⟩, origin := .root "" }).label.requirements.isEmpty then
      frontier := frontier.push e
  for _ in [0:fuel] do
    if frontier.isEmpty then break
    let mut next : Array Nat := #[]
    for e in frontier do
      let requirements :=
        (elements.getD e { label := ⟨[], [], false⟩, origin := .root "" }).label.requirements
      for (role, filler) in requirements do
        let key := match filler with
          | .named name => some ("N" ++ name)
          | .thing => some "T"
          | .nothing => none
        match key with
        | none =>
            return .clash (clashCert ontology.same elements e .close [(role, .nothing)])
        | some key =>
            let mut w := 0
            match witnessOf.get? key with
            | some existing => w := existing
            | none =>
                let seedNames := match filler with
                  | .named name => [name]
                  | _ => []
                let label := closeLabel sub topSub seedNames bound
                w := elements.size
                elements := elements.push { label := label, origin := .child e role filler }
                witnessOf := witnessOf.insert key w
                if label.bottom then
                  return .clash (clashCert ontology.same elements w .close [])
                if !label.requirements.isEmpty then next := next.push w
            elements := elements.modify e (fun element =>
              { element with edges := (role, w) :: element.edges })
    frontier := next
  if !frontier.isEmpty then return .budget
  return .model {
    labels := elements.map (·.label.names)
    edges := elements.map (·.edges)
    names := names
    sub := sub
    topSub := topSub
    restr := restrIndex graph
    full := ontology.rbox.trans.eraseDups }

/-! ## The decision -/

/-- The default bound of `owlIsConsistent` and `owlEntails` (rounds). -/
def defaultFuel : Nat := 20000

/-- A refutation certificate, checked at `fuel`. A rejection that the same
certificate passes at `defaultFuel` is reported as budget exhaustion. -/
def refuteChecked (graph : Graph) (ontology : DlOntology)
    (reading : readOntology graph = some ontology) (fuel : Nat) (certificate : Cert) :
    CertifiedVerdict graph :=
  if accepted : checkCertFuel ontology fuel certificate = true then
    .inconsistent ⟨ontology, reading⟩
      (fun model => checkCertFuel_sound accepted (readOntology_hasModel reading model))
  else if fuel < defaultFuel && checkCertFuel ontology defaultFuel certificate then
    .unknown .budgetExhausted
  else .unknown .certificateRejected

/-- THE PRODUCER: a verdict only with a checked model or a checked
refutation, about the original graph. -/
def certifiedDecision (graph : Graph) (fuel : Nat) : CertifiedVerdict graph :=
  match reading : readOntology graph with
  | none => .unknown .unsupported
  | some ontology =>
      match search graph ontology fuel with
      | .model M =>
          if checked : checkModel graph M = true then
            .consistent ⟨ontology, reading⟩ (checkModel_satisfiable checked)
          else .unknown .certificateRejected
      | .clash certificate => refuteChecked graph ontology reading fuel certificate
      | .budget =>
          match refuteChecked graph ontology reading fuel .close with
          | .inconsistent admitted noModel => .inconsistent admitted noModel
          | _ => .unknown .budgetExhausted
      | .failed =>
          match refuteChecked graph ontology reading fuel .close with
          | .inconsistent admitted noModel => .inconsistent admitted noModel
          | _ => .unknown .certificateRejected

def decideFuel (graph : Graph) (fuel : Nat) : CertifiedDecision.WireVerdict :=
  erase (certifiedDecision graph fuel)

/-- The exported decision: `true` means the whole graph is admitted and has a
model; `false` means it is admitted and has none. -/
theorem decideFuel_sound (graph : Graph) (fuel : Nat) :
    Meaning graph (decideFuel graph fuel).consistent :=
  erase_sound (certifiedDecision graph fuel)

/-- What a definite entailment answer means. Only `false` is produced here. -/
def EntailmentMeaning (premise conclusion : Graph) : Option Bool → Prop
  | some false => Accepted premise ∧ Accepted conclusion ∧ ¬ Entails premise conclusion
  | some true => Accepted premise ∧ Accepted conclusion ∧ Entails premise conclusion
  | none => True

/-- A checked countermodel for `premise ⊭ conclusion`, or nothing. -/
def countermodel (premise conclusion : Graph) (fuel : Nat) :
    Option (PLift (Accepted premise ∧ Accepted conclusion ∧ ¬ Entails premise conclusion)) :=
  match readingP : readOntology premise, readingC : readOntology conclusion with
  | some ontology, some conclusionOntology =>
      match search premise ontology fuel with
      | .model M =>
          if checked : checkCountermodel premise conclusion M = true then
            some ⟨⟨ontology, readingP⟩, ⟨conclusionOntology, readingC⟩,
              checkCountermodel_sound checked⟩
          else none
      | _ => none
  | _, _ => none

/-- The entailment answer of the countermodel route: `false` or unknown. -/
def entailsFuel (premise conclusion : Graph) (fuel : Nat) : Option Bool :=
  (countermodel premise conclusion fuel).map (fun _ => false)

theorem entailsFuel_sound (premise conclusion : Graph) (fuel : Nat) :
    EntailmentMeaning premise conclusion (entailsFuel premise conclusion fuel) := by
  unfold entailsFuel
  cases h : countermodel premise conclusion fuel with
  | none => trivial
  | some proof => exact proof.down

#print axioms decideFuel_sound
#print axioms entailsFuel_sound

end L4Factoidal.OWL.AtomicModel
