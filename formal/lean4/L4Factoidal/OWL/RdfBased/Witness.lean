/-
L4Factoidal.OWL.RdfBased.Witness — existential successors for
`owl:someValuesFrom` (OWL 2 RDF-Based Semantics, Table 5.6), with a
blank-node assignment that is EXTENDED at the new labels.

Table 5.6: if `(z, c) ∈ IEXT(I(owl:someValuesFrom))` and `(z, p) ∈
IEXT(I(owl:onProperty))` then `ICEXT(z) = {x | ∃ y : (x, y) ∈ IEXT(p)
and y ∈ ICEXT(c)}`. So `x rdf:type z` with those two triples entails
`x p _:w`, `_:w rdf:type c` for a blank node `_:w`: the condition makes
the successor exist, and a blank node in a graph asks only that SOME
element be assigned to it (RDF 1.1 Semantics § 5.2).

`RbDerives` states soundness under the premise's own assignment; a rule
that mints a blank node cannot be stated that way. `svfWits_sound` is
the statement this rule needs: for a list of witnesses whose labels are
fresh for `g` and name their witness (two witnesses with one label have
the same subject, property and class), every assignment making `g`
true extends, at those labels, to one making `g` and every witness
triple true. The executable side (`svfWitsFor`) checks freshness and
the naming at run time and drops what fails, so the theorem needs no
proof that a string encoding is injective.

The regime adds witnesses only for properties the conclusion graph uses
with a blank-node object (goal-directed), and the number of rounds
bounds the depth of witness chains.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RdfBased.Rules

namespace L4Factoidal.OWL.RdfBased

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-- One existential successor: `x rdf:type r`, `r owl:someValuesFrom c`,
`r owl:onProperty p`, named by the label `b`. -/
structure SvfWit where
  x : Subject
  r : Subject
  p : WfIri
  c : Term
  b : BNodeId
deriving DecidableEq

def SvfWit.Valid (g : Graph) (w : SvfWit) : Prop :=
  (⟨w.x, rdfType, w.r.toTerm⟩ : Triple) ∈ g ∧
  (⟨w.r, owlSomeValuesFrom, w.c⟩ : Triple) ∈ g ∧
  (⟨w.r, owlOnProperty, .iri w.p⟩ : Triple) ∈ g

def SvfWit.triples (w : SvfWit) : List Triple :=
  [⟨w.x, w.p, .bnode w.b⟩, ⟨.bnode w.b, rdfType, w.c⟩]

/-- Valid witnesses, labels fresh for `g`, and a label determines the
witness's subject, property and class. -/
def WitsOk (g : Graph) (ws : List SvfWit) : Prop :=
  (∀ w ∈ ws, w.Valid g) ∧ (∀ w ∈ ws, w.b ∉ graphBnodeIds g) ∧
  (∀ w1 ∈ ws, ∀ w2 ∈ ws, w1.b = w2.b → w1.x = w2.x ∧ w1.p = w2.p ∧ w1.c = w2.c)

theorem mem_graphBnodeIds_subj {g : Graph} {t : Triple} (ht : t ∈ g) {b : BNodeId}
    (hb : b ∈ subjectBnodes t.s) : b ∈ graphBnodeIds g :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_append_left _ hb⟩

theorem mem_graphBnodeIds_obj {g : Graph} {t : Triple} (ht : t ∈ g) {b : BNodeId}
    (hb : b ∈ termBnodes t.o) : b ∈ graphBnodeIds g :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_append_right _ hb⟩

section Soundness

variable {i : Interp} (hc : RdfBasedConditions i)
include hc

/-- **Existential witnesses are sound.** -/
theorem svfWits_sound {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {ws : List SvfWit} (hok : WitsOk g ws) :
    ∃ A' : BnodeAssignment i.idom, HoldsAll i A' (g ++ ws.flatMap SvfWit.triples) := by
  obtain ⟨hval, hfresh, hname⟩ := hok
  -- The successor of a valid witness, under the premise assignment.
  have hex : ∀ w ∈ ws, ∃ z : i.idom,
      i.iext (i.iIri w.p) (denotSubject i A w.x) z ∧ icext i z (denotTerm i A w.c) := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hval w hw
    have t1 := hA _ h1
    have t2 := hA _ h2
    have t3 := hA _ h3
    simp only [TripleHolds, denot_toTerm, denotTerm] at t1 t2 t3
    exact hc.someValuesFromSub _ _ _ _ t2 t3 t1
  classical
  let A' : BnodeAssignment i.idom := fun b =>
    if h : ∃ w, w ∈ ws ∧ w.b = b then
      Classical.choose (hex (Classical.choose h) (Classical.choose_spec h).1)
    else A b
  -- `A'` agrees with `A` on every label of `g`.
  have hagree : ∀ b ∈ graphBnodeIds g, A' b = A b := by
    intro b hb
    have hno : ¬ ∃ w, w ∈ ws ∧ w.b = b := by
      rintro ⟨w, hw, rfl⟩; exact hfresh w hw hb
    simp only [A', dif_neg hno]
  have hsubj : ∀ (t : Triple), t ∈ g → denotSubject i A' t.s = denotSubject i A t.s :=
    fun t ht => denot_subject_agree i (fun b hb => hagree b (mem_graphBnodeIds_subj ht hb))
  have hobj : ∀ (t : Triple), t ∈ g → denotTerm i A' t.o = denotTerm i A t.o :=
    fun t ht => denot_term_agree i (fun b hb => hagree b (mem_graphBnodeIds_obj ht hb))
  refine ⟨A', fun t ht => ?_⟩
  rcases List.mem_append.mp ht with ht | ht
  · have := hA t ht
    simp only [TripleHolds] at this ⊢
    rw [hsubj t ht, hobj t ht]; exact this
  · obtain ⟨w, hw, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨h1, h2, _⟩ := hval w hw
    have hb : ∃ w', w' ∈ ws ∧ w'.b = w.b := ⟨w, hw, rfl⟩
    have hA'b : A' w.b = Classical.choose (hex (Classical.choose hb) (Classical.choose_spec hb).1) := by
      simp only [A', dif_pos hb]
    have hspec := Classical.choose_spec (hex (Classical.choose hb) (Classical.choose_spec hb).1)
    generalize Classical.choose (hex (Classical.choose hb) (Classical.choose_spec hb).1) = z
      at hspec hA'b
    obtain ⟨hx, hp, hcc⟩ := hname _ (Classical.choose_spec hb).1 w hw (Classical.choose_spec hb).2
    rw [hx, hp, hcc] at hspec
    have hxs : denotSubject i A' w.x = denotSubject i A w.x := by
      have := hsubj _ h1; simpa using this
    have hcs : denotTerm i A' w.c = denotTerm i A w.c := by
      have := hobj _ h2; simpa using this
    simp only [SvfWit.triples, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · show i.iext (i.iIri w.p) (denotSubject i A' w.x) (A' w.b)
      rw [hxs, hA'b]; exact hspec.1
    · show i.iext (i.iIri rdfType) (A' w.b) (denotTerm i A' w.c)
      rw [hcs, hA'b]; exact hspec.2

end Soundness

/-- Entailment form: `g` entails `g` with the witness triples added. -/
theorem svfWits_entailed {g : Graph} {ws : List SvfWit} (hok : WitsOk g ws) :
    RbEntails g (g ++ ws.flatMap SvfWit.triples) := by
  intro i hc ⟨A, hA⟩
  exact svfWits_sound hc hA hok

/-! ## Executable -/

def rbSubjKey : Subject → String
  | .iri w => "i" ++ w.val
  | .bnode b => "b" ++ b

def svfWitLabel (x r : Subject) : BNodeId :=
  "__rb_svf__" ++ rbSubjKey x ++ "__" ++ rbSubjKey r

/-- Candidate witnesses: every `x rdf:type r` with `r owl:someValuesFrom
c` and `r owl:onProperty p` for a property `p` in `ps`. -/
def svfCandidates (g : Graph) (ps : List WfIri) : List SvfWit :=
  (g.filter (fun t => t.p == owlSomeValuesFrom)).flatMap (fun t =>
    (withSubjPred g t.s owlOnProperty).flatMap (fun u =>
      (asIri u.o).flatMap (fun p =>
        if ps.contains p then
          (withPredObj g rdfType t.s.toTerm).map (fun tx =>
            ({ x := tx.s, r := t.s, p := p, c := t.o, b := svfWitLabel tx.s t.s } : SvfWit))
        else [])))

/-- The predicates the goal uses with a blank-node object. -/
def bnodeObjectPredicates (goal : Graph) : List WfIri :=
  goal.filterMap (fun t => match t.o with | .bnode _ => some t.p | _ => none)

/-- The witnesses the regime adds: candidates whose label is fresh for
`g` and names one (subject, property, class). -/
def svfWitsFor (g goal : Graph) : List SvfWit :=
  let bs := graphBnodeIds g
  let fresh := (svfCandidates g (bnodeObjectPredicates goal)).filter (fun w => !bs.contains w.b)
  fresh.filter (fun w => fresh.all (fun w2 => w2.b != w.b || (w2.x == w.x && w2.p == w.p && w2.c == w.c)))

theorem svfCandidates_valid {g : Graph} {ps : List WfIri} {w : SvfWit}
    (h : w ∈ svfCandidates g ps) : w.Valid g := by
  simp only [svfCandidates, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨t, ⟨ht, htp⟩, u, hu, p, hp, h⟩ := h
  split at h
  · simp only [List.mem_map] at h
    obtain ⟨tx, htx, rfl⟩ := h
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    obtain ⟨htxg, htxp, htxo⟩ := mem_withPredObj htx
    have htp' : t.p = owlSomeValuesFrom := Subtype.ext (by simpa using htp)
    exact ⟨mem_of_parts htxg rfl htxp htxo, mem_of_parts ht rfl htp' rfl,
      mem_of_parts hug hus hup (mem_asIri hp)⟩
  · simp at h

theorem svfWitsFor_ok (g goal : Graph) : WitsOk g (svfWitsFor g goal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simp only [svfWitsFor, List.mem_filter] at hw
    exact svfCandidates_valid hw.1.1
  · intro w hw hmem
    simp only [svfWitsFor, List.mem_filter] at hw
    have h := hw.1.2
    rw [List.contains_iff_mem.mpr hmem] at h
    simp at h
  · intro w1 hw1 w2 hw2 hb
    simp only [svfWitsFor, List.mem_filter, List.all_eq_true] at hw1 hw2
    have := hw2.2 w1 hw1.1
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq] at this
    rcases this with h | ⟨⟨hx, hp⟩, hc⟩
    · exact absurd hb h
    · exact ⟨hx, hp, hc⟩

/-- The witness triples the regime adds to `g`. -/
def svfWitTriples (g goal : Graph) : List Triple :=
  (svfWitsFor g goal).flatMap SvfWit.triples

end L4Factoidal.OWL.RdfBased
