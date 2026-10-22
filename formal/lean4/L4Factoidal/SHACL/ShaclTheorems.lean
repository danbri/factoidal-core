/-
L4Factoidal.SHACL.ShaclTheorems — what is proved about the SHACL Core
validator, with SHACL 1.2 conformance checking.

  * `validate_empty_conforms` — an empty shapes graph conforms (§3.1).
  * `validate_no_targets_conforms` — with no declared targets and no
    sh:shape triple in the data graph (SHACL 1.2 §explicit-shape-target)
    there is no focus node and no result (§2.1).
  * `minCount_zero_no_result` — `sh:minCount 0` never produces a
    result (§4.2.1).
  * `notOf_flips` — `sh:not` on a single-component node shape flips
    conformance of the referenced shape (§4.6.1).
  * `isShaclInstance_iff` — the engine's SHACL-instance test decides
    the §1.4 relation (rdf:type + rdfs:subClassOf*), both directions:
    the closure walk is sound and, with fuel `g.length + 1`, complete.
  * `simpleValueCheck_iff` — every per-value component (§4.1, §4.3,
    §4.4.1–4, §4.8.3, and SHACL 1.2 sh:singleLine, sh:rootClass,
    sh:minListLength, sh:maxListLength, sh:uniqueMembers) decides its
    declarative statement.
  * `evalAggregateNonRec_eq_nil_iff` — every per-focus-node component
    (§4.2, §4.4.5, §4.5, §4.8.1 in both sh:closed forms, §4.8.2, and
    SHACL 1.2 sh:subsetOf, sh:uniqueValuesFor) decides its declarative
    statement.
  * `collectShapeViolations_conforms_iff` — SHACL 1.2 conformance
    checking (`ValidationEnv.conforms`: no result with a disallowed
    severity) of the engine's results for a focus node and a shape iff
    `Spec.Conforms` holds, at every fuel; `validate_conforms_iff` lifts
    this to §3.1: `(validate g sg cfg).conforms = true ↔
    Spec.GraphConforms (cfg.envFor g sg.shapes) g sg`. Under SHACL 1.2
    "no result" and "conforms" differ (a sh:Debug result does not
    count), so the SHACL 1.1 statement `collectShapeViolations … = [] ↔
    Spec.Conforms …` is no longer true; its sound direction is
    `collectShapeViolations_eq_nil_conforms`.
  * `someValue_aggConforms_iff` — the sh:someValue clause of
    `Spec.AggConforms` stated through `Spec.Conforms`.

Places where the specification names the engine rather than restating
it, so that the equivalence there is by definition: the count of
conforming value nodes for `sh:qualifiedValueShape` (`qualifyingCount`),
the number of matching shapes for `sh:xone` (the filter over
`collectShapeViolations`), the SHACL list reading (`shaclListMembers`),
the sh:uniqueValuesFor key (`uvfKey`, `keyEq`) and target table
(`ValidationEnv.targetsOf`), the sh:closed sh:ByTypes property table
(computed at decode time from the shapes graph), the node-expression
evaluator (`ValidationEnv.evalExpr`), and the focus nodes
(`shapeFocusNodes`). Everything else in `Spec` is stated with
quantifiers over the data graph.

Axiom audit (`#print axioms` at the end): propext, Classical.choice,
Quot.sound only. No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.SHACL.Report

namespace L4Factoidal.SHACL

open L4Factoidal.RDF

/-! ## Empty / target-less shapes graphs -/

/-- §3.1: with no shapes there are no results. -/
theorem validate_empty_conforms (g : Graph) (cfg : ValidationConfig) :
    (validate g ShapesGraph.empty cfg).conforms = true := by
  simp [validate, ShapesGraph.empty, ValidationEnv.conforms]

/-- §2.1: only focus nodes are validated — with no declared target and
(SHACL 1.2 §explicit-shape-target) no sh:shape triple in the data
graph, no shape has a focus node. -/
theorem validate_no_targets_conforms (g : Graph) (sg : ShapesGraph) (cfg : ValidationConfig)
    (h : ∀ s ∈ sg.shapes, s.targets = []) (hl : ∀ t ∈ g, t.p ≠ shShape) :
    (validate g sg cfg).conforms = true := by
  have hf : ∀ s ∈ sg.shapes,
      shapeFocusNodes (cfg.envFor g sg.shapes) g sg.shapes (distinctSubjects g) s = [] := by
    intro s hs
    have he : explicitShapeTargets g s = [] := by
      simp only [explicitShapeTargets, List.map_eq_nil_iff, List.filter_eq_nil_iff,
        Bool.and_eq_true, beq_iff_eq, not_and]
      intro t ht hp
      exact absurd hp (hl t ht)
    simp [shapeFocusNodes, h s hs, he, dedupTerms]
  simp only [validate, ValidationEnv.conforms, List.all_eq_true, List.mem_flatMap]
  rintro x ⟨s, hs, fn, hfn, _⟩
  rw [hf s hs] at hfn
  simp at hfn

/-! ## sh:minCount 0 -/

/-- §4.2.1: `sh:minCount 0` is satisfied by every value-node set. -/
theorem minCount_zero_no_result (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (focus : Term) (s : Shape) (values : List Term) :
    evalAggregateNonRec env g sg focus s values (.minCount 0) = [] := by
  simp [evalAggregateNonRec]

/-! ## sh:not flips conformance -/

/-- §4.6.1 with SHACL 1.2 conformance checking: for a node shape whose
only component is `sh:not r` (and no property shapes), the focus node
produces no result iff it does NOT conform to `r`'s shape — at two
fuel units less, the cost of one nesting level. -/
theorem notOf_flips (env : ValidationEnv) (g : Graph) (sg : List Shape) (v : Term)
    (s rs : Shape) (r : ShapeRef)
    (hc : s.constraints = [.notOf r]) (hp : s.isProperty = false)
    (hr : s.propertyRefs = []) (hl : lookupShape r sg = some rs) (fuel : Nat) :
    (collectShapeViolations env g sg v s (fuel + 2)).isEmpty =
      !env.conforms (collectShapeViolations env g sg v rs fuel) := by
  simp only [collectShapeViolations, evalOneConstraint, evalAggregate, evalAggregateNonRec,
    valueNodes, hc, hp, hr]
  simp only [hl, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  by_cases h : env.conforms (collectShapeViolations env g sg v rs fuel) = true <;> simp [h]

/-! ## §1.4 SHACL instance: the closure walk is sound and complete -/

namespace Spec

theorem SubClassOf.trans {g : Graph} {a b c : WfIri}
    (h1 : SubClassOf g a b) (h2 : SubClassOf g b c) : SubClassOf g a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact SubClassOf.step h (ih h2)

end Spec

/-- Membership in `objectsOf` is membership of the triple. -/
theorem mem_objectsOf_iff (g : Graph) (s : Subject) (p : WfIri) (o : Term) :
    o ∈ objectsOf g s p ↔ ({ s := s, p := p, o := o } : Triple) ∈ g := by
  unfold objectsOf
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨t, ⟨ht, hs, hp⟩, rfl⟩
    cases t; simp_all
  · intro h
    exact ⟨_, ⟨h, rfl, rfl⟩, rfl⟩

theorem mem_directSupers_iff (g : Graph) (c d : WfIri) :
    d ∈ directSupers g c ↔
      ({ s := .iri c, p := rdfsSubClassOf, o := .iri d } : Triple) ∈ g := by
  unfold directSupers
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hd⟩
    cases t <;> simp at hd
    subst hd
    exact (mem_objectsOf_iff ..).mp ht
  · intro h
    exact ⟨.iri d, (mem_objectsOf_iff ..).mpr h, rfl⟩

theorem mem_addNew_iff (acc xs : List WfIri) (x : WfIri) :
    x ∈ addNew acc xs ↔ x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => simp [addNew]
  | cons d rest ih =>
    simp only [addNew, ih, List.mem_cons]
    constructor
    · rintro (h | h)
      · split at h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · left; split
        · exact h
        · exact List.mem_append_left _ h
      · left; split
        · rename_i hc; exact List.contains_iff_mem.mp hc
        · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · exact Or.inr h

theorem addNew_length_ge (acc xs : List WfIri) : acc.length ≤ (addNew acc xs).length := by
  induction xs generalizing acc with
  | nil => simp [addNew]
  | cons d rest ih =>
    simp only [addNew]
    refine Nat.le_trans ?_ (ih _)
    split <;> simp

theorem addNew_length_eq (acc xs : List WfIri)
    (h : (addNew acc xs).length ≤ acc.length) : ∀ x ∈ xs, x ∈ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons d rest ih =>
    simp only [addNew] at h
    intro x hx
    split at h
    · rename_i hc
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.contains_iff_mem.mp hc
      · exact ih acc h x hx'
    · have := addNew_length_ge (acc ++ [d]) rest
      simp at this
      omega

theorem addNew_nodup (acc xs : List WfIri) (h : acc.Nodup) : (addNew acc xs).Nodup := by
  induction xs generalizing acc with
  | nil => simpa [addNew]
  | cons d rest ih =>
    simp only [addNew]
    apply ih
    split
    · exact h
    · rename_i hc
      have hd : d ∉ acc := fun hm => hc (List.contains_iff_mem.mpr hm)
      refine List.nodup_append.mpr ⟨h, List.nodup_cons.mpr ⟨by simp, List.Pairwise.nil⟩, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      exact hd (hab ▸ ha)

theorem mem_superClassesStep_iff (g : Graph) (cs : List WfIri) (x : WfIri) :
    x ∈ superClassesStep g cs ↔ x ∈ cs ∨ ∃ c ∈ cs, x ∈ directSupers g c := by
  simp [superClassesStep, mem_addNew_iff, List.mem_flatMap]

/-- A step that adds nothing means the set is closed under direct supers. -/
theorem superClassesStep_closed (g : Graph) (cs : List WfIri)
    (h : (superClassesStep g cs).length ≤ cs.length) :
    ∀ c ∈ cs, ∀ d ∈ directSupers g c, d ∈ cs := by
  intro c hc d hd
  exact addNew_length_eq cs _ h d (List.mem_flatMap.mpr ⟨c, hc, hd⟩)

theorem mem_superClassesFuel_of_mem (g : Graph) (cs : List WfIri) (k : Nat) (x : WfIri)
    (h : x ∈ cs) : x ∈ superClassesFuel g cs k := by
  induction k generalizing cs with
  | zero => simpa [superClassesFuel]
  | succ k ih =>
    simp only [superClassesFuel]
    split
    · exact h
    · exact ih _ ((mem_superClassesStep_iff ..).mpr (Or.inl h))

/-- Soundness of the walk: everything reached is a SHACL superclass
of something started from. -/
theorem superClassesFuel_sound (g : Graph) (cs : List WfIri) (k : Nat) (x : WfIri)
    (h : x ∈ superClassesFuel g cs k) : ∃ c ∈ cs, Spec.SubClassOf g c x := by
  induction k generalizing cs with
  | zero => exact ⟨x, by simpa [superClassesFuel] using h, Spec.SubClassOf.refl x⟩
  | succ k ih =>
    simp only [superClassesFuel] at h
    split at h
    · exact ⟨x, h, Spec.SubClassOf.refl x⟩
    · obtain ⟨c', hc', hsub⟩ := ih _ h
      rcases (mem_superClassesStep_iff ..).mp hc' with hc | ⟨c, hc, hd⟩
      · exact ⟨c', hc, hsub⟩
      · exact ⟨c, hc, Spec.SubClassOf.step ((mem_directSupers_iff ..).mp hd) hsub⟩

/-- The walk either reaches a closed set or runs out of fuel having
grown by at least one class per step. -/
theorem superClassesFuel_closed_or_long (g : Graph) (k : Nat) (cs : List WfIri) :
    (∀ c ∈ superClassesFuel g cs k, ∀ d ∈ directSupers g c, d ∈ superClassesFuel g cs k) ∨
    (cs.Nodup → (superClassesFuel g cs k).Nodup ∧
      cs.length + k ≤ (superClassesFuel g cs k).length) := by
  induction k generalizing cs with
  | zero =>
    right; intro h; simp only [superClassesFuel]; exact ⟨h, by omega⟩
  | succ k ih =>
    simp only [superClassesFuel]
    split
    · rename_i hle
      left
      exact superClassesStep_closed g cs hle
    · rename_i hlt
      rcases ih (superClassesStep g cs) with h | h
      · left; exact h
      · right
        intro hn
        have hn' : (superClassesStep g cs).Nodup := addNew_nodup _ _ hn
        obtain ⟨h1, h2⟩ := h hn'
        refine ⟨h1, ?_⟩
        have : cs.length < (superClassesStep g cs).length := by omega
        omega

/-- The IRIs that are objects of rdfs:subClassOf triples — the only
classes a walk can add. -/
def subClassObjects (g : Graph) : List WfIri :=
  g.filterMap fun t =>
    if t.p == rdfsSubClassOf then
      match t.o with
      | .iri d => some d
      | _ => none
    else none

theorem mem_subClassObjects_of_directSupers (g : Graph) (c d : WfIri)
    (h : d ∈ directSupers g c) : d ∈ subClassObjects g := by
  have ht := (mem_directSupers_iff ..).mp h
  unfold subClassObjects
  exact List.mem_filterMap.mpr ⟨_, ht, by simp⟩

theorem subClassObjects_length_le (g : Graph) : (subClassObjects g).length ≤ g.length :=
  List.length_filterMap_le _ _

theorem superClassesFuel_subset (g : Graph) (k : Nat) (cs : List WfIri)
    (hcs : ∀ x ∈ cs, x ∈ subClassObjects g ∨ x ∈ cs) :
    ∀ x ∈ superClassesFuel g cs k, x ∈ subClassObjects g ∨ x ∈ cs := by
  induction k generalizing cs with
  | zero => simpa [superClassesFuel] using hcs
  | succ k ih =>
    simp only [superClassesFuel]
    split
    · exact hcs
    · intro x hx
      have hstep : ∀ y ∈ superClassesStep g cs, y ∈ subClassObjects g ∨ y ∈ superClassesStep g cs := by
        intro y hy
        rcases (mem_superClassesStep_iff ..).mp hy with h | ⟨c, _, hd⟩
        · exact Or.inr hy
        · exact Or.inl (mem_subClassObjects_of_directSupers g c y hd)
      rcases ih _ hstep x hx with h | h
      · exact Or.inl h
      · rcases (mem_superClassesStep_iff ..).mp h with h | ⟨c, _, hd⟩
        · exact Or.inr h
        · exact Or.inl (mem_subClassObjects_of_directSupers g c x hd)

/-- Completeness of the walk from `[t]` with fuel `g.length + 1`: a
closed set contains every SHACL superclass; a non-closed run would
hold more distinct classes than rdfs:subClassOf triples plus one. -/
theorem superClasses_complete (g : Graph) (t d : WfIri) (h : Spec.SubClassOf g t d) :
    d ∈ superClasses g t := by
  unfold superClasses
  rcases superClassesFuel_closed_or_long g (g.length + 1) [t] with hclosed | hlong
  · have ht : t ∈ superClassesFuel g [t] (g.length + 1) :=
      mem_superClassesFuel_of_mem g [t] _ t (List.mem_singleton.mpr rfl)
    -- closed sets contain every superclass of every member
    suffices ∀ a c, Spec.SubClassOf g a c → a ∈ superClassesFuel g [t] (g.length + 1) →
        c ∈ superClassesFuel g [t] (g.length + 1) from this t d h ht
    intro a c hac
    induction hac with
    | refl => exact id
    | step hab _ ih =>
      intro ha
      exact ih (hclosed _ ha _ ((mem_directSupers_iff ..).mpr hab))
  · exfalso
    obtain ⟨hnodup, hlen⟩ := hlong (List.nodup_cons.mpr ⟨by simp, List.Pairwise.nil⟩)
    have hsub : superClassesFuel g [t] (g.length + 1) ⊆ t :: subClassObjects g := by
      intro x hx
      rcases superClassesFuel_subset g _ [t] (fun x hx => Or.inr hx) x hx with h | h
      · exact List.mem_cons_of_mem _ h
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
    have h1 := hnodup.length_le_of_subset hsub
    rw [List.length_cons] at h1
    have h2 := subClassObjects_length_le g
    simp at hlen
    omega

theorem superClasses_sound (g : Graph) (t d : WfIri) (h : d ∈ superClasses g t) :
    Spec.SubClassOf g t d := by
  obtain ⟨c, hc, hsub⟩ := superClassesFuel_sound g [t] _ d h
  rw [List.mem_singleton.mp hc] at hsub
  exact hsub

/-- The engine decides §1.4 SHACL instance. -/
theorem isShaclInstance_iff (g : Graph) (n : Term) (c : WfIri) :
    isShaclInstance g n c = true ↔ Spec.IsInstance g n c := by
  unfold isShaclInstance Spec.IsInstance
  cases hs : n.toSubject? with
  | none => simp
  | some s =>
    simp only [List.any_eq_true, Option.some.injEq, exists_and_left, exists_eq_left']
    constructor
    · rintro ⟨t, ht, hmatch⟩
      cases t <;> simp at hmatch
      rename_i ti
      exact ⟨ti, (mem_objectsOf_iff ..).mp ht, superClasses_sound g ti c hmatch⟩
    · rintro ⟨t, ht, hsub⟩
      exact ⟨.iri t, (mem_objectsOf_iff ..).mpr ht,
        List.contains_iff_mem.mpr (superClasses_complete g t c hsub)⟩

/-! ## The per-value components decide their specification -/

/-- The components `simpleValueCheck` answers. -/
def isSimple : Constraint → Bool
  | .cls _ | .datatype _ | .nodeKind _ | .inSet _ | .pattern _ _ | .minLength _
  | .maxLength _ | .languageIn _ | .minInclusive _ | .maxInclusive _
  | .minExclusive _ | .maxExclusive _ | .singleLine _ | .rootClass _
  | .minListLength _ | .maxListLength _ | .uniqueMembers _ => true
  | _ => false

theorem simpleValueCheck_isSome (g : Graph) (cc : Constraint) (v : Term) :
    (simpleValueCheck g cc v).isSome = isSimple cc := by
  cases cc <;> simp [simpleValueCheck, isSimple]

theorem simpleValueCheck_iff (g : Graph) (cc : Constraint) (v : Term) (hs : isSimple cc = true) :
    simpleValueCheck g cc v = some true ↔ Spec.ValueSatisfies g cc v := by
  cases cc with
  | cls cs =>
    simp only [simpleValueCheck, Spec.ValueSatisfies, Option.some.injEq, List.any_eq_true]
    exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, (isShaclInstance_iff g v c).mp h⟩,
           fun ⟨c, hc, h⟩ => ⟨c, hc, (isShaclInstance_iff g v c).mpr h⟩⟩
  | datatype dts =>
    cases v with
    | literal l =>
      simp only [simpleValueCheck, Spec.ValueSatisfies, Option.some.injEq, List.any_eq_true,
        Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Term.literal.injEq, exists_eq_left']
    | _ => simp [simpleValueCheck, Spec.ValueSatisfies]
  | nodeKind nks =>
    simp only [simpleValueCheck, Spec.ValueSatisfies, Option.some.injEq, List.any_eq_true]
    have hk : ∀ nk, nodeKindOk v nk = true ↔ Spec.NodeKindOk nk v := by
      intro nk
      cases nk <;> cases v <;>
        simp [Spec.NodeKindOk, nodeKindOk, isBnodeTerm, isIriTerm, isLiteralTerm,
          isTripleTermTerm]
    exact ⟨fun ⟨nk, hn, h⟩ => ⟨nk, hn, (hk nk).mp h⟩, fun ⟨nk, hn, h⟩ => ⟨nk, hn, (hk nk).mpr h⟩⟩
  | singleLine b =>
    cases v <;> cases b <;>
      simp [simpleValueCheck, Spec.ValueSatisfies, hasLineBreak, List.any_eq_false]
  | rootClass cs =>
    cases v with
    | iri i =>
      simp only [simpleValueCheck, Spec.ValueSatisfies, Option.some.injEq, List.any_eq_true,
        Term.iri.injEq, exists_eq_left']
      exact ⟨fun ⟨c, hc, h⟩ =>
               ⟨c, hc, superClasses_sound g i c (List.contains_iff_mem.mp h)⟩,
             fun ⟨c, hc, h⟩ =>
               ⟨c, hc, List.contains_iff_mem.mpr (superClasses_complete g i c h)⟩⟩
    | _ => simp [simpleValueCheck, Spec.ValueSatisfies]
  | inSet items =>
    simp [simpleValueCheck, Spec.ValueSatisfies, termMem, List.any_eq_true]
  | pattern re flags =>
    cases h : termLexical v <;> simp [simpleValueCheck, Spec.ValueSatisfies, h]
  | minLength n =>
    cases h : termLexical v <;> simp [simpleValueCheck, Spec.ValueSatisfies, h]
  | maxLength n =>
    cases h : termLexical v <;> simp [simpleValueCheck, Spec.ValueSatisfies, h]
  | languageIn langs =>
    cases v with
    | literal l =>
      cases h : l.val.langTag <;>
        simp [simpleValueCheck, Spec.ValueSatisfies, h, List.any_eq_true]
    | _ => simp [simpleValueCheck, Spec.ValueSatisfies]
  | minInclusive t =>
    cases v <;> cases t <;> simp [simpleValueCheck, Spec.ValueSatisfies]
  | maxInclusive t =>
    cases v <;> cases t <;> simp [simpleValueCheck, Spec.ValueSatisfies]
  | minExclusive t =>
    cases v <;> cases t <;> simp [simpleValueCheck, Spec.ValueSatisfies]
  | maxExclusive t =>
    cases v <;> cases t <;> simp [simpleValueCheck, Spec.ValueSatisfies]
  | minListLength n =>
    cases h : shaclListMembers g v <;> simp [simpleValueCheck, Spec.ValueSatisfies, h]
  | maxListLength n =>
    cases h : shaclListMembers g v <;> simp [simpleValueCheck, Spec.ValueSatisfies, h]
  | uniqueMembers b =>
    cases h : shaclListMembers g v with
    | none => simp [simpleValueCheck, Spec.ValueSatisfies, h]
    | some ms =>
      cases b <;> simp [simpleValueCheck, Spec.ValueSatisfies, h, dupMembers,
        List.filter_eq_nil_iff]
  | _ => simp [isSimple] at hs

/-- `simpleValueCheck_iff` without the `isSimple` side condition: for a
component that is not per-value the check is `none` and the
specification is vacuous. -/
theorem simpleValueCheck_ne_none (g : Graph) (cc : Constraint) (v : Term) (hs : isSimple cc = true) :
    simpleValueCheck g cc v ≠ none := by
  intro h
  have := simpleValueCheck_isSome g cc v
  rw [h, hs] at this
  simp at this

theorem simpleValueCheck_iff' (g : Graph) (cc : Constraint) (v : Term) :
    (simpleValueCheck g cc v = some true ∨ simpleValueCheck g cc v = none) ↔
      Spec.ValueSatisfies g cc v := by
  cases cc with
  | cls c =>
    rw [← simpleValueCheck_iff g (.cls c) v rfl]
    simp [simpleValueCheck_ne_none g (.cls c) v rfl]
  | datatype dt =>
    rw [← simpleValueCheck_iff g (.datatype dt) v rfl]
    simp [simpleValueCheck_ne_none g (.datatype dt) v rfl]
  | nodeKind nk =>
    rw [← simpleValueCheck_iff g (.nodeKind nk) v rfl]
    simp [simpleValueCheck_ne_none g (.nodeKind nk) v rfl]
  | inSet items =>
    rw [← simpleValueCheck_iff g (.inSet items) v rfl]
    simp [simpleValueCheck_ne_none g (.inSet items) v rfl]
  | pattern re flags =>
    rw [← simpleValueCheck_iff g (.pattern re flags) v rfl]
    simp [simpleValueCheck_ne_none g (.pattern re flags) v rfl]
  | minLength n =>
    rw [← simpleValueCheck_iff g (.minLength n) v rfl]
    simp [simpleValueCheck_ne_none g (.minLength n) v rfl]
  | maxLength n =>
    rw [← simpleValueCheck_iff g (.maxLength n) v rfl]
    simp [simpleValueCheck_ne_none g (.maxLength n) v rfl]
  | languageIn langs =>
    rw [← simpleValueCheck_iff g (.languageIn langs) v rfl]
    simp [simpleValueCheck_ne_none g (.languageIn langs) v rfl]
  | minInclusive t =>
    rw [← simpleValueCheck_iff g (.minInclusive t) v rfl]
    simp [simpleValueCheck_ne_none g (.minInclusive t) v rfl]
  | maxInclusive t =>
    rw [← simpleValueCheck_iff g (.maxInclusive t) v rfl]
    simp [simpleValueCheck_ne_none g (.maxInclusive t) v rfl]
  | minExclusive t =>
    rw [← simpleValueCheck_iff g (.minExclusive t) v rfl]
    simp [simpleValueCheck_ne_none g (.minExclusive t) v rfl]
  | maxExclusive t =>
    rw [← simpleValueCheck_iff g (.maxExclusive t) v rfl]
    simp [simpleValueCheck_ne_none g (.maxExclusive t) v rfl]
  | singleLine b =>
    rw [← simpleValueCheck_iff g (.singleLine b) v rfl]
    simp [simpleValueCheck_ne_none g (.singleLine b) v rfl]
  | rootClass cs =>
    rw [← simpleValueCheck_iff g (.rootClass cs) v rfl]
    simp [simpleValueCheck_ne_none g (.rootClass cs) v rfl]
  | minListLength n =>
    rw [← simpleValueCheck_iff g (.minListLength n) v rfl]
    simp [simpleValueCheck_ne_none g (.minListLength n) v rfl]
  | maxListLength n =>
    rw [← simpleValueCheck_iff g (.maxListLength n) v rfl]
    simp [simpleValueCheck_ne_none g (.maxListLength n) v rfl]
  | uniqueMembers b =>
    rw [← simpleValueCheck_iff g (.uniqueMembers b) v rfl]
    simp [simpleValueCheck_ne_none g (.uniqueMembers b) v rfl]
  | _ => simp [simpleValueCheck, Spec.ValueSatisfies]

/-! ## The per-focus-node components decide their specification -/

/-- §4.8.1 sh:closed (either form): no result iff `Spec.ClosedOk`. -/
theorem closedViolations_eq_nil_iff (g : Graph) (focus : Term) (s : Shape) (cc : Constraint)
    (values : List Term) (allowed : Subject → List WfIri) :
    closedViolations g focus s cc values allowed = [] ↔ Spec.ClosedOk g values allowed := by
  unfold closedViolations Spec.ClosedOk
  simp only [List.flatMap_eq_nil_iff]
  apply forall_congr'; intro v; apply imp_congr_right; intro _
  cases h : v.toSubject? with
  | none => simp
  | some subj =>
    simp only [List.filterMap_eq_nil_iff, Option.some.injEq, forall_eq']
    constructor
    · intro hall t ht hts
      have := hall t ht
      split at this
      · exact absurd this (by simp)
      · rename_i hcond
        simp only [hts, beq_self_eq_true, Bool.true_and, Bool.not_eq_true',
          Bool.not_eq_false] at hcond
        first
          | exact List.contains_iff_mem.mp hcond
          | exact hcond
    · intro hall t ht
      by_cases hts : t.s = subj
      · have hc : (allowed subj).contains t.p = true :=
          List.contains_iff_mem.mpr (hall t ht hts)
        simp only [hts, hc, beq_self_eq_true, Bool.true_and, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
      · simp [hts]

theorem closedViolations_severity (g : Graph) (focus : Term) (s : Shape) (cc : Constraint)
    (values : List Term) (allowed : Subject → List WfIri) :
    ∀ x ∈ closedViolations g focus s cc values allowed, x.severity = s.severityOf cc := by
  intro x hx
  obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hx
  split at hv
  · simp at hv
  · obtain ⟨t, _, ht⟩ := List.mem_filterMap.mp hv
    split at ht
    · cases ht; rfl
    · cases ht

/-- SHACL 1.2 sh:uniqueValuesFor: no clash iff no other target node
shares the value node's key. -/
theorem uvfClash_eq_false_iff (g : Graph) (targets : List Term) (props : List WfIri) (v : Term) :
    uvfClash g targets props v = false ↔
      ∀ k, uvfKey g v props = some k → ∀ t ∈ targets, Term.sameTerm t v = false →
        ∀ k2, uvfKey g t props = some k2 → keyEq k k2 = false := by
  unfold uvfClash
  cases hk : uvfKey g v props with
  | none => simp
  | some k =>
    simp only [Option.some.injEq, forall_eq', List.any_eq_false, Bool.and_eq_true,
      Bool.not_eq_true', not_and]
    apply forall_congr'; intro t; apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    cases hk2 : uvfKey g t props with
    | none => simp
    | some k2 => simp

theorem termMem_iff (t : Term) (l : List Term) :
    termMem t l = true ↔ ∃ u ∈ l, Term.sameTerm u t = true := by
  simp [termMem, List.any_eq_true]

theorem evalAggregateNonRec_eq_nil_iff (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (focus : Term) (s : Shape) (values : List Term) (cc : Constraint) :
    evalAggregateNonRec env g sg focus s values cc = [] ↔
      Spec.FocusSatisfies env g sg focus s cc values := by
  cases cc with
  | uniqueValuesFor props =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies, List.filterMap_eq_nil_iff]
    apply forall_congr'; intro v; apply imp_congr_right; intro _
    rw [← uvfClash_eq_false_iff]
    cases uvfClash g (env.targetsOf s.id) props v <;> simp
  | minCount n =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies]
    split <;> simp <;> omega
  | maxCount n =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies]
    split <;> simp <;> omega
  | hasValue t =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies]
    split <;> simp_all [termMem_iff]
  | uniqueLang b =>
    cases b <;> simp [evalAggregateNonRec, Spec.FocusSatisfies]
  | closed ignored =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies]
    exact closedViolations_eq_nil_iff g focus s _ values _
  | closedByTypes table ignored =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies]
    exact closedViolations_eq_nil_iff g focus s _ values _
  | equals p =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies, List.append_eq_nil_iff,
      List.filterMap_eq_nil_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, fun o ho => ?_⟩
      · have := h1 v hv
        simpa [termMem_iff] using this
      · have := h2 o ho
        simpa [termMem_iff] using this
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, fun o ho => ?_⟩
      · simp [termMem_iff, h1 v hv]
      · simp [termMem_iff, h2 o ho]
  | disjoint p =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies, List.filterMap_eq_nil_iff]
    constructor
    · intro h v hv hmem
      have := h v hv
      simp [termMem_iff, hmem] at this
    · intro h v hv
      have := h v hv
      simp [termMem_iff, this]
  | subsetOf p =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies, List.filterMap_eq_nil_iff]
    constructor
    · intro h v hv
      have := h v hv
      simpa [termMem_iff] using this
    · intro h v hv
      simp [termMem_iff, h v hv]
  | lessThan p =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies, List.flatMap_eq_nil_iff,
      List.filterMap_eq_nil_iff]
    constructor
    · intro h v hv w hw
      have := h v hv w hw
      simpa using this
    · intro h v hv w hw
      simp [h v hv w hw]
  | lessThanOrEquals p =>
    simp only [evalAggregateNonRec, Spec.FocusSatisfies, List.flatMap_eq_nil_iff,
      List.filterMap_eq_nil_iff]
    constructor
    · intro h v hv w hw
      have := h v hv w hw
      simpa using this
    · intro h v hv w hw
      simp [h v hv w hw]
  | _ => simp [evalAggregateNonRec, Spec.FocusSatisfies]

/-! ## §3.4: SHACL 1.2 conformance checking, at every fuel -/

/-- A list of results that all carry the severity `sev` conforms iff it
is empty or `sev` is outside the disallowed set. -/
theorem conforms_uniform (env : ValidationEnv) (sev : Severity) (l : List Violation)
    (h : ∀ x ∈ l, x.severity = sev) :
    env.conforms l = true ↔ (env.blocks sev = true → l = []) := by
  unfold ValidationEnv.conforms
  constructor
  · intro hall hb
    cases l with
    | nil => rfl
    | cons x xs =>
      exfalso
      have hx := (List.all_eq_true.mp hall) x List.mem_cons_self
      rw [h x List.mem_cons_self, hb] at hx
      simp at hx
  · intro himp
    rw [List.all_eq_true]
    intro x hx
    cases hb : env.blocks sev with
    | false => rw [h x hx, hb]; rfl
    | true => rw [himp hb] at hx; simp at hx

theorem conforms_append (env : ValidationEnv) (l1 l2 : List Violation) :
    env.conforms (l1 ++ l2) = (env.conforms l1 && env.conforms l2) := by
  simp [ValidationEnv.conforms]

theorem conforms_flatMap {α : Type} (env : ValidationEnv) (l : List α) (f : α → List Violation) :
    env.conforms (l.flatMap f) = true ↔ ∀ a ∈ l, env.conforms (f a) = true := by
  simp [ValidationEnv.conforms]

theorem conforms_nil (env : ValidationEnv) : env.conforms [] = true := rfl

/-- Every result of one per-value component carries the constraint's
severity (`Shape.severityOf`). -/
theorem evalOneConstraint_severity (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (focus : Term) (s : Shape) (v : Term) (cc : Constraint) (fuel : Nat) :
    ∀ x ∈ evalOneConstraint env g sg focus s v cc fuel, x.severity = s.severityOf cc := by
  intro x hx
  cases fuel with
  | zero => simp [evalOneConstraint] at hx
  | succ n =>
    cases cc with
    | nodeByExpression expr =>
      simp only [evalOneConstraint] at hx
      obtain ⟨st, _, hst⟩ := List.mem_filterMap.mp hx
      split at hst
      · cases hst
      · split at hst
        · cases hst
        · split at hst
          · cases hst
          · cases hst; rfl
    | reifierShape r required =>
      simp only [evalOneConstraint] at hx
      split at hx
      · simp at hx
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · split at hx <;> simp_all [valueViolation]
        · split at hx
          · simp at hx
          · obtain ⟨_, _, ht⟩ := List.mem_filterMap.mp hx
            split at ht
            · cases ht
            · cases ht; rfl
    | _ =>
      simp only [evalOneConstraint] at hx
      (repeat' split at hx) <;> simp_all [valueViolation]

/-- Every result of one per-focus-node component carries the
constraint's severity. -/
theorem evalAggregateNonRec_severity (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (focus : Term) (s : Shape) (values : List Term) (cc : Constraint) :
    ∀ x ∈ evalAggregateNonRec env g sg focus s values cc, x.severity = s.severityOf cc := by
  intro x hx
  cases cc with
  | uniqueValuesFor props =>
    simp only [evalAggregateNonRec] at hx
    obtain ⟨_, _, ht⟩ := List.mem_filterMap.mp hx
    split at ht
    · cases ht; rfl
    · cases ht
  | minCount n | maxCount n | hasValue n =>
    simp only [evalAggregateNonRec] at hx
    split at hx <;> simp_all [focusViolation]
  | uniqueLang b =>
    simp only [evalAggregateNonRec] at hx
    split at hx
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl
    · simp at hx
  | closed ignored | closedByTypes _ ignored =>
    simp only [evalAggregateNonRec] at hx
    exact closedViolations_severity g focus s _ values _ x hx
  | equals p =>
    simp only [evalAggregateNonRec, List.mem_append] at hx
    rcases hx with hx | hx <;>
    · obtain ⟨_, _, ht⟩ := List.mem_filterMap.mp hx
      split at ht
      · cases ht
      · cases ht; rfl
  | disjoint p =>
    simp only [evalAggregateNonRec] at hx
    obtain ⟨_, _, ht⟩ := List.mem_filterMap.mp hx
    split at ht
    · cases ht; rfl
    · cases ht
  | subsetOf p =>
    simp only [evalAggregateNonRec] at hx
    obtain ⟨_, _, ht⟩ := List.mem_filterMap.mp hx
    split at ht
    · cases ht
    · cases ht; rfl
  | lessThan p | lessThanOrEquals p =>
    simp only [evalAggregateNonRec] at hx
    obtain ⟨_, _, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨_, _, ht⟩ := List.mem_filterMap.mp hx
    split at ht
    · cases ht
    · cases ht; rfl
  | _ => simp [evalAggregateNonRec] at hx

/-- Every result of a qualified-cardinality or sh:someValue component
carries the constraint's severity. -/
theorem evalAggregate_severity (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (focus : Term) (s : Shape) (values : List Term) (cc : Constraint) (fuel : Nat) :
    ∀ x ∈ evalAggregate env g sg focus s values cc fuel, x.severity = s.severityOf cc := by
  intro x hx
  cases fuel with
  | zero => simp [evalAggregate] at hx
  | succ n =>
    simp only [evalAggregate] at hx
    split at hx <;> (repeat' split at hx) <;> simp_all [focusViolation]

theorem evalAggregate_eq_nil_iff (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (focus : Term) (s : Shape) (values : List Term) (cc : Constraint) (fuel : Nat) :
    evalAggregate env g sg focus s values cc fuel = [] ↔
      Spec.AggConforms env g sg s values cc fuel := by
  cases fuel with
  | zero => simp [evalAggregate, Spec.AggConforms]
  | succ n =>
    cases cc with
    | someValue r =>
      simp only [evalAggregate, Spec.AggConforms]
      cases hl : lookupShape r sg with
      | none => simp
      | some rs =>
        simp only [Option.some.injEq, forall_eq']
        split <;> simp_all
    | _ =>
      simp only [evalAggregate, Spec.AggConforms] <;> first | simp | (split <;> simp_all)

theorem ite_eq_left_iff_nil {β : Type} (c : Prop) [Decidable c] (v : β) :
    (if c then ([] : List β) else [v]) = [] ↔ c := by
  split <;> simp_all

theorem ite_nil_all_iff {α β : Type} (l : List α) (P : α → Bool) (viol : List β)
    (hv : viol ≠ []) : (if l.all P then [] else viol) = [] ↔ ∀ r ∈ l, P r = true := by
  split <;> simp_all [List.all_eq_true]

theorem ite_nil_any_iff {α β : Type} (l : List α) (P : α → Bool) (viol : List β)
    (hv : viol ≠ []) : (if l.any P then [] else viol) = [] ↔ ∃ r ∈ l, P r = true := by
  split <;> simp_all [List.any_eq_true]

theorem conforms_evalOne (env : ValidationEnv) (g : Graph) (sg : List Shape) (focus : Term)
    (s : Shape) (v : Term) (cc : Constraint) (n : Nat) :
    env.conforms (evalOneConstraint env g sg focus s v cc n) = true ↔
      (env.blocks (s.severityOf cc) = true → evalOneConstraint env g sg focus s v cc n = []) :=
  conforms_uniform env _ _ (evalOneConstraint_severity env g sg focus s v cc n)

theorem conforms_aggNonRec (env : ValidationEnv) (g : Graph) (sg : List Shape) (focus : Term)
    (s : Shape) (values : List Term) (cc : Constraint) :
    env.conforms (evalAggregateNonRec env g sg focus s values cc) = true ↔
      (env.blocks (s.severityOf cc) = true → evalAggregateNonRec env g sg focus s values cc = []) :=
  conforms_uniform env _ _ (evalAggregateNonRec_severity env g sg focus s values cc)

theorem conforms_agg (env : ValidationEnv) (g : Graph) (sg : List Shape) (focus : Term)
    (s : Shape) (values : List Term) (cc : Constraint) (n : Nat) :
    env.conforms (evalAggregate env g sg focus s values cc n) = true ↔
      (env.blocks (s.severityOf cc) = true → evalAggregate env g sg focus s values cc n = []) :=
  conforms_uniform env _ _ (evalAggregate_severity env g sg focus s values cc n)

/-- The two judgments of the mutual group, by induction on the fuel:
the engine's results for a focus node and a shape pass SHACL 1.2
conformance checking iff `Spec.Conforms` holds, and one per-value
component produces no result iff `Spec.ValueConforms` holds. -/
theorem conformance_iff (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (hcoh : env.dataIx.Coherent g) : ∀ fuel : Nat,
    (∀ node s, env.conforms (collectShapeViolations env g sg node s fuel) = true ↔
      Spec.Conforms env g sg node s fuel) ∧
    (∀ focus s v cc, evalOneConstraint env g sg focus s v cc fuel = [] ↔
      Spec.ValueConforms env g sg focus s v cc fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun node s => ?_, fun focus s v cc => ?_⟩
    · simp [collectShapeViolations, Spec.Conforms, ValidationEnv.conforms]
    · simp [evalOneConstraint, Spec.ValueConforms]
  | succ n ih =>
    obtain ⟨ihc, ihv⟩ := ih
    refine ⟨fun node s => ?_, fun focus s v cc => ?_⟩
    · simp only [collectShapeViolations, Spec.Conforms, conforms_append, Bool.and_eq_true,
        conforms_flatMap, conforms_evalOne, conforms_aggNonRec, conforms_agg, ihv,
        evalAggregateNonRec_eq_nil_iff, evalAggregate_eq_nil_iff]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨fun cc hcc hb => ⟨fun v hv => h1 v hv cc hcc hb, h2 cc hcc hb, h3 cc hcc hb⟩,
          fun v hv r hr ps hps => ?_⟩
        have := h4 v hv r hr
        simp only [hps] at this
        exact (ihc v ps).mp this
      · rintro ⟨h1, h4⟩
        refine ⟨⟨⟨fun v hv cc hcc hb => (h1 cc hcc hb).1 v hv,
          fun cc hcc hb => (h1 cc hcc hb).2.1⟩, fun cc hcc hb => (h1 cc hcc hb).2.2⟩,
          fun v hv r hr => ?_⟩
        cases hps : lookupShape r sg with
        | none => exact conforms_nil env
        | some ps => exact (ihc v ps).mpr (h4 v hv r hr ps hps)
    · cases cc with
      | notOf r =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        cases hl : lookupShape r sg with
        | none => simp
        | some rs =>
          simp only [Option.some.injEq, forall_eq']
          rw [← ihc v rs]
          split <;> simp_all
      | andOf rs =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        rw [ite_nil_all_iff _ _ _ (List.cons_ne_nil _ _)]
        constructor
        · intro h r hr s2 hs2
          have := h r hr
          simp only [hs2] at this
          exact (ihc v s2).mp this
        · intro h r hr
          cases hs2 : lookupShape r sg with
          | none => rfl
          | some s2 => exact (ihc v s2).mpr (h r hr s2 hs2)
      | orOf rs =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        rw [ite_nil_any_iff _ _ _ (List.cons_ne_nil _ _)]
        constructor
        · rintro ⟨r, hr, hok⟩
          cases hs2 : lookupShape r sg with
          | none => simp [hs2] at hok
          | some s2 =>
            simp only [hs2] at hok
            exact ⟨r, hr, s2, hs2, (ihc v s2).mp hok⟩
        · rintro ⟨r, hr, s2, hs2, hc⟩
          refine ⟨r, hr, ?_⟩
          simp only [hs2]
          exact (ihc v s2).mpr hc
      | xoneOf rs =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        split <;> simp_all
      | nodeOf r =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        cases hl : lookupShape r sg with
        | none => simp
        | some s2 =>
          simp only [Option.some.injEq, forall_eq']
          rw [← ihc v s2]
          split <;> simp_all
      | nodeByExpression expr =>
        simp only [evalOneConstraint, Spec.ValueConforms, List.filterMap_eq_nil_iff]
        apply forall_congr'; intro st; apply imp_congr_right; intro _
        cases hr : termToShapeRef st with
        | none => simp
        | some r =>
          simp only [Option.some.injEq, forall_eq']
          cases hl : lookupShape r sg with
          | none => simp
          | some s2 =>
            simp only [Option.some.injEq, forall_eq']
            rw [← ihc v s2]
            split <;> simp_all
      | reifierShape r required =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        cases ht : reifiedTripleOf focus s with
        | none => simp
        | some fp =>
          obtain ⟨fs, p⟩ := fp
          simp only [List.append_eq_nil_iff]
          have hmiss : ((if required && (reifiersOf g fs p v).isEmpty then
                [valueViolation focus s (.reifierShape r required) v] else []) = []) ↔
              (required = true → reifiersOf g fs p v ≠ []) := by
            cases required <;> cases h : reifiersOf g fs p v <;> simp
          rw [hmiss]
          apply and_congr_right; intro _
          cases hl : lookupShape r sg with
          | none => simp
          | some s2 =>
            simp only [Option.some.injEq, forall_eq', List.filterMap_eq_nil_iff]
            apply forall_congr'; intro x; apply imp_congr_right; intro _
            rw [← ihc x s2]
            split <;> simp_all
      | memberShape r =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        cases hm : shaclListMembers g v with
        | none => simp
        | some members =>
          cases hl : lookupShape r sg with
          | none => simp
          | some s2 =>
            simp only [Option.some.injEq, exists_eq_left', forall_eq']
            rw [ite_eq_left_iff_nil]
            simp only [List.isEmpty_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
              Bool.not_eq_false, List.mem_eraseDups]
            exact ⟨fun h m hm' => (ihc m s2).mp (h m hm'), fun h m hm' => (ihc m s2).mpr (h m hm')⟩
      | _ =>
        simp only [evalOneConstraint, Spec.ValueConforms]
        rw [← simpleValueCheck_iff' g _ v, simpleValueCheckIx_eq hcoh]
        split <;> simp_all

/-- SHACL 1.2 conformance checking for one focus node and one shape:
the engine's results pass iff `Spec.Conforms` holds, at every fuel. -/
theorem collectShapeViolations_conforms_iff (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (hcoh : env.dataIx.Coherent g) (node : Term) (s : Shape) (fuel : Nat) :
    env.conforms (collectShapeViolations env g sg node s fuel) = true ↔
      Spec.Conforms env g sg node s fuel :=
  (conformance_iff env g sg hcoh fuel).1 node s

/-- No result at all is, in particular, conformance (whatever the
disallowed set). -/
theorem collectShapeViolations_eq_nil_conforms (env : ValidationEnv) (g : Graph)
    (sg : List Shape) (hcoh : env.dataIx.Coherent g) (node : Term) (s : Shape) (fuel : Nat)
    (h : collectShapeViolations env g sg node s fuel = []) :
    Spec.Conforms env g sg node s fuel :=
  (collectShapeViolations_conforms_iff env g sg hcoh node s fuel).mp (by rw [h]; rfl)

/-- SHACL 1.2 §SomeValueConstraintComponent, declaratively: the
engine-named clause of `Spec.AggConforms` for sh:someValue is "some
value node conforms to the shape" in the sense of `Spec.Conforms`. -/
theorem someValue_aggConforms_iff (env : ValidationEnv) (g : Graph) (sg : List Shape)
    (hcoh : env.dataIx.Coherent g)
    (s : Shape) (values : List Term) (r : ShapeRef) (fuel : Nat) :
    Spec.AggConforms env g sg s values (.someValue r) (fuel + 1) ↔
      ∀ rs, lookupShape r sg = some rs → ∃ v ∈ values, Spec.Conforms env g sg v rs fuel := by
  simp only [Spec.AggConforms, collectShapeViolations_conforms_iff env g sg hcoh]

/-- The environment of a validation run carries an index coherent with the
data graph, so the theorems above that assume coherence hold for `validate`
without a hypothesis (https://github.com/danbri/factoidal/issues/723). -/
theorem envFor_dataIx_coherent (cfg : ValidationConfig) (g : Graph) (shapes : List Shape) :
    (cfg.envFor g shapes).dataIx.Coherent g :=
  DataIndex.ofGraph_coherent g

/-- §3.1 / SHACL 1.2 §conformance-definition: the report conforms iff
every focus node of every targeted shape conforms. -/
theorem validate_conforms_iff (g : Graph) (sg : ShapesGraph) (cfg : ValidationConfig) :
    (validate g sg cfg).conforms = true ↔ Spec.GraphConforms (cfg.envFor g sg.shapes) g sg := by
  simp only [validate, Spec.GraphConforms, conforms_flatMap,
    collectShapeViolations_conforms_iff _ g _ (envFor_dataIx_coherent cfg g sg.shapes)]

/-- Soundness in the direction the name suggests: a conforming report
is a certificate of §3.4 conformance for every targeted focus node. -/
theorem validate_sound (g : Graph) (sg : ShapesGraph) (cfg : ValidationConfig)
    (h : (validate g sg cfg).conforms = true) :
    Spec.GraphConforms (cfg.envFor g sg.shapes) g sg :=
  (validate_conforms_iff g sg cfg).mp h

/-! ## Axiom audit -/

#print axioms validate_empty_conforms
#print axioms envFor_dataIx_coherent
#print axioms evalPathFuelIx_eq
#print axioms isShaclInstanceIx_eq
#print axioms simpleValueCheckIx_eq
#print axioms validate_no_targets_conforms
#print axioms minCount_zero_no_result
#print axioms notOf_flips
#print axioms isShaclInstance_iff
#print axioms simpleValueCheck_iff
#print axioms evalAggregateNonRec_eq_nil_iff
#print axioms collectShapeViolations_conforms_iff
#print axioms collectShapeViolations_eq_nil_conforms
#print axioms conforms_uniform
#print axioms someValue_aggConforms_iff
#print axioms validate_conforms_iff
#print axioms validate_sound
#print axioms closedViolations_eq_nil_iff
#print axioms uvfClash_eq_false_iff
#print axioms evalOneConstraint_severity
#print axioms conformance_iff

end L4Factoidal.SHACL
