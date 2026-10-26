/-
L4Factoidal.RDF.EntailmentGeneralize — the generalisation step of the
graph-entailment procedure is licensed by the RDF 1.2 rule rows.

`RDF.Regime.generalize` (`RDF/Entailment.lean`) adds, before the
regime's closure runs, the conclusions of the three RDF 1.2 entailment
patterns that mint a blank node: rdfD1 (RDF 1.2 Semantics §8.1.1),
rdfs14 and rdfs14a (§9.2.1). The rows are transcribed, engine-free, as
`RdfD1Derives` (`RDF/EntailmentRdfSpec.lean`), `Rdfs14Derives` and
`Rdfs14aDerives` (`RDF/EntailmentRdfsSpec.lean`).

`surrogateTriples_licensed` is the refinement statement: every triple
the step adds is one of the two conclusions of an rdfD1 or rdfs14 row
instance, or the conclusion of rdfs14a, in each case for a label that
is FRESH for the input graph at every depth (`BnodeFreshFor`). The
freshness half is `freshLabelPrefix_fresh`: a label that starts with
`freshLabelPrefix g` is longer than every label of `g`.

What is NOT proved here: that the rows are TRUE in every RDF / RDFS
interpretation. The model theory of `RDF/EntailmentRdfsModelTheory.lean`
has no condition for the datatype clause of §8 ("For every IRI aaa in D,
< x, I(aaa) > is in IEXT(I(rdf:type)) if and only if x is in the value
space of I(aaa)") nor for the proposition clause of §9, so the rows
cannot yet be checked against it. The step is used only by
`regimeEntails` / `regimeInconsistent` for `.rdf`, `.rdfs` and
`.rdfsPlus`, none of which carries a model-theoretic soundness theorem;
`.simple` and `.d` are unchanged (`generalize_simple`, `generalize_d`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Entailment
import L4Factoidal.RDF.EntailmentRdfsSpec

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-! ## The two regimes left unchanged -/

theorem generalize_simple (D : List WfIri) (g : Graph) :
    Regime.generalize .simple D g = g := rfl

theorem generalize_d (D : List WfIri) (g : Graph) :
    Regime.generalize .d D g = g := rfl

/-! ## The engine's term operations are the specification's -/

theorem termMentions_iff (x : Term) :
    ∀ t : Term, termMentions x t = true ↔ TermAppearsIn x t
  | .iri i => by simp [termMentions, TermAppearsIn]
  | .bnode b => by simp [termMentions, TermAppearsIn]
  | .literal l => by simp [termMentions, TermAppearsIn]
  | .tripleTerm s p o => by
      simp [termMentions, TermAppearsIn, termMentions_iff x o]

theorem replaceTermIn_eq_termSubst (x r : Term) :
    ∀ t : Term, replaceTermIn x r t = termSubst x r t
  | .iri i => by simp [replaceTermIn, termSubst]
  | .bnode b => by simp [replaceTermIn, termSubst]
  | .literal l => by simp [replaceTermIn, termSubst]
  | .tripleTerm s p o => by
      simp [replaceTermIn, termSubst, replaceTermIn_eq_termSubst x r o]

/-! ## Freshness -/

theorem le_foldl_max_init (l : List Nat) : ∀ init : Nat, init ≤ l.foldl max init := by
  induction l with
  | nil => intro init; exact Nat.le_refl _
  | cons a rest ih =>
      intro init
      exact Nat.le_trans (Nat.le_max_left init a) (ih (max init a))

theorem le_foldl_max (l : List Nat) : ∀ init : Nat, ∀ a ∈ l, a ≤ l.foldl max init := by
  induction l with
  | nil => intro _ a ha; cases ha
  | cons b rest ih =>
      intro init a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact Nat.le_trans (Nat.le_max_right init a) (le_foldl_max_init rest (max init a))
      · exact ih (max init b) a ha'

theorem mentionsBnode_mem_labels (b : BNodeId) :
    ∀ t : Term, TermMentionsBnode b t → b ∈ t.bnodeLabels
  | .iri _, h => by simp [TermMentionsBnode] at h
  | .bnode c, h => by simp [TermMentionsBnode] at h; simp [Term.bnodeLabels, h]
  | .literal _, h => by simp [TermMentionsBnode] at h
  | .tripleTerm s p o, h => by
      simp only [TermMentionsBnode] at h
      rcases h with hs | ho
      · subst hs; simp [Term.bnodeLabels]
      · simp [Term.bnodeLabels, mentionsBnode_mem_labels b o ho]

theorem length_freshLabelPrefix (g : Graph) :
    (freshLabelPrefix g).length = (g.bnodeLabels.map String.length).foldl max 0 + 1 := by
  simp [freshLabelPrefix]

/-- Every label that starts with `freshLabelPrefix g` is fresh for `g`,
triple-term interiors included. -/
theorem freshLabelPrefix_fresh (g : Graph) (suffix : String) :
    BnodeFreshFor (freshLabelPrefix g ++ suffix) g := by
  have hlong : ∀ c ∈ g.bnodeLabels, c ≠ freshLabelPrefix g ++ suffix := by
    intro c hc heq
    have h1 : c.length ≤ (g.bnodeLabels.map String.length).foldl max 0 :=
      le_foldl_max _ 0 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have h2 : (freshLabelPrefix g ++ suffix).length
        = (g.bnodeLabels.map String.length).foldl max 0 + 1 + suffix.length := by
      rw [String.length_append, length_freshLabelPrefix]
    rw [heq, h2] at h1
    omega
  intro t ht
  constructor
  · intro hs
    apply hlong _ _ rfl
    exact List.mem_flatMap.mpr ⟨t, ht, by simp [hs]⟩
  · intro hm
    apply hlong _ _ rfl
    exact List.mem_flatMap.mpr ⟨t, ht,
      List.mem_append_right _ (mentionsBnode_mem_labels _ _ hm)⟩

/-! ## Where a generalised term comes from -/

/-- The classification of a generalisable term: a literal with a
recognised datatype, typed into that datatype; or (when `props`) a
triple term, typed into `rdfs:Proposition`. Either way it appears in
the object chain it was read from. -/
theorem mem_generalisableTerms {D : List WfIri} {props : Bool} {x : Term} {c : WfIri} :
    ∀ {o : Term}, (x, c) ∈ generalisableTerms D props o →
      TermAppearsIn x o ∧
      ((∃ l : WfLiteral, x = .literal l ∧ c = l.val.datatype ∧ l.val.datatype ∈ D) ∨
       (props = true ∧ c = rdfsProposition ∧
         ∃ (s : Subject) (p : WfIri) (o' : Term), x = .tripleTerm s p o'))
  | .iri _, h => by simp [generalisableTerms] at h
  | .bnode _, h => by simp [generalisableTerms] at h
  | .literal l, h => by
      simp only [generalisableTerms] at h
      split at h
      · rename_i hD
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [TermAppearsIn], Or.inl ⟨l, rfl, rfl, List.contains_iff_mem.mp hD⟩⟩
      · cases h
  | .tripleTerm s p o, h => by
      simp only [generalisableTerms, List.mem_append] at h
      rcases h with h | h
      · split at h
        · rename_i hp
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Or.inl rfl, Or.inr ⟨hp, rfl, s, p, o, rfl⟩⟩
        · cases h
      · obtain ⟨happ, hcls⟩ := mem_generalisableTerms h
        exact ⟨Or.inr happ, hcls⟩

/-- The duplicate-free fold keeps only elements of its input. -/
theorem mem_dedupFold {α : Type} (key : α → Term) :
    ∀ (l acc : List α) (k : α),
      k ∈ l.foldl (fun acc k => if acc.any (fun a => key a == key k) then acc else acc ++ [k]) acc →
      k ∈ acc ∨ k ∈ l
  | [], acc, k, h => Or.inl h
  | a :: rest, acc, k, h => by
      simp only [List.foldl_cons] at h
      rcases mem_dedupFold key rest _ k h with h' | h'
      · split at h'
        · exact Or.inl h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h''
            exact Or.inr (h'' ▸ List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_generalisedTermsOf {D : List WfIri} {props : Bool} {g : Graph}
    {k : Term × WfIri} (h : k ∈ generalisedTermsOf D props g) :
    ∃ u ∈ g, k ∈ generalisableTerms D props u.o := by
  unfold generalisedTermsOf at h
  rcases mem_dedupFold Prod.fst _ [] k h with h' | h'
  · cases h'
  · exact List.mem_flatMap.mp h'

/-! ## The refinement statement -/

/-- Shared shape of the two row relations: the generalised term `x`
appears in the object chain of `u ∈ g` and has class `c`; the
conclusion pair is `ttt[x/_:b]` and `_:b rdf:type c`. -/
theorem row_of_key {D : List WfIri} {props : Bool} {g : Graph} {x : Term} {c : WfIri}
    {b : BNodeId} {u : Triple} (hfresh : BnodeFreshFor b g) (hu : u ∈ g)
    (happ : TermAppearsIn x u.o)
    (hcls : (∃ l : WfLiteral, x = .literal l ∧ c = l.val.datatype ∧ l.val.datatype ∈ D) ∨
       (props = true ∧ c = rdfsProposition ∧
         ∃ (s : Subject) (p : WfIri) (o' : Term), x = .tripleTerm s p o')) :
    RdfD1Derives (fun d => d ∈ D) g b
        { s := u.s, p := u.p, o := termSubst x (.bnode b) u.o }
        { s := .bnode b, p := rdfType, o := .iri c } ∨
    (props = true ∧ Rdfs14Derives g b
        { s := u.s, p := u.p, o := termSubst x (.bnode b) u.o }
        { s := .bnode b, p := rdfType, o := .iri c }) := by
  rcases hcls with ⟨l, rfl, rfl, hD⟩ | ⟨hp, rfl, s, p, o', rfl⟩
  · exact Or.inl ⟨hfresh, u, hu, l, happ, hD, rfl, rfl⟩
  · exact Or.inr ⟨hp, hfresh, u, hu, s, p, o', happ, rfl, rfl⟩

/-- **Every triple the generalisation step adds is licensed** by an
RDF 1.2 row instance whose minted label is fresh for the input graph:
it is `ttt[x/_:b]` or `_:b rdf:type c` for an rdfD1 or (RDFS regimes
only) rdfs14 instance, or the rdfs14a conclusion. -/
theorem surrogateTriples_licensed {D : List WfIri} {props : Bool} {g : Graph} {t : Triple}
    (ht : t ∈ surrogateTriples D props g) :
    (∃ b t1 t2, (RdfD1Derives (fun d => d ∈ D) g b t1 t2 ∨
                 (props = true ∧ Rdfs14Derives g b t1 t2)) ∧ (t = t1 ∨ t = t2)) ∨
    (props = true ∧ ∃ b, Rdfs14aDerives g b t) := by
  unfold surrogateTriples at ht
  simp only [List.mem_append] at ht
  rcases ht with (htyped | hrepl) | hprop
  · -- `_:b rdf:type c` for a key `(x, c)` labelled `pre ++ i`
    obtain ⟨⟨x, c, b⟩, hkey, rfl⟩ := List.mem_map.mp htyped
    obtain ⟨⟨k, i⟩, hzi, hk⟩ := List.mem_map.mp hkey
    simp only [Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    obtain ⟨u, hu, hmem⟩ := mem_generalisedTermsOf (List.fst_mem_of_mem_zipIdx hzi)
    obtain ⟨happ, hcls⟩ := mem_generalisableTerms hmem
    exact Or.inl ⟨_, _, _,
      row_of_key (freshLabelPrefix_fresh g _) hu happ hcls, Or.inr rfl⟩
  · -- `ttt[x/_:b]` for a triple `u` of `g` in which `x` appears
    obtain ⟨u, hu, hu'⟩ := List.mem_flatMap.mp hrepl
    obtain ⟨⟨x, c, b⟩, hkey, hsome⟩ := List.mem_filterMap.mp hu'
    obtain ⟨⟨k, i⟩, hzi, hk⟩ := List.mem_map.mp hkey
    simp only [Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    dsimp only at hsome
    split at hsome
    · rename_i hment
      cases hsome
      obtain ⟨u', _, hmem⟩ := mem_generalisedTermsOf (List.fst_mem_of_mem_zipIdx hzi)
      obtain ⟨_, hcls⟩ := mem_generalisableTerms hmem
      refine Or.inl ⟨freshLabelPrefix g ++ toString i, _, _,
        row_of_key (freshLabelPrefix_fresh g (toString i)) hu
          ((termMentions_iff _ _).mp hment) hcls,
        Or.inl ?_⟩
      rw [replaceTermIn_eq_termSubst]
    · cases hsome
  · -- rdfs14a's `_:pre rdf:type rdfs:Proposition`
    split at hprop
    · rename_i hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hprop
      subst hprop
      refine Or.inr ⟨hp, freshLabelPrefix g, ?_, rfl⟩
      have := freshLabelPrefix_fresh g ""
      rwa [String.append_empty] at this
    · cases hprop

/-- The generalised graph is the input plus licensed triples. -/
theorem generalize_licensed {r : Regime} {D : List WfIri} {g : Graph} {t : Triple}
    (ht : t ∈ r.generalize D g) :
    t ∈ g ∨
    (∃ b t1 t2, (RdfD1Derives (fun d => d ∈ D) g b t1 t2 ∨ Rdfs14Derives g b t1 t2) ∧
      (t = t1 ∨ t = t2)) ∨
    (∃ b, Rdfs14aDerives g b t) := by
  have weaken : ∀ props : Bool, t ∈ surrogateTriples D props g →
      (∃ b t1 t2, (RdfD1Derives (fun d => d ∈ D) g b t1 t2 ∨ Rdfs14Derives g b t1 t2) ∧
        (t = t1 ∨ t = t2)) ∨ (∃ b, Rdfs14aDerives g b t) := by
    intro props h
    rcases surrogateTriples_licensed h with ⟨b, t1, t2, hrow, heq⟩ | ⟨_, b, h14a⟩
    · refine Or.inl ⟨b, t1, t2, ?_, heq⟩
      rcases hrow with h1 | ⟨_, h14⟩
      · exact Or.inl h1
      · exact Or.inr h14
    · exact Or.inr ⟨b, h14a⟩
  cases r with
  | simple => exact Or.inl ht
  | d => exact Or.inl ht
  | rdf =>
      rcases List.mem_append.mp ht with h | h
      · exact Or.inl h
      · exact Or.inr (weaken false h)
  | rdfs =>
      rcases List.mem_append.mp ht with h | h
      · exact Or.inl h
      · exact Or.inr (weaken true h)
  | rdfsPlus =>
      rcases List.mem_append.mp ht with h | h
      · exact Or.inl h
      · exact Or.inr (weaken true h)

/-- Under the RDF regime (`props = false`) no rdfs14 / rdfs14a
conclusion is added: every added triple is an rdfD1 conclusion. -/
theorem surrogateTriples_rdf_only_rdfD1 {D : List WfIri} {g : Graph} {t : Triple}
    (ht : t ∈ surrogateTriples D false g) :
    ∃ b t1 t2, RdfD1Derives (fun d => d ∈ D) g b t1 t2 ∧ (t = t1 ∨ t = t2) := by
  rcases surrogateTriples_licensed ht with ⟨b, t1, t2, hrow, heq⟩ | ⟨hp, _⟩
  · rcases hrow with h1 | ⟨hp, _⟩
    · exact ⟨b, t1, t2, h1, heq⟩
    · cases hp
  · cases hp

#print axioms surrogateTriples_licensed
#print axioms generalize_licensed
#print axioms freshLabelPrefix_fresh

end L4Factoidal.RDF
