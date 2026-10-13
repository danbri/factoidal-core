/-
L4Factoidal.RDF.EntailmentRegimeSoundness — the RDF-regime and
RDFS-regime closures are sound, stated over whole graphs, in the model
theory of RDF 1.1 Semantics §8 and §9; the finding RS-1; and the
two-graph forms of the rdfs5, rdfs9 and rdfs11 truth lemmas.

Written for https://github.com/danbri/factoidal/issues/767 (three F\*
theorems with no Lean counterpart of equal strength) and the
classification of https://github.com/danbri/factoidal/issues/757.
Each section names the F\* theorem it answers.

## Gap 1 — the RDFS regime for every D

`RDFS.fullClosure` seeded two `rdf:XMLLiteral` rows until 2026-10-13
(`rdf:XMLLiteral rdf:type rdfs:Datatype .` and `rdf:XMLLiteral
rdfs:subClassOf rdfs:Literal .`). They are rows of the RDF 1.0 (2004)
RDFS axiomatic table, not of the RDF 1.1 §9 table, and §8 says "RDF-D
interpretations MAY fail to recognize these datatypes". When
`rdf:XMLLiteral ∉ D` they are not RDFS-entailed: no §9 condition and no
§9 axiomatic triple mentions `rdf:XMLLiteral`, and the condition that
puts a datatype in `rdfs:Datatype` ("for every IRI aaa in D, I(aaa) is in
ICEXT(I(rdfs:Datatype))") holds only for IRIs in D. The rows left the
seed table; `fullClosure_entails` below holds for every D, and
`fullClosure_entails_dMinimal` is the instance at
`{rdf:langString, xsd:string}`, the F\* theorem's `d_minimal`.

## Gap 2 — the RDF regime under the RDF conditions only

`rdfClosure_entails` needs `RdfConditions` (§8) and nothing of §9. The
proof does not go through `DerivesFull`, whose truth lemma needs the
whole of `RdfsConditions`: the RDF-regime closure emits only the seed
(the input and the §8 axiomatic triples) and rdfD2 conclusions, and
each is true under `CondRdfAxioms` or `CondRdfProperty`.

## Gap 3 — the finding RS-1

`rdfsReflexivityAxioms` is the RDFS-regime reflexivity harvest of the
F\* engine (`RDFS.Closure.rdfs_reflexivity_axioms`, after the RS-1
split): `c rdfs:subClassOf c` for every IRI `c` typed `rdfs:Class` or at
either end of a `rdfs:subClassOf` triple, and the dual for properties.
The Lean closure does not run this harvest (rdfs6, rdfs10 and the §9
domain and range axioms give the same triples), so the definition is
here only to carry the F\* theorems: every triple it emits is licensed
(`rdfsReflexivityAxioms_licensed`) and so true
(`rdfsReflexivityAxioms_preserves`). `reflexivity_needs_rdfsClass` is the
semantic half of RS-1: under §9 the only premise-free route to a
`rdfs:subClassOf` self-loop is membership in IC.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfsSchema
import L4Factoidal.RDF.EntailmentRdfsModelTheory
import L4Factoidal.RDFS.RhoDfCompleteness
import L4Factoidal.RDFS.ReflexivityWitness

namespace L4Factoidal.RDF

open L4Factoidal.RDFS (DerivesFull)

variable {i : Interp} {aa : BnodeAssignment i.idom} {t : Triple}

/-! ## The two-graph forms of rdfs5, rdfs9 and rdfs11

The F\* lemmas `rdfs5_true`, `rdfs9_true` and `rdfs11_true` read their
two premises from two graphs (`gd` and `gs`, for the semi-naive driver).
`rdfs5_true` and the others in `EntailmentRdfsModelTheory` state the
diagonal `gd = gs = g`. These are the forms with the same hypotheses as
the F\* lemmas. -/

theorem rdfs5_true2 {gd gs : Graph} (h : CondSubPropertyOfTrans i)
    (hgd : HoldsAll i aa gd) (hgs : HoldsAll i aa gs)
    (hd : Rdfs5Derives2 gd gs t) : TripleHolds i aa t := by
  obtain ⟨t1, ht1, t2, ht2, ys, hp1, hp2, hys, hs2, rfl⟩ := hd
  have h1 := hgd t1 ht1
  have h2 := hgs t2 ht2
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp1] at h1
  rw [hp2, hs2] at h2
  rw [show denotTerm i aa t1.o = denotSubject i aa ys from
        hys ▸ denot_subjTerm i aa ys] at h1
  exact h _ _ _ h1 h2

theorem rdfs9_true2 {gd gs : Graph} (h : CondSubClassOf i)
    (hgd : HoldsAll i aa gd) (hgs : HoldsAll i aa gs)
    (hd : Rdfs9Derives2 gd gs t) : TripleHolds i aa t := by
  obtain ⟨sub, hsub, typ, htyp, xs, hsp, hss, htp, hto, rfl⟩ := hd
  have h1 := hgs sub hsub
  have h2 := hgd typ htyp
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hsp, hss] at h1
  rw [htp, hto] at h2
  simp only [denot_subjTerm] at h1 h2 ⊢
  exact h _ _ _ h1 h2

theorem rdfs11_true2 {gd gs : Graph} (h : CondSubClassOfTrans i)
    (hgd : HoldsAll i aa gd) (hgs : HoldsAll i aa gs)
    (hd : Rdfs11Derives2 gd gs t) : TripleHolds i aa t := by
  obtain ⟨t1, ht1, t2, ht2, ys, hp1, hp2, hys, hs2, rfl⟩ := hd
  have h1 := hgd t1 ht1
  have h2 := hgs t2 ht2
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp1] at h1
  rw [hp2, hs2] at h2
  rw [show denotTerm i aa t1.o = denotSubject i aa ys from
        hys ▸ denot_subjTerm i aa ys] at h1
  exact h _ _ _ h1 h2

/-- The diagonal is an instance: the one-graph lemma follows. -/
example (h : CondSubPropertyOfTrans i) {g : Graph} (hg : HoldsAll i aa g)
    (hd : Rdfs5Derives g t) : TripleHolds i aa t := rdfs5_true2 h hg hg hd

/-! ## Gap 2 — the RDF-regime closure under `RdfConditions` only

F\*: `RDF.Entailment.RDFS.ModelTheory.rdf_property_axiom_closure_entails`. -/

/-- The §8 axiomatic triples the RDF-regime closure seeds hold under
`CondRdfAxioms`, when the `rdf:_n` slice is a slice of the family. -/
theorem rdfAxiomaticTriples_hold (a : BnodeAssignment i.idom)
    (cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (hrdfax : CondRdfAxioms i) :
    ∀ u ∈ RDFS.rdfAxiomaticTriples cmps, TripleHolds i a u := by
  intro u h1
  have hsplit : RDFS.rdfAxiomaticTriples cmps
      = RDFS.rdfAxiomaticTriples [] ++ cmps.map
          (fun c => RDFS.iriTriple c RDFS.rdfType RDFS.rdfProperty) := by
    simp [RDFS.rdfAxiomaticTriples]
  rw [hsplit] at h1
  rcases List.mem_append.mp h1 with h8 | hcm
  · refine hrdfax a u (Or.inl ?_)
    exact of_decide_eq_true (List.all_eq_true.mp (by decide :
      (RDFS.rdfAxiomaticTriples []).all
        (fun x => decide (x ∈ RDF.rdfAxiomaticTriples)) = true) u h8)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcm
    exact hrdfax a _ (Or.inr ⟨c, hcmps c hc, rfl⟩)

/-- **Gap 2.** Every triple of the RDF-regime closure is true under the
same assignment as the input, in every interpretation meeting the §8
conditions. -/
theorem rdfClosure_holds (hc : RdfConditions i) (cmps : List WfIri)
    (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) {g : Graph}
    (hg : HoldsAll i aa g) : HoldsAll i aa (RDFS.rdfClosure cmps g) := by
  have hseed : HoldsAll i aa (RDFS.addAll g (RDFS.rdfAxiomaticTriples cmps)) := by
    intro u hu
    rcases RDFS.mem_addAll_cases _ g hu with h | h
    · exact hg u h
    · exact rdfAxiomaticTriples_hold aa cmps hcmps hc.2 u h
  intro u hu
  unfold RDFS.rdfClosure at hu
  rcases RDFS.mem_addAll_cases _ _ hu with h | h
  · exact hseed u h
  · obtain ⟨v, hv, huv⟩ := List.mem_flatMap.mp h
    simp only [RDFS.rdfD2For, List.mem_singleton] at huv
    subst huv
    exact hc.1 _ _ _ (hseed v hv)

/-- **Gap 2, entailment form.** The RDF-regime closure is RDF-entailed by
its input (`RdfEntails`: the §8 conditions only). -/
theorem rdfClosure_entails (cmps : List WfIri)
    (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) (g : Graph) :
    RdfEntails g (RDFS.rdfClosure cmps g) := by
  intro i hc hsat
  obtain ⟨a, ha⟩ := hsat
  exact ⟨a, rdfClosure_holds hc cmps hcmps ha⟩

/-- With the empty `rdf:_n` slice the statement has no hypothesis, as
the F\* theorem has none. -/
theorem rdfClosure_entails_nil (g : Graph) : RdfEntails g (RDFS.rdfClosure [] g) :=
  rdfClosure_entails [] (fun _ h => absurd h List.not_mem_nil) g

/-! ## The RDFS-regime closure over whole graphs

F\*: `rdfs_closure_sound`, `rdfs_closure_entails` (the rule loop) and
`rdfs_closure_with_reflexivity_sound`, `rdfs_closure_with_reflexivity_entails`
(the regime entry point). -/

/-- The rule loop alone (no seeding) keeps every triple true, for every
datatype set and every graph. F\* `rdfs_closure_sound` needs the index
hypothesis `closure_chain_wf g`; this does not. -/
theorem fullClosureLoop_holds {D : DatatypeSet} (hc : RdfsConditions D i)
    {g : Graph} (fuel : Nat) (hg : HoldsAll i aa g) :
    HoldsAll i aa (RDFS.fullClosureLoop g fuel) := fun _ ht =>
  derivesFull_holds hc (ax := []) (fun _ h => absurd h List.not_mem_nil) hg
    (RDFS.fullClosureLoop_sound [] fuel g ht)

theorem fullClosureLoop_entails (D : DatatypeSet) (g : Graph) (fuel : Nat) :
    RdfsEntails D g (RDFS.fullClosureLoop g fuel) := by
  intro i hc hsat
  obtain ⟨a, ha⟩ := hsat
  exact ⟨a, fullClosureLoop_holds hc fuel ha⟩

/-- **Gap 1.** The RDFS-regime closure (`RDF.Regime.closure .rdfs`)
keeps every triple true, for every datatype list `D`. -/
theorem fullClosure_holds (D cmps : List WfIri)
    (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (hc : RdfsConditions (fun x => x ∈ D) i) {g : Graph}
    (hg : HoldsAll i aa g) : HoldsAll i aa (RDFS.fullClosure D cmps g) := by
  obtain ⟨⟨hprop, hrdfax⟩, hdom, hran, hdt, hdmin, hres, hsp, hsptr, hsprefl, hspip,
          hsc, hsctr, hscrefl, hscic, hcsr, hdsl, hcmp, hrdfsax⟩ := hc
  intro u hu
  exact derivesFull_holds
    ⟨⟨hprop, hrdfax⟩, hdom, hran, hdt, hdmin, hres, hsp, hsptr, hsprefl, hspip,
     hsc, hsctr, hscrefl, hscic, hcsr, hdsl, hcmp, hrdfsax⟩
    (axiomaticTriples_hold aa D cmps hcmps hrdfax hrdfsax hdt) hg
    (RDFS.fullClosure_sound D cmps g hu)

/-- **Gap 1, entailment form.** -/
theorem fullClosure_entails (D cmps : List WfIri)
    (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) (g : Graph) :
    RdfsEntails (fun x => x ∈ D) g (RDFS.fullClosure D cmps g) := by
  intro i hc hsat
  obtain ⟨a, ha⟩ := hsat
  exact ⟨a, fullClosure_holds D cmps hcmps hc ha⟩

theorem mem_dMinimalList_iff : (fun x => x ∈ [rdfLangString, xsdString]) = dMinimal := by
  funext x
  exact propext (by simp [dMinimal])

/-- **Gap 1 at the F\* theorem's datatype set.** With
D = `{rdf:langString, xsd:string}`, the RDFS-regime closure is
RDFS-entailed (`rdfs_entails d_minimal` in F\*). Neither
`rdf:XMLLiteral` triple is emitted at this D (the `#guard` lines in
`Unified/RdfsSchema.lean`). -/
theorem fullClosure_entails_dMinimal (cmps : List WfIri)
    (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) (g : Graph) :
    RdfsEntails dMinimal g (RDFS.fullClosure [rdfLangString, xsdString] cmps g) := by
  rw [← mem_dMinimalList_iff]
  exact fullClosure_entails _ cmps hcmps g

/-! ## Gap 3 — the finding RS-1

F\*: `RDF.Entailment.RDFS.ModelTheory.reflexivity_needs_rdfs_Class`,
`rdfs_reflexivity_axioms_preserves`, and
`RDF.Entailment.RDFS.Refinement.rdfs_reflexivity_axioms_licensed`. -/

/-- **RS-1, the semantic half.** Under the §9 condition "IEXT(I(rdfs:subClassOf))
is ... reflexive on IC", a thing that is not its own subclass is not in
IC. So a `rdfs:subClassOf` self-loop needs `rdfs:Class` membership; a
typing with another class IRI (for example `owl:Class`) does not
supply it. -/
theorem reflexivity_needs_rdfsClass (i : Interp) (x : i.idom)
    (h : CondSubClassOfRefl i)
    (hn : ¬ i.iext (i.iIri RDFS.rdfsSubClassOf) x x) :
    ¬ icext i x (i.iIri RDFS.rdfsClass) :=
  fun hc => hn (h x hc)

/-- The IRI of a subject, if it is an IRI. -/
def subjectIriList : Subject → List WfIri
  | .iri c => [c]
  | .bnode _ => []

/-- The IRI of a term, if it is an IRI. -/
def termIriList : Term → List WfIri
  | .iri c => [c]
  | _ => []

/-- One triple's contribution to the harvest (F\* `collect_related_iris
typing rel`): the IRI ends of a `rel` triple, and the IRI subject of a
`rdf:type typing` triple. -/
def reflexivityIrisOf (typing rel : WfIri) (u : Triple) : List WfIri :=
  (if u.p = rel then subjectIriList u.s ++ termIriList u.o else []) ++
  (if u.p = RDFS.rdfType ∧ u.o = .iri typing then subjectIriList u.s else [])

/-- The RDFS-regime reflexivity harvest (F\* `RDFS.Closure.rdfs_reflexivity_axioms`
after the RS-1 split): typing by `rdfs:Class` and `rdf:Property` only,
never by `owl:Class`, `owl:ObjectProperty` or `owl:DatatypeProperty`. -/
def rdfsReflexivityAxioms (g : Graph) : Graph :=
  (g.flatMap (reflexivityIrisOf RDFS.rdfsClass RDFS.rdfsSubClassOf)).map
    (fun c => RDFS.iriTriple c RDFS.rdfsSubClassOf c) ++
  (g.flatMap (reflexivityIrisOf RDFS.rdfProperty RDFS.rdfsSubPropertyOf)).map
    (fun c => RDFS.iriTriple c RDFS.rdfsSubPropertyOf c)

theorem mem_subjectIriList {s : Subject} {c : WfIri} (h : c ∈ subjectIriList s) :
    s = .iri c := by
  cases s with
  | iri d => simp only [subjectIriList, List.mem_singleton] at h; rw [h]
  | bnode _ => simp [subjectIriList] at h

theorem mem_termIriList {o : Term} {c : WfIri} (h : c ∈ termIriList o) :
    o = subjTerm (.iri c) := by
  cases o with
  | iri d => simp only [termIriList, List.mem_singleton] at h; rw [h]; rfl
  | _ => simp [termIriList] at h

/-- Where a harvested IRI comes from: an end of a `rel` triple, or the
subject of a `rdf:type typing` triple. -/
theorem mem_reflexivityIrisOf {typing rel c : WfIri} {u : Triple}
    (h : c ∈ reflexivityIrisOf typing rel u) :
    (u.p = rel ∧ (u.s = .iri c ∨ u.o = subjTerm (.iri c))) ∨
    (u.p = RDFS.rdfType ∧ u.o = .iri typing ∧ u.s = .iri c) := by
  unfold reflexivityIrisOf at h
  rcases List.mem_append.mp h with h1 | h2
  · split at h1
    · rename_i hp
      rcases List.mem_append.mp h1 with hs | ho
      · exact Or.inl ⟨hp, Or.inl (mem_subjectIriList hs)⟩
      · exact Or.inl ⟨hp, Or.inr (mem_termIriList ho)⟩
    · simp at h1
  · split at h2
    · rename_i hp
      exact Or.inr ⟨hp.1, hp.2, mem_subjectIriList h2⟩
    · simp at h2

/-- **RS-1, the syntactic half (positive).** Every triple of the
RDFS-regime harvest is licensed by the §9 table: a class self-loop by
rdfs10 or by the subClassOf endpoint condition, a property self-loop by
rdfs6 or by the subPropertyOf endpoint condition. For every `D`. -/
theorem rdfsReflexivityAxioms_licensed {D : DatatypeSet} {g : Graph} :
    RdfsStepLicensed D g (rdfsReflexivityAxioms g) := by
  intro t ht
  unfold rdfsReflexivityAxioms at ht
  rcases List.mem_append.mp ht with hc | hp
  · obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc
    obtain ⟨u, hu, hcu⟩ := List.mem_flatMap.mp hcm
    rcases mem_reflexivityIrisOf hcu with ⟨hrel, hend⟩ | ⟨hty, hto, hs⟩
    · -- the subClassOf endpoint condition
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨u, hu, .iri c, hrel, hend, rfl⟩))))
    · -- rdfs10
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ?_)))))))))))))))))
      exact ⟨u, hu, hty, hto, by rw [hs]; rfl⟩
  · obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨u, hu, hcu⟩ := List.mem_flatMap.mp hcm
    rcases mem_reflexivityIrisOf hcu with ⟨hrel, hend⟩ | ⟨hty, hto, hs⟩
    · -- the subPropertyOf endpoint condition
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨u, hu, .iri c, hrel, hend, rfl⟩)))))
    · -- rdfs6
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
      exact ⟨u, hu, hty, hto, by rw [hs]; rfl⟩

/-- **RS-1, truth.** Every triple of the RDFS-regime harvest is true in
every interpretation meeting the §9 conditions, under the assignment
that makes the graph true. For every `D`; the F\* theorem states it at
`d_minimal`. -/
theorem rdfsReflexivityAxioms_preserves {D : DatatypeSet} {g : Graph}
    (hc : RdfsConditions D i) (hg : HoldsAll i aa g) :
    HoldsAll i aa (rdfsReflexivityAxioms g) :=
  rdfsStepLicensed_holds hc hg rdfsReflexivityAxioms_licensed


/-- The RDFS-regime harvest emits nothing from a graph whose only class
typing is `owl:Class` (F\* `rdfs_reflexivity_axioms_owl_class_empty`,
the RS-1 witness graph). -/
theorem rdfsReflexivityAxioms_owlClassGraph (c : WfIri) :
    rdfsReflexivityAxioms (RDFS.owlClassGraph c) = [] := by
  simp (config := { decide := true }) [rdfsReflexivityAxioms, RDFS.owlClassGraph,
    reflexivityIrisOf]

/-! ## ρdf saturation — F\* `RDF.Entailment.RDFS.Completeness`

The F\* module states completeness for a ρdf-closed graph that contains
the input (`rho_df_saturation_*`) and for the six-rule closure
(`rdfs_closure_rho_df_complete`). `RDFS/RhoDfCompleteness.lean` has the
closed-graph forms (`rhoDfClosed_*`); these are the saturation forms. -/

/-- A subgraph is satisfied wherever the graph is. -/
theorem subgraph_satisfies {g c : Graph} (hsub : ∀ t ∈ g, t ∈ c)
    (h : Satisfies i c) : Satisfies i g := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun t ht => ha t (hsub t ht)⟩

theorem rhoDf_saturation_sound {g c e : Graph} (hgc : RhoDfEntails g c)
    (hce : SimpleEntailmentSpec c e) : RhoDfEntails g e :=
  fun i hi hs => rhoDfClosed_sound hce i hi (hgc i hi hs)

theorem rhoDf_saturation_complete {g c e : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) (hfe : GraphTtFree e) (hsub : ∀ t ∈ g, t ∈ c)
    (h : RhoDfEntails g e) : SimpleEntailmentSpec c e :=
  rhoDfClosed_complete hc hf hfe (fun i hi hs => h i hi (subgraph_satisfies hsub hs))

theorem rhoDf_saturation_iff {g c e : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) (hfe : GraphTtFree e) (hsub : ∀ t ∈ g, t ∈ c)
    (hgc : RhoDfEntails g c) : RhoDfEntails g e ↔ SimpleEntailmentSpec c e :=
  ⟨rhoDf_saturation_complete hc hf hfe hsub, rhoDf_saturation_sound hgc⟩

/-- The six-rule ρdf closure (`RDFS.closure`) decides ρdf entailment when
it is closed and in the fragment: no hypothesis on the input graph, since
`RDFS.closure_extensive` holds for every graph. -/
theorem closure_rhoDf_complete {g e : Graph} (fuel : Nat)
    (hc : RhoDfClosed (RDFS.closure g fuel))
    (hf : RhoDfModelFragGraph (RDFS.closure g fuel)) (hfe : GraphTtFree e)
    (h : RhoDfEntails g e) : SimpleEntailmentSpec (RDFS.closure g fuel) e :=
  rhoDf_saturation_complete hc hf hfe (fun _ ht => RDFS.closure_extensive fuel g ht) h

/-- The six-rule ρdf closure is ρdf-entailed by its input, for every
graph and fuel (F\* `rho_df_closure_sound` needs the index hypothesis
`rho_df_chain_wf g`). -/
theorem closure_rhoDfEntails (g : Graph) (fuel : Nat) :
    RhoDfEntails g (RDFS.closure g fuel) := by
  intro i hc hsat
  obtain ⟨a, ha⟩ := hsat
  exact ⟨a, fun _ ht => rhoDf_derives_holds hc ha (RDFS.closure_sound fuel g ht)⟩

/-- The closure decides ρdf entailment when it is closed and in the
fragment (F\* `rho_df_closure_decides`, which also needs the chain
hypotheses on `g`). -/
theorem closure_rhoDf_iff {g e : Graph} (fuel : Nat)
    (hc : RhoDfClosed (RDFS.closure g fuel))
    (hf : RhoDfModelFragGraph (RDFS.closure g fuel)) (hfe : GraphTtFree e) :
    RhoDfEntails g e ↔ SimpleEntailmentSpec (RDFS.closure g fuel) e :=
  ⟨closure_rhoDf_complete fuel hc hf hfe, rhoDf_saturation_sound (closure_rhoDfEntails g fuel)⟩

/-- Finding C-1 for every pair of IRIs: `x rdfs:subClassOf y` RDFS-entails
`x rdfs:subClassOf x`, for every datatype set. (`rdfsEntails_subclassSelfLoop`
in `RDFS/RhoDfCompleteness.lean` is the instance at two example IRIs.) -/
theorem rdfsEntails_subclassSelfLoop_iri {D : DatatypeSet} (x y : WfIri) :
    RdfsEntails D [{ s := .iri x, p := RDFS.rdfsSubClassOf, o := .iri y }]
      [{ s := .iri x, p := RDFS.rdfsSubClassOf, o := .iri x }] := by
  rintro i hcond ⟨aa, haa⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hrefl, hic, -⟩ := hcond
  have hpremise := haa _ (List.mem_singleton.mpr rfl)
  simp only [TripleHolds, denotSubject, denotTerm] at hpremise
  refine ⟨aa, fun t ht => ?_⟩
  rw [List.mem_singleton.mp ht]
  simp only [TripleHolds, denotSubject, denotTerm]
  exact hrefl _ (hic _ _ hpremise).1

/-- The executable fragment check is exact: `isRhoDfFrag` answers true
exactly on the model fragment (F\* `lemma_is_rho_df_frag_correct`). -/
theorem isRhoDfFrag_iff (g : Graph) :
    RDFS.isRhoDfFrag g = true ↔ RhoDfModelFragGraph g := by
  constructor
  · intro h t ht
    have hb := List.all_eq_true.mp h t ht
    simp only [RDFS.isRhoDfFragTriple, Bool.and_eq_true] at hb
    obtain ⟨hobj, hsp⟩ := hb
    constructor
    · cases ho : t.o with
      | iri x => trivial
      | bnode b => trivial
      | literal l => simp [ho] at hobj
      | tripleTerm s p o => simp [ho] at hobj
    · intro hp
      rw [hp] at hsp
      simp only [bne_self_eq_false, Bool.false_or] at hsp
      cases ho : t.o with
      | iri x => exact ⟨x, rfl⟩
      | bnode b => simp [ho] at hsp
      | literal l => simp [ho] at hsp
      | tripleTerm s p o => simp [ho] at hsp
  · intro h
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨hobj, hsp⟩ := h t ht
    simp only [RDFS.isRhoDfFragTriple, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · cases ho : t.o with
      | iri x => rfl
      | bnode b => rfl
      | literal l => rw [ho] at hobj; exact absurd hobj id
      | tripleTerm s p o => rw [ho] at hobj; exact absurd hobj id
    · by_cases hp : t.p = RDFS.rdfsSubPropertyOf
      · obtain ⟨x, hx⟩ := hsp hp
        simp [hx]
      · simp [hp]

/-- The F\* finding F1 witness graph: `p rdfs:subPropertyOf
rdfs:subPropertyOf . a p _:b1 .` -/
def f1Witness (p a : WfIri) : Graph :=
  [⟨.iri p, RDFS.rdfsSubPropertyOf, .iri RDFS.rdfsSubPropertyOf⟩, ⟨.iri a, p, .bnode "b1"⟩]

/-- What rdfs7 derives from it: a `rdfs:subPropertyOf` triple whose
object is a blank node. -/
def f1BadTriple (a : WfIri) : Triple := ⟨.iri a, RDFS.rdfsSubPropertyOf, .bnode "b1"⟩

/-- **Finding F1.** The ρdf model fragment is not preserved by the rules:
the witness graph is in the fragment, rdfs7 derives `f1BadTriple a` from
it, and that triple is not in the fragment. So the closure's fragment
membership is a hypothesis of `closure_rhoDf_complete`, never a
consequence of the input's. -/
theorem rhoDf_frag_preservation_fails (p a : WfIri)
    (hp : p ≠ RDFS.rdfsSubPropertyOf) :
    RhoDfModelFragGraph (f1Witness p a) ∧ Rdfs7Derives (f1Witness p a) (f1BadTriple a) ∧
    ¬ RhoDfModelFragTriple (f1BadTriple a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [f1Witness, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨trivial, fun _ => ⟨_, rfl⟩⟩
    · exact ⟨trivial, fun h => absurd h hp⟩
  · exact ⟨_, List.mem_cons_self .., _, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      p, RDFS.rdfsSubPropertyOf, rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    obtain ⟨x, hx⟩ := h.2 rfl
    cases hx


/-! ## Merging — F\* `RDF.Entailment.Simple.ModelTheory`, the merge lemmas

RDF 1.1 Semantics §4: the merge of two graphs is their union after the
blank nodes are made distinct. For two graphs with no shared blank node
the merge is the union, and it is satisfied exactly when both are. -/

/-- No blank node occurs in both graphs (F\* `bnode_disjoint`; its
`graph_has_bnode g b` is `b ∈ graphBnodeIds g` here). -/
def BnodeDisjoint (g1 g2 : Graph) : Prop :=
  ∀ b : BNodeId, ¬ (b ∈ graphBnodeIds g1 ∧ b ∈ graphBnodeIds g2)

/-- The merged assignment: `a1` on the blank nodes of `g1`, `a2` elsewhere. -/
def mergeAssignment (i : Interp) (g1 : Graph) (a1 a2 : BnodeAssignment i.idom) :
    BnodeAssignment i.idom :=
  fun b => if b ∈ graphBnodeIds g1 then a1 b else a2 b

theorem mergeAssignment_g1 {g1 : Graph} {a1 a2 : BnodeAssignment i.idom} {b : BNodeId}
    (h : b ∈ graphBnodeIds g1) : mergeAssignment i g1 a1 a2 b = a1 b := by
  simp [mergeAssignment, h]

theorem mergeAssignment_g2 {g1 g2 : Graph} {a1 a2 : BnodeAssignment i.idom} {b : BNodeId}
    (hd : BnodeDisjoint g1 g2) (h : b ∈ graphBnodeIds g2) :
    mergeAssignment i g1 a1 a2 b = a2 b := by
  have hn : b ∉ graphBnodeIds g1 := fun h1 => hd b ⟨h1, h⟩
  simp [mergeAssignment, hn]

theorem mem_graphBnodeIds {g : Graph} {u : Triple} {b : BNodeId} (hu : u ∈ g)
    (hb : b ∈ tripleBnodes u) : b ∈ graphBnodeIds g :=
  List.mem_flatMap.mpr ⟨u, hu, hb⟩

/-- The union of two blank-node-disjoint graphs holds under the merged
assignment of the two witnesses (F\* `lemma_merge_satisfies`). -/
theorem merge_holdsAll {g1 g2 : Graph} {a1 a2 : BnodeAssignment i.idom}
    (hd : BnodeDisjoint g1 g2) (h1 : HoldsAll i a1 g1) (h2 : HoldsAll i a2 g2) :
    HoldsAll i (mergeAssignment i g1 a1 a2) (g1 ++ g2) := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · refine (tripleHolds_agree i (t := u) ?_).mp (h1 u hu)
    intro b hb
    exact (mergeAssignment_g1 (mem_graphBnodeIds hu hb)).symm
  · refine (tripleHolds_agree i (t := u) ?_).mp (h2 u hu)
    intro b hb
    exact (mergeAssignment_g2 hd (mem_graphBnodeIds hu hb)).symm

/-- **Merging.** The union of two blank-node-disjoint graphs is satisfied
by an interpretation exactly when both graphs are. -/
theorem merge_satisfies_iff {g1 g2 : Graph} (hd : BnodeDisjoint g1 g2) :
    Satisfies i (g1 ++ g2) ↔ Satisfies i g1 ∧ Satisfies i g2 := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, fun u hu => ha u (List.mem_append_left _ hu)⟩,
           ⟨a, fun u hu => ha u (List.mem_append_right _ hu)⟩⟩
  · rintro ⟨⟨a1, h1⟩, ⟨a2, h2⟩⟩
    exact ⟨_, merge_holdsAll hd h1 h2⟩

theorem merge_entails_component {g1 g2 : Graph} (hd : BnodeDisjoint g1 g2)
    (h : Satisfies i (g1 ++ g2)) : Satisfies i g1 ∧ Satisfies i g2 :=
  (merge_satisfies_iff hd).mp h

/-- The pair `{g1, g2}` entails `e` in an interpretation exactly when the
merge does. -/
theorem merge_entails_iff {g1 g2 e : Graph} (hd : BnodeDisjoint g1 g2) :
    (Satisfies i g1 ∧ Satisfies i g2 → Satisfies i e) ↔
      (Satisfies i (g1 ++ g2) → Satisfies i e) := by
  rw [merge_satisfies_iff hd]

/-! ## Build-time checks -/

section Checks

/- The harvest reads `rdfs:Class` typing, and not `owl:Class` typing
(the RS-1 split). -/
#guard decide (RDFS.iriTriple RDFS.rdfsResource RDFS.rdfsSubClassOf RDFS.rdfsResource ∈
  rdfsReflexivityAxioms [⟨.iri RDFS.rdfsResource, RDFS.rdfType, .iri RDFS.rdfsClass⟩])
#guard !decide (RDFS.iriTriple RDFS.rdfsResource RDFS.rdfsSubClassOf RDFS.rdfsResource ∈
  rdfsReflexivityAxioms [⟨.iri RDFS.rdfsResource, RDFS.rdfType, .iri L4Factoidal.OWL.RL.owlClass⟩])
/- Both ends of a subPropertyOf triple are harvested; a blank node is not. -/
#guard (rdfsReflexivityAxioms [⟨.iri RDFS.rdfType, RDFS.rdfsSubPropertyOf, .iri RDFS.rdfsMember⟩]).length == 2
#guard (rdfsReflexivityAxioms [⟨.bnode "b", RDFS.rdfsSubPropertyOf, .bnode "c"⟩]).length == 0

end Checks

/-! Axiom audit — expected `propext`, `Classical.choice`, `Quot.sound`
at most. -/

#print axioms rdfs5_true2
#print axioms rdfs9_true2
#print axioms rdfs11_true2
#print axioms rdfAxiomaticTriples_hold
#print axioms rdfClosure_holds
#print axioms rdfClosure_entails
#print axioms rdfClosure_entails_nil
#print axioms fullClosureLoop_holds
#print axioms fullClosureLoop_entails
#print axioms fullClosure_holds
#print axioms fullClosure_entails
#print axioms mem_dMinimalList_iff
#print axioms fullClosure_entails_dMinimal
#print axioms reflexivity_needs_rdfsClass
#print axioms mem_reflexivityIrisOf
#print axioms rdfsReflexivityAxioms_licensed
#print axioms rdfsReflexivityAxioms_preserves
#print axioms rdfsReflexivityAxioms_owlClassGraph
#print axioms subgraph_satisfies
#print axioms rhoDf_saturation_sound
#print axioms rhoDf_saturation_complete
#print axioms rhoDf_saturation_iff
#print axioms closure_rhoDf_complete
#print axioms closure_rhoDfEntails
#print axioms closure_rhoDf_iff
#print axioms rdfsEntails_subclassSelfLoop_iri
#print axioms isRhoDfFrag_iff
#print axioms rhoDf_frag_preservation_fails
#print axioms mergeAssignment_g1
#print axioms mergeAssignment_g2
#print axioms mem_graphBnodeIds
#print axioms merge_holdsAll
#print axioms merge_satisfies_iff
#print axioms merge_entails_component
#print axioms merge_entails_iff

end L4Factoidal.RDF
