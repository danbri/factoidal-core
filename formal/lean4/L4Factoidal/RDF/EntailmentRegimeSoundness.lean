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

end L4Factoidal.RDF
