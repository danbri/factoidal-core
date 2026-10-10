/-
L4Factoidal.OWL.RdfBased.Engine — the executable side of the OWL 2
RDF-Based Semantics rules of `RdfBased/Rules.lean`.

`rbConclusions g goal` lists triples the rules derive from the graph
`g` (an OWL 2 RL/RDF closure, in the regime). `rbConclusions_derives`
proves that each of them is `RbDerives g`, so each is entailed by `g`
(`Rules.rbDerives_entailed`).

Two rule families are GOAL-DIRECTED by the conclusion graph `goal`,
because they are premise-free and would otherwise add their whole
table to every graph: the axiomatic triples (`axiomsFor`: only rows
whose subject IRI the goal names) and the universal-class typings
(`universalFor`: only when the goal asks for an `owl:Thing` or
`rdfs:Resource` typing). The other rules read `g` alone. Each rule is
one pass over `g` with at most two nested lookups, and mints no blank
node, so the result is finite and its size is bounded by a polynomial
in `|g|`. The regime (`Harness/OwlProbe.lean`, `--rdf-based`) applies
the rules and the RL closure alternately for a stated number of rounds.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RdfBased.Rules

namespace L4Factoidal.OWL.RdfBased

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.RDFS (rdfsClass rdfsLiteral rdfProperty rdfsResource rdfList)

/-! ## The rules, executable -/

/-- Every IRI the goal graph names. -/
def goalIris (goal : Graph) : List WfIri :=
  goal.flatMap (fun t => subjIri t.s ++ [t.p] ++ asIri t.o)

def axiomsFor (goal : Graph) : List Triple :=
  let ws := goalIris goal
  rbAxioms.filter (fun t => (subjIri t.s).any (fun w => ws.contains w))

def vocabTypeAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.p == rdfType then
      (asIri t.o).flatMap (fun e1 =>
        (extSubTable.filter (fun e => e.1 == e1)).map
          (fun e => (⟨t.s, rdfType, .iri e.2⟩ : Triple)))
    else [])

/-- The subjects a universal-class goal is asked of: the goal's own
subject when it is an IRI, every subject of `g` when it is a blank
node. -/
def universalSubjects (g : Graph) (s : Subject) : List Subject :=
  match s with
  | .iri _ => [s]
  | .bnode _ => (g.map (·.s)).eraseDups

def universalFor (g goal : Graph) : List Triple :=
  goal.flatMap (fun t =>
    if t.p == rdfType then
      (asIri t.o).flatMap (fun c =>
        if universalClasses.contains c then
          (universalSubjects g t.s).map (fun s => (⟨s, rdfType, .iri c⟩ : Triple))
        else [])
    else [])

def compSymAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.p == owlComplementOf then
      (asSubject t.o).map (fun b => (⟨b, owlComplementOf, t.s.toTerm⟩ : Triple))
    else [])

/-- `aj owl:differentFrom ak` for every pair of distinct POSITIONS of
the sequence whose `j`-th member is not a literal. -/
def diffPairs (es : List Term) : List Triple :=
  (List.range es.length).flatMap (fun j =>
    (List.range es.length).flatMap (fun k =>
      if j == k then []
      else
        match es[j]?, es[k]? with
        | some aj, some ak =>
            (asSubject aj).map (fun sj => (⟨sj, owlDifferentFrom, ak⟩ : Triple))
        | _, _ => []))

def allDiffAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.p == rdfType && t.o == Term.iri owlAllDifferent then
      g.flatMap (fun u =>
        if u.s == t.s && (u.p == owlMembers || u.p == owlDistinctMembers) then
          (listSeqs g u.o (listFuel g)).flatMap diffPairs
        else [])
    else [])

/-- The singleton-enumeration rule, for `rdfs:range` (`funSingleton`)
and `rdfs:domain` (`ifpSingleton`). -/
def singletonAll (g : Graph) (rel ch : WfIri) : List Triple :=
  g.flatMap (fun t =>
    if t.p == rel then
      (asSubject t.o).flatMap (fun c =>
        (withSubjPred g c owlOneOf).flatMap (fun u =>
          (listSeqs g u.o (listFuel g)).flatMap (fun es =>
            if es.length == 1 then [(⟨t.s, rdfType, .iri ch⟩ : Triple)] else [])))
    else [])

def typeDomainSubAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.s == Subject.iri rdfType && t.p == rdfsDomain then
      g.flatMap (fun u =>
        if u.p == rdfType && u.o == Term.iri rdfsClass then
          [(⟨u.s, rdfsSubClassOf, t.o⟩ : Triple)]
        else [])
    else [])

def avfRangeAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.s == Subject.iri owlThing && t.p == rdfsSubClassOf then
      (asSubject t.o).flatMap (fun r =>
        (withSubjPred g r owlOnProperty).flatMap (fun u =>
          (asSubject u.o).flatMap (fun p =>
            (withSubjPred g r owlAllValuesFrom).map
              (fun v => (⟨p, rdfsRange, v.o⟩ : Triple)))))
    else [])

def svfDomainAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.p == owlSomeValuesFrom && t.o == Term.iri owlThing then
      (withSubjPred g t.s owlOnProperty).flatMap (fun u =>
        (asSubject u.o).flatMap (fun p =>
          (withSubjPred g t.s rdfsSubClassOf).map
            (fun v => (⟨p, rdfsDomain, v.o⟩ : Triple))))
    else [])

def emptySubPropAll (g : Graph) : List Triple :=
  g.flatMap (fun t =>
    if t.p == rdfsRange then
      (asIri t.o).flatMap (fun d1 =>
        (withSubjPred g t.s rdfsRange).flatMap (fun u =>
          (asIri u.o).flatMap (fun d2 =>
            if xsdValueSpacesDisjoint d1 d2 then
              (g.filter (fun v => v.p == rdfType && v.o == Term.iri rdfProperty)).map
                (fun v => (⟨t.s, rdfsSubPropertyOf, v.s.toTerm⟩ : Triple))
            else [])))
    else [])

/-- Everything the rules derive from `g` in one pass, with the
premise-free families restricted to what `goal` names. -/
def rbConclusions (g goal : Graph) : List Triple :=
  axiomsFor goal ++ vocabTypeAll g ++ universalFor g goal ++ compSymAll g ++
  allDiffAll g ++ singletonAll g rdfsRange owlFunctionalProperty ++
  singletonAll g rdfsDomain owlInverseFunctionalProperty ++ typeDomainSubAll g ++
  avfRangeAll g ++ svfDomainAll g ++ emptySubPropAll g

/-! ## Every executable conclusion is a rule application -/

theorem axiomsFor_derives {g goal : Graph} {t : Triple} (h : t ∈ axiomsFor goal) :
    RbDerives g t := by
  simp only [axiomsFor, List.mem_filter] at h
  exact RbDerives.ax h.1

theorem vocabTypeAll_derives {g : Graph} {t : Triple} (h : t ∈ vocabTypeAll g) :
    RbDerives g t := by
  simp only [vocabTypeAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i hp
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq] at h
    obtain ⟨e1, he1, e, ⟨he, hee⟩, rfl⟩ := h
    have ho := mem_asIri he1
    have hp' : u.p = rdfType := Subtype.ext (by simpa using hp)
    have hm : (⟨u.s, rdfType, .iri e1⟩ : Triple) ∈ g := mem_of_parts hu rfl hp' ho
    have hpair : (e1, e.2) ∈ extSubTable := by rw [← hee]; exact he
    exact RbDerives.vocabType hm hpair
  · simp at h

theorem universalFor_derives {g goal : Graph} {t : Triple} (h : t ∈ universalFor g goal) :
    RbDerives g t := by
  simp only [universalFor, List.mem_flatMap] at h
  obtain ⟨u, _, h⟩ := h
  split at h
  · simp only [List.mem_flatMap] at h
    obtain ⟨c, _, h⟩ := h
    split at h
    · rename_i hc
      simp only [List.mem_map] at h
      obtain ⟨s, _, rfl⟩ := h
      exact RbDerives.universal s (by simpa using hc)
    · simp at h
  · simp at h

theorem compSymAll_derives {g : Graph} {t : Triple} (h : t ∈ compSymAll g) :
    RbDerives g t := by
  simp only [compSymAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i hp
    simp only [List.mem_map] at h
    obtain ⟨b, hb, rfl⟩ := h
    have ho := mem_asSubject hb
    have hp' : u.p = owlComplementOf := Subtype.ext (by simpa using hp)
    exact RbDerives.compSym (mem_of_parts hu rfl hp' ho)
  · simp at h

theorem diffPairs_spec {es : List Term} {t : Triple} (h : t ∈ diffPairs es) :
    ∃ (j k : Nat) (aj ak : Term) (sj : Subject), j ≠ k ∧ es[j]? = some aj ∧
      es[k]? = some ak ∧ aj = sj.toTerm ∧ t = ⟨sj, owlDifferentFrom, ak⟩ := by
  simp only [diffPairs, List.mem_flatMap] at h
  obtain ⟨j, _, k, _, h⟩ := h
  split at h
  · simp at h
  · rename_i hjk
    split at h
    · rename_i aj ak hj hk
      simp only [List.mem_map] at h
      obtain ⟨sj, hsj, rfl⟩ := h
      exact ⟨j, k, aj, ak, sj, by simpa using hjk, hj, hk, mem_asSubject hsj, rfl⟩
    · simp at h

theorem allDiffAll_derives {g : Graph} {t : Triple} (h : t ∈ allDiffAll g) :
    RbDerives g t := by
  simp only [allDiffAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i hty
    simp only [Bool.and_eq_true, beq_iff_eq] at hty
    simp only [List.mem_flatMap] at h
    obtain ⟨v, hv, h⟩ := h
    split at h
    · rename_i hmem
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmem
      simp only [List.mem_flatMap] at h
      obtain ⟨es, hes, h⟩ := h
      obtain ⟨j, k, aj, ak, sj, hjk, hj, hk, hs, rfl⟩ := diffPairs_spec h
      have hl := listSeqs_sound g _ _ hes
      have hty' : (⟨u.s, rdfType, .iri owlAllDifferent⟩ : Triple) ∈ g :=
        mem_of_parts hu rfl hty.1 hty.2
      have hm : (⟨u.s, v.p, v.o⟩ : Triple) ∈ g := mem_of_parts hv hmem.1 rfl rfl
      exact RbDerives.allDiff hmem.2 hty' hm hl hjk hj hk hs
    · simp at h
  · simp at h

theorem singletonAll_spec {g : Graph} {rel ch : WfIri} {t : Triple}
    (h : t ∈ singletonAll g rel ch) :
    ∃ (p c : Subject) (lst a : Term), (⟨p, rel, c.toTerm⟩ : Triple) ∈ g ∧
      (⟨c, owlOneOf, lst⟩ : Triple) ∈ g ∧ ListDenotes g lst [a] ∧
      t = ⟨p, rdfType, .iri ch⟩ := by
  simp only [singletonAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i hp
    simp only [List.mem_flatMap] at h
    obtain ⟨c, hc, v, hv, es, hes, h⟩ := h
    split at h
    · rename_i hlen
      simp only [List.mem_singleton] at h
      subst h
      have hl := listSeqs_sound g _ _ hes
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
      obtain ⟨hvg, hvs, hvp⟩ := mem_withSubjPred hv
      have hp' : u.p = rel := Subtype.ext (by simpa using hp)
      exact ⟨u.s, c, v.o, a, mem_of_parts hu rfl hp' (mem_asSubject hc),
        mem_of_parts hvg hvs hvp rfl, hl, rfl⟩
    · simp at h
  · simp at h

theorem singletonRange_derives {g : Graph} {t : Triple}
    (h : t ∈ singletonAll g rdfsRange owlFunctionalProperty) : RbDerives g t := by
  obtain ⟨_, _, _, _, hr, ho, hl, rfl⟩ := singletonAll_spec h
  exact RbDerives.funSingleton hr ho hl

theorem singletonDomain_derives {g : Graph} {t : Triple}
    (h : t ∈ singletonAll g rdfsDomain owlInverseFunctionalProperty) : RbDerives g t := by
  obtain ⟨_, _, _, _, hd, ho, hl, rfl⟩ := singletonAll_spec h
  exact RbDerives.ifpSingleton hd ho hl

theorem typeDomainSubAll_derives {g : Graph} {t : Triple} (h : t ∈ typeDomainSubAll g) :
    RbDerives g t := by
  simp only [typeDomainSubAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    simp only [List.mem_flatMap] at h
    obtain ⟨v, hv, h⟩ := h
    split at h
    · rename_i h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      simp only [List.mem_singleton] at h
      subst h
      exact RbDerives.typeDomainSub (mem_of_parts hu h1.1 h1.2 rfl)
        (mem_of_parts hv rfl h2.1 h2.2)
    · simp at h
  · simp at h

theorem avfRangeAll_derives {g : Graph} {t : Triple} (h : t ∈ avfRangeAll g) :
    RbDerives g t := by
  simp only [avfRangeAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨r, hr, v, hv, p, hp, w, hw, rfl⟩ := h
    obtain ⟨hvg, hvs, hvp⟩ := mem_withSubjPred hv
    obtain ⟨hwg, hws, hwp⟩ := mem_withSubjPred hw
    exact RbDerives.avfRange (mem_of_parts hu h1.1 h1.2 (mem_asSubject hr))
      (mem_of_parts hvg hvs hvp (mem_asSubject hp)) (mem_of_parts hwg hws hwp rfl)
  · simp at h

theorem svfDomainAll_derives {g : Graph} {t : Triple} (h : t ∈ svfDomainAll g) :
    RbDerives g t := by
  simp only [svfDomainAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨v, hv, p, hp, w, hw, rfl⟩ := h
    obtain ⟨hvg, hvs, hvp⟩ := mem_withSubjPred hv
    obtain ⟨hwg, hws, hwp⟩ := mem_withSubjPred hw
    exact RbDerives.svfDomain (mem_of_parts hu rfl h1.1 h1.2)
      (mem_of_parts hvg hvs hvp (mem_asSubject hp)) (mem_of_parts hwg hws hwp rfl)
  · simp at h

theorem emptySubPropAll_derives {g : Graph} {t : Triple} (h : t ∈ emptySubPropAll g) :
    RbDerives g t := by
  simp only [emptySubPropAll, List.mem_flatMap] at h
  obtain ⟨u, hu, h⟩ := h
  split at h
  · rename_i hp
    have hp' : u.p = rdfsRange := Subtype.ext (by simpa using hp)
    simp only [List.mem_flatMap] at h
    obtain ⟨d1, hd1, v, hv, d2, hd2, h⟩ := h
    split at h
    · rename_i hdis
      simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨w, ⟨hw, hwp, hwo⟩, rfl⟩ := h
      obtain ⟨hvg, hvs, hvp⟩ := mem_withSubjPred hv
      exact RbDerives.emptySubProp (mem_of_parts hu rfl hp' (mem_asIri hd1))
        (mem_of_parts hvg hvs hvp (mem_asIri hd2)) hdis (mem_of_parts hw rfl hwp hwo)
    · simp at h
  · simp at h

theorem rbConclusions_derives {g goal : Graph} {t : Triple} (h : t ∈ rbConclusions g goal) :
    RbDerives g t := by
  simp only [rbConclusions, List.mem_append] at h
  rcases h with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact axiomsFor_derives h
  · exact vocabTypeAll_derives h
  · exact universalFor_derives h
  · exact compSymAll_derives h
  · exact allDiffAll_derives h
  · exact singletonRange_derives h
  · exact singletonDomain_derives h
  · exact typeDomainSubAll_derives h
  · exact avfRangeAll_derives h
  · exact svfDomainAll_derives h
  · exact emptySubPropAll_derives h

/-- Every triple `rbConclusions` lists is OWL 2 RDF-Based entailed by `g`. -/
theorem rbConclusions_entailed {g goal : Graph} {t : Triple} (h : t ∈ rbConclusions g goal) :
    RbEntails g [t] :=
  rbDerives_entailed (rbConclusions_derives h)

/-! ## The comprehension witnesses of the RL closure are not evidence here

The OWL 2 RL/RDF closure of this tree has three `[ext]` rows that mint a
blank node standing for a class expression (`caxDwToComplement`,
`clsMaxqc1ToComplement`, `minCard1Comprehension`; labels
`__rl_comp__…`, `__rl_minc1__…`, `RL.rlReservedBnode`). Their soundness
(`RLSemantics.RlCondCompDw`, `RlCondCompMqc`, `RlCondMinc1`) rests on
the comprehension conditions of RDF-Based Semantics §8, which are NOT
part of the normative semantics (§9, "Correspondence Theorem and
Comprehension Conditions [DEV]": combining them with §5 "would lead to
formal inconsistency"). So the regime never uses a triple that mentions
such a witness as evidence: `withoutCompWitness` removes them before a
conclusion is matched and before the clash check. -/

def tripleMentionsCompWitness (t : Triple) : Bool :=
  (match t.s with | .bnode b => rlReservedBnode b | _ => false) ||
  (match t.o with | .bnode b => rlReservedBnode b | _ => false)

def withoutCompWitness (g : Graph) : Graph :=
  g.filter (fun t => !tripleMentionsCompWitness t)

theorem withoutCompWitness_sub {g : Graph} {t : Triple} (h : t ∈ withoutCompWitness g) :
    t ∈ g := (List.mem_filter.mp h).1

#guard (withoutCompWitness
  [⟨.bnode "__rl_minc1__http://ex/p", rdfType, .iri owlRestriction⟩,
   ⟨.iri ⟨"http://ex/a", rfl⟩, rdfType, .iri owlThing⟩]).length == 1

/-! ## The regime, as a pure function

`rbSaturate g goal fuel n`: `n` rounds of (OWL 2 RL/RDF closure at
`fuel`, then `rbConclusions` over it), then a last closure. The harness
runs the same alternation in `IO` with the indexed closure and a wall
clock (`Harness/OwlProbe.lean`, `rbClosureIO`); this definition is what
the `#guard` cases of `RdfBased/Tests.lean` run. -/

def rbRound (g goal : Graph) (fuel : Nat) : Graph :=
  let c := closure g fuel
  addAll c (rbConclusions c goal)

def rbSaturate (g goal : Graph) (fuel : Nat) : Nat → Graph
  | 0     => closure g fuel
  | n + 1 => rbSaturate (rbRound g goal fuel) goal fuel n

end L4Factoidal.OWL.RdfBased
