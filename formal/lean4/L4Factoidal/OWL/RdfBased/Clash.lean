/-
L4Factoidal.OWL.RdfBased.Clash — clash rows for the OWL 2 RDF-Based
Semantics regime, each proved against `RdfBased/Spec.lean`.

Source: OWL 2 Web Ontology Language RDF-Based Semantics (Second
Edition), W3C Recommendation 11 December 2012,
https://www.w3.org/TR/owl2-rdf-based-semantics/. Section and table
numbers are that document's. Design record:
`docs/designissues/2026-10-10-owl2-rdf-based-semantics.md` (§ 4.5);
issues https://github.com/danbri/factoidal/issues/721 and
https://github.com/danbri/factoidal/issues/733.

## Shape

`RbClash g` — one row of the table below matches the graph `g`.
`rbClash_sound`: in every interpretation that meets
`RdfBasedConditions`, no blank-node assignment makes `g` true. So a
graph on which a row fires is OWL 2 RDF-Based inconsistent (Definition
4.4; the bundle admits every OWL 2 RDF-Based interpretation, see the
`Spec.lean` header). The executable side, `rbClashAny g`, is proved to
answer `true` only on a graph that `RbClash` holds of
(`rbClashAny_spec`).

The regime (`Harness/OwlProbe.lean`, `--rdf-based`) checks these rows
next to the OWL 2 RL/RDF clash rows of `detectClashPlusI`.

## The rows, each with the conditions its proof reads

| constructor | premise | conditions (RDF-Based Semantics) |
|---|---|---|
| `thingEnum` | `c owl:oneOf (a)` or `c owl:oneOf ()`, where `c` is `owl:Thing` or `rdfs:Resource` or `owl:Thing rdfs:subClassOf c` | Tables 5.2, 5.5, 5.8 |
| `svfAvfDt` | `x rdf:type r1`, `r1 owl:someValuesFrom d1`, `r1 owl:onProperty p`, `x rdf:type r2`, `r2 owl:allValuesFrom d2`, `r2 owl:onProperty p`, the datatypes `d1`, `d2` with disjoint value spaces | Table 5.6, the datatype map (§ 4.1) |

`thingEnum` (issue 733, `WebOnt-Thing-005`): Table 5.5 makes
`ICEXT(I(c)) = {I(a)}`, and Table 5.2 (`ICEXT(I(owl:Thing)) = IR`) with
Table 5.8 makes every element of IR a member of `ICEXT(I(c))`. So IR =
`{I(a)}`, and `I(owl:Thing) = I(owl:Nothing) = I(a)`. Table 5.2 puts
`I(a)` in `ICEXT(I(owl:Thing))` and gives `ICEXT(I(owl:Nothing)) = ∅`:
a contradiction. With the empty enumeration, `ICEXT(I(c)) = ∅` while
IR is not empty (Table 5.1, "IR: S ≠ ∅").

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RdfBased.Engine

namespace L4Factoidal.OWL.RdfBased

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.RDFS (rdfsClass rdfsLiteral rdfProperty rdfsResource rdfList)

/-! ## The clash relation -/

inductive RbClash (g : Graph) : Prop where
  | thingEnum {c : Subject} {l : Term} {es : List Term}
      (hu : c = .iri owlThing ∨ c = .iri rdfsResource ∨
        (⟨.iri owlThing, rdfsSubClassOf, c.toTerm⟩ : Triple) ∈ g)
      (ho : (⟨c, owlOneOf, l⟩ : Triple) ∈ g) (hl : ListDenotes g l es)
      (hn : es.length ≤ 1) : RbClash g
  | svfAvfDt {x r1 r2 : Subject} {p : Term} {d1 d2 : WfIri}
      (h1 : (⟨x, rdfType, r1.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨r1, owlSomeValuesFrom, .iri d1⟩ : Triple) ∈ g)
      (h3 : (⟨r1, owlOnProperty, p⟩ : Triple) ∈ g)
      (h4 : (⟨x, rdfType, r2.toTerm⟩ : Triple) ∈ g)
      (h5 : (⟨r2, owlAllValuesFrom, .iri d2⟩ : Triple) ∈ g)
      (h6 : (⟨r2, owlOnProperty, p⟩ : Triple) ∈ g)
      (hd : xsdValueSpacesDisjoint d1 d2 = true) : RbClash g

/-! ## Soundness -/

section Soundness

variable {i : Interp} (hc : RdfBasedConditions i)
include hc

theorem thing_universal' (x : i.idom) : icext i x (i.iIri owlThing) :=
  hc.universal owlThing (by decide) x

/-- A class every element of IR belongs to has no enumeration with at
most one member (Tables 5.1, 5.2, 5.5). -/
theorem no_small_universal_enum {z s : i.idom} {as : List i.idom}
    (hseq : SeqIs i s as) (ho : i.iext (i.iIri owlOneOf) z s)
    (hall : ∀ x : i.idom, icext i x z) (hn : as.length ≤ 1) : False := by
  obtain ⟨_, hext⟩ := (hc.oneOf _ _ _ hseq).mp ho
  have hmem : ∀ x : i.idom, x ∈ as := fun x => (hext x).mp (hall x)
  match as, hn, hmem with
  | [], _, hmem => exact absurd (hmem i.idomWit) List.not_mem_nil
  | [a], _, hmem =>
      have e1 := hmem (i.iIri owlThing)
      have e2 := hmem (i.iIri owlNothing)
      simp only [List.mem_singleton] at e1 e2
      have h1 : icext i (i.iIri owlNothing) (i.iIri owlThing) := thing_universal' hc _
      have h2 : i.iIri owlThing = i.iIri owlNothing := e1.trans e2.symm
      rw [h2] at h1
      exact hc.nothing _ h1
  | _ :: _ :: _, hn, _ => simp at hn

theorem rbClash_sound {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    (h : RbClash g) : False := by
  cases h with
  | thingEnum hu ho hl hn =>
      rename_i c l es
      have hseq := holds_seqIs (fun u hu => hA u hu) hl
      have hall : ∀ x : i.idom, icext i x (denotSubject i A c) := by
        intro x
        rcases hu with rfl | rfl | hs
        · exact thing_universal' hc x
        · exact hc.universal rdfsResource (by decide) x
        · have t := hA _ hs
          simp only [TripleHolds, denot_toTerm, denotSubject] at t
          exact ((hc.subClassOf _ _).mp t).2.2 x (thing_universal' hc x)
      exact no_small_universal_enum hc hseq (hA _ ho) hall (by simpa using hn)
  | svfAvfDt h1 h2 h3 h4 h5 h6 hd =>
      rename_i x r1 r2 p d1 d2
      have t1 := hA _ h1
      have t4 := hA _ h4
      simp only [TripleHolds, denot_toTerm] at t1 t4
      have t2 : i.iext (i.iIri owlSomeValuesFrom) (denotSubject i A r1) (i.iIri d1) := hA _ h2
      have t3 : i.iext (i.iIri owlOnProperty) (denotSubject i A r1) (denotTerm i A p) := hA _ h3
      have t5 : i.iext (i.iIri owlAllValuesFrom) (denotSubject i A r2) (i.iIri d2) := hA _ h5
      have t6 : i.iext (i.iIri owlOnProperty) (denotSubject i A r2) (denotTerm i A p) := hA _ h6
      obtain ⟨z, hz, hzd1⟩ := hc.someValuesFromSub _ _ _ _ t2 t3 t1
      have hzd2 := hc.allValuesFromSub _ _ _ _ z t5 t6 t4 hz
      exact hc.disjointDatatypes d1 d2 hd z ⟨hzd1, hzd2⟩

end Soundness

/-- A graph a row fires on has no OWL 2 RDF-Based model (with
`RdfBasedConditions` as the reading of "OWL 2 RDF-Based
interpretation"; see the `Spec.lean` header). -/
theorem rbClash_unsat {g : Graph} (h : RbClash g) {i : Interp} (hc : RdfBasedConditions i) :
    ¬ Satisfies i g := by
  rintro ⟨A, hA⟩
  exact rbClash_sound hc hA h

/-- `RbEntails g [t]` for every `t`: an inconsistent graph entails
everything (Definition 4.5, read over the bundle). -/
theorem rbClash_entails {g : Graph} (h : RbClash g) (g2 : Graph) : RbEntails g g2 := by
  intro i hc hs
  exact absurd hs (rbClash_unsat h hc)

/-! ## The rows, executable -/

/-- `thingEnum`: an enumeration with at most one member on `owl:Thing`,
`rdfs:Resource`, or a class `owl:Thing` is a subclass of. -/
def thingEnumAny (g : Graph) : Bool :=
  (g.filter (fun t => t.p == owlOneOf)).any (fun t =>
    (t.s == Subject.iri owlThing || t.s == Subject.iri rdfsResource ||
     memB g ⟨.iri owlThing, rdfsSubClassOf, t.s.toTerm⟩) &&
    (listSeqs g t.o (listFuel g)).any (fun es => decide (es.length ≤ 1)))

/-- `svfAvfDt`: read from the (rare) `owl:someValuesFrom` triples whose
filler is a datatype IRI of a known value-space family. -/
def svfAvfDtAny (g : Graph) : Bool :=
  (g.filter (fun t => t.p == owlSomeValuesFrom)).any (fun s =>
    match s.o with
    | .iri d1 =>
        (xsdFamily d1).isSome &&
        (withSubjPred g s.s owlOnProperty).any (fun op =>
          (withPredObj g rdfType s.s.toTerm).any (fun tx =>
            (withSubjPred g tx.s rdfType).any (fun ty =>
              (asSubject ty.o).any (fun r2 =>
                (withSubjPred g r2 owlAllValuesFrom).any (fun av =>
                  match av.o with
                  | .iri d2 => xsdValueSpacesDisjoint d1 d2 &&
                      memB g ⟨r2, owlOnProperty, op.o⟩
                  | _ => false)))))
    | _ => false)

def rbClashAny (g : Graph) : Bool := thingEnumAny g || svfAvfDtAny g

theorem thingEnumAny_spec {g : Graph} (h : thingEnumAny g = true) : RbClash g := by
  simp only [thingEnumAny, List.any_eq_true, List.mem_filter, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨t, ⟨ht, hp⟩, hu, es, hes, hn⟩ := h
  have hm : (⟨t.s, owlOneOf, t.o⟩ : Triple) ∈ g := mem_of_parts ht rfl hp rfl
  have hl := listSeqs_sound g _ _ hes
  refine RbClash.thingEnum ?_ hm hl hn
  rcases hu with (h1 | h2) | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (mem_of_memB h3))

theorem svfAvfDtAny_spec {g : Graph} (h : svfAvfDtAny g = true) : RbClash g := by
  simp only [svfAvfDtAny, List.any_eq_true, List.mem_filter, beq_iff_eq] at h
  obtain ⟨s, ⟨hs, hsp⟩, h⟩ := h
  split at h
  · rename_i d1 hso
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨_, op, hop, tx, htx, ty, hty, r2, hr2, av, hav, h⟩ := h
    split at h
    · rename_i d2 havo
      simp only [Bool.and_eq_true] at h
      obtain ⟨hd, hm⟩ := h
      obtain ⟨hopg, hops, hopp⟩ := mem_withSubjPred hop
      obtain ⟨htxg, htxp, htxo⟩ := mem_withPredObj htx
      obtain ⟨htyg, htys, htyp⟩ := mem_withSubjPred hty
      obtain ⟨havg, havs, havp⟩ := mem_withSubjPred hav
      exact RbClash.svfAvfDt (x := tx.s) (r1 := s.s) (r2 := r2) (p := op.o)
        (mem_of_parts htxg rfl htxp htxo)
        (mem_of_parts hs rfl hsp hso)
        (mem_of_parts hopg hops hopp rfl)
        (mem_of_parts htyg htys htyp (mem_asSubject hr2))
        (mem_of_parts havg havs havp havo)
        (mem_of_memB hm) hd
    · simp at h
  · simp at h

theorem rbClashAny_spec {g : Graph} (h : rbClashAny g = true) : RbClash g := by
  simp only [rbClashAny, Bool.or_eq_true] at h
  rcases h with h | h
  · exact thingEnumAny_spec h
  · exact svfAvfDtAny_spec h

/-- What the regime reads: a `true` answer is a proof of inconsistency. -/
theorem rbClashAny_unsat {g : Graph} (h : rbClashAny g = true) {i : Interp}
    (hc : RdfBasedConditions i) : ¬ Satisfies i g :=
  rbClash_unsat (rbClashAny_spec h) hc

end L4Factoidal.OWL.RdfBased
