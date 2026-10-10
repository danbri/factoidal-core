/-
L4Factoidal.OWL.RdfBased.Rules — the inference rules the OWL 2
RDF-Based Semantics regime adds to the OWL 2 RL/RDF closure, each
proved sound against `RdfBased/Spec.lean`.

Design record: `docs/designissues/2026-10-10-owl2-rdf-based-semantics.md`
(§ 4, the rules); issue https://github.com/danbri/factoidal/issues/721.

## Shape

`RbDerives g t` — one application of one rule to the graph `g`
derives `t`. `rbDerives_sound`: in every interpretation that meets
`RdfBasedConditions`, under every blank-node assignment that makes `g`
true, `t` is true. The executable side, `rbConclusions g goal`, lists
candidate triples; `rbConclusions_derives` proves each of them is
`RbDerives g`. So every triple the regime adds is entailed by `g`
under the OWL 2 RDF-Based Semantics (Spec.lean header: the bundle
admits every OWL 2 RDF-Based interpretation).

No rule mints a blank node. No rule reads the comprehension conditions
of §8, which are not normative (§9, "Correspondence Theorem and
Comprehension Conditions [DEV]").

## The rules, each with the conditions its proof reads

| constructor | conclusion | conditions (RDF-Based Semantics) |
|---|---|---|
| `ax` | one of `rbAxioms` (premise-free) | Tables 5.2, 5.3, 5.5, 5.8, 5.9 |
| `vocabType` | `x rdf:type E2` from `x rdf:type E1`, `ICEXT(E1) ⊆ ICEXT(E2)` | Tables 5.1, 5.2 |
| `universal` | `x rdf:type owl:Thing` / `rdfs:Resource` | Table 5.2 |
| `compSym` | `b owl:complementOf a` from `a owl:complementOf b` | Table 5.4 |
| `allDiff` | `aj owl:differentFrom ak` from an `owl:AllDifferent` list | Tables 5.9, 5.10 |
| `funSingleton` | `p rdf:type owl:FunctionalProperty` when the range is a one-element enumeration | Tables 5.5, 5.8, 5.13 |
| `ifpSingleton` | `p rdf:type owl:InverseFunctionalProperty`, the domain dual | Tables 5.5, 5.8, 5.13 |
| `typeDomainSub` | `x rdfs:subClassOf y` from `rdf:type rdfs:domain y`, `x rdf:type rdfs:Class` | Table 5.8 |
| `avfRange` | `p rdfs:range c` from `owl:Thing rdfs:subClassOf ∀p.c` | Tables 5.2, 5.3, 5.6, 5.8 |
| `svfDomain` | `p rdfs:domain c` from `∃p.owl:Thing rdfs:subClassOf c` | Tables 5.2, 5.3, 5.6, 5.8 |
| `emptySubProp` | `p rdfs:subPropertyOf q` when two ranges of `p` are disjoint datatypes | Table 5.8, the datatype map |
| `oneOfSub` | `c1 rdfs:subClassOf c2` when every member of `c1`'s enumeration is a member of `c2`'s | Tables 5.5, 5.8 |
| `unionSub` | `c1 rdfs:subClassOf c2` when every operand of `c1`'s union is an operand of `c2`'s | Tables 5.4, 5.8 |
| `interSub` | `c1 rdfs:subClassOf c2` when every operand of `c2`'s intersection is an operand of `c1`'s | Tables 5.4, 5.8 |
| `literalValue` | `s p "s2"^^d` from `s p "s1"^^u` when `u` is `d` or `u owl:sameAs d`, `d` is `xsd:decimal` or `xsd:integer`, and the lexical forms denote one value | § 4.2 (IL), Table 5.9 |
| `hvEqProp` | `p owl:equivalentProperty q` when `p`, `q` are functional with domain `d`, and `d` is a subclass of `∋ v` restrictions on `p` and on `q` with the same value | Tables 5.6, 5.8, 5.9, 5.13 |
| `minCardSucc` | `x rdf:type z` from `z owl:minCardinality n` (n = 0 or 1), `z owl:onProperty p`, `x p y` | Table 5.6, § 4.2 |

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RdfBased.Spec
import L4Factoidal.OWL.RLSemantics
import L4Factoidal.OWL.RLTheorems

namespace L4Factoidal.OWL.RdfBased

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.RDFS (rdfsClass rdfsLiteral rdfProperty rdfsResource rdfList)

/-! ## Premise-free triples -/

/-- `E rdf:type rdfs:Class` for every class Table 5.2 lists. -/
def axClassTriples : List Triple :=
  vocabClasses.map (fun e => ⟨.iri e, rdfType, .iri rdfsClass⟩)

/-- `E1 rdfs:subClassOf E2` for every inclusion of `extSubTable`. -/
def axSubTriples : List Triple :=
  extSubTable.map (fun e => ⟨.iri e.1, rdfsSubClassOf, .iri e.2⟩)

/-- `E1 owl:equivalentClass E2` where `extSubTable` holds both
inclusions. -/
def axEqTriples : List Triple :=
  (extSubTable.filter (fun e => extSubTable.contains (e.2, e.1))).map
    (fun e => ⟨.iri e.1, owlEquivalentClass, .iri e.2⟩)

/-- The part, domain and range of every transcribed Table 5.3 row. -/
def axPropTriples : List Triple :=
  vocabPropTable.flatMap (fun r =>
    [⟨.iri r.e, rdfType, .iri r.part⟩, ⟨.iri r.e, rdfsDomain, .iri r.dom⟩,
     ⟨.iri r.e, rdfsRange, .iri r.rng⟩])

/-- `owl:Nothing owl:oneOf rdf:nil`: Table 5.5 with n = 0, since
`ICEXT(I(owl:Nothing)) = ∅` (Table 5.2) and `I(rdf:nil)` is the empty
sequence (§5, "Sequence expressions"). -/
def axNothingOneOf : Triple := ⟨.iri owlNothing, owlOneOf, .iri rdfNil⟩

def rbAxioms : List Triple :=
  axClassTriples ++ axSubTriples ++ axEqTriples ++ axPropTriples ++ [axNothingOneOf]

/-! ## The rule relation -/

inductive RbDerives (g : Graph) : Triple → Prop where
  | ax {t : Triple} (h : t ∈ rbAxioms) : RbDerives g t
  | vocabType {s : Subject} {e1 e2 : WfIri}
      (hm : (⟨s, rdfType, .iri e1⟩ : Triple) ∈ g) (he : (e1, e2) ∈ extSubTable) :
      RbDerives g ⟨s, rdfType, .iri e2⟩
  | universal (s : Subject) {c : WfIri} (hc : c ∈ universalClasses) :
      RbDerives g ⟨s, rdfType, .iri c⟩
  | compSym {a b : Subject}
      (h : (⟨a, owlComplementOf, b.toTerm⟩ : Triple) ∈ g) :
      RbDerives g ⟨b, owlComplementOf, a.toTerm⟩
  | allDiff {z sj : Subject} {mp : WfIri} {lst aj ak : Term} {es : List Term} {j k : Nat}
      (hmp : mp = owlMembers ∨ mp = owlDistinctMembers)
      (hty : (⟨z, rdfType, .iri owlAllDifferent⟩ : Triple) ∈ g)
      (hm : (⟨z, mp, lst⟩ : Triple) ∈ g) (hl : ListDenotes g lst es)
      (hjk : j ≠ k) (hj : es[j]? = some aj) (hk : es[k]? = some ak)
      (hs : aj = sj.toTerm) :
      RbDerives g ⟨sj, owlDifferentFrom, ak⟩
  | funSingleton {p c : Subject} {lst a : Term}
      (hr : (⟨p, rdfsRange, c.toTerm⟩ : Triple) ∈ g)
      (ho : (⟨c, owlOneOf, lst⟩ : Triple) ∈ g) (hl : ListDenotes g lst [a]) :
      RbDerives g ⟨p, rdfType, .iri owlFunctionalProperty⟩
  | ifpSingleton {p c : Subject} {lst a : Term}
      (hd : (⟨p, rdfsDomain, c.toTerm⟩ : Triple) ∈ g)
      (ho : (⟨c, owlOneOf, lst⟩ : Triple) ∈ g) (hl : ListDenotes g lst [a]) :
      RbDerives g ⟨p, rdfType, .iri owlInverseFunctionalProperty⟩
  | typeDomainSub {x : Subject} {y : Term}
      (hd : (⟨.iri rdfType, rdfsDomain, y⟩ : Triple) ∈ g)
      (hx : (⟨x, rdfType, .iri rdfsClass⟩ : Triple) ∈ g) :
      RbDerives g ⟨x, rdfsSubClassOf, y⟩
  | avfRange {r p : Subject} {c : Term}
      (h1 : (⟨.iri owlThing, rdfsSubClassOf, r.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨r, owlOnProperty, p.toTerm⟩ : Triple) ∈ g)
      (h3 : (⟨r, owlAllValuesFrom, c⟩ : Triple) ∈ g) :
      RbDerives g ⟨p, rdfsRange, c⟩
  | svfDomain {r p : Subject} {c : Term}
      (h1 : (⟨r, owlSomeValuesFrom, .iri owlThing⟩ : Triple) ∈ g)
      (h2 : (⟨r, owlOnProperty, p.toTerm⟩ : Triple) ∈ g)
      (h3 : (⟨r, rdfsSubClassOf, c⟩ : Triple) ∈ g) :
      RbDerives g ⟨p, rdfsDomain, c⟩
  | emptySubProp {p q : Subject} {d1 d2 : WfIri}
      (h1 : (⟨p, rdfsRange, .iri d1⟩ : Triple) ∈ g)
      (h2 : (⟨p, rdfsRange, .iri d2⟩ : Triple) ∈ g)
      (hd : xsdValueSpacesDisjoint d1 d2 = true)
      (hq : (⟨q, rdfType, .iri rdfProperty⟩ : Triple) ∈ g) :
      RbDerives g ⟨p, rdfsSubPropertyOf, q.toTerm⟩
  | oneOfSub {c1 c2 : Subject} {l1 l2 : Term} {es1 es2 : List Term}
      (h1 : (⟨c1, owlOneOf, l1⟩ : Triple) ∈ g) (h2 : (⟨c2, owlOneOf, l2⟩ : Triple) ∈ g)
      (hl1 : ListDenotes g l1 es1) (hl2 : ListDenotes g l2 es2)
      (hsub : ∀ e ∈ es1, e ∈ es2) :
      RbDerives g ⟨c1, rdfsSubClassOf, c2.toTerm⟩
  | unionSub {c1 c2 : Subject} {l1 l2 : Term} {es1 es2 : List Term}
      (h1 : (⟨c1, owlUnionOf, l1⟩ : Triple) ∈ g) (h2 : (⟨c2, owlUnionOf, l2⟩ : Triple) ∈ g)
      (hl1 : ListDenotes g l1 es1) (hl2 : ListDenotes g l2 es2)
      (hne1 : es1 ≠ []) (hne2 : es2 ≠ [])
      (hsub : ∀ e ∈ es1, e ∈ es2) :
      RbDerives g ⟨c1, rdfsSubClassOf, c2.toTerm⟩
  | interSub {c1 c2 : Subject} {l1 l2 : Term} {es1 es2 : List Term}
      (h1 : (⟨c1, owlIntersectionOf, l1⟩ : Triple) ∈ g)
      (h2 : (⟨c2, owlIntersectionOf, l2⟩ : Triple) ∈ g)
      (hl1 : ListDenotes g l1 es1) (hl2 : ListDenotes g l2 es2)
      (hne1 : es1 ≠ []) (hne2 : es2 ≠ [])
      (hsub : ∀ e ∈ es2, e ∈ es1) :
      RbDerives g ⟨c1, rdfsSubClassOf, c2.toTerm⟩
  | literalValue {s : Subject} {p : WfIri} {l1 l2 : WfLiteral}
      (hm : (⟨s, p, .literal l1⟩ : Triple) ∈ g)
      (hu : l1.val.datatype = l2.val.datatype ∨
        (⟨.iri l1.val.datatype, owlSameAs, .iri l2.val.datatype⟩ : Triple) ∈ g)
      (hl : l1.val.langTag = none)
      (hv : sameDecimalValue l2.val.datatype l1.val.lexicalForm l2.val.lexicalForm = true) :
      RbDerives g ⟨s, p, .literal l2⟩
  | hvEqProp {p q d r1 r2 : Subject} {v : Term}
      (hdp : (⟨p, rdfsDomain, d.toTerm⟩ : Triple) ∈ g)
      (hdq : (⟨q, rdfsDomain, d.toTerm⟩ : Triple) ∈ g)
      (hs1 : (⟨d, rdfsSubClassOf, r1.toTerm⟩ : Triple) ∈ g)
      (hs2 : (⟨d, rdfsSubClassOf, r2.toTerm⟩ : Triple) ∈ g)
      (ho1 : (⟨r1, owlOnProperty, p.toTerm⟩ : Triple) ∈ g)
      (hv1 : (⟨r1, owlHasValue, v⟩ : Triple) ∈ g)
      (ho2 : (⟨r2, owlOnProperty, q.toTerm⟩ : Triple) ∈ g)
      (hv2 : (⟨r2, owlHasValue, v⟩ : Triple) ∈ g)
      (hfp : (⟨p, rdfType, .iri owlFunctionalProperty⟩ : Triple) ∈ g)
      (hfq : (⟨q, rdfType, .iri owlFunctionalProperty⟩ : Triple) ∈ g) :
      RbDerives g ⟨p, owlEquivalentProperty, q.toTerm⟩
  | minCardSucc {x z : Subject} {p : WfIri} {y : Term} {l : WfLiteral} {k : Int}
      (hm : (⟨z, owlMinCardinality, .literal l⟩ : Triple) ∈ g)
      (ho : (⟨z, owlOnProperty, .iri p⟩ : Triple) ∈ g)
      (hxy : (⟨x, p, y⟩ : Triple) ∈ g) (hk : intLitValue l = some k) (h0 : 0 ≤ k)
      (h1 : k ≤ 1) :
      RbDerives g ⟨x, rdfType, z.toTerm⟩

/-! ## Table facts, checked by evaluation -/

theorem extSub_classes : ∀ e ∈ extSubTable, e.1 ∈ vocabClasses ∧ e.2 ∈ vocabClasses := by
  decide

theorem propRow_facts : ∀ r ∈ vocabPropTable,
    (r.part = rdfProperty ∨ (r.part, rdfProperty) ∈ extSubTable) ∧
    r.dom ∈ vocabClasses ∧ r.rng ∈ vocabClasses := by
  decide

def onPropertyRow : PropRow := ⟨owlOnProperty, rdfProperty, owlRestriction, rdfProperty⟩
def allValuesFromRow : PropRow := ⟨owlAllValuesFrom, rdfProperty, owlRestriction, rdfsClass⟩

theorem onPropertyRow_mem : onPropertyRow ∈ vocabPropTable := by decide
theorem allValuesFromRow_mem : allValuesFromRow ∈ vocabPropTable := by decide
theorem thing_universal : owlThing ∈ universalClasses := by decide
theorem nothing_class : owlNothing ∈ vocabClasses := by decide

/-! ## Soundness -/

section Soundness

variable {i : Interp} (hc : RdfBasedConditions i)
include hc

theorem class_of_vocab {e : WfIri} (he : e ∈ vocabClasses) : IC i (i.iIri e) :=
  hc.vocabClasses e he

theorem prop_of_row {r : PropRow} (hr : r ∈ vocabPropTable) : IP i (i.iIri r.e) := by
  have hpart := (hc.vocabProps r hr).1
  rcases (propRow_facts r hr).1 with h | h
  · unfold IP; rw [← h]; exact hpart
  · exact hc.extSub _ h _ hpart

theorem ax_holds {t : Triple} (h : t ∈ rbAxioms) (A : BnodeAssignment i.idom) :
    TripleHolds i A t := by
  simp only [rbAxioms, List.mem_append, List.mem_singleton] at h
  rcases h with ((((h | h) | h) | h) | h)
  · simp only [axClassTriples, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    exact class_of_vocab hc he
  · simp only [axSubTriples, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    obtain ⟨h1, h2⟩ := extSub_classes e he
    exact (hc.subClassOf _ _).mpr
      ⟨class_of_vocab hc h1, class_of_vocab hc h2, fun x hx => hc.extSub e he x hx⟩
  · simp only [axEqTriples, List.mem_map, List.mem_filter, List.contains_iff_mem] at h
    obtain ⟨e, ⟨he, hrev⟩, rfl⟩ := h
    obtain ⟨h1, h2⟩ := extSub_classes e he
    exact hc.equivalentClassIf _ _ (class_of_vocab hc h1) (class_of_vocab hc h2)
      (fun x => ⟨fun hx => hc.extSub e he x hx, fun hx => hc.extSub _ hrev x hx⟩)
  · simp only [axPropTriples, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨_, hdom, hrng⟩ := propRow_facts r hr
    rcases h with rfl | rfl | rfl
    · exact (hc.vocabProps r hr).1
    · exact (hc.domain _ _).mpr ⟨prop_of_row hc hr, class_of_vocab hc hdom,
        fun x y hxy => ((hc.vocabProps r hr).2 x y hxy).1⟩
    · exact (hc.range _ _).mpr ⟨prop_of_row hc hr, class_of_vocab hc hrng,
        fun x y hxy => ((hc.vocabProps r hr).2 x y hxy).2⟩
  · subst h
    show i.iext (i.iIri owlOneOf) (i.iIri owlNothing) (i.iIri rdfNil)
    exact (hc.oneOf (i.iIri owlNothing) (i.iIri rdfNil) [] rfl).mpr
      ⟨class_of_vocab hc nothing_class,
       fun x => ⟨fun hx => absurd hx (hc.nothing x), fun hx => absurd hx List.not_mem_nil⟩⟩

theorem rbDerives_sound {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {t : Triple} (h : RbDerives g t) : TripleHolds i A t := by
  cases h with
  | ax h => exact ax_holds hc h A
  | vocabType hm he =>
      have := hA _ hm
      exact hc.extSub _ he _ this
  | universal s hu => exact hc.universal _ hu _
  | compSym h =>
      have hh := hA _ h
      simp only [TripleHolds, denot_toTerm] at hh ⊢
      obtain ⟨hza, hzb, hext⟩ := (hc.complementOf _ _).mp hh
      refine (hc.complementOf _ _).mpr ⟨hzb, hza, fun x => ?_⟩
      constructor
      · intro hb ha; exact (hext x).mp ha hb
      · intro hna
        exact Classical.byContradiction (fun hnb => hna ((hext x).mpr hnb))
  | allDiff hmp hty hm hl hjk hj hk hs =>
      rename_i z sj mp lst aj ak es j k
      have hseq := holds_seqIs (fun u hu => hA u hu) hl
      have hz : icext i (denotSubject i A z) (i.iIri owlAllDifferent) := hA _ hty
      have hmz : i.iext (i.iIri mp) (denotSubject i A z) (denotTerm i A lst) := hA _ hm
      have hne := hc.allDifferent mp hmp _ _ _ hseq hz hmz j k
        (denotTerm i A aj) (denotTerm i A ak) hjk
        (by simp [List.getElem?_map, hj]) (by simp [List.getElem?_map, hk])
      show i.iext (i.iIri owlDifferentFrom) (denotSubject i A sj) (denotTerm i A ak)
      rw [← denot_toTerm, ← hs]
      exact hc.differentFromIf _ _ hne
  | funSingleton hr ho hl =>
      rename_i p c lst a
      have hrng := hA _ hr
      simp only [TripleHolds, denot_toTerm] at hrng
      obtain ⟨hpP, _, hry⟩ := (hc.range _ _).mp hrng
      have hseq := holds_seqIs (fun u hu => hA u hu) hl
      obtain ⟨_, hext⟩ := (hc.oneOf _ _ _ hseq).mp (hA _ ho)
      refine hc.functionalIf _ hpP (fun x y1 y2 h1 h2 => ?_)
      have e1 := (hext y1).mp (hry x y1 h1)
      have e2 := (hext y2).mp (hry x y2 h2)
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at e1 e2
      rw [e1, e2]
  | ifpSingleton hd ho hl =>
      rename_i p c lst a
      have hdom := hA _ hd
      simp only [TripleHolds, denot_toTerm] at hdom
      obtain ⟨hpP, _, hdx⟩ := (hc.domain _ _).mp hdom
      have hseq := holds_seqIs (fun u hu => hA u hu) hl
      obtain ⟨_, hext⟩ := (hc.oneOf _ _ _ hseq).mp (hA _ ho)
      refine hc.inverseFunctionalIf _ hpP (fun x1 x2 y h1 h2 => ?_)
      have e1 := (hext x1).mp (hdx x1 y h1)
      have e2 := (hext x2).mp (hdx x2 y h2)
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at e1 e2
      rw [e1, e2]
  | typeDomainSub hd hx =>
      rename_i x y
      obtain ⟨_, hy, hdom⟩ := (hc.domain _ _).mp (hA _ hd)
      have hxc : IC i (denotSubject i A x) := hA _ hx
      exact (hc.subClassOf _ _).mpr ⟨hxc, hy, fun z hz => hdom z _ hz⟩
  | avfRange h1 h2 h3 =>
      rename_i r p c
      have t1 := hA _ h1
      have t2 := hA _ h2
      have t3 := hA _ h3
      simp only [TripleHolds, denot_toTerm, denotSubject] at t1 t2 t3
      obtain ⟨_, _, hsub⟩ := (hc.subClassOf _ _).mp t1
      have hpP : IP i (denotSubject i A p) :=
        ((hc.vocabProps onPropertyRow onPropertyRow_mem).2 _ _ t2).2
      have hcC : IC i (denotTerm i A c) :=
        ((hc.vocabProps allValuesFromRow allValuesFromRow_mem).2 _ _ t3).2
      refine (hc.range _ _).mpr ⟨hpP, hcC, fun x y hxy => ?_⟩
      exact hc.allValuesFromSub _ _ _ x y t3 t2
        (hsub x (hc.universal owlThing thing_universal x)) hxy
  | svfDomain h1 h2 h3 =>
      rename_i r p c
      have t1 := hA _ h1
      have t2 := hA _ h2
      have t3 := hA _ h3
      simp only [TripleHolds, denot_toTerm, denotTerm] at t1 t2 t3
      obtain ⟨_, hcC, hsub⟩ := (hc.subClassOf _ _).mp t3
      have hpP : IP i (denotSubject i A p) :=
        ((hc.vocabProps onPropertyRow onPropertyRow_mem).2 _ _ t2).2
      refine (hc.domain _ _).mpr ⟨hpP, hcC, fun x y hxy => ?_⟩
      exact hsub x (hc.someValuesFromSup _ _ _ x y t1 t2 hxy
        (hc.universal owlThing thing_universal y))
  | emptySubProp h1 h2 hd hq =>
      rename_i p q d1 d2
      obtain ⟨hpP, _, hr1⟩ := (hc.range _ _).mp (hA _ h1)
      obtain ⟨_, _, hr2⟩ := (hc.range _ _).mp (hA _ h2)
      have hqP : IP i (denotSubject i A q) := hA _ hq
      show i.iext (i.iIri rdfsSubPropertyOf) (denotSubject i A p) (denotTerm i A q.toTerm)
      rw [denot_toTerm]
      refine hc.subPropertyOfIf _ _ hpP hqP (fun x y hxy => ?_)
      exact absurd ⟨hr1 x y hxy, hr2 x y hxy⟩ (hc.disjointDatatypes d1 d2 hd y)
  | oneOfSub h1 h2 hl1 hl2 hsub =>
      rename_i c1 c2 l1 l2 es1 es2
      obtain ⟨hc1, he1⟩ := (hc.oneOf _ _ _ (holds_seqIs (fun u hu => hA u hu) hl1)).mp (hA _ h1)
      obtain ⟨hc2, he2⟩ := (hc.oneOf _ _ _ (holds_seqIs (fun u hu => hA u hu) hl2)).mp (hA _ h2)
      show i.iext (i.iIri rdfsSubClassOf) (denotSubject i A c1) (denotTerm i A c2.toTerm)
      rw [denot_toTerm]
      refine (hc.subClassOf _ _).mpr ⟨hc1, hc2, fun x hx => (he2 x).mpr ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((he1 x).mp hx)
      exact List.mem_map.mpr ⟨e, hsub e he, rfl⟩
  | unionSub h1 h2 hl1 hl2 hne1 hne2 hsub =>
      rename_i c1 c2 l1 l2 es1 es2
      obtain ⟨hc1, he1⟩ := hc.unionOfOnly _ _ _ (by simpa using hne1)
        (holds_seqIs (fun u hu => hA u hu) hl1) (hA _ h1)
      obtain ⟨hc2, he2⟩ := hc.unionOfOnly _ _ _ (by simpa using hne2)
        (holds_seqIs (fun u hu => hA u hu) hl2) (hA _ h2)
      show i.iext (i.iIri rdfsSubClassOf) (denotSubject i A c1) (denotTerm i A c2.toTerm)
      rw [denot_toTerm]
      refine (hc.subClassOf _ _).mpr ⟨hc1, hc2, fun x hx => (he2 x).mpr ?_⟩
      obtain ⟨c, hcm, hxc⟩ := (he1 x).mp hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hcm
      exact ⟨_, List.mem_map.mpr ⟨e, hsub e he, rfl⟩, hxc⟩
  | interSub h1 h2 hl1 hl2 hne1 hne2 hsub =>
      rename_i c1 c2 l1 l2 es1 es2
      obtain ⟨hc1, he1⟩ := hc.intersectionOfOnly _ _ _ (by simpa using hne1)
        (holds_seqIs (fun u hu => hA u hu) hl1) (hA _ h1)
      obtain ⟨hc2, he2⟩ := hc.intersectionOfOnly _ _ _ (by simpa using hne2)
        (holds_seqIs (fun u hu => hA u hu) hl2) (hA _ h2)
      show i.iext (i.iIri rdfsSubClassOf) (denotSubject i A c1) (denotTerm i A c2.toTerm)
      rw [denot_toTerm]
      refine (hc.subClassOf _ _).mpr ⟨hc1, hc2, fun x hx => (he2 x).mpr ?_⟩
      intro c hcm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hcm
      exact (he1 x).mp hx _ (List.mem_map.mpr ⟨e, hsub e he, rfl⟩)
  | literalValue hm hu hl hv =>
      rename_i s p l1 l2
      have t := hA _ hm
      have hI : i.iIri l1.val.datatype = i.iIri l2.val.datatype := by
        rcases hu with h | h
        · rw [h]
        · exact hc.sameAsOnly _ _ (hA _ h)
      show i.iext (i.iIri p) (denotSubject i A s) (i.iLit l2)
      rw [← hc.typedLiteralValue l1 l2 hl hv hI]
      exact t
  | hvEqProp hdp hdq hs1 hs2 ho1 hv1 ho2 hv2 hfp hfq =>
      rename_i p q d r1 r2 v
      have tdp := hA _ hdp
      have tdq := hA _ hdq
      have ts1 := hA _ hs1
      have ts2 := hA _ hs2
      have to1 := hA _ ho1
      have to2 := hA _ ho2
      simp only [TripleHolds, denot_toTerm] at tdp tdq ts1 ts2 to1 to2
      have tv1 : i.iext (i.iIri owlHasValue) (denotSubject i A r1) (denotTerm i A v) := hA _ hv1
      have tv2 : i.iext (i.iIri owlHasValue) (denotSubject i A r2) (denotTerm i A v) := hA _ hv2
      have tfp : icext i (denotSubject i A p) (i.iIri owlFunctionalProperty) := hA _ hfp
      have tfq : icext i (denotSubject i A q) (i.iIri owlFunctionalProperty) := hA _ hfq
      obtain ⟨hpP, _, hdomp⟩ := (hc.domain _ _).mp tdp
      obtain ⟨hqP, _, hdomq⟩ := (hc.domain _ _).mp tdq
      obtain ⟨_, _, hsub1⟩ := (hc.subClassOf _ _).mp ts1
      obtain ⟨_, _, hsub2⟩ := (hc.subClassOf _ _).mp ts2
      show i.iext (i.iIri owlEquivalentProperty) (denotSubject i A p) (denotTerm i A q.toTerm)
      rw [denot_toTerm]
      refine hc.equivalentPropertyIf _ _ hpP hqP (fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩)
      · have hxd := hdomp x y hxy
        have hpv := hc.hasValueSub _ _ _ x tv1 to1 (hsub1 x hxd)
        have hqv := hc.hasValueSub _ _ _ x tv2 to2 (hsub2 x hxd)
        rw [hc.functionalOnly _ x y _ tfp hxy hpv]
        exact hqv
      · have hxd := hdomq x y hxy
        have hpv := hc.hasValueSub _ _ _ x tv1 to1 (hsub1 x hxd)
        have hqv := hc.hasValueSub _ _ _ x tv2 to2 (hsub2 x hxd)
        rw [hc.functionalOnly _ x y _ tfq hxy hqv]
        exact hpv
  | minCardSucc hm ho hxy hk h0 h1 =>
      rename_i x z p y l k
      show i.iext (i.iIri rdfType) (denotSubject i A x) (denotTerm i A z.toTerm)
      rw [denot_toTerm]
      exact hc.minCardLe1Sup _ _ _ _ l k hk h0 h1 (hA _ hm) (hA _ ho) (hA _ hxy)

end Soundness

/-- Every triple `RbDerives` derives from `g` is OWL 2 RDF-Based
entailed by `g` (with `RbEntails` as the reading of entailment; see
the `Spec.lean` header). -/
theorem rbDerives_entailed {g : Graph} {t : Triple} (h : RbDerives g t) :
    RbEntails g [t] := by
  intro i hc ⟨A, hA⟩
  exact ⟨A, fun u hu => by
    rw [List.mem_singleton] at hu; subst hu; exact rbDerives_sound hc hA h⟩

end L4Factoidal.OWL.RdfBased
