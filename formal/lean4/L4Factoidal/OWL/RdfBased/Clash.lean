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
| `litSucc` | the `p`-successor `x`'s `owl:someValuesFrom` restriction asks for is a member of its filler and of each `AllSucc` class; one of them is an enumeration of literals, each excluded (`LitOut`) by one of them | Tables 5.4, 5.5, 5.6, 5.7, 5.8, § 4.2 |
| `intSucc` | the same successor; one class is an integer datatype restriction, another excludes every integer within its bounds (`IntOut`) | Tables 5.6, 5.7, 5.8, § 4.2 |

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

/-! ## Data successors: what the graph says about them

`AllSucc g x p d`: every `p`-successor of `x` is a member of `d`.
`IntRestr g d e fv`: `d` is a datatype restriction of the integer
datatype `e` whose facet nodes carry the pairs `fv`. `LitOut g l d`:
the literal `l` is not a member of `d`. `IntOut g b d`: no literal whose
integer value lies within the bounds `b` is a member of `d`. -/

inductive AllSucc (g : Graph) (x : Subject) (p : Term) : Term → Prop where
  | avf {r : Subject} {d : Term}
      (h1 : (⟨x, rdfType, r.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨r, owlAllValuesFrom, d⟩ : Triple) ∈ g)
      (h3 : (⟨r, owlOnProperty, p⟩ : Triple) ∈ g) : AllSucc g x p d
  | range {ps : Subject} {d : Term} (hp : p = ps.toTerm)
      (h : (⟨ps, rdfsRange, d⟩ : Triple) ∈ g) : AllSucc g x p d

def IntRestr (g : Graph) (d : Subject) (e : WfIri) (fv : List (WfIri × WfLiteral)) : Prop :=
  (intDtBounds e).isSome = true ∧ (⟨d, owlOnDatatype, .iri e⟩ : Triple) ∈ g ∧
  ∃ (lst : Term) (fs : List Term), fs ≠ [] ∧
    (⟨d, owlWithRestrictions, lst⟩ : Triple) ∈ g ∧ ListDenotes g lst fs ∧
    (∀ f ∈ fv, ∃ zs : Subject, zs.toTerm ∈ fs ∧ (⟨zs, f.1, .literal f.2⟩ : Triple) ∈ g) ∧
    (∀ ft ∈ fs, ∃ f ∈ fv, ∃ zs : Subject, ft = zs.toTerm ∧
      (⟨zs, f.1, .literal f.2⟩ : Triple) ∈ g)

inductive LitOut (g : Graph) (l : WfLiteral) : Term → Prop where
  /-- `l` is outside the value space of the datatype `e`. -/
  | dt {e : WfIri} (h : litOutsideDt l e = true) : LitOut g l (.iri e)
  /-- `d` is an enumeration of literals, each with a value other than `l`'s. -/
  | enum {d : Subject} {lst : Term} {es : List Term}
      (ho : (⟨d, owlOneOf, lst⟩ : Triple) ∈ g) (hl : ListDenotes g lst es)
      (hd : ∀ t ∈ es, ∃ m : WfLiteral, t = .literal m ∧ litDistinct l m = true) :
      LitOut g l d.toTerm
  /-- `d` is an integer restriction whose bounds exclude `l`'s value. -/
  | restr {d : Subject} {e : WfIri} {fv : List (WfIri × WfLiteral)} {k : Int}
      (hr : IntRestr g d e fv) (hk : intLitValue l = some k)
      (hout : inBounds k (intRestrBounds e fv) = false) : LitOut g l d.toTerm
  /-- `d` is the datatype complement of an enumeration that lists `l`'s value. -/
  | compl {d d' : Subject} {lst : Term} {es : List Term} {m : WfLiteral}
      (hc : (⟨d, owlDatatypeComplementOf, d'.toTerm⟩ : Triple) ∈ g)
      (ho : (⟨d', owlOneOf, lst⟩ : Triple) ∈ g) (hl : ListDenotes g lst es)
      (hm : Term.literal m ∈ es) (hs : litSame l m = true) : LitOut g l d.toTerm

inductive IntOut (g : Graph) (b : Option Int × Option Int) : Term → Prop where
  /-- An integer datatype whose bounds are disjoint from `b`. -/
  | dt {e : WfIri} {b' : Option Int × Option Int} (he : intDtBounds e = some b')
      (hdis : boundsDisjoint b b' = true) : IntOut g b (.iri e)
  /-- An integer restriction whose bounds are disjoint from `b`. -/
  | restr {d : Subject} {e : WfIri} {fv : List (WfIri × WfLiteral)} (hr : IntRestr g d e fv)
      (hdis : boundsDisjoint b (intRestrBounds e fv) = true) : IntOut g b d.toTerm

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
  /-- A successor `x` must have by `r` (`owl:someValuesFrom sv`) is a
  member of `sv` and of every `d` with `AllSucc g x p d`; one of those
  classes, `c`, is an enumeration of literals, and each listed literal is
  excluded by one of those classes. -/
  | litSucc {x r c : Subject} {p sv lst : Term} {es : List Term}
      (h1 : (⟨x, rdfType, r.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨r, owlSomeValuesFrom, sv⟩ : Triple) ∈ g)
      (h3 : (⟨r, owlOnProperty, p⟩ : Triple) ∈ g)
      (hcd : c.toTerm = sv ∨ AllSucc g x p c.toTerm)
      (ho : (⟨c, owlOneOf, lst⟩ : Triple) ∈ g) (hl : ListDenotes g lst es)
      (hout : ∀ t ∈ es, ∃ (l : WfLiteral) (d : Term), t = .literal l ∧
        (d = sv ∨ AllSucc g x p d) ∧ LitOut g l d) : RbClash g
  /-- The same successor is a member of an integer restriction `c` and of
  a class `d` that excludes every integer within `c`'s bounds. -/
  | intSucc {x r c : Subject} {p sv d : Term} {e : WfIri} {fv : List (WfIri × WfLiteral)}
      (h1 : (⟨x, rdfType, r.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨r, owlSomeValuesFrom, sv⟩ : Triple) ∈ g)
      (h3 : (⟨r, owlOnProperty, p⟩ : Triple) ∈ g)
      (hcd : c.toTerm = sv ∨ AllSucc g x p c.toTerm) (hr : IntRestr g c e fv)
      (hdd : d = sv ∨ AllSucc g x p d) (hout : IntOut g (intRestrBounds e fv) d) : RbClash g

theorem boundsDisjoint_spec {k : Int} {a b : Option Int × Option Int}
    (hd : boundsDisjoint a b = true) (ha : inBounds k a = true) : inBounds k b = false := by
  obtain ⟨alo, ahi⟩ := a
  obtain ⟨blo, bhi⟩ := b
  cases alo <;> cases ahi <;> cases blo <;> cases bhi <;>
    simp_all [boundsDisjoint, inBounds] <;> omega

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

theorem allSucc_holds {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {x : Subject} {p d : Term} (h : AllSucc g x p d) :
    ∀ y, i.iext (denotTerm i A p) (denotSubject i A x) y → icext i y (denotTerm i A d) := by
  intro y hy
  cases h with
  | avf h1 h2 h3 =>
      rename_i r
      have t1 := hA _ h1
      simp only [TripleHolds, denot_toTerm] at t1
      exact hc.allValuesFromSub _ _ _ _ y (hA _ h2) (hA _ h3) t1 hy
  | range hp h =>
      rename_i ps
      have t := hA _ h
      subst hp
      rw [denot_toTerm] at hy
      exact ((hc.range _ _).mp t).2.2 _ y hy

/-- A member of the class `sv` or of an `AllSucc` class. -/
theorem succ_member {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {x : Subject} {p sv d : Term} {y : i.idom}
    (hy : i.iext (denotTerm i A p) (denotSubject i A x) y) (hsv : icext i y (denotTerm i A sv))
    (hd : d = sv ∨ AllSucc g x p d) : icext i y (denotTerm i A d) := by
  rcases hd with rfl | hd
  · exact hsv
  · exact allSucc_holds hc hA hd y hy

omit hc in
theorem intRestr_holds {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {d : Subject} {e : WfIri} {fv : List (WfIri × WfLiteral)} (h : IntRestr g d e fv) :
    RestrictionFacets i (denotSubject i A d) e fv := by
  obtain ⟨he, hdt, lst, fs, hne, hw, hl, hf, hall⟩ := h
  refine ⟨he, hA _ hdt, denotTerm i A lst, fs.map (denotTerm i A), ?_, hA _ hw,
    holds_seqIs (fun u hu => hA u hu) hl, ?_, ?_⟩
  · intro hnil
    exact hne (List.map_eq_nil_iff.mp hnil)
  · intro f hfm
    obtain ⟨zs, hzs, ht⟩ := hf f hfm
    refine ⟨denotTerm i A zs.toTerm, List.mem_map_of_mem hzs, ?_⟩
    rw [denot_toTerm]
    exact hA _ ht
  · intro zk hzk
    obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hzk
    obtain ⟨f, hfm, zs, rfl, ht⟩ := hall ft hft
    refine ⟨f, hfm, ?_⟩
    rw [denot_toTerm]
    exact hA _ ht

theorem litOut_holds {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {l : WfLiteral} {d : Term} (h : LitOut g l d) : ¬ icext i (i.iLit l) (denotTerm i A d) := by
  cases h with
  | dt h => exact hc.litOutsideDt l _ h
  | enum ho hl hd =>
      rename_i ds lst es
      rw [denot_toTerm]
      refine hc.oneOfLitExcl _ _ _ l (holds_seqIs (fun u hu => hA u hu) hl) (hA _ ho) ?_
      intro a ha
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      obtain ⟨m, rfl, hm⟩ := hd t ht
      exact ⟨m, rfl, hm⟩
  | restr hr hk hout =>
      rw [denot_toTerm]
      exact hc.intRestrExcl _ _ _ l _ (intRestr_holds hA hr) hk hout
  | compl hcm ho hl hm hs =>
      rename_i ds d' lst es m
      rw [denot_toTerm]
      intro hin
      have tc := hA _ hcm
      simp only [TripleHolds, denot_toTerm] at tc
      have hnot := hc.datatypeComplementSub _ _ _ tc hin
      obtain ⟨_, hext⟩ := (hc.oneOf _ _ _ (holds_seqIs (fun u hu => hA u hu) hl)).mp (hA _ ho)
      have hmem : i.iLit m ∈ es.map (denotTerm i A) :=
        List.mem_map.mpr ⟨.literal m, hm, rfl⟩
      rw [hc.litSame l m hs] at hnot
      exact hnot ((hext _).mpr hmem)

theorem intOut_holds {g : Graph} {A : BnodeAssignment i.idom} (hA : HoldsAll i A g)
    {b : Option Int × Option Int} {d : Term} (h : IntOut g b d) {l : WfLiteral} {k : Int}
    (hk : intLitValue l = some k) (hb : inBounds k b = true) :
    ¬ icext i (i.iLit l) (denotTerm i A d) := by
  cases h with
  | dt he hdis =>
      rename_i e b'
      apply hc.litOutsideDt l e
      have hout := boundsDisjoint_spec hdis hb
      simp only [litOutsideDt, hk, he, hout, Bool.not_false, Bool.true_or]
  | restr hr hdis =>
      rw [denot_toTerm]
      exact hc.intRestrExcl _ _ _ l k (intRestr_holds hA hr) hk (boundsDisjoint_spec hdis hb)

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
  | litSucc h1 h2 h3 hcd ho hl hout =>
      rename_i x r c p sv lst es
      have t1 := hA _ h1
      simp only [TripleHolds, denot_toTerm] at t1
      obtain ⟨y, hy, hysv⟩ := hc.someValuesFromSub _ _ _ _ (hA _ h2) (hA _ h3) t1
      have hyc : icext i y (denotSubject i A c) := by
        have := succ_member hc hA hy hysv hcd
        rwa [denot_toTerm] at this
      obtain ⟨_, hext⟩ := (hc.oneOf _ _ _ (holds_seqIs (fun u hu => hA u hu) hl)).mp (hA _ ho)
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ((hext y).mp hyc)
      obtain ⟨l, d, rfl, hdd, hlo⟩ := hout t ht
      exact litOut_holds hc hA hlo (succ_member hc hA hy hysv hdd)
  | intSucc h1 h2 h3 hcd hr hdd hout =>
      rename_i x r c p sv d e fv
      have t1 := hA _ h1
      simp only [TripleHolds, denot_toTerm] at t1
      obtain ⟨y, hy, hysv⟩ := hc.someValuesFromSub _ _ _ _ (hA _ h2) (hA _ h3) t1
      have hyc : icext i y (denotSubject i A c) := by
        have := succ_member hc hA hy hysv hcd
        rwa [denot_toTerm] at this
      obtain ⟨l, k, hk, hb, rfl⟩ := hc.intRestrMembers _ _ _ (intRestr_holds hA hr) y hyc
      exact intOut_holds hc hA hout hk hb (succ_member hc hA hy hysv hdd)

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

/-! ### Data successors, executable -/

/-- The classes `AllSucc g x p` names: the `owl:allValuesFrom` fillers of
the restrictions on `p` that `x` is typed with, and the ranges of `p`. -/
def allSuccClasses (g : Graph) (x : Subject) (p : Term) : List Term :=
  (withSubjPred g x rdfType).flatMap (fun ty =>
    (asSubject ty.o).flatMap (fun r =>
      if memB g ⟨r, owlOnProperty, p⟩ then (withSubjPred g r owlAllValuesFrom).map (·.o)
      else [])) ++
  (asSubject p).flatMap (fun ps => (withSubjPred g ps rdfsRange).map (·.o))

/-- `(x, r, sv, p)`: `x rdf:type r`, `r owl:someValuesFrom sv`,
`r owl:onProperty p`. Read from the `owl:someValuesFrom` triples. -/
def succFrames (g : Graph) : List (Subject × Subject × Term × Term) :=
  (g.filter (fun t => t.p == owlSomeValuesFrom)).flatMap (fun s =>
    (withSubjPred g s.s owlOnProperty).flatMap (fun op =>
      (withPredObj g rdfType s.s.toTerm).map (fun tx => (tx.s, s.s, s.o, op.o))))

/-- The classes a successor of a frame is a member of. -/
def succClasses (g : Graph) (fr : Subject × Subject × Term × Term) : List Term :=
  fr.2.2.1 :: allSuccClasses g fr.1 fr.2.2.2

/-- The member lists of the enumerations of `d`. -/
def enumLists (g : Graph) (d : Subject) : List (List Term) :=
  (withSubjPred g d owlOneOf).flatMap (fun o => listSeqs g o.o (listFuel g))

/-- The facet pairs the facet nodes `fs` carry. -/
def facetPairs (g : Graph) (fs : List Term) : List (WfIri × WfLiteral) :=
  fs.flatMap (fun f => (asSubject f).flatMap (fun zs =>
    (g.filter (fun t => t.s == zs)).flatMap (fun t => (asLit t.o).map (fun v => (t.p, v)))))

/-- The readings of `d` as an integer restriction. -/
def intRestrs (g : Graph) (d : Subject) : List (WfIri × List (WfIri × WfLiteral)) :=
  (withSubjPred g d owlOnDatatype).flatMap (fun od =>
    (asIri od.o).flatMap (fun e =>
      if (intDtBounds e).isSome then
        (withSubjPred g d owlWithRestrictions).flatMap (fun wr =>
          (listSeqs g wr.o (listFuel g)).flatMap (fun fs =>
            if !fs.isEmpty && fs.all (fun ft => !(facetPairs g [ft]).isEmpty) then
              [(e, facetPairs g fs)]
            else []))
      else []))

def distinctFromAll (l : WfLiteral) (es : List Term) : Bool :=
  es.all (fun t => match t with | .literal m => litDistinct l m | _ => false)

def sameAsSome (l : WfLiteral) (es : List Term) : Bool :=
  es.any (fun t => match t with | .literal m => litSame l m | _ => false)

/-- Decides `LitOut g l d` for the four ways it is read. -/
def litOutB (g : Graph) (l : WfLiteral) (d : Term) : Bool :=
  (match d with | .iri e => litOutsideDt l e | _ => false) ||
  (asSubject d).any (fun ds =>
    (enumLists g ds).any (distinctFromAll l) ||
    (match intLitValue l with
     | some k => (intRestrs g ds).any (fun r => !inBounds k (intRestrBounds r.1 r.2))
     | none => false) ||
    (withSubjPred g ds owlDatatypeComplementOf).any (fun c =>
      (asSubject c.o).any (fun d' => (enumLists g d').any (sameAsSome l))))

/-- Decides `IntOut g b d`. -/
def intOutB (g : Graph) (b : Option Int × Option Int) (d : Term) : Bool :=
  (match d with
   | .iri e => (match intDtBounds e with | some b' => boundsDisjoint b b' | none => false)
   | _ => false) ||
  (asSubject d).any (fun ds =>
    (intRestrs g ds).any (fun r => boundsDisjoint b (intRestrBounds r.1 r.2)))

/-- `litSucc`: some class of the successor is an enumeration of literals,
each excluded by some class of the successor. -/
def litSuccAny (g : Graph) : Bool :=
  (succFrames g).any (fun fr =>
    (succClasses g fr).any (fun c => (asSubject c).any (fun cs =>
      (enumLists g cs).any (fun es =>
        es.all (fun t => match t with
          | .literal l => (succClasses g fr).any (fun d => litOutB g l d)
          | _ => false)))))

/-- `intSucc`: some class of the successor is an integer restriction whose
bounds another class of the successor excludes. -/
def intSuccAny (g : Graph) : Bool :=
  (succFrames g).any (fun fr =>
    (succClasses g fr).any (fun c => (asSubject c).any (fun cs =>
      (intRestrs g cs).any (fun r =>
        (succClasses g fr).any (fun d => intOutB g (intRestrBounds r.1 r.2) d)))))

def rbClashAny (g : Graph) : Bool :=
  thingEnumAny g || svfAvfDtAny g || litSuccAny g || intSuccAny g

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

theorem allSuccClasses_spec {g : Graph} {x : Subject} {p d : Term}
    (h : d ∈ allSuccClasses g x p) : AllSucc g x p d := by
  simp only [allSuccClasses, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨ty, hty, r, hr, h⟩ | ⟨ps, hps, h⟩
  · split at h
    · rename_i hm
      obtain ⟨av, hav, rfl⟩ := List.mem_map.mp h
      obtain ⟨htyg, htys, htyp⟩ := mem_withSubjPred hty
      obtain ⟨havg, havs, havp⟩ := mem_withSubjPred hav
      exact AllSucc.avf (mem_of_parts htyg htys htyp (mem_asSubject hr))
        (mem_of_parts havg havs havp rfl) (mem_of_memB hm)
    · simp at h
  · obtain ⟨rg, hrg, rfl⟩ := List.mem_map.mp h
    obtain ⟨hrgg, hrgs, hrgp⟩ := mem_withSubjPred hrg
    exact AllSucc.range (mem_asSubject hps) (mem_of_parts hrgg hrgs hrgp rfl)

theorem succFrames_spec {g : Graph} {fr : Subject × Subject × Term × Term}
    (h : fr ∈ succFrames g) :
    (⟨fr.1, rdfType, fr.2.1.toTerm⟩ : Triple) ∈ g ∧
    (⟨fr.2.1, owlSomeValuesFrom, fr.2.2.1⟩ : Triple) ∈ g ∧
    (⟨fr.2.1, owlOnProperty, fr.2.2.2⟩ : Triple) ∈ g := by
  simp only [succFrames, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at h
  obtain ⟨s, ⟨hs, hsp⟩, op, hop, tx, htx, rfl⟩ := h
  obtain ⟨hopg, hops, hopp⟩ := mem_withSubjPred hop
  obtain ⟨htxg, htxp, htxo⟩ := mem_withPredObj htx
  exact ⟨mem_of_parts htxg rfl htxp htxo, mem_of_parts hs rfl hsp rfl,
    mem_of_parts hopg hops hopp rfl⟩

theorem succClasses_spec {g : Graph} {fr : Subject × Subject × Term × Term} {d : Term}
    (h : d ∈ succClasses g fr) : d = fr.2.2.1 ∨ AllSucc g fr.1 fr.2.2.2 d := by
  simp only [succClasses, List.mem_cons] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (allSuccClasses_spec h)

theorem enumLists_spec {g : Graph} {d : Subject} {es : List Term} (h : es ∈ enumLists g d) :
    ∃ lst, (⟨d, owlOneOf, lst⟩ : Triple) ∈ g ∧ ListDenotes g lst es := by
  simp only [enumLists, List.mem_flatMap] at h
  obtain ⟨o, ho, hes⟩ := h
  obtain ⟨hog, hos, hop⟩ := mem_withSubjPred ho
  exact ⟨o.o, mem_of_parts hog hos hop rfl, listSeqs_sound g _ _ hes⟩

theorem facetPairs_spec {g : Graph} {fs : List Term} {f : WfIri × WfLiteral}
    (h : f ∈ facetPairs g fs) :
    ∃ zs : Subject, zs.toTerm ∈ fs ∧ (⟨zs, f.1, .literal f.2⟩ : Triple) ∈ g := by
  simp only [facetPairs, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at h
  obtain ⟨ft, hft, zs, hzs, t, ⟨ht, hts⟩, v, hv, rfl⟩ := h
  refine ⟨zs, ?_, mem_of_parts ht hts rfl (mem_asLit hv)⟩
  rw [← mem_asSubject hzs]
  exact hft

theorem facetPairs_single {g : Graph} {fs : List Term} {ft : Term} {f : WfIri × WfLiteral}
    (hft : ft ∈ fs) (h : f ∈ facetPairs g [ft]) : f ∈ facetPairs g fs := by
  simp only [facetPairs, List.mem_flatMap, List.mem_singleton] at h ⊢
  obtain ⟨_, rfl, h⟩ := h
  exact ⟨_, hft, h⟩

theorem intRestrs_spec {g : Graph} {d : Subject} {r : WfIri × List (WfIri × WfLiteral)}
    (h : r ∈ intRestrs g d) : IntRestr g d r.1 r.2 := by
  simp only [intRestrs, List.mem_flatMap] at h
  obtain ⟨od, hod, e, he, h⟩ := h
  split at h
  · rename_i hb
    simp only [List.mem_flatMap] at h
    obtain ⟨wr, hwr, fs, hfs, h⟩ := h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at hok
      obtain ⟨hne, hall⟩ := hok
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨hodg, hods, hodp⟩ := mem_withSubjPred hod
      obtain ⟨hwrg, hwrs, hwrp⟩ := mem_withSubjPred hwr
      refine ⟨hb, mem_of_parts hodg hods hodp (mem_asIri he), wr.o, fs, hne,
        mem_of_parts hwrg hwrs hwrp rfl, listSeqs_sound g _ _ hfs, ?_, ?_⟩
      · intro f hf
        exact facetPairs_spec hf
      · intro ft hft
        have hnz : facetPairs g [ft] ≠ [] := by simpa using hall ft hft
        obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hnz
        obtain ⟨zs, hzs, ht⟩ := facetPairs_spec hf
        simp only [List.mem_singleton] at hzs
        exact ⟨f, facetPairs_single hft hf, zs, hzs.symm, ht⟩
    · simp at h
  · simp at h

theorem litOutB_spec {g : Graph} {l : WfLiteral} {d : Term} (h : litOutB g l d = true) :
    LitOut g l d := by
  simp only [litOutB, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨ds, hds, h⟩
  · split at h
    · exact LitOut.dt h
    · simp at h
  · rw [mem_asSubject hds]
    rcases h with (⟨es, hes, h⟩ | h) | ⟨c, hc, d', hd', es, hes, h⟩
    · obtain ⟨lst, ho, hl⟩ := enumLists_spec hes
      refine LitOut.enum ho hl ?_
      intro t ht
      have := List.all_eq_true.mp h t ht
      split at this
      · rename_i m
        exact ⟨m, rfl, this⟩
      · simp at this
    · split at h
      · rename_i k hk
        obtain ⟨r, hr, hout⟩ := List.any_eq_true.mp h
        exact LitOut.restr (intRestrs_spec hr) hk (by simpa using hout)
      · simp at h
    · obtain ⟨lst, ho, hl⟩ := enumLists_spec hes
      obtain ⟨hcg, hcs, hcp⟩ := mem_withSubjPred hc
      obtain ⟨t, ht, hs⟩ := List.any_eq_true.mp h
      split at hs
      · rename_i m
        exact LitOut.compl (mem_of_parts hcg hcs hcp (mem_asSubject hd')) ho hl ht hs
      · simp at hs

theorem intOutB_spec {g : Graph} {b : Option Int × Option Int} {d : Term}
    (h : intOutB g b d = true) : IntOut g b d := by
  simp only [intOutB, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨ds, hds, r, hr, h⟩
  · split at h
    · rename_i e
      split at h
      · rename_i b' he
        exact IntOut.dt he h
      · simp at h
    · simp at h
  · rw [mem_asSubject hds]
    exact IntOut.restr (intRestrs_spec hr) h

theorem litSuccAny_spec {g : Graph} (h : litSuccAny g = true) : RbClash g := by
  simp only [litSuccAny, List.any_eq_true] at h
  obtain ⟨fr, hfr, c, hc, cs, hcs, es, hes, h⟩ := h
  obtain ⟨h1, h2, h3⟩ := succFrames_spec hfr
  obtain ⟨lst, ho, hl⟩ := enumLists_spec hes
  have hcd := succClasses_spec hc
  rw [mem_asSubject hcs] at hcd
  refine RbClash.litSucc h1 h2 h3 (Or.symm (Or.symm hcd)) ho hl ?_
  intro t ht
  have := List.all_eq_true.mp h t ht
  split at this
  · rename_i l
    obtain ⟨d, hd, hout⟩ := List.any_eq_true.mp this
    exact ⟨l, d, rfl, succClasses_spec hd, litOutB_spec hout⟩
  · simp at this

theorem intSuccAny_spec {g : Graph} (h : intSuccAny g = true) : RbClash g := by
  simp only [intSuccAny, List.any_eq_true] at h
  obtain ⟨fr, hfr, c, hc, cs, hcs, r, hr, d, hd, hout⟩ := h
  obtain ⟨h1, h2, h3⟩ := succFrames_spec hfr
  have hcd := succClasses_spec hc
  rw [mem_asSubject hcs] at hcd
  exact RbClash.intSucc h1 h2 h3 hcd (intRestrs_spec hr) (succClasses_spec hd)
    (intOutB_spec hout)

theorem rbClashAny_spec {g : Graph} (h : rbClashAny g = true) : RbClash g := by
  simp only [rbClashAny, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact thingEnumAny_spec h
  · exact svfAvfDtAny_spec h
  · exact litSuccAny_spec h
  · exact intSuccAny_spec h

/-- What the regime reads: a `true` answer is a proof of inconsistency. -/
theorem rbClashAny_unsat {g : Graph} (h : rbClashAny g = true) {i : Interp}
    (hc : RdfBasedConditions i) : ¬ Satisfies i g :=
  rbClash_unsat (rbClashAny_spec h) hc

end L4Factoidal.OWL.RdfBased
