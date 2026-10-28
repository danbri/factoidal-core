/-
L4Factoidal.SPARQLRL.BgpAgreement — one semantics for basic graph patterns:
SPARQL-RL triple-pattern matching (`matchTriple`, `evalSeq` in
`SPARQLRL/Eval.lean`) has the same solutions as the SPARQL reference
(`SPARQL.evalTP`, `SPARQL.evalBgpFrom` in `SPARQL/Algebra.lean`, SPARQL 1.1
§18.3) on the fragment where both have a meaning.
Pull request: https://github.com/danbri/factoidal-core/pull/163 (SPARQL 1.2 RL).
Issue: https://github.com/danbri/factoidal/issues/1099.

## The fragment

`trTerm`, `trSubj` and `trTP` translate a SPARQL-RL pattern term or triple
pattern to a SPARQL one. They are defined (`some`) on:
* variables, IRIs and literals in every position, except a literal subject;
* triple-term patterns `<<( s p o )>>` whose three positions are in the
  fragment (`PatternTerm.tripleTerm`; in subject position
  `PatternSubject.tripleTerm`, which matches no RDF subject, as the
  SPARQL-RL matcher does not either).
They are `none` (excluded) on:
* blank nodes. A blank node of a rule BODY is a variable in SPARQL-RL (draft
  "Treating blank nodes as variables"): the parser
  (`SPARQLRL/Parser.lean`, `userBnode`) turns it into the variable `.b<label>`
  before evaluation, so it is covered as a variable. An `STerm.bnode` left in
  a pattern matches nothing in `matchTerm`, while a SPARQL `PatternTerm.bnode`
  matches the same blank node; the two disagree, so it is excluded.
* a literal in subject position. SPARQL's `PatternSubject` has no literal
  form; the SPARQL-RL matcher can match one only against a generalized
  triple, which an RDF graph does not hold.

## The graph

The theorems take an `IGraph` that satisfies `IGraph.Inv` (the set and the
three position indexes hold exactly the triples of `.all`), and whose `.all`
holds exactly the images (`tripleToT3`) of the triples of an RDF graph `g`
(`IGraph.Represents`). `IGraph.ofGraph g` represents `g`
(`IGraph.ofGraph_represents`), and `IGraph.insert` and `IGraph.insertAll`
keep `IGraph.Inv` (`IGraph.Inv.insert`, `IGraph.Inv.insertAll`), so every
graph the semi-naive loop builds by insertion satisfies the invariant. A
graph that holds a generalized triple (a literal subject, from a data block
or a head) represents no RDF graph: there a variable subject can match a
literal, which SPARQL cannot express.

## Multiplicity and order

The theorems are about membership. `evalTP` lists one solution per matching
triple of the LIST `g`, in the order of `g`; `matchTriple` lists one solution
per matching triple of the chosen index entry, in insertion order, and the
`IGraph` holds each triple once. So for a graph with a repeated triple the
reference has the solution more often, and the orders can differ.

## The index lookup

`Src.candidates` is where the two can differ. `Src.mem_candidates` proves
that every candidate is a triple of the graph that the exclusion graph does
not hold, and that every such triple that agrees with all bound positions is
a candidate (a superset that `matchTriple` filters with `matchTerm`).
`matchTriple_iff_all` then removes the index from the statement.
-/
import L4Factoidal.SPARQLRL.Eval

namespace L4Factoidal.SPARQLRL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Translation to SPARQL triple patterns -/

/-- A SPARQL-RL pattern term as a SPARQL pattern term; `none` outside the
fragment (a blank node anywhere in the term). -/
def trTerm : STerm → Option PatternTerm
  | .var v => some (.var v)
  | .iri i => some (.iri i)
  | .lit l => some (.literal l)
  | .bnode _ => none
  | .triple s p o =>
      match trTerm s, trTerm p, trTerm o with
      | some a, some b, some c => some (.tripleTerm a b c)
      | _, _, _ => none

/-- A SPARQL-RL subject pattern as a SPARQL subject pattern; `none` for a
blank node and for a literal. -/
def trSubj : STerm → Option PatternSubject
  | .var v => some (.var v)
  | .iri i => some (.iri i)
  | .triple s p o =>
      match trTerm s, trTerm p, trTerm o with
      | some a, some b, some c => some (.tripleTerm a b c)
      | _, _, _ => none
  | _ => none

/-- A SPARQL-RL triple pattern as a SPARQL triple pattern. -/
def trTP (tp : STriple) : Option TriplePattern :=
  match trSubj tp.s, trTerm tp.p, trTerm tp.o with
  | some a, some b, some c => some { s := a, p := b, o := c }
  | _, _, _ => none

/-! ## Term-level agreement -/

theorem term_beq_iff (u t : Term) : (u == t) = Term.eqb u t := by
  cases h : Term.eqb u t
  · have : u ≠ t := fun e => by rw [(Term.eqb_iff_eq u t).mpr e] at h; cases h
    simpa using this
  · simpa using (Term.eqb_iff_eq u t).mp h

/-- `matchTerm` is `tryBindTerm` on the fragment. -/
theorem matchTerm_eq_tryBindTerm : ∀ (t : STerm) (pt : PatternTerm), trTerm t = some pt →
    ∀ (b : Binding) (x : Term), matchTerm b t x = tryBindTerm pt x b
  | .var v, pt, h, b, x => by
      simp only [trTerm, Option.some.injEq] at h; subst h
      simp only [matchTerm, tryBindTerm]
      cases b.lookup v with
      | none => rfl
      | some u => simp only [term_beq_iff]
  | .iri i, pt, h, b, x => by
      simp only [trTerm, Option.some.injEq] at h; subst h
      cases x with
      | iri i' =>
          simp only [matchTerm, tryBindTerm]
          by_cases e : i = i'
          · subst e; simp
          · have e' : i' ≠ i := Ne.symm e
            have e2 : ¬ i.val = i'.val := fun hh => e (Subtype.ext hh)
            simp [e', e2]
      | _ => simp [matchTerm, tryBindTerm]
  | .lit l, pt, h, b, x => by
      simp only [trTerm, Option.some.injEq] at h; subst h
      cases x with
      | literal l' =>
          have e := Term.eqb_iff_eq (.literal l) (.literal l')
          simp only [Term.eqb] at e
          cases hq : l.val.eqb l'.val
          · have hne : l ≠ l' := fun hh => by
              subst hh; have := e.mpr rfl; rw [hq] at this; cases this
            have hne' : l' ≠ l := Ne.symm hne
            simp [matchTerm, tryBindTerm, hq, hne']
          · have hl : l = l' := by have := e.mp hq; injection this
            subst hl; simp [matchTerm, tryBindTerm]
      | _ => simp [matchTerm, tryBindTerm]
  | .bnode _, pt, h, _, _ => by simp [trTerm] at h
  | .triple s p o, pt, h, b, x => by
      simp only [trTerm] at h
      cases hs : trTerm s <;> cases hp : trTerm p <;> cases ho : trTerm o <;>
        simp only [hs, hp, ho, Option.some.injEq, reduceCtorEq] at h
      subst h
      rename_i a c d
      cases x with
      | tripleTerm ts tp to =>
          simp only [matchTerm, tryBindTerm]
          rw [matchTerm_eq_tryBindTerm s a hs]
          cases tryBindTerm a ts.toTerm b with
          | none => rfl
          | some b1 =>
              simp only
              rw [matchTerm_eq_tryBindTerm p c hp]
              cases tryBindTerm c (.iri tp) b1 with
              | none => rfl
              | some b2 => simp only; rw [matchTerm_eq_tryBindTerm o d ho]
      | _ => simp [matchTerm, tryBindTerm]

/-- `matchTerm` on a subject is `tryBindSubject` on the fragment. -/
theorem matchTerm_eq_tryBindSubject (t : STerm) (ps : PatternSubject) (h : trSubj t = some ps)
    (b : Binding) (s : Subject) : matchTerm b t s.toTerm = tryBindSubject ps s b := by
  cases t with
  | var v =>
      simp only [trSubj, Option.some.injEq] at h; subst h
      simp only [matchTerm, tryBindSubject]
      cases b.lookup v with
      | none => rfl
      | some u => simp only [term_beq_iff]
  | iri i =>
      simp only [trSubj, Option.some.injEq] at h; subst h
      cases s with
      | iri i' =>
          simp only [matchTerm, tryBindSubject, Subject.toTerm]
          by_cases e : i = i'
          · subst e; simp
          · have e' : i' ≠ i := Ne.symm e
            have e2 : ¬ i.val = i'.val := fun hh => e (Subtype.ext hh)
            simp [e', e2]
      | bnode _ => simp [matchTerm, tryBindSubject, Subject.toTerm]
  | triple s' p' o' =>
      simp only [trSubj] at h
      cases hs : trTerm s' <;> cases hp : trTerm p' <;> cases ho : trTerm o' <;>
        simp only [hs, hp, ho, Option.some.injEq, reduceCtorEq] at h
      subst h
      cases s <;> simp [matchTerm, tryBindSubject, Subject.toTerm]
  | lit _ => simp [trSubj] at h
  | bnode _ => simp [trSubj] at h

/-- One generalized triple matched against a SPARQL-RL triple pattern: the
three `matchTerm` steps of `matchTriple`. -/
def chainT3 (b : Binding) (tp : STriple) : T3 → Option Binding
  | (s, p, o) =>
      match matchTerm b tp.s s with
      | none => none
      | some b1 =>
          match matchTerm b1 tp.p p with
          | none => none
          | some b2 => matchTerm b2 tp.o o

/-- On an RDF triple, the SPARQL-RL triple step is `tpMatch` of the
translation. -/
theorem chainT3_eq_tpMatch (tp : STriple) (tp' : TriplePattern) (h : trTP tp = some tp')
    (b : Binding) (t : Triple) : chainT3 b tp (tripleToT3 t) = tpMatch tp' t b := by
  simp only [trTP] at h
  cases hs : trSubj tp.s <;> cases hp : trTerm tp.p <;> cases ho : trTerm tp.o <;>
    simp only [hs, hp, ho, Option.some.injEq, reduceCtorEq] at h
  subst h
  rename_i a c d
  simp only [chainT3, tripleToT3, tpMatch]
  rw [matchTerm_eq_tryBindSubject tp.s a hs]
  cases tryBindSubject a t.s b with
  | none => rfl
  | some b1 =>
      simp only
      rw [matchTerm_eq_tryBindTerm tp.p c hp]
      cases tryBindTerm c (.iri t.p) b1 with
      | none => rfl
      | some b2 => simp only; rw [matchTerm_eq_tryBindTerm tp.o d ho]

/-! ## `matchTriple` as a filter over the candidates -/

/-- A left fold that pushes the `some` results of `f` is `filterMap f`. -/
theorem foldl_opt {α β : Type} (f : α → Option β) (F : Array β → α → Array β)
    (hF : ∀ acc x, F acc x = match f x with | none => acc | some y => acc.push y) :
    ∀ (l : List α) (acc : Array β), (l.foldl F acc).toList = acc.toList ++ l.filterMap f
  | [], acc => by simp
  | x :: rest, acc => by
      rw [List.foldl_cons, foldl_opt f F hF rest, hF]
      cases h : f x <;> simp [h]

theorem matchTriple_eq (src : Src) (b : Binding) (tp : STriple) :
    matchTriple src b tp =
      (src.candidates (ground? b tp.s) (ground? b tp.p) (ground? b tp.o)).toList.filterMap
        (chainT3 b tp) := by
  unfold matchTriple
  rw [← Array.foldl_toList]
  refine (foldl_opt (chainT3 b tp) _ ?_ _ #[]).trans (by simp)
  intro acc x
  obtain ⟨s, p, o⟩ := x
  simp only [chainT3]
  rcases matchTerm b tp.s s with _ | b1
  · rfl
  · simp only
    rcases matchTerm b1 tp.p p with _ | b2
    · rfl
    · simp only
      rcases matchTerm b2 tp.o o with _ | b3 <;> rfl

/-! ## Bindings only grow -/

/-- `b'` extends `b`: every variable bound in `b` has the same value in `b'`. -/
def Ext (b b' : Binding) : Prop := ∀ v u, b.lookup v = some u → b'.lookup v = some u

theorem Ext.refl (b : Binding) : Ext b b := fun _ _ h => h

theorem Ext.trans {a b c : Binding} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  fun v u h => h2 v u (h1 v u h)

theorem matchTerm_ext : ∀ (t : STerm) (b b' : Binding) (x : Term),
    matchTerm b t x = some b' → Ext b b'
  | .var v, b, b', x, h => by
      simp only [matchTerm] at h
      cases hl : b.lookup v with
      | some u =>
          simp only [hl] at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact Ext.refl _
          · cases h
      | none =>
          simp only [hl, Option.some.injEq] at h; subst h
          intro w u hw
          simp only [Binding.bind, Binding.lookup]
          split
          · rename_i e; subst e; rw [hl] at hw; cases hw
          · exact hw
  | .iri i, b, b', x, h => by
      simp only [matchTerm] at h; split at h
      · simp only [Option.some.injEq] at h; subst h; exact Ext.refl _
      · cases h
  | .lit l, b, b', x, h => by
      simp only [matchTerm] at h; split at h
      · simp only [Option.some.injEq] at h; subst h; exact Ext.refl _
      · cases h
  | .bnode _, b, b', x, h => by simp [matchTerm] at h
  | .triple s p o, b, b', x, h => by
      cases x with
      | tripleTerm ts tp to =>
          simp only [matchTerm] at h
          cases h1 : matchTerm b s ts.toTerm with
          | none => simp [h1] at h
          | some b1 =>
              simp only [h1] at h
              cases h2 : matchTerm b1 p (.iri tp) with
              | none => simp [h2] at h
              | some b2 =>
                  simp only [h2] at h
                  exact (matchTerm_ext s b b1 _ h1).trans
                    ((matchTerm_ext p b1 b2 _ h2).trans (matchTerm_ext o b2 b' _ h))
      | _ => simp [matchTerm] at h

/-- A position that is ground under `b` matches only its ground value, under
any extension of `b`. -/
theorem match_ground : ∀ (t : STerm) (b b' b'' : Binding) (x k : Term),
    t.bnodes = [] → inst b (fun y => .bnode y) t = some k → Ext b b' →
    matchTerm b' t x = some b'' → x = k
  | .var v, b, b', b'', x, k, _, hi, he, hm => by
      simp only [inst] at hi
      have hl := he v k hi
      simp only [matchTerm, hl] at hm
      split at hm
      · rename_i e; exact (beq_iff_eq.mp e).symm
      · cases hm
  | .iri i, b, b', b'', x, k, _, hi, _, hm => by
      simp only [inst, Option.some.injEq] at hi; subst hi
      simp only [matchTerm] at hm; split at hm
      · rename_i e; exact beq_iff_eq.mp e
      · cases hm
  | .lit l, b, b', b'', x, k, _, hi, _, hm => by
      simp only [inst, Option.some.injEq] at hi; subst hi
      simp only [matchTerm] at hm; split at hm
      · rename_i e; exact beq_iff_eq.mp e
      · cases hm
  | .bnode y, _, _, _, _, _, hb, _, _, _ => by simp [STerm.bnodes] at hb
  | .triple s p o, b, b', b'', x, k, hb, hi, he, hm => by
      simp only [STerm.bnodes, List.append_eq_nil_iff] at hb
      obtain ⟨⟨hbs, hbp⟩, hbo⟩ := hb
      simp only [inst] at hi
      cases hs : inst b (fun y => .bnode y) s <;> cases hp : inst b (fun y => .bnode y) p <;>
        cases ho : inst b (fun y => .bnode y) o <;> simp only [hs, hp, ho, reduceCtorEq] at hi
      rename_i s' p' o'
      cases p' with
      | iri p'' =>
          simp only at hi
          cases hss : s'.toSubject? with
          | none => simp [hss] at hi
          | some ss =>
              simp only [hss, Option.map_some, Option.some.injEq] at hi
              subst hi
              cases x with
              | tripleTerm ts tp to =>
                  simp only [matchTerm] at hm
                  cases h1 : matchTerm b' s ts.toTerm with
                  | none => simp [h1] at hm
                  | some b1 =>
                      simp only [h1] at hm
                      cases h2 : matchTerm b1 p (.iri tp) with
                      | none => simp [h2] at hm
                      | some b2 =>
                          simp only [h2] at hm
                          have e1 := match_ground s b b' b1 _ _ hbs hs he h1
                          have he1 := he.trans (matchTerm_ext s b' b1 _ h1)
                          have e2 := match_ground p b b1 b2 _ _ hbp hp he1 h2
                          have he2 := he1.trans (matchTerm_ext p b1 b2 _ h2)
                          have e3 := match_ground o b b2 b'' _ _ hbo ho he2 hm
                          simp only [Term.iri.injEq] at e2
                          subst e2; subst e3
                          have : ts = ss := by
                            cases ts <;> cases s' <;> simp_all [Subject.toTerm, Term.toSubject?]
                          subst this; rfl
              | _ => simp [matchTerm] at hm
      | _ => simp at hi

theorem ground?_spec {b : Binding} {t : STerm} {k : Term} (h : ground? b t = some k) :
    t.bnodes = [] ∧ inst b (fun y => .bnode y) t = some k := by
  unfold ground? at h
  split at h
  · cases h
  · rename_i hb
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Classical.not_not] at hb
    exact ⟨by simpa using hb, h⟩

/-- A triple that a pattern matches agrees with every position the pattern
has ground under the starting solution. -/
theorem chainT3_agrees {b b' : Binding} {tp : STriple} {t : T3} (h : chainT3 b tp t = some b') :
    (∀ k, ground? b tp.s = some k → t.1 = k) ∧ (∀ k, ground? b tp.p = some k → t.2.1 = k) ∧
    (∀ k, ground? b tp.o = some k → t.2.2 = k) := by
  obtain ⟨s, p, o⟩ := t
  simp only [chainT3] at h
  cases h1 : matchTerm b tp.s s with
  | none => simp [h1] at h
  | some b1 =>
      simp only [h1] at h
      cases h2 : matchTerm b1 tp.p p with
      | none => simp [h2] at h
      | some b2 =>
          simp only [h2] at h
          have he1 := matchTerm_ext _ _ _ _ h1
          have he2 := he1.trans (matchTerm_ext _ _ _ _ h2)
          refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
          · obtain ⟨hb, hi⟩ := ground?_spec hk
            exact match_ground _ b b _ _ _ hb hi (Ext.refl b) h1
          · obtain ⟨hb, hi⟩ := ground?_spec hk
            exact match_ground _ b b1 _ _ _ hb hi he1 h2
          · obtain ⟨hb, hi⟩ := ground?_spec hk
            exact match_ground _ b b2 _ _ _ hb hi he2 h

/-! ## The graph invariant -/

/-- The set and the three position indexes of an `IGraph` hold exactly the
triples of `.all`. -/
structure IGraph.Inv (g : IGraph) : Prop where
  set_iff : ∀ t, g.set.contains t = true ↔ t ∈ g.all
  byS_iff : ∀ k t, t ∈ g.byS.getD k #[] ↔ t ∈ g.all ∧ t.1 = k
  byP_iff : ∀ k t, t ∈ g.byP.getD k #[] ↔ t ∈ g.all ∧ t.2.1 = k
  byO_iff : ∀ k t, t ∈ g.byO.getD k #[] ↔ t ∈ g.all ∧ t.2.2 = k

theorem IGraph.Inv.empty : IGraph.Inv {} where
  set_iff t := by simp
  byS_iff k t := by simp
  byP_iff k t := by simp
  byO_iff k t := by simp

theorem index_insert_iff {m : Std.HashMap Term (Array T3)} {all : Array T3} {f : T3 → Term}
    (hm : ∀ k t, t ∈ m.getD k #[] ↔ t ∈ all ∧ f t = k) (x : T3) (k : Term) (t : T3) :
    t ∈ (m.insert (f x) ((m.getD (f x) #[]).push x)).getD k #[] ↔
      t ∈ all.push x ∧ f t = k := by
  rw [Std.HashMap.getD_insert]
  by_cases e : f x = k
  · subst e
    simp only [beq_self_eq_true, ite_true, Array.mem_push, hm]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨Or.inl h1, h2⟩
      · subst h; exact ⟨Or.inr rfl, rfl⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
  · have : (f x == k) = false := by simpa using e
    simp only [this, Bool.false_eq_true, ite_false, hm, Array.mem_push]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, h2⟩
      · subst h1; exact absurd h2 e

/-- `IGraph.insert` keeps the invariant and adds exactly its triple. -/
theorem IGraph.Inv.insert {g : IGraph} (hg : g.Inv) (x : T3) :
    (g.insert x).Inv ∧ ∀ t, t ∈ (g.insert x).all ↔ t ∈ g.all ∨ t = x := by
  unfold IGraph.insert
  split
  · rename_i hc
    refine ⟨hg, fun t => ⟨Or.inl, ?_⟩⟩
    rintro (h | h)
    · exact h
    · subst h; exact (hg.set_iff t).mp hc
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro t
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hg.set_iff,
        Array.mem_push]
      exact ⟨fun h => h.elim (fun e => Or.inr e.symm) Or.inl,
             fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e.symm)⟩
    · exact index_insert_iff (f := fun t => t.1) hg.byS_iff x
    · exact index_insert_iff (f := fun t => t.2.1) hg.byP_iff x
    · exact index_insert_iff (f := fun t => t.2.2) hg.byO_iff x
    · intro t; simp [Array.mem_push]

theorem IGraph.Inv.insertList {g : IGraph} (hg : g.Inv) (ts : List T3) :
    (ts.foldl IGraph.insert g).Inv ∧
      ∀ t, t ∈ (ts.foldl IGraph.insert g).all ↔ t ∈ g.all ∨ t ∈ ts := by
  induction ts generalizing g with
  | nil => exact ⟨hg, fun t => by simp⟩
  | cons x rest ih =>
      obtain ⟨h1, h2⟩ := hg.insert x
      obtain ⟨h3, h4⟩ := ih h1
      refine ⟨h3, fun t => ?_⟩
      simp only [List.foldl_cons, h4, h2, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- `IGraph.insertAll` keeps the invariant and adds exactly its triples. -/
theorem IGraph.Inv.insertAll {g : IGraph} (hg : g.Inv) (ts : Array T3) :
    (g.insertAll ts).Inv ∧ ∀ t, t ∈ (g.insertAll ts).all ↔ t ∈ g.all ∨ t ∈ ts := by
  unfold IGraph.insertAll
  rw [← Array.foldl_toList]
  obtain ⟨h1, h2⟩ := hg.insertList ts.toList
  exact ⟨h1, fun t => by rw [h2, Array.mem_toList_iff]⟩

/-- An `IGraph` represents the RDF graph `g`: the invariant holds and `.all`
holds exactly the triples of `g`. -/
def IGraph.Represents (ig : IGraph) (g : Graph) : Prop :=
  ig.Inv ∧ ∀ t, t ∈ ig.all ↔ ∃ tr ∈ g, tripleToT3 tr = t

theorem IGraph.ofGraph_represents (g : Graph) : (IGraph.ofGraph g).Represents g := by
  unfold IGraph.ofGraph
  have e : g.foldl (fun acc t => acc.insert (tripleToT3 t)) ({} : IGraph) =
      (g.map tripleToT3).foldl IGraph.insert {} := by
    rw [List.foldl_map]
  rw [e]
  obtain ⟨h1, h2⟩ := IGraph.Inv.empty.insertList (g.map tripleToT3)
  refine ⟨h1, fun t => ?_⟩
  rw [h2]
  simp

/-! ## The index lookup -/

theorem foldl_min_mem (a : Array T3) (rest : List (Array T3)) :
    rest.foldl (fun m x => if x.size < m.size then x else m) a ∈ a :: rest := by
  induction rest generalizing a with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons]
      split
      · exact List.mem_cons_of_mem _ (ih x)
      · have := ih a
        simp only [List.mem_cons] at this ⊢
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- The index lookup: every candidate is a triple of the graph that the
exclusion graph does not hold; every such triple that agrees with all bound
positions is a candidate. -/
theorem Src.mem_candidates (src : Src) (hg : src.g.Inv) (s p o : Option Term) (t : T3) :
    (t ∈ src.candidates s p o →
      t ∈ src.g.all ∧ ∀ ex, src.excl = some ex → ex.contains t = false) ∧
    (t ∈ src.g.all → (∀ ex, src.excl = some ex → ex.contains t = false) →
      (∀ k, s = some k → t.1 = k) → (∀ k, p = some k → t.2.1 = k) →
      (∀ k, o = some k → t.2.2 = k) → t ∈ src.candidates s p o) := by
  -- The base array, before the exclusion graph is removed.
  have hbase : (t ∈ (match s, p, o with
      | some s, some p, some o => if src.g.contains (s, p, o) then #[(s, p, o)] else #[]
      | _, _, _ =>
        match [s.map (fun k => src.g.byS.getD k #[]), p.map (fun k => src.g.byP.getD k #[]),
                   o.map (fun k => src.g.byO.getD k #[])].filterMap id with
        | [] => src.g.all
        | a :: rest => rest.foldl (fun (m x : Array T3) => if x.size < m.size then x else m) a) →
        t ∈ src.g.all) ∧
      (t ∈ src.g.all → (∀ k, s = some k → t.1 = k) → (∀ k, p = some k → t.2.1 = k) →
        (∀ k, o = some k → t.2.2 = k) → t ∈ (match s, p, o with
      | some s, some p, some o => if src.g.contains (s, p, o) then #[(s, p, o)] else #[]
      | _, _, _ =>
        match [s.map (fun k => src.g.byS.getD k #[]), p.map (fun k => src.g.byP.getD k #[]),
                   o.map (fun k => src.g.byO.getD k #[])].filterMap id with
        | [] => src.g.all
        | a :: rest => rest.foldl (fun (m x : Array T3) => if x.size < m.size then x else m) a)) := by
    -- every index array in the list is a subset of `.all` and holds every agreeing triple
    have hopts : ∀ a ∈ [s.map (fun k => src.g.byS.getD k #[]), p.map (fun k => src.g.byP.getD k #[]),
                   o.map (fun k => src.g.byO.getD k #[])].filterMap id,
        (t ∈ a → t ∈ src.g.all) ∧
        (t ∈ src.g.all → (∀ k, s = some k → t.1 = k) → (∀ k, p = some k → t.2.1 = k) →
          (∀ k, o = some k → t.2.2 = k) → t ∈ a) := by
      intro a ha
      simp only [List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false, id] at ha
      obtain ⟨x, hx, hxa⟩ := ha
      rcases hx with hx | hx | hx <;> subst hx
      · cases s with
        | none => cases hxa
        | some k =>
            simp only [Option.map_some, Option.some.injEq] at hxa; subst hxa
            exact ⟨fun h => ((hg.byS_iff k t).mp h).1,
                   fun h hs _ _ => (hg.byS_iff k t).mpr ⟨h, hs k rfl⟩⟩
      · cases p with
        | none => cases hxa
        | some k =>
            simp only [Option.map_some, Option.some.injEq] at hxa; subst hxa
            exact ⟨fun h => ((hg.byP_iff k t).mp h).1,
                   fun h _ hp _ => (hg.byP_iff k t).mpr ⟨h, hp k rfl⟩⟩
      · cases o with
        | none => cases hxa
        | some k =>
            simp only [Option.map_some, Option.some.injEq] at hxa; subst hxa
            exact ⟨fun h => ((hg.byO_iff k t).mp h).1,
                   fun h _ _ ho => (hg.byO_iff k t).mpr ⟨h, ho k rfl⟩⟩
    split
    · rename_i s' p' o'
      constructor
      · intro h
        split at h
        · rename_i hc
          simp only [Array.mem_singleton] at h; subst h
          exact (hg.set_iff _).mp hc
        · simp at h
      · intro h hs hp ho
        have e : t = (s', p', o') := by
          obtain ⟨a, b, c⟩ := t
          simp only at hs hp ho
          rw [hs s' rfl, hp p' rfl, ho o' rfl]
        subst e
        have hc : src.g.contains (s', p', o') = true := (hg.set_iff _).mpr h
        simp [hc]
    · generalize hL : [s.map (fun k => src.g.byS.getD k #[]), p.map (fun k => src.g.byP.getD k #[]),
                   o.map (fun k => src.g.byO.getD k #[])].filterMap id = L at hopts
      cases L with
      | nil => exact ⟨id, fun h _ _ _ => h⟩
      | cons a rest =>
          have hm := foldl_min_mem a rest
          have := hopts _ hm
          exact ⟨this.1, this.2⟩
  unfold Src.candidates
  cases hex : src.excl with
  | none =>
      simp only
      refine ⟨fun h => ⟨hbase.1 h, fun ex e => by cases e⟩, fun h _ hs hp ho => hbase.2 h hs hp ho⟩
  | some ex =>
      simp only [Array.mem_filter, Bool.not_eq_true']
      refine ⟨fun h => ⟨hbase.1 h.1, fun ex' e => ?_⟩, fun h hx hs hp ho => ⟨hbase.2 h hs hp ho, hx ex rfl⟩⟩
      cases e; exact h.2

/-- `matchTriple` with the index removed: its solutions are the solutions of
the triple step on the triples of the graph that the exclusion graph does not
hold. -/
theorem matchTriple_iff_all (src : Src) (hg : src.g.Inv) (b b' : Binding) (tp : STriple) :
    b' ∈ matchTriple src b tp ↔
      ∃ t ∈ src.g.all, (∀ ex, src.excl = some ex → ex.contains t = false) ∧
        chainT3 b tp t = some b' := by
  rw [matchTriple_eq, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hc⟩
    obtain ⟨h1, h2⟩ := (src.mem_candidates hg _ _ _ t).1 (Array.mem_toList_iff.mp ht)
    exact ⟨t, h1, h2, hc⟩
  · rintro ⟨t, ht, hx, hc⟩
    obtain ⟨hs, hp, ho⟩ := chainT3_agrees hc
    exact ⟨t, Array.mem_toList_iff.mpr ((src.mem_candidates hg _ _ _ t).2 ht hx hs hp ho), hc⟩

/-! ## Theorem A: one triple pattern -/

/-- One triple pattern: over an `IGraph` that represents the RDF graph `g`,
with the full source (no exclusion graph), the SPARQL-RL solutions are the
SPARQL `evalTP` solutions of the translated pattern (as members). -/
theorem matchTriple_mem_iff_evalTP {ig : IGraph} {g : Graph} (hr : ig.Represents g)
    (tp : STriple) (tp' : TriplePattern) (htr : trTP tp = some tp') (mu mu' : Binding) :
    mu' ∈ matchTriple ⟨ig, none⟩ mu tp ↔ mu' ∈ evalTP tp' g mu := by
  rw [matchTriple_iff_all ⟨ig, none⟩ hr.1, evalTP, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, _, hc⟩
    obtain ⟨tr, htr', e⟩ := (hr.2 t).mp ht
    subst e
    exact ⟨tr, htr', by rw [← chainT3_eq_tpMatch tp tp' htr]; exact hc⟩
  · rintro ⟨tr, htr', hc⟩
    refine ⟨tripleToT3 tr, (hr.2 _).mpr ⟨tr, htr', rfl⟩, fun ex e => by simp at e, ?_⟩
    rw [chainT3_eq_tpMatch tp tp' htr]; exact hc

/-- Theorem A for `IGraph.ofGraph`. -/
theorem matchTriple_ofGraph_mem_iff_evalTP (g : Graph) (tp : STriple) (tp' : TriplePattern)
    (htr : trTP tp = some tp') (mu mu' : Binding) :
    mu' ∈ matchTriple ⟨IGraph.ofGraph g, none⟩ mu tp ↔ mu' ∈ evalTP tp' g mu :=
  matchTriple_mem_iff_evalTP (IGraph.ofGraph_represents g) tp tp' htr mu mu'

/-! ## Theorem B: a sequence of triple-pattern elements -/

/-- A list of SPARQL-RL triple patterns and a SPARQL BGP related elementwise
by `trTP`. -/
inductive TrBgp : List STriple → Bgp → Prop where
  | nil : TrBgp [] []
  | cons {a : STriple} {c : TriplePattern} {as : List STriple} {cs : Bgp} :
      trTP a = some c → TrBgp as cs → TrBgp (a :: as) (c :: cs)

/-- `mapM trTP` gives the related BGP. -/
theorem TrBgp.of_mapM : ∀ (tps : List STriple) (bgp : Bgp), tps.mapM trTP = some bgp → TrBgp tps bgp
  | [], bgp, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; exact .nil
  | tp :: tps, bgp, h => by
      simp only [List.mapM_cons, bind, pure] at h
      cases h1 : trTP tp with
      | none => simp [h1] at h
      | some c =>
          cases h2 : tps.mapM trTP with
          | none => simp [h1, h2] at h
          | some cs =>
              simp only [h1, h2, Option.bind_some, Option.some.injEq] at h
              subst h
              exact .cons h1 (TrBgp.of_mapM tps cs h2)

/-- A sequence of triple-pattern elements: `evalSeq` from the solutions `seq`
over the full graph has the members of `evalBgpFrom` of the translated
patterns from each solution of `seq`. The patterns are related elementwise
by `trTP`. -/
theorem evalSeq_triples_mem_iff {ig : IGraph} {g : Graph} (hr : ig.Represents g) (cx : Ctx) :
    ∀ (tps : List STriple) (bgp : Bgp), TrBgp tps bgp →
    ∀ (idx : Nat) (seq : List Binding) (mu' : Binding),
      mu' ∈ (evalSeq cx ig (fun _ => ⟨ig, none⟩) idx seq (tps.map Elt.triple)).1 ↔
        ∃ mu ∈ seq, mu' ∈ evalBgpFrom g bgp mu
  | [], [], .nil, idx, seq, mu' => by
      simp only [List.map_nil, evalSeq, evalBgpFrom, List.mem_singleton]
      exact ⟨fun h => ⟨mu', h, rfl⟩, fun ⟨mu, h, e⟩ => e ▸ h⟩
  | tp :: tps, tp' :: bgp, .cons htr hrest, idx, seq, mu' => by
      simp only [List.map_cons, evalSeq, evalElt]
      have ih := evalSeq_triples_mem_iff hr cx tps bgp hrest (idx + 1)
      have key : ∀ nu, nu ∈ seq.flatMap (fun mu => matchTriple ⟨ig, none⟩ mu tp) ↔
          ∃ mu ∈ seq, nu ∈ evalTP tp' g mu := by
        intro nu
        simp only [List.mem_flatMap]
        exact ⟨fun ⟨mu, h1, h2⟩ => ⟨mu, h1, (matchTriple_mem_iff_evalTP hr tp tp' htr mu nu).mp h2⟩,
               fun ⟨mu, h1, h2⟩ => ⟨mu, h1, (matchTriple_mem_iff_evalTP hr tp tp' htr mu nu).mpr h2⟩⟩
      simp only [evalBgpFrom, List.mem_flatMap]
      by_cases he : (List.flatMap (fun mu => matchTriple ⟨ig, none⟩ mu tp) seq).isEmpty = true
      · simp only [he, ite_true]
        simp only [List.isEmpty_iff] at he
        simp only [List.not_mem_nil, false_iff, not_exists, not_and]
        intro mu hmu nu hnu _
        have := (key nu).mpr ⟨mu, hmu, hnu⟩
        rw [he] at this; simp at this
      · simp only [he, Bool.false_eq_true, ite_false]
        rw [ih]
        constructor
        · rintro ⟨nu, hnu, h⟩
          obtain ⟨mu, hmu, hnu'⟩ := (key nu).mp hnu
          exact ⟨mu, hmu, nu, hnu', h⟩
        · rintro ⟨mu, hmu, nu, hnu, h⟩
          exact ⟨nu, (key nu).mpr ⟨mu, hmu, hnu⟩, h⟩

/-- Theorem B from one solution: a body of triple-pattern elements evaluated
by `evalSeq` from `mu` over an `IGraph` that represents `g` has the members
of `SPARQL.evalBgpFrom g bgp mu`. -/
theorem evalSeq_triples_mem_iff_evalBgpFrom {ig : IGraph} {g : Graph} (hr : ig.Represents g)
    (cx : Ctx) (tps : List STriple) (bgp : Bgp)
    (htr : TrBgp tps bgp) (idx : Nat) (mu mu' : Binding) :
    mu' ∈ (evalSeq cx ig (fun _ => ⟨ig, none⟩) idx [mu] (tps.map Elt.triple)).1 ↔
      mu' ∈ evalBgpFrom g bgp mu := by
  rw [evalSeq_triples_mem_iff hr cx tps bgp htr idx [mu] mu']
  simp

/-- Theorem B from the empty solution, against `SPARQL.evalBgp`, over
`IGraph.ofGraph g`. -/
theorem evalSeq_triples_ofGraph_mem_iff_evalBgp (g : Graph) (cx : Ctx) (tps : List STriple)
    (bgp : Bgp) (htr : TrBgp tps bgp) (mu' : Binding) :
    mu' ∈ (evalSeq cx (IGraph.ofGraph g) (fun _ => ⟨IGraph.ofGraph g, none⟩) 0 [[]]
        (tps.map Elt.triple)).1 ↔ mu' ∈ evalBgp bgp g :=
  evalSeq_triples_mem_iff_evalBgpFrom (IGraph.ofGraph_represents g) cx tps bgp htr 0 [] mu'

#print axioms matchTerm_eq_tryBindTerm
#print axioms matchTerm_eq_tryBindSubject
#print axioms chainT3_eq_tpMatch
#print axioms matchTriple_eq
#print axioms chainT3_agrees
#print axioms IGraph.Inv.insert
#print axioms IGraph.Inv.insertAll
#print axioms IGraph.ofGraph_represents
#print axioms Src.mem_candidates
#print axioms matchTriple_iff_all
#print axioms matchTriple_mem_iff_evalTP
#print axioms matchTriple_ofGraph_mem_iff_evalTP
#print axioms TrBgp.of_mapM
#print axioms evalSeq_triples_mem_iff
#print axioms evalSeq_triples_mem_iff_evalBgpFrom
#print axioms evalSeq_triples_ofGraph_mem_iff_evalBgp

end L4Factoidal.SPARQLRL
