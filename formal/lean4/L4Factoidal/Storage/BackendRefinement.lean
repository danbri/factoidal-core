/-
L4Factoidal.Storage.BackendRefinement — the backend evaluator
(`evalBgpBackend`, `evalPatternBackend`) against the reference evaluator and
against `Allowed`, the answers SPARQL 1.1 allows
(https://github.com/danbri/factoidal/issues/975, finding 6).

## What is proved

* `evalBgpBackend_kequiv`: for a backend `gb` whose law holds for a graph `G`
  (`BackendExact gb G`), and a list `g` that denotes the same graph and holds
  each triple once up to RDF term equality (`G t ↔ KeyMem g t`,
  `g.KeyNodup`), `evalBgpBackend b gb` and the reference `evalBgp b g`
  (SPARQL 1.1 section 18.3) give the same multiset of solution mappings up to
  RDF term equality (`SolKEquiv`: a permutation, then row for row the same
  `Term.joinKey` for every variable). Every basic graph pattern, triple-term
  patterns included. The planner's choice of the next pattern per row
  (`chooseBestTpBackend`), the bound it pushes down (`patternBoundFor`,
  `tpMatch_boundMatches`) and the representative of each `Term.eqb` class
  that a backend returns (`KeyMem`) are all covered.
  `evalBgpBackend_kequiv_of_den`: two backends with one denotation give the
  same answer in this sense.
* Multiplicity (SPARQL 1.1 section 18.5 counts solutions as a multiset):
  `SolKEquiv` is a permutation followed by a row-for-row relation, so each
  class of RDF-term-equal solution mappings has the same number of rows on
  both sides, and `SolKEquiv.length_eq` gives the same total. That the
  answer has no duplicate row is not claimed.
* `evalBgpBackend_solEquiv`, `evalBgpBackend_allowed`: every object of the
  graph and of the backend's rows is its own join key (`graphFixed`,
  `backendFixed`: no well-formed literal has an upper-case letter in a
  language tag), so the relation is the structural one (`SolEquiv`), and the
  backend's answer to a basic graph pattern with no `text:query` pattern is
  an answer `Allowed` admits.
* `evalPatternBackend_allowed`: for every pattern of `NativeFrag` (BGP with no
  `text:query` pattern, FILTER and OPTIONAL with a `backendLocal`
  condition, JOIN, UNION, MINUS, GRAPH with an IRI or a variable, VALUES,
  the empty pattern), over a graph backend that reads the active graph and
  named backends that read the named graphs pair for pair (`GraphRel`,
  `NamedRel`, distinct names), the answer of `evalPatternBackend` is an
  answer `Allowed` admits. Each operator of `Allowed` is the reference's own
  function, so the step is the arm's equality with it: `hashJoin_eq_join`,
  `hashLeftJoin_eq_leftJoin`, `hashMinus_eq_minus`, and `filterFn_local` (a
  `backendLocal` condition has no EXISTS, `existsFree_of_backendLocal`, and
  reads only the lookups of the row).
* `indexedWhere_allowed`: the same for the dataset record of the reference
  fallback, `indexedDatasetBackend d`, with premises on `d` only:
  `Dataset.IsSet` and IRI graph names.

## What is not proved

* BIND, LATERAL, property paths, SERVICE, sub-SELECT, FILTER and OPTIONAL
  with a condition that is not `backendLocal`, GRAPH with a blank node or a
  literal: the arms that materialise the dataset and call the reference, or
  whose freshness context differs from the reference's (`bindRowsFresh` with
  the empty graph); not in `NativeFrag`.
* The SELECT layer of `runSelectQueryBackendDataset` (the streaming
  COUNT and GROUP BY paths, ORDER BY, projection, DISTINCT, slices).
* That two answers `Allowed` admits for one pattern of `NativeFrag` are the
  same multiset (`SolEquiv`). So the id path (`IdLeaf.where_allowed`) and the
  fallback are both proved to give an allowed answer, and are not proved to
  give the same one.

## Why RDF term equality, and why it is now structural equality

`tryBindTerm` keeps the FIRST term bound to a variable and compares later
ones with `Term.eqb`, which folds the case of language tags. Until
2026-10-24 a graph could hold `"x"@en` and `"x"@EN`: for
`a :p "x"@en . b :p "y" . a :q "x"@EN` and the pattern `?s :p ?o . ?s :q ?o`
the reference bound `?o` to `"x"@en` and the backend (which reads `:q`
first) to `"x"@EN`, and `LANG(?o) = "en"` kept one row on one side and none
on the other. The reference had the same dependence on the order in which
the patterns are written. RDF 1.2 Concepts §3.4 makes the two spellings one
RDF term and permits the lower-case one; `RDF.literalWf` now requires it
(https://github.com/danbri/factoidal/issues/1001). So every term is its own
join key (`Term.joinKey_eq_self`), `Term.eqb` is structural equality
(`Term.eqb_iff_eq`), and the premises `GraphFixed` and `BackendFixed` hold
for every graph and every backend (`graphFixed`, `backendFixed`). The
theorems keep `SolKEquiv` where it is the natural statement; it now implies
`SolEquiv` with no premise. The `#guard`s at the end are the issue's case.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdLeafTheorems
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.StoreBackendDenotation
import L4Factoidal.Storage.Sbm11.AllowedPermTheorems
import L4Factoidal.Storage.Sbm11.ExprLocalTheorems
import L4Factoidal.Storage.Sbm11.IdPostTheorems
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.SPARQL.DatasetRestriction
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.Storage.BackendRefinement

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.Storage.Sbm11.IdGroup (Pw PermPw BindEq SolEquiv Allowed refSol filterFn)
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.DatasetRestriction (ngKey indexedDatasetBackend_named)
open L4Factoidal.Storage.Sbm11.AllowedPerm (GraphFixed graphFixed)
open L4Factoidal.Storage.Sbm11.IdLeaf (flatMap_comm_perm)

/-! ## 1. Solution mappings up to RDF term equality -/

/-- The same solution mapping up to RDF term equality: every variable has
    the same lookup, compared by `Term.joinKey` (`Term.eqb_iff_joinKey`). -/
def BindKEq (mu nu : Binding) : Prop :=
  ∀ v, (mu.lookup v).map Term.joinKey = (nu.lookup v).map Term.joinKey

theorem BindKEq.refl (mu : Binding) : BindKEq mu mu := fun _ => rfl
theorem BindKEq.symm {mu nu : Binding} (h : BindKEq mu nu) : BindKEq nu mu := fun v => (h v).symm
theorem BindKEq.trans {mu nu xi : Binding} (h1 : BindKEq mu nu) (h2 : BindKEq nu xi) :
    BindKEq mu xi := fun v => (h1 v).trans (h2 v)
theorem BindKEq.of_bindEq {mu nu : Binding} (h : BindEq mu nu) : BindKEq mu nu := fun v => by
  rw [h v]

/-- The same multiset of solution mappings up to RDF term equality. -/
def SolKEquiv (A B : SolutionSeq) : Prop := PermPw BindKEq A B

theorem SolKEquiv.refl (A : SolutionSeq) : SolKEquiv A A := PermPw.refl BindKEq.refl A
theorem SolKEquiv.symm {A B : SolutionSeq} (h : SolKEquiv A B) : SolKEquiv B A :=
  PermPw.symm (R := BindKEq) (fun _ _ h => BindKEq.symm h) h
theorem SolKEquiv.trans {A B C : SolutionSeq} (h1 : SolKEquiv A B) (h2 : SolKEquiv B C) :
    SolKEquiv A C :=
  PermPw.trans (R := BindKEq) (fun _ _ _ h h' => BindKEq.trans h h') h1 h2
theorem SolKEquiv.of_perm {A B : SolutionSeq} (h : A.Perm B) : SolKEquiv A B :=
  PermPw.of_perm BindKEq.refl h
theorem SolKEquiv.of_pw {A B : SolutionSeq} (h : Pw BindKEq A B) : SolKEquiv A B := PermPw.of_pw h

/-- The same number of rows. -/
theorem SolKEquiv.length_eq {A B : SolutionSeq} (h : SolKEquiv A B) : A.length = B.length := by
  obtain ⟨C, p, w⟩ := h
  exact p.length_eq.trans (Pw.length_eq w)

/-- Both absent, or both present and the same solution mapping up to RDF
    term equality. -/
def OptKEq : Option Binding → Option Binding → Prop
  | none, none => True
  | some a, some b => BindKEq a b
  | _, _ => False

theorem OptKEq.refl : ∀ (o : Option Binding), OptKEq o o
  | none => trivial
  | some a => BindKEq.refl a

theorem OptKEq.symm : ∀ {o o' : Option Binding}, OptKEq o o' → OptKEq o' o
  | none, none, _ => trivial
  | some _, some _, h => BindKEq.symm h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem OptKEq.trans : ∀ {o1 o2 o3 : Option Binding}, OptKEq o1 o2 → OptKEq o2 o3 → OptKEq o1 o3
  | none, none, none, _, _ => trivial
  | some _, some _, some _, h1, h2 => BindKEq.trans h1 h2
  | none, some _, _, h, _ => h.elim
  | some _, none, _, h, _ => h.elim
  | none, none, some _, _, h => h.elim
  | some _, some _, none, _, h => h.elim

theorem OptKEq.isSome_eq : ∀ {o o' : Option Binding}, OptKEq o o' → o.isSome = o'.isSome
  | none, none, _ => rfl
  | some _, some _, _ => rfl
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem lookup_bind_self (v : VarName) (x : Term) (mu : Binding) :
    (mu.bind v x).lookup v = some x := by
  simp [Binding.bind, Binding.lookup]

theorem lookup_bind_ne {v w : VarName} (x : Term) (mu : Binding) (h : v ≠ w) :
    (mu.bind v x).lookup w = mu.lookup w := by
  simp [Binding.bind, Binding.lookup, h]

theorem bindKEq_bind {mu nu : Binding} (v : VarName) {x y : Term} (hxy : x.joinKey = y.joinKey)
    (h : BindKEq mu nu) : BindKEq (mu.bind v x) (nu.bind v y) := by
  intro w
  by_cases hw : v = w
  · subst hw; rw [lookup_bind_self, lookup_bind_self]; simp [hxy]
  · rw [lookup_bind_ne _ _ hw, lookup_bind_ne _ _ hw]; exact h w

theorem bindKEq_bind_swap {v w : VarName} (x y : Term) (mu : Binding) (h : v ≠ w) :
    BindKEq ((mu.bind v x).bind w y) ((mu.bind w y).bind v x) := by
  intro u
  by_cases hv : v = u
  · subst hv
    rw [lookup_bind_ne _ _ (Ne.symm h), lookup_bind_self, lookup_bind_self]
  · by_cases hw : w = u
    · subst hw
      rw [lookup_bind_self, lookup_bind_ne _ _ hv, lookup_bind_self]
    · rw [lookup_bind_ne _ _ hw, lookup_bind_ne _ _ hv, lookup_bind_ne _ _ hv,
        lookup_bind_ne _ _ hw]

/-! ## 2. Matching as a sequence of positions

`tryBindTerm` on a triple-term pattern matches its three positions one after
the other; `tpMatch` matches subject, predicate and object one after the
other. `slotsT` and `tpSlots` flatten both into one list of positions, each a
variable, a constant, or a shape that cannot match (`fail`), and
`tpMatch_slots` proves `tpMatch` is the match of that list. -/

/-- One position of a flattened pattern. -/
inductive TSlot where
  | var (v : VarName)
  | iri (i : WfIri)
  | bnode (b : BNodeId)
  | lit (l : WfLiteral)
  | fail

/-- One position against one term: `tryBindTerm` on a pattern that is not a
    triple term. -/
def slotMatch : TSlot → Term → Binding → Option Binding
  | .var v, x, mu =>
      match mu.lookup v with
      | some e => if e.eqb x then some mu else none
      | none => some (mu.bind v x)
  | .iri i, x, mu =>
      match x with
      | .iri i' => if i == i' then some mu else none
      | _ => none
  | .bnode b, x, mu =>
      match x with
      | .bnode b' => if b == b' then some mu else none
      | _ => none
  | .lit l, x, mu =>
      match x with
      | .literal l' => if l.val.eqb l'.val then some mu else none
      | _ => none
  | .fail, _, _ => none

/-- A list of positions, matched left to right. -/
def matchSlots : List (TSlot × Term) → Binding → Option Binding
  | [], mu => some mu
  | (s, x) :: rest, mu =>
      match slotMatch s x mu with
      | none => none
      | some mu1 => matchSlots rest mu1

/-- The positions of a pattern term against a term. A device of the proofs,
    never run: `noncomputable`, so no code is generated for its recursion on
    the nesting of triple terms. -/
noncomputable def slotsT : PatternTerm → Term → List (TSlot × Term)
  | .var v, x => [(.var v, x)]
  | .iri i, x => [(.iri i, x)]
  | .bnode b, x => [(.bnode b, x)]
  | .literal l, x => [(.lit l, x)]
  | .tripleTerm ps pp po, x =>
      match x with
      | .tripleTerm s p o => slotsT ps s.toTerm ++ slotsT pp (.iri p) ++ slotsT po o
      | _ => [(.fail, x)]

/-- The positions of a subject pattern against a subject. -/
def slotsS : PatternSubject → Subject → List (TSlot × Term)
  | .var v, s => [(.var v, s.toTerm)]
  | .iri i, s => [(.iri i, s.toTerm)]
  | .bnode b, s => [(.bnode b, s.toTerm)]
  | .tripleTerm _ _ _, s => [(.fail, s.toTerm)]

/-- The positions of a triple pattern against a triple. -/
noncomputable def tpSlots (tp : TriplePattern) (t : Triple) : List (TSlot × Term) :=
  slotsS tp.s t.s ++ slotsT tp.p (.iri t.p) ++ slotsT tp.o t.o

theorem matchSlots_single (s : TSlot) (x : Term) (mu : Binding) :
    matchSlots [(s, x)] mu = slotMatch s x mu := by
  simp only [matchSlots]
  cases slotMatch s x mu <;> rfl

theorem matchSlots_append : ∀ (S1 S2 : List (TSlot × Term)) (mu : Binding),
    matchSlots (S1 ++ S2) mu =
      match matchSlots S1 mu with
      | none => none
      | some mu1 => matchSlots S2 mu1
  | [], _, _ => rfl
  | (s, x) :: rest, S2, mu => by
    simp only [List.cons_append, matchSlots]
    cases slotMatch s x mu with
    | none => rfl
    | some mu1 => exact matchSlots_append rest S2 mu1

theorem tryBindTerm_slots : ∀ (pt : PatternTerm) (x : Term) (mu : Binding),
    tryBindTerm pt x mu = matchSlots (slotsT pt x) mu
  | .var v, x, mu => by rw [slotsT, matchSlots_single]; rfl
  | .iri i, x, mu => by rw [slotsT, matchSlots_single]; cases x <;> rfl
  | .bnode b, x, mu => by rw [slotsT, matchSlots_single]; cases x <;> rfl
  | .literal l, x, mu => by rw [slotsT, matchSlots_single]; cases x <;> rfl
  | .tripleTerm ps pp po, x, mu => by
    cases x with
    | tripleTerm s p o =>
      simp only [slotsT, tryBindTerm]
      rw [matchSlots_append, matchSlots_append, ← tryBindTerm_slots ps]
      cases tryBindTerm ps s.toTerm mu with
      | none => rfl
      | some mu1 =>
        simp only
        rw [← tryBindTerm_slots pp]
        cases tryBindTerm pp (.iri p) mu1 with
        | none => rfl
        | some mu2 => exact tryBindTerm_slots po o mu2
    | iri _ => rfl
    | bnode _ => rfl
    | literal _ => rfl

theorem tryBindSubject_slots (ps : PatternSubject) (s : Subject) (mu : Binding) :
    tryBindSubject ps s mu = matchSlots (slotsS ps s) mu := by
  cases ps <;> rw [slotsS, matchSlots_single] <;> cases s <;> rfl

theorem tpMatch_slots (tp : TriplePattern) (t : Triple) (mu : Binding) :
    tpMatch tp t mu = matchSlots (tpSlots tp t) mu := by
  unfold tpMatch tpSlots
  rw [matchSlots_append, matchSlots_append, ← tryBindSubject_slots]
  cases tryBindSubject tp.s t.s mu with
  | none => rfl
  | some mu1 =>
    simp only
    rw [← tryBindTerm_slots]
    cases tryBindTerm tp.p (.iri t.p) mu1 with
    | none => rfl
    | some mu2 => exact tryBindTerm_slots tp.o t.o mu2

/-! ## 3. Matching depends on the row and the triple only up to RDF term equality -/

/-- `Term.eqb` is equality of join keys, on either side. -/
theorem eqb_congr {e e' x y : Term} (he : e.joinKey = e'.joinKey) (hxy : x.joinKey = y.joinKey) :
    e.eqb x = e'.eqb y := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.eqb_iff_joinKey, Term.eqb_iff_joinKey, he, hxy]

theorem slotMatch_congr (s : TSlot) {x y : Term} (hxy : x.joinKey = y.joinKey) {mu nu : Binding}
    (h : BindKEq mu nu) : OptKEq (slotMatch s x mu) (slotMatch s y nu) := by
  cases s with
  | var v =>
    have hv := h v
    simp only [slotMatch]
    cases hm : mu.lookup v <;> cases hn : nu.lookup v <;> rw [hm, hn] at hv <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hv
    · exact bindKEq_bind v hxy h
    · rename_i e e'
      show OptKEq (if e.eqb x = true then some mu else none) (if e'.eqb y = true then some nu else none)
      rw [eqb_congr hv hxy]
      cases e'.eqb y
      · trivial
      · exact h
  | iri i =>
    cases x <;> cases y <;> simp only [Term.joinKey, reduceCtorEq, Term.iri.injEq,
      Term.bnode.injEq, Term.literal.injEq, Term.tripleTerm.injEq] at hxy <;> try trivial
    subst hxy
    simp only [slotMatch]
    split
    · exact h
    · trivial
  | bnode b =>
    cases x <;> cases y <;> simp only [Term.joinKey, reduceCtorEq, Term.iri.injEq,
      Term.bnode.injEq, Term.literal.injEq, Term.tripleTerm.injEq] at hxy <;> try trivial
    subst hxy
    simp only [slotMatch]
    split
    · exact h
    · trivial
  | lit l =>
    cases x <;> cases y <;> simp only [Term.joinKey, reduceCtorEq, Term.iri.injEq,
      Term.bnode.injEq, Term.literal.injEq, Term.tripleTerm.injEq] at hxy <;> try trivial
    rename_i l1 l2
    simp only [Subtype.mk.injEq] at hxy
    have e : l.val.eqb l1.val = l.val.eqb l2.val := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h1
        exact Literal.eqb_of_joinKey_eq ((Literal.joinKey_eq_of_eqb h1).trans hxy)
      · intro h1
        exact Literal.eqb_of_joinKey_eq ((Literal.joinKey_eq_of_eqb h1).trans hxy.symm)
    simp only [slotMatch, e]
    split
    · exact h
    · trivial
  | fail => trivial

/-- Two position lists with the same positions and terms equal up to RDF
    term equality. -/
def SlotRel (a b : TSlot × Term) : Prop := a.1 = b.1 ∧ a.2.joinKey = b.2.joinKey

theorem slotRel_refl (a : TSlot × Term) : SlotRel a a := ⟨rfl, rfl⟩

theorem matchSlots_congr : ∀ {S S' : List (TSlot × Term)}, Pw SlotRel S S' →
    ∀ {mu nu : Binding}, BindKEq mu nu → OptKEq (matchSlots S mu) (matchSlots S' nu)
  | _, _, .nil, _, _, h => h
  | (s, x) :: _, (s', y) :: _, .cons hr t, mu, nu, h => by
    obtain ⟨e1, e2⟩ := hr
    simp only at e1 e2
    subst e1
    have hs := slotMatch_congr s e2 h
    simp only [matchSlots]
    revert hs
    cases slotMatch s x mu <;> cases slotMatch s y nu <;> intro hs
    · trivial
    · exact hs.elim
    · exact hs.elim
    · exact matchSlots_congr t hs

theorem slotsT_congr : ∀ (pt : PatternTerm) {x y : Term}, x.joinKey = y.joinKey →
    Pw SlotRel (slotsT pt x) (slotsT pt y)
  | .var _, _, _, h => .cons ⟨rfl, h⟩ .nil
  | .iri _, _, _, h => .cons ⟨rfl, h⟩ .nil
  | .bnode _, _, _, h => .cons ⟨rfl, h⟩ .nil
  | .literal _, _, _, h => .cons ⟨rfl, h⟩ .nil
  | .tripleTerm ps pp po, x, y, h => by
    cases x with
    | tripleTerm s1 p1 o1 =>
      cases y with
      | tripleTerm s2 p2 o2 =>
        simp only [Term.joinKey, Term.tripleTerm.injEq] at h
        obtain ⟨hs, hp, ho⟩ := h
        subst hs; subst hp
        simp only [slotsT]
        exact Pw.append (Pw.append (Pw.refl slotRel_refl _) (Pw.refl slotRel_refl _))
          (slotsT_congr po ho)
      | _ => simp [Term.joinKey] at h
    | _ =>
      cases y <;> simp only [slotsT] <;> first | exact .cons ⟨rfl, h⟩ .nil | simp [Term.joinKey] at h

theorem tpSlots_congr (tp : TriplePattern) {t t' : Triple} (h : t.key = t'.key) :
    Pw SlotRel (tpSlots tp t) (tpSlots tp t') := by
  obtain ⟨s, p, o⟩ := t
  obtain ⟨s', p', o'⟩ := t'
  simp only [Triple.key, Triple.mk.injEq] at h
  obtain ⟨hs, hp, ho⟩ := h
  subst hs; subst hp
  exact Pw.append (Pw.refl slotRel_refl _) (slotsT_congr tp.o ho)

/-- **`tpMatch` up to RDF term equality**: RDF-term-equal triples and rows
    give RDF-term-equal rows. -/
theorem tpMatch_congr (tp : TriplePattern) {t t' : Triple} (ht : t.key = t'.key)
    {mu nu : Binding} (h : BindKEq mu nu) : OptKEq (tpMatch tp t mu) (tpMatch tp t' nu) := by
  rw [tpMatch_slots, tpMatch_slots]
  exact matchSlots_congr (tpSlots_congr tp ht) h

/-! ## 4. The order of the positions does not matter -/

/-- A position that is not a variable does not change the row. -/
def constOk : TSlot → Term → Bool
  | .var _, _ => true
  | .iri i, x => match x with | .iri i' => i == i' | _ => false
  | .bnode b, x => match x with | .bnode b' => b == b' | _ => false
  | .lit l, x => match x with | .literal l' => l.val.eqb l'.val | _ => false
  | .fail, _ => false

theorem slot_var_or_const (s : TSlot) :
    (∃ v, s = .var v) ∨ (∀ x mu, slotMatch s x mu = if constOk s x then some mu else none) := by
  cases s with
  | var v => exact .inl ⟨v, rfl⟩
  | iri i => exact .inr fun x mu => by cases x <;> simp [slotMatch, constOk]
  | bnode b => exact .inr fun x mu => by cases x <;> simp [slotMatch, constOk]
  | lit l => exact .inr fun x mu => by cases x <;> simp only [slotMatch, constOk] <;> rfl
  | fail => exact .inr fun x mu => by simp [slotMatch, constOk]

/-- Two positions in a row. -/
def slot2 (a b : TSlot × Term) (mu : Binding) : Option Binding :=
  match slotMatch a.1 a.2 mu with
  | none => none
  | some r1 => slotMatch b.1 b.2 r1

/-- Two positions commute, up to RDF term equality. -/
theorem slot_swap (a b : TSlot × Term) (mu : Binding) : OptKEq (slot2 a b mu) (slot2 b a mu) := by
  obtain ⟨sa, x⟩ := a
  obtain ⟨sb, y⟩ := b
  simp only [slot2]
  rcases slot_var_or_const sa with ⟨v, rfl⟩ | ha <;> rcases slot_var_or_const sb with ⟨w, rfl⟩ | hb
  · -- two variables
    by_cases hvw : v = w
    · subst hvw
      simp only [slotMatch]
      cases hv : mu.lookup v with
      | some e =>
        simp only
        cases h1 : e.eqb x <;> cases h2 : e.eqb y <;> simp [hv, h1, h2, OptKEq, BindKEq.refl]
      | none =>
        simp only [lookup_bind_self]
        rw [Term.eqb_symm y x]
        cases h1 : x.eqb y
        · trivial
        · exact bindKEq_bind v (Term.joinKey_eq_of_eqb h1) (BindKEq.refl mu)
    · simp only [slotMatch]
      cases hv : mu.lookup v with
      | some e =>
        cases hw : mu.lookup w with
        | some f =>
          simp only
          cases h1 : e.eqb x <;> cases h2 : f.eqb y <;> simp [hv, hw, h1, h2, OptKEq, BindKEq.refl]
        | none =>
          simp only [hv, lookup_bind_ne _ _ (Ne.symm hvw)]
          cases h1 : e.eqb x <;> simp [hw, OptKEq, BindKEq.refl]
      | none =>
        cases hw : mu.lookup w with
        | some f =>
          simp only [hw, lookup_bind_ne _ _ hvw]
          cases h2 : f.eqb y <;> simp [hv, OptKEq, BindKEq.refl]
        | none =>
          simp only [hv, hw, lookup_bind_ne _ _ hvw, lookup_bind_ne _ _ (Ne.symm hvw)]
          exact bindKEq_bind_swap x y mu hvw
  · -- a variable, then a constant
    simp only [hb]
    cases constOk sb y <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
      generalize slotMatch (.var v) x mu = o <;> cases o <;> simp [OptKEq, BindKEq.refl]
  · -- a constant, then a variable
    simp only [ha]
    cases constOk sa x <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
      generalize slotMatch (.var w) y mu = o <;> cases o <;> simp [OptKEq, BindKEq.refl]
  · -- two constants
    simp only [ha, hb]
    cases constOk sa x <;> cases constOk sb y <;> simp [OptKEq, BindKEq.refl]

theorem optBind_congr (S : List (TSlot × Term)) :
    ∀ {o o' : Option Binding}, OptKEq o o' →
      OptKEq (match o with | none => none | some r1 => matchSlots S r1)
        (match o' with | none => none | some r1 => matchSlots S r1)
  | none, none, _ => trivial
  | some _, some _, h => matchSlots_congr (Pw.refl slotRel_refl S) h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

/-- **The order of the positions**: a permutation of the positions gives the
    same match, up to RDF term equality. -/
theorem matchSlots_perm {S S' : List (TSlot × Term)} (hp : S.Perm S') :
    ∀ (mu : Binding), OptKEq (matchSlots S mu) (matchSlots S' mu) := by
  induction hp with
  | nil => intro mu; exact BindKEq.refl mu
  | cons x _ ih =>
    intro mu
    obtain ⟨s, y⟩ := x
    simp only [matchSlots]
    cases slotMatch s y mu with
    | none => trivial
    | some r1 => exact ih r1
  | swap a b l =>
    intro mu
    have h2 := optBind_congr l (slot_swap b a mu)
    have e1 : matchSlots (b :: a :: l) mu =
        match slot2 b a mu with
        | none => none
        | some r1 => matchSlots l r1 := by
      obtain ⟨sb, z⟩ := b
      obtain ⟨sa, y⟩ := a
      simp only [matchSlots, slot2]
      cases slotMatch sb z mu <;> rfl
    have e2 : matchSlots (a :: b :: l) mu =
        match slot2 a b mu with
        | none => none
        | some r1 => matchSlots l r1 := by
      obtain ⟨sb, z⟩ := b
      obtain ⟨sa, y⟩ := a
      simp only [matchSlots, slot2]
      cases slotMatch sa y mu <;> rfl
    rw [e1, e2]
    exact h2
  | trans _ _ ih1 ih2 => intro mu; exact OptKEq.trans (ih1 mu) (ih2 mu)

/-! ## 5. The reference BGP evaluation in any order of the patterns -/

theorem pw_filterMap2 {α : Type} {Rel : α → α → Prop} (f : α → Option Binding)
    (g : α → Option Binding) (hfg : ∀ a b, Rel a b → OptKEq (f a) (g b)) :
    ∀ {A B : List α}, Pw Rel A B → Pw BindKEq (A.filterMap f) (B.filterMap g)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons h t => by
    have ih := pw_filterMap2 f g hfg t
    have hx := hfg a b h
    simp only [List.filterMap_cons]
    revert hx
    cases f a <;> cases g b <;> intro hx
    · exact ih
    · exact hx.elim
    · exact hx.elim
    · exact .cons hx ih

theorem pw_flatMap (F G : Binding → SolutionSeq)
    (hFG : ∀ a b, BindKEq a b → SolKEquiv (F a) (G b)) :
    ∀ {A B : SolutionSeq}, Pw BindKEq A B → SolKEquiv (A.flatMap F) (B.flatMap G)
  | _, _, .nil => SolKEquiv.refl []
  | _, _, .cons h t => by
    simp only [List.flatMap_cons]
    exact PermPw.append (hFG _ _ h) (pw_flatMap F G hFG t)

theorem solK_flatMap (F G : Binding → SolutionSeq)
    (hFG : ∀ a b, BindKEq a b → SolKEquiv (F a) (G b)) {A B : SolutionSeq}
    (h : SolKEquiv A B) : SolKEquiv (A.flatMap F) (B.flatMap G) := by
  obtain ⟨C, p, w⟩ := h
  exact SolKEquiv.trans (SolKEquiv.of_perm (p.flatMap_right F)) (pw_flatMap F G hFG w)

theorem pw_flatMap_pw (F : Binding → SolutionSeq) (hF : ∀ a b, BindKEq a b → Pw BindKEq (F a) (F b)) :
    ∀ {A B : SolutionSeq}, Pw BindKEq A B → Pw BindKEq (A.flatMap F) (B.flatMap F)
  | _, _, .nil => .nil
  | _, _, .cons h t => by
    simp only [List.flatMap_cons]
    exact Pw.append (hF _ _ h) (pw_flatMap_pw F hF t)

theorem evalTP_congr (tp : TriplePattern) (g : Graph) {mu nu : Binding} (h : BindKEq mu nu) :
    Pw BindKEq (evalTP tp g mu) (evalTP tp g nu) :=
  pw_filterMap2 (Rel := Eq) _ _ (fun t t' e => tpMatch_congr tp (by rw [e]) h) (Pw.refl (fun _ => rfl) g)

theorem evalBgpFrom_congr (g : Graph) :
    ∀ (ps : Bgp) {mu nu : Binding}, BindKEq mu nu →
      Pw BindKEq (evalBgpFrom g ps mu) (evalBgpFrom g ps nu)
  | [], _, _, h => .cons h .nil
  | tp :: rest, _, _, h =>
    pw_flatMap_pw _ (fun _ _ h' => evalBgpFrom_congr g rest h') (evalTP_congr tp g h)

/-- An optional row, continued. -/
def optCont (o : Option Binding) (H : Binding → SolutionSeq) : SolutionSeq :=
  match o with
  | none => []
  | some r => H r

theorem filterMap_flatMap {α : Type} (f : α → Option Binding) (H : Binding → SolutionSeq) :
    ∀ (T : List α), (T.filterMap f).flatMap H = T.flatMap fun x => optCont (f x) H
  | [] => rfl
  | x :: T => by
    simp only [List.filterMap_cons, List.flatMap_cons]
    cases f x with
    | none => simp only [optCont, List.nil_append]; exact filterMap_flatMap f H T
    | some r => simp only [List.flatMap_cons, optCont]; rw [filterMap_flatMap f H T]; rfl

theorem optCont_flatMap {α : Type} (o : Option Binding) (T : List α)
    (m : α → Binding → Option Binding) (H : Binding → SolutionSeq) :
    optCont o (fun r1 => T.flatMap fun x => optCont (m x r1) H) =
      T.flatMap fun x => optCont (match o with | none => none | some r1 => m x r1) H := by
  cases o with
  | none => simp [optCont]
  | some r1 => rfl

theorem optCont_equiv (H : Binding → SolutionSeq) (hH : ∀ a b, BindKEq a b → SolKEquiv (H a) (H b)) :
    ∀ {o o' : Option Binding}, OptKEq o o' → SolKEquiv (optCont o H) (optCont o' H)
  | none, none, _ => SolKEquiv.refl []
  | some _, some _, h => hH _ _ h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem flatMap_kequiv {α : Type} (F G : α → SolutionSeq) (L : List α)
    (h : ∀ x ∈ L, SolKEquiv (F x) (G x)) : SolKEquiv (L.flatMap F) (L.flatMap G) :=
  PermPw.flatMap F G L h

/-- Two patterns evaluated one after the other, as one double loop over the
    triples. -/
theorem evalBgpFrom_two (g : Graph) (a b : TriplePattern) (l : Bgp) (mu : Binding) :
    evalBgpFrom g (a :: b :: l) mu =
      g.flatMap fun x => g.flatMap fun x' =>
        optCont (matchSlots (tpSlots a x ++ tpSlots b x') mu) (evalBgpFrom g l) := by
  simp only [evalBgpFrom, evalTP, filterMap_flatMap]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x _
  rw [optCont_flatMap]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x' _
  rw [matchSlots_append, tpMatch_slots]
  cases matchSlots (tpSlots a x) mu with
  | none => rfl
  | some r => simp only [tpMatch_slots]

/-- **The order of the patterns** (SPARQL 1.1 section 18.3: a basic graph
    pattern is a set of triple patterns). The reference evaluation in any
    order of the patterns gives the same multiset of solution mappings up to
    RDF term equality. -/
theorem evalBgpFrom_perm (g : Graph) {ps ps' : Bgp} (hp : ps.Perm ps') :
    ∀ (mu nu : Binding), BindKEq mu nu → SolKEquiv (evalBgpFrom g ps mu) (evalBgpFrom g ps' nu) := by
  induction hp with
  | nil => intro mu nu h; exact SolKEquiv.of_pw (.cons h .nil)
  | cons t _ ih =>
    intro mu nu h
    exact pw_flatMap _ _ (fun a b hab => ih a b hab) (evalTP_congr t g h)
  | swap a b l =>
    intro mu nu h
    rw [evalBgpFrom_two, evalBgpFrom_two]
    have hH : ∀ a b, BindKEq a b → SolKEquiv (evalBgpFrom g l a) (evalBgpFrom g l b) :=
      fun _ _ hab => SolKEquiv.of_pw (evalBgpFrom_congr g l hab)
    refine SolKEquiv.trans (SolKEquiv.of_perm (flatMap_comm_perm _ g g)) ?_
    apply flatMap_kequiv
    intro x1 _
    apply flatMap_kequiv
    intro x2 _
    apply optCont_equiv _ hH
    exact OptKEq.trans (matchSlots_perm List.perm_append_comm mu)
      (matchSlots_congr (Pw.refl slotRel_refl _) h)
  | trans _ _ ih1 ih2 =>
    intro mu nu h
    exact SolKEquiv.trans (ih1 mu nu h) (ih2 nu nu (BindKEq.refl nu))

/-! ## 6. The bound the planner hands the backend drops no match -/

theorem ite_some' {α : Type} {c : Prop} [Decidable c] {a b : α}
    (h : (if c then some a else none) = some b) : c ∧ b = a := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h; exact ⟨hc, rfl⟩
  · rw [if_neg hc] at h; cases h

/-- The bound of an object (or predicate) position under `mu` is
    RDF-term-equal to every term the position matches from a row that
    extends `mu`. -/
theorem boundObject_sound : ∀ (pt : PatternTerm) {x : Term} {mu mu1 mu' : Binding},
    (∀ {v e}, mu.lookup v = some e → mu1.lookup v = some e) →
    tryBindTerm pt x mu1 = some mu' →
    ∀ {o0 : Term}, boundObjectOfPattern pt mu = some o0 → o0.eqb x = true := by
  intro pt
  induction pt with
  | iri i =>
    intro x mu mu1 mu' _ h o0 hb
    simp only [boundObjectOfPattern, Option.some.injEq] at hb; subst hb
    cases x <;> simp only [tryBindTerm, reduceCtorEq] at h
    simpa [Term.eqb] using (ite_some' h).1
  | bnode b =>
    intro x mu mu1 mu' _ h o0 hb
    simp only [boundObjectOfPattern, Option.some.injEq] at hb; subst hb
    cases x <;> simp only [tryBindTerm, reduceCtorEq] at h
    simpa [Term.eqb] using (ite_some' h).1
  | literal l =>
    intro x mu mu1 mu' _ h o0 hb
    simp only [boundObjectOfPattern, Option.some.injEq] at hb; subst hb
    cases x <;> simp only [tryBindTerm, reduceCtorEq] at h
    simpa [Term.eqb] using (ite_some' h).1
  | var v =>
    intro x mu mu1 mu' hext h o0 hb
    simp only [boundObjectOfPattern] at hb
    simp only [tryBindTerm, hext hb] at h
    exact (ite_some' h).1
  | tripleTerm ps pp po ihs ihp iho =>
    intro x mu mu1 mu' hext h o0 hb
    cases x with
    | tripleTerm s p o =>
      simp only [tryBindTerm] at h
      cases h1 : tryBindTerm ps s.toTerm mu1 with
      | none => rw [h1] at h; cases h
      | some m1 =>
        rw [h1] at h; simp only at h
        cases h2 : tryBindTerm pp (.iri p) m1 with
        | none => rw [h2] at h; cases h
        | some m2 =>
          rw [h2] at h; simp only at h
          have e1 : ∀ {v e}, mu.lookup v = some e → m1.lookup v = some e :=
            fun hv => tryBindTerm_preserves_lookup h1 (hext hv)
          have e2 : ∀ {v e}, mu.lookup v = some e → m2.lookup v = some e :=
            fun hv => tryBindTerm_preserves_lookup h2 (e1 hv)
          simp only [boundObjectOfPattern] at hb
          cases hs : boundObjectOfPattern ps mu with
          | none => rw [hs] at hb; cases hb
          | some sterm =>
            rw [hs] at hb; simp only at hb
            cases hss : sterm.toSubject? with
            | none => rw [hss] at hb; cases hb
            | some ssub =>
              rw [hss] at hb; simp only at hb
              cases hp : boundObjectOfPattern pp mu with
              | none => rw [hp] at hb; cases hb
              | some pterm =>
                rw [hp] at hb
                cases pterm with
                | iri ppi =>
                  simp only at hb
                  cases ho : boundObjectOfPattern po mu with
                  | none => rw [ho] at hb; cases hb
                  | some oterm =>
                    rw [ho] at hb; simp only [Option.some.injEq] at hb; subst hb
                    have q1 := ihs hext h1 hs
                    have q2 := ihp e1 h2 hp
                    have q3 := iho e2 h ho
                    have es : sterm = s.toTerm :=
                      Term.eqb_eq_of_toSubject (x := s) q1 (by cases s <;> rfl)
                    subst es
                    have hsub : ssub = s := by
                      cases s <;> simp [Subject.toTerm, Term.toSubject?] at hss <;> exact hss.symm
                    subst hsub
                    simp only [Term.eqb, Subject.eqb_refl, Bool.true_and, q3, Bool.and_true]
                    simpa [Term.eqb] using q2
                | bnode _ => simp at hb
                | literal _ => simp at hb
                | tripleTerm _ _ _ => simp at hb
    | iri _ => simp [tryBindTerm] at h
    | bnode _ => simp [tryBindTerm] at h
    | literal _ => simp [tryBindTerm] at h

theorem boundSubject_sound {ps : PatternSubject} {s : Subject} {mu mu' : Binding}
    (h : tryBindSubject ps s mu = some mu') {s0 : Subject}
    (hb : boundSubjectOfPattern ps mu = some s0) : s0.eqb s = true := by
  cases ps with
  | iri i =>
    simp only [boundSubjectOfPattern, Option.some.injEq] at hb; subst hb
    cases s <;> simp only [tryBindSubject, reduceCtorEq] at h
    simpa [Subject.eqb] using (ite_some' h).1
  | bnode b =>
    simp only [boundSubjectOfPattern, Option.some.injEq] at hb; subst hb
    cases s <;> simp only [tryBindSubject, reduceCtorEq] at h
    simpa [Subject.eqb] using (ite_some' h).1
  | tripleTerm _ _ _ => simp [boundSubjectOfPattern] at hb
  | var v =>
    simp only [boundSubjectOfPattern] at hb
    simp only [tryBindSubject] at h
    cases hv : mu.lookup v with
    | none => rw [hv] at hb; cases hb
    | some e =>
      rw [hv] at hb h
      have he := (ite_some' h).1
      cases e <;> simp only [Option.some.injEq, reduceCtorEq] at hb <;> subst hb <;>
        cases s <;> simp_all [Term.eqb, Subject.toTerm, Subject.eqb]

theorem boundPredicate_obj {pt : PatternTerm} {mu : Binding} {p0 : WfIri}
    (h : boundPredicateOfPattern pt mu = some p0) : boundObjectOfPattern pt mu = some (.iri p0) := by
  cases pt with
  | iri i => simp only [boundPredicateOfPattern, Option.some.injEq] at h; subst h; rfl
  | var v =>
    simp only [boundPredicateOfPattern] at h
    simp only [boundObjectOfPattern]
    cases hv : mu.lookup v with
    | none => rw [hv] at h; cases h
    | some e => rw [hv] at h; cases e <;> simp_all
  | bnode _ => simp [boundPredicateOfPattern] at h
  | literal _ => simp [boundPredicateOfPattern] at h
  | tripleTerm _ _ _ => simp [boundPredicateOfPattern] at h

/-- **The pushdown drops no match**: a triple that a pattern matches from
    `mu` satisfies the bound the planner computes from `mu`. -/
theorem tpMatch_boundMatches {tp : TriplePattern} {t : Triple} {mu mu' : Binding}
    (h : tpMatch tp t mu = some mu') : boundMatches (patternBoundFor tp mu) t = true := by
  unfold tpMatch at h
  cases h1 : tryBindSubject tp.s t.s mu with
  | none => rw [h1] at h; cases h
  | some m1 =>
    rw [h1] at h; simp only at h
    cases h2 : tryBindTerm tp.p (.iri t.p) m1 with
    | none => rw [h2] at h; cases h
    | some m2 =>
      rw [h2] at h; simp only at h
      have e1 : ∀ {v e}, mu.lookup v = some e → m1.lookup v = some e :=
        fun hv => tryBindSubject_preserves_lookup h1 hv
      have e2 : ∀ {v e}, mu.lookup v = some e → m2.lookup v = some e :=
        fun hv => tryBindTerm_preserves_lookup h2 (e1 hv)
      simp only [boundMatches, patternBoundFor, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases hs : boundSubjectOfPattern tp.s mu with
        | none => rfl
        | some s0 => exact boundSubject_sound h1 hs
      · cases hp : boundPredicateOfPattern tp.p mu with
        | none => rfl
        | some p0 =>
          have := boundObject_sound tp.p e1 h2 (boundPredicate_obj hp)
          simpa [Term.eqb] using this
      · cases ho : boundObjectOfPattern tp.o mu with
        | none => rfl
        | some o0 => exact boundObject_sound tp.o e2 h ho

/-! ## 7. One pattern through the backend -/

theorem filterMap_filter_of {α β : Type} (p : α → Bool) (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = true → p x = true) →
      (l.filter p).filterMap f = l.filterMap f
  | [], _ => rfl
  | x :: l, h => by
    have ih := filterMap_filter_of p f l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filter_cons]
    by_cases hp : p x = true
    · simp only [hp, ite_true, List.filterMap_cons, ih]
    · have hn : f x = none := by
        cases hf : f x with
        | none => rfl
        | some _ => exact absurd (h x (List.mem_cons_self ..) (by simp [hf])) hp
      simp only [hp, List.filterMap_cons, hn, Bool.false_eq_true, ite_false]
      exact ih

/-- A permutation of the images lifts to a permutation of the list, followed
    by equal images element for element. -/
theorem perm_map_lift {α β : Type} (f : α → β) :
    ∀ (B A : List α), (A.map f).Perm (B.map f) → ∃ C, A.Perm C ∧ Pw (fun a b => f a = f b) C B
  | [], A, h => by
    have : A = [] := by simpa using h.length_eq
    subst this; exact ⟨[], List.Perm.refl _, .nil⟩
  | b :: B, A, h => by
    have hm : f b ∈ A.map f := h.symm.subset (by simp)
    obtain ⟨a, ha, hab⟩ := List.mem_map.mp hm
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
    have hp : (s ++ a :: t).Perm (a :: (s ++ t)) := List.perm_middle
    have h' : ((s ++ t).map f).Perm (B.map f) := by
      have := (hp.map f).symm.trans h
      simp only [List.map_cons] at this
      rw [hab] at this
      exact this.cons_inv
    obtain ⟨C, pc, wc⟩ := perm_map_lift f B (s ++ t) h'
    exact ⟨a :: C, hp.trans (pc.cons a), .cons hab wc⟩

/-- **One pattern through the backend**: the backend's rows for one
    pattern from `mu` are the reference's rows from `nu`, up to order and
    RDF term equality, for `mu` and `nu` RDF-term-equal. -/
theorem evalSingleTpBackend_kequiv {gb : GraphBackend} {G : Triple → Prop} {g : Graph}
    (hx : BackendExact gb G) (hg : g.KeyNodup) (hG : ∀ t, G t ↔ KeyMem g t)
    (tp : TriplePattern) {mu nu : Binding} (h : BindKEq mu nu) :
    SolKEquiv (evalSingleTpBackend tp gb mu) (evalTP tp g nu) := by
  have hcongr : ∀ t, OptKEq (tpMatch tp t mu) (tpMatch tp t nu) :=
    fun t => tpMatch_congr tp rfl h
  have e1 : evalTP tp g nu =
      (g.filter (boundMatches (patternBoundFor tp mu))).filterMap (fun t => tpMatch tp t nu) := by
    unfold evalTP
    refine (filterMap_filter_of _ _ g ?_).symm
    intro t _ hs
    rw [← (hcongr t).isSome_eq] at hs
    obtain ⟨mu', hm⟩ := Option.isSome_iff_exists.mp hs
    exact tpMatch_boundMatches hm
  rw [e1]
  have hkeys : ((backendSearch gb (patternBoundFor tp mu)).map Triple.key).Perm
      ((g.filter (boundMatches (patternBoundFor tp mu))).map Triple.key) := by
    have hnF : ((g.filter (boundMatches (patternBoundFor tp mu))).map Triple.key).Nodup :=
      ((List.filter_sublist (p := boundMatches (patternBoundFor tp mu)) (l := g)).map Triple.key).nodup hg
    refine (List.perm_ext_iff_of_nodup (backendSearch_nodupKeys hx _) hnF).mpr ?_
    intro k
    constructor
    · intro hk
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
      obtain ⟨hGu, hbu⟩ := (backendSearch_exact hx _ u).mp ⟨u, hu, rfl⟩
      obtain ⟨w, hw, hwu⟩ := (hG u).mp hGu
      have hbw : boundMatches (patternBoundFor tp mu) w = true := by
        rw [boundMatches_congr _ w u ((Triple.eqb_iff_key w u).mpr hwu)]; exact hbu
      exact List.mem_map.mpr ⟨w, List.mem_filter.mpr ⟨hw, hbw⟩, hwu⟩
    · intro hk
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
      obtain ⟨hwg, hbw⟩ := List.mem_filter.mp hw
      obtain ⟨u, hu, huw⟩ := (backendSearch_exact hx _ w).mpr ⟨(hG w).mpr ⟨w, hwg, rfl⟩, hbw⟩
      exact List.mem_map.mpr ⟨u, hu, huw⟩
  obtain ⟨C, pc, wc⟩ := perm_map_lift Triple.key _ _ hkeys
  refine ⟨C.filterMap (fun t => tpMatch tp t mu), pc.filterMap _, ?_⟩
  exact pw_filterMap2 (Rel := fun a b => a.key = b.key) (fun t => tpMatch tp t mu)
    (fun t => tpMatch tp t nu) (fun a b hab => tpMatch_congr tp hab h) wc

/-! ## 8. The whole basic graph pattern through the backend -/

/-- The planner's choice is a permutation of the patterns. -/
theorem chooseBest_perm' (gb : GraphBackend) (mu : Binding) :
    ∀ (patterns : Bgp) (tp : TriplePattern) (rest : Bgp),
      chooseBestTpBackend gb mu patterns = some (tp, rest) → (tp :: rest).Perm patterns
  | [], _, _ => by intro h; exact absurd h (by simp [chooseBestTpBackend])
  | p :: ps, tp, rest => by
      intro h
      simp only [chooseBestTpBackend] at h
      cases hb : chooseBestTpBackend gb mu ps with
      | none =>
          rw [hb] at h; dsimp only at h
          have hnil : ps = [] := (chooseBest_none_iff_nil gb mu ps).mp hb
          subst hnil
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2; exact List.Perm.refl _
      | some pair =>
          obtain ⟨best, remaining⟩ := pair
          rw [hb] at h; dsimp only at h
          have ih := chooseBest_perm' gb mu ps best remaining hb
          by_cases hc : estimateTpBackend p gb mu <= estimateTpBackend best gb mu
          · rw [if_pos hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h1; subst h2; exact List.Perm.refl _
          · rw [if_neg hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h1; subst h2
            exact (List.Perm.swap p best remaining).trans (ih.cons p)

theorem evalBgpConcatMapAcc_eq (rest : Bgp) (gb : GraphBackend) (n : Nat) :
    ∀ (rows acc : SolutionSeq), evalBgpConcatMapAcc rest gb n rows acc =
      (rows.flatMap fun mu' => evalBgpFromMuFuel rest gb mu' n).reverse ++ acc
  | [], acc => by simp [evalBgpConcatMapAcc]
  | mu' :: more, acc => by
    rw [evalBgpConcatMapAcc, evalBgpConcatMapAcc_eq rest gb n more]
    simp [List.reverseAux_eq, List.flatMap_cons, List.reverse_append]

theorem evalBgpFromMuFuel_kequiv {gb : GraphBackend} {G : Triple → Prop} {g : Graph}
    (hx : BackendExact gb G) (hg : g.KeyNodup) (hG : ∀ t, G t ↔ KeyMem g t) :
    ∀ (n : Nat) (ps : Bgp) (mu nu : Binding), ps.length < n → BindKEq mu nu →
      SolKEquiv (evalBgpFromMuFuel ps gb mu n) (evalBgpFrom g ps nu)
  | 0, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | n + 1, [], mu, nu, _, h => by
    rw [evalBgpFromMuFuel_nil]; exact SolKEquiv.of_pw (.cons h .nil)
  | n + 1, p :: ps, mu, nu, hl, h => by
    cases hc : chooseBestTpBackend gb mu (p :: ps) with
    | none => exact absurd ((chooseBest_none_iff_nil gb mu _).mp hc) (by simp)
    | some pr =>
      obtain ⟨tp, rest⟩ := pr
      have hperm := chooseBest_perm' gb mu (p :: ps) tp rest hc
      have hlen : rest.length < n := by
        have := hperm.length_eq
        simp only [List.length_cons] at this hl
        omega
      have e : evalBgpFromMuFuel (p :: ps) gb mu (n + 1) =
          (evalSingleTpBackend tp gb mu).flatMap (fun mu' => evalBgpFromMuFuel rest gb mu' n) := by
        simp only [evalBgpFromMuFuel, hc]
        rw [evalBgpConcatMapAcc_eq]
        simp
      rw [e]
      refine SolKEquiv.trans ?_ (evalBgpFrom_perm g hperm nu nu (BindKEq.refl nu))
      show SolKEquiv _ ((evalTP tp g nu).flatMap (evalBgpFrom g rest))
      exact solK_flatMap _ _ (fun a b hab => evalBgpFromMuFuel_kequiv hx hg hG n rest a b hlen hab)
        (evalSingleTpBackend_kequiv hx hg hG tp h)

/-- **The backend BGP evaluator against SPARQL 1.1 section 18.3.** For a
    backend whose law holds for the graph `G`, and a list `g` that denotes
    `G` with each triple once up to RDF term equality, the backend's
    solutions of the basic graph pattern `b` are the reference's
    (`evalBgp b g`), as a multiset up to order and RDF term equality. -/
theorem evalBgpBackend_kequiv {gb : GraphBackend} {G : Triple → Prop} {g : Graph}
    (hx : BackendExact gb G) (hg : g.KeyNodup) (hG : ∀ t, G t ↔ KeyMem g t) (b : Bgp) :
    SolKEquiv (evalBgpBackend b gb) (evalBgp b g) :=
  evalBgpFromMuFuel_kequiv hx hg hG _ b _ _ (Nat.lt_succ_self _) (BindKEq.refl _)

/-- Two backends with one denotation give one answer, up to order and RDF
    term equality. -/
theorem evalBgpBackend_kequiv_of_den {gb gb' : GraphBackend} {G : Triple → Prop} {g : Graph}
    (hx : BackendExact gb G) (hx' : BackendExact gb' G) (hg : g.KeyNodup)
    (hG : ∀ t, G t ↔ KeyMem g t) (b : Bgp) :
    SolKEquiv (evalBgpBackend b gb) (evalBgpBackend b gb') :=
  (evalBgpBackend_kequiv hx hg hG b).trans (evalBgpBackend_kequiv hx' hg hG b).symm

/-! ## 9. Terms that are their own join key: the structural relation -/

/-- Every value of the row is its own join key. -/
def BindFixed (mu : Binding) : Prop := ∀ v e, mu.lookup v = some e → e.joinKey = e

/-- Every row a backend search returns has an object that is its own join
    key. -/
def BackendFixed (gb : GraphBackend) : Prop :=
  ∀ b u, u ∈ backendSearch gb b → u.o.joinKey = u.o

theorem bindFixed_empty : BindFixed Binding.empty := fun _ _ h => by
  simp [Binding.empty, Binding.lookup] at h

/-- Every backend is `BackendFixed`: every term is its own join key
    (`Term.joinKey_eq_self`). -/
theorem backendFixed (gb : GraphBackend) : BackendFixed gb :=
  fun _ u _ => Term.joinKey_eq_self u.o

theorem bindFixed_bind {mu : Binding} {x : Term} (v : VarName) (hm : BindFixed mu)
    (hx : x.joinKey = x) : BindFixed (mu.bind v x) := by
  intro w e h
  by_cases hw : v = w
  · subst hw; rw [lookup_bind_self] at h; cases h; exact hx
  · rw [lookup_bind_ne _ _ hw] at h; exact hm w e h

theorem slotMatch_fixed {s : TSlot} {x : Term} {mu mu' : Binding} (h : slotMatch s x mu = some mu')
    (hm : BindFixed mu) (hx : x.joinKey = x) : BindFixed mu' := by
  rcases slot_var_or_const s with ⟨v, rfl⟩ | hc
  · simp only [slotMatch] at h
    cases hv : mu.lookup v with
    | some e => rw [hv] at h; obtain ⟨-, rfl⟩ := ite_some' h; exact hm
    | none => rw [hv] at h; cases h; exact bindFixed_bind v hm hx
  · rw [hc] at h; obtain ⟨-, rfl⟩ := ite_some' h; exact hm

theorem matchSlots_fixed : ∀ (S : List (TSlot × Term)) {mu mu' : Binding},
    matchSlots S mu = some mu' → (∀ q ∈ S, q.2.joinKey = q.2) → BindFixed mu → BindFixed mu'
  | [], _, _, h, _, hm => by cases h; exact hm
  | (s, x) :: rest, mu, mu', h, hS, hm => by
    simp only [matchSlots] at h
    cases h1 : slotMatch s x mu with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1] at h
      exact matchSlots_fixed rest h (fun q hq => hS q (List.mem_cons_of_mem _ hq))
        (slotMatch_fixed h1 hm (hS (s, x) List.mem_cons_self))

theorem slotsT_fixed : ∀ (pt : PatternTerm) {x : Term}, x.joinKey = x →
    ∀ q ∈ slotsT pt x, q.2.joinKey = q.2
  | .var _, _, hx, q, hq => by simp [slotsT] at hq; subst hq; exact hx
  | .iri _, _, hx, q, hq => by simp [slotsT] at hq; subst hq; exact hx
  | .bnode _, _, hx, q, hq => by simp [slotsT] at hq; subst hq; exact hx
  | .literal _, _, hx, q, hq => by simp [slotsT] at hq; subst hq; exact hx
  | .tripleTerm ps pp po, x, hx, q, hq => by
    cases x with
    | tripleTerm s p o =>
      simp only [Term.joinKey, Term.tripleTerm.injEq, true_and] at hx
      simp only [slotsT, List.mem_append] at hq
      rcases hq with (hq | hq) | hq
      · exact slotsT_fixed ps (by cases s <;> rfl) q hq
      · exact slotsT_fixed pp rfl q hq
      · exact slotsT_fixed po hx q hq
    | iri _ => simp [slotsT] at hq; subst hq; exact hx
    | bnode _ => simp [slotsT] at hq; subst hq; exact hx
    | literal _ => simp [slotsT] at hq; subst hq; exact hx

theorem tpMatch_fixed {tp : TriplePattern} {t : Triple} {mu mu' : Binding}
    (h : tpMatch tp t mu = some mu') (ht : t.o.joinKey = t.o) (hm : BindFixed mu) : BindFixed mu' := by
  rw [tpMatch_slots] at h
  refine matchSlots_fixed _ h ?_ hm
  intro q hq
  simp only [tpSlots, List.mem_append] at hq
  rcases hq with (hq | hq) | hq
  · cases hs : tp.s <;> rw [hs] at hq <;> simp [slotsS] at hq <;> subst hq <;> cases t.s <;> rfl
  · exact slotsT_fixed tp.p rfl q hq
  · exact slotsT_fixed tp.o ht q hq

theorem evalBgpFrom_fixed {g : Graph} (hg : GraphFixed g) :
    ∀ (ps : Bgp) {mu : Binding}, BindFixed mu → ∀ nu ∈ evalBgpFrom g ps mu, BindFixed nu
  | [], _, hm, nu, hn => by simp [evalBgpFrom] at hn; subst hn; exact hm
  | tp :: rest, mu, hm, nu, hn => by
    simp only [evalBgpFrom, List.mem_flatMap, evalTP, List.mem_filterMap] at hn
    obtain ⟨m1, ⟨t, ht, h1⟩, hn⟩ := hn
    exact evalBgpFrom_fixed hg rest (tpMatch_fixed h1 (hg t ht) hm) nu hn

theorem evalBgpFromMuFuel_fixed {gb : GraphBackend} (hb : BackendFixed gb) :
    ∀ (n : Nat) (ps : Bgp) {mu : Binding}, BindFixed mu → ∀ nu ∈ evalBgpFromMuFuel ps gb mu n, BindFixed nu
  | 0, _, _, hm, nu, hn => by simp [evalBgpFromMuFuel] at hn; subst hn; exact hm
  | n + 1, [], _, hm, nu, hn => by
    rw [evalBgpFromMuFuel_nil] at hn; simp at hn; subst hn; exact hm
  | n + 1, p :: ps, mu, hm, nu, hn => by
    cases hc : chooseBestTpBackend gb mu (p :: ps) with
    | none => exact absurd ((chooseBest_none_iff_nil gb mu _).mp hc) (by simp)
    | some pr =>
      obtain ⟨tp, rest⟩ := pr
      have e : evalBgpFromMuFuel (p :: ps) gb mu (n + 1) =
          (evalSingleTpBackend tp gb mu).flatMap (fun mu' => evalBgpFromMuFuel rest gb mu' n) := by
        simp only [evalBgpFromMuFuel, hc]
        rw [evalBgpConcatMapAcc_eq]
        simp
      rw [e] at hn
      simp only [List.mem_flatMap, evalSingleTpBackend, List.mem_filterMap] at hn
      obtain ⟨m1, ⟨t, ht, h1⟩, hn⟩ := hn
      exact evalBgpFromMuFuel_fixed hb n rest (tpMatch_fixed h1 (hb _ t ht) hm) nu hn

theorem bindEq_of_fixed {mu nu : Binding} (h : BindKEq mu nu) (hm : BindFixed mu) (hn : BindFixed nu) :
    BindEq mu nu := by
  intro v
  have hv := h v
  cases h1 : mu.lookup v <;> cases h2 : nu.lookup v <;> rw [h1, h2] at hv <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hv
  all_goals first
    | rfl
    | (rename_i e e'; rw [← hm v e h1, ← hn v e' h2, hv])

theorem pw_imp_mem {α : Type} {R S : α → α → Prop} :
    ∀ {A B : List α}, Pw R A B → (∀ a ∈ A, ∀ b ∈ B, R a b → S a b) → Pw S A B
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hS =>
    .cons (hS _ List.mem_cons_self _ List.mem_cons_self h)
      (pw_imp_mem t (fun a ha b hb => hS a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)))

/-- Up to RDF term equality is structural when every value is its own join
    key. -/
theorem solEquiv_of_fixed {A B : SolutionSeq} (h : SolKEquiv A B)
    (hA : ∀ mu ∈ A, BindFixed mu) (hB : ∀ mu ∈ B, BindFixed mu) : SolEquiv A B := by
  obtain ⟨C, p, w⟩ := h
  exact ⟨C, p, pw_imp_mem w (fun a ha b hb hab =>
    bindEq_of_fixed hab (hA a (p.mem_iff.mpr ha)) (hB b hb))⟩

/-- **The backend BGP evaluator, structurally.** The backend's solutions of
    `b` are the reference's as a multiset of solution mappings (`SolEquiv`:
    a permutation, then the same lookup of every variable). Every object of
    the graph and of the backend's rows is its own join key (`graphFixed`,
    `backendFixed`), so the premises `GraphFixed g` and `BackendFixed gb`
    that this theorem had until 2026-10-24 are gone
    (https://github.com/danbri/factoidal/issues/1001). -/
theorem evalBgpBackend_solEquiv {gb : GraphBackend} {G : Triple → Prop} {g : Graph}
    (hx : BackendExact gb G) (hg : g.KeyNodup) (hG : ∀ t, G t ↔ KeyMem g t) (b : Bgp) :
    SolEquiv (evalBgpBackend b gb) (evalBgp b g) :=
  solEquiv_of_fixed (evalBgpBackend_kequiv hx hg hG b)
    (fun mu hm => evalBgpFromMuFuel_fixed (backendFixed gb) _ b bindFixed_empty mu hm)
    (fun mu hm => evalBgpFrom_fixed (graphFixed g) b bindFixed_empty mu hm)

/-- The backend's answer to a basic graph pattern with no `text:query`
    pattern is an answer `Allowed` admits. -/
theorem evalBgpBackend_allowed (env : EvalEnv) (ds : Dataset) {gb : GraphBackend} {a : Graph}
    (hx : BackendExact gb (KeyMem a)) (ha : a.KeyNodup)
    (b : Bgp) (hf : bgpHasFulltext b = false) :
    Allowed env ds (.bgp b) a (evalBgpBackend b gb) := by
  have h0 := Allowed.bgp (env := env) (ds := ds) b a
  rw [Storage.Sbm11.IdLeaf.refSol_bgp env ds b a hf] at h0
  exact .equiv h0 (SolEquiv.symm (evalBgpBackend_solEquiv hx ha (fun _ => Iff.rfl) b))

/-! ## 10. FILTER, OPTIONAL, JOIN, UNION, MINUS, GRAPH, VALUES and the empty
pattern on the backend path -/

mutual
/-- A `backendLocal` expression has no EXISTS in it. -/
theorem existsFree_of_backendLocal : (e : Expr) → e.backendLocal = true → e.existsFree = true
  | .var _, _ => rfl
  | .iri _, _ => rfl
  | .lit _, _ => rfl
  | .boolLit _, _ => rfl
  | .numericLit _, _ => rfl
  | .decimalLit _, _ => rfl
  | .doubleLit _, _ => rfl
  | .bound _, _ => rfl
  | .unaryMinus a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .unaryPlus a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .not a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .isIri a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .isBlank a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .isLiteral a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .isNumeric a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .str a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .lang a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .datatype a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .hasLang a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .hasLangDir a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .langDir a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .strLen a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .uCase a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .lCase a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .encodeForUri a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .abs a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .round a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .ceil a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .floor a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .year a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .month a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .day a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .hours a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .minutes a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .seconds a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .timezone a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .tz a, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFree_of_backendLocal a h]
  | .arith _ a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .compare _ a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .and a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .or a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .sameTerm a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strDt a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strLang a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strStarts a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strEnds a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .contains a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strBefore a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strAfter a b, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .strLangDir a b c, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1.1, existsFree_of_backendLocal b h.1.2,
      existsFree_of_backendLocal c h.2, Bool.and_self]
  | .cond a b c, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1.1, existsFree_of_backendLocal b h.1.2,
      existsFree_of_backendLocal c h.2, Bool.and_self]
  | .substr a b none, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFree_of_backendLocal b h.2, Bool.and_self]
  | .substr a b (some c), h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1.1, existsFree_of_backendLocal b h.1.2,
      existsFree_of_backendLocal c h.2, Bool.and_self]
  | .coalesce es, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFreeList_of_backendLocal es h]
  | .concat es, h => by
    simp only [Expr.backendLocal] at h; simp only [Expr.existsFree, existsFreeList_of_backendLocal es h]
  | .inList a es, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFreeList_of_backendLocal es h.2,
      Bool.and_self]
  | .notInList a es, h => by
    simp only [Expr.backendLocal, Bool.and_eq_true] at h
    simp only [Expr.existsFree, existsFree_of_backendLocal a h.1, existsFreeList_of_backendLocal es h.2,
      Bool.and_self]
  | .now, h => by simp [Expr.backendLocal] at h
  | .iriFn _, h => by simp [Expr.backendLocal] at h
  | .md5 _, h => by simp [Expr.backendLocal] at h
  | .sha1 _, h => by simp [Expr.backendLocal] at h
  | .sha256 _, h => by simp [Expr.backendLocal] at h
  | .sha384 _, h => by simp [Expr.backendLocal] at h
  | .sha512 _, h => by simp [Expr.backendLocal] at h
  | .replace _ _ _ _, h => by simp [Expr.backendLocal] at h
  | .regex _ _ _, h => by simp [Expr.backendLocal] at h
  | .existsPat _, h => by simp [Expr.backendLocal] at h
  | .notExistsPat _, h => by simp [Expr.backendLocal] at h
  | .aggregate _ _ _, h => by simp [Expr.backendLocal] at h
  | .functionCall _ _, h => by simp [Expr.backendLocal] at h
  | .tripleTerm _ _ _, h => by simp [Expr.backendLocal] at h
  | .ttSubject _, h => by simp [Expr.backendLocal] at h
  | .ttPredicate _, h => by simp [Expr.backendLocal] at h
  | .ttObject _, h => by simp [Expr.backendLocal] at h
  | .isTriple _, h => by simp [Expr.backendLocal] at h

theorem existsFreeList_of_backendLocal : (es : List Expr) → Expr.backendLocalList es = true →
    Expr.existsFreeList es = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.backendLocalList, Bool.and_eq_true] at h
    simp only [Expr.existsFreeList, existsFree_of_backendLocal e h.1, existsFreeList_of_backendLocal es h.2,
      Bool.and_self]
end


/-- A `backendLocal` condition is the reference's condition. -/
theorem filterFn_local (env : EvalEnv) {c : Expr} (hc : c.backendLocal = true) (a : Graph) :
    filterFn env c a = fun row => ebvOrFalse (Expr.evalIn env row c) := by
  funext row
  simp only [filterFn]
  rw [Storage.Sbm11.IdPostTheorems.substituteExistentials_existsFree env a _ c
    (existsFree_of_backendLocal c hc)]
  rw [Storage.Sbm11.ExprLocalTheorems.evalIn_bindEq env _ row
    (Storage.Sbm11.ExprLocalTheorems.lookup_merge_empty row) c]

/-- A graph backend and the list it reads: the law of the backend for the
    list's triples, and each triple once up to RDF term equality. -/
structure GraphRel (gb : GraphBackend) (a : Graph) : Prop where
  exact : BackendExact gb (KeyMem a)
  keyNodup : a.KeyNodup

/-- The named backends of a dataset record and the named graphs of a dataset,
    pair for pair: an IRI name, the backend's name its string, and the
    backend reads the graph. -/
inductive NamedRel : List NamedGraphBackend → List NamedGraph → Prop
  | nil : NamedRel [] []
  | cons {ngb : NamedGraphBackend} {ng : NamedGraph} {rest : List NamedGraphBackend}
      {rest' : List NamedGraph} (j : WfIri) :
      ng.name = .iri j → ngb.name = j.val → GraphRel ngb.backend ng.graph →
      NamedRel rest rest' → NamedRel (ngb :: rest) (ng :: rest')

theorem wfIriOf_val (j : WfIri) : wfIriOf? j.val = some j := by
  simp [wfIriOf?, j.property]

theorem lookupNamedIri_wf (ds : Dataset) (i : WfIri) :
    ds.lookupNamedIri i.val = (ds.named.find? (fun ng => ng.name == .iri i)).map (·.graph) := by
  unfold Dataset.lookupNamedIri Dataset.lookupNamed
  rw [dif_pos i.property]
  cases ds.named.find? (fun ng => ng.name == .iri i) <;> rfl

theorem lookup_rel (i : WfIri) : ∀ {L : List NamedGraphBackend} {L' : List NamedGraph}, NamedRel L L' →
    (lookupNamedBackend i.val L = none ∧ (L'.find? (fun ng => ng.name == .iri i)).map (·.graph) = none) ∨
    ∃ gb g, lookupNamedBackend i.val L = some gb ∧
      (L'.find? (fun ng => ng.name == .iri i)).map (·.graph) = some g ∧ GraphRel gb g
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | ngb :: rest, ng :: rest', .cons j hn hb hr t => by
    simp only [lookupNamedBackend, List.find?_cons, hn, hb]
    by_cases hji : j = i
    · subst hji
      exact .inr ⟨ngb.backend, ng.graph, by simp, by simp, hr⟩
    · have h1 : (j.val == i.val) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun e => hji (Subtype.ext e)
      have h2 : (Subject.iri j == Subject.iri i) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, Subject.iri.injEq]
        exact hji
      simp only [h1, h2]
      exact lookup_rel i t

theorem lookupNamedBackend_of_mem : ∀ {L : List NamedGraphBackend}, (L.map (·.name)).Nodup →
    ∀ {ngb : NamedGraphBackend}, ngb ∈ L → lookupNamedBackend ngb.name L = some ngb.backend
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: L, hnd, ngb, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [lookupNamedBackend]
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · have hne : x.name ≠ ngb.name := fun e => hnd.1 (e ▸ List.mem_map_of_mem hm)
      rw [if_neg (by simpa using hne)]
      exact lookupNamedBackend_of_mem hnd.2 hm

theorem namedRel_mem : ∀ {L : List NamedGraphBackend} {L' : List NamedGraph}, NamedRel L L' →
    ∀ {ng : NamedGraph}, ng ∈ L' → ∃ ngb ∈ L, ∃ j : WfIri, ng.name = .iri j ∧ ngb.name = j.val ∧
      GraphRel ngb.backend ng.graph
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | ngb :: _, _ :: _, .cons j hn hb hr t, ng, h => by
    rcases List.mem_cons.mp h with rfl | hm
    · exact ⟨ngb, List.mem_cons_self, j, hn, hb, hr⟩
    · obtain ⟨x, hx, j', e1, e2, e3⟩ := namedRel_mem t hm
      exact ⟨x, List.mem_cons_of_mem _ hx, j', e1, e2, e3⟩

/-- The backend of a named graph in a dataset record, by the graph's name. -/
def backendFor (L : List NamedGraphBackend) (n : Subject) : GraphBackend :=
  (match n with
   | .iri j => lookupNamedBackend j.val L
   | .bnode _ => none).getD (.list [])

theorem graphVar_eq (env : EvalEnv) (dsb : DatasetBackend) (q : QueryPattern) (v : VarName) :
    ∀ {L : List NamedGraphBackend} {L' : List NamedGraph}, NamedRel L L' →
      (∀ ngb ∈ L, lookupNamedBackend ngb.name dsb.named = some ngb.backend) →
      L.flatMap (fun ngb =>
        match wfIriOf? ngb.name with
        | none => []
        | some i => (evalPatternBackend env dsb q ngb.backend).filterMap
            (fun mu => mu.bindIfCompatible v (.iri i)))
      = L'.flatMap (fun ng => (evalPatternBackend env dsb q (backendFor dsb.named ng.name)).filterMap
          (Binding.bindIfCompatible v ng.name.toTerm))
  | _, _, .nil, _ => rfl
  | ngb :: rest, ng :: rest', .cons j hn hb _ t, hlk => by
    simp only [List.flatMap_cons]
    have hbk : backendFor dsb.named ng.name = ngb.backend := by
      simp only [backendFor, hn]
      rw [← hb, hlk ngb List.mem_cons_self]
      rfl
    have head : (match wfIriOf? ngb.name with
        | none => []
        | some i => (evalPatternBackend env dsb q ngb.backend).filterMap
            (fun mu => mu.bindIfCompatible v (.iri i))) =
        (evalPatternBackend env dsb q (backendFor dsb.named ng.name)).filterMap
          (Binding.bindIfCompatible v ng.name.toTerm) := by
      rw [hb, wfIriOf_val, hbk, hn]
      rfl
    rw [head, graphVar_eq env dsb q v t (fun x hx => hlk x (List.mem_cons_of_mem _ hx))]

/-- The patterns the theorem covers: those whose every operator is a
    backend-native arm of `evalPatternBackend` (BGP with no `text:query`
    pattern, FILTER and OPTIONAL with a `backendLocal` condition, JOIN,
    UNION, MINUS, GRAPH with an IRI or a variable, VALUES, the empty
    pattern). -/
def NativeFrag : QueryPattern → Prop
  | .bgp b => bgpHasFulltext b = false
  | .filter c q => c.backendLocal = true ∧ NativeFrag q
  | .leftJoin l r c => c.backendLocal = true ∧ NativeFrag l ∧ NativeFrag r
  | .join l r => NativeFrag l ∧ NativeFrag r
  | .union l r => NativeFrag l ∧ NativeFrag r
  | .minus l r => NativeFrag l ∧ NativeFrag r
  | .graph t q =>
      match t with
      | .iri _ => NativeFrag q
      | .var _ => NativeFrag q
      | _ => False
  | .empty => True
  | .values _ _ => True
  | _ => False

/-- **The backend evaluator's WHERE answer is an answer SPARQL 1.1 allows**,
    for every pattern of `NativeFrag`: over a graph backend that reads the
    active graph `a`, and named backends that read the named graphs of `ds`
    pair for pair with distinct names. -/
theorem evalPatternBackend_allowed (env : EvalEnv) (dsb : DatasetBackend) (ds : Dataset)
    (hn : NamedRel dsb.named ds.named) (hnd : (dsb.named.map (·.name)).Nodup) :
    ∀ (p : QueryPattern), NativeFrag p → ∀ (gb : GraphBackend) (a : Graph), GraphRel gb a →
      Allowed env ds p a (evalPatternBackend env dsb p gb)
  | .bgp b, hp, gb, a, hr => by
    rw [evalPatternBackend_bgp_native]
    exact evalBgpBackend_allowed env ds hr.exact hr.keyNodup b hp
  | .filter c q, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.filter c q) gb =
        (evalPatternBackend env dsb q gb).filter (fun row => ebvOrFalse (Expr.evalIn env row c)) := by
      simp [evalPatternBackend, hp.1]
    rw [e, ← filterFn_local env hp.1 a]
    exact .filter (evalPatternBackend_allowed env dsb ds hn hnd q hp.2 gb a hr)
  | .leftJoin l r c, hp, gb, a, hr => by
    rw [evalPatternBackend_leftJoin_spec env dsb l r c gb hp.1, ← filterFn_local env hp.1 a]
    exact .leftJoin (evalPatternBackend_allowed env dsb ds hn hnd l hp.2.1 gb a hr)
      (evalPatternBackend_allowed env dsb ds hn hnd r hp.2.2 gb a hr)
  | .join l r, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.join l r) gb =
        SPARQL.hashJoin (evalPatternBackend env dsb l gb) (evalPatternBackend env dsb r gb) := by
      simp [evalPatternBackend]
    rw [e, SPARQL.hashJoin_eq_join]
    exact .join (evalPatternBackend_allowed env dsb ds hn hnd l hp.1 gb a hr)
      (evalPatternBackend_allowed env dsb ds hn hnd r hp.2 gb a hr)
  | .union l r, hp, gb, a, hr => by
    rw [evalPatternBackend_union_native]
    exact .union (evalPatternBackend_allowed env dsb ds hn hnd l hp.1 gb a hr)
      (evalPatternBackend_allowed env dsb ds hn hnd r hp.2 gb a hr)
  | .minus l r, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.minus l r) gb =
        SPARQL.hashMinus (evalPatternBackend env dsb l gb) (evalPatternBackend env dsb r gb) := by
      simp [evalPatternBackend]
    rw [e, SPARQL.hashMinus_eq_minus]
    exact .minus (evalPatternBackend_allowed env dsb ds hn hnd l hp.1 gb a hr)
      (evalPatternBackend_allowed env dsb ds hn hnd r hp.2 gb a hr)
  | .graph (.iri i) q, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.graph (.iri i) q) gb =
        match lookupNamedBackend i.val dsb.named with
        | some g => evalPatternBackend env dsb q g
        | none => [] := rfl
    rw [e]
    rcases lookup_rel i hn with ⟨h1, h2⟩ | ⟨gb', g, h1, h2, hr'⟩
    · rw [h1]
      exact .graphIriNone (by rw [lookupNamedIri_wf]; exact h2)
    · rw [h1]
      exact .graphIri (by rw [lookupNamedIri_wf]; exact h2)
        (evalPatternBackend_allowed env dsb ds hn hnd q hp gb' g hr')
  | .graph (.var v) q, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.graph (.var v) q) gb =
        dsb.named.flatMap (fun ngb =>
          match wfIriOf? ngb.name with
          | none => []
          | some i => (evalPatternBackend env dsb q ngb.backend).filterMap
              (fun mu => mu.bindIfCompatible v (.iri i))) := rfl
    rw [e, graphVar_eq env dsb q v hn (fun x hx => lookupNamedBackend_of_mem hnd hx)]
    refine .graphVar (fun ng => evalPatternBackend env dsb q (backendFor dsb.named ng.name)) ?_
    intro ng hng
    obtain ⟨ngb, hngb, j, e1, e2, hr'⟩ := namedRel_mem hn hng
    have hbk : backendFor dsb.named ng.name = ngb.backend := by
      simp only [backendFor, e1]
      rw [← e2, lookupNamedBackend_of_mem hnd hngb]
      rfl
    rw [hbk]
    exact evalPatternBackend_allowed env dsb ds hn hnd q hp ngb.backend ng.graph hr'
  | .empty, _, gb, a, _ => by
    rw [evalPatternBackend_empty]
    exact .empty a
  | .values vs rows, _, gb, a, _ => by
    rw [evalPatternBackend_values_native]
    exact .values vs rows a

/-! ## 11. The dataset record of the reference fallback

`indexedDatasetBackend d` is the record `runSelectQueryBackendDataset` runs
on in the reference fallback of `l4sbm11 query`
(`Storage/SelectedDataset.lean`, `referenceSelect`). -/

/-- A row of a search of the in-memory index of `g` is a triple of `g`. -/
theorem mem_backendSearch_indexed {g : Graph} {b : PatternBound} {u : Triple}
    (hu : u ∈ backendSearch (indexedGraphBackend g) b) : u ∈ g := by
  have hw := OWL.RL.Index.Wf.ofGraph g
  simp only [backendSearch, indexedGraphBackend, capsOfBackend, capsOfIndexed, igSearch,
    tripleMatchesBound] at hu
  have hu' := (List.mem_filter.mp hu).1
  revert hu'
  rcases b with ⟨s, p, o⟩
  cases s <;> cases p <;> cases o <;> simp only [] <;> (try split) <;>
    simp only [hw.withSubjPred_eq, hw.withPredObj_eq, hw.withPred_eq, hw.withSubj_eq,
      hw.withObj_eq, OWL.RL.Index.toGraph, hw.all, OWL.RL.withSubjPred, OWL.RL.withPredObj,
      OWL.RL.withPred, OWL.RL.withSubj, OWL.RL.withObj, List.mem_filter] <;>
    intro h <;> first | exact h | exact h.1

theorem graphRel_indexed {g : Graph} (hg : g.KeyNodup) :
    GraphRel (indexedGraphBackend g) g where
  exact := ⟨g, OWL.RL.Index.Wf.ofGraph g, hg, fun _ => Iff.rfl⟩
  keyNodup := hg

theorem namedRel_indexed : ∀ (l : List NamedGraph), (∀ ng ∈ l, ng.graph.KeyNodup) →
    (∀ ng ∈ l, ∃ j, ng.name = .iri j) →
    NamedRel (l.map (fun ng => (⟨ngKey ng, indexedGraphBackend ng.graph⟩ : NamedGraphBackend))) l
  | [], _, _ => .nil
  | ng :: rest, hs, hi => by
    obtain ⟨j, hj⟩ := hi ng List.mem_cons_self
    refine .cons j hj (by simp [ngKey, hj]) (graphRel_indexed (hs ng List.mem_cons_self)) ?_
    exact namedRel_indexed rest (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (fun x hx => hi x (List.mem_cons_of_mem _ hx))

theorem ngKey_nodup : ∀ (l : List NamedGraph), (l.map (·.name)).Nodup →
    (∀ ng ∈ l, ∃ j, ng.name = .iri j) → (l.map ngKey).Nodup
  | [], _, _ => List.nodup_nil
  | ng :: rest, hn, hi => by
    rw [List.map_cons, List.nodup_cons] at hn ⊢
    refine ⟨fun hm => ?_, ngKey_nodup rest hn.2 (fun x hx => hi x (List.mem_cons_of_mem _ hx))⟩
    obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
    obtain ⟨j, hj⟩ := hi ng List.mem_cons_self
    obtain ⟨k, hk⟩ := hi x (List.mem_cons_of_mem _ hx)
    simp only [ngKey, hj, hk] at e
    have : k = j := Subtype.ext e
    subst this
    exact hn.1 (List.mem_map.mpr ⟨x, hx, by rw [hk, hj]⟩)

theorem iris_of_namesAreIris {d : Dataset} (h : Storage.QuadDataset.namesAreIris d = true) :
    ∀ ng ∈ d.named, ∃ j, ng.name = .iri j := by
  intro ng hng
  have := List.all_eq_true.mp h ng hng
  revert this
  cases ng.name with
  | iri j => intro _; exact ⟨j, rfl⟩
  | bnode _ => intro h; cases h

/-- **The reference fallback's WHERE answer is an answer SPARQL 1.1
    allows.** Over the in-memory dataset record of a dataset that is a set
    with IRI graph names, `evalPatternBackend` answers every pattern of
    `NativeFrag` with an answer `Allowed` admits, in the default graph. Since
    2026-10-24 there is no premise on the language tags: every dataset is
    `GraphFixed` (`graphFixed`, https://github.com/danbri/factoidal/issues/1001). -/
theorem indexedWhere_allowed (env : EvalEnv) (d : Dataset) (hset : d.IsSet)
    (hiri : Storage.QuadDataset.namesAreIris d = true) (p : QueryPattern) (hp : NativeFrag p) :
    Allowed env d p d.default
      (evalPatternBackend env (indexedDatasetBackend d) p (indexedDatasetBackend d).default) := by
  have hi := iris_of_namesAreIris hiri
  have hn : NamedRel (indexedDatasetBackend d).named d.named := by
    rw [indexedDatasetBackend_named]
    exact namedRel_indexed d.named hset.graphs hi
  have hnd : ((indexedDatasetBackend d).named.map (·.name)).Nodup := by
    rw [indexedDatasetBackend_named, List.map_map]
    exact ngKey_nodup d.named hset.names hi
  exact evalPatternBackend_allowed env _ d hn hnd p hp _ _ (graphRel_indexed hset.default)

/-- Every dataset, parsed by any reader or built by any constructor,
    satisfies the premises on language tags that `indexedWhere_allowed`
    carried until 2026-10-24 (https://github.com/danbri/factoidal/issues/1001). -/
theorem datasetFixed (D : Dataset) : GraphFixed D.default ∧ ∀ ng ∈ D.named, GraphFixed ng.graph :=
  ⟨graphFixed _, fun ng _ => graphFixed ng.graph⟩

/-! ## 12. The stages -/

/-- The contract of a backend's BGP answer: for every graph the backend's law
    holds for, and that the list `g` denotes with each triple once, the
    answer is the reference's over `g` up to order and RDF term equality. -/
def BackendBgpContract (b : Bgp) (g : Graph) (gb : GraphBackend) (r : SolutionSeq) : Prop :=
  ∀ G : Triple → Prop, BackendExact gb G → g.KeyNodup → (∀ t, G t ↔ KeyMem g t) →
    SolKEquiv r (evalBgp b g)

/-- A graph backend → the backend's solutions of the basic graph pattern `b`. -/
def backendBgpStage (b : Bgp) (g : Graph) :
    L4Factoidal.Dataflow.Stage String GraphBackend SolutionSeq :=
  L4Factoidal.Dataflow.Stage.ofFun (fun gb => evalBgpBackend b gb) (BackendBgpContract b g)
    (fun _ _ hx hg hG => evalBgpBackend_kequiv hx hg hG b)

/-- The contract of the reference fallback's WHERE answer: for a pattern of
    `NativeFrag` over a dataset that is a set with IRI graph names, an answer
    `Allowed` admits in the default graph. -/
def FallbackWhereContract (env : EvalEnv) (p : QueryPattern) (D : Dataset) (r : SolutionSeq) : Prop :=
  NativeFrag p → D.IsSet → Storage.QuadDataset.namesAreIris D = true → Allowed env D p D.default r

/-- A dataset → the WHERE answer of `evalPatternBackend` over its in-memory
    dataset record (`indexedDatasetBackend`, the record of the reference
    fallback). -/
def fallbackWhereStage (env : EvalEnv) (p : QueryPattern) :
    L4Factoidal.Dataflow.Stage String Dataset SolutionSeq :=
  L4Factoidal.Dataflow.Stage.ofFun
    (fun D => evalPatternBackend env (indexedDatasetBackend D) p (indexedDatasetBackend D).default)
    (FallbackWhereContract env p)
    (fun D hp hset hiri => indexedWhere_allowed env D hset hiri p hp)

/-! ## 13. Build-time checks: one representative of an RDF term

The module header's example (https://github.com/danbri/factoidal/issues/1001).
`Literal.langString "x" "EN"` is `"x"@en`: the two spellings are one RDF term
with one representation, so the backend, the reference, and both orders of
the patterns bind `?o` to the same term, and `FILTER(LANG(?o) = "en")` keeps
the row on every path. -/

private def gxA : WfIri := ⟨"http://example.org/a", by decide⟩
private def gxB : WfIri := ⟨"http://example.org/b", by decide⟩
private def gxP : WfIri := ⟨"http://example.org/p", by decide⟩
private def gxQ : WfIri := ⟨"http://example.org/q", by decide⟩

private def gxEn : Term := .literal (Literal.langString "x" "en")
private def gxEN : Term := .literal (Literal.langString "x" "EN")

#guard gxEn == gxEN

private def gxGraph : Graph :=
  [ { s := .iri gxA, p := gxP, o := gxEn },
    { s := .iri gxB, p := gxP, o := .literal (Literal.string "y") },
    { s := .iri gxA, p := gxQ, o := gxEN } ]

private def gxBgp : Bgp :=
  [ { s := .var "s", p := .iri gxP, o := .var "o" },
    { s := .var "s", p := .iri gxQ, o := .var "o" } ]

private def gxLangEn : Expr :=
  .compare .eq (.lang (.var "o")) (.lit (Literal.string "en"))

private def gxDsb : DatasetBackend := { default := .list gxGraph, named := [] }

#guard (evalBgp gxBgp gxGraph).map (fun mu => mu.lookup "o") == [some gxEn]
#guard (evalBgpBackend gxBgp (.list gxGraph)).map (fun mu => mu.lookup "o") == [some gxEn]
#guard (evalBgp gxBgp.reverse gxGraph).map (fun mu => mu.lookup "o") == [some gxEn]
#guard (evalBgpBackend gxBgp.reverse (.list gxGraph)).map (fun mu => mu.lookup "o") == [some gxEn]
#guard gxLangEn.backendLocal
#guard (refSol emptyEnv { default := gxGraph, named := [] } (.filter gxLangEn (.bgp gxBgp)) gxGraph).length == 1
#guard (refSol emptyEnv { default := gxGraph, named := [] }
  (.filter gxLangEn (.bgp gxBgp.reverse)) gxGraph).length == 1
#guard (evalPatternBackend emptyEnv gxDsb (.filter gxLangEn (.bgp gxBgp)) (.list gxGraph)).length == 1
#guard (evalPatternBackend emptyEnv gxDsb (.filter gxLangEn (.bgp gxBgp.reverse))
  (.list gxGraph)).length == 1

/-! ## Axiom audit -/

#print axioms evalBgpFrom_perm
#print axioms evalSingleTpBackend_kequiv
#print axioms evalBgpBackend_kequiv
#print axioms evalBgpBackend_kequiv_of_den
#print axioms evalBgpBackend_solEquiv
#print axioms evalBgpBackend_allowed
#print axioms evalPatternBackend_allowed
#print axioms indexedWhere_allowed
#print axioms datasetFixed
#print axioms backendFixed
#print axioms backendBgpStage
#print axioms fallbackWhereStage

end L4Factoidal.Storage.BackendRefinement
