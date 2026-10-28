/-
L4Factoidal.SPARQLRL.SemiNaiveTheorems — the semi-naive fixpoint of the
SPARQL-RL general rules (`generalLoop`, `Eval.lean`) computes the same triples
as the naive fixpoint. Asked for by the owner in
https://github.com/danbri/factoidal-core/pull/163 (SPARQL 1.2 RL); feature
issue https://github.com/danbri/factoidal/issues/1099.

## The specification

`naiveLoop` (below) is the naive fixpoint: each round evaluates the body of
every rule against the evaluation graph `GE` of the round start (`evalBody` with
every triple pattern matched against `GE`), instantiates the heads, and adds the
new triples; it stops when a round adds nothing or the fuel ends. `NOut M` is
the set of triples one naive round over the triples `M` derives, stated with a
declarative semantics `Sem` of a rule-element sequence (triple pattern,
`FILTER`, `NOT`, `NOT DATA`; `WHERE DATA` reads `G0`).

## The hypotheses

* `∀ r ∈ rules, r.runOnce = false` — the rules are general rules
  (`Rule.runOnce`, `Syntax.lean`): no assignment and no group element at any
  depth, and no blank node in a head. `evalLayers` passes exactly the
  `general` rules of a layer, which `stratify` selects by this test.
* `NegBlind rules` — a triple pattern inside a top-level `NOT` (at any depth,
  except under `NOT DATA`) matches no head instance of the rules. This is what
  the draft's stratification gives a layer: a `NOT` makes a closed dependency,
  and a closed dependency puts the producing rule in a strictly lower layer.
  It is a hypothesis here, not derived from `stratify`: that derivation needs
  the completeness of the unifier in `patternMatchesTemplate` and the fixpoint
  property of `strataLoop`, and neither is proved yet.
* `IGraph.WF` of `G0` and of the input `GE` — the index invariant of the
  evaluation graph (`IGraph.wf_ofGraph`, `IGraph.wf_insertAll`, so it holds of
  every graph `RuleSet.evalGraph` builds).

## The theorems

1. **Equal to naive** — `generalLoop_eq_naiveLoop`: for the same fuel, the
   semi-naive loop and the naive loop give the same triples
   (`t ∈ semi ↔ t ∈ naive`). The proof is per round: the semi-naive round, run
   on `GE = P ∪ Δ` where `GE` is the naive round of `P`, adds exactly the
   triples the naive round over `GE` adds (`semi_round_new`). Its main lemma is
   the Δ-decomposition `Sem_decompose`: a body solution over `GE` matches every
   triple pattern in `GE \ Δ`, or it is a solution of the pass `k` for its
   first triple pattern `k` that matched a `Δ` triple. A solution of the first
   kind is a solution over `P` (`NegBlind` makes the `NOT` elements read the
   same over `P` and over `GE`, `Sem_frame`), so its head is already in `GE`.
2. **Soundness** — `generalLoop_sound`: every triple of the result is in the
   input or a head instance of the rules.
3. **Saturation** — `generalLoop_saturated`: when one more unit of fuel does not
   change the result, the result is closed under the naive round.
4. **Least fixed point** — `generalLoop_least`: the result is contained in every
   set of triples that contains the input, is closed under the naive round, and
   adds only head instances.

`mem_evalSeq` connects the executable `evalSeq` (with the hash indexes of
`IGraph` and `Src.candidates`) to `Sem`; `mem_matchTriple` is its triple-pattern
case.

## Not proved

* That the fuel `N^3 + 2` of `evalLayers` is enough to reach the stable state
  that theorem 3 needs (the term-universe bound of the `Eval.lean` header).
* `NegBlind` from `stratify` (see the hypotheses).
* The naive loop here evaluates every rule against the graph of the round
  start; the draft's loop evaluates the rules in turn against the current
  `GE`. The two have the same least fixed point under the same hypotheses; that
  equality is not stated here.
-/
import L4Factoidal.SPARQLRL.Eval

namespace L4Factoidal.SPARQLRL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## The evaluation graph as a set -/

/-- Membership in an evaluation graph. -/
def IGraph.mem (g : IGraph) (t : T3) : Prop := g.contains t = true

/-- The index invariant of an evaluation graph: the set, the three position
indexes and the insertion-order array hold the same triples. -/
structure IGraph.WF (g : IGraph) : Prop where
  set_all : ∀ t, g.set.contains t = true ↔ t ∈ g.all
  byS : ∀ k t, t ∈ g.byS.getD k #[] ↔ t ∈ g.all ∧ t.1 = k
  byP : ∀ k t, t ∈ g.byP.getD k #[] ↔ t ∈ g.all ∧ t.2.1 = k
  byO : ∀ k t, t ∈ g.byO.getD k #[] ↔ t ∈ g.all ∧ t.2.2 = k

theorem IGraph.mem_iff_all {g : IGraph} (h : g.WF) (t : T3) : g.mem t ↔ t ∈ g.all :=
  h.set_all t

theorem IGraph.wf_empty : (({} : IGraph)).WF where
  set_all t := by simp
  byS k t := by simp
  byP k t := by simp
  byO k t := by simp

theorem IGraph.wf_insert {g : IGraph} (h : g.WF) (t : T3) : (g.insert t).WF := by
  unfold IGraph.insert
  split
  · exact h
  · rename_i hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Array.mem_push]
      rw [h.set_all]
      constructor
      · rintro (rfl | hu) <;> simp_all
      · rintro (hu | rfl) <;> simp_all
    · intro k u
      simp only [Std.HashMap.getD_insert, beq_iff_eq, Array.mem_push]
      split
      · rename_i hk
        subst hk
        rw [Array.mem_push, h.byS]
        constructor
        · rintro (⟨hu, _⟩ | rfl) <;> simp_all
        · rintro ⟨hu | rfl, _⟩ <;> simp_all
      · rename_i hk
        rw [h.byS]
        constructor
        · rintro ⟨hu, rfl⟩; exact ⟨Or.inl hu, rfl⟩
        · rintro ⟨hu | rfl, rfl⟩
          · exact ⟨hu, rfl⟩
          · exact absurd rfl hk
    · intro k u
      simp only [Std.HashMap.getD_insert, beq_iff_eq, Array.mem_push]
      split
      · rename_i hk
        subst hk
        rw [Array.mem_push, h.byP]
        constructor
        · rintro (⟨hu, _⟩ | rfl) <;> simp_all
        · rintro ⟨hu | rfl, _⟩ <;> simp_all
      · rename_i hk
        rw [h.byP]
        constructor
        · rintro ⟨hu, rfl⟩; exact ⟨Or.inl hu, rfl⟩
        · rintro ⟨hu | rfl, rfl⟩
          · exact ⟨hu, rfl⟩
          · exact absurd rfl hk
    · intro k u
      simp only [Std.HashMap.getD_insert, beq_iff_eq, Array.mem_push]
      split
      · rename_i hk
        subst hk
        rw [Array.mem_push, h.byO]
        constructor
        · rintro (⟨hu, _⟩ | rfl) <;> simp_all
        · rintro ⟨hu | rfl, _⟩ <;> simp_all
      · rename_i hk
        rw [h.byO]
        constructor
        · rintro ⟨hu, rfl⟩; exact ⟨Or.inl hu, rfl⟩
        · rintro ⟨hu | rfl, rfl⟩
          · exact ⟨hu, rfl⟩
          · exact absurd rfl hk

theorem IGraph.mem_insert (g : IGraph) (t u : T3) : (g.insert t).mem u ↔ u = t ∨ g.mem u := by
  unfold IGraph.insert IGraph.mem IGraph.contains
  split
  · rename_i hc
    constructor
    · intro hu; exact Or.inr hu
    · rintro (rfl | hu)
      · exact hc
      · exact hu
  · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (rfl | hu)
      · exact Or.inl rfl
      · exact Or.inr hu
    · rintro (rfl | hu)
      · exact Or.inl rfl
      · exact Or.inr hu

theorem IGraph.wf_foldl_insert {g : IGraph} (h : g.WF) (ts : List T3) :
    (ts.foldl IGraph.insert g).WF := by
  induction ts generalizing g with
  | nil => exact h
  | cons t ts ih => exact ih (IGraph.wf_insert h t)

theorem IGraph.mem_foldl_insert (g : IGraph) (ts : List T3) (u : T3) :
    (ts.foldl IGraph.insert g).mem u ↔ u ∈ ts ∨ g.mem u := by
  induction ts generalizing g with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, IGraph.mem_insert]
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem IGraph.wf_ofGraph (g : Graph) : (IGraph.ofGraph g).WF := by
  unfold IGraph.ofGraph
  exact IGraph.wf_foldl_insert IGraph.wf_empty (g.map tripleToT3) |> fun h => by
    rw [List.foldl_map] at h; exact h

theorem IGraph.wf_insertAll {g : IGraph} (h : g.WF) (ts : Array T3) : (g.insertAll ts).WF := by
  unfold IGraph.insertAll
  rw [← Array.foldl_toList]
  exact IGraph.wf_foldl_insert h ts.toList

theorem IGraph.mem_insertAll (g : IGraph) (ts : Array T3) (u : T3) :
    (g.insertAll ts).mem u ↔ u ∈ ts ∨ g.mem u := by
  unfold IGraph.insertAll
  rw [← Array.foldl_toList, IGraph.mem_foldl_insert, Array.mem_toList_iff]

/-! ## Matching one triple pattern -/

/-- A triple pattern matched against one triple, extending `b`. -/
def matchT (b : Binding) (tp : STriple) (t : T3) : Option Binding :=
  (matchTerm b tp.s t.1).bind fun b1 => (matchTerm b1 tp.p t.2.1).bind fun b2 => matchTerm b2 tp.o t.2.2

/-- Membership in a source: in its graph and not in its excluded graph. -/
def Src.mem (src : Src) (t : T3) : Prop := src.g.mem t ∧ ∀ ex, src.excl = some ex → ¬ ex.mem t

/-- `b1` keeps every binding of `b`. -/
def BExt (b b1 : Binding) : Prop := ∀ v u, b.lookup v = some u → b1.lookup v = some u

theorem BExt.refl (b : Binding) : BExt b b := fun _ _ h => h

theorem BExt.trans {a b c : Binding} (h1 : BExt a b) (h2 : BExt b c) : BExt a c :=
  fun v u h => h2 v u (h1 v u h)

theorem matchTerm_bext : ∀ (x : STerm) (b : Binding) (t : Term) (b' : Binding),
    matchTerm b x t = some b' → BExt b b'
  | .var v, b, t, b', h => by
    unfold matchTerm at h
    split at h
    · split at h
      · cases h; exact BExt.refl _
      · cases h
    · rename_i hv
      cases h
      intro w u hw
      simp only [Binding.bind, Binding.lookup]
      split
      · rename_i hwv; subst hwv; rw [hv] at hw; cases hw
      · exact hw
  | .iri i, b, t, b', h => by
    unfold matchTerm at h; split at h
    · cases h; exact BExt.refl _
    · cases h
  | .lit l, b, t, b', h => by
    unfold matchTerm at h; split at h
    · cases h; exact BExt.refl _
    · cases h
  | .bnode _, b, t, b', h => by unfold matchTerm at h; cases h
  | .triple s p o, b, t, b', h => by
    cases t with
    | tripleTerm ts tq to =>
      unfold matchTerm at h
      split at h
      · cases h
      · rename_i b1 h1
        split at h
        · cases h
        · rename_i b2 h2
          exact (matchTerm_bext s _ _ _ h1).trans ((matchTerm_bext p _ _ _ h2).trans
            (matchTerm_bext o _ _ _ h))
    | iri _ => unfold matchTerm at h; cases h
    | bnode _ => unfold matchTerm at h; cases h
    | literal _ => unfold matchTerm at h; cases h

theorem inst_ext {b b1 : Binding} (he : BExt b b1) (bn : String → Term) :
    ∀ (x : STerm) (u : Term), inst b bn x = some u → inst b1 bn x = some u
  | .var v, u, h => by unfold inst at h ⊢; exact he v u h
  | .iri _, u, h => by unfold inst at h ⊢; exact h
  | .lit _, u, h => by unfold inst at h ⊢; exact h
  | .bnode _, u, h => by unfold inst at h ⊢; exact h
  | .triple s p o, u, h => by
    unfold inst at h ⊢
    split at h
    · rename_i s' p' o' hs hp ho
      rw [inst_ext he bn s _ hs, inst_ext he bn p _ hp, inst_ext he bn o _ ho]
      exact h
    · cases h

theorem Subject.toTerm_toSubject (s : Subject) : s.toTerm.toSubject? = some s := by
  cases s <;> rfl

theorem Subject.toTerm_inj {s s' : Subject} (h : s.toTerm = s'.toTerm) : s = s' := by
  cases s <;> cases s' <;> simp_all [Subject.toTerm]

/-- A pattern term with no blank node whose instance is `u` matches `u` only. -/
theorem matchTerm_ground : ∀ (x : STerm) (b : Binding) (bn : String → Term) (u t : Term)
    (b' : Binding), x.bnodes = [] → inst b bn x = some u → matchTerm b x t = some b' → t = u
  | .var v, b, bn, u, t, b', _, hi, hm => by
    unfold inst at hi; unfold matchTerm at hm
    rw [hi] at hm
    simp only at hm
    split at hm
    · rename_i heq; exact (beq_iff_eq.mp heq).symm
    · cases hm
  | .iri i, b, bn, u, t, b', _, hi, hm => by
    unfold inst at hi; unfold matchTerm at hm
    cases hi
    split at hm
    · rename_i heq; exact beq_iff_eq.mp heq
    · cases hm
  | .lit l, b, bn, u, t, b', _, hi, hm => by
    unfold inst at hi; unfold matchTerm at hm
    cases hi
    split at hm
    · rename_i heq; exact beq_iff_eq.mp heq
    · cases hm
  | .bnode x, b, bn, u, t, b', hb, hi, hm => by simp [STerm.bnodes] at hb
  | .triple s p o, b, bn, u, t, b', hb, hi, hm => by
    simp only [STerm.bnodes, List.append_eq_nil_iff] at hb
    obtain ⟨⟨hbs, hbp⟩, hbo⟩ := hb
    unfold inst at hi
    split at hi
    · rename_i s' p' o' hs hp ho
      cases t with
      | tripleTerm ts tq to =>
        unfold matchTerm at hm
        split at hm
        · cases hm
        · rename_i b1 h1
          split at hm
          · cases hm
          · rename_i b2 h2
            have e1 := matchTerm_ground s b bn _ _ _ hbs hs h1
            have e2 := matchTerm_ground p b1 bn _ _ _ hbp
              (inst_ext (matchTerm_bext s _ _ _ h1) bn p _ hp) h2
            have e3 := matchTerm_ground o b2 bn _ _ _ hbo
              (inst_ext ((matchTerm_bext s _ _ _ h1).trans (matchTerm_bext p _ _ _ h2)) bn o _ ho) hm
            cases e2
            subst e3
            rw [← e1, Subject.toTerm_toSubject] at hi
            cases hi
            rfl
      | iri _ => unfold matchTerm at hm; cases hm
      | bnode _ => unfold matchTerm at hm; cases hm
      | literal _ => unfold matchTerm at hm; cases hm
    · cases hi

theorem ground?_some {b : Binding} {x : STerm} {u : Term} (h : ground? b x = some u) :
    x.bnodes = [] ∧ inst b (fun y => .bnode y) x = some u := by
  unfold ground? at h
  split at h
  · cases h
  · rename_i hb
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Decidable.not_not] at hb
    exact ⟨hb, h⟩

/-- A ground position of a pattern fixes that position of every triple it
matches, also after earlier positions extended the solution. -/
theorem matchTerm_ground? {b b0 : Binding} {x : STerm} {u t : Term} {b' : Binding}
    (hg : ground? b x = some u) (he : BExt b b0) (hm : matchTerm b0 x t = some b') : t = u := by
  obtain ⟨hb, hi⟩ := ground?_some hg
  exact matchTerm_ground x b0 _ u t b' hb (inst_ext he _ x u hi) hm

theorem matchT_some {b : Binding} {tp : STriple} {t : T3} {b' : Binding}
    (h : matchT b tp t = some b') :
    (∀ k, ground? b tp.s = some k → t.1 = k) ∧ (∀ k, ground? b tp.p = some k → t.2.1 = k) ∧
    (∀ k, ground? b tp.o = some k → t.2.2 = k) := by
  unfold matchT at h
  cases h1 : matchTerm b tp.s t.1 with
  | none => rw [h1] at h; cases h
  | some b1 =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    cases h2 : matchTerm b1 tp.p t.2.1 with
    | none => rw [h2] at h; cases h
    | some b2 =>
      rw [h2] at h
      simp only [Option.bind_some] at h
      have e1 := matchTerm_bext _ _ _ _ h1
      have e2 := matchTerm_bext _ _ _ _ h2
      exact ⟨fun k hk => matchTerm_ground? hk (BExt.refl b) h1,
             fun k hk => matchTerm_ground? hk e1 h2,
             fun k hk => matchTerm_ground? hk (e1.trans e2) h⟩

/-- The candidate array before the exclusion. -/
def candBase (g : IGraph) (s p o : Option Term) : Array T3 :=
  match s, p, o with
  | some s, some p, some o => if g.contains (s, p, o) then #[(s, p, o)] else #[]
  | _, _, _ =>
    let opts := [s.map (fun k => g.byS.getD k #[]), p.map (fun k => g.byP.getD k #[]),
                 o.map (fun k => g.byO.getD k #[])].filterMap id
    match opts with
    | [] => g.all
    | a :: rest => rest.foldl (fun m x => if x.size < m.size then x else m) a

theorem candidates_eq (src : Src) (s p o : Option Term) :
    src.candidates s p o = match src.excl with
      | none => candBase src.g s p o
      | some ex => (candBase src.g s p o).filter (fun t => !ex.contains t) := rfl

theorem foldl_shortest_prop (P : Array T3 → Prop) :
    ∀ (rest : List (Array T3)) (a : Array T3), P a → (∀ x ∈ rest, P x) →
      P (rest.foldl (fun m x => if x.size < m.size then x else m) a)
  | [], a, ha, _ => ha
  | x :: rest, a, ha, hr => by
    simp only [List.foldl_cons]
    apply foldl_shortest_prop P rest
    · split
      · exact hr x (List.mem_cons_self ..)
      · exact ha
    · intro y hy; exact hr y (List.mem_cons_of_mem _ hy)

theorem candBase_sound {g : IGraph} (hwf : g.WF) (s p o : Option Term) :
    ∀ t ∈ candBase g s p o, g.mem t := by
  intro t ht
  unfold candBase at ht
  split at ht
  · split at ht
    · rename_i hc
      simp at ht
      subst ht; exact hc
    · simp at ht
  · rw [IGraph.mem_iff_all hwf]
    revert ht
    generalize hopts : List.filterMap id _ = opts
    intro ht
    dsimp only at ht
    split at ht
    · exact ht
    · rename_i a rest
      have hall : ∀ x ∈ a :: rest, ∀ y ∈ x, y ∈ g.all := by
        intro x hx y hy
        rw [← hopts] at hx
        simp only [List.mem_filterMap, id_eq, List.mem_cons, List.mem_nil_iff, or_false] at hx
        obtain ⟨z, hz, hzx⟩ := hx
        rcases hz with rfl | rfl | rfl
        · cases s with
          | none => cases hzx
          | some k =>
            simp only [Option.map_some, Option.some.injEq] at hzx; subst hzx
            exact ((hwf.byS k y).mp hy).1
        · cases p with
          | none => cases hzx
          | some k =>
            simp only [Option.map_some, Option.some.injEq] at hzx; subst hzx
            exact ((hwf.byP k y).mp hy).1
        · cases o with
          | none => cases hzx
          | some k =>
            simp only [Option.map_some, Option.some.injEq] at hzx; subst hzx
            exact ((hwf.byO k y).mp hy).1
      exact foldl_shortest_prop (fun x => ∀ y ∈ x, y ∈ g.all) rest a
        (hall a (List.mem_cons_self ..)) (fun x hx => hall x (List.mem_cons_of_mem _ hx)) t ht

theorem candBase_complete {g : IGraph} (hwf : g.WF) (s p o : Option Term) (t : T3)
    (hm : g.mem t) (hs : ∀ k, s = some k → t.1 = k) (hp : ∀ k, p = some k → t.2.1 = k)
    (ho : ∀ k, o = some k → t.2.2 = k) : t ∈ candBase g s p o := by
  have hall : t ∈ g.all := (IGraph.mem_iff_all hwf t).mp hm
  unfold candBase
  split
  · rename_i s0 p0 o0
    obtain ⟨t1, t2, t3⟩ := t
    have e1 := hs s0 rfl; have e2 := hp p0 rfl; have e3 := ho o0 rfl
    simp only at e1 e2 e3
    subst e1 e2 e3
    simp only [IGraph.mem] at hm
    simp [hm]
  · generalize hopts : List.filterMap id _ = opts
    dsimp only
    split
    · exact hall
    · rename_i a rest
      have hin : ∀ x ∈ a :: rest, t ∈ x := by
        intro x hx
        rw [← hopts] at hx
        simp only [List.mem_filterMap, id_eq, List.mem_cons, List.mem_nil_iff, or_false] at hx
        obtain ⟨z, hz, hzx⟩ := hx
        rcases hz with rfl | rfl | rfl
        · cases s with
          | none => cases hzx
          | some k =>
            simp only [Option.map_some, Option.some.injEq] at hzx; subst hzx
            exact (hwf.byS k t).mpr ⟨hall, hs k rfl⟩
        · cases p with
          | none => cases hzx
          | some k =>
            simp only [Option.map_some, Option.some.injEq] at hzx; subst hzx
            exact (hwf.byP k t).mpr ⟨hall, hp k rfl⟩
        · cases o with
          | none => cases hzx
          | some k =>
            simp only [Option.map_some, Option.some.injEq] at hzx; subst hzx
            exact (hwf.byO k t).mpr ⟨hall, ho k rfl⟩
      exact foldl_shortest_prop (fun x => t ∈ x) rest a (hin a (List.mem_cons_self ..))
        (fun x hx => hin x (List.mem_cons_of_mem _ hx))

theorem foldl_optPush {α β : Type} (f : α → Option β) (F : Array β → α → Array β)
    (hF : ∀ acc x, F acc x = match f x with | none => acc | some y => acc.push y) :
    ∀ (l : List α) (init : Array β), (l.foldl F init).toList = init.toList ++ l.filterMap f
  | [], init => by simp
  | x :: l, init => by
    simp only [List.foldl_cons, List.filterMap_cons]
    rw [foldl_optPush f F hF l, hF]
    cases f x <;> simp

theorem mem_matchTriple {src : Src} (hwf : src.g.WF) (b : Binding) (tp : STriple) (b' : Binding) :
    b' ∈ matchTriple src b tp ↔ ∃ t, src.mem t ∧ matchT b tp t = some b' := by
  unfold matchTriple
  rw [← Array.foldl_toList, foldl_optPush (matchT b tp)]
  rotate_left
  · intro acc x
    obtain ⟨s, p, o⟩ := x
    unfold matchT
    rcases h1 : matchTerm b tp.s s with _ | b1
    · simp [h1]
    · rcases h2 : matchTerm b1 tp.p p with _ | b2
      · simp [h1, h2]
      · rcases h3 : matchTerm b2 tp.o o with _ | b3 <;> simp [h1, h2, h3]
  simp only [List.nil_append, List.mem_filterMap, Array.mem_toList_iff]
  constructor
  · rintro ⟨t, ht, hm⟩
    refine ⟨t, ?_, hm⟩
    rw [candidates_eq] at ht
    split at ht
    · rename_i hex
      exact ⟨candBase_sound hwf _ _ _ t ht, fun ex h => by rw [hex] at h; cases h⟩
    · rename_i ex hex
      rw [Array.mem_filter] at ht
      refine ⟨candBase_sound hwf _ _ _ t ht.1, fun ex' h => ?_⟩
      rw [hex] at h; cases h
      simp only [IGraph.mem]
      simpa using ht.2
  · rintro ⟨t, ⟨hg, hx⟩, hm⟩
    refine ⟨t, ?_, hm⟩
    obtain ⟨hs, hp, ho⟩ := matchT_some hm
    have hc := candBase_complete hwf _ _ _ t hg hs hp ho
    rw [candidates_eq]
    split
    · exact hc
    · rename_i ex hex
      rw [Array.mem_filter]
      refine ⟨hc, ?_⟩
      have := hx ex hex
      simp only [IGraph.mem] at this
      simpa using this

/-! ## A declarative semantics of a rule-element sequence

`Sem cx G0 F S idx μ es μ'`: the sequence `es`, its first top-level triple
pattern numbered `idx`, extends the solution `μ` to `μ'`, when the triple
pattern number `i` is matched against the triples `S i`, a `NOT` element reads
`F` (or `G0` for `NOT DATA`), and `WHERE DATA`/`NOT DATA` read `G0`. It has no
assignment and no group element: those make a rule run-once
(`Rule.runOnce`), and this file is about the general rules. -/
def Sem (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ : Binding)
    (es : List Elt) (μ' : Binding) : Prop :=
  match es with
  | [] => μ' = μ
  | .triple tp :: es => ∃ t μ1, S idx t ∧ matchT μ tp t = some μ1 ∧ Sem cx G0 F S (idx + 1) μ1 es μ'
  | .filter e _ :: es => ebv (Expr.evalIn cx.env μ e) = some true ∧ Sem cx G0 F S idx μ es μ'
  | .neg ev inner :: es =>
      (¬ ∃ ν, Sem cx G0 (if ev then F else G0) (fun _ => if ev then F else G0) 0 μ inner ν) ∧
      Sem cx G0 F S idx μ es μ'
  | .assign .. :: _ => False
  | .group .. :: _ => False
termination_by sizeOf es

theorem Sem_nil (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ μ' : Binding) :
    Sem cx G0 F S idx μ [] μ' ↔ μ' = μ := by rw [Sem.eq_1]

theorem Sem_triple (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ μ' : Binding)
    (tp : STriple) (es : List Elt) :
    Sem cx G0 F S idx μ (.triple tp :: es) μ' ↔
      ∃ t μ1, S idx t ∧ matchT μ tp t = some μ1 ∧ Sem cx G0 F S (idx + 1) μ1 es μ' := by
  rw [Sem.eq_2]

theorem Sem_filter (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ μ' : Binding)
    (e : Expr) (vs : List String) (es : List Elt) :
    Sem cx G0 F S idx μ (.filter e vs :: es) μ' ↔
      ebv (Expr.evalIn cx.env μ e) = some true ∧ Sem cx G0 F S idx μ es μ' := by
  rw [Sem.eq_3]

theorem Sem_neg (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ μ' : Binding)
    (ev : Bool) (inner es : List Elt) :
    Sem cx G0 F S idx μ (.neg ev inner :: es) μ' ↔
      (¬ ∃ ν, Sem cx G0 (if ev then F else G0) (fun _ => if ev then F else G0) 0 μ inner ν) ∧
      Sem cx G0 F S idx μ es μ' := by
  rw [Sem.eq_4]

theorem Sem_assign (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ μ' : Binding)
    (v : String) (e : Expr) (vs : List String) (es : List Elt) :
    ¬ Sem cx G0 F S idx μ (.assign v e vs :: es) μ' := by
  rw [Sem.eq_5]; exact id

theorem Sem_group (cx : Ctx) (G0 F : T3 → Prop) (S : Nat → T3 → Prop) (idx : Nat) (μ μ' : Binding)
    (ks : List String) (pat : List Elt) (aggs : List (String × AggFn)) (es : List Elt) :
    ¬ Sem cx G0 F S idx μ (.group ks pat aggs :: es) μ' := by
  rw [Sem.eq_6]; exact id

theorem Src.mem_none (g : IGraph) : (Src.mem ⟨g, none⟩) = g.mem := by
  funext t
  apply propext
  simp only [Src.mem]
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, fun ex he => by cases he⟩

theorem if_empty_mem {seq' : List Binding} {idx' : Nat} {E : List Binding × Nat} {μ' : Binding}
    {T : Binding → Prop} (h : μ' ∈ E.1 ↔ ∃ x ∈ seq', T x) :
    μ' ∈ (if seq'.isEmpty = true then (([] : List Binding), idx') else E).1 ↔ ∃ x ∈ seq', T x := by
  split
  · rename_i he
    rw [List.isEmpty_iff] at he
    subst he
    simp
  · exact h

theorem listMakesRunOnce_cons {e : Elt} {es : List Elt} (h : Elt.listMakesRunOnce (e :: es) = false) :
    e.makesRunOnce = false ∧ Elt.listMakesRunOnce es = false := by
  rw [Elt.listMakesRunOnce.eq_2] at h
  split at h
  · cases h
  · rename_i he
    simp only [Bool.not_eq_true] at he
    exact ⟨he, h⟩

/-- The executable sequence evaluation computes `Sem`, for a sequence with no
assignment or group element at any depth. -/
theorem mem_evalSeq (cx : Ctx) (hg0 : cx.g0.WF) (es : List Elt) (full : IGraph)
    (sel : Nat → Src) (idx : Nat) (seq : List Binding) (μ' : Binding)
    (hfull : full.WF) (hsel : ∀ i, (sel i).g.WF) (hro : Elt.listMakesRunOnce es = false) :
    μ' ∈ (evalSeq cx full sel idx seq es).1 ↔
      ∃ μ ∈ seq, Sem cx cx.g0.mem full.mem (fun i => (sel i).mem) idx μ es μ' := by
  match es with
  | [] =>
    rw [evalSeq.eq_1]; simp only [Sem_nil]
    constructor
    · intro h; exact ⟨μ', h, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩; exact hμ
  | e :: es =>
    obtain ⟨he, hes⟩ := listMakesRunOnce_cons hro
    rw [evalSeq.eq_2]
    cases e with
    | triple tp =>
      rw [evalElt.eq_1]
      dsimp only
      rw [if_empty_mem (mem_evalSeq cx hg0 es full sel (idx + 1) _ μ' hfull hsel hes)]
      simp only [Sem_triple, List.mem_flatMap, mem_matchTriple (hsel idx)]
      constructor
      · rintro ⟨x, ⟨μ, hμ, t, ht, hm⟩, hx⟩; exact ⟨μ, hμ, t, x, ht, hm, hx⟩
      · rintro ⟨μ, hμ, t, x, ht, hm, hx⟩; exact ⟨x, ⟨μ, hμ, t, ht, hm⟩, hx⟩
    | filter fe vs =>
      rw [evalElt.eq_2]
      dsimp only
      rw [if_empty_mem (mem_evalSeq cx hg0 es full sel idx _ μ' hfull hsel hes)]
      simp only [Sem_filter, List.mem_filter]
      constructor
      · rintro ⟨x, ⟨hx, hf⟩, hs⟩; exact ⟨x, hx, beq_iff_eq.mp hf, hs⟩
      · rintro ⟨x, hx, hf, hs⟩; exact ⟨x, ⟨hx, beq_iff_eq.mpr hf⟩, hs⟩
    | neg ev inner =>
      have hin : Elt.listMakesRunOnce inner = false := by
        simpa [Elt.makesRunOnce] using he
      rw [evalElt.eq_3]
      dsimp only
      rw [if_empty_mem (mem_evalSeq cx hg0 es full sel idx _ μ' hfull hsel hes)]
      simp only [Sem_neg]
      have hg : (if ev = true then full else cx.g0).WF := by split <;> assumption
      have key : ∀ μ, (evalSeq cx (if ev = true then full else cx.g0)
          (fun _ => { g := if ev = true then full else cx.g0 }) 0 [μ] inner).1.isEmpty = true ↔
          ¬ ∃ ν, Sem cx cx.g0.mem (if ev = true then full.mem else cx.g0.mem)
            (fun _ => if ev = true then full.mem else cx.g0.mem) 0 μ inner ν := by
        intro μ
        rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
        have hrec := fun ν => mem_evalSeq cx hg0 inner (if ev = true then full else cx.g0)
          (fun _ => { g := if ev = true then full else cx.g0 }) 0 [μ] ν hg (fun _ => hg) hin
        simp only [Src.mem_none, List.mem_singleton, exists_eq_left] at hrec
        have hm : (if ev = true then full else cx.g0).mem =
            (if ev = true then full.mem else cx.g0.mem) := by split <;> rfl
        rw [hm] at hrec
        constructor
        · rintro h ⟨ν, hν⟩; exact h ν ((hrec ν).mpr hν)
        · intro h ν hν; exact h ⟨ν, (hrec ν).mp hν⟩
      simp only [List.mem_filter, key]
      constructor
      · rintro ⟨x, ⟨hx, hf⟩, hs⟩; exact ⟨x, hx, hf, hs⟩
      · rintro ⟨x, hx, hf, hs⟩; exact ⟨x, ⟨hx, hf⟩, hs⟩
    | assign v ae vs => simp [Elt.makesRunOnce] at he
    | group ks pat aggs => simp [Elt.makesRunOnce] at he
termination_by sizeOf es

/-! ## Properties of `Sem` -/

/-- Transfer: a solution stays a solution when every triple-pattern source
from `idx` on grows and every `NOT` of the sequence that passes stays passing. -/
theorem Sem_transfer (cx : Ctx) (G0 F F' : T3 → Prop) (S S' : Nat → T3 → Prop) :
    ∀ (es : List Elt) (idx : Nat) (μ μ' : Binding),
    (∀ i, idx ≤ i → ∀ t, S i t → S' i t) →
    (∀ ev inner, Elt.neg ev inner ∈ es → ∀ μ0,
      (∃ ν, Sem cx G0 (if ev then F' else G0) (fun _ => if ev then F' else G0) 0 μ0 inner ν) →
      (∃ ν, Sem cx G0 (if ev then F else G0) (fun _ => if ev then F else G0) 0 μ0 inner ν)) →
    Sem cx G0 F S idx μ es μ' → Sem cx G0 F' S' idx μ es μ'
  | [], idx, μ, μ', _, _, h => by rw [Sem_nil] at h ⊢; exact h
  | .triple tp :: es, idx, μ, μ', hS, hN, h => by
    rw [Sem_triple] at h ⊢
    obtain ⟨t, μ1, ht, hm, hr⟩ := h
    refine ⟨t, μ1, hS idx (Nat.le_refl _) t ht, hm, ?_⟩
    exact Sem_transfer cx G0 F F' S S' es (idx + 1) μ1 μ'
      (fun i hi => hS i (by omega)) (fun ev inner hm => hN ev inner (List.mem_cons_of_mem _ hm)) hr
  | .filter e vs :: es, idx, μ, μ', hS, hN, h => by
    rw [Sem_filter] at h ⊢
    exact ⟨h.1, Sem_transfer cx G0 F F' S S' es idx μ μ' hS
      (fun ev inner hm => hN ev inner (List.mem_cons_of_mem _ hm)) h.2⟩
  | .neg ev inner :: es, idx, μ, μ', hS, hN, h => by
    rw [Sem_neg] at h ⊢
    refine ⟨fun hx => h.1 (hN ev inner (List.mem_cons_self ..) μ hx), ?_⟩
    exact Sem_transfer cx G0 F F' S S' es idx μ μ' hS
      (fun ev inner hm => hN ev inner (List.mem_cons_of_mem _ hm)) h.2
  | .assign .. :: _, _, _, _, _, _, h => (Sem_assign _ _ _ _ _ _ _ _ _ _ _ h).elim
  | .group .. :: _, _, _, _, _, _, h => (Sem_group _ _ _ _ _ _ _ _ _ _ _ h).elim

/-- The triple patterns of `es`, at any depth except under `NOT DATA`, match
no triple of `D`. -/
def Blind (D : T3 → Prop) (es : List Elt) : Prop :=
  match es with
  | [] => True
  | .triple tp :: es => (∀ μ t, D t → matchT μ tp t = none) ∧ Blind D es
  | .neg ev inner :: es => (ev = true → Blind D inner) ∧ Blind D es
  | .filter .. :: es => Blind D es
  | .assign .. :: es => Blind D es
  | .group .. :: es => Blind D es
termination_by sizeOf es

/-- Frame: a sequence blind to `D` has the same solutions over `F` and over
`F` with the triples of `D` added. -/
theorem Sem_frame (cx : Ctx) (G0 F F' D : T3 → Prop) (hF : ∀ t, F' t ↔ F t ∨ D t)
    (es : List Elt) (idx : Nat) (μ μ' : Binding) (hb : Blind D es) :
    Sem cx G0 F (fun _ => F) idx μ es μ' ↔ Sem cx G0 F' (fun _ => F') idx μ es μ' := by
  match es with
  | [] => simp only [Sem_nil]
  | .triple tp :: es =>
    rw [Blind.eq_2] at hb
    simp only [Sem_triple]
    constructor
    · rintro ⟨t, μ1, ht, hm, hr⟩
      exact ⟨t, μ1, (hF t).mpr (Or.inl ht), hm,
        (Sem_frame cx G0 F F' D hF es (idx + 1) μ1 μ' hb.2).mp hr⟩
    · rintro ⟨t, μ1, ht, hm, hr⟩
      refine ⟨t, μ1, ?_, hm, (Sem_frame cx G0 F F' D hF es (idx + 1) μ1 μ' hb.2).mpr hr⟩
      rcases (hF t).mp ht with h | h
      · exact h
      · rw [hb.1 μ t h] at hm; cases hm
  | .filter e vs :: es =>
    rw [Blind.eq_4] at hb
    simp only [Sem_filter]
    rw [Sem_frame cx G0 F F' D hF es idx μ μ' hb]
  | .neg ev inner :: es =>
    rw [Blind.eq_3] at hb
    simp only [Sem_neg]
    rw [Sem_frame cx G0 F F' D hF es idx μ μ' hb.2]
    cases ev with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
      simp only [if_true]
      have hi := fun ν => Sem_frame cx G0 F F' D hF inner 0 μ ν (hb.1 rfl)
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun ⟨ν, hν⟩ => h1 ⟨ν, (hi ν).mpr hν⟩, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun ⟨ν, hν⟩ => h1 ⟨ν, (hi ν).mp hν⟩, h2⟩
  | .assign .. :: _ =>
    constructor
    · intro h; exact (Sem_assign _ _ _ _ _ _ _ _ _ _ _ h).elim
    · intro h; exact (Sem_assign _ _ _ _ _ _ _ _ _ _ _ h).elim
  | .group .. :: _ =>
    constructor
    · intro h; exact (Sem_group _ _ _ _ _ _ _ _ _ _ _ h).elim
    · intro h; exact (Sem_group _ _ _ _ _ _ _ _ _ _ _ h).elim
termination_by sizeOf es

/-- The number of top-level triple-pattern elements. -/
noncomputable def countT : List Elt → Nat
  | [] => 0
  | .triple _ :: es => countT es + 1
  | _ :: es => countT es

theorem countTriples_eq (es : List Elt) : countTriples es = countT es := by
  unfold countTriples
  rw [show countT es = 0 + countT es by simp]
  generalize (0 : Nat) = n
  induction es generalizing n with
  | nil => simp [countT]
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    cases e <;> simp only [countT] <;> omega

/-- The source of triple pattern `i` in the semi-naive pass `k`: before `k`,
the old triples (`M` less `Δ`); at `k`, `Δ`; after `k`, all of `M`. -/
def selK (M Δ : T3 → Prop) (k i : Nat) (t : T3) : Prop :=
  if i < k then M t ∧ ¬ Δ t else if i = k then Δ t else M t

/-- **The Δ-decomposition.** A solution over `M` is a solution over the old
triples alone, or a solution of the pass for its first triple pattern that
matched a triple of `Δ`. -/
theorem Sem_decompose (cx : Ctx) (G0 F M Δ : T3 → Prop) :
    ∀ (es : List Elt) (idx : Nat) (μ μ' : Binding),
    Sem cx G0 F (fun _ => M) idx μ es μ' →
    Sem cx G0 F (fun _ t => M t ∧ ¬ Δ t) idx μ es μ' ∨
      ∃ k, idx ≤ k ∧ k < idx + countT es ∧ Sem cx G0 F (selK M Δ k) idx μ es μ'
  | [], idx, μ, μ', h => by rw [Sem_nil] at h ⊢; exact Or.inl h
  | .triple tp :: es, idx, μ, μ', h => by
    rw [Sem_triple] at h
    obtain ⟨t, μ1, ht, hm, hr⟩ := h
    by_cases hd : Δ t
    · refine Or.inr ⟨idx, Nat.le_refl _, by simp only [countT]; omega, ?_⟩
      rw [Sem_triple]
      refine ⟨t, μ1, by simp [selK, hd], hm, ?_⟩
      refine Sem_transfer cx G0 F F _ _ es (idx + 1) μ1 μ' ?_ (fun _ _ _ _ h => h) hr
      intro i hi t' h'
      simp only [selK]
      rw [if_neg (by omega), if_neg (by omega)]
      exact h'
    · rcases Sem_decompose cx G0 F M Δ es (idx + 1) μ1 μ' hr with h | ⟨k, hk1, hk2, hk⟩
      · left
        rw [Sem_triple]
        exact ⟨t, μ1, ⟨ht, hd⟩, hm, h⟩
      · right
        refine ⟨k, by omega, by simp only [countT]; omega, ?_⟩
        rw [Sem_triple]
        refine ⟨t, μ1, ?_, hm, hk⟩
        simp only [selK]
        rw [if_pos (by omega)]
        exact ⟨ht, hd⟩
  | .filter e vs :: es, idx, μ, μ', h => by
    rw [Sem_filter] at h
    rcases Sem_decompose cx G0 F M Δ es idx μ μ' h.2 with h' | ⟨k, hk1, hk2, hk⟩
    · left; rw [Sem_filter]; exact ⟨h.1, h'⟩
    · right; refine ⟨k, hk1, by simpa [countT] using hk2, ?_⟩
      rw [Sem_filter]; exact ⟨h.1, hk⟩
  | .neg ev inner :: es, idx, μ, μ', h => by
    rw [Sem_neg] at h
    rcases Sem_decompose cx G0 F M Δ es idx μ μ' h.2 with h' | ⟨k, hk1, hk2, hk⟩
    · left; rw [Sem_neg]; exact ⟨h.1, h'⟩
    · right; refine ⟨k, hk1, by simpa [countT] using hk2, ?_⟩
      rw [Sem_neg]; exact ⟨h.1, hk⟩
  | .assign .. :: _, _, _, _, h => (Sem_assign _ _ _ _ _ _ _ _ _ _ _ h).elim
  | .group .. :: _, _, _, _, h => (Sem_group _ _ _ _ _ _ _ _ _ _ _ h).elim


/-! ## Head instances -/

/-- A head template instantiated by a solution, blank nodes given by `bn`. -/
def headInstB (μ : Binding) (bn : String → Term) (tt : STriple) : Option T3 :=
  match inst μ bn tt.s, inst μ bn tt.p, inst μ bn tt.o with
  | some s, some p, some o => some (s, p, o)
  | _, _, _ => none

/-- A head template with no blank node instantiated by a solution. -/
def headInst (μ : Binding) (tt : STriple) : Option T3 := headInstB μ (fun x => .bnode x) tt

theorem inst_bn_irrel (b : Binding) (bn bn' : String → Term) :
    ∀ x : STerm, x.bnodes = [] → inst b bn x = inst b bn' x
  | .var _, _ => rfl
  | .iri _, _ => rfl
  | .lit _, _ => rfl
  | .bnode _, h => by simp [STerm.bnodes] at h
  | .triple s p o, h => by
    simp only [STerm.bnodes, List.append_eq_nil_iff] at h
    unfold inst
    rw [inst_bn_irrel b bn bn' s h.1.1, inst_bn_irrel b bn bn' p h.1.2,
      inst_bn_irrel b bn bn' o h.2]

theorem headInstB_irrel (μ : Binding) (bn : String → Term) (tt : STriple) (h : tt.bnodes = []) :
    headInstB μ bn tt = headInst μ tt := by
  simp only [STriple.bnodes, List.append_eq_nil_iff] at h
  unfold headInst headInstB
  rw [inst_bn_irrel μ bn (fun x => .bnode x) tt.s h.1.1,
    inst_bn_irrel μ bn (fun x => .bnode x) tt.p h.1.2,
    inst_bn_irrel μ bn (fun x => .bnode x) tt.o h.2]

theorem foldl_mem {α σ : Type} (l : List α) (f : σ → α → σ) (M : σ → T3 → Prop)
    (Q : α → T3 → Prop) (hf : ∀ s, ∀ a ∈ l, ∀ u, M (f s a) u ↔ M s u ∨ Q a u) :
    ∀ s u, M (l.foldl f s) u ↔ M s u ∨ ∃ a ∈ l, Q a u := by
  induction l with
  | nil => intro s u; simp
  | cons a l ih =>
    intro s u
    rw [List.foldl_cons, ih (fun s b hb u => hf s b (List.mem_cons_of_mem _ hb) u),
      hf s a (List.mem_cons_self ..)]
    constructor
    · rintro ((h | h) | ⟨b, hb, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h⟩
    · rintro (h | ⟨b, hb, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨b, hb, h⟩

theorem headStep (μ : Binding) (bn : String → Term) (o : Array T3) (tt : STriple) (w : T3) :
    w ∈ (match inst μ bn tt.s, inst μ bn tt.p, inst μ bn tt.o with
      | some s, some p, some o' => o.push (s, p, o')
      | _, _, _ => o) ↔ w ∈ o ∨ headInstB μ bn tt = some w := by
  unfold headInstB
  cases inst μ bn tt.s <;> cases inst μ bn tt.p <;> cases inst μ bn tt.o <;>
    simp [Array.mem_push, eq_comm]

theorem mem_instHead (r : Rule) (pfx : String) (ctr : Nat) (sols : List Binding) (u : T3)
    (hb : ∀ tt ∈ r.head, tt.bnodes = []) :
    u ∈ (instHead r pfx ctr sols).1 ↔ ∃ μ ∈ sols, ∃ tt ∈ r.head, headInst μ tt = some u := by
  unfold instHead
  dsimp only
  refine (foldl_mem (σ := Array T3 × Nat) sols _ (fun (s : Array T3 × Nat) (u : T3) => u ∈ s.1)
    (fun μ u => ∃ tt ∈ r.head, headInst μ tt = some u) ?_ _ u).trans ?_
  · intro s μ _ v
    obtain ⟨out, c⟩ := s
    dsimp only
    refine (foldl_mem (σ := Array T3) r.head _ (fun (o : Array T3) (v : T3) => v ∈ o)
      (fun tt v => headInstB μ (fun x => Term.bnode (pfx ++ toString (c + idxOfStr x
        (addVars [] (List.flatMap STriple.bnodes r.head))))) tt = some v) ?_ out v).trans ?_
    · intro o tt _ w
      exact headStep μ _ o tt w
    · constructor
      · rintro (h | ⟨tt, htt, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨tt, htt, (headInstB_irrel _ _ tt (hb tt htt)) ▸ h⟩
      · rintro (h | ⟨tt, htt, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨tt, htt, (headInstB_irrel _ _ tt (hb tt htt)).symm ▸ h⟩
  · simp


theorem foldl_inv {α σ : Type} (P : σ → Prop) (f : σ → α → σ) (hf : ∀ s a, P s → P (f s a)) :
    ∀ (l : List α) (s : σ), P s → P (l.foldl f s)
  | [], _, h => h
  | a :: l, s, h => foldl_inv P f hf l (f s a) (hf s a h)

/-! ## New triples of a round -/

/-- The triples of `out` that are not in `ge`, as a graph (the `delta'` of
`generalLoop`). -/
def newOf (ge : IGraph) (out : Array T3) : IGraph :=
  out.foldl (fun d t => if ge.contains t then d else d.insert t) {}

theorem wf_newOf (ge : IGraph) (out : Array T3) : (newOf ge out).WF := by
  unfold newOf
  rw [← Array.foldl_toList]
  refine foldl_inv IGraph.WF _ ?_ out.toList {} IGraph.wf_empty
  intro d t hd
  split
  · exact hd
  · exact IGraph.wf_insert hd t

theorem mem_newOf (ge : IGraph) (out : Array T3) (u : T3) :
    (newOf ge out).mem u ↔ u ∈ out ∧ ¬ ge.mem u := by
  unfold newOf
  rw [← Array.foldl_toList]
  rw [foldl_mem (σ := IGraph) out.toList _ IGraph.mem (fun t u => u = t ∧ ¬ ge.mem u) ?_ {} u]
  · constructor
    · rintro (h | ⟨t, ht, rfl, hn⟩)
      · simp [IGraph.mem, IGraph.contains] at h
      · exact ⟨Array.mem_toList_iff.mp ht, hn⟩
    · rintro ⟨h, hn⟩
      exact Or.inr ⟨u, Array.mem_toList_iff.mpr h, rfl, hn⟩
  · intro d t _ w
    split
    · rename_i hc
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨rfl, hn⟩)
        · exact h
        · exact absurd hc hn
    · rename_i hc
      rw [IGraph.mem_insert]
      constructor
      · rintro (rfl | h)
        · exact Or.inr ⟨rfl, hc⟩
        · exact Or.inl h
      · rintro (h | ⟨rfl, _⟩)
        · exact Or.inr h
        · exact Or.inl rfl

theorem size_eq_zero_iff {d : IGraph} (h : d.WF) : (d.size == 0) = true ↔ ∀ u, ¬ d.mem u := by
  simp only [IGraph.size, beq_iff_eq, Array.size_eq_zero_iff]
  constructor
  · intro he u hu
    rw [IGraph.mem_iff_all h, he] at hu
    simp at hu
  · intro hn
    match hl : d.all with
    | ⟨[]⟩ => rfl
    | ⟨x :: xs⟩ => exact absurd ((IGraph.mem_iff_all h x).mpr (by rw [hl]; simp)) (hn x)

/-! ## The naive round and the naive loop (the specification) -/

/-- A solution of a rule body in the naive round over the triples `M`. -/
def NSol (cx : Ctx) (M : T3 → Prop) (r : Rule) (μ : Binding) : Prop :=
  if r.evaldata then Sem cx cx.g0.mem M (fun _ => M) 0 [] r.body μ
  else Sem cx cx.g0.mem cx.g0.mem (fun _ => cx.g0.mem) 0 [] r.body μ

/-- The triples one naive round over `M` derives: a head instance of a body
solution, for every rule. -/
def NOut (cx : Ctx) (rules : List Rule) (M : T3 → Prop) (t : T3) : Prop :=
  ∃ r ∈ rules, ∃ μ, NSol cx M r μ ∧ ∃ tt ∈ r.head, headInst μ tt = some t

/-- A triple that some head of `rules` can produce. -/
def HeadInst (rules : List Rule) (t : T3) : Prop :=
  ∃ r ∈ rules, ∃ tt ∈ r.head, ∃ μ, headInst μ tt = some t

/-- The `NOT` elements of the rules read no triple that the rules can produce:
the triple patterns inside each top-level `NOT` (at any depth, except under
`NOT DATA`) match no head instance of the rules. This is the property the
draft's stratification gives a layer: a `NOT` makes a closed dependency, so a
rule that can produce a triple the `NOT` reads is in a lower layer. -/
def NegBlind (rules : List Rule) : Prop :=
  ∀ r ∈ rules, ∀ inner, Elt.neg true inner ∈ r.body → Blind (HeadInst rules) inner

/-- The naive round as an executable: every rule's body against `ge`. -/
def naiveOut (cx : Ctx) (rules : List Rule) (ge : IGraph) : Array T3 :=
  rules.foldl (fun acc r => acc ++ (instHead r "" 0 (evalBody cx r ge (fun _ => ⟨ge, none⟩))).1) #[]

/-- The naive loop: naive rounds until one adds nothing, or the fuel ends. -/
def naiveLoop (cx : Ctx) (rules : List Rule) : Nat → IGraph → IGraph
  | 0, ge => ge
  | f + 1, ge =>
    let d := newOf ge (naiveOut cx rules ge)
    if d.size == 0 then ge else naiveLoop cx rules f (ge.insertAll d.all)

theorem runOnce_false {r : Rule} (h : r.runOnce = false) :
    Elt.listMakesRunOnce r.body = false ∧ ∀ tt ∈ r.head, tt.bnodes = [] := by
  simp only [Rule.runOnce, Bool.or_eq_false_iff, List.any_eq_false, Bool.or_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, not_or] at h
  refine ⟨h.1, fun tt htt => ?_⟩
  have := (h.2 tt htt).1
  simpa using this

theorem mem_evalBody_full (cx : Ctx) (hg0 : cx.g0.WF) {ge : IGraph} (hge : ge.WF) {r : Rule}
    (hro : Elt.listMakesRunOnce r.body = false) (μ : Binding) :
    μ ∈ evalBody cx r ge (fun _ => ⟨ge, none⟩) ↔ NSol cx ge.mem r μ := by
  unfold evalBody NSol
  split
  · rw [mem_evalSeq cx hg0 r.body ge _ 0 [[]] μ hge (fun _ => hge) hro]
    simp [Src.mem_none]
  · rw [mem_evalSeq cx hg0 r.body cx.g0 _ 0 [[]] μ hg0 (fun _ => hg0) hro]
    simp [Src.mem_none]

theorem mem_naiveOut (cx : Ctx) (hg0 : cx.g0.WF) (rules : List Rule)
    (hgen : ∀ r ∈ rules, r.runOnce = false) {ge : IGraph} (hge : ge.WF) (u : T3) :
    u ∈ naiveOut cx rules ge ↔ NOut cx rules ge.mem u := by
  unfold naiveOut
  rw [foldl_mem (σ := Array T3) rules _ (fun o v => v ∈ o)
    (fun r v => ∃ μ, NSol cx ge.mem r μ ∧ ∃ tt ∈ r.head, headInst μ tt = some v) ?_ #[] u]
  · simp [NOut]
  · intro acc r hr v
    obtain ⟨hro, hb⟩ := runOnce_false (hgen r hr)
    rw [Array.mem_append, mem_instHead r "" 0 _ v hb]
    simp only [mem_evalBody_full cx hg0 hge hro]

/-! ## The semi-naive round -/

/-- The solutions `generalLoop` computes for rule `r` in one round. -/
def semiSols (cx : Ctx) (first : Bool) (ge delta : IGraph) (r : Rule) : List Binding :=
  if first then evalBody cx r ge (fun _ => ⟨ge, none⟩)
  else if !r.evaldata then []
  else (List.range (countTriples r.body)).flatMap fun k =>
    evalBody cx r ge (fun i =>
      if i < k then ⟨ge, some delta⟩ else if i == k then ⟨delta, none⟩ else ⟨ge, none⟩)

/-- One round of `generalLoop` before the new triples are taken. -/
def roundFold (pfx : String) (rules : List Rule) (S : Rule → List Binding) (ctr : Nat) :
    Array T3 × Nat :=
  rules.foldl (fun x r =>
    match x with
    | (acc, c) =>
      match instHead r pfx c (S r) with
      | (ts, c') => (acc ++ ts, c')) (#[], ctr)

theorem generalLoop_succ (cx : Ctx) (pfx : String) (rules : List Rule) (f : Nat) (first : Bool)
    (ge delta : IGraph) (ctr : Nat) :
    generalLoop cx pfx rules (f + 1) first ge delta ctr =
      match roundFold pfx rules (semiSols cx first ge delta) ctr with
      | (out, ctr') =>
        if (newOf ge out).size == 0 then (ge, ctr')
        else generalLoop cx pfx rules f false (ge.insertAll (newOf ge out).all) (newOf ge out) ctr' := by
  rw [generalLoop.eq_2]
  rfl

theorem mem_roundFold (pfx : String) (rules : List Rule) (S : Rule → List Binding)
    (hb : ∀ r ∈ rules, ∀ tt ∈ r.head, tt.bnodes = []) (ctr : Nat) (u : T3) :
    u ∈ (roundFold pfx rules S ctr).1 ↔ ∃ r ∈ rules, ∃ μ ∈ S r, ∃ tt ∈ r.head, headInst μ tt = some u := by
  unfold roundFold
  rw [foldl_mem (σ := Array T3 × Nat) rules _ (fun s v => v ∈ s.1)
    (fun r v => ∃ μ ∈ S r, ∃ tt ∈ r.head, headInst μ tt = some v) ?_ (#[], ctr) u]
  · simp
  · intro s r hr v
    obtain ⟨acc, c⟩ := s
    dsimp only
    have hm := mem_instHead r pfx c (S r) v (hb r hr)
    revert hm
    cases instHead r pfx c (S r) with
    | mk ts c' =>
      intro hm
      dsimp only
      rw [Array.mem_append, hm]

theorem selSrc_mem (ge delta : IGraph) (k : Nat) :
    (fun i => (if i < k then (⟨ge, some delta⟩ : Src)
      else if (i == k) = true then ⟨delta, none⟩ else ⟨ge, none⟩).mem) = selK ge.mem delta.mem k := by
  funext i t
  apply propext
  unfold selK
  by_cases h1 : i < k
  · simp only [h1, if_true, Src.mem]
    constructor
    · rintro ⟨h, hx⟩; exact ⟨h, hx delta rfl⟩
    · rintro ⟨h, hx⟩; exact ⟨h, fun ex he => by cases he; exact hx⟩
  · simp only [h1, if_false]
    by_cases h2 : i = k
    · simp only [h2, beq_self_eq_true, if_true, Src.mem_none]
    · have : (i == k) = false := by simpa using h2
      simp only [this, Bool.false_eq_true, if_false, h2, Src.mem_none]

theorem mem_semiSols_later (cx : Ctx) (hg0 : cx.g0.WF) {ge delta : IGraph} (hge : ge.WF)
    (hd : delta.WF) {r : Rule} (hro : Elt.listMakesRunOnce r.body = false) (μ : Binding) :
    μ ∈ semiSols cx false ge delta r ↔
      r.evaldata = true ∧ ∃ k < countT r.body,
        Sem cx cx.g0.mem ge.mem (selK ge.mem delta.mem k) 0 [] r.body μ := by
  unfold semiSols
  simp only [Bool.false_eq_true, if_false]
  cases hr : r.evaldata with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false, List.mem_flatMap, List.mem_range,
      countTriples_eq, true_and]
    apply exists_congr
    intro k
    apply and_congr_right
    intro _
    unfold evalBody
    rw [if_pos hr]
    have hsel : ∀ i, (if i < k then (⟨ge, some delta⟩ : Src)
        else if (i == k) = true then ⟨delta, none⟩ else ⟨ge, none⟩).g.WF := by
      intro i
      split
      · exact hge
      · split
        · exact hd
        · exact hge
    rw [mem_evalSeq cx hg0 r.body ge _ 0 [[]] μ hge hsel hro, selSrc_mem]
    simp

theorem Blind_mono (D D' : T3 → Prop) (hD : ∀ t, D' t → D t) (es : List Elt) (h : Blind D es) :
    Blind D' es := by
  match es with
  | [] => rw [Blind.eq_1]; trivial
  | .triple tp :: es =>
    rw [Blind.eq_2] at h ⊢
    exact ⟨fun μ t ht => h.1 μ t (hD t ht), Blind_mono D D' hD es h.2⟩
  | .neg ev inner :: es =>
    rw [Blind.eq_3] at h ⊢
    exact ⟨fun he => Blind_mono D D' hD inner (h.1 he), Blind_mono D D' hD es h.2⟩
  | .filter .. :: es =>
    rw [Blind.eq_4] at h ⊢
    exact Blind_mono D D' hD es h
  | .assign .. :: es =>
    rw [Blind.eq_5] at h ⊢
    exact Blind_mono D D' hD es h
  | .group .. :: es =>
    rw [Blind.eq_6] at h ⊢
    exact Blind_mono D D' hD es h
termination_by sizeOf es

/-- **The semi-naive round finds the new triples of the naive round.** In a
round whose input `ge` is the naive round of `P` (`ge = P ∪ Δ`, `Δ` the new
head instances), a triple not in `ge` is produced by the semi-naive round
exactly when the naive round over `ge` produces it. -/
theorem semi_round_new (cx : Ctx) (hg0 : cx.g0.WF) (rules : List Rule)
    (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules)
    {ge Δ P : IGraph} (hge : ge.WF) (hΔ : Δ.WF)
    (hsplit : ∀ t, ge.mem t ↔ P.mem t ∨ Δ.mem t)
    (hhead : ∀ t, Δ.mem t → HeadInst rules t) (hP : ∀ t, NOut cx rules P.mem t → ge.mem t)
    (u : T3) (hu : ¬ ge.mem u) :
    (∃ r ∈ rules, ∃ μ ∈ semiSols cx false ge Δ r, ∃ tt ∈ r.head, headInst μ tt = some u) ↔
      NOut cx rules ge.mem u := by
  constructor
  · rintro ⟨r, hr, μ, hμ, tt, htt, hi⟩
    obtain ⟨hro, _⟩ := runOnce_false (hgen r hr)
    obtain ⟨hev, k, _, hs⟩ := (mem_semiSols_later cx hg0 hge hΔ hro μ).mp hμ
    refine ⟨r, hr, μ, ?_, tt, htt, hi⟩
    unfold NSol
    rw [if_pos hev]
    refine Sem_transfer cx _ _ _ _ _ r.body 0 [] μ ?_ (fun _ _ _ _ h => h) hs
    intro i _ t ht
    unfold selK at ht
    split at ht
    · exact ht.1
    · split at ht
      · exact (hsplit t).mpr (Or.inr ht)
      · exact ht
  · rintro ⟨r, hr, μ, hns, tt, htt, hi⟩
    obtain ⟨hro, _⟩ := runOnce_false (hgen r hr)
    unfold NSol at hns
    split at hns
    · rename_i hev
      rcases Sem_decompose cx _ _ ge.mem Δ.mem r.body 0 [] μ hns with hold | ⟨k, _, hk, hs⟩
      · -- every pattern matched an old triple: a solution of the round over `P`
        exfalso
        apply hu
        apply hP
        refine ⟨r, hr, μ, ?_, tt, htt, hi⟩
        unfold NSol
        rw [if_pos hev]
        refine Sem_transfer cx _ _ _ _ _ r.body 0 [] μ ?_ ?_ hold
        · intro i _ t ⟨h1, h2⟩
          rcases (hsplit t).mp h1 with h | h
          · exact h
          · exact absurd h h2
        · intro ev inner hm μ0 hx
          cases ev with
          | false => simpa using hx
          | true =>
            simp only [if_true] at hx ⊢
            obtain ⟨ν, hν⟩ := hx
            have hb := Blind_mono _ _ (fun t ht => hhead t ht) inner (hneg r hr inner hm)
            exact ⟨ν, (Sem_frame cx cx.g0.mem P.mem ge.mem Δ.mem hsplit inner 0 μ0 ν hb).mp hν⟩
      · refine ⟨r, hr, μ, ?_, tt, htt, hi⟩
        exact (mem_semiSols_later cx hg0 hge hΔ hro μ).mpr ⟨hev, k, by omega, hs⟩
    · exfalso
      apply hu
      apply hP
      refine ⟨r, hr, μ, ?_, tt, htt, hi⟩
      unfold NSol
      rw [if_neg (by assumption)]
      exact hns

theorem NOut_congr (cx : Ctx) (rules : List Rule) {M M' : T3 → Prop} (h : ∀ t, M t ↔ M' t) :
    NOut cx rules M = NOut cx rules M' := by
  have : M = M' := funext fun t => propext (h t)
  rw [this]

/-- The invariant of the later rounds. -/
theorem loop_later (cx : Ctx) (pfx : String) (rules : List Rule) (hg0 : cx.g0.WF)
    (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules) :
    ∀ (f : Nat) (ge Δ gn P : IGraph) (ctr : Nat), ge.WF → Δ.WF → gn.WF → P.WF →
    (∀ t, ge.mem t ↔ gn.mem t) → (∀ t, ge.mem t ↔ P.mem t ∨ Δ.mem t) →
    (∀ t, Δ.mem t → HeadInst rules t) →
    (∀ t, NOut cx rules P.mem t → ge.mem t) →
    ∀ t, (generalLoop cx pfx rules f false ge Δ ctr).1.mem t ↔ (naiveLoop cx rules f gn).mem t
  | 0, ge, Δ, gn, P, ctr, _, _, _, _, heq, _, _, _ => by
    intro t
    rw [generalLoop.eq_1]
    exact heq t
  | f + 1, ge, Δ, gn, P, ctr, hge, hΔ, hgn, hPw, heq, hsplit, hhead, hP => by
    intro t
    have hb : ∀ r ∈ rules, ∀ tt ∈ r.head, tt.bnodes = [] :=
      fun r hr => (runOnce_false (hgen r hr)).2
    rw [generalLoop_succ]
    have hout := mem_roundFold pfx rules (semiSols cx false ge Δ) hb ctr
    generalize roundFold pfx rules (semiSols cx false ge Δ) ctr = res at hout
    obtain ⟨out, ctr'⟩ := res
    dsimp only at hout ⊢
    have hmeq : NOut cx rules gn.mem = NOut cx rules ge.mem :=
      NOut_congr cx rules (fun t => (heq t).symm)
    -- the new triples of the two rounds
    have hd : ∀ u, (newOf ge out).mem u ↔ (newOf gn (naiveOut cx rules gn)).mem u := by
      intro u
      rw [mem_newOf, mem_newOf, mem_naiveOut cx hg0 rules hgen hgn, hmeq, ← heq u]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(semi_round_new cx hg0 rules hgen hneg hge hΔ hsplit hhead hP u h2).mp
          ((hout u).mp h1), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hout u).mpr
          ((semi_round_new cx hg0 rules hgen hneg hge hΔ hsplit hhead hP u h2).mpr h1), h2⟩
    have hdw := wf_newOf ge out
    have hdnw := wf_newOf gn (naiveOut cx rules gn)
    unfold naiveLoop
    dsimp only
    by_cases hz : ((newOf ge out).size == 0) = true
    · have hzn : ((newOf gn (naiveOut cx rules gn)).size == 0) = true := by
        rw [size_eq_zero_iff hdnw]
        intro u hu
        exact (size_eq_zero_iff hdw).mp hz u ((hd u).mpr hu)
      rw [if_pos hz, if_pos hzn]
      exact heq t
    · have hzn : ¬ ((newOf gn (naiveOut cx rules gn)).size == 0) = true := by
        rw [size_eq_zero_iff hdnw]
        intro hn
        apply hz
        rw [size_eq_zero_iff hdw]
        intro u hu
        exact hn u ((hd u).mp hu)
      rw [if_neg hz, if_neg hzn]
      refine loop_later cx pfx rules hg0 hgen hneg f _ _ _ ge ctr'
        (IGraph.wf_insertAll hge _) hdw (IGraph.wf_insertAll hgn _) hge ?_ ?_ ?_ ?_ t
      · intro u
        rw [IGraph.mem_insertAll, IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw,
          ← IGraph.mem_iff_all hdnw, hd u, heq u]
      · intro u
        rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw]
        exact Or.comm
      · intro u hu
        obtain ⟨r, hr, μ, _, tt, htt, hi⟩ := (hout u).mp ((mem_newOf ge out u).mp hu).1
        exact ⟨r, hr, tt, htt, μ, hi⟩
      · intro u hu
        rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw]
        by_cases hg : ge.mem u
        · exact Or.inr hg
        · refine Or.inl ((mem_newOf ge out u).mpr ⟨?_, hg⟩)
          exact (hout u).mpr
            ((semi_round_new cx hg0 rules hgen hneg hge hΔ hsplit hhead hP u hg).mpr hu)

/-- **Semi-naive equals naive.** For the general rules of a layer (no rule is
run-once, so no assignment, no group element and no blank node in a head), whose
`NOT` elements read no triple the rules can produce (`NegBlind`), the
semi-naive loop `generalLoop` and the naive loop `naiveLoop`, given the same
fuel, return evaluation graphs with the same triples. -/
theorem generalLoop_eq_naiveLoop (cx : Ctx) (pfx : String) (rules : List Rule)
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules)
    {ge : IGraph} (hge : ge.WF) (fuel ctr : Nat) (t : T3) :
    (generalLoop cx pfx rules fuel true ge {} ctr).1.mem t ↔ (naiveLoop cx rules fuel ge).mem t := by
  match fuel with
  | 0 => rw [generalLoop.eq_1]; rfl
  | f + 1 =>
    have hb : ∀ r ∈ rules, ∀ tt ∈ r.head, tt.bnodes = [] :=
      fun r hr => (runOnce_false (hgen r hr)).2
    rw [generalLoop_succ]
    have hout := mem_roundFold pfx rules (semiSols cx true ge {}) hb ctr
    generalize roundFold pfx rules (semiSols cx true ge {}) ctr = res at hout
    obtain ⟨out, ctr'⟩ := res
    dsimp only at hout ⊢
    have hout' : ∀ u, u ∈ out ↔ NOut cx rules ge.mem u := by
      intro u
      rw [hout u]
      unfold NOut semiSols
      simp only [if_true]
      constructor
      · rintro ⟨r, hr, μ, hμ, tt, htt, hi⟩
        exact ⟨r, hr, μ, (mem_evalBody_full cx hg0 hge (runOnce_false (hgen r hr)).1 μ).mp hμ,
          tt, htt, hi⟩
      · rintro ⟨r, hr, μ, hμ, tt, htt, hi⟩
        exact ⟨r, hr, μ, (mem_evalBody_full cx hg0 hge (runOnce_false (hgen r hr)).1 μ).mpr hμ,
          tt, htt, hi⟩
    have hd : ∀ u, (newOf ge out).mem u ↔ (newOf ge (naiveOut cx rules ge)).mem u := by
      intro u
      rw [mem_newOf, mem_newOf, mem_naiveOut cx hg0 rules hgen hge, hout' u]
    have hdw := wf_newOf ge out
    have hdnw := wf_newOf ge (naiveOut cx rules ge)
    unfold naiveLoop
    dsimp only
    by_cases hz : ((newOf ge out).size == 0) = true
    · have hzn : ((newOf ge (naiveOut cx rules ge)).size == 0) = true := by
        rw [size_eq_zero_iff hdnw]
        intro u hu
        exact (size_eq_zero_iff hdw).mp hz u ((hd u).mpr hu)
      rw [if_pos hz, if_pos hzn]
    · have hzn : ¬ ((newOf ge (naiveOut cx rules ge)).size == 0) = true := by
        rw [size_eq_zero_iff hdnw]
        intro hn
        apply hz
        rw [size_eq_zero_iff hdw]
        intro u hu
        exact hn u ((hd u).mp hu)
      rw [if_neg hz, if_neg hzn]
      refine loop_later cx pfx rules hg0 hgen hneg f _ _ _ ge ctr'
        (IGraph.wf_insertAll hge _) hdw (IGraph.wf_insertAll hge _) hge ?_ ?_ ?_ ?_ t
      · intro u
        rw [IGraph.mem_insertAll, IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw,
          ← IGraph.mem_iff_all hdnw, hd u]
      · intro u
        rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw]
        exact Or.comm
      · intro u hu
        obtain ⟨r, hr, μ, _, tt, htt, hi⟩ := (hout u).mp ((mem_newOf ge out u).mp hu).1
        exact ⟨r, hr, tt, htt, μ, hi⟩
      · intro u hu
        rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw]
        by_cases hg : ge.mem u
        · exact Or.inr hg
        · exact Or.inl ((mem_newOf ge out u).mpr ⟨(hout' u).mpr hu, hg⟩)


/-! ## Saturation and least fixed point of the naive loop -/

/-- A naive round is monotone between graphs that differ only in head
instances: the `NOT` elements cannot see the difference (`NegBlind`). -/
theorem NOut_mono (cx : Ctx) (rules : List Rule) (hneg : NegBlind rules)
    {G S : T3 → Prop} (hGS : ∀ t, G t → S t) (hdiff : ∀ t, S t → ¬ G t → HeadInst rules t)
    (t : T3) (h : NOut cx rules G t) : NOut cx rules S t := by
  obtain ⟨r, hr, μ, hns, tt, htt, hi⟩ := h
  refine ⟨r, hr, μ, ?_, tt, htt, hi⟩
  unfold NSol at hns ⊢
  split
  · rename_i hev
    rw [if_pos hev] at hns
    refine Sem_transfer cx _ _ _ _ _ r.body 0 [] μ (fun _ _ t ht => hGS t ht) ?_ hns
    intro ev inner hm μ0 hx
    cases ev with
    | false => simpa using hx
    | true =>
      simp only [if_true] at hx ⊢
      obtain ⟨ν, hν⟩ := hx
      have hb := Blind_mono (HeadInst rules) (fun t => S t ∧ ¬ G t)
        (fun t ht => hdiff t ht.1 ht.2) inner (hneg r hr inner hm)
      have hF : ∀ t, S t ↔ G t ∨ (S t ∧ ¬ G t) := by
        intro t
        by_cases hg : G t
        · exact ⟨fun _ => Or.inl hg, fun _ => hGS t hg⟩
        · exact ⟨fun hs => Or.inr ⟨hs, hg⟩, fun h => h.elim (fun h => hGS t h) (fun h => h.1)⟩
      exact ⟨ν, (Sem_frame cx cx.g0.mem G S _ hF inner 0 μ0 ν hb).mpr hν⟩
  · rename_i hev
    rw [if_neg hev] at hns
    exact hns

/-- Every triple of the naive loop is in its input or a head instance. -/
theorem naiveLoop_sound (cx : Ctx) (rules : List Rule) (hg0 : cx.g0.WF)
    (hgen : ∀ r ∈ rules, r.runOnce = false) :
    ∀ (f : Nat) (ge : IGraph), ge.WF → ∀ t, (naiveLoop cx rules f ge).mem t →
      ge.mem t ∨ HeadInst rules t
  | 0, ge, _, t, h => Or.inl h
  | f + 1, ge, hge, t, h => by
    unfold naiveLoop at h
    dsimp only at h
    split at h
    · exact Or.inl h
    · have hdw := wf_newOf ge (naiveOut cx rules ge)
      rcases naiveLoop_sound cx rules hg0 hgen f _ (IGraph.wf_insertAll hge _) t h with h' | h'
      · rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw, mem_newOf,
          mem_naiveOut cx hg0 rules hgen hge] at h'
        rcases h' with ⟨⟨r, hr, μ, _, tt, htt, hi⟩, _⟩ | h'
        · exact Or.inr ⟨r, hr, tt, htt, μ, hi⟩
        · exact Or.inl h'
      · exact Or.inr h'

/-- **Least fixed point.** The naive loop's result is contained in every set of
triples `S` that contains its input, is closed under the naive round, and adds
only head instances to the input. -/
theorem naiveLoop_least (cx : Ctx) (rules : List Rule) (hg0 : cx.g0.WF)
    (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules) (S : T3 → Prop)
    (hclosed : ∀ t, NOut cx rules S t → S t) :
    ∀ (f : Nat) (ge : IGraph), ge.WF → (∀ t, ge.mem t → S t) →
      (∀ t, S t → ¬ ge.mem t → HeadInst rules t) →
      ∀ t, (naiveLoop cx rules f ge).mem t → S t
  | 0, ge, _, hsub, _, t, h => hsub t h
  | f + 1, ge, hge, hsub, hdiff, t, h => by
    unfold naiveLoop at h
    dsimp only at h
    split at h
    · exact hsub t h
    · have hdw := wf_newOf ge (naiveOut cx rules ge)
      have hnew : ∀ u, (ge.insertAll (newOf ge (naiveOut cx rules ge)).all).mem u → S u := by
        intro u hu
        rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw, mem_newOf,
          mem_naiveOut cx hg0 rules hgen hge] at hu
        rcases hu with ⟨hn, _⟩ | hu
        · exact hclosed u (NOut_mono cx rules hneg hsub hdiff u hn)
        · exact hsub u hu
      refine naiveLoop_least cx rules hg0 hgen hneg S hclosed f _ (IGraph.wf_insertAll hge _)
        hnew ?_ t h
      intro u hu hn
      apply hdiff u hu
      intro hg
      apply hn
      rw [IGraph.mem_insertAll]
      exact Or.inr hg

/-- **Saturation.** When one more round of fuel does not change the naive
loop's triples, its result is closed under the naive round. -/
theorem naiveLoop_saturated (cx : Ctx) (rules : List Rule) (hg0 : cx.g0.WF)
    (hgen : ∀ r ∈ rules, r.runOnce = false) :
    ∀ (f : Nat) (ge : IGraph), ge.WF →
      (∀ t, (naiveLoop cx rules (f + 1) ge).mem t ↔ (naiveLoop cx rules f ge).mem t) →
      ∀ t, NOut cx rules (naiveLoop cx rules f ge).mem t → (naiveLoop cx rules f ge).mem t
  | 0, ge, hge, heq, t, ht => by
    have hdw := wf_newOf ge (naiveOut cx rules ge)
    show ge.mem t
    by_cases hg : ge.mem t
    · exact hg
    · have hd : (newOf ge (naiveOut cx rules ge)).mem t := by
        rw [mem_newOf, mem_naiveOut cx hg0 rules hgen hge]
        exact ⟨ht, hg⟩
      have h1 := (heq t).mp
      unfold naiveLoop at h1
      dsimp only at h1
      by_cases hz : ((newOf ge (naiveOut cx rules ge)).size == 0) = true
      · exact absurd hd ((size_eq_zero_iff hdw).mp hz t)
      · rw [if_neg hz] at h1
        apply h1
        unfold naiveLoop
        rw [IGraph.mem_insertAll, ← IGraph.mem_iff_all hdw]
        exact Or.inl hd
  | f + 1, ge, hge, heq, t, ht => by
    have hdw := wf_newOf ge (naiveOut cx rules ge)
    revert heq ht
    unfold naiveLoop
    dsimp only
    by_cases hz : ((newOf ge (naiveOut cx rules ge)).size == 0) = true
    · rw [if_pos hz, if_pos hz]
      intro _ ht
      have hn : ¬ (newOf ge (naiveOut cx rules ge)).mem t := (size_eq_zero_iff hdw).mp hz t
      rw [mem_newOf, mem_naiveOut cx hg0 rules hgen hge] at hn
      by_cases hg : ge.mem t
      · exact hg
      · exact absurd ⟨ht, hg⟩ hn
    · rw [if_neg hz, if_neg hz]
      intro heq ht
      exact naiveLoop_saturated cx rules hg0 hgen f _ (IGraph.wf_insertAll hge _) heq t ht

/-! ## The semi-naive loop: sound, saturated, least -/

/-- **Soundness.** Every triple of the semi-naive loop is in its input or a
head instance of the rules. -/
theorem generalLoop_sound (cx : Ctx) (pfx : String) (rules : List Rule)
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules)
    {ge : IGraph} (hge : ge.WF) (fuel ctr : Nat) (t : T3)
    (h : (generalLoop cx pfx rules fuel true ge {} ctr).1.mem t) : ge.mem t ∨ HeadInst rules t :=
  naiveLoop_sound cx rules hg0 hgen fuel ge hge t
    ((generalLoop_eq_naiveLoop cx pfx rules hg0 hgen hneg hge fuel ctr t).mp h)

/-- **Least fixed point.** The semi-naive loop's result is contained in every
set of triples that contains the input, is closed under the naive round and
adds only head instances. -/
theorem generalLoop_least (cx : Ctx) (pfx : String) (rules : List Rule)
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules)
    {ge : IGraph} (hge : ge.WF) (fuel ctr : Nat) (S : T3 → Prop)
    (hclosed : ∀ t, NOut cx rules S t → S t) (hsub : ∀ t, ge.mem t → S t)
    (hdiff : ∀ t, S t → ¬ ge.mem t → HeadInst rules t) (t : T3)
    (h : (generalLoop cx pfx rules fuel true ge {} ctr).1.mem t) : S t :=
  naiveLoop_least cx rules hg0 hgen hneg S hclosed fuel ge hge hsub hdiff t
    ((generalLoop_eq_naiveLoop cx pfx rules hg0 hgen hneg hge fuel ctr t).mp h)

/-- **Saturation.** When one more round of fuel does not change the
semi-naive loop's triples, its result is closed under the naive round. -/
theorem generalLoop_saturated (cx : Ctx) (pfx : String) (rules : List Rule)
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules)
    {ge : IGraph} (hge : ge.WF) (fuel ctr : Nat)
    (hstable : ∀ t, (generalLoop cx pfx rules (fuel + 1) true ge {} ctr).1.mem t ↔
      (generalLoop cx pfx rules fuel true ge {} ctr).1.mem t) (t : T3)
    (h : NOut cx rules (generalLoop cx pfx rules fuel true ge {} ctr).1.mem t) :
    (generalLoop cx pfx rules fuel true ge {} ctr).1.mem t := by
  have heq : ∀ u, (generalLoop cx pfx rules fuel true ge {} ctr).1.mem u ↔
      (naiveLoop cx rules fuel ge).mem u :=
    generalLoop_eq_naiveLoop cx pfx rules hg0 hgen hneg hge fuel ctr
  rw [NOut_congr cx rules heq] at h
  rw [heq]
  refine naiveLoop_saturated cx rules hg0 hgen fuel ge hge ?_ t h
  intro u
  rw [← generalLoop_eq_naiveLoop cx pfx rules hg0 hgen hneg hge (fuel + 1) ctr u, ← heq u]
  exact hstable u

#print axioms generalLoop_eq_naiveLoop
#print axioms generalLoop_sound
#print axioms generalLoop_saturated
#print axioms generalLoop_least
#print axioms semi_round_new
#print axioms Sem_decompose
#print axioms mem_evalSeq

end L4Factoidal.SPARQLRL
