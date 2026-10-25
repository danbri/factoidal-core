/-
L4Factoidal.Storage.BackendAgreement — the backend evaluator's WHERE answer
is the reference evaluator's WHERE answer up to the order of the solutions
(https://github.com/danbri/factoidal/issues/1014, part of
https://github.com/danbri/factoidal/issues/975).

## Why `Allowed` is not enough

`IdGroup.Allowed` (SPARQL 1.1 section 18.5 up to multiset equality) lets any
answer be replaced by a `SolEquiv` list (rule `equiv`): a permutation, then
row for row `BindEq`, the same lookup for every variable. `BindEq` does not
constrain a pair that an earlier pair of the same name hides, and
`Binding.compatible` reads every pair of its first argument, hidden ones
included. So `Allowed` admits two answers of one pattern with different
numbers of rows: `allowed_not_unique` (VALUES ?x { :t } joined with itself;
the left answer replaced by the row `[(x, t), (x, u)]`, `BindEq` to `[(x, t)]`,
gives a join with no row instead of one). Two answers `Allowed` admits are
therefore NOT one multiset, and the step "the backend's answer is allowed,
so it is the reference answer up to order" has no proof from `Allowed`.

## The tightened relation

* `RowS μ ν`: the same lookup for every variable (`BindEq`) and the same
  pairs (`∀ p, p ∈ μ ↔ p ∈ ν`). The order of the pairs is free; a hidden pair
  is not. For rows with distinct names (`Nd`) `BindEq` implies `RowS`
  (`rowS_of_nd`).
* `SolSEquiv A B := PermPw RowS A B`: the same multiset of solution
  mappings, with the same pairs in each. An equivalence relation; it implies
  `SolEquiv` and equal length.
* `AllowedS env ds p a A`: `Allowed` for the operators of `NativeFrag`, with
  the rule `equiv` over `SolSEquiv`, and FILTER and OPTIONAL with a
  `backendLocal` condition. `AllowedS.toAllowed`: every `AllowedS` answer is
  an `Allowed` answer.

## The theorems

* Congruence of the operators under `SolSEquiv`: `join_congr`,
  `leftJoin_congr`, `filter_congr`, `union_congr`, `minus_congr`,
  `graphVar_congr`. The row lemmas under them: `compatible_congr`
  (`Binding.compatible` reads the pairs of its first argument and the
  lookups of its second), `merge_congr`, `domainsDisjoint_congr`,
  `bindIfCompatible_congr`.
* `AllowedS.ref`: every answer `AllowedS` admits is `SolSEquiv` to the
  reference answer `refSol`. `AllowedS.unique`: two answers `AllowedS`
  admits for one pattern are `SolSEquiv`. `allowedS_ref`: the reference
  answer is one `AllowedS` admits, for every pattern of `NativeFrag`.
* `evalPatternBackend_allowedS`: the backend's answer is one `AllowedS`
  admits (the step from `Allowed` is the leaf: the rows of a basic graph
  pattern, backend and reference, have distinct names, `evalBgpFrom_nd`,
  `evalBgpFromMuFuel_nd`). `evalPatternBackend_ref`: so it is `SolSEquiv` to
  the reference answer.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.BackendRefinement

namespace L4Factoidal.Storage.Sbm11.IdGroup

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## The reference answer, operator by operator (the equations of `allowed_ref`) -/

theorem refSol_join_eq (env : EvalEnv) (ds : Dataset) {l r : QueryPattern} (a : Graph)
    (hl : InIdFragment l) (hr : InIdFragment r) :
    refSol env ds (.join l r) a = join (refSol env ds l a) (refSol env ds r a) := by
  show (GraphPattern.join _ _).evalIn ds a = _
  rw [evalIn_join ds a _ _ (lower_ne_serviceVar env l hl) (lower_ne_serviceVar env r hr),
    hashJoin_eq_join]
  rfl

theorem refSol_leftJoin_eq (env : EvalEnv) (ds : Dataset) (l r : QueryPattern) (c : Expr) (a : Graph) :
    refSol env ds (.leftJoin l r c) a =
      leftJoin (refSol env ds l a) (refSol env ds r a) (filterFn env c a) := by
  simp only [refSol, QueryPattern.lowerWith]
  rw [GraphPattern.evalIn, hashLeftJoin_eq_leftJoin]
  rfl

theorem refSol_filter_eq (env : EvalEnv) (ds : Dataset) (c : Expr) (q : QueryPattern) (a : Graph) :
    refSol env ds (.filter c q) a = (refSol env ds q a).filter (filterFn env c a) := by
  simp only [refSol, QueryPattern.lowerWith]
  rw [filterLowered_evalIn]
  rfl

theorem refSol_union_eq (env : EvalEnv) (ds : Dataset) (l r : QueryPattern) (a : Graph) :
    refSol env ds (.union l r) a = refSol env ds l a ++ refSol env ds r a := by
  simp only [refSol, QueryPattern.lowerWith]
  rw [GraphPattern.evalIn]
  rfl

theorem refSol_minus_eq (env : EvalEnv) (ds : Dataset) (l r : QueryPattern) (a : Graph) :
    refSol env ds (.minus l r) a = minus (refSol env ds l a) (refSol env ds r a) := by
  simp only [refSol, QueryPattern.lowerWith]
  rw [GraphPattern.evalIn, hashMinus_eq_minus]

theorem refSol_graphIri_eq (env : EvalEnv) (ds : Dataset) (i : WfIri) (q : QueryPattern) (a : Graph) :
    refSol env ds (.graph (.iri i) q) a =
      match ds.lookupNamedIri i.val with
      | some g => refSol env ds q g
      | none => [] := by
  show (GraphPattern.graph (.iri i) (QueryPattern.lowerWith env Binding.empty q)).evalIn ds a = _
  rw [GraphPattern.evalIn]
  rfl

theorem refSol_graphVar_eq (env : EvalEnv) (ds : Dataset) (v : VarName) (q : QueryPattern) (a : Graph) :
    refSol env ds (.graph (.var v) q) a =
      ds.named.flatMap fun ng => (refSol env ds q ng.graph).filterMap
        (Binding.bindIfCompatible v ng.name.toTerm) := by
  show (GraphPattern.graph (.var v) (QueryPattern.lowerWith env Binding.empty q)).evalIn ds a = _
  rw [GraphPattern.evalIn]
  rfl

theorem refSol_values_eq (env : EvalEnv) (ds : Dataset) (vars : List VarName)
    (rows : List (List (Option Term))) (a : Graph) :
    refSol env ds (.values vars rows) a = evalValues vars rows := by
  simp only [refSol, QueryPattern.lowerWith]
  rw [GraphPattern.evalIn]

theorem refSol_empty_eq (env : EvalEnv) (ds : Dataset) (a : Graph) :
    refSol env ds .empty a = [Binding.empty] := by
  simp only [refSol, QueryPattern.lowerWith]
  rw [GraphPattern.evalIn]

end L4Factoidal.Storage.Sbm11.IdGroup

namespace L4Factoidal.Storage.BackendAgreement

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.Sbm11.IdGroup (Pw PermPw BindEq SolEquiv Allowed refSol filterFn
  InIdFragment)
open L4Factoidal.Storage.BackendRefinement (GraphRel NamedRel NativeFrag)

/-! ## 1. `Allowed` admits answers of different lengths -/

/-- The blank node `_:t`. -/
def tT : Term := .bnode "t"
/-- The blank node `_:u`. -/
def tU : Term := .bnode "u"

/-- `VALUES ?x { _:t }`. -/
def valuesT : QueryPattern := .values ["x"] [[some tT]]

theorem bindEq_hidden : BindEq [("x", tT)] [("x", tT), ("x", tU)] := by
  intro v
  by_cases h : "x" = v
  · subst h; rfl
  · simp [Binding.lookup, h]

/-- **`Allowed` does not fix the multiset.** For every environment, dataset
    and active graph, `Allowed` admits an answer with one row and an answer
    with no row for `VALUES ?x { _:t }` joined with itself. The rule `equiv`
    replaces the left answer `[[(x, _:t)]]` by `[[(x, _:t), (x, _:u)]]`
    (`BindEq`: the second pair is hidden), and `Binding.compatible` reads
    the hidden pair. -/
theorem allowed_not_unique (env : EvalEnv) (ds : Dataset) (a : Graph) :
    ∃ A B, Allowed env ds (.join valuesT valuesT) a A ∧ Allowed env ds (.join valuesT valuesT) a B ∧
      A.length = 1 ∧ B.length = 0 := by
  have hv : Allowed env ds valuesT a [[("x", tT)]] := by
    have h := Allowed.values (env := env) (ds := ds) ["x"] [[some tT]] a
    exact h
  have hv' : Allowed env ds valuesT a [[("x", tT), ("x", tU)]] :=
    .equiv hv ⟨[[("x", tT)]], List.Perm.refl _, .cons bindEq_hidden .nil⟩
  refine ⟨_, _, .join hv hv, .join hv' hv, ?_, ?_⟩
  · decide
  · decide

/-! ## 2. Rows with the same pairs -/

/-- The same solution mapping with the same pairs: every variable has the
    same lookup, and the two rows have the same pairs in any order. -/
def RowS (mu nu : Binding) : Prop := BindEq mu nu ∧ ∀ p, p ∈ mu ↔ p ∈ nu

theorem RowS.refl (mu : Binding) : RowS mu mu := ⟨BindEq.refl mu, fun _ => Iff.rfl⟩
theorem RowS.symm {mu nu : Binding} (h : RowS mu nu) : RowS nu mu :=
  ⟨BindEq.symm h.1, fun p => (h.2 p).symm⟩
theorem RowS.trans {mu nu xi : Binding} (h1 : RowS mu nu) (h2 : RowS nu xi) : RowS mu xi :=
  ⟨BindEq.trans h1.1 h2.1, fun p => (h1.2 p).trans (h2.2 p)⟩

/-- The same multiset of solution mappings, with the same pairs in each. -/
def SolSEquiv (A B : SolutionSeq) : Prop := PermPw RowS A B

theorem SolSEquiv.refl (A : SolutionSeq) : SolSEquiv A A := PermPw.refl RowS.refl A
theorem SolSEquiv.symm {A B : SolutionSeq} (h : SolSEquiv A B) : SolSEquiv B A :=
  PermPw.symm (R := RowS) (fun _ _ h => RowS.symm h) h
theorem SolSEquiv.trans {A B C : SolutionSeq} (h1 : SolSEquiv A B) (h2 : SolSEquiv B C) :
    SolSEquiv A C :=
  PermPw.trans (R := RowS) (fun _ _ _ h h' => RowS.trans h h') h1 h2
theorem SolSEquiv.of_perm {A B : SolutionSeq} (h : A.Perm B) : SolSEquiv A B :=
  PermPw.of_perm RowS.refl h

theorem pw_mono {α : Type} {R S : α → α → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {A B : List α}, Pw R A B → Pw S A B
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hRS _ _ h) (pw_mono hRS t)

theorem SolSEquiv.toSolEquiv {A B : SolutionSeq} (h : SolSEquiv A B) : SolEquiv A B := by
  obtain ⟨C, p, w⟩ := h
  exact ⟨C, p, pw_mono (fun _ _ h => h.1) w⟩

theorem SolSEquiv.length_eq {A B : SolutionSeq} (h : SolSEquiv A B) : A.length = B.length := by
  obtain ⟨C, p, w⟩ := h
  exact p.length_eq.trans (Pw.length_eq w)

/-! ## 3. Lists related element for element -/

/-- Both absent, or both present and related. -/
def OptRel {α : Type} (R : α → α → Prop) : Option α → Option α → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem pw_filterMap {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {f g : α → Option β}
    (hfg : ∀ a b, R a b → OptRel S (f a) (g b)) :
    ∀ {A B : List α}, Pw R A B → Pw S (A.filterMap f) (B.filterMap g)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons h t => by
    have hab := hfg a b h
    simp only [List.filterMap_cons]
    revert hab
    cases f a <;> cases g b <;> intro hab
    · exact pw_filterMap hfg t
    · exact absurd hab id
    · exact absurd hab id
    · exact .cons hab (pw_filterMap hfg t)

theorem pw_flatMap {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {f g : α → List β}
    (hfg : ∀ a b, R a b → Pw S (f a) (g b)) :
    ∀ {A B : List α}, Pw R A B → Pw S (A.flatMap f) (B.flatMap g)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons h t => by
    simp only [List.flatMap_cons]
    exact Pw.append (hfg a b h) (pw_flatMap hfg t)

theorem pw_filter {α : Type} {R : α → α → Prop} {f g : α → Bool}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {A B : List α}, Pw R A B → Pw R (A.filter f) (B.filter g)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons h t => by
    simp only [List.filter_cons, hfg a b h]
    split
    · exact .cons h (pw_filter hfg t)
    · exact pw_filter hfg t

theorem pw_any {α : Type} {R : α → α → Prop} {f g : α → Bool}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {A B : List α}, Pw R A B → A.any f = B.any g
  | _, _, .nil => rfl
  | a :: _, b :: _, .cons h t => by
    simp only [List.any_cons, hfg a b h, pw_any hfg t]

/-! ## 4. The row operations read the pairs and the lookups -/

/-- The condition `Binding.compatible` puts on one pair of its first
    argument. -/
def CompatAt (p : VarName × Term) (mu2 : Binding) : Prop :=
  match mu2.lookup p.1 with
  | none => True
  | some t2 => p.2.eqb t2 = true

theorem compatible_iff (mu2 : Binding) :
    ∀ (mu1 : Binding), mu1.compatible mu2 = true ↔ ∀ p ∈ mu1, CompatAt p mu2
  | [] => by simp [Binding.compatible]
  | (v, t) :: rest => by
    simp only [Binding.compatible, Bool.and_eq_true, List.forall_mem_cons, compatible_iff mu2 rest,
      CompatAt]
    apply and_congr_left'
    cases mu2.lookup v <;> simp

theorem compatAt_congr {p : VarName × Term} {mu2 mu2' : Binding} (h : BindEq mu2 mu2') :
    CompatAt p mu2 ↔ CompatAt p mu2' := by
  simp only [CompatAt, h p.1]

theorem compatible_congr {mu1 mu1' mu2 mu2' : Binding} (h1 : RowS mu1 mu1') (h2 : BindEq mu2 mu2') :
    mu1.compatible mu2 = mu1'.compatible mu2' := by
  apply Bool.eq_iff_iff.mpr
  rw [compatible_iff, compatible_iff]
  constructor
  · intro h p hp; exact (compatAt_congr h2).mp (h p ((h1.2 p).mpr hp))
  · intro h p hp; exact (compatAt_congr h2).mpr (h p ((h1.2 p).mp hp))

theorem lookup_isSome_of_mem : ∀ {mu : Binding} {p : VarName × Term}, p ∈ mu → (mu.lookup p.1).isSome
  | (w, t) :: rest, p, h => by
    simp only [Binding.lookup]
    by_cases e : w = p.1
    · simp [e]
    · rw [if_neg e]
      rcases List.mem_cons.mp h with h | h
      · subst h; exact absurd rfl e
      · exact lookup_isSome_of_mem h

theorem lookup_none_not_mem {mu : Binding} {v : VarName} (h : mu.lookup v = none) (t : Term) :
    (v, t) ∉ mu := fun hm => by
  have := lookup_isSome_of_mem hm
  simp only at this
  rw [h] at this
  cases this

theorem mem_of_lookup : ∀ {mu : Binding} {v : VarName} {t : Term}, mu.lookup v = some t → (v, t) ∈ mu
  | (w, s) :: rest, v, t, h => by
    simp only [Binding.lookup] at h
    by_cases e : w = v
    · rw [if_pos e] at h; cases h; subst e; exact List.mem_cons_self
    · rw [if_neg e] at h; exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- The pairs of `merge`: those of the first row, and each name of the
    second row that the first does not bind, with its lookup. -/
theorem mem_merge' : ∀ (mu2 mu1 : Binding) (w : VarName) (s : Term),
    (w, s) ∈ mu1.merge mu2 ↔ (w, s) ∈ mu1 ∨ (mu1.lookup w = none ∧ mu2.lookup w = some s)
  | [], mu1, w, s => by simp [Binding.merge, Binding.lookup]
  | (v, t) :: rest, mu1, w, s => by
    simp only [Binding.merge]
    cases hv : mu1.lookup v with
    | some s' =>
      simp only []
      rw [mem_merge' rest mu1 w s]
      apply or_congr_right
      simp only [Binding.lookup]
      by_cases e : v = w
      · subst e; simp [hv]
      · simp [e]
    | none =>
      simp only []
      rw [mem_merge' rest ((v, t) :: mu1) w s]
      simp only [Binding.lookup, List.mem_cons]
      by_cases e : v = w
      · subst e
        simp only [if_true, hv, Prod.mk.injEq, true_and, Option.some.injEq, reduceCtorEq, false_and,
          or_false]
        constructor
        · rintro (h | h)
          · exact .inr (by subst h; rfl)
          · exact .inl h
        · rintro (h | h)
          · exact .inr h
          · exact .inl (by subst h; rfl)
      · simp only [if_neg e]
        constructor
        · rintro ((h | h) | h)
          · cases h; exact absurd rfl e
          · exact .inl h
          · exact .inr h
        · rintro (h | h)
          · exact .inl (.inr h)
          · exact .inr h

theorem mem_merge (mu2 mu1 : Binding) (p : VarName × Term) :
    p ∈ mu1.merge mu2 ↔ p ∈ mu1 ∨ (mu1.lookup p.1 = none ∧ mu2.lookup p.1 = some p.2) :=
  mem_merge' mu2 mu1 p.1 p.2

theorem merge_congr {mu1 mu1' mu2 mu2' : Binding} (h1 : RowS mu1 mu1') (h2 : BindEq mu2 mu2') :
    RowS (mu1.merge mu2) (mu1'.merge mu2') := by
  refine ⟨fun v => ?_, fun p => ?_⟩
  · rw [Storage.Sbm11.ExprLocalTheorems.lookup_merge, Storage.Sbm11.ExprLocalTheorems.lookup_merge,
      h1.1 v, h2 v]
  · rw [mem_merge, mem_merge, h1.2 p, h1.1 p.1, h2 p.1]

theorem domainsDisjoint_iff (mu2 : Binding) :
    ∀ (mu1 : Binding), domainsDisjoint mu1 mu2 = true ↔ ∀ p ∈ mu1, mu2.lookup p.1 = none
  | [] => by simp [domainsDisjoint]
  | (v, t) :: rest => by
    simp only [domainsDisjoint, Bool.and_eq_true, List.forall_mem_cons, domainsDisjoint_iff mu2 rest,
      Option.isNone_iff_eq_none]

theorem domainsDisjoint_congr {mu1 mu1' mu2 mu2' : Binding} (h1 : RowS mu1 mu1')
    (h2 : BindEq mu2 mu2') : domainsDisjoint mu1 mu2 = domainsDisjoint mu1' mu2' := by
  apply Bool.eq_iff_iff.mpr
  rw [domainsDisjoint_iff, domainsDisjoint_iff]
  constructor
  · intro h p hp; rw [← h2 p.1]; exact h p ((h1.2 p).mpr hp)
  · intro h p hp; rw [h2 p.1]; exact h p ((h1.2 p).mp hp)

theorem rowS_bind {mu mu' : Binding} (h : RowS mu mu') (v : VarName) (t : Term) :
    RowS (mu.bind v t) (mu'.bind v t) := by
  refine ⟨fun w => ?_, fun p => ?_⟩
  · simp only [Binding.bind, Binding.lookup]
    split
    · rfl
    · exact h.1 w
  · simp only [Binding.bind, List.mem_cons, h.2 p]

theorem bindIfCompatible_congr {mu mu' : Binding} (h : RowS mu mu') (v : VarName) (t : Term) :
    OptRel RowS (mu.bindIfCompatible v t) (mu'.bindIfCompatible v t) := by
  simp only [Binding.bindIfCompatible, ← h.1 v]
  cases mu.lookup v with
  | some e =>
    simp only []
    split
    · exact h
    · trivial
  | none => exact rowS_bind h v t

/-! ## 5. The operators under `SolSEquiv` -/

theorem join_congr {A A' B B' : SolutionSeq} (hA : SolSEquiv A A') (hB : SolSEquiv B B') :
    SolSEquiv (join A B) (join A' B') := by
  obtain ⟨C, pA, wA⟩ := hA
  obtain ⟨D, pB, wB⟩ := hB
  refine ⟨join C D, Storage.Sbm11.IdGroup.join_perm pA pB, ?_⟩
  unfold join
  refine pw_flatMap (fun mu1 mu1' h1 => pw_filterMap (fun mu2 mu2' h2 => ?_) wB) wA
  rw [compatible_congr h1 h2.1]
  split
  · exact merge_congr h1 h2.1
  · trivial

/-- A condition that reads only the lookups of a row. -/
def CondOk (cond : Binding → Bool) : Prop := ∀ mu mu', BindEq mu mu' → cond mu = cond mu'

theorem leftJoin_congr {A A' B B' : SolutionSeq} (cond : Binding → Bool) (hc : CondOk cond)
    (hA : SolSEquiv A A') (hB : SolSEquiv B B') :
    SolSEquiv (leftJoin A B cond) (leftJoin A' B' cond) := by
  obtain ⟨C, pA, wA⟩ := hA
  obtain ⟨D, pB, wB⟩ := hB
  refine ⟨leftJoin C D cond, Storage.Sbm11.IdGroup.leftJoin_perm cond pA pB, ?_⟩
  unfold leftJoin
  refine pw_flatMap (fun mu1 mu1' h1 => ?_) wA
  have hx : Pw RowS
      (D.filterMap fun mu2 => if mu1.compatible mu2 then
        (if cond (mu1.merge mu2) then some (mu1.merge mu2) else none) else none)
      (B'.filterMap fun mu2 => if mu1'.compatible mu2 then
        (if cond (mu1'.merge mu2) then some (mu1'.merge mu2) else none) else none) := by
    refine pw_filterMap (fun mu2 mu2' h2 => ?_) wB
    rw [compatible_congr h1 h2.1]
    split
    · have hm := merge_congr h1 h2.1
      rw [hc _ _ hm.1]
      split
      · exact hm
      · trivial
    · trivial
  dsimp only
  have hl := Pw.length_eq hx
  have he : ∀ {X Y : SolutionSeq}, X.length = Y.length → X.isEmpty = Y.isEmpty := by
    intro X Y h
    cases X <;> cases Y <;> simp_all
  rw [he hl]
  split
  · exact .cons h1 .nil
  · exact hx

theorem filter_congr {A A' : SolutionSeq} (cond : Binding → Bool) (hc : CondOk cond)
    (hA : SolSEquiv A A') : SolSEquiv (A.filter cond) (A'.filter cond) := by
  obtain ⟨C, pA, wA⟩ := hA
  exact ⟨C.filter cond, pA.filter cond, pw_filter (fun a b h => hc a b h.1) wA⟩

theorem union_congr {A A' B B' : SolutionSeq} (hA : SolSEquiv A A') (hB : SolSEquiv B B') :
    SolSEquiv (A ++ B) (A' ++ B') := PermPw.append hA hB

theorem minus_congr {A A' B B' : SolutionSeq} (hA : SolSEquiv A A') (hB : SolSEquiv B B') :
    SolSEquiv (minus A B) (minus A' B') := by
  obtain ⟨C, pA, wA⟩ := hA
  obtain ⟨D, pB, wB⟩ := hB
  refine ⟨minus C D, Storage.Sbm11.IdGroup.minus_perm pA pB, ?_⟩
  unfold minus
  refine pw_filter (fun mu1 mu1' h1 => ?_) wA
  congr 1
  refine pw_any (fun mu2 mu2' h2 => ?_) wB
  rw [compatible_congr h1 h2.1, domainsDisjoint_congr h1 h2.1]

theorem permPw_filterMap {f : Binding → Option Binding}
    (hf : ∀ a b, RowS a b → OptRel RowS (f a) (f b)) {A B : SolutionSeq} (h : SolSEquiv A B) :
    SolSEquiv (A.filterMap f) (B.filterMap f) := by
  obtain ⟨C, p, w⟩ := h
  exact ⟨C.filterMap f, p.filterMap f, pw_filterMap hf w⟩

theorem graphVar_congr (named : List NamedGraph) (v : VarName) (F F' : NamedGraph → SolutionSeq)
    (h : ∀ ng ∈ named, SolSEquiv (F ng) (F' ng)) :
    SolSEquiv (named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
      (named.flatMap fun ng => (F' ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)) :=
  PermPw.flatMap _ _ named fun ng hng =>
    permPw_filterMap (fun _ _ hab => bindIfCompatible_congr hab v ng.name.toTerm) (h ng hng)

/-- A `backendLocal` FILTER or OPTIONAL condition reads only the lookups of
    the row. -/
theorem filterFn_condOk (env : EvalEnv) {c : Expr} (hc : c.backendLocal = true) (a : Graph) :
    CondOk (filterFn env c a) := by
  intro mu mu' h
  rw [BackendRefinement.filterFn_local env hc a]
  simp only []
  rw [Storage.Sbm11.ExprLocalTheorems.evalIn_bindEq env mu mu' h c]


/-! ## 6. Rows with distinct names -/

/-- The names of the row are distinct. -/
def Nd (mu : Binding) : Prop := (mu.map Prod.fst).Nodup

theorem nd_empty : Nd Binding.empty := by simp [Nd, Binding.empty]

theorem nd_bind {mu : Binding} (h : Nd mu) {v : VarName} (hv : mu.lookup v = none) (x : Term) :
    Nd (mu.bind v x) := by
  simp only [Nd, Binding.bind, List.map_cons, List.nodup_cons]
  refine ⟨fun hm => ?_, h⟩
  obtain ⟨⟨w, t⟩, hp, e⟩ := List.mem_map.mp hm
  simp only at e
  subst e
  exact lookup_none_not_mem hv t hp

theorem lookup_of_mem_nd : ∀ {mu : Binding}, Nd mu → ∀ {p : VarName × Term}, p ∈ mu →
    mu.lookup p.1 = some p.2
  | (w, t) :: rest, h, p, hp => by
    simp only [Nd, List.map_cons, List.nodup_cons] at h
    simp only [Binding.lookup]
    rcases List.mem_cons.mp hp with e | hp
    · subst e; simp
    · have hne : w ≠ p.1 := fun e => h.1 (e ▸ List.mem_map_of_mem hp)
      rw [if_neg hne]
      exact lookup_of_mem_nd h.2 hp

/-- For rows with distinct names, the same lookups give the same pairs. -/
theorem rowS_of_nd {mu nu : Binding} (h : BindEq mu nu) (hm : Nd mu) (hn : Nd nu) : RowS mu nu := by
  refine ⟨h, fun p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have e := lookup_of_mem_nd hm hp
    rw [h p.1] at e
    exact mem_of_lookup e
  · have e := lookup_of_mem_nd hn hp
    rw [← h p.1] at e
    exact mem_of_lookup e

theorem solSEquiv_of_nd {A B : SolutionSeq} (h : SolEquiv A B) (hA : ∀ mu ∈ A, Nd mu)
    (hB : ∀ mu ∈ B, Nd mu) : SolSEquiv A B := by
  obtain ⟨C, p, w⟩ := h
  exact ⟨C, p, BackendRefinement.pw_imp_mem w fun a ha b hb hab =>
    rowS_of_nd hab (hA a (p.mem_iff.mpr ha)) (hB b hb)⟩

theorem slotMatch_nd {s : BackendRefinement.TSlot} {x : Term} {mu mu' : Binding}
    (h : BackendRefinement.slotMatch s x mu = some mu') (hm : Nd mu) : Nd mu' := by
  rcases BackendRefinement.slot_var_or_const s with ⟨v, rfl⟩ | hc
  · simp only [BackendRefinement.slotMatch] at h
    cases hv : mu.lookup v with
    | some e => rw [hv] at h; obtain ⟨-, rfl⟩ := BackendRefinement.ite_some' h; exact hm
    | none => rw [hv] at h; cases h; exact nd_bind hm hv x
  · rw [hc] at h; obtain ⟨-, rfl⟩ := BackendRefinement.ite_some' h; exact hm

theorem matchSlots_nd : ∀ (S : List (BackendRefinement.TSlot × Term)) {mu mu' : Binding},
    BackendRefinement.matchSlots S mu = some mu' → Nd mu → Nd mu'
  | [], _, _, h, hm => by cases h; exact hm
  | (s, x) :: rest, mu, mu', h, hm => by
    simp only [BackendRefinement.matchSlots] at h
    cases h1 : BackendRefinement.slotMatch s x mu with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1] at h
      exact matchSlots_nd rest h (slotMatch_nd h1 hm)

theorem tpMatch_nd {tp : TriplePattern} {t : Triple} {mu mu' : Binding}
    (h : tpMatch tp t mu = some mu') (hm : Nd mu) : Nd mu' := by
  rw [BackendRefinement.tpMatch_slots] at h
  exact matchSlots_nd _ h hm

theorem evalBgpFrom_nd {g : Graph} :
    ∀ (ps : Bgp) {mu : Binding}, Nd mu → ∀ nu ∈ evalBgpFrom g ps mu, Nd nu
  | [], _, hm, nu, hn => by simp [evalBgpFrom] at hn; subst hn; exact hm
  | tp :: rest, mu, hm, nu, hn => by
    simp only [evalBgpFrom, List.mem_flatMap, evalTP, List.mem_filterMap] at hn
    obtain ⟨m1, ⟨t, _, h1⟩, hn⟩ := hn
    exact evalBgpFrom_nd rest (tpMatch_nd h1 hm) nu hn

theorem evalBgpFromMuFuel_nd {gb : GraphBackend} :
    ∀ (n : Nat) (ps : Bgp) {mu : Binding}, Nd mu → ∀ nu ∈ evalBgpFromMuFuel ps gb mu n, Nd nu
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
        rw [BackendRefinement.evalBgpConcatMapAcc_eq]
        simp
      rw [e] at hn
      simp only [List.mem_flatMap, evalSingleTpBackend, List.mem_filterMap] at hn
      obtain ⟨m1, ⟨t, _, h1⟩, hn⟩ := hn
      exact evalBgpFromMuFuel_nd n rest (tpMatch_nd h1 hm) nu hn

/-! ## 7. The tightened relation -/

/-- **The answers SPARQL 1.1 allows, with the same pairs in each row.** The
    operators of `NativeFrag`, each the reference evaluator's own function
    (as in `Allowed`), FILTER and OPTIONAL with a `backendLocal` condition,
    and the rule `equiv` over `SolSEquiv` instead of `SolEquiv`. -/
inductive AllowedS (env : EvalEnv) (ds : Dataset) : QueryPattern → Graph → SolutionSeq → Prop
  | bgp (b : Bgp) (a : Graph) : AllowedS env ds (.bgp b) a (refSol env ds (.bgp b) a)
  | join {l r : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      AllowedS env ds l a A → AllowedS env ds r a B → AllowedS env ds (.join l r) a (join A B)
  | leftJoin {l r : QueryPattern} {c : Expr} {a : Graph} {A B : SolutionSeq} :
      c.backendLocal = true → AllowedS env ds l a A → AllowedS env ds r a B →
        AllowedS env ds (.leftJoin l r c) a (leftJoin A B (filterFn env c a))
  | filter {c : Expr} {q : QueryPattern} {a : Graph} {A : SolutionSeq} :
      c.backendLocal = true → AllowedS env ds q a A →
        AllowedS env ds (.filter c q) a (A.filter (filterFn env c a))
  | union {l r : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      AllowedS env ds l a A → AllowedS env ds r a B → AllowedS env ds (.union l r) a (A ++ B)
  | minus {l r : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      AllowedS env ds l a A → AllowedS env ds r a B → AllowedS env ds (.minus l r) a (minus A B)
  | graphIri {i : WfIri} {q : QueryPattern} {a g : Graph} {A : SolutionSeq} :
      ds.lookupNamedIri i.val = some g → AllowedS env ds q g A →
        AllowedS env ds (.graph (.iri i) q) a A
  | graphIriNone {i : WfIri} {q : QueryPattern} {a : Graph} :
      ds.lookupNamedIri i.val = none → AllowedS env ds (.graph (.iri i) q) a []
  | graphVar {v : VarName} {q : QueryPattern} {a : Graph} (F : NamedGraph → SolutionSeq) :
      (∀ ng ∈ ds.named, AllowedS env ds q ng.graph (F ng)) →
        AllowedS env ds (.graph (.var v) q) a
          (ds.named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
  | values (vars : List VarName) (rows : List (List (Option Term))) (a : Graph) :
      AllowedS env ds (.values vars rows) a (evalValues vars rows)
  | empty (a : Graph) : AllowedS env ds .empty a [Binding.empty]
  | equiv {p : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      AllowedS env ds p a A → SolSEquiv A B → AllowedS env ds p a B

/-- Every answer `AllowedS` admits is an answer `Allowed` admits. -/
theorem AllowedS.toAllowed {env : EvalEnv} {ds : Dataset} {p : QueryPattern} {a : Graph}
    {A : SolutionSeq} (h : AllowedS env ds p a A) : Allowed env ds p a A := by
  induction h with
  | bgp b a => exact .bgp b a
  | join _ _ ih1 ih2 => exact .join ih1 ih2
  | leftJoin _ _ _ ih1 ih2 => exact .leftJoin ih1 ih2
  | filter _ _ ih => exact .filter ih
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | minus _ _ ih1 ih2 => exact .minus ih1 ih2
  | graphIri hg _ ih => exact .graphIri hg ih
  | graphIriNone hg => exact .graphIriNone hg
  | graphVar F _ ih => exact .graphVar F ih
  | values vars rows a => exact .values vars rows a
  | empty a => exact .empty a
  | equiv _ hs ih => exact .equiv ih hs.toSolEquiv

/-- Every pattern of `NativeFrag` is in the fragment of `allowed_ref`. -/
theorem nativeFrag_inIdFragment : ∀ (p : QueryPattern), NativeFrag p → InIdFragment p
  | .bgp _, _ => trivial
  | .filter _ q, hp => nativeFrag_inIdFragment q hp.2
  | .leftJoin l r _, hp => ⟨nativeFrag_inIdFragment l hp.2.1, nativeFrag_inIdFragment r hp.2.2⟩
  | .join l r, hp => ⟨nativeFrag_inIdFragment l hp.1, nativeFrag_inIdFragment r hp.2⟩
  | .union l r, hp => ⟨nativeFrag_inIdFragment l hp.1, nativeFrag_inIdFragment r hp.2⟩
  | .minus l r, hp => ⟨nativeFrag_inIdFragment l hp.1, nativeFrag_inIdFragment r hp.2⟩
  | .graph (.iri _) q, hp => nativeFrag_inIdFragment q hp
  | .graph (.var _) q, hp => nativeFrag_inIdFragment q hp
  | .empty, _ => trivial
  | .values _ _, _ => trivial

open L4Factoidal.Storage.Sbm11.IdGroup (refSol_join_eq refSol_leftJoin_eq refSol_filter_eq
  refSol_union_eq refSol_minus_eq refSol_graphIri_eq refSol_graphVar_eq refSol_values_eq
  refSol_empty_eq)

/-- **Every answer `AllowedS` admits is the reference answer up to the order
    of the solutions** (`SolSEquiv`), for a pattern of the fragment of
    `allowed_ref`. -/
theorem AllowedS.ref {env : EvalEnv} {ds : Dataset} {p : QueryPattern} {a : Graph}
    {A : SolutionSeq} (h : AllowedS env ds p a A) (hp : InIdFragment p) :
    SolSEquiv A (refSol env ds p a) := by
  induction h with
  | bgp b a => exact SolSEquiv.refl _
  | join _ _ ih1 ih2 =>
    rw [refSol_join_eq env ds _ hp.1 hp.2]
    exact join_congr (ih1 hp.1) (ih2 hp.2)
  | @leftJoin l r c a A B hc _ _ ih1 ih2 =>
    rw [refSol_leftJoin_eq]
    exact leftJoin_congr _ (filterFn_condOk env hc a) (ih1 hp.1) (ih2 hp.2)
  | @filter c q a A hc _ ih =>
    rw [refSol_filter_eq]
    exact filter_congr _ (filterFn_condOk env hc a) (ih hp)
  | union _ _ ih1 ih2 =>
    rw [refSol_union_eq]
    exact union_congr (ih1 hp.1) (ih2 hp.2)
  | minus _ _ ih1 ih2 =>
    rw [refSol_minus_eq]
    exact minus_congr (ih1 hp.1) (ih2 hp.2)
  | graphIri hg _ ih =>
    rw [refSol_graphIri_eq, hg]
    exact ih hp
  | graphIriNone hg =>
    rw [refSol_graphIri_eq, hg]
    exact SolSEquiv.refl _
  | graphVar F _ ih =>
    rw [refSol_graphVar_eq]
    exact graphVar_congr _ _ _ _ fun ng hng => ih ng hng hp
  | values vars rows a =>
    rw [refSol_values_eq]
    exact SolSEquiv.refl _
  | empty a =>
    rw [refSol_empty_eq]
    exact SolSEquiv.refl _
  | equiv _ hs ih => exact SolSEquiv.trans hs.symm (ih hp)

/-- **Two answers `AllowedS` admits for one pattern are one multiset**
    (`SolSEquiv`), for a pattern of the fragment of `allowed_ref`. -/
theorem AllowedS.unique {env : EvalEnv} {ds : Dataset} {p : QueryPattern} {a : Graph}
    {A B : SolutionSeq} (hA : AllowedS env ds p a A) (hB : AllowedS env ds p a B)
    (hp : InIdFragment p) : SolSEquiv A B :=
  SolSEquiv.trans (hA.ref hp) (hB.ref hp).symm

/-- **The reference answer is one `AllowedS` admits**, for every pattern of
    `NativeFrag`. -/
theorem allowedS_ref (env : EvalEnv) (ds : Dataset) :
    ∀ (p : QueryPattern) (a : Graph), NativeFrag p → AllowedS env ds p a (refSol env ds p a)
  | .bgp b, a, _ => .bgp b a
  | .filter c q, a, hp => by
    rw [refSol_filter_eq]
    exact .filter hp.1 (allowedS_ref env ds q a hp.2)
  | .leftJoin l r c, a, hp => by
    rw [refSol_leftJoin_eq]
    exact .leftJoin hp.1 (allowedS_ref env ds l a hp.2.1) (allowedS_ref env ds r a hp.2.2)
  | .join l r, a, hp => by
    rw [refSol_join_eq env ds a (nativeFrag_inIdFragment l hp.1) (nativeFrag_inIdFragment r hp.2)]
    exact .join (allowedS_ref env ds l a hp.1) (allowedS_ref env ds r a hp.2)
  | .union l r, a, hp => by
    rw [refSol_union_eq]
    exact .union (allowedS_ref env ds l a hp.1) (allowedS_ref env ds r a hp.2)
  | .minus l r, a, hp => by
    rw [refSol_minus_eq]
    exact .minus (allowedS_ref env ds l a hp.1) (allowedS_ref env ds r a hp.2)
  | .graph (.iri i) q, a, hp => by
    rw [refSol_graphIri_eq]
    cases hg : ds.lookupNamedIri i.val with
    | none => exact .graphIriNone hg
    | some g => exact .graphIri hg (allowedS_ref env ds q g hp)
  | .graph (.var v) q, a, hp => by
    rw [refSol_graphVar_eq]
    exact .graphVar (fun ng => refSol env ds q ng.graph) fun ng _ => allowedS_ref env ds q ng.graph hp
  | .empty, a, _ => by
    rw [refSol_empty_eq]
    exact .empty a
  | .values vars rows, a, _ => by
    rw [refSol_values_eq]
    exact .values vars rows a

/-! ## 8. The backend's answer -/

/-- The backend's answer to a basic graph pattern with no `text:query`
    pattern is one `AllowedS` admits: backend and reference rows have
    distinct names, so `SolEquiv` gives `SolSEquiv`. -/
theorem evalBgpBackend_allowedS (env : EvalEnv) (ds : Dataset) {gb : GraphBackend} {a : Graph}
    (hr : GraphRel gb a) (b : Bgp) (hf : bgpHasFulltext b = false) :
    AllowedS env ds (.bgp b) a (evalBgpBackend b gb) := by
  refine .equiv (.bgp b a) ?_
  rw [Storage.Sbm11.IdLeaf.refSol_bgp env ds b a hf]
  refine solSEquiv_of_nd
    (SolEquiv.symm (BackendRefinement.evalBgpBackend_solEquiv hr.exact hr.keyNodup (fun _ => Iff.rfl) b))
    (fun mu hm => evalBgpFrom_nd b nd_empty mu hm)
    (fun mu hm => evalBgpFromMuFuel_nd _ b nd_empty mu hm)

/-- **The backend evaluator's WHERE answer is one `AllowedS` admits**, for
    every pattern of `NativeFrag`, under the premises of
    `evalPatternBackend_allowed`. -/
theorem evalPatternBackend_allowedS (env : EvalEnv) (dsb : DatasetBackend) (ds : Dataset)
    (hn : NamedRel dsb.named ds.named) (hnd : (dsb.named.map (·.name)).Nodup) :
    ∀ (p : QueryPattern), NativeFrag p → ∀ (gb : GraphBackend) (a : Graph), GraphRel gb a →
      AllowedS env ds p a (evalPatternBackend env dsb p gb)
  | .bgp b, hp, gb, a, hr => by
    rw [evalPatternBackend_bgp_native]
    exact evalBgpBackend_allowedS env ds hr b hp
  | .filter c q, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.filter c q) gb =
        (evalPatternBackend env dsb q gb).filter (fun row => ebvOrFalse (Expr.evalIn env row c)) := by
      simp [evalPatternBackend, hp.1]
    rw [e, ← BackendRefinement.filterFn_local env hp.1 a]
    exact .filter hp.1 (evalPatternBackend_allowedS env dsb ds hn hnd q hp.2 gb a hr)
  | .leftJoin l r c, hp, gb, a, hr => by
    rw [evalPatternBackend_leftJoin_spec env dsb l r c gb hp.1, ← BackendRefinement.filterFn_local env hp.1 a]
    exact .leftJoin hp.1 (evalPatternBackend_allowedS env dsb ds hn hnd l hp.2.1 gb a hr)
      (evalPatternBackend_allowedS env dsb ds hn hnd r hp.2.2 gb a hr)
  | .join l r, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.join l r) gb =
        SPARQL.hashJoin (evalPatternBackend env dsb l gb) (evalPatternBackend env dsb r gb) := by
      simp [evalPatternBackend]
    rw [e, SPARQL.hashJoin_eq_join]
    exact .join (evalPatternBackend_allowedS env dsb ds hn hnd l hp.1 gb a hr)
      (evalPatternBackend_allowedS env dsb ds hn hnd r hp.2 gb a hr)
  | .union l r, hp, gb, a, hr => by
    rw [evalPatternBackend_union_native]
    exact .union (evalPatternBackend_allowedS env dsb ds hn hnd l hp.1 gb a hr)
      (evalPatternBackend_allowedS env dsb ds hn hnd r hp.2 gb a hr)
  | .minus l r, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.minus l r) gb =
        SPARQL.hashMinus (evalPatternBackend env dsb l gb) (evalPatternBackend env dsb r gb) := by
      simp [evalPatternBackend]
    rw [e, SPARQL.hashMinus_eq_minus]
    exact .minus (evalPatternBackend_allowedS env dsb ds hn hnd l hp.1 gb a hr)
      (evalPatternBackend_allowedS env dsb ds hn hnd r hp.2 gb a hr)
  | .graph (.iri i) q, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.graph (.iri i) q) gb =
        match lookupNamedBackend i.val dsb.named with
        | some g => evalPatternBackend env dsb q g
        | none => [] := rfl
    rw [e]
    rcases BackendRefinement.lookup_rel i hn with ⟨h1, h2⟩ | ⟨gb', g, h1, h2, hr'⟩
    · rw [h1]
      exact .graphIriNone (by rw [BackendRefinement.lookupNamedIri_wf]; exact h2)
    · rw [h1]
      exact .graphIri (by rw [BackendRefinement.lookupNamedIri_wf]; exact h2)
        (evalPatternBackend_allowedS env dsb ds hn hnd q hp gb' g hr')
  | .graph (.var v) q, hp, gb, a, hr => by
    have e : evalPatternBackend env dsb (.graph (.var v) q) gb =
        dsb.named.flatMap (fun ngb => (evalPatternBackend env dsb q ngb.backend).filterMap
          (fun mu => mu.bindIfCompatible v ngb.name.toTerm)) := rfl
    rw [e, BackendRefinement.graphVar_eq env dsb q v hn
      (fun x hx => BackendRefinement.lookupNamedSubject_of_mem hnd hx)]
    refine .graphVar (fun ng => evalPatternBackend env dsb q
      (BackendRefinement.backendFor dsb.named ng.name)) ?_
    intro ng hng
    obtain ⟨ngb, hngb, e1, hr'⟩ := BackendRefinement.namedRel_mem hn hng
    have hbk : BackendRefinement.backendFor dsb.named ng.name = ngb.backend := by
      simp only [BackendRefinement.backendFor]
      rw [← e1, BackendRefinement.lookupNamedSubject_of_mem hnd hngb]
      rfl
    rw [hbk]
    exact evalPatternBackend_allowedS env dsb ds hn hnd q hp ngb.backend ng.graph hr'
  | .empty, _, gb, a, _ => by
    rw [evalPatternBackend_empty]
    exact .empty a
  | .values vs rows, _, gb, a, _ => by
    rw [evalPatternBackend_values_native]
    exact .values vs rows a

/-- **The backend evaluator's WHERE answer is the reference answer up to the
    order of the solutions** (`SolSEquiv`: the same multiset of solution
    mappings, each with the same pairs), for every pattern of `NativeFrag`. -/
theorem evalPatternBackend_ref (env : EvalEnv) (dsb : DatasetBackend) (ds : Dataset)
    (hn : NamedRel dsb.named ds.named) (hnd : (dsb.named.map (·.name)).Nodup)
    (p : QueryPattern) (hp : NativeFrag p) (gb : GraphBackend) (a : Graph) (hr : GraphRel gb a) :
    SolSEquiv (evalPatternBackend env dsb p gb) (refSol env ds p a) :=
  (evalPatternBackend_allowedS env dsb ds hn hnd p hp gb a hr).ref (nativeFrag_inIdFragment p hp)


/-! ## 9. The order-free part of the solution-modifier layer

SPARQL 1.1 fixes no order of the solutions without ORDER BY and none among
the solutions ORDER BY does not separate (section 15.1). A slice (OFFSET,
LIMIT), DISTINCT and REDUCED (which keep the first of the duplicates), an
order-sensitive aggregate (GROUP_CONCAT, SAMPLE) and a SELECT expression
that reads the row index (BNODE(), UUID(), STRUUID()) therefore have more
than one correct answer on one multiset of WHERE solutions. The theorems
below cover the modifiers that do not read the order: for ASK, no GROUP BY
and no HAVING; for SELECT, no GROUP BY, no aggregate, no SELECT expression,
no DISTINCT, no REDUCED, no OFFSET, no LIMIT; ORDER BY and a trailing VALUES
clause allowed. -/

theorem isEmpty_of_length {α : Type} : ∀ {X Y : List α}, X.length = Y.length → X.isEmpty = Y.isEmpty
  | [], [], _ => rfl
  | _ :: _, _ :: _, _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem sliceSolutions_length (o l : Option Nat) {X Y : SolutionSeq} (h : X.length = Y.length) :
    (sliceSolutions o l X).length = (sliceSolutions o l Y).length := by
  cases o <;> cases l <;> simp [sliceSolutions, h]

/-- ASK with no GROUP BY and no HAVING: the answer depends on the number of
    WHERE solutions only. -/
theorem formHasSolution_congr (env : EvalEnv) (a : Graph) (q : Query) (hg : q.groupsSolutions = false)
    {A A' : SolutionSeq} (h : SolSEquiv A A') :
    formHasSolution env a q A = formHasSolution env a q A' := by
  unfold formHasSolution formRows
  rw [hg]
  simp only [Bool.false_eq_true, if_false]
  congr 1
  apply isEmpty_of_length
  apply sliceSolutions_length
  cases q.postValues with
  | none => exact h.length_eq
  | some vals => exact (join_congr h (SolSEquiv.refl vals)).length_eq

theorem lookup_filterKey (k : VarName → Bool) (v : VarName) :
    ∀ (mu : Binding), Binding.lookup v (mu.filter (fun p => k p.1)) = if k v then mu.lookup v else none
  | [] => by simp [Binding.lookup]
  | (w, t) :: rest => by
    simp only [List.filter_cons]
    by_cases e : w = v
    · subst e
      by_cases hk : k w <;> simp [hk, Binding.lookup, lookup_filterKey k w rest]
    · by_cases hk : k w <;> simp [hk, Binding.lookup, e, lookup_filterKey k v rest]

theorem rowS_filterKey (k : VarName → Bool) {mu nu : Binding} (h : RowS mu nu) :
    RowS (mu.filter (fun p => k p.1)) (nu.filter (fun p => k p.1)) := by
  refine ⟨fun v => ?_, fun p => ?_⟩
  · rw [lookup_filterKey, lookup_filterKey, h.1 v]
  · simp only [List.mem_filter, h.2 p]

theorem projectBinding_eq_filter (vars : List VarName) :
    ∀ (mu : Binding), projectBinding vars mu = mu.filter (fun p => vars.contains p.1)
  | [] => rfl
  | (v, t) :: rest => by
    simp only [projectBinding, List.filter_cons, projectBinding_eq_filter vars rest]

/-- No SELECT expression: every item is a variable. -/
def itemsPlain : List SelectItem → Bool
  | [] => true
  | .var _ :: rest => itemsPlain rest
  | .expr _ _ :: _ => false

/-- No SELECT expression in the SELECT clause. -/
def selectPlain : SelectClause → Bool
  | .all => true
  | .vars items => itemsPlain items

theorem evalSelectItemsRowFrom_plain (env : EvalEnv) (a : Graph) (row : String) :
    ∀ (items : List SelectItem), itemsPlain items = true → ∀ (mu : Binding) (i : Nat),
      evalSelectItemsRowFrom env a row items mu i = mu
  | [], _, _, _ => rfl
  | .var _ :: rest, h, mu, i => by
    simp only [evalSelectItemsRowFrom]
    exact evalSelectItemsRowFrom_plain env a row rest h mu (i + 1)
  | .expr _ _ :: _, h, _, _ => by simp [itemsPlain] at h

theorem numberRows_id (f : String → Binding → Binding) (hf : ∀ row mu, f row mu = mu) :
    ∀ (omega : SolutionSeq) (i : Nat), numberRows f omega i = omega
  | [], _ => rfl
  | mu :: rest, i => by simp only [numberRows, hf, numberRows_id f hf rest (i + 1)]

/-- The SELECT modifiers that do not read the order of the solutions. -/
def SelectOrderFree (q : Query) (sel : SelectClause) : Prop :=
  q.groupBy = none ∧ selectHasAggregates sel = false ∧ selectPlain sel = true ∧
    q.modifier.distinct = false ∧ q.modifier.reduced = false ∧ q.modifier.offset = none ∧
    q.modifier.limit = none

theorem finishSelectRows_plain (order : Option (Binding → Binding → Int)) (project : Binding → Binding)
    (rows : SolutionSeq) :
    finishSelectRows order project false false none none rows =
      (match order with
       | none => rows
       | some cmp => sortSolutionsFast cmp rows).map project := by
  cases order <;> rfl

theorem finishSelectRows_congr (order : Option (Binding → Binding → Int)) (k : VarName → Bool)
    {X Y : SolutionSeq} (h : SolSEquiv X Y) :
    SolSEquiv (finishSelectRows order (fun mu => mu.filter (fun p => k p.1)) false false none none X)
      (finishSelectRows order (fun mu => mu.filter (fun p => k p.1)) false false none none Y) := by
  rw [finishSelectRows_plain, finishSelectRows_plain]
  have ho : SolSEquiv (match order with | none => X | some cmp => sortSolutionsFast cmp X)
      (match order with | none => Y | some cmp => sortSolutionsFast cmp Y) := by
    cases order with
    | none => exact h
    | some cmp =>
      exact SolSEquiv.trans (SolSEquiv.of_perm (List.mergeSort_perm X _))
        (SolSEquiv.trans h (SolSEquiv.of_perm (List.mergeSort_perm Y _).symm))
  exact PermPw.map _ (fun hab => rowS_filterKey k hab) ho

/-- **SELECT with order-free modifiers: one multiset of WHERE solutions
    gives one multiset of rows** (`SolSEquiv`). -/
theorem selectPost_congr (env : EvalEnv) (a : Graph) (q : Query) (sel : SelectClause)
    (hform : q.form = .select sel) (hof : SelectOrderFree q sel) {A A' : SolutionSeq}
    (h : SolSEquiv A A') : SolSEquiv (selectPost env a q A) (selectPost env a q A') := by
  obtain ⟨hgb, hagg, hpl, hdd, hrr, hoo, hll⟩ := hof
  cases q with
  | mk form dcs pat gb hv md pv base =>
    cases md with
    | mk ob dd rr oo ll =>
      simp only [Query.form] at hform
      subst hform
      simp only [Query.groupBy, Query.modifier] at hgb hdd hrr hoo hll
      subst hgb hdd hrr hoo hll
      have hw : SolSEquiv (match pv with | none => A | some vals => join A vals)
          (match pv with | none => A' | some vals => join A' vals) := by
        cases pv with
        | none => exact h
        | some vals => exact join_congr h (SolSEquiv.refl vals)
      cases sel with
      | all =>
        unfold selectPost
        dsimp only
        rw [if_neg (by simp [hagg])]
        cases ob <;> exact finishSelectRows_congr _ (fun v => !isSyntheticBnodeVar v) hw
      | vars items =>
        unfold selectPost
        dsimp only
        have hc : ¬ (((none : Option (List GroupCondition)).isSome ||
            selectHasAggregates (.vars items)) = true) := by simp [hagg]
        rw [if_neg hc, if_neg hc]
        have hid := numberRows_id (fun row mu => evalSelectItemsRowFrom env a row items mu 0)
          (fun row mu => evalSelectItemsRowFrom_plain env a row items hpl mu 0)
        rw [hid, hid]
        have hp : projectBinding (selectItemVars items) =
            fun mu => mu.filter (fun p => (selectItemVars items).contains p.1) :=
          funext (projectBinding_eq_filter _)
        rw [hp]
        cases ob <;> exact finishSelectRows_congr _ (fun v => (selectItemVars items).contains v) hw

#print axioms allowed_not_unique
#print axioms join_congr
#print axioms leftJoin_congr
#print axioms minus_congr
#print axioms graphVar_congr
#print axioms AllowedS.toAllowed
#print axioms AllowedS.ref
#print axioms AllowedS.unique
#print axioms allowedS_ref
#print axioms evalPatternBackend_allowedS
#print axioms evalPatternBackend_ref
#print axioms formHasSolution_congr
#print axioms selectPost_congr

end L4Factoidal.Storage.BackendAgreement
