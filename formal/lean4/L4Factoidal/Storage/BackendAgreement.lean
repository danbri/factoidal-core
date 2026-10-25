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

namespace L4Factoidal.Storage.BackendAgreement

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
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

#print axioms allowed_not_unique
#print axioms join_congr
#print axioms leftJoin_congr
#print axioms minus_congr
#print axioms graphVar_congr

end L4Factoidal.Storage.BackendAgreement
