/-
L4Factoidal.Storage.Sbm11.ScopeTheorems — the variables an allowed answer
binds are in scope (SPARQL 1.1 section 18.2.1), and the rows of a `SELECT *`
sub-SELECT bind only its projected variables
(https://github.com/danbri/factoidal/issues/776; lemma L4w of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md, the `SELECT *` case).

* `allowed_keys`: every row of an answer that SPARQL 1.1 allows for a
  pattern (`IdGroup.Allowed`) binds only variables in scope of the pattern
  (`QueryPattern.inScopeVars`), for a pattern whose basic graph patterns
  have no `text:query` pattern and whose `SELECT *` sub-SELECTs have no
  GROUP BY (`ScopeOk`). By induction on `Allowed`: the leaves
  (`IdExists.evalBgpFrom_dom`, `pathResultToSolutions`), the merge of two
  rows (`merge_keys`), the binding of one variable (`bindIfCompatible`,
  `bindRowsFresh`), VALUES (`zipBindings`), the sub-SELECT
  (`SubSelect.selectPost_dom`, `selectPost_all_keys`), and the same multiset
  of solution mappings in another order (`Allowed.equiv`, `keys_solEquiv`).
* `selectPost_all_keys`: the rows of `selectPost` of `SELECT *` with no
  GROUP BY over rows whose variables are in scope of the WHERE clause bind
  only the variables `Query.projectedVars` gives (`finishSelectRows_mem'`:
  every output row is the projection of an input row).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.SubSelectTableTheorems
import L4Factoidal.Storage.Sbm11.IdExistsTheorems
import L4Factoidal.Storage.Sbm11.IdAllowedTheorems
import L4Factoidal.SPARQL.ProjectionTheorems

set_option linter.unusedSimpArgs false

namespace L4Factoidal.Storage.Sbm11.ScopeTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdGroup (Allowed refSol SolEquiv BindEq PermPw Pw)

/-- Every row of `A` binds only variables of `S`. -/
def KeysIn (S : List VarName) (A : SolutionSeq) : Prop := ∀ mu ∈ A, ∀ p ∈ mu, p.1 ∈ S

theorem keysIn_mono {S T : List VarName} (h : ∀ v ∈ S, v ∈ T) {A : SolutionSeq} (hA : KeysIn S A) :
    KeysIn T A := fun mu hmu p hp => h _ (hA mu hmu p hp)

/-! ## Rows -/

theorem merge_keys : ∀ (mu1 mu2 : Binding), ∀ p ∈ mu1.merge mu2, p ∈ mu1 ∨ p ∈ mu2
  | mu1, [], p, hp => Or.inl hp
  | mu1, (v, t) :: rest, p, hp => by
    simp only [Binding.merge] at hp
    split at hp
    · rcases merge_keys mu1 rest p hp with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases merge_keys ((v, t) :: mu1) rest p hp with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem keys_join {S T : List VarName} {A B : SolutionSeq} (hA : KeysIn S A) (hB : KeysIn T B) :
    KeysIn (S ++ T) (join A B) := by
  intro mu hmu p hp
  simp only [join, List.mem_flatMap, List.mem_filterMap] at hmu
  obtain ⟨mu1, h1, mu2, h2, e⟩ := hmu
  split at e
  · cases e
    rcases merge_keys mu1 mu2 p hp with h | h
    · exact List.mem_append_left _ (hA mu1 h1 p h)
    · exact List.mem_append_right _ (hB mu2 h2 p h)
  · cases e

theorem keys_leftJoin {S T : List VarName} {A B : SolutionSeq} (hA : KeysIn S A) (hB : KeysIn T B)
    (cond : Binding → Bool) : KeysIn (S ++ T) (leftJoin A B cond) := by
  intro mu hmu p hp
  simp only [leftJoin, List.mem_flatMap] at hmu
  obtain ⟨mu1, h1, hm⟩ := hmu
  split at hm
  · rw [List.mem_singleton] at hm
    subst hm
    exact List.mem_append_left _ (hA _ h1 p hp)
  · rw [List.mem_filterMap] at hm
    obtain ⟨mu2, h2, e⟩ := hm
    split at e
    · split at e
      · cases e
        rcases merge_keys mu1 mu2 p hp with h | h
        · exact List.mem_append_left _ (hA mu1 h1 p h)
        · exact List.mem_append_right _ (hB mu2 h2 p h)
      · cases e
    · cases e

theorem keys_filter {S : List VarName} {A : SolutionSeq} (hA : KeysIn S A) (f : Binding → Bool) :
    KeysIn S (A.filter f) := fun mu hmu p hp => hA mu (List.mem_filter.mp hmu).1 p hp

theorem keys_bindIfCompatible (v : VarName) (t : Term) (mu nu : Binding)
    (h : Binding.bindIfCompatible v t mu = some nu) : ∀ p ∈ nu, p.1 = v ∨ p ∈ mu := by
  intro p hp
  simp only [Binding.bindIfCompatible] at h
  split at h
  · split at h
    · cases h; exact Or.inr hp
    · cases h
  · cases h
    simp only [Binding.bind, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · exact Or.inr hp

theorem keys_bindRowsFresh (binder : Graph → Binding → Option Term) (a : Graph) (v : VarName) {S : List VarName} :
    ∀ (A : SolutionSeq) (i : Nat), KeysIn S A → KeysIn (S ++ [v]) (bindRowsFresh binder a v A i)
  | [], _, _ => fun mu hmu => by cases hmu
  | mu :: rest, i, hA => by
    intro nu hnu p hp
    simp only [bindRowsFresh, List.mem_cons] at hnu
    rcases hnu with rfl | hnu
    · split at hp
      · split at hp
        · exact List.mem_append_left _ (hA mu List.mem_cons_self p hp)
        · simp only [Binding.bind, List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp
          · exact List.mem_append_left _ (hA mu List.mem_cons_self p hp)
      · exact List.mem_append_left _ (hA mu List.mem_cons_self p hp)
    · exact keys_bindRowsFresh binder a v rest (i + 1) (fun m hm => hA m (List.mem_cons_of_mem _ hm)) nu hnu p hp

theorem keys_zipBindings : ∀ (vars : List VarName) (row : List (Option Term)) (mu : Binding),
    ∀ p ∈ zipBindings vars row mu, p ∈ mu ∨ p.1 ∈ vars
  | [], _, mu, p, hp => by simp [zipBindings] at hp; exact Or.inl hp
  | _ :: _, [], mu, p, hp => by simp [zipBindings] at hp; exact Or.inl hp
  | v :: vs, some t :: ts, mu, p, hp => by
    simp only [zipBindings] at hp
    rcases keys_zipBindings vs ts (mu.bind v t) p hp with h | h
    · simp only [Binding.bind, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr List.mem_cons_self
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  | v :: vs, none :: ts, mu, p, hp => by
    simp only [zipBindings] at hp
    rcases keys_zipBindings vs ts mu p hp with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem keys_evalValues (vars : List VarName) (rows : List (List (Option Term))) :
    KeysIn vars (evalValues vars rows) := by
  intro mu hmu p hp
  simp only [evalValues, List.mem_map] at hmu
  obtain ⟨row, _, rfl⟩ := hmu
  rcases keys_zipBindings vars row Binding.empty p hp with h | h
  · simp [Binding.empty] at h
  · exact h

theorem lookup_isSome_of_mem : ∀ {mu : Binding} {p : VarName × Term}, p ∈ mu → (mu.lookup p.1).isSome = true
  | [], _, h => by cases h
  | (w, u) :: rest, p, h => by
    simp only [Binding.lookup]
    split
    · rfl
    · next hw =>
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hw
      · exact lookup_isSome_of_mem h

/-- A row of the same solution mapping binds the same variables. -/
theorem keys_solEquiv {S : List VarName} {A B : SolutionSeq} (hA : KeysIn S A) (h : SolEquiv A B) :
    KeysIn S B := by
  obtain ⟨C, hp, hw⟩ := h
  have hC : KeysIn S C := fun mu hmu => hA mu (hp.mem_iff.mpr hmu)
  clear hA hp
  induction hw with
  | nil => intro mu hmu; cases hmu
  | @cons a b l l' hab _ ih =>
    intro mu hmu p hpm
    rcases List.mem_cons.mp hmu with rfl | hmu
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem hpm)
      rw [← hab p.1] at ht
      exact hC a List.mem_cons_self (p.1, t) (IdExists.lookup_mem ht)
    · exact ih (fun m hm => hC m (List.mem_cons_of_mem _ hm)) mu hmu p hpm

/-! ## The leaves -/

theorem patternTermVars_eq : ∀ (t : PatternTerm), Unified.patternTermVars t = projectionTermVars t
  | .var _ => rfl
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal _ => rfl
  | .tripleTerm s p o => by
    simp only [Unified.patternTermVars, projectionTermVars, patternTermVars_eq s, patternTermVars_eq p,
      patternTermVars_eq o]

theorem patternSubjectVars_eq : ∀ (s : PatternSubject), Unified.patternSubjectVars s = projectionSubjectVars s
  | .var _ => rfl
  | .iri _ => rfl
  | .bnode _ => rfl
  | .tripleTerm s p o => by
    simp only [Unified.patternSubjectVars, projectionSubjectVars, patternTermVars_eq s, patternTermVars_eq p,
      patternTermVars_eq o]

theorem keys_evalBgp (b : Bgp) (a : Graph) : KeysIn (QueryPattern.bgp b).inScopeVars (evalBgp b a) := by
  intro mu hmu p hp
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem hp)
  rcases IdExists.evalBgpFrom_dom a b hmu hu with h | h
  · simp [Binding.empty, Binding.lookup] at h
  · simp only [QueryPattern.inScopeVars]
    simp only [Unified.bgpVars, Unified.tpVars, List.mem_flatMap] at h
    obtain ⟨tp, htp, hv⟩ := h
    rw [patternSubjectVars_eq, patternTermVars_eq, patternTermVars_eq] at hv
    exact List.mem_flatMap.mpr ⟨tp, htp, hv⟩

theorem keys_pathResult (ps : PatternSubject) (pt : PatternTerm) (pairs : PathResult) :
    KeysIn (projectionSubjectVars ps ++ projectionTermVars pt) (pathResultToSolutions ps pt pairs) := by
  intro mu hmu p hp
  simp only [pathResultToSolutions, List.mem_filterMap] at hmu
  obtain ⟨pr, _, e⟩ := hmu
  cases ps <;> cases pt <;> simp only [] at e <;> (repeat' split at e) <;>
    simp_all [projectionSubjectVars, projectionTermVars] <;>
    (try (subst_vars; simp_all)) <;>
    (try (rcases hp with h | h <;> simp_all))

/-! ## `finishSelectRows` and `SELECT *` -/

/-- Every row of `finishSelectRows` is the projection of an input row. -/
theorem finishSelectRows_mem' (order : Option (Binding → Binding → Int)) (project : Binding → Binding)
    (dd rr : Bool) (oo ll : Option Nat) (rows : SolutionSeq) :
    ∀ mu ∈ finishSelectRows order project dd rr oo ll rows, ∃ nu ∈ rows, mu = project nu := by
  intro mu hmu
  unfold finishSelectRows sliceSolutions at hmu
  have hslice : ∀ (L : SolutionSeq), mu ∈ (match ll with
      | none => (match oo with | none => L | some n => L.drop n)
      | some n => (match oo with | none => L | some n => L.drop n).take n) → mu ∈ L := by
    intro L h
    cases ll <;> cases oo <;> simp at h
    all_goals first
      | exact h
      | exact List.mem_of_mem_drop h
      | exact List.mem_of_mem_take h
      | exact List.mem_of_mem_drop (List.mem_of_mem_take h)
  have h1 := hslice _ hmu
  have h2 : mu ∈ (match order with | none => rows | some cmp => sortSolutionsFast cmp rows).map project := by
    split at h1
    · rw [distinctSolutionsFast_eq] at h1
      exact mem_of_mem_distinctSolutions h1
    · split at h1
      · exact h1
      · exact h1
  obtain ⟨nu, hnu, e⟩ := List.mem_map.mp h2
  refine ⟨nu, ?_, e.symm⟩
  split at hnu
  · exact hnu
  · exact (List.mergeSort_perm _ _).mem_iff.mp hnu

/-- **The rows of `SELECT *` with no GROUP BY.** Over rows whose variables are
    in scope of the WHERE clause, every row of `selectPost` binds only the
    variables `Query.projectedVars` gives: those in scope of the WHERE clause
    and those of the trailing VALUES. -/
theorem selectPost_all_keys (env : EvalEnv) (a : Graph) (dcs : List DatasetClause) (inner : QueryPattern)
    (hv : List Expr) (md : SolutionModifier) (pv : Option (List Binding)) (bs : Option String)
    (A : SolutionSeq) (hA : KeysIn inner.inScopeVars A) :
    KeysIn (Query.projectedVars (.mk (.select .all) dcs inner none hv md pv bs))
      (selectPost env a (.mk (.select .all) dcs inner none hv md pv bs) A) := by
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  have hW : KeysIn (inner.inScopeVars ++ (pv.getD []).flatMap (fun row => row.map Prod.fst))
      (match pv with | none => A | some vals => join A vals) := by
    cases pv with
    | none => exact keysIn_mono (fun v hv => List.mem_append_left _ hv) hA
    | some vals =>
      apply keys_join hA
      intro mu hmu p hp
      exact List.mem_flatMap.mpr ⟨mu, hmu, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  intro mu hmu p hp
  simp only [Query.projectedVars]
  rw [List.mem_eraseDups]
  unfold selectPost at hmu
  simp only [Option.isSome_none, selectHasAggregates, Bool.false_or, Bool.false_eq_true, if_false] at hmu
  have key : ∃ nu ∈ (match pv with | none => A | some vals => join A vals),
      mu = nu.filter (fun b => !isSyntheticBnodeVar b.1) := by
    split at hmu
    · exact finishSelectRows_mem' _ _ _ _ _ _ _ mu hmu
    · exact finishSelectRows_mem' _ _ _ _ _ _ _ mu hmu
  obtain ⟨nu, hnu, rfl⟩ := key
  exact hW nu hnu p (List.mem_filter.mp hp).1

/-! ## The answers SPARQL 1.1 allows bind only variables in scope -/

/-- The patterns `allowed_keys` is proved for: basic graph patterns with no
    `text:query` pattern, and `SELECT *` sub-SELECTs with no GROUP BY, at any
    depth. -/
def ScopeOk : QueryPattern → Prop
  | .bgp b => bgpHasFulltext b = false
  | .join l r => ScopeOk l ∧ ScopeOk r
  | .leftJoin l r _ => ScopeOk l ∧ ScopeOk r
  | .filter _ q => ScopeOk q
  | .union l r => ScopeOk l ∧ ScopeOk r
  | .minus l _ => ScopeOk l
  | .graph _ q => ScopeOk q
  | .bind _ _ q => ScopeOk q
  | .subSelect (.mk form _ inner gb _ _ _ _) => form = .select .all → gb = none ∧ ScopeOk inner
  | _ => True

/-- **Every row of an allowed answer binds only variables in scope** (SPARQL
    1.1 section 18.2.1), for a pattern that is `ScopeOk`. -/
theorem allowed_keys (env : EvalEnv) (ds : Dataset) {p : QueryPattern} {a : Graph} {A : SolutionSeq}
    (h : Allowed env ds p a A) : ScopeOk p → KeysIn p.inScopeVars A := by
  induction h with
  | bgp b a =>
    intro hs
    rw [IdLeaf.refSol_bgp env ds b a hs]
    exact keys_evalBgp b a
  | path s path o a =>
    intro _
    rw [IdLeaf.refSol_path]
    exact keys_pathResult s o _
  | join _ _ ih1 ih2 =>
    intro hs
    exact keys_join (ih1 hs.1) (ih2 hs.2)
  | leftJoin _ _ ih1 ih2 =>
    intro hs
    exact keys_leftJoin (ih1 hs.1) (ih2 hs.2) _
  | filter _ ih =>
    intro hs
    exact keys_filter (ih hs) _
  | union _ _ ih1 ih2 =>
    intro hs mu hmu p hp
    rcases List.mem_append.mp hmu with h | h
    · exact List.mem_append_left _ (ih1 hs.1 mu h p hp)
    · exact List.mem_append_right _ (ih2 hs.2 mu h p hp)
  | minus _ _ ih1 _ =>
    intro hs
    exact keys_filter (ih1 hs) _
  | graphIri _ _ ih =>
    intro hs
    exact keysIn_mono (fun v hv => List.mem_append_right _ hv) (ih hs)
  | graphIriNone _ =>
    intro _ mu hmu
    cases hmu
  | @graphVar v q a F _ ih =>
    intro hs mu hmu p hp
    simp only [List.mem_flatMap, List.mem_filterMap] at hmu
    obtain ⟨ng, hng, mu', hmu', e⟩ := hmu
    rcases keys_bindIfCompatible v _ mu' mu e p hp with h | h
    · simp [QueryPattern.inScopeVars, projectionTermVars, h]
    · exact List.mem_append_right _ (ih ng hng hs mu' hmu' p h)
  | graphBnode _ ih =>
    intro hs
    exact keysIn_mono (fun v hv => List.mem_append_right _ hv) (ih hs)
  | graphLiteral _ ih =>
    intro hs
    exact keysIn_mono (fun v hv => List.mem_append_right _ hv) (ih hs)
  | graphTriple _ ih =>
    intro hs
    exact keysIn_mono (fun v hv => List.mem_append_right _ hv) (ih hs)
  | bind _ ih =>
    intro hs
    exact keys_bindRowsFresh _ _ _ _ 0 (ih hs)
  | values vars rows a =>
    intro _
    exact keys_evalValues vars rows
  | @subSelect form dcs inner gb hv md pv bs a A _ ih =>
    intro hs
    cases form with
    | select sel =>
      cases sel with
      | vars items =>
        intro mu hmu p hp
        exact SubSelect.selectPost_dom env a items dcs inner gb hv md pv bs A mu hmu p hp
      | all =>
        obtain ⟨rfl, hs'⟩ := hs rfl
        exact selectPost_all_keys env a dcs inner hv md pv bs A (ih hs')
    | construct _ => intro mu hmu; cases md; simp [selectPost] at hmu
    | ask => intro mu hmu; cases md; simp [selectPost] at hmu
    | describe _ => intro mu hmu; cases md; simp [selectPost] at hmu
  | empty a =>
    intro _ mu hmu p hp
    simp only [List.mem_singleton] at hmu
    subst hmu
    cases hp
  | equiv _ hE ih =>
    intro hs
    exact keys_solEquiv (ih hs) hE

end L4Factoidal.Storage.Sbm11.ScopeTheorems

#print axioms L4Factoidal.Storage.Sbm11.ScopeTheorems.allowed_keys
#print axioms L4Factoidal.Storage.Sbm11.ScopeTheorems.selectPost_all_keys
#print axioms L4Factoidal.Storage.Sbm11.ScopeTheorems.finishSelectRows_mem'
