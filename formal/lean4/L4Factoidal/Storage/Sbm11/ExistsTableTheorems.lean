/-
L4Factoidal.Storage.Sbm11.ExistsTableTheorems — FILTER and OPTIONAL
conditions with EXISTS and NOT EXISTS conjuncts, as the nested evaluator runs
them (https://github.com/danbri/factoidal/issues/776; the table part of lemma
L5r and the FILTER and LeftJoin steps of L5t,
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

## What the code does and what the reference does

SPARQL 1.1 section 18.6: `EXISTS { B }` substitutes the current solution
mapping μ into `B` and asks whether the substituted pattern has a solution
in the active graph (`Query.substituteExistentials`). The id path
(`IdQuery.semiHitsM`) evaluates `B` once, by itself, and keeps a row when some
row of `B` is compatible with it (`IdQuery.semiMatches`). The two agree on a
row when substitution replaces every variable of `B` that the row binds at
every position where it occurs (`IdExists.SubstOk`) and the substituted
pattern holds no `text:query` pattern; `semiHitsM` checks both on every row
that the earlier conjuncts kept and refuses the query otherwise
(`substRefusalMsg`, `fulltextRefusalMsg`, now `LocalVocab.LocalRefusal`s).

* `conjuncts_all`, `filterFn_conjuncts`: the reference FILTER of a condition
  is the conjunction of the values of its conjuncts (`cjVal`), each with its
  EXISTS substituted.
* `cjVal_existsFree`, `cjVal_existsEmpty`, `cjVal_notExistsEmpty`,
  `cjVal_existsBgp`: the value of each kind of conjunct.
* `filterKindsM_spec_ex`: `IdGroup.filterKindsM` classifies the conjuncts of
  a condition whose conjuncts are `CjExOk`: the EXISTS-free ones as
  `FilterIdTheorems.KindOf`, the EXISTS and NOT EXISTS of a basic graph
  pattern as semi-join blocks (`semiOf`), `NOT EXISTS {}` as the flag.
* `substCellM_spec`, `check_loop`: the substitution check of `semiHitsM`
  refuses, or every checked row passes it (`CellOk`).
* `subst_ok_of_cells`, `fulltext_of_cells`: a row that passes the check is
  `SubstOk` for `B`, and the substituted pattern has no `text:query` pattern.
* `semiHitsM_spec`: `semiHitsM` refuses, or its test on each checked row is
  whether the substituted pattern has a solution in the active graph.
* `filterMaskM_spec`: `IdGroup.filterMaskM` refuses, or entry `i` of its mask
  is the reference FILTER (`IdGroup.filterFn`) of the condition on the decoded
  row `i`.
* `filterM_run`, `leftJoinCond_run`: FILTER and OPTIONAL with a condition
  other than `true`, from `filterMaskM_spec`.

The hypotheses beyond those of `FilterTableTheorems`: the reference's
environment `env` has a dataset (`env.dataset = some _`; without one the
reference leaves EXISTS unevaluated, SPARQL 1.1 section 18.6 evaluates it
against the active graph of the dataset). The id path's environment `cx.env`
need not have one: it evaluates EXISTS on ids (`semiHitsM`), and agrees with
`env` on what `Expr.evalIn` reads (`ExprLocalTheorems.EnvAgree`: `ext`, `now`,
`base`; `henv`). The leaf conditions of each EXISTS body in the active graph
(`ExecLeafTheorems.ExecLeaf`), as for a basic graph pattern of the WHERE
clause; no EXISTS body has `text:query` as a constant predicate (`NoFtPred`;
`IdQuery.translate` refuses such a query); and the tag of a store id says
whether it is an IRI or blank node (tags 1, 2) or a literal (tags 3, 4, 5)
(`TagKind`, what `IdQuery.substOkIdM` reads without decoding).

## Restrictions

EXISTS and NOT EXISTS of a pattern that is not a basic graph pattern or `{}`
(a pattern with MINUS, OPTIONAL, FILTER, a nested EXISTS, ...), and EXISTS
inside an expression (under `||`, `!`, `IF`, ...): `filterKindsM` refuses
them, and `CjExOk` excludes them. A blank node in an EXISTS body:
`ExecLeafTheorems.ExecTp` excludes it, as for the basic graph patterns of
the WHERE clause.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.SemiTableTheorems
import L4Factoidal.Storage.Sbm11.GraphVarTableTheorems
import L4Factoidal.Storage.Sbm11.IdQueryTests

set_option linter.unusedSimpArgs false

namespace L4Factoidal.Storage.Sbm11.ExistsTableTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt NM GCtx filterKindsM filterMaskM filterM leftJoinCondM liftE)
open L4Factoidal.Storage.Sbm11.FilterIdTheorems
open L4Factoidal.Storage.Sbm11.ExprLocalTheorems
open L4Factoidal.Storage.Sbm11.FilterTableTheorems (Fa2 select_spec forIn_nm' FilterOk keep_all rows_of
  forall₂_take_succ)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible decRow RowIds unbound)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems (ExecTp specE argS argT patSpecsOf_run)
open L4Factoidal.Storage.Sbm11.LocalVocab

/-! ## The conjuncts of a condition -/

/-- What the loop of `conjuncts` keeps, for any `f` that is a conjunction on
    `.and`. -/
def AInv (f : Expr → Bool) (c : Expr) (s : Array Expr × Array Expr) : Prop :=
  f c = (s.2.toList.all f && s.1.toList.all f)

/-- **The conjuncts of a condition.** For a function `f` that maps `.and l r`
    to the conjunction of its values on `l` and `r`, `f c` is the conjunction
    of its values on `IdQuery.conjuncts c`. -/
theorem conjuncts_all (f : Expr → Bool) (hf : ∀ l r, f (.and l r) = (f l && f r)) (c : Expr) :
    f c = (conjuncts c).toList.all f := by
  unfold conjuncts
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  generalize hF : forIn (m := Id) (List.range' 0 _) _ _ = F
  have hI := forIn_pq (AInv f c) (AInv f c) _ hF (by simp [AInv]) (by
    intro a s hs
    obtain ⟨st, out⟩ := s
    unfold AInv at hs
    simp only [] at hs
    cases hb : st.back? with
    | none =>
      simp only []
      exact done_ok hs
    | some x =>
      have hst := back_pop' hb
      simp only []
      revert hb
      cases x
      all_goals intro hb
      case and l r =>
        refine yield_ok ?_
        unfold AInv
        rw [hs, hst]
        simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true, hf]
        cases (out.toList.all f) <;> cases (st.pop.toList.all f) <;> cases f l <;> cases f r <;> rfl
      all_goals
        refine yield_ok ?_
        unfold AInv
        rw [hs, hst]
        simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
        generalize (out.toList.all f) = p
        generalize (st.pop.toList.all f) = q
        generalize f _ = w
        cases p <;> cases q <;> cases w <;> rfl)
  have hfin : AInv f c F.run := by rcases hI with h | h <;> exact h
  show _ = (F.run.2 ++ F.run.1.reverse).toList.all f
  generalize F.run = S at hfin
  obtain ⟨st, out⟩ := S
  unfold AInv at hfin
  rw [hfin]
  simp only [Array.toList_append, Array.toList_reverse, List.all_append, List.all_reverse]

/-- The value of one conjunct in the reference FILTER `IdGroup.filterFn`: its
    EXISTS substituted (`substituteExistentials`), then its effective boolean
    value. -/
def cjVal (env : EvalEnv) (a : Graph) (row : Binding) (cj : Expr) : Bool :=
  ebvOrFalse (Expr.evalIn env (Binding.empty.merge row)
    (substituteExistentials env a (Binding.empty.merge row) cj))

/-- **The reference FILTER is the conjunction of its conjuncts' values.** -/
theorem filterFn_conjuncts (env : EvalEnv) (c : Expr) (a : Graph) (row : Binding) :
    IdGroup.filterFn env c a row = (conjuncts c).toList.all (cjVal env a row) :=
  conjuncts_all (cjVal env a row) (fun l r => by
    simp only [cjVal, substituteExistentials]
    exact L4Factoidal.Storage.Sbm11.IdQueryTests.ebvOrFalse_evalIn_and _ _ _ _) c

theorem cjVal_existsFree (env : EvalEnv) (a : Graph) (row : Binding) (cj : Expr) (hef : cj.existsFree = true) :
    cjVal env a row cj = ebvOrFalse (Expr.evalIn env row cj) := by
  unfold cjVal
  rw [L4Factoidal.Storage.Sbm11.IdPostTheorems.substituteExistentials_existsFree env a _ cj hef,
    evalIn_bindEq env _ row (lookup_merge_empty row) cj]

theorem cjVal_existsEmpty (env : EvalEnv) (ds0 : Dataset) (hds : env.dataset = some ds0) (a : Graph)
    (row : Binding) : cjVal env a row (.existsPat .empty) = true := by
  simp [cjVal, substituteExistentials, hds, QueryPattern.lowerWith, GraphPattern.evalIn, Expr.evalIn,
    ebvOrFalse, ebv]

theorem cjVal_notExistsEmpty (env : EvalEnv) (ds0 : Dataset) (hds : env.dataset = some ds0) (a : Graph)
    (row : Binding) : cjVal env a row (.notExistsPat .empty) = false := by
  simp [cjVal, substituteExistentials, hds, QueryPattern.lowerWith, GraphPattern.evalIn, Expr.evalIn,
    ebvOrFalse, ebv]

/-- **EXISTS and NOT EXISTS of a basic graph pattern in the reference.** With
    a dataset in the environment and no `text:query` pattern after
    substitution, the value of the conjunct is whether `substBgp row b` has a
    solution in the active graph (EXISTS) or has none (NOT EXISTS). -/
theorem cjVal_existsBgp (env : EvalEnv) (ds0 : Dataset) (hds : env.dataset = some ds0) (a : Graph)
    (row : Binding) (b : Bgp) (hft : bgpHasFulltext (substBgp row b) = false) :
    cjVal env a row (.existsPat (.bgp b)) = !(evalBgp (substBgp row b) a).isEmpty ∧
      cjVal env a row (.notExistsPat (.bgp b)) = (evalBgp (substBgp row b) a).isEmpty := by
  have hs : substBgp (Binding.empty.merge row) b = substBgp row b :=
    IdExists.substBgp_congr (fun v => lookup_merge_empty row v) b
  have he : (QueryPattern.lowerWith env (Binding.empty.merge row) (.bgp b)).evalIn ds0 a =
      evalBgp (substBgp row b) a := by
    simp only [QueryPattern.lowerWith]
    rw [hs, lowerBgp_of_no_fulltext _ hft, GraphPattern.evalIn, evalBgpIdx_eq_evalBgp]
  constructor
  · simp only [cjVal, substituteExistentials, hds, he]
    cases (evalBgp (substBgp row b) a).isEmpty <;> rfl
  · simp only [cjVal, substituteExistentials, hds, he]
    cases (evalBgp (substBgp row b) a).isEmpty <;> rfl

/-! ## The conditions the id path runs -/

/-- A triple pattern whose predicate is not the constant `text:query`
    (`IdQuery.translate` refuses a query that mentions it). -/
def NoFtPred (tp : TriplePattern) : Prop := ∀ i, tp.p = .iri i → i ≠ fulltextQueryPred

/-- A conjunct the id path's FILTER runs (`IdGroup.filterKindsM`): an
    EXISTS-free conjunct (`CjOk`); `EXISTS { B }` or `NOT EXISTS { B }` with
    `B` a basic graph pattern whose triple patterns the id path resolves as
    the model does (`ExecTp`) and whose predicates are not `text:query`; or
    `EXISTS {}` or `NOT EXISTS {}`. -/
def CjExOk (cj : Expr) : Prop :=
  CjOk cj ∨
    (∃ b, (cj = .existsPat (.bgp b) ∨ cj = .notExistsPat (.bgp b)) ∧ ∀ tp ∈ b, ExecTp tp ∧ NoFtPred tp) ∨
    cj = .existsPat .empty ∨ cj = .notExistsPat .empty

/-- What the id path's FILTER and LeftJoin conditions are proved for: every
    conjunct is `CjExOk`. -/
def FilterExOk (c : Expr) : Prop := ∀ cj ∈ (conjuncts c).toList, CjExOk cj

theorem filterExOk_of_filterOk {c : Expr} (h : FilterOk c) : FilterExOk c := fun cj hcj => Or.inl (h.2 cj hcj)

/-- `b` is the basic graph pattern of an EXISTS or NOT EXISTS conjunct of
    `c`. -/
def ExistsBgp (c : Expr) (b : Bgp) : Prop :=
  Expr.existsPat (.bgp b) ∈ (conjuncts c).toList ∨ Expr.notExistsPat (.bgp b) ∈ (conjuncts c).toList

/-- The block `filterKindsM` builds for an EXISTS or NOT EXISTS conjunct of a
    basic graph pattern. -/
def semiOf : Expr → Option SemiBlock
  | .existsPat (.bgp b) => some { pats := (b.map specE).toArray, kind := .semi }
  | .notExistsPat (.bgp b) => some { pats := (b.map specE).toArray, kind := .anti }
  | _ => none

/-- `NOT EXISTS {}`: no row passes. -/
def isNotExistsEmpty : Expr → Bool
  | .notExistsPat .empty => true
  | _ => false

theorem semiOf_existsFree {cj : Expr} (h : cj.existsFree = true) : semiOf cj = none := by
  unfold semiOf
  split <;> simp_all [Expr.existsFree]

theorem isNotExistsEmpty_existsFree {cj : Expr} (h : cj.existsFree = true) : isNotExistsEmpty cj = false := by
  unfold isNotExistsEmpty
  split <;> simp_all [Expr.existsFree]

/-- **The classification of the conjuncts, EXISTS included.** Over a store
    whose dictionary lookup is `cid`, for a condition whose conjuncts are
    `CjExOk`, `filterKindsM` returns, without changing the state, one kind
    per EXISTS-free conjunct as `KindOf` says, the blocks of the EXISTS and
    NOT EXISTS conjuncts of a basic graph pattern in order (`semiOf`), and
    whether some conjunct is `NOT EXISTS {}`. -/
theorem filterKindsM_spec_ex (cx : NCx Id) (cid : Term → Option UInt64) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (t : Table) (c : Expr) (hc : FilterExOk c) (nst : NSt) :
    ∃ fs, (filterKindsM cx t c).run nst =
        pure ((fs, ((conjuncts c).toList.filterMap semiOf).toArray, (conjuncts c).toList.any isNotExistsEmpty), nst) ∧
      Fa2 (KindOf cx.env cid t) ((conjuncts c).toList.filter (·.existsFree)) fs.toList ∧
      ∀ k ∈ fs.toList, ∀ v, k = .idEq v none → nst.vocab.isEmpty = true := by
  unfold filterKindsM
  simp only []
  rw [StateT.run_bind, ← Array.forIn_toList]
  generalize hF : forIn (m := NM Id) (conjuncts c).toList ((#[] : Array FKind), (#[] : Array SemiBlock), false) _ = F
  obtain ⟨⟨fs, semis, none_⟩, h, hsem, hnone, hP, hve⟩ := forIn_nm' nst hF
    (fun k (s : Array FKind × Array SemiBlock × Bool) =>
      s.2.1.toList = ((conjuncts c).toList.take k).filterMap semiOf ∧
      s.2.2 = ((conjuncts c).toList.take k).any isNotExistsEmpty ∧
      Fa2 (KindOf cx.env cid t) (((conjuncts c).toList.take k).filter (·.existsFree)) s.1.toList ∧
      ∀ k' ∈ s.1.toList, ∀ v, k' = .idEq v none → nst.vocab.isEmpty = true)
    ⟨by simp, by simp, by simp; exact Fa2.nil, by simp⟩ (by
      intro k hk ⟨fs, semis, none_⟩ ⟨hs, hn, hf, hne⟩
      simp only [] at hs hn hf hne
      have htake : (conjuncts c).toList.take (k + 1) = (conjuncts c).toList.take k ++ [(conjuncts c).toList[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; simp
      have hcj := hc _ (List.getElem_mem hk)
      rw [htake]
      generalize (conjuncts c).toList[k] = cj at hcj ⊢
      generalize (conjuncts c).toList.take k = P at hs hn hf ⊢
      rcases hcj with hok | ⟨b, hb | hb, htp⟩ | hb | hb
      · -- an EXISTS-free conjunct: as `FilterTableTheorems.filterKindsM_spec`
        have hef := hok.ef
        have hstep : ∀ k', KindOf cx.env cid t cj k' →
            (∀ v, k' = .idEq v none → nst.vocab.isEmpty = true) →
            (semis.toList = (P ++ [cj]).filterMap semiOf ∧ none_ = (P ++ [cj]).any isNotExistsEmpty ∧
              Fa2 (KindOf cx.env cid t) ((P ++ [cj]).filter (·.existsFree)) (fs.push k').toList ∧
              ∀ k'' ∈ (fs.push k').toList, ∀ v, k'' = .idEq v none → nst.vocab.isEmpty = true) := by
          intro k' hk' hv
          refine ⟨by rw [hs, List.filterMap_append]; simp [semiOf_existsFree hef],
            by rw [hn, List.any_append]; simp [isNotExistsEmpty_existsFree hef], ?_, fun k'' hk'' => ?_⟩
          · rw [List.filter_append, Array.toList_push]
            simp only [List.filter_cons, hef, if_true, List.filter_nil]
            exact Fa2.snoc hf hk'
          · rw [Array.toList_push] at hk''
            rcases List.mem_append.mp hk'' with h | h
            · exact hne k'' h
            · rw [List.mem_singleton] at h; subst h; exact hv
        obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hok.rv
        split
        · simp [Expr.existsFree] at hef
        · simp [Expr.existsFree] at hef
        · simp [Expr.existsFree] at hef
        · simp [Expr.existsFree] at hef
        · rw [hvs]
          simp only [hef, if_true]
          split
          · next hcond =>
            simp only [Bool.and_eq_true, Option.isSome_iff_exists, Array.all_eq_true] at hcond
            obtain ⟨⟨hbl, vs', hev⟩, hcb⟩ := hcond
            have hcb' : ∀ w ∈ ((residualVars cj).getD #[]).toList, IdGroup.colBound t w = true := by
              rw [hvs, Option.getD_some]
              intro w hw
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
              simp only [Array.length_toList] at hj
              simpa using hcb j hj
            obtain ⟨k0, hk0, hK⟩ := compile_spec cx.st cid hid cj hok.nostr vs' hev
            have hl : (liftE (compileFilter cx.st cj) : NM Id FKind).run nst = pure (k0, nst) := by
              unfold liftE; rw [StateT.run_lift, hk0]; rfl
            rw [StateT.run_bind, hl, pure_bind]
            split
            · next v hk0e =>
              rw [StateT.run_bind]
              simp only [StateT.run_get, pure_bind]
              split
              · next hvemp => exact ⟨_, rfl, hstep _ (Or.inr ⟨hbl, hcb', hK⟩) fun _ _ => hvemp⟩
              · exact ⟨_, rfl, hstep _ (Or.inl rfl) fun _ e => by cases e⟩
            · next hne0 => exact ⟨_, rfl, hstep _ (Or.inr ⟨hbl, hcb', hK⟩) fun v e => absurd e (hne0 v)⟩
          · exact ⟨_, rfl, hstep _ (Or.inl rfl) fun _ e => by cases e⟩
      · -- EXISTS { B }
        subst hb
        simp only []
        rw [StateT.run_bind, patSpecsOf_run b (fun tp htp' => (htp tp htp').1) nst, pure_bind]
        refine ⟨_, rfl, ?_, ?_, ?_, hne⟩
        · rw [Array.toList_push, hs, List.filterMap_append]; rfl
        · rw [hn, List.any_append]; simp [isNotExistsEmpty]
        · rw [List.filter_append]; simpa [Expr.existsFree] using hf
      · -- NOT EXISTS { B }
        subst hb
        simp only []
        rw [StateT.run_bind, patSpecsOf_run b (fun tp htp' => (htp tp htp').1) nst, pure_bind]
        refine ⟨_, rfl, ?_, ?_, ?_, hne⟩
        · rw [Array.toList_push, hs, List.filterMap_append]; rfl
        · rw [hn, List.any_append]; simp [isNotExistsEmpty]
        · rw [List.filter_append]; simpa [Expr.existsFree] using hf
      · -- EXISTS {}
        subst hb
        refine ⟨_, rfl, ?_, ?_, ?_, hne⟩
        · rw [hs, List.filterMap_append]; simp [semiOf]
        · rw [hn, List.any_append]; simp [isNotExistsEmpty]
        · rw [List.filter_append]; simpa [Expr.existsFree] using hf
      · -- NOT EXISTS {}
        subst hb
        refine ⟨_, rfl, ?_, ?_, ?_, hne⟩
        · rw [hs, List.filterMap_append]; simp [semiOf]
        · rw [List.any_append]; simp [isNotExistsEmpty]
        · rw [List.filter_append]; simpa [Expr.existsFree] using hf)
  simp only [] at hsem hnone hP hve
  rw [List.take_length] at hsem hnone hP
  refine ⟨fs, ?_, hP, hve⟩
  rw [h]
  have : semis = ((conjuncts c).toList.filterMap semiOf).toArray := by
    rw [← hsem]
  rw [this, hnone]
  rfl

/-! ## The substitution check of `semiHitsM` -/

/-- What `IdQuery.substOkIdM` reads from the tag of a store id without
    decoding it: tags 1 and 2 are IRIs and blank nodes, tags 3, 4 and 5
    literals. -/
def TagKind (x : UInt64) (t : Term) : Prop :=
  ((tagOf x = 1 ∨ tagOf x = 2) → (∃ i, t = .iri i) ∨ ∃ b, t = .bnode b) ∧
    ((tagOf x = 3 ∨ tagOf x = 4 ∨ tagOf x = 5) → ∃ l, t = .literal l)

/-- A term substitution puts into a subject position (`subject`: an IRI or a
    blank node) or into a predicate or object position (any term but a triple
    term): `substPatternSubject`, `substPatternTerm`. -/
def SubstTerm (subject : Bool) (t : Term) : Prop :=
  if subject then (∃ i, t = .iri i) ∨ ∃ b, t = .bnode b else ∀ s p o, t ≠ .tripleTerm s p o

/-- **`substOkIdM`.** Over a store whose `termOf` decodes the ids in `O` as
    `D` does, whose tags `TagKind` describes, `substOkIdM` answers, and
    `true` only for a term substitution puts into the position. -/
theorem substOkIdM_spec (st : Store Id) (D : UInt64 → Term) (O : UInt64 → Prop)
    (hterm : ∀ x, O x → st.termOf x = pure (D x)) (hkind : ∀ x, O x → TagKind x (D x))
    (x : UInt64) (hx : O x ∨ x = unbound) (subject : Bool) :
    ∃ r, substOkIdM st x subject = pure r ∧ (r = true → x ≠ unbound → SubstTerm subject (D x)) := by
  unfold substOkIdM
  by_cases hu : x = unbound
  · subst hu
    exact ⟨true, rfl, fun _ h => absurd rfl h⟩
  have hO : O x := hx.resolve_right hu
  have hk := hkind x hO
  have hu' : (x == unbound) = false := by simpa using hu
  simp only [hu', Bool.false_eq_true, if_false]
  by_cases h12 : (tagOf x == 1 || tagOf x == 2) = true
  · simp only [h12, if_true]
    refine ⟨true, rfl, fun _ _ => ?_⟩
    have hi := hk.1 (by simpa using h12)
    unfold SubstTerm
    split
    · exact hi
    · rcases hi with ⟨i, hi⟩ | ⟨b, hb⟩
      · intro s p o; rw [hi]; simp
      · intro s p o; rw [hb]; simp
  · simp only [h12, Bool.false_eq_true, if_false]
    by_cases h9 : (tagOf x == 9) = true
    · simp only [h9, if_true]
      exact ⟨false, rfl, fun h => by cases h⟩
    · simp only [h9, Bool.false_eq_true, if_false]
      by_cases h345 : (tagOf x == 3 || tagOf x == 4 || tagOf x == 5) = true
      · simp only [h345, if_true]
        refine ⟨!subject, rfl, fun hs _ => ?_⟩
        obtain ⟨l, hl⟩ := hk.2 (by simpa [or_assoc] using h345)
        cases subject
        · simp only [SubstTerm, Bool.false_eq_true, if_false]
          intro s p o; rw [hl]; simp
        · simp at hs
      · simp only [h345, Bool.false_eq_true, if_false]
        rw [hterm x hO]
        simp only [pure_bind]
        cases hd : D x with
        | iri i =>
          refine ⟨true, rfl, fun _ _ => ?_⟩
          unfold SubstTerm; split
          · exact Or.inl ⟨i, rfl⟩
          · intro s p o; simp
        | bnode b =>
          refine ⟨true, rfl, fun _ _ => ?_⟩
          unfold SubstTerm; split
          · exact Or.inr ⟨b, rfl⟩
          · intro s p o; simp
        | literal l =>
          refine ⟨!subject, rfl, fun hs _ => ?_⟩
          cases subject
          · simp only [SubstTerm, Bool.false_eq_true, if_false]
            intro s p o; simp
          · simp at hs
        | tripleTerm s p o => exact ⟨false, rfl, fun h => by cases h⟩

/-- Every entry of the memo of the check is the answer of `substOkIdM`. -/
def SubstMemoOk (st : Store Id) (memo : Std.HashMap (UInt64 × Bool) Bool) : Prop :=
  ∀ x s r, memo[(x, s)]? = some r → substOkIdM st x s = pure r

theorem substMemoOk_empty (st : Store Id) : SubstMemoOk st {} := fun x s r h => by simp at h

theorem pure_inj_exc {α : Type} {a b : α} (h : (pure a : ExceptT String Id α) = pure b) : a = b := by
  have : (Except.ok a : Except String α) = Except.ok b := h
  cases this; rfl

theorem substOkMemoM_spec (st : Store Id) (memo : Std.HashMap (UInt64 × Bool) Bool) (hm : SubstMemoOk st memo)
    (x : UInt64) (s : Bool) (r0 : Bool) (h0 : substOkIdM st x s = pure r0) :
    ∃ memo', substOkMemoM st memo x s = pure (r0, memo') ∧ SubstMemoOk st memo' := by
  unfold substOkMemoM
  cases hq : memo[(x, s)]? with
  | some r =>
    have := hm x s r hq
    rw [h0] at this
    rw [pure_inj_exc this]
    exact ⟨memo, rfl, hm⟩
  | none =>
    refine ⟨memo.insert (x, s) r0, by simp only []; rw [h0]; rfl, ?_⟩
    intro y s' r h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next hb =>
      cases h
      have e : (x, s) = (y, s') := by simpa using hb
      cases e
      exact h0
    · exact hm y s' r h

/-- A cell `x` of a column whose variable has a subject position (`subject`)
    or a predicate position (`pred`) in the pattern passes the check: an id
    substitution puts into those positions, and not `text:query` in a
    predicate position. -/
def CellOk (D : UInt64 → Term) (subject pred : Bool) (x : UInt64) : Prop :=
  (x ≠ unbound → SubstTerm subject (D x)) ∧ (pred = true → x ≠ unbound → D x ≠ .iri fulltextQueryPred)

/-- **One cell of the check.** `substCellM` refuses (a `LocalRefusal`) or
    passes the cell (`CellOk`), keeping the memo sound. `hft`: an id with no
    local tag that decodes to `text:query` is `ftId`. -/
theorem substCellM_spec (st : Store Id) (D : UInt64 → Term) (O : UInt64 → Prop)
    (hterm : ∀ x, O x → st.termOf x = pure (D x)) (hkind : ∀ x, O x → TagKind x (D x))
    (ftId : Option UInt64)
    (hft : ∀ x, O x → D x = .iri fulltextQueryPred → tagOf x ≠ tagLocal → ftId = some x)
    (v : String) (subject pred : Bool) (memo : Std.HashMap (UInt64 × Bool) Bool) (hm : SubstMemoOk st memo)
    (x : UInt64) (hx : O x ∨ x = unbound) :
    (∃ e, substCellM st ftId v subject pred memo x = throw e ∧ LocalRefusal e) ∨
      ∃ memo', substCellM st ftId v subject pred memo x = pure memo' ∧ SubstMemoOk st memo' ∧
        CellOk D subject pred x := by
  obtain ⟨r, hr, hrs⟩ := substOkIdM_spec st D O hterm hkind x hx subject
  obtain ⟨memo', hmm, hm'⟩ := substOkMemoM_spec st memo hm x subject r hr
  unfold substCellM
  rw [hmm, pure_bind]
  simp only []
  cases r with
  | false =>
    left
    exact ⟨_, rfl, Or.inr (Or.inr (Or.inl ⟨v, subject, rfl⟩))⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
    have hsub : x ≠ unbound → SubstTerm subject (D x) := hrs rfl
    by_cases hp : (pred && x != unbound) = true
    · simp only [hp, if_true]
      have hxu : x ≠ unbound := by simp only [Bool.and_eq_true, bne_iff_ne] at hp; exact hp.2
      have hO : O x := hx.resolve_right hxu
      by_cases hf : (ftId == some x) = true
      · simp only [hf, if_true]
        left
        exact ⟨_, rfl, Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))⟩
      · simp only [hf, Bool.false_eq_true, if_false, pure_bind]
        by_cases hl : (tagOf x == tagLocal) = true
        · simp only [hl, if_true]
          rw [hterm x hO, pure_bind]
          by_cases he : (D x == .iri fulltextQueryPred) = true
          · simp only [he, if_true]
            left
            exact ⟨_, rfl, Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))⟩
          · simp only [he, Bool.false_eq_true, if_false, pure_bind]
            right
            exact ⟨memo', rfl, hm', hsub, fun _ _ e => he (by rw [e]; simp)⟩
        · simp only [hl, Bool.false_eq_true, if_false, pure_bind]
          right
          refine ⟨memo', rfl, hm', hsub, fun _ _ e => hf ?_⟩
          rw [hft x hO e (by simpa using hl)]
          simp
    · simp only [hp, Bool.false_eq_true, if_false, pure_bind]
      right
      refine ⟨memo', rfl, hm', hsub, fun hpr hxu => ?_⟩
      exact absurd (by simp [hpr, hxu]) hp

/-- **The rows of one column.** The check of column `v` over the rows `i <
    n` with `live i` refuses, or passes every such cell, the memo sound. -/
theorem check_rows (st : Store Id) (D : UInt64 → Term) (O : UInt64 → Prop)
    (hterm : ∀ x, O x → st.termOf x = pure (D x)) (hkind : ∀ x, O x → TagKind x (D x))
    (ftId : Option UInt64)
    (hft : ∀ x, O x → D x = .iri fulltextQueryPred → tagOf x ≠ tagLocal → ftId = some x)
    (v : String) (subject pred : Bool) (n : Nat) (xs : Nat → UInt64)
    (hx : ∀ i, i < n → O (xs i) ∨ xs i = unbound)
    (live : Nat → Bool) (memo0 : Std.HashMap (UInt64 × Bool) Bool) (hm0 : SubstMemoOk st memo0) :
    (∃ e, forIn (List.range' 0 n) memo0 (fun i (memo : Std.HashMap (UInt64 × Bool) Bool) =>
        if live i = true then do
          let memo ← substCellM st ftId v subject pred memo (xs i)
          pure (ForInStep.yield memo)
        else pure (ForInStep.yield memo)) = throw e ∧ LocalRefusal e) ∨
      ∃ memo, forIn (List.range' 0 n) memo0 (fun i (memo : Std.HashMap (UInt64 × Bool) Bool) =>
        if live i = true then do
          let memo ← substCellM st ftId v subject pred memo (xs i)
          pure (ForInStep.yield memo)
        else pure (ForInStep.yield memo)) = pure memo ∧ SubstMemoOk st memo ∧
        ∀ i, i < n → live i = true → CellOk D subject pred (xs i) := by
  have := LocalTable.forIn_ends (fun i (memo : Std.HashMap (UInt64 × Bool) Bool) =>
      (if live i = true then do
          let memo ← substCellM st ftId v subject pred memo (xs i)
          pure (ForInStep.yield memo)
        else pure (ForInStep.yield memo) : ExceptT String Id _)) (List.range' 0 n)
    (fun k memo => SubstMemoOk st memo ∧ ∀ i, i < k → live i = true → CellOk D subject pred (xs i)) memo0
    ⟨hm0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩ (by
      intro k hk memo ⟨hm, hc⟩
      simp only [List.length_range'] at hk
      simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
      by_cases hl : live k = true
      · simp only [hl, if_true]
        rcases substCellM_spec st D O hterm hkind ftId hft v subject pred memo hm (xs k) (hx k hk) with
          ⟨e, he, hr⟩ | ⟨memo', he, hm', hck⟩
        · left; exact ⟨e, by rw [he]; rfl, hr⟩
        · right
          refine ⟨memo', by rw [he]; rfl, hm', fun i hi hli => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hc i hi hli
          · exact hck
      · simp only [hl, Bool.false_eq_true, if_false]
        right
        refine ⟨memo, rfl, hm, fun i hi hli => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hc i hi hli
        · exact absurd hli hl)
  simpa using this

/-- **The check of `semiHitsM`.** Over the columns of `t` whose variable is
    a variable of the pattern (`inB`), and the rows with `live`, the check
    refuses, or passes every such cell (`CellOk`, with the position kinds
    `subj` and `pred` of the variable). -/
theorem check_loop (st : Store Id) (D : UInt64 → Term) (O : UInt64 → Prop)
    (hterm : ∀ x, O x → st.termOf x = pure (D x)) (hkind : ∀ x, O x → TagKind x (D x))
    (ftId : Option UInt64)
    (hft : ∀ x, O x → D x = .iri fulltextQueryPred → tagOf x ≠ tagLocal → ftId = some x)
    (t : Table) (hO : ∀ c i, c < t.vars.size → i < t.rows → O (t.at c i) ∨ t.at c i = unbound)
    (inB subj pred : String → Bool) (live : Nat → Bool) :
    (∃ e, forIn (List.range' 0 t.vars.size) ({} : Std.HashMap (UInt64 × Bool) Bool)
        (fun c (memo : Std.HashMap (UInt64 × Bool) Bool) =>
          if (!inB t.vars[c]!) = true then pure (ForInStep.yield memo)
          else do
            let memo ← forIn (List.range' 0 t.rows) memo (fun i (memo : Std.HashMap (UInt64 × Bool) Bool) =>
              if live i = true then do
                let memo ← substCellM st ftId t.vars[c]! (subj t.vars[c]!) (pred t.vars[c]!) memo (t.at c i)
                pure (ForInStep.yield memo)
              else pure (ForInStep.yield memo))
            pure (ForInStep.yield memo)) = throw e ∧ LocalRefusal e) ∨
      ∃ memo, forIn (List.range' 0 t.vars.size) ({} : Std.HashMap (UInt64 × Bool) Bool)
        (fun c (memo : Std.HashMap (UInt64 × Bool) Bool) =>
          if (!inB t.vars[c]!) = true then pure (ForInStep.yield memo)
          else do
            let memo ← forIn (List.range' 0 t.rows) memo (fun i (memo : Std.HashMap (UInt64 × Bool) Bool) =>
              if live i = true then do
                let memo ← substCellM st ftId t.vars[c]! (subj t.vars[c]!) (pred t.vars[c]!) memo (t.at c i)
                pure (ForInStep.yield memo)
              else pure (ForInStep.yield memo))
            pure (ForInStep.yield memo)) = pure memo ∧
        ∀ c i, c < t.vars.size → i < t.rows → inB t.vars[c]! = true → live i = true →
          CellOk D (subj t.vars[c]!) (pred t.vars[c]!) (t.at c i) := by
  have := LocalTable.forIn_ends (fun c (memo : Std.HashMap (UInt64 × Bool) Bool) =>
      (if (!inB t.vars[c]!) = true then pure (ForInStep.yield memo)
          else do
            let memo ← forIn (List.range' 0 t.rows) memo (fun i (memo : Std.HashMap (UInt64 × Bool) Bool) =>
              if live i = true then do
                let memo ← substCellM st ftId t.vars[c]! (subj t.vars[c]!) (pred t.vars[c]!) memo (t.at c i)
                pure (ForInStep.yield memo)
              else pure (ForInStep.yield memo))
            pure (ForInStep.yield memo) : ExceptT String Id _)) (List.range' 0 t.vars.size)
    (fun k memo => SubstMemoOk st memo ∧ ∀ c i, c < k → i < t.rows → inB t.vars[c]! = true → live i = true →
      CellOk D (subj t.vars[c]!) (pred t.vars[c]!) (t.at c i)) {}
    ⟨substMemoOk_empty st, fun c i hc => absurd hc (Nat.not_lt_zero c)⟩ (by
      intro k hk memo ⟨hm, hc⟩
      simp only [List.length_range'] at hk
      simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
      by_cases hb : (!inB t.vars[k]!) = true
      · simp only [hb, if_true]
        right
        refine ⟨memo, rfl, hm, fun c i hck hi hin hli => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hck with hck | rfl
        · exact hc c i hck hi hin hli
        · simp [hin] at hb
      · simp only [hb, Bool.false_eq_true, if_false]
        rcases check_rows st D O hterm hkind ftId hft t.vars[k]! (subj t.vars[k]!) (pred t.vars[k]!) t.rows
            (fun i => t.at k i) (fun i hi => hO k i hk hi) live memo hm with
          ⟨e, he, hr⟩ | ⟨memo', he, hm', hcells⟩
        · left; exact ⟨e, by rw [he]; rfl, hr⟩
        · right
          refine ⟨memo', by rw [he]; rfl, hm', fun c i hck hi hin hli => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hck with hck | rfl
          · exact hc c i hck hi hin hli
          · exact hcells i hi hli)
  rcases this with h | ⟨memo, h, _, hP⟩
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨memo, by simpa using h, by simpa using hP⟩

/-! ## A row that passes the check -/

open L4Factoidal.Storage.Sbm11.TableTheorems (idx_some)

/-- The lookup of a variable in a decoded row of a well-formed table. -/
theorem lookup_row (D : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (v : String) :
    (decRow D (t.idRow i)).lookup v = none ∨
      ∃ c, c < t.vars.size ∧ t.vars[c]! = v ∧ t.at c i ≠ unbound ∧
        (decRow D (t.idRow i)).lookup v = some (D (t.at c i)) := by
  rw [decRow_lookup D t ht i v]
  cases hc : t.idx v with
  | none => left; rfl
  | some c =>
    obtain ⟨hcs, hcv⟩ := idx_some hc
    by_cases hu : t.at c i = unbound
    · left; simp [hu]
    · right
      refine ⟨c, hcs, hcv, hu, ?_⟩
      simp [hu]

/-- **The check gives `SubstOk`.** When every cell of row `i` in a column
    whose variable is a variable of `b` passes the check, with the position
    kinds of the variable, the decoded row is `SubstOk` for `b`, and binds
    no variable of a predicate position of `b` to `text:query`. -/
theorem subst_of_cells (D : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (b : Bgp)
    (inB subj pred : String → Bool)
    (hin : ∀ tp ∈ b, ∀ v, (tp.s = .var v ∨ tp.p = .var v ∨ tp.o = .var v) → inB v = true)
    (hsubj : ∀ tp ∈ b, ∀ v, tp.s = .var v → subj v = true)
    (hpred : ∀ tp ∈ b, ∀ v, tp.p = .var v → pred v = true)
    (hcells : ∀ c, c < t.vars.size → inB t.vars[c]! = true →
      CellOk D (subj t.vars[c]!) (pred t.vars[c]!) (t.at c i)) :
    IdExists.SubstOk (decRow D (t.idRow i)) b ∧
      ∀ tp ∈ b, ∀ v, tp.p = .var v → (decRow D (t.idRow i)).lookup v ≠ some (.iri fulltextQueryPred) := by
  -- the decoded value of a variable of `b` is one substitution puts in its positions
  have hval : ∀ tp ∈ b, ∀ v, (tp.s = .var v ∨ tp.p = .var v ∨ tp.o = .var v) →
      (decRow D (t.idRow i)).lookup v = none ∨
        ∃ x, x ≠ unbound ∧ (decRow D (t.idRow i)).lookup v = some (D x) ∧
        CellOk D (subj v) (pred v) x := by
    intro tp htp v hv
    rcases lookup_row D t ht i v with h | ⟨c, hc, hcv, hu, h⟩
    · exact Or.inl h
    · right
      have hcell := hcells c hc (by rw [hcv]; exact hin tp htp v hv)
      rw [hcv] at hcell
      exact ⟨_, hu, h, hcell⟩
  refine ⟨fun tp htp => ⟨?_, ?_, ?_⟩, fun tp htp v hp => ?_⟩
  · cases hs : tp.s with
    | var v =>
      simp only [IdExists.SubjOk]
      rcases hval tp htp v (Or.inl hs) with h | ⟨x, hx, h, hcell⟩
      · rw [h]; trivial
      · rw [h]
        have := hcell.1 hx
        rw [hsubj tp htp v hs] at this
        simp only [SubstTerm, if_true] at this
        rcases this with ⟨i', e⟩ | ⟨b', e⟩ <;> rw [e] <;> trivial
    | iri _ => trivial
    | bnode _ => trivial
    | tripleTerm _ _ _ => trivial
  · cases hp : tp.p with
    | var v =>
      simp only [IdExists.TermOk]
      rcases hval tp htp v (Or.inr (Or.inl hp)) with h | ⟨x, hx, h, hcell⟩
      · rw [h]; trivial
      · rw [h]
        have := hcell.1 hx
        unfold SubstTerm at this
        split at this
        · rcases this with ⟨i', e⟩ | ⟨b', e⟩ <;> rw [e] <;> trivial
        · cases e : D x with
          | tripleTerm s' p' o' => exact this s' p' o' e
          | _ => trivial
    | _ => trivial
  · cases ho : tp.o with
    | var v =>
      simp only [IdExists.TermOk]
      rcases hval tp htp v (Or.inr (Or.inr ho)) with h | ⟨x, hx, h, hcell⟩
      · rw [h]; trivial
      · rw [h]
        have := hcell.1 hx
        unfold SubstTerm at this
        split at this
        · rcases this with ⟨i', e⟩ | ⟨b', e⟩ <;> rw [e] <;> trivial
        · cases e : D x with
          | tripleTerm s' p' o' => exact this s' p' o' e
          | _ => trivial
    | _ => trivial
  · rcases hval tp htp v (Or.inr (Or.inl hp)) with h | ⟨x, hx, h, hcell⟩
    · rw [h]; simp
    · rw [h]
      intro e
      have := hcell.2 (by rw [← hpred tp htp v hp]) hx
      exact this (by injection e)

/-- **No `text:query` after substitution.** For a basic graph pattern with no
    `text:query` predicate and a row that binds no variable of a predicate
    position to `text:query`, the substituted pattern has no `text:query`
    pattern. -/
theorem noFulltext_subst (mu : Binding) (b : Bgp) (hnf : ∀ tp ∈ b, NoFtPred tp)
    (hp : ∀ tp ∈ b, ∀ v, tp.p = .var v → mu.lookup v ≠ some (.iri fulltextQueryPred)) :
    bgpHasFulltext (substBgp mu b) = false := by
  unfold bgpHasFulltext substBgp
  rw [List.any_map, List.any_eq_false]
  intro tp htp
  simp only [Function.comp_def, Option.isSome_iff_exists, not_exists]
  intro q hq
  simp only [TriplePattern.fulltext?, substTriplePattern] at hq
  have hne : ∀ i, substPatternTerm mu tp.p = .iri i → i ≠ fulltextQueryPred := by
    intro i hi
    cases e : tp.p with
    | var v =>
      rw [e] at hi
      simp only [substPatternTerm] at hi
      cases hl : mu.lookup v with
      | none => rw [hl] at hi; cases hi
      | some u =>
        rw [hl] at hi
        cases u with
        | iri j =>
          simp only [] at hi; cases hi
          intro e'; subst e'
          exact hp tp htp v e hl
        | bnode _ => simp at hi
        | literal _ => simp at hi
        | tripleTerm _ _ _ => simp at hi
    | iri j =>
      rw [e] at hi
      simp only [substPatternTerm] at hi
      cases hi
      exact hnf tp htp _ e
    | bnode _ => rw [e] at hi; simp [substPatternTerm] at hi
    | literal _ => rw [e] at hi; simp [substPatternTerm] at hi
    | tripleTerm _ _ _ => rw [e] at hi; simp [substPatternTerm] at hi
  revert hq
  split
  · next i l hi _ =>
    have := hne i hi
    simp only [beq_iff_eq, if_neg this]
    intro h; cases h
  · intro h; cases h

/-! ## The variables of a semi-join block -/

theorem dedup_mono (a : Array String) (v w : String) (h : w ∈ a) : w ∈ (if a.contains v then a else a.push v) := by
  split
  · exact h
  · exact Array.mem_push.mpr (Or.inl h)

theorem dedup_mem (a : Array String) (v : String) : v ∈ (if a.contains v then a else a.push v) := by
  split
  · next h => simpa using h
  · exact Array.mem_push.mpr (Or.inr rfl)

theorem foldl_mono {α : Type} (f : Array String → α → Array String) (hf : ∀ a x w, w ∈ a → w ∈ f a x) :
    ∀ (xs : List α) (a : Array String) (w : String), w ∈ a → w ∈ xs.foldl f a
  | [], _, _, h => h
  | x :: xs, a, w, h => foldl_mono f hf xs (f a x) w (hf a x w h)

theorem foldl_mem {α : Type} (f : Array String → α → Array String) (hf : ∀ a x w, w ∈ a → w ∈ f a x)
    (P : α → String → Prop) (hP : ∀ a x w, P x w → w ∈ f a x) :
    ∀ (xs : List α) (a : Array String) (x : α) (w : String), x ∈ xs → P x w → w ∈ xs.foldl f a
  | [], _, _, _, hx, _ => by cases hx
  | y :: xs, a, x, w, hx, hp => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact foldl_mono f hf xs _ w (hP a x w hp)
    · exact foldl_mem f hf P hP xs (f a y) x w hx hp

/-- A variable of a position of a triple pattern is a variable of its
    `PatSpec`. -/
theorem mem_specE_vars (tp : TriplePattern) (v : String) (hv : tp.s = .var v ∨ tp.p = .var v ∨ tp.o = .var v) :
    v ∈ (specE tp).vars := by
  unfold PatSpec.vars
  simp only [specE]
  have hmono : ∀ (a : Array String) (x : Arg) (w : String), w ∈ a →
      w ∈ (match x.var? with
        | some v => if a.contains v then a else a.push v
        | none => a) := by
    intro a x w h
    cases x.var? with
    | some v => exact dedup_mono a v w h
    | none => exact h
  have hm := foldl_mem (fun (acc : Array String) (x : Arg) => match x.var? with
      | some v => if acc.contains v then acc else acc.push v
      | none => acc) hmono (fun x w => x.var? = some w) (by
        intro a x w hx
        simp only [hx]
        exact dedup_mem a w)
  rcases hv with h | h | h
  · exact hm _ #[] (argS tp.s) v (by simp) (by rw [h]; rfl)
  · exact hm _ #[] (argT tp.p) v (by simp) (by rw [h]; rfl)
  · exact hm _ #[] (argT tp.o) v (by simp) (by rw [h]; rfl)

/-- A variable of a position of `b` is a variable of its block
    (`SemiBlock.vars`). -/
theorem mem_block_vars (b : Bgp) (k : SemiKind) (tp : TriplePattern) (htp : tp ∈ b) (v : String)
    (hv : tp.s = .var v ∨ tp.p = .var v ∨ tp.o = .var v) :
    (({ pats := (b.map specE).toArray, kind := k } : SemiBlock).vars.contains v) = true := by
  unfold SemiBlock.vars
  simp only [← Array.foldl_toList, List.toList_toArray]
  have hinner : ∀ (a : Array String) (q : PatSpec) (w : String), w ∈ a →
      w ∈ q.vars.toList.foldl (fun a v => if a.contains v then a else a.push v) a :=
    fun a q w h => foldl_mono _ (fun a v w h => dedup_mono a v w h) _ a w h
  have := foldl_mem (fun (a : Array String) (q : PatSpec) =>
      q.vars.toList.foldl (fun a v => if a.contains v then a else a.push v) a) hinner
    (fun q w => w ∈ q.vars) (by
      intro a q w hw
      exact foldl_mem _ (fun a v w h => dedup_mono a v w h) (fun x w => x = w) (by
        intro a x w e; subst e; exact dedup_mem a x) q.vars.toList a w w (by simpa using hw) rfl)
    (b.map specE) #[] (specE tp) v (List.mem_map.mpr ⟨tp, htp, rfl⟩) (mem_specE_vars tp v hv)
  simpa using this

theorem mem_subjVars (b : Bgp) (tp : TriplePattern) (htp : tp ∈ b) (v : String) (hv : tp.s = .var v) :
    ((b.map specE).toArray.filterMap fun p => p.s.var?).contains v = true := by
  have : v ∈ ((b.map specE).toArray.filterMap fun p => p.s.var?) := by
    simp only [Array.mem_filterMap, List.mem_toArray, List.mem_map]
    exact ⟨specE tp, ⟨tp, htp, rfl⟩, by simp [specE, hv, argS, Arg.var?]⟩
  simpa using this

theorem mem_predVars (b : Bgp) (tp : TriplePattern) (htp : tp ∈ b) (v : String) (hv : tp.p = .var v) :
    ((b.map specE).toArray.filterMap fun p => p.p.var?).contains v = true := by
  have : v ∈ ((b.map specE).toArray.filterMap fun p => p.p.var?) := by
    simp only [Array.mem_filterMap, List.mem_toArray, List.mem_map]
    exact ⟨specE tp, ⟨tp, htp, rfl⟩, by simp [specE, hv, argT, Arg.var?]⟩
  simpa using this

/-! ## Compatibility with a multiset of solution mappings -/

theorem compatible_bindEq (mu : Binding) {nu nu' : Binding} (h : IdGroup.BindEq nu nu') :
    Binding.compatible mu nu = Binding.compatible mu nu' := by
  apply Bool.eq_iff_iff.mpr
  rw [IdExists.compatible_iff, IdExists.compatible_iff]
  simp only [h _]

theorem any_perm {α : Type} (p : α → Bool) {A B : List α} (h : A.Perm B) : A.any p = B.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.mp hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.mpr hx, hp⟩⟩

/-- Whether some solution mapping is compatible with `mu` depends on the
    multiset of solution mappings only. -/
theorem any_solEquiv (mu : Binding) {A B : SolutionSeq} (h : IdGroup.SolEquiv A B) :
    A.any (Binding.compatible mu) = B.any (Binding.compatible mu) := by
  obtain ⟨C, hp, hw⟩ := h
  rw [any_perm _ hp]
  clear hp
  induction hw with
  | nil => rfl
  | cons hab _ ih => simp only [List.any_cons, compatible_bindEq mu hab, ih]

theorem idCompatible_nil : ∀ (r : IdRow), idCompatible r [] = true
  | [] => rfl
  | (_, _) :: rest => by simp [idCompatible, idLookup, idCompatible_nil rest]

/-! ## `semiHitsM` -/

section hits

open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk spo IdEquiv ipat Nd)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems (ExecLeaf listingsOf patOfSpec resolveIn_eq patG_spec ipatOf_spec
  bgpStore_withLocal unitTable_wf gctxId)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem ipatOf)
open L4Factoidal.Storage.Sbm11.BgpTableTheorems (BgpStore PatG evalBgpM_model nd_idRows)

theorem withLocal_idOf (st : Store Id) (voc : Array Term) (t : Term) : (st.withLocal voc).idOf t = st.idOf t := by
  unfold Store.withLocal; split <;> rfl

theorem rowIds_cell {O : UInt64 → Prop} (t : Table) (hrows : ∀ r ∈ t.idRows, RowIds O r) (c i : Nat)
    (hc : c < t.vars.size) (hi : i < t.rows) : O (t.at c i) ∨ t.at c i = unbound := by
  by_cases hu : t.at c i = unbound
  · exact Or.inr hu
  · left
    have hm : (t.vars[c]!, t.at c i) ∈ t.idRow i :=
      L4Factoidal.Storage.Sbm11.TableTheorems.mem_idRow.mpr ⟨c, hc, hu, rfl⟩
    exact hrows _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩) _ hm

variable (cx : NCx Id) (gof : Graph → GCtx) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta)
  (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)

/-- **EXISTS and NOT EXISTS of a basic graph pattern on a table (L5r, the
    table part).** Over the store with the query-local vocabulary of `nst`,
    `semiHitsM` with the patterns of `b` in the active graph `gof a` refuses
    (a `LocalRefusal`), or its test on each checked row `i` (`live i`) is
    whether `substBgp row b`, the row substituted into `b`, has a solution in
    `a`, and that substituted pattern has no `text:query` pattern.
    Hypotheses: those of the leaves (`hpm`, `hscan`, `hds`, `hid`, `hdec`,
    `hsok`, `hcid`, `hcidS`, `htermOf`, `hloc`), the invariant of the state,
    the tags of the store (`htagk`), the leaf conditions of `b` in `a`
    (`hleaf`) and no `text:query` predicate in `b` (`hnft`). -/
theorem semiHitsM_spec (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.Sequential)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidS : ∀ c, CidOk dec sok c (cid c))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (htagk : ∀ x, ok x → TagKind x (dec x))
    (nst : NSt) (hinv : LocalVocab.Inv cid nst)
    (a : Graph) (b : Bgp) (hleaf : ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) a)
    (hnft : ∀ tp ∈ b, NoFtPred tp) (k : SemiKind) (hk : k ≠ .minus)
    (t : Table) (ht : t.WF) (hrows : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r) (live : Nat → Bool) :
    (∃ e, semiHitsM (cx.st.withLocal nst.vocab) (IdGroup.resolveIn cx (gof a)) t
        { pats := (b.map specE).toArray, kind := k } live = throw e ∧ LocalRefusal e) ∨
      ∃ hits n s, semiHitsM (cx.st.withLocal nst.vocab) (IdGroup.resolveIn cx (gof a)) t
          { pats := (b.map specE).toArray, kind := k } live = pure (hits, n, s) ∧
        ∀ i, i < t.rows → live i = true →
          hits[i]! = !(evalBgp (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) a).isEmpty ∧
          bgpHasFulltext (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) = false := by
  have hterm : ∀ x, okV ok nst.vocab x → (cx.st.withLocal nst.vocab).termOf x = pure (decV dec nst.vocab x) :=
    termOf_withLocal cx.st cid dec ok htermOf hloc hinv
  have hkind : ∀ x, okV ok nst.vocab x → TagKind x (decV dec nst.vocab x) := by
    intro x hx
    rcases hx with hx | ⟨j, hj, rfl⟩
    · rw [decV_ok dec hloc _ hx]; exact htagk x hx
    · have htl : tagOf (localId j) = tagLocal := tag_localId j (by have := hinv.size; omega)
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> (rw [htl] at h; simp [tagLocal] at h)
  have hft : ∀ x, okV ok nst.vocab x → decV dec nst.vocab x = .iri fulltextQueryPred → tagOf x ≠ tagLocal →
      cid (.iri fulltextQueryPred) = some x := by
    intro x hx he hnl
    have hok : ok x := by
      rcases hx with hx | ⟨j, hj, rfl⟩
      · exact hx
      · exact absurd (tag_localId j (by have := hinv.size; omega)) hnl
    rw [decV_ok dec hloc _ hok] at he
    have hc := hcid (.iri fulltextQueryPred)
    cases e : cid (.iri fulltextQueryPred) with
    | none =>
      rw [e] at hc
      have := hc x hok
      rw [he, Term.eqb_refl] at this
      cases this
    | some z =>
      rw [e] at hc
      have := hc x hok
      rw [he, Term.eqb_refl] at this
      have : z = x := by simpa using this.symm
      rw [this]
  have hkm : (k == SemiKind.minus) = false := by cases k <;> first | rfl | exact absurd rfl hk
  unfold semiHitsM
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, hkm, Bool.false_eq_true, if_false]
  rw [withLocal_idOf, hid, pure_bind]
  generalize hC : forIn (m := ExceptT String Id) (List.range' 0 t.vars.size)
    (∅ : Std.HashMap (UInt64 × Bool) Bool) _ = C
  rcases check_loop (cx.st.withLocal nst.vocab) (decV dec nst.vocab) (okV ok nst.vocab) hterm hkind
      (cid (.iri fulltextQueryPred)) hft t (fun c i hc hi => rowIds_cell t hrows c i hc hi)
      (fun v => ({ pats := (b.map specE).toArray, kind := k } : SemiBlock).vars.contains v)
      (fun v => ((b.map specE).toArray.filterMap fun p => p.s.var?).contains v)
      (fun v => ((b.map specE).toArray.filterMap fun p => p.p.var?).contains v) live with
    ⟨e, he, hr⟩ | ⟨memo, he, hcells⟩
  · have hC' : C = throw e := by rw [← hC]; exact he
    left
    exact ⟨e, by rw [hC']; rfl, hr⟩
  have hC' : C = pure memo := by rw [← hC]; exact he
  rw [hC', pure_bind]
  -- a checked row is `SubstOk` and gives no `text:query` pattern
  have hrow : ∀ i, i < t.rows → live i = true →
      IdExists.SubstOk (decRow (decV dec nst.vocab) (t.idRow i)) b ∧
        bgpHasFulltext (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) = false := by
    intro i hi hli
    obtain ⟨hsub, hftp⟩ := subst_of_cells (decV dec nst.vocab) t ht i b
      (fun v => ({ pats := (b.map specE).toArray, kind := k } : SemiBlock).vars.contains v)
      (fun v => ((b.map specE).toArray.filterMap fun p => p.s.var?).contains v)
      (fun v => ((b.map specE).toArray.filterMap fun p => p.p.var?).contains v)
      (fun tp htp v hv => mem_block_vars b k tp htp v hv) (fun tp htp v hv => mem_subjVars b tp htp v hv)
      (fun tp htp v hv => mem_predVars b tp htp v hv) (fun c hc hin => hcells c i hc hi hin hli)
    exact ⟨hsub, noFulltext_subst _ b hnft hftp⟩
  have hrowi : ∀ i, i < t.rows → RowIds (okV ok nst.vocab) (t.idRow i) :=
    fun i hi => hrows _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have hkeys : ∀ i, ((decRow (decV dec nst.vocab) (t.idRow i)).map Prod.fst).Nodup := by
    intro i
    have e : (decRow (decV dec nst.vocab) (t.idRow i)).map Prod.fst = (t.idRow i).map Prod.fst := by
      simp [decRow, Function.comp_def]
    rw [e]
    exact L4Factoidal.Storage.Sbm11.BgpTableTheorems.nd_idRow t ht.nodup i
  have hdV := hdecV cid dec ok hdec hcid hloc hinv
  by_cases hb : b = []
  · subst hb
    rw [show (([] : Bgp).map specE).toArray.isEmpty = true from rfl]
    simp only [if_true, pure_bind]
    right
    refine ⟨_, _, _, rfl, fun i hi hli => ⟨?_, (hrow i hi hli).2⟩⟩
    rw [SemiTableTheorems.semiMatches_rows t ({ vars := #[], cols := #[], rows := 1 } : Table) unitTable_wf i hi]
    show [([] : IdRow)].any (idCompatible (t.idRow i)) = _
    simp [idCompatible_nil, substBgp, evalBgp, evalBgpFrom]
  have hne : (b.map specE).toArray.isEmpty = false := by
    cases b with
    | nil => exact absurd rfl hb
    | cons _ _ => rfl
  simp only [hne, Bool.false_eq_true, if_false]
  have hmap : Array.mapM (IdGroup.resolveIn cx (gof a)) (b.map specE).toArray =
      pure ((b.map specE).toArray.map (patOfSpec cid (gof a))) := by
    have : IdGroup.resolveIn cx (gof a) = fun p => pure (patOfSpec cid (gof a) p) :=
      funext (resolveIn_eq cx cid hid hds (gof a))
    rw [this, Array.mapM_pure]
  rw [hmap, pure_bind]
  have hm : ((b.map specE).toArray.map (patOfSpec cid (gof a))).toList.map ipatOf = b.map (ipat cid) := by
    simp only [Array.toList_map, List.toList_toArray, List.map_map]
    apply List.map_congr_left
    intro tp htp'
    exact ipatOf_spec cid (gof a) tp (hleaf.2 tp htp')
  generalize hpats : (b.map specE).toArray.map (patOfSpec cid (gof a)) = pats at hm
  have hsz : 0 < pats.size := by
    rw [← hpats]
    cases b with
    | nil => exact absurd rfl hb
    | cons _ _ => simp
  have hpg : ∀ i, i < pats.size → PatG (gctxId (gof a)) pats[i]! := by
    intro i hi
    rw [getElem!_pos pats i hi]
    have hmem : pats[i] ∈ pats.toList := Array.getElem_mem_toList hi
    generalize pats[i] = q at hmem ⊢
    rw [← hpats] at hmem
    simp only [Array.toList_map, List.toList_toArray, List.mem_map] at hmem
    obtain ⟨_, ⟨tp, _, rfl⟩, rfl⟩ := hmem
    exact patG_spec cid (gof a) tp
  have hst : BgpStore (cx.st.withLocal nst.vocab) (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
    bgpStore_withLocal cx.st nst.vocab _ _ ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hleaf.1.1.2 ⟨k, hk⟩⟩, hscan⟩
  obtain ⟨tab, lines, stats, he2, hwf, hnd, heq⟩ := evalBgpM_model _ pats hsz _ _ hst hpg
  rw [he2, pure_bind]
  right
  refine ⟨_, _, _, rfl, fun i hi hli => ⟨?_, (hrow i hi hli).2⟩⟩
  rw [SemiTableTheorems.semiMatches_rows t tab hwf i hi]
  -- the rows of the body are the solutions of `b` in `a`
  rw [hm] at heq
  have hnd0 : ∀ r ∈ ([[]] : List IdRow), Nd r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.nodup_nil
  have h1 := IdLeaf.bgpJoin_equiv (listingsOf gof prb ms spo a) (fun _ => listingsOf gof prb ms spo a)
    (fun _ => List.Perm.refl _) (b.map (ipat cid)) [[]] hnd0
  rw [List.flatMap_singleton] at h1
  have heq' := IdEquiv.trans heq h1.symm
  obtain ⟨hs1, hs2⟩ := IdLeaf.leafRel_of_store env ds (listingsOf gof prb ms) (fun _ => spo)
    (fun _ b => ⟨b, List.Perm.refl b⟩) cid dec idv sok ok hdec hsok hcidS (.bgp b) a hleaf.1
  have hsol : IdGroup.SolEquiv (evalBgp b a) (tab.idRows.map (decRow dec)) := by
    rw [← IdLeaf.refSol_bgp env ds b a hleaf.1.2.2]
    exact IdGroup.SolEquiv.trans hs1 (IdLeaf.solEquiv_decode dec heq'.symm)
  have htabok : ∀ r ∈ tab.idRows, RowIds ok r := ExecLeafTheorems.rowIds_of_equiv ok hnd heq' hs2
  have e1 : tab.idRows.any (idCompatible (t.idRow i)) =
      (tab.idRows.map (decRow dec)).any (Binding.compatible (decRow (decV dec nst.vocab) (t.idRow i))) := by
    rw [List.any_map]
    apply SemiTableTheorems.any_congr_mem
    intro r hr
    simp only [Function.comp_def]
    rw [← L4Factoidal.Storage.Sbm11.OptJoin.compatible_decRow (decV dec nst.vocab) (okV ok nst.vocab) hdV
      (t.idRow i) r (hrowi i hi)
      (fun p hp => ok_okV (htabok r hr p hp))]
    congr 1
    unfold decRow
    apply List.map_congr_left
    intro p hp
    obtain ⟨v, x⟩ := p
    simp only [decV_ok dec hloc _ (htabok r hr (v, x) hp)]
  rw [e1, ← any_solEquiv _ hsol,
    IdExists.exists_bgp_iff a b _ hleaf.1.2.1 (hrow i hi hli).1 (hkeys i)]
  simp

end hits

/-! ## The mask of a condition -/

/-- The EXISTS-free conjuncts and the EXISTS and NOT EXISTS conjuncts of a
    basic graph pattern cover a condition with no `NOT EXISTS {}`: `EXISTS {}`
    is true. -/
theorem all_split (f : Expr → Bool) :
    ∀ (L : List Expr), (∀ cj ∈ L, cj = .existsPat .empty → f cj = true) → (∀ cj ∈ L, CjExOk cj) →
      L.any isNotExistsEmpty = false →
      L.all f = ((L.filter (·.existsFree)).all f && (L.filter fun cj => (semiOf cj).isSome).all f)
  | [], _, _, _ => rfl
  | cj :: L, hemp, h, hn => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hn
    have ih := all_split f L (fun x hx => hemp x (List.mem_cons_of_mem _ hx))
      (fun x hx => h x (List.mem_cons_of_mem _ hx)) hn.2
    simp only [List.all_cons, List.filter_cons]
    rw [ih]
    rcases h cj List.mem_cons_self with hok | ⟨b, hb | hb, _⟩ | hb | hb
    · simp only [hok.ef, if_true, semiOf_existsFree hok.ef, Option.isSome_none, Bool.false_eq_true, if_false,
        List.all_cons]
      cases f cj <;> simp
    · subst hb
      simp only [Expr.existsFree, Bool.false_eq_true, if_false, semiOf, Option.isSome_some, if_true,
        List.all_cons]
      cases f (.existsPat (.bgp b)) <;> simp
    · subst hb
      simp only [Expr.existsFree, Bool.false_eq_true, if_false, semiOf, Option.isSome_some, if_true,
        List.all_cons]
      cases f (.notExistsPat (.bgp b)) <;> simp
    · subst hb
      simp only [Expr.existsFree, Bool.false_eq_true, if_false, semiOf, Option.isSome_none,
        hemp _ List.mem_cons_self rfl, Bool.true_and]
    · subst hb
      simp [isNotExistsEmpty] at hn

theorem fa2_semiOf : ∀ (L : List Expr),
    Fa2 (fun cj blk => semiOf cj = some blk) (L.filter fun cj => (semiOf cj).isSome) (L.filterMap semiOf)
  | [] => Fa2.nil
  | cj :: L => by
    simp only [List.filter_cons, List.filterMap_cons]
    cases h : semiOf cj with
    | none => simpa using fa2_semiOf L
    | some blk =>
      simp only [Option.isSome_some, if_true]
      exact Fa2.cons (R := fun cj blk => semiOf cj = some blk) h (fa2_semiOf L)

/-- `liftE` of a run that refuses or yields. -/
theorem liftE_run {α : Type} (x : ExceptT String Id α) (nst : NSt) :
    (liftE x : NM Id α).run nst = (do let a ← x; pure (a, nst)) := by
  unfold liftE; rw [StateT.run_lift]

/-- `CidOk` on the ids of a state, for a term with an id, or for any term when
    the state has no local id. -/
theorem cidOkV (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcid : ∀ c, IdLeaf.CidOk dec ok c (cid c)) (hcidok : ∀ t x, cid t = some x → ok x)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {voc : Array Term} {ix : Std.HashMap Term Nat}
    (hinv : VocInv cid voc ix) :
    ∀ c, ((cid c).isSome = true ∨ voc.isEmpty = true) → IdLeaf.CidOk (decV dec voc) (okV ok voc) c (cid c) := by
  intro c hc
  rcases hc with hc | hc
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc
    rw [hx]
    exact cidOkV_some cid dec ok hcid hcidok hloc hinv c x hx
  · have h := hcid c
    have he : voc = #[] := by simpa using hc
    subst he
    cases e : cid c with
    | none =>
      rw [e] at h
      intro y hy
      rcases hy with hy | ⟨k, hk, _⟩
      · rw [decV_ok dec hloc _ hy]; exact h y hy
      · simp at hk
    | some x =>
      rw [e] at h
      intro y hy
      rcases hy with hy | ⟨k, hk, _⟩
      · rw [decV_ok dec hloc _ hy]; exact h y hy
      · simp at hk

/-- The condition has an EXISTS or NOT EXISTS conjunct: the reference reads
    the dataset of the environment for it (`substituteExistentials`). -/
def HasExists (c : Expr) : Prop := ∃ cj ∈ (conjuncts c).toList, cj.existsFree = false

/-! ## The condition reads the row through its lookups -/

/-- The value of a conjunct the id path runs reads the row only through its
    lookups. -/
theorem cjVal_bindEq (env : EvalEnv) (a : Graph) (cj : Expr) (hcj : CjExOk cj) (mu1 mu2 : Binding)
    (h : ∀ v, mu1.lookup v = mu2.lookup v) : cjVal env a mu1 cj = cjVal env a mu2 cj := by
  have hl : ∀ v, (Binding.empty.merge mu1).lookup v = (Binding.empty.merge mu2).lookup v := fun v => by
    rw [lookup_merge_empty, lookup_merge_empty, h]
  rcases hcj with hok | ⟨b, hb | hb, _⟩ | hb | hb
  · rw [cjVal_existsFree env a _ cj hok.ef, cjVal_existsFree env a _ cj hok.ef, evalIn_bindEq env _ _ h]
  all_goals
    subst hb
    unfold cjVal
    rw [evalIn_bindEq env _ _ hl]
    simp only [substituteExistentials, QueryPattern.lowerWith, IdExists.substBgp_congr hl]

/-- **The reference FILTER of a condition the id path runs reads the row
    through its lookups.** -/
theorem filterFn_bindEq (env : EvalEnv) (c : Expr) (a : Graph) (hc : FilterExOk c) (mu1 mu2 : Binding)
    (h : ∀ v, mu1.lookup v = mu2.lookup v) : IdGroup.filterFn env c a mu1 = IdGroup.filterFn env c a mu2 := by
  rw [filterFn_conjuncts, filterFn_conjuncts]
  have : ∀ (L : List Expr), (∀ cj ∈ L, CjExOk cj) → L.all (cjVal env a mu1) = L.all (cjVal env a mu2) := by
    intro L hL
    induction L with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.all_cons, cjVal_bindEq env a x (hL x List.mem_cons_self) mu1 mu2 h,
        ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))]
  exact this _ hc

section mask

open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk spo)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems (ExecLeaf listingsOf)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem)

variable (cx : NCx Id) (gof : Graph → GCtx) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta)
  (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)

/-- What the loop over the semi-join blocks of `filterMaskM` keeps: the state
    keeps its vocabulary, and entry `i` of the mask is the mask of the
    EXISTS-free conjuncts and the values of the EXISTS conjuncts `D` done so
    far on row `i`. -/
def MaskInv (env : EvalEnv) (a : Graph) (D : UInt64 → Term) (t : Table) (keep0 : Array Bool) (nst : NSt)
    (done : List Expr) (keep : Array Bool) (s : NSt) : Prop :=
  s.vocab = nst.vocab ∧ s.localIdx = nst.localIdx ∧ keep.size = t.rows ∧
    ∀ i, i < t.rows → keep[i]! = (keep0[i]! && done.all (cjVal env a (decRow D (t.idRow i))))

theorem mapIdx_get (keep : Array Bool) (f : Nat → Bool → Bool) (i : Nat) (hi : i < keep.size) :
    (keep.mapIdx f)[i]! = f i keep[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_mapIdx, getElem!_pos keep i hi]

/-- **The loop over the EXISTS and NOT EXISTS blocks.** -/
theorem semis_loop (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.Sequential)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidS : ∀ c, CidOk dec sok c (cid c))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (htagk : ∀ x, ok x → TagKind x (dec x))
    (nst : NSt) (hinv : LocalVocab.Inv cid nst) (a : Graph)
    (t : Table) (ht : t.WF) (hrows : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r) (keep0 : Array Bool)
    (c : Expr) (hds0 : HasExists c → ∃ ds0, env.dataset = some ds0)
    (hbody : ∀ b, (Expr.existsPat (.bgp b) ∈ (conjuncts c).toList ∨
      Expr.notExistsPat (.bgp b) ∈ (conjuncts c).toList) →
      ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) a ∧ ∀ tp ∈ b, NoFtPred tp) :
    ∀ (E : List Expr) (S : List SemiBlock), Fa2 (fun cj blk => semiOf cj = some blk) E S →
      (∀ cj ∈ E, cj ∈ (conjuncts c).toList) →
      ∀ (done : List Expr) (keep : Array Bool) (s : NSt),
        MaskInv env a (decV dec nst.vocab) t keep0 nst done keep s →
        Ends ((forIn S keep fun (b : SemiBlock) (keep : Array Bool) => do
            let x ← liftE (semiHitsM (cx.st.withLocal nst.vocab) (IdGroup.resolveIn cx (gof a)) t b fun i => keep[i]!)
            IdGroup.addStats x.2.2
            pure (ForInStep.yield (keep.mapIdx fun i k => k && x.1[i]! == (b.kind == SemiKind.semi)))).run s)
          (fun keep' s' => MaskInv env a (decV dec nst.vocab) t keep0 nst (done ++ E) keep' s') := by
  intro E S hES
  induction hES with
  | nil =>
    intro _ done keep s hI
    exact ends_pure rfl (by simpa using hI)
  | @cons cj blk E' S' hcb _ ih =>
    intro hmem done keep s hI
    obtain ⟨hv1, hv2, hsz, hk⟩ := hI
    -- one block: `EXISTS { b }` (`neg = false`) or `NOT EXISTS { b }`
    have hstep : ∀ (b : Bgp) (k : SemiKind) (hk0 : k ≠ .minus),
        blk = { pats := (b.map specE).toArray, kind := k } →
        (Expr.existsPat (.bgp b) ∈ (conjuncts c).toList ∨ Expr.notExistsPat (.bgp b) ∈ (conjuncts c).toList) →
        (∀ i, i < t.rows → keep[i]! = true →
          ∀ h : Bool, h = !(evalBgp (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) a).isEmpty →
            bgpHasFulltext (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) = false →
            (h == (k == SemiKind.semi)) = cjVal env a (decRow (decV dec nst.vocab) (t.idRow i)) cj) →
        Ends ((forIn (blk :: S') keep fun (b : SemiBlock) (keep : Array Bool) => do
            let x ← liftE (semiHitsM (cx.st.withLocal nst.vocab) (IdGroup.resolveIn cx (gof a)) t b fun i => keep[i]!)
            IdGroup.addStats x.2.2
            pure (ForInStep.yield (keep.mapIdx fun i k => k && x.1[i]! == (b.kind == SemiKind.semi)))).run s)
          (fun keep' s' => MaskInv env a (decV dec nst.vocab) t keep0 nst (done ++ cj :: E') keep' s') := by
      intro b k hk0 hblk hin hval
      subst hblk
      obtain ⟨hleaf, hnft⟩ := hbody b hin
      rw [List.forIn_cons, StateT.run_bind, StateT.run_bind, liftE_run]
      rcases semiHitsM_spec cx gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok hcid hcidS htermOf
          hloc htagk nst hinv a b hleaf hnft k hk0 t ht hrows (fun i => keep[i]!) with
        ⟨e, he, hr⟩ | ⟨hits, n, st', he, hh⟩
      · left
        exact ⟨e, by rw [he]; rfl, hr⟩
      · rw [he]
        simp only [pure_bind, StateT.run_bind]
        simp only [IdGroup.addStats, StateT.run_modify, pure_bind, StateT.run_pure]
        refine ends_mono (ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) (done ++ [cj]) _ _ ⟨hv1, hv2, ?_, ?_⟩)
          (fun keep' s' h => by simpa using h)
        · simp [hsz]
        · intro i hi
          rw [mapIdx_get keep _ i (by rw [hsz]; exact hi), hk i hi]
          simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
          rw [← Bool.and_assoc]
          by_cases hAB : (keep0[i]! && done.all (cjVal env a (decRow (decV dec nst.vocab) (t.idRow i)))) = true
          · obtain ⟨hh1, hh2⟩ := hh i hi (by rw [hk i hi]; exact hAB)
            rw [hAB]
            simp only [Bool.true_and]
            exact hval i hi (by rw [hk i hi]; exact hAB) _ hh1 hh2
          · simp only [Bool.not_eq_true] at hAB
            rw [hAB]
            rfl
    revert hcb
    unfold semiOf
    split
    · next b =>
      intro hcb
      cases hcb
      obtain ⟨ds0, hds0⟩ := hds0 ⟨_, hmem _ List.mem_cons_self, rfl⟩
      exact hstep b .semi (by intro h; cases h) rfl (Or.inl (hmem _ List.mem_cons_self)) (by
        intro i _ _ h hh hft
        rw [(cjVal_existsBgp env ds0 hds0 a _ b hft).1, hh]
        cases (evalBgp (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) a).isEmpty <;> rfl)
    · next b =>
      intro hcb
      cases hcb
      obtain ⟨ds0, hds0⟩ := hds0 ⟨_, hmem _ List.mem_cons_self, rfl⟩
      exact hstep b .anti (by intro h; cases h) rfl (Or.inr (hmem _ List.mem_cons_self)) (by
        intro i _ _ h hh hft
        rw [(cjVal_existsBgp env ds0 hds0 a _ b hft).2, hh]
        cases (evalBgp (substBgp (decRow (decV dec nst.vocab) (t.idRow i)) b) a).isEmpty <;> rfl)
    · intro hcb; cases hcb
/-- **The mask of a FILTER condition, EXISTS included.** For a condition
    whose conjuncts are `CjExOk`, each EXISTS body with the leaf conditions in
    the active graph `a` (`hbody`), a dataset in the reference's environment
    `env`, the id path's environment agreeing with it on `ext`, `now` and
    `base` (`henv`), the hypotheses of `semiHitsM_spec` and of the EXISTS-free conjuncts
    (`FilterTableTheorems`): `filterMaskM` refuses (a `LocalRefusal`), or
    returns, keeping the vocabulary, a mask with one entry per row of `t`,
    entry `i` the reference FILTER (`IdGroup.filterFn`) of the condition on
    the decoded row `i`. -/
theorem filterMaskM_spec (env : EvalEnv) (ds : Dataset)
    (henv : ExprLocalTheorems.EnvAgree cx.env env)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.Sequential)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidS : ∀ c, CidOk dec sok c (cid c))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (htagk : ∀ x, ok x → TagKind x (dec x)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hcidok : ∀ t x, cid t = some x → ok x)
    (nst : NSt) (hinv : LocalVocab.Inv cid nst) (a : Graph)
    (t : Table) (ht : t.WF) (hrows : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r)
    (c : Expr) (hc : FilterExOk c) (hds0 : HasExists c → ∃ ds0, env.dataset = some ds0)
    (hbody : ∀ b, ExistsBgp c b → ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) a) :
    Ends ((filterMaskM cx (gof a) t c).run nst) (fun keep nst' => nst'.vocab = nst.vocab ∧
      nst'.localIdx = nst.localIdx ∧ keep.size = t.rows ∧
      ∀ i, i < t.rows → keep[i]! = IdGroup.filterFn env c a (decRow (decV dec nst.vocab) (t.idRow i))) := by
  obtain ⟨fs, hk, hfs, hve⟩ := filterKindsM_spec_ex cx cid hid t c hc nst
  unfold filterMaskM
  rw [StateT.run_bind, hk, pure_bind]
  simp only []
  by_cases hn : ((conjuncts c).toList.any isNotExistsEmpty) = true
  · simp only [hn, if_true]
    refine ends_pure rfl ⟨rfl, rfl, by simp, fun i hi => ?_⟩
    rw [filterFn_conjuncts]
    obtain ⟨cj, hcj, hne⟩ := List.any_eq_true.mp hn
    have e : cj = .notExistsPat .empty := by
      unfold isNotExistsEmpty at hne; split at hne <;> simp_all
    subst e
    obtain ⟨ds0, hds0⟩ := hds0 ⟨_, hcj, rfl⟩
    rw [getElem!_pos _ i (by simpa using hi)]
    symm
    simp only [Array.getElem_replicate, List.all_eq_false]
    exact ⟨_, hcj, by rw [cjVal_notExistsEmpty env ds0 hds0]; simp⟩
  have hn' : ((conjuncts c).toList.any isNotExistsEmpty) = false := by simpa using hn
  simp only [hn', Bool.false_eq_true, if_false]
  rw [StateT.run_bind]
  have hls : (IdGroup.localStore cx).run nst = pure (cx.st.withLocal nst.vocab, nst) := rfl
  rw [hls, pure_bind, StateT.run_bind, liftE_run]
  have hdV := hdecV cid dec ok hdec hcid hloc hinv
  have hrows' := rows_of t (okV ok nst.vocab) hrows
  have hcidV := cidOkV cid dec ok hcid hcidok hloc hinv
  have hcidN' : ∀ t x, cid t = some x → decV dec nst.vocab x = normalizeTerm t :=
    fun t x hx => by rw [decV_ok dec hloc _ (hcidok t x hx)]; exact hcidN t x hx
  have hterm : ∀ x, okV ok nst.vocab x → (cx.st.withLocal nst.vocab).termOf x = pure (decV dec nst.vocab x) :=
    termOf_withLocal cx.st cid dec ok htermOf hloc hinv
  -- the EXISTS-free conjuncts
  have hplain : ∀ cj ∈ (conjuncts c).toList.filter (·.existsFree), CjOk cj := by
    intro cj hcj
    obtain ⟨hm, hef⟩ := List.mem_filter.mp hcj
    rcases hc cj hm with hok | ⟨b, hb | hb, _⟩ | hb | hb
    · exact hok
    all_goals (subst hb; simp [Expr.existsFree] at hef)
  -- the code classifies the conjuncts with its own environment `cx.env`;
  -- `Expr.evalIn` reads only what `henv` says the two environments share
  have hsem : ∀ cj ∈ (conjuncts c).toList.filter (·.existsFree), ∀ k ∈ fs.toList, KindOf cx.env cid t cj k →
      KWf t k ∧ ∀ i, i < t.rows → keepOf (decV dec nst.vocab) t i k =
        cjVal env a (decRow (decV dec nst.vocab) (t.idRow i)) cj := by
    intro cj hcj k hk' hK
    obtain ⟨hkw, hkv⟩ := kind_sem (decV dec nst.vocab) (okV ok nst.vocab) cid _ hcidV hcidN' hdV t ht hrows' cx.env
      cj (hplain cj hcj) k hK (hve k hk')
    refine ⟨hkw, fun i hi => ?_⟩
    rw [hkv i hi, cjVal_existsFree env a _ cj (List.mem_filter.mp hcj).2, ExprLocalTheorems.evalIn_agree henv]
  have hkw : ∀ k ∈ fs.toList, KWf t k := by
    intro k hk'
    obtain ⟨cj, hcj, hK⟩ := hfs.mem_right k hk'
    exact (hsem cj hcj k hk' hK).1
  have hterm' : ∀ i, i < t.rows → ∀ p ∈ t.idRow i, (cx.st.withLocal nst.vocab).termOf p.2 =
      pure (decV dec nst.vocab p.2) := fun i hi p hp => hterm p.2 (hrows' i hi p hp)
  obtain ⟨keep0, ms', hfk, hsz0, hkk⟩ := filterKeep_spec (cx.st.withLocal nst.vocab) (decV dec nst.vocab) t ht
    hterm' fs hkw _ (memoOk_empty (decV dec nst.vocab) fs)
  rw [hfk]
  simp only [pure_bind]
  rw [StateT.run_bind, ← Array.forIn_toList, List.toList_toArray]
  have hbody' : ∀ b, (Expr.existsPat (.bgp b) ∈ (conjuncts c).toList ∨
      Expr.notExistsPat (.bgp b) ∈ (conjuncts c).toList) →
      ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) a ∧ ∀ tp ∈ b, NoFtPred tp := by
    intro b hb
    refine ⟨hbody b hb, ?_⟩
    rcases hb with hb | hb
    · rcases hc _ hb with hok | ⟨b', hb' | hb', htp⟩ | hb' | hb'
      · exact absurd hok.ef (by simp [Expr.existsFree])
      · cases hb'; exact fun tp h => (htp tp h).2
      · cases hb'
      · cases hb'
      · cases hb'
    · rcases hc _ hb with hok | ⟨b', hb' | hb', htp⟩ | hb' | hb'
      · exact absurd hok.ef (by simp [Expr.existsFree])
      · cases hb'
      · cases hb'; exact fun tp h => (htp tp h).2
      · cases hb'
      · cases hb'
  refine ends_bind (semis_loop cx gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok hcid hcidS
    htermOf hloc htagk nst hinv a t ht hrows keep0 c hds0 hbody' _ _ (fa2_semiOf _)
    (fun x hx => (List.mem_filter.mp hx).1) [] keep0 nst ⟨rfl, rfl, hsz0, fun i hi => by simp⟩) fun keep s' hI => ?_
  obtain ⟨hv1, hv2, hsz, hkeep⟩ := hI
  refine ends_pure rfl ⟨hv1, hv2, hsz, fun i hi => ?_⟩
  rw [hkeep i hi, hkk i hi, filterFn_conjuncts,
    all_split _ _ (fun cj hcj e => by
      subst e
      obtain ⟨ds0, hds0⟩ := hds0 ⟨_, hcj, rfl⟩
      exact cjVal_existsEmpty env ds0 hds0 a _) hc hn', List.nil_append]
  congr 1
  apply Fa2.all_eq' _ _ hfs
  intro cj hcj k hk' hK
  exact (hsem cj hcj k hk' hK).2 i hi

/-- **FILTER as `filterM` runs it, EXISTS included.** Under the hypotheses of
    `filterMaskM_spec`, `filterM` refuses (a `LocalRefusal`), or returns,
    keeping the vocabulary, a well-formed table whose rows are the rows of `t`
    that pass the reference FILTER (`IdGroup.filterFn`), in order. -/
theorem filterM_run (env : EvalEnv) (ds : Dataset)
    (henv : ExprLocalTheorems.EnvAgree cx.env env)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.Sequential)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidS : ∀ c, CidOk dec sok c (cid c))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (htagk : ∀ x, ok x → TagKind x (dec x)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hcidok : ∀ t x, cid t = some x → ok x)
    (nst : NSt) (hinv : LocalVocab.Inv cid nst) (a : Graph)
    (t : Table) (ht : t.WF) (hrows : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r)
    (c : Expr) (hc : FilterExOk c) (hds0 : HasExists c → ∃ ds0, env.dataset = some ds0)
    (hbody : ∀ b, ExistsBgp c b → ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) a) :
    Ends ((filterM cx (gof a) t c).run nst) (fun t' nst' => t'.WF ∧
      t'.idRows = t.idRows.filter (fun r => IdGroup.filterFn env c a (decRow (decV dec nst.vocab) r)) ∧
      nst'.vocab = nst.vocab ∧ nst'.localIdx = nst.localIdx) := by
  unfold filterM
  refine ends_bind (filterMaskM_spec cx gof prb ms cid dec idv sok ok env ds henv hpm hscan hds hid hdec hsok
    hcid hcidS htermOf hloc htagk hcidN hcidok nst hinv a t ht hrows c hc hds0 hbody)
    fun keep s ⟨hv1, hv2, _, hkeep⟩ => ?_
  obtain ⟨hwf, _, hsel⟩ := select_spec t ht fun i => keep[i]!
  refine ends_pure (a := t.select fun i => keep[i]!) (s := { s with lines := s.lines.push _ }) rfl
    ⟨hwf, ?_, hv1, hv2⟩
  rw [hsel, Table.idRows, List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_def]
  rw [hkeep i hi]

/-- **The run of `leftJoinCondM` with a condition other than `true`, EXISTS
    included.** Under the hypotheses of `filterMaskM_spec` on the merged rows
    of the compatible pairs (`IdJoin.joinIds l r`), `leftJoinCondM` refuses (a
    `LocalRefusal`), or returns, keeping the vocabulary, the `LeftJoin` table
    of a mask whose entry `k` is the reference FILTER of the condition on
    merged row `k`. -/
theorem leftJoinCond_run (env : EvalEnv) (ds : Dataset)
    (henv : ExprLocalTheorems.EnvAgree cx.env env)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.Sequential)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidS : ∀ c, CidOk dec sok c (cid c))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (htagk : ∀ x, ok x → TagKind x (dec x)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hcidok : ∀ t x, cid t = some x → ok x)
    (nst : NSt) (hinv : LocalVocab.Inv cid nst) (a : Graph) (l r : Table)
    (hm : (IdJoin.joinIds l r).WF) (hrows : ∀ q ∈ (IdJoin.joinIds l r).idRows, RowIds (okV ok nst.vocab) q)
    (c : Expr) (hc : FilterExOk c) (hds0 : HasExists c → ∃ ds0, env.dataset = some ds0)
    (htriv : c ≠ .boolLit true)
    (hbody : ∀ b, ExistsBgp c b → ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) a) :
    Ends ((leftJoinCondM cx (gof a) l r c).run nst) (fun T nst' => ∃ keep,
      T = LeftJoinTableTheorems.ljTable (IdJoin.joinIds l r) l (IdGroup.ljSource l.rows
        (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1 keep) ∧
      nst'.vocab = nst.vocab ∧ nst'.localIdx = nst.localIdx ∧ keep.size = (IdJoin.joinIds l r).rows ∧
      ∀ k, k < (IdJoin.joinIds l r).rows →
        keep[k]! = IdGroup.filterFn env c a (decRow (decV dec nst.vocab) ((IdJoin.joinIds l r).idRow k))) := by
  have hspec := filterMaskM_spec cx gof prb ms cid dec idv sok ok env ds henv hpm hscan hds hid hdec hsok
    hcid hcidS htermOf hloc htagk hcidN hcidok nst hinv a (IdJoin.joinIds l r) hm hrows c hc hds0 hbody
  unfold leftJoinCondM
  revert hspec htriv
  cases c
  case boolLit b =>
    cases b
    · intro _ hspec
      simp only [Bool.false_eq_true, if_false]
      exact ends_bind hspec fun keep s ⟨hv1, hv2, hsz, hkeep⟩ => ends_pure rfl ⟨keep, rfl, hv1, hv2, hsz, hkeep⟩
    · intro h _; exact absurd rfl h
  all_goals
    intro _ hspec
    simp only [Bool.false_eq_true, if_false]
    exact ends_bind hspec fun keep s ⟨hv1, hv2, hsz, hkeep⟩ => ends_pure rfl ⟨keep, rfl, hv1, hv2, hsz, hkeep⟩

end mask

end L4Factoidal.Storage.Sbm11.ExistsTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.conjuncts_all
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.cjVal_existsBgp
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.filterKindsM_spec_ex
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.substCellM_spec
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.check_loop
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.subst_of_cells
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.noFulltext_subst
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.semiHitsM_spec
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.filterFn_bindEq
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.filterMaskM_spec
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.filterM_run
#print axioms L4Factoidal.Storage.Sbm11.ExistsTableTheorems.leftJoinCond_run

