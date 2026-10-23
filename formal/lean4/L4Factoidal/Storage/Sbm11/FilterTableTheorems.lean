/-
L4Factoidal.Storage.Sbm11.FilterTableTheorems — FILTER and OPTIONAL with a
condition as the nested evaluator runs them
(https://github.com/danbri/factoidal/issues/776; the FILTER step of L5t,
lemma L4q of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `select_spec` (moved here from `GroupTableTheorems`): `Table.select` keeps
  the rows its test passes, in order.
* `filterKindsM_spec`: over a store whose dictionary lookup is `cid`,
  `IdGroup.filterKindsM` classifies each conjunct of an EXISTS-free condition
  whose conjuncts are `CjOk` (`FilterOk`) as `FilterIdTheorems.KindOf` says,
  without changing the state.
* `keep_all`: the tests of those kinds are covered by `filterKeep_spec`, and
  their conjunction in a row is the reference FILTER of the condition on the
  decoded row (`IdGroup.filterFn`, via `kind_sem` and `conjuncts_spec`).
* `filterM_run`: `IdGroup.filterM` returns a well-formed table whose rows
  are the rows of its input that pass the reference FILTER, in order.
* `leftJoinCond_run`: for a condition other than `true`,
  `IdGroup.leftJoinCondM` evaluates the condition on the merged rows of the
  compatible pairs as a mask (`filterKeep`); entry `k` is the reference
  FILTER on merged row `k`.
* `ljSource_spec'`, `leftJoinCond_rows`: with any mask, `ljSource` lists per
  left row its pairs that passed, else the left row alone; so the table's
  rows are, row for row, the same solution mappings as
  `IdGroup.idLeftJoinC cond` of the input rows.

The store hypotheses beyond those of the leaves: `termOf` decodes the ids in
`ok` as `dec` does and no id in `ok` has the query-local tag (`htermOf`,
`hloc`); the dictionary lookup is exact on the ids in `ok` and answers the
tag-folded term itself (`CidOk` over `ok`, `hcidN`); the environment of the
evaluator is the query's (`henv`).

## Not proved here

A condition with an EXISTS or NOT EXISTS conjunct (`semiJoinByM`, and the
tagged-table path of `leftJoinCondM`), and the string tests on dictionary
keys (`FilterIdTheorems.StrForm`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FilterIdTheorems

namespace L4Factoidal.Storage.Sbm11.FilterTableTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt NM GCtx filterKindsM filterM leftJoinCondM liftE)
open L4Factoidal.Storage.Sbm11.FilterIdTheorems
open L4Factoidal.Storage.Sbm11.ExprLocalTheorems

open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Qlvr (gather)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq RowsEq ColHolds forIn_range_inv range'_succ_filter gather_at)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds unbound)

/-! ## `Table.select` -/

theorem select_idx (t : Table) (keep : Nat → Bool) :
    (forIn (m := _root_.Id) (List.range' 0 t.rows) (#[] : Array Nat) fun i r =>
        if keep i then ForInStep.yield (r.push i) else ForInStep.yield r).run.toList =
      (List.range' 0 t.rows).filter keep := by
  generalize hF : forIn (m := _root_.Id) (List.range' 0 t.rows) (#[] : Array Nat) _ = F
  have := forIn_range_inv t.rows (fun k (r : Array Nat) => r.toList = (List.range' 0 k).filter keep) hF
    (by simp) (fun k r _ hk => by
      by_cases hc : keep k = true
      · refine ⟨r.push k, by simp [hc, Id.run], ?_⟩
        rw [range'_succ_filter, Array.toList_push, hk]; simp [hc]
      · refine ⟨r, by simp [hc, Id.run], ?_⟩
        rw [range'_succ_filter, hk]; simp [hc])
  exact this

/-- `Table.select` of a well-formed table: a well-formed table whose rows are
    the rows `i` with `keep i`, in order. -/
theorem select_spec (t : Table) (ht : t.WF) (keep : Nat → Bool) :
    (t.select keep).WF ∧ (t.select keep).vars = t.vars ∧
      (t.select keep).idRows = ((List.range t.rows).filter keep).map t.idRow := by
  have hidx := select_idx t keep
  unfold Table.select
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize forIn (m := _root_.Id) (List.range' 0 t.rows) (#[] : Array Nat) _ = F at hidx ⊢
  rw [List.range_eq_range']
  have hin : ∀ i ∈ F.run.toList, i < t.rows := by
    intro i hi
    rw [hidx, List.mem_filter, List.mem_range'] at hi
    omega
  by_cases hs : F.run.size = t.rows
  · have hall : (List.range' 0 t.rows).filter keep = List.range' 0 t.rows := by
      apply List.Sublist.eq_of_length (List.filter_sublist)
      rw [← hidx, Array.length_toList]; simpa using hs
    rw [TableTheorems.id_bind, if_pos (by simpa using hs)]
    refine ⟨ht, rfl, ?_⟩
    show t.idRows = _
    rw [hall, Table.idRows, List.range_eq_range']
  · have hne : (F.run.size == t.rows) = false := by simpa using hs
    rw [TableTheorems.id_bind, if_neg (by simpa using hs)]
    change (({ t with cols := t.cols.map (gather · F.run), rows := F.run.size } : Table)).WF ∧
      (({ t with cols := t.cols.map (gather · F.run), rows := F.run.size } : Table)).vars = t.vars ∧
      (({ t with cols := t.cols.map (gather · F.run), rows := F.run.size } : Table)).idRows = _
    refine ⟨⟨?_, ?_, ht.nodup⟩, rfl, ?_⟩
    · simp [ht.cols_size]
    · intro c hc
      simp only [Array.size_map] at hc
      simp only [Array.getElem_map]
      have hc' : c < t.vars.size := by rw [← ht.cols_size]; exact hc
      have := (gather_at t ht c hc' F.run hin).1
      rw [getElem!_pos t.cols c hc] at this
      rw [this]; simp
    · rw [← hidx]
      apply List.ext_getElem
      · simp [Table.idRows]
      · intro k h1 h2
        simp only [Table.idRows, List.getElem_map, List.getElem_range] at h1 ⊢
        simp only [List.length_map, Array.length_toList] at h2
        rw [Array.getElem_toList]
        unfold Table.idRow
        apply OptJoin.filterMap_congr' _ _ _
        intro c hc
        rw [List.mem_range] at hc
        have hw : (({ t with cols := t.cols.map (gather · F.run), rows := F.run.size } : Table).at c k) =
            t.at c F.run[k] := by
          show word64 (t.cols.map (gather · F.run))[c]! (8 * k) = _
          have hc' : c < t.cols.size := by rw [ht.cols_size]; exact hc
          rw [getElem!_pos _ c (by simpa using hc'), Array.getElem_map,
            ← getElem!_pos t.cols c hc', TableTheorems.gather_word t ht c hc F.run hin k h2,
            getElem!_pos F.run k h2]
        rw [hw]

/-- A loop in the nested evaluator's monad over a list whose steps leave the
    state as it is and yield. -/
theorem forIn_nm {α β : Type} (f : α → β → NM Id (ForInStep β)) (nst : NSt) :
    ∀ (xs : List α) (P : Nat → β → Prop) (b0 : β), P 0 b0 →
      (∀ k (hk : k < xs.length) b, P k b → ∃ b', (f xs[k] b).run nst = pure (.yield b', nst) ∧ P (k + 1) b') →
      ∃ b', (forIn xs b0 f).run nst = pure (b', nst) ∧ P xs.length b'
  | [], P, b0, h0, _ => ⟨b0, rfl, h0⟩
  | a :: as, P, b0, h0, hs => by
    obtain ⟨b1, h1, hP1⟩ := hs 0 (by simp) b0 h0
    obtain ⟨b', h', hP'⟩ := forIn_nm f nst as (fun k b => P (k + 1) b) b1 hP1
      (fun k hk b hb => hs (k + 1) (by simp; omega) b hb)
    refine ⟨b', ?_, by simpa using hP'⟩
    rw [List.forIn_cons, StateT.run_bind]
    simp only [List.getElem_cons_zero] at h1
    rw [h1, pure_bind]
    exact h'

/-- Two lists related element by element. -/
inductive Fa2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Fa2 R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → Fa2 R l l' → Fa2 R (a :: l) (b :: l')

theorem Fa2.snoc {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β} {a : α} {b : β},
    Fa2 R l l' → R a b → Fa2 R (l ++ [a]) (l' ++ [b])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (Fa2.snoc h2 h)

theorem Fa2.mem_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    Fa2 R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], .nil, b, hb => by cases hb
  | a :: l, b' :: l', .cons h1 h2, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨a', ha', h⟩ := Fa2.mem_right h2 b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h⟩

theorem Fa2.all_eq {α β : Type} {R : α → β → Prop} (f : α → Bool) (g : β → Bool) :
    ∀ {l : List α} {l' : List β}, Fa2 R l l' → (∀ a ∈ l, ∀ b, R a b → g b = f a) → l'.all g = l.all f
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons h1 h2, hfg => by
    simp only [List.all_cons]
    rw [hfg _ List.mem_cons_self _ h1, Fa2.all_eq f g h2 (fun a ha b hr => hfg a (List.mem_cons_of_mem _ ha) b hr)]

theorem forIn_nm' {α β : Type} {f : α → β → NM Id (ForInStep β)} (nst : NSt) {xs : List α} {b0 : β}
    {F : NM Id β} (hF : forIn xs b0 f = F) (P : Nat → β → Prop) (h0 : P 0 b0)
    (hs : ∀ k (hk : k < xs.length) b, P k b → ∃ b', (f xs[k] b).run nst = pure (.yield b', nst) ∧ P (k + 1) b') :
    ∃ b', F.run nst = pure (b', nst) ∧ P xs.length b' := by
  subst hF; exact forIn_nm f nst xs P b0 h0 hs

/-- What the id path's FILTER is proved for: an EXISTS-free condition whose
    conjuncts are each `CjOk`. -/
def FilterOk (c : Expr) : Prop := c.existsFree = true ∧ ∀ cj ∈ (conjuncts c).toList, CjOk cj

theorem forall₂_take_succ {α β : Type} (R : α → β → Prop) (xs : List α) (ys : List β) (k : Nat) (hk : k < xs.length)
    (y : β) (h : Fa2 R (xs.take k) ys) (hr : R xs[k] y) : Fa2 R (xs.take (k + 1)) (ys ++ [y]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some]
  exact Fa2.snoc h hr

/-- **The classification of the conjuncts.** Over a store whose dictionary
    lookup is `cid`, `filterKindsM` returns, without changing the state, one
    kind per conjunct of `c` as `KindOf` says, no semi-join and no `NOT
    EXISTS {}`. -/
theorem filterKindsM_spec (cx : NCx Id) (cid : Term → Option UInt64) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (t : Table) (c : Expr) (hc : FilterOk c) (nst : NSt) :
    ∃ fs, (filterKindsM cx t c).run nst = pure ((fs, #[], false), nst) ∧
      Fa2 (KindOf cx.env cid t) (conjuncts c).toList fs.toList := by
  unfold filterKindsM
  simp only []
  rw [StateT.run_bind, ← Array.forIn_toList]
  generalize hF : forIn (m := NM Id) (conjuncts c).toList ((#[] : Array FKind), (#[] : Array SemiBlock), false) _ = F
  obtain ⟨⟨fs, semis, none_⟩, h, hsem, hnone, hP⟩ := forIn_nm' nst hF
    (fun k (s : Array FKind × Array SemiBlock × Bool) => s.2.1 = #[] ∧ s.2.2 = false ∧
      Fa2 (KindOf cx.env cid t) ((conjuncts c).toList.take k) s.1.toList)
    ⟨rfl, rfl, by simp; exact Fa2.nil⟩ (by
      intro k hk ⟨fs, semis, none_⟩ ⟨hs, hn, hf⟩
      simp only [] at hs hn hf
      subst hs hn
      have hcj := hc.2 _ (List.getElem_mem hk)
      have hstep : ∀ k', KindOf cx.env cid t (conjuncts c).toList[k] k' →
          Fa2 (KindOf cx.env cid t) ((conjuncts c).toList.take (k + 1)) (fs.push k').toList := by
        intro k' hk'
        rw [Array.toList_push]
        exact forall₂_take_succ _ _ _ k hk k' hf hk'
      generalize hcd : (conjuncts c).toList[k] = cj at hcj hstep ⊢
      obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hcj.rv
      have hef := hcj.ef
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
          obtain ⟨k0, hk0, hK⟩ := compile_spec cx.st cid hid cj hcj.nostr vs' hev
          have hl : (liftE (compileFilter cx.st cj) : NM Id FKind).run nst = pure (k0, nst) := by
            unfold liftE; rw [StateT.run_lift, hk0]; rfl
          rw [StateT.run_bind, hl, pure_bind]
          split
          · next v hk0e =>
            rw [StateT.run_bind]
            simp only [StateT.run_get, pure_bind]
            split
            · exact ⟨_, rfl, rfl, rfl, hstep _ (Or.inr ⟨hbl, hcb', hK⟩)⟩
            · exact ⟨_, rfl, rfl, rfl, hstep _ (Or.inl rfl)⟩
          · exact ⟨_, rfl, rfl, rfl, hstep _ (Or.inr ⟨hbl, hcb', hK⟩)⟩
        · exact ⟨_, rfl, rfl, rfl, hstep _ (Or.inl rfl)⟩)
  simp only [] at hsem hnone hP
  subst hsem hnone
  rw [List.take_length] at hP
  exact ⟨fs, by rw [h]; rfl, hP⟩

/-! ## FILTER as `filterM` runs it -/

section filter
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)

/-- The FILTER condition of `QueryPattern.lowerWith` on an EXISTS-free
    condition is the EBV of the condition on the row. -/
theorem filterFn_eq (env : EvalEnv) (c : Expr) (a : Graph) (row : Binding) (hef : c.existsFree = true) :
    IdGroup.filterFn env c a row = ebvOrFalse (Expr.evalIn env row c) := by
  unfold IdGroup.filterFn
  simp only []
  rw [L4Factoidal.Storage.Sbm11.IdPostTheorems.substituteExistentials_existsFree env a _ c hef,
    evalIn_bindEq env _ row (lookup_merge_empty row) c]

/-- The store with the query-local vocabulary decodes the ids in `ok` as the
    store does, when no id in `ok` has the local tag. -/
theorem termOf_local (st : Store Id) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (htermOf : ∀ x, ok x → st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (voc : Array Term) (x : UInt64) (hx : ok x) : (st.withLocal voc).termOf x = pure (dec x) := by
  unfold Store.withLocal
  split
  · exact htermOf x hx
  · show localTermOf st voc x = _
    unfold localTermOf
    rw [if_neg (by simpa using hloc x hx)]
    exact htermOf x hx

/-- **The kept rows.** For conjuncts classified as `KindOf` says, the tests
    `filterKeep` runs are covered (`KWf`) and their conjunction in row `i` is
    the reference FILTER of the condition on the decoded row. -/
theorem keep_all (dec : UInt64 → Term) (ok : UInt64 → Prop) (cid : Term → Option UInt64)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (t : Table) (ht : t.WF) (hrows : ∀ i, i < t.rows → RowIds ok (t.idRow i)) (env : EvalEnv) (c : Expr)
    (hc : FilterOk c) (fs : Array FKind) (hfs : Fa2 (KindOf env cid t) (conjuncts c).toList fs.toList) (a : Graph) :
    (∀ k ∈ fs.toList, KWf t k) ∧
      ∀ i, i < t.rows → fs.toList.all (keepOf dec t i) = IdGroup.filterFn env c a (decRow dec (t.idRow i)) := by
  refine ⟨fun k hk => ?_, fun i hi => ?_⟩
  · obtain ⟨cj, hcj, hK⟩ := hfs.mem_right k hk
    exact (kind_sem dec ok cid hcid hcidN hdec t ht hrows env cj (hc.2 cj hcj) k hK).1
  · rw [filterFn_eq env c a _ hc.1, (conjuncts_spec env _ c).1]
    apply Fa2.all_eq _ _ hfs
    intro cj hcj k hK
    exact (kind_sem dec ok cid hcid hcidN hdec t ht hrows env cj (hc.2 cj hcj) k hK).2 i hi

theorem rows_of (t : Table) (ok : UInt64 → Prop) (hrows : ∀ r ∈ t.idRows, RowIds ok r) :
    ∀ i, i < t.rows → RowIds ok (t.idRow i) := fun i hi =>
  hrows _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

/-- `applyFilters` keeps the rows of `t` whose tests all pass. -/
theorem applyFilters_ok (st : Store Id) (dec : UInt64 → Term) (t : Table) (ht : t.WF)
    (hterm : ∀ i, i < t.rows → ∀ p ∈ t.idRow i, st.termOf p.2 = pure (dec p.2))
    (fs : Array FKind) (hfs : ∀ k ∈ fs.toList, KWf t k) (P : IdRow → Bool)
    (hP : ∀ i, i < t.rows → fs.toList.all (keepOf dec t i) = P (t.idRow i)) :
    ∃ t1 ms', applyFilters st fs (fs.map fun _ => {}) t = pure (t1, ms') ∧ t1.WF ∧
      t1.idRows = t.idRows.filter P := by
  unfold applyFilters
  by_cases hem : (fs.isEmpty || t.rows == 0) = true
  · rw [if_pos hem]
    refine ⟨t, _, rfl, ht, ?_⟩
    symm
    rw [List.filter_eq_self]
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    rw [List.mem_range] at hi
    rw [← hP i hi]
    simp only [Bool.or_eq_true, Array.isEmpty_iff, beq_iff_eq] at hem
    rcases hem with h | h
    · subst h; rfl
    · omega
  · rw [if_neg hem]
    obtain ⟨keep, ms', hk, hsz, hkeep⟩ := filterKeep_spec st dec t ht hterm fs hfs _ (memoOk_empty dec fs)
    rw [hk]
    obtain ⟨hwf, _, hrows⟩ := select_spec t ht fun i => keep[i]!
    refine ⟨_, ms', rfl, hwf, ?_⟩
    rw [hrows, Table.idRows, List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_def]
    rw [hkeep i hi, hP i hi]

/-- **FILTER as `filterM` runs it.** For an EXISTS-free condition whose
    conjuncts are `CjOk`, over a store whose dictionary lookup is `cid` and
    whose `termOf` decodes the ids in `ok` (none with the local tag),
    `filterM` returns, from any state, a well-formed table whose rows are the
    rows of `t` that pass the reference FILTER (`IdGroup.filterFn`), in
    order. -/
theorem filterM_run (cx : NCx Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hid : ∀ t, cx.st.idOf t = pure (cid t)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (env : EvalEnv) (henv : cx.env = env) (g : GCtx) (t : Table) (ht : t.WF)
    (hrows : ∀ r ∈ t.idRows, RowIds ok r) (c : Expr) (hc : FilterOk c) (a : Graph) (nst : NSt) :
    ∃ t' nst', (filterM cx g t c).run nst = pure (t', nst') ∧ t'.WF ∧
      t'.idRows = t.idRows.filter (fun r => IdGroup.filterFn env c a (decRow dec r)) := by
  obtain ⟨fs, hk, hfs⟩ := filterKindsM_spec cx cid hid t c hc nst
  rw [henv] at hfs
  have hrows' := rows_of t ok hrows
  obtain ⟨hkw, hkeep⟩ := keep_all dec ok cid hcid hcidN hdec t ht hrows' env c hc fs hfs a
  unfold filterM
  rw [StateT.run_bind, hk, pure_bind]
  simp only [Bool.false_eq_true, if_false]
  rw [StateT.run_bind]
  have hls : (IdGroup.localStore cx).run nst = pure (cx.st.withLocal nst.vocab, nst) := rfl
  rw [hls, pure_bind, StateT.run_bind]
  have hterm : ∀ i, i < t.rows → ∀ p ∈ t.idRow i, (cx.st.withLocal nst.vocab).termOf p.2 = pure (dec p.2) :=
    fun i hi p hp => termOf_local cx.st dec ok htermOf hloc nst.vocab p.2 (hrows' i hi p hp)
  obtain ⟨t1, ms', ha, hwf, hrw⟩ := applyFilters_ok (cx.st.withLocal nst.vocab) dec t ht hterm fs hkw
    (fun r => IdGroup.filterFn env c a (decRow dec r)) (fun i hi => hkeep i hi)
  have hl : (liftE (applyFilters (cx.st.withLocal nst.vocab) fs (fs.map fun _ => {}) t) : NM Id _).run nst =
      pure ((t1, ms'), nst) := by
    unfold liftE; rw [StateT.run_lift, ha]; rfl
  rw [hl, pure_bind]
  exact ⟨t1, _, rfl, hwf, hrw⟩

end filter

/-! ## OPTIONAL with a condition as `leftJoinCondM` runs it -/

section lj
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)
open L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems (ljTable)

/-- **The run of `leftJoinCondM` with a condition other than `true`.** For
    an EXISTS-free condition whose conjuncts are `CjOk`, `leftJoinCondM`
    evaluates the condition on the merged rows of the compatible pairs as a
    mask (`filterKeep`): entry `k` is the reference FILTER of the condition on
    merged row `k`. -/
theorem leftJoinCond_run (cx : NCx Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hid : ∀ t, cx.st.idOf t = pure (cid t)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (env : EvalEnv) (henv : cx.env = env) (g : GCtx) (l r : Table)
    (hm : (IdJoin.joinIds l r).WF) (hrows : ∀ q ∈ (IdJoin.joinIds l r).idRows, RowIds ok q)
    (c : Expr) (hc : FilterOk c) (htriv : c ≠ .boolLit true) (a : Graph) (nst : NSt) :
    ∃ keep nst', (leftJoinCondM cx g l r c).run nst =
      pure (ljTable (IdJoin.joinIds l r) l (IdGroup.ljSource l.rows
        (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1 keep), nst') ∧
      keep.size = (IdJoin.joinIds l r).rows ∧
      ∀ k, k < (IdJoin.joinIds l r).rows →
        keep[k]! = IdGroup.filterFn env c a (decRow dec ((IdJoin.joinIds l r).idRow k)) := by
  have hmj : IdJoin.joinIds l r = IdJoin.pairsTable l r (L4Factoidal.Qlvr.sharedCols l r)
      (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1
      (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).2 := rfl
  generalize hM : IdJoin.joinIds l r = M at hm hrows ⊢
  obtain ⟨fs, hk, hfs⟩ := filterKindsM_spec cx cid hid M c hc nst
  rw [henv] at hfs
  have hrows' := rows_of M ok hrows
  obtain ⟨hkw, hkeep⟩ := keep_all dec ok cid hcid hcidN hdec M hm hrows' env c hc fs hfs a
  have hterm : ∀ i, i < M.rows → ∀ p ∈ M.idRow i, (cx.st.withLocal nst.vocab).termOf p.2 = pure (dec p.2) :=
    fun i hi p hp => termOf_local cx.st dec ok htermOf hloc nst.vocab p.2 (hrows' i hi p hp)
  obtain ⟨keep, ms', hfk, hsz, hkk⟩ := filterKeep_spec (cx.st.withLocal nst.vocab) dec M hm hterm fs hkw _
    (memoOk_empty dec fs)
  have hrun : ∃ nst', (leftJoinCondM cx g l r c).run nst =
      pure (ljTable M l (IdGroup.ljSource l.rows
        (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1 keep), nst') := by
    unfold leftJoinCondM
    simp only []
    rw [hmj] at hM
    rcases hjp : IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r) with ⟨li, ri⟩
    rw [hjp] at hM
    simp only [] at hM ⊢
    rw [hM]
    revert htriv hc hk hfs hkeep
    cases c
    case boolLit b =>
      cases b
      · intro hc _ hk hfs hkeep
        simp only [Bool.false_eq_true, if_false]
        rw [StateT.run_bind, hk, pure_bind]
        simp only [Array.isEmpty_empty, Bool.not_false, Bool.and_self, if_true]
        rw [StateT.run_bind]
        have hls : (IdGroup.localStore cx).run nst = pure (cx.st.withLocal nst.vocab, nst) := rfl
        rw [hls, pure_bind, StateT.run_bind]
        have hl : (liftE (filterKeep (cx.st.withLocal nst.vocab) fs (fs.map fun _ => {}) M) : NM Id _).run nst =
            pure ((keep, ms'), nst) := by
          unfold liftE; rw [StateT.run_lift, hfk]; rfl
        rw [hl, pure_bind]
        exact ⟨_, rfl⟩
      · intro _ h _ _ _; exact absurd rfl h
    all_goals intro hc _ hk hfs hkeep
    all_goals simp only [Bool.false_eq_true, if_false]
    all_goals
      rw [StateT.run_bind, hk, pure_bind]
      simp only [Array.isEmpty_empty, Bool.not_false, Bool.and_self, if_true]
      rw [StateT.run_bind]
      have hls : (IdGroup.localStore cx).run nst = pure (cx.st.withLocal nst.vocab, nst) := rfl
      rw [hls, pure_bind, StateT.run_bind]
      have hl : (liftE (filterKeep (cx.st.withLocal nst.vocab) fs (fs.map fun _ => {}) M) : NM Id _).run nst =
          pure ((keep, ms'), nst) := by
        unfold liftE; rw [StateT.run_lift, hfk]; rfl
      rw [hl, pure_bind]
      exact ⟨_, rfl⟩
  obtain ⟨nst', hr⟩ := hrun
  exact ⟨keep, nst', hr, hsz, fun k hk' => by rw [hkk k hk', hkeep k hk']⟩

end lj

/-! ## `ljSource` with a mask -/

section src
open L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems (off off_succ off_mono rep_get rep_next length_flatMap_range)
open L4Factoidal.Storage.Sbm11.TableTheorems (forIn_inv' id_bind)

/-- The entries of LeftJoin for left row `i` with a mask: the pairs of `i`
    that passed, else the left row alone. -/
def ljBlockA (cnt : Nat → Nat) (alive : Array Bool) (i : Nat) : List (Option Nat × Nat) :=
  let ks := (List.range' (off (fun i => List.replicate (cnt i) i) i) (cnt i)).filter fun k => alive[k]!
  if ks.isEmpty then [(none, i)] else ks.map fun k => (some k, i)

theorem ljSource_spec' (nl : Nat) (cnt : Nat → Nat) (li : Array Nat) (alive : Array Bool)
    (hli : li.toList = (List.range nl).flatMap fun i => List.replicate (cnt i) i) :
    (IdGroup.ljSource nl li alive).toList = (List.range nl).flatMap (ljBlockA cnt alive) := by
  let B : Nat → List Nat := fun i => List.replicate (cnt i) i
  have hsz : li.size = off B nl := by
    rw [← Array.length_toList, hli]; exact length_flatMap_range B nl
  unfold IdGroup.ljSource
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 nl) ((Array.mkEmpty (nl + li.size) : Array (Option Nat × Nat)), 0) _ = F
  have := L4Factoidal.Storage.Sbm11.TableTheorems.forIn_range_inv nl (fun m (s : Array (Option Nat × Nat) × Nat) =>
      s.2 = off B m ∧ s.1.toList = (List.range m).flatMap (ljBlockA cnt alive)) hF ⟨rfl, by simp⟩ (by
    intro m s hm ⟨h1, h2⟩
    have hle : off B m + cnt m ≤ li.size := by
      rw [hsz]; have := off_mono B (show m + 1 ≤ nl by omega); rw [off_succ] at this; simpa [B] using this
    rw [id_bind]
    generalize hI : forIn (m := _root_.Id) (List.range' 0 li.size) (s.1, s.2, false) _ = I
    let A : Nat → List Nat := fun a => (List.range' (off B m) a).filter fun k => alive[k]!
    have hinv := forIn_inv' (fun a (st : Array (Option Nat × Nat) × Nat × Bool) => a ≤ cnt m ∧ st.2.1 = off B m + a ∧
        st.1.toList = s.1.toList ++ (A a).map (fun k => (some k, m)) ∧ st.2.2 = !(A a).isEmpty)
      (fun st => st.2.1 = off B m + cnt m ∧
        st.1.toList = s.1.toList ++ (A (cnt m)).map (fun k => (some k, m)) ∧
        st.2.2 = !(A (cnt m)).isEmpty) hI ⟨Nat.zero_le _, by simp [h1], by simp [A], by simp [A]⟩
      (by
        intro a st _ _ ⟨ha1, ha2, ha3, ha4⟩
        have hA : A (a + 1) = A a ++ (if alive[off B m + a]! then [off B m + a] else []) := by
          simp only [A]
          rw [List.range'_concat, List.filter_append]
          by_cases hal : alive[off B m + a]! = true <;> simp [hal]
        constructor
        · intro st' hst
          by_cases hc : (decide (st.2.1 < li.size) && li[st.2.1]! == m) = true
          · have hlt : a < cnt m := by
              apply Classical.byContradiction
              intro hn
              have hae : a = cnt m := by omega
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
              rw [ha2, hae] at hc
              exact rep_next cnt nl m hm li hli hc.1 hc.2
            by_cases hal : alive[st.2.1]! = true
            · simp only [hc, hal, if_true] at hst
              cases hst
              refine ⟨by omega, by simp [ha2]; omega, ?_, ?_⟩
              · rw [hA, ← ha2, if_pos hal]
                simp [ha3]
              · rw [hA, ← ha2, if_pos hal]; simp
            · simp only [hc, hal, if_true, Bool.false_eq_true, if_false] at hst
              cases hst
              refine ⟨by omega, by simp [ha2]; omega, ?_, ?_⟩
              · rw [hA, ← ha2, if_neg hal]; simpa using ha3
              · rw [hA, ← ha2, if_neg hal]; simpa using ha4
          · simp only [hc, Bool.false_eq_true, if_false] at hst
            cases hst
        · intro st' hst
          by_cases hc : (decide (st.2.1 < li.size) && li[st.2.1]! == m) = true
          · by_cases hal : alive[st.2.1]! = true
            · simp only [hc, hal, if_true] at hst
              cases hst
            · simp only [hc, hal, if_true, Bool.false_eq_true, if_false] at hst
              cases hst
          · simp only [hc, Bool.false_eq_true, if_false] at hst
            cases hst
            have hae : a = cnt m := by
              apply Classical.byContradiction
              intro hn
              have hlt : a < cnt m := by omega
              obtain ⟨hs, hg⟩ := rep_get cnt nl m a hm hlt li hli
              apply hc
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
              rw [ha2]
              exact ⟨hs, hg⟩
            subst hae
            exact ⟨ha2, ha3, ha4⟩)
    have hQ : I.run.2.1 = off B m + cnt m ∧
        I.run.1.toList = s.1.toList ++ (A (cnt m)).map (fun k => (some k, m)) ∧
        I.run.2.2 = !(A (cnt m)).isEmpty := by
      rcases hinv with ⟨ha1, ha2, ha3, ha4⟩ | hq
      · have hae : li.size = cnt m := by simp at ha1; omega
        simp only [Nat.zero_add] at ha1 ha2 ha3 ha4
        rw [hae] at ha2 ha3 ha4
        exact ⟨ha2, ha3, ha4⟩
      · exact hq
    obtain ⟨q1, q2, q3⟩ := hQ
    by_cases h0 : (A (cnt m)).isEmpty = true
    · refine ⟨(I.run.1.push (none, m), I.run.2.1), by simp [q3, h0], ?_, ?_⟩
      · simp only [q1, off_succ, B, List.length_replicate]
      · rw [Array.toList_push, q2, h2, List.range_succ, List.flatMap_append, List.flatMap_singleton]
        have he : A (cnt m) = [] := List.isEmpty_iff.mp h0
        simp only [he, List.map_nil, List.append_nil, ljBlockA]
        rw [if_pos (by simpa [A, B] using he)]
    · refine ⟨(I.run.1, I.run.2.1), by simp [q3, h0], ?_, ?_⟩
      · simp only [q1, off_succ, B, List.length_replicate]
      · rw [q2, h2, List.range_succ, List.flatMap_append, List.flatMap_singleton]
        simp only [ljBlockA]
        rw [if_neg (by simpa [A, B] using h0)])
  exact this.2

end src

/-! ## The rows of OPTIONAL with a condition -/

section ljrows
open L4Factoidal.Storage.Sbm11.IdGroup (Pw idLeftJoinC)
open L4Factoidal.Storage.Sbm11.OptJoin (innerSpec idCompatible idMerge)
open L4Factoidal.Storage.Sbm11.TableTheorems (joinPairs_spec innerSpec_eq idJoin_rows innerSpec_congr compatAt_iff
  joinIds_rows pairsTable_eq joinVars_vars)
open L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems (off ljTable ljRow ljTable_rows pw_flatMap_same filterMap_ite
  off_congr flatMap_get)

theorem pw_map_same {γ : Type} {R : IdRow → IdRow → Prop} (f g : γ → IdRow) :
    ∀ (L : List γ), (∀ t ∈ L, R (f t) (g t)) → Pw R (L.map f) (L.map g)
  | [], _ => .nil
  | t :: L, h => .cons (h t List.mem_cons_self) (pw_map_same f g L fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem list_eq_map_range (S : List Nat) : S = (List.range S.length).map fun t => S[t]! := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, getElem!_pos S n h1]

/-- **OPTIONAL with a condition on id tables.** For two well-formed tables
    and a mask whose entry `k` is `cond` of merged row `k`, with `cond` the
    same on rows with the same lookups, the table of `leftJoinCondM` is
    well formed and its rows are, row for row, the same solution mappings as
    `idLeftJoinC cond` of the rows of the two tables. -/
theorem leftJoinCond_rows (l r : Table) (hl : l.WF) (hr : r.WF) (keep : Array Bool) (cond : IdRow → Bool)
    (hkeep : ∀ k, k < (IdJoin.joinIds l r).rows → keep[k]! = cond ((IdJoin.joinIds l r).idRow k))
    (hcond : ∀ r1 r2, RowEq r1 r2 → cond r1 = cond r2) :
    let t := ljTable (IdJoin.joinIds l r) l (IdGroup.ljSource l.rows
        (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1 keep)
    t.WF ∧ Pw RowEq t.idRows (idLeftJoinC cond l.idRows r.idRows) := by
  intro t
  let shared := L4Factoidal.Qlvr.sharedCols l r
  let cmp := IdJoin.compatAt l r shared
  let Sj : Nat → List Nat := fun i => (List.range' 0 r.rows).filter (cmp i)
  let cnt : Nat → Nat := fun i => (Sj i).length
  let BP : Nat → List (Nat × Nat) := fun i => (Sj i).map fun j => (i, j)
  let P := innerSpec l.rows r.rows cmp
  have hP : P = (List.range l.rows).flatMap BP := by
    show innerSpec l.rows r.rows cmp = _
    rw [innerSpec_eq, List.range_eq_range']
  let li := (IdJoin.joinPairs l r shared).1
  have hli : li.toList = (List.range l.rows).flatMap fun i => List.replicate (cnt i) i := by
    rw [(joinPairs_spec l r shared).1]
    show P.map Prod.fst = _
    rw [hP, List.map_flatMap]
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro i _
    simp only [BP, cnt, List.map_map, Function.comp_def]
    exact List.map_const'
  have hsrc := ljSource_spec' l.rows cnt li keep hli
  let merged := IdJoin.joinIds l r
  obtain ⟨hmwf, hmr⟩ := joinIds_rows l r hl hr
  have hjoin : IdJoin.idJoin l.idRows r.idRows = P.map fun p => idMerge (l.idRow p.1) (r.idRow p.2) := by
    rw [idJoin_rows]
    congr 1
    apply innerSpec_congr
    intro i j _ _
    exact (compatAt_iff l r hr.nodup i j).symm
  rw [hjoin] at hmr
  have hmrow : ∀ k (hk : k < P.length), RowEq (merged.idRow k) (idMerge (l.idRow P[k].1) (r.idRow P[k].2)) := by
    intro k hk
    have hk1 : k < merged.idRows.length := by rw [hmr.1]; simpa using hk
    have := hmr.2 k hk1 (by simpa using hk)
    simp only [Table.idRows, List.getElem_map, List.getElem_range] at this
    exact this
  have hmrows : merged.rows = P.length := by
    have := hmr.1
    simp only [Table.idRows, List.length_map, List.length_range] at this
    exact this
  obtain ⟨cols, sv, hT, _, _, _⟩ := pairsTable_eq l r hl shared li (IdJoin.joinPairs l r shared).2 (by
    intro i hi
    rw [hli, List.mem_flatMap] at hi
    obtain ⟨i', hi', hm⟩ := hi
    rw [(List.mem_replicate.mp hm).2]; simpa using hi')
  have hmv : merged.vars.toList =
      l.vars.toList ++ (L4Factoidal.Qlvr.joinVars l r).2.toList.map (fun q => r.vars[q]!) := by
    show (IdJoin.pairsTable l r shared li (IdJoin.joinPairs l r shared).2).vars.toList = _
    rw [hT]
    exact joinVars_vars l r
  have hpre : l.vars.size ≤ merged.vars.size := by
    rw [← Array.length_toList, ← Array.length_toList, hmv, List.length_append]; omega
  have hv : ∀ c, c < l.vars.size → merged.vars[c]! = l.vars[c]! := by
    intro c hc
    rw [getElem!_pos _ c (by omega), getElem!_pos _ c hc, ← Array.getElem_toList, ← Array.getElem_toList]
    simp only [hmv]
    rw [List.getElem_append_left]
  obtain ⟨htwf, hrows⟩ := ljTable_rows merged l hmwf _ hpre hv
  refine ⟨htwf, ?_⟩
  show Pw RowEq (ljTable merged l _).idRows _
  rw [hrows, hsrc, List.map_flatMap]
  -- the specification, per left row
  let M : Nat → Nat → IdRow := fun i j => idMerge (l.idRow i) (r.idRow j)
  have hspec : idLeftJoinC cond l.idRows r.idRows = (List.range l.rows).flatMap fun i =>
      if ((Sj i).filter fun j => cond (M i j)).isEmpty then [l.idRow i]
      else ((Sj i).filter fun j => cond (M i j)).map (M i) := by
    unfold idLeftJoinC Table.idRows
    rw [List.flatMap_map]
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro i _
    have he : ((List.range r.rows).map r.idRow).filterMap (fun r2 =>
          if idCompatible (l.idRow i) r2 = true then
            (if cond (idMerge (l.idRow i) r2) = true then some (idMerge (l.idRow i) r2) else none) else none) =
        ((Sj i).filter fun j => cond (M i j)).map (M i) := by
      rw [List.filterMap_map]
      simp only [Function.comp_def]
      have hc : ∀ j, (if idCompatible (l.idRow i) (r.idRow j) = true then
            (if cond (idMerge (l.idRow i) (r.idRow j)) = true then some (idMerge (l.idRow i) (r.idRow j)) else none)
            else none) =
          (if (idCompatible (l.idRow i) (r.idRow j) && cond (M i j)) = true then some (M i j) else none) := by
        intro j
        cases idCompatible (l.idRow i) (r.idRow j) <;> cases cond (M i j) <;> rfl
      simp only [hc]
      rw [filterMap_ite (fun j => idCompatible (l.idRow i) (r.idRow j) && cond (M i j)) (M i),
        List.range_eq_range', List.filter_filter]
      congr 1
      apply List.filter_congr
      intro j _
      simp only [cmp, shared]
      rw [compatAt_iff l r hr.nodup i j, Bool.and_comm]
    rw [he]
    simp only [List.isEmpty_map]
  rw [hspec]
  apply pw_flatMap_same
  intro i hi
  rw [List.mem_range] at hi
  let o := off (fun i => List.replicate (cnt i) i) i
  let S := Sj i
  have hoff : o = off BP i := off_congr _ _ (fun i => by simp [BP, cnt]) i
  -- merged row `o + t` is the pair `(i, S[t])`
  have hpair : ∀ t (ht : t < S.length), o + t < merged.rows ∧
      RowEq (merged.idRow (o + t)) (M i S[t]) := by
    intro t ht
    have ht' : t < (BP i).length := by simpa [BP] using ht
    obtain ⟨hk, e⟩ := flatMap_get BP l.rows i t hi ht'
    have hk' : off BP i + t < P.length := by rw [hP]; exact hk
    have := hmrow (off BP i + t) hk'
    have eP : P[off BP i + t] = (i, S[t]) := by
      simp only [hP]; rw [e]; simp [BP, S]
    rw [eP] at this
    refine ⟨by rw [hmrows, hoff]; exact hk', by rw [hoff]; exact this⟩
  have hkp : ∀ t (ht : t < S.length), keep[o + t]! = cond (M i S[t]) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hpair t ht
    rw [hkeep _ h1]
    exact hcond _ _ h2
  let T := (List.range S.length).filter fun t => keep[o + t]!
  have hks : (List.range' o (cnt i)).filter (fun k => keep[k]!) = T.map (o + ·) := by
    rw [List.range'_eq_map_range, List.filter_map]
    rfl
  have hF : S.filter (fun j => cond (M i j)) = T.map fun t => S[t]! := by
    conv => lhs; rw [list_eq_map_range S]
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro t ht
    rw [List.mem_range] at ht
    simp only [Function.comp_def, getElem!_pos S t ht]
    exact (hkp t ht).symm
  simp only [ljBlockA]
  show Pw RowEq (List.map (ljRow merged l) (if ((List.range' o (cnt i)).filter fun k => keep[k]!).isEmpty = true
      then [(none, i)] else ((List.range' o (cnt i)).filter fun k => keep[k]!).map fun k => (some k, i)))
    (if (S.filter fun j => cond (M i j)).isEmpty = true then [l.idRow i]
      else (S.filter fun j => cond (M i j)).map (M i))
  rw [hks, hF]
  simp only [List.isEmpty_map]
  split
  · exact .cons (RowEq.refl _) .nil
  · simp only [List.map_map]
    apply pw_map_same
    intro t ht
    have htl : t < S.length := List.mem_range.mp (List.mem_filter.mp ht).1
    show RowEq (merged.idRow (o + t)) (M i S[t]!)
    rw [getElem!_pos S t htl]
    exact (hpair t htl).2

end ljrows

end L4Factoidal.Storage.Sbm11.FilterTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.FilterTableTheorems.select_spec
#print axioms L4Factoidal.Storage.Sbm11.FilterTableTheorems.filterKindsM_spec
#print axioms L4Factoidal.Storage.Sbm11.FilterTableTheorems.filterM_run
#print axioms L4Factoidal.Storage.Sbm11.FilterTableTheorems.leftJoinCond_run
#print axioms L4Factoidal.Storage.Sbm11.FilterTableTheorems.ljSource_spec'
#print axioms L4Factoidal.Storage.Sbm11.FilterTableTheorems.leftJoinCond_rows
