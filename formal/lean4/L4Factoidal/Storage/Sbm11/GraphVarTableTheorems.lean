/-
L4Factoidal.Storage.Sbm11.GraphVarTableTheorems — GRAPH with a variable as the
nested evaluator runs it, per named graph (https://github.com/danbri/factoidal/issues/776;
lemma L4t of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `bindGraph_rows`: `IdGroup.bindGraph t v x` (bind `?v` to the graph id `x`
  in each row, `Binding.bindIfCompatible` on ids) is a well-formed table whose
  rows are, row for row, the same solution mappings as
  `IdGroup.idBindG v x` of the rows of `t`.
* `forIn_nm_ends`: a loop of the nested evaluator whose every step refuses
  with a `LocalVocab.LocalRefusal` or yields keeps an invariant.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.LocalTableTheorems
import L4Factoidal.Storage.Sbm11.FilterTableTheorems

namespace L4Factoidal.Storage.Sbm11.GraphVar

open L4Factoidal.RDF
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (ColHolds RowEq)
open L4Factoidal.Storage.Sbm11.LocalVocab
open L4Factoidal.Storage.Sbm11.LocalTable (pw_of_get ext_table extTable)
open L4Factoidal.Storage.Sbm11.IdGroup (NSt NM idBindG bindGraph)

theorem const_loop (n : Nat) (x : UInt64) {F : _root_.Id ByteArray}
    (hF : forIn (List.range' 0 n) (ByteArray.emptyWithCapacity (8 * n))
      (fun _ (s : ByteArray) => pure (.yield (L4Factoidal.Qlvr.Side.put64 s x))) = F) :
    ColHolds F.run (List.replicate n x) := by
  have := TableTheorems.put64_loop (fun _ => x) n hF
  rwa [List.map_const', List.length_range] at this

/-- Two tables with the same variables, columns and row count. -/
theorem tab_congr {T1 T2 : Table} (h1 : T1.vars = T2.vars) (h2 : T1.cols = T2.cols) (h3 : T1.rows = T2.rows) :
    (T1.WF → T2.WF) ∧ T1.idRows = T2.idRows ∧ ∀ j w, T1.lookupAt j w = T2.lookupAt j w := by
  obtain ⟨v1, c1, r1, s1⟩ := T1
  obtain ⟨v2, c2, r2, s2⟩ := T2
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, rfl, fun _ _ => rfl⟩

/-- `filter` then `map` against `filterMap`, related element by element. -/
theorem pw_filter_filterMap {R : IdRow → IdRow → Prop} (p : Nat → Bool) (g : Nat → IdRow)
    (h : Nat → Option IdRow) :
    ∀ (L : List Nat), (∀ i ∈ L, (p i = true → ∃ y, h i = some y ∧ R (g i) y) ∧ (p i = false → h i = none)) →
      IdGroup.Pw R ((L.filter p).map g) (L.filterMap h)
  | [], _ => .nil
  | i :: L, hL => by
    have ih := pw_filter_filterMap p g h L fun j hj => hL j (List.mem_cons_of_mem _ hj)
    obtain ⟨h1, h2⟩ := hL i List.mem_cons_self
    cases hp : p i with
    | true =>
      obtain ⟨y, hy, hr⟩ := h1 hp
      simp only [List.filter_cons, hp, if_true, List.map_cons, List.filterMap_cons, hy]
      exact .cons hr ih
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, if_false, List.filterMap_cons, h2 hp]
      exact ih

/-- **`bindGraph` on a table.** -/
theorem bindGraph_rows (t : Table) (ht : t.WF) (v : String) (x : UInt64) (hx : x ≠ unbound) :
    (bindGraph t v x).WF ∧ IdGroup.Pw RowEq (bindGraph t v x).idRows (t.idRows.filterMap (idBindG v x)) := by
  have hlk : ∀ i, idLookup v (t.idRow i) = t.lookupAt i v := fun i => TableTheorems.lookup_idRow t ht.nodup i v
  unfold bindGraph
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, bind_pure]
  cases hv : t.idx v with
  | none =>
    simp only []
    generalize hF : forIn (m := _root_.Id) (List.range' 0 t.rows) (ByteArray.emptyWithCapacity (8 * t.rows)) _ = F
    have hcol := const_loop t.rows x hF
    obtain ⟨hwf0, _, hl0⟩ := ext_table t ht v F.run (List.replicate t.rows x) hcol (by simp)
    simp only [extTable, hv] at hwf0 hl0
    obtain ⟨hc1, hc2, hc3⟩ := tab_congr (T1 := { t with vars := t.vars.push v, cols := t.cols.push F.run })
      (T2 := { vars := t.vars.push v, cols := t.cols.push F.run, rows := t.rows }) rfl rfl rfl
    have hwf := hc1 hwf0
    have hl : ∀ j, j < t.rows → ∀ w, ({ vars := t.vars.push v, cols := t.cols.push F.run, rows := t.rows } : Table).lookupAt j w =
        if w = v then (if (List.replicate t.rows x)[j]! = unbound then none else some (List.replicate t.rows x)[j]!)
        else t.lookupAt j w := fun j hj w => by rw [← hc3]; exact hl0 j hj w
    refine ⟨hwf, ?_⟩
    have hrows : t.idRows.filterMap (idBindG v x) = (List.range t.rows).map fun i => (v, x) :: t.idRow i := by
      unfold Table.idRows
      rw [List.filterMap_map, ← List.filterMap_eq_map]
      congr 1
      funext i
      simp only [Function.comp_def, idBindG, hlk i]
      unfold Table.lookupAt
      rw [hv]
    rw [hrows]
    apply pw_of_get
    · simp [Table.idRows]
    · intro j h1 h2
      have hj : j < t.rows := by simpa [Table.idRows] using h1
      simp only [Table.idRows, List.getElem_map, List.getElem_range]
      intro w
      rw [TableTheorems.lookup_idRow _ hwf.nodup j w]
      rw [hl j hj w]
      simp only [idLookup]
      by_cases hw : w = v
      · subst hw
        rw [if_pos rfl, if_pos rfl, getElem!_pos _ j (by simpa using hj), List.getElem_replicate, if_neg hx]
      · rw [if_neg hw, if_neg (Ne.symm hw), TableTheorems.lookup_idRow t ht.nodup j w]
  | some c =>
    simp only []
    obtain ⟨hwf', hv', hrows'⟩ := FilterTableTheorems.select_spec t ht
      (fun i => t.at c i == x || t.at c i == unbound)
    generalize hS : t.select (fun i => t.at c i == x || t.at c i == unbound) = t' at hwf' hv' hrows' ⊢
    generalize hF : forIn (m := _root_.Id) (List.range' 0 t'.rows) (ByteArray.emptyWithCapacity (8 * t'.rows)) _ = F
    have hcol := const_loop t'.rows x hF
    have hv'' : t'.idx v = some c := by
      show t'.vars.findIdx? (· == v) = _
      rw [hv']; exact hv
    obtain ⟨hwf, _, hl⟩ := ext_table t' hwf' v F.run (List.replicate t'.rows x) hcol (by simp)
    simp only [extTable, hv''] at hwf hl
    refine ⟨hwf, ?_⟩
    generalize hSd : (List.range t.rows).filter (fun i => t.at c i == x || t.at c i == unbound) = S at hrows'
    have hlen : t'.rows = S.length := by
      have := congrArg List.length hrows'
      simpa [Table.idRows] using this
    have hget : ∀ k (hk : k < t'.rows), t'.idRow k = t.idRow S[k] := by
      intro k hk
      have := congrArg (fun l : List IdRow => l[k]?) hrows'
      simp only [Table.idRows, List.getElem?_map, List.getElem?_range hk] at this
      rw [List.getElem?_eq_getElem (by omega)] at this
      simpa using this
    refine IdGroup.Pw.trans (R := RowEq) (fun _ _ _ h1 h2 => TableTheorems.RowEq.trans h1 h2)
      (l' := S.map fun i => (v, x) :: t.idRow i) ?_ ?_
    · apply pw_of_get
      · simp [Table.idRows, hlen]
      · intro k h1 h2
        have hk : k < t'.rows := by simpa [Table.idRows] using h1
        simp only [Table.idRows, List.getElem_map, List.getElem_range]
        intro w
        rw [TableTheorems.lookup_idRow _ hwf.nodup k w, hl k hk w]
        simp only [idLookup]
        by_cases hw : w = v
        · subst hw
          rw [if_pos rfl, if_pos rfl, getElem!_pos _ k (by simpa using hk), List.getElem_replicate, if_neg hx]
        · rw [if_neg hw, if_neg (Ne.symm hw), ← TableTheorems.lookup_idRow t' hwf'.nodup k w, hget k hk]
    · unfold Table.idRows
      rw [List.filterMap_map, ← hSd]
      apply pw_filter_filterMap
      intro i hi
      have hli : idLookup v (t.idRow i) = if t.at c i == unbound then none else some (t.at c i) := by
        rw [hlk i]; unfold Table.lookupAt; rw [hv]
      constructor
      · intro hk
        simp only [Bool.or_eq_true, beq_iff_eq] at hk
        rcases hk with hk | hk
        · refine ⟨t.idRow i, ?_, ?_⟩
          · simp only [Function.comp_def, idBindG, hli, hk, beq_iff_eq, hx, if_false, beq_self_eq_true, if_true]
          · intro w
            simp only [idLookup]
            by_cases hw : v = w
            · subst hw; rw [if_pos rfl, hli, hk]; simp [hx]
            · rw [if_neg hw]
        · refine ⟨(v, x) :: t.idRow i, ?_, TableTheorems.RowEq.refl _⟩
          simp only [Function.comp_def, idBindG, hli, hk, beq_self_eq_true, if_true]
      · intro hk
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hk
        simp only [Function.comp_def, idBindG, hli]
        rw [if_neg (by simpa using hk.2)]
        simp only [beq_eq_false_iff_ne.mpr hk.1, Bool.false_eq_true, if_false]

/-! ## Loops of the nested evaluator -/

theorem forIn_nm_ends {α β : Type} (f : α → β → NM Id (ForInStep β)) :
    ∀ (xs : List α) (P : Nat → β → NSt → Prop) (b0 : β) (s0 : NSt), P 0 b0 s0 →
      (∀ k (hk : k < xs.length) b s, P k b s →
        Ends ((f xs[k] b).run s) fun r s' => ∃ b', r = .yield b' ∧ P (k + 1) b' s') →
      Ends ((forIn xs b0 f).run s0) fun b s => P xs.length b s
  | [], _, b0, s0, h0, _ => Or.inr ⟨b0, s0, rfl, h0⟩
  | a :: as, P, b0, s0, h0, hs => by
    rw [List.forIn_cons, StateT.run_bind]
    rcases hs 0 (by simp) b0 s0 h0 with ⟨e, he, hr⟩ | ⟨r, s1, he, b1, rfl, hP1⟩
    · left
      simp only [List.getElem_cons_zero] at he
      exact ⟨e, by rw [he]; rfl, hr⟩
    · simp only [List.getElem_cons_zero] at he
      rw [he, pure_bind]
      simp only []
      have := forIn_nm_ends f as (fun k b s => P (k + 1) b s) b1 s1 hP1
        (fun k hk b s hb => by
          have := hs (k + 1) (by simp; omega) b s hb
          simpa using this)
      simpa using this

/-- A list as the indices of its elements. -/
theorem flatMap_range {α β : Type} (G : α → List β) :
    ∀ (L : List α), L.flatMap G = (List.range L.length).flatMap fun j => match L[j]? with
      | some a => G a
      | none => []
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, flatMap_range G L, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

theorem fa2_get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, FilterTableTheorems.Fa2 R l l' →
      l.length = l'.length ∧ ∀ (j : Nat) a b, l[j]? = some a → l'[j]? = some b → R a b
  | [], [], .nil => ⟨rfl, fun j a b h => by simp at h⟩
  | a :: l, b :: l', .cons h1 h2 => by
    obtain ⟨hl, hr⟩ := fa2_get h2
    refine ⟨by simp [hl], fun j x y hx hy => ?_⟩
    cases j with
    | zero => simp at hx hy; subst hx hy; exact h1
    | succ j => simp at hx hy; exact hr j x y hx hy

end L4Factoidal.Storage.Sbm11.GraphVar

#print axioms L4Factoidal.Storage.Sbm11.GraphVar.bindGraph_rows
#print axioms L4Factoidal.Storage.Sbm11.GraphVar.forIn_nm_ends
