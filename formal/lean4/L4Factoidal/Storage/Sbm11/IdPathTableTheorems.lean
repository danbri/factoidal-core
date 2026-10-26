/-
L4Factoidal.Storage.Sbm11.IdPathTableTheorems — the table of a property path
pattern on ids (`IdQuery.pathTableM`) against the model's rows
(`IdPath.idPathRows` after `idConstRefl` of `idEvalPath`)
(https://github.com/danbri/factoidal/issues/776; part of lemma L4n of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `pathRowsTable_rows`: the table `pathRowsTable` builds from pairs has, row
  for row (`Pw RowEq`), the rows `idPathRow` gives for the pairs, for
  endpoints that are variables or constants and pair ids that are not 0.
* `pathPairs_rows`: the reflexive pairs `pathPairsOf` appends from the
  restricted relation give the rows `idConstRefl` gives from the whole
  relation, up to order: a pair outside the restriction gives no row.
* `pathTableM_rows`: `pathTableM` over a store of `BgpStore`, with no rows
  joined before (`unitTable`, the leaf of the nested evaluator), answers a
  well-formed table whose rows are `IdEquiv` to the model's rows of the path
  pattern.
* `pathTableM_join`: `pathTableM` with the rows of a well-formed table `t`
  joined before (the right side of a join in `IdGroup.evalGroupM`, with
  candidates for a variable endpoint from `t`, `pathCands`): the table is
  well formed and its join with the rows of `t` is `IdEquiv` to the join of
  the rows of `t` with the model's rows. A pair the candidates drop gives a
  row whose restricted variable is not a candidate; every row of `t` binds
  that variable to a candidate (`pathCands_rows`), so that row joins no row
  of `t` (`SemiJoin.idJoin_semijoin`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPathEvalTheorems
import L4Factoidal.Storage.Sbm11.IdLeafTheorems
import L4Factoidal.Storage.Sbm11.IdGroup

namespace L4Factoidal.Storage.Sbm11.IdPathTable

open L4Factoidal.RDF
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple IdPairs Pairs End idPathRow idPathRows)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq ColHolds NoUnbound)
open L4Factoidal.Storage.Sbm11.IdGroup (Pw)

/-! ## Columns built by a fold -/

theorem getElem!_modify (cols : Array ByteArray) (k c : Nat) (f : ByteArray → ByteArray) (hc : c < cols.size) :
    (cols.modify k f)[c]! = if k = c then f cols[c]! else cols[c]! := by
  rw [getElem!_pos _ c (by rw [Array.size_modify]; exact hc), Array.getElem_modify, getElem!_pos _ c hc]

/-- A fold over the pairs that, for each pair `acc` keeps, appends value
    `colF c a` to column `c` (of `nv`) and counts it. -/
theorem fold_cols (nv : Nat) (acc : UInt64 × UInt64 → Bool) (colF : Nat → UInt64 × UInt64 → UInt64)
    (step : Array ByteArray × Nat → UInt64 × UInt64 → Array ByteArray × Nat)
    (hstep : ∀ b a, b.1.size = nv →
      (acc a = true → (step b a).2 = b.2 + 1 ∧ (step b a).1.size = nv ∧
        ∀ c < nv, (step b a).1[c]! = L4Factoidal.Qlvr.Side.put64 b.1[c]! (colF c a)) ∧
      (acc a = false → step b a = b)) :
    ∀ (l : List (UInt64 × UInt64)) (b : Array ByteArray × Nat) (xs : Nat → List UInt64), b.1.size = nv →
      (∀ c < nv, ColHolds b.1[c]! (xs c)) →
      (l.foldl step b).1.size = nv ∧ (l.foldl step b).2 = b.2 + (l.filter acc).length ∧
        ∀ c < nv, ColHolds (l.foldl step b).1[c]! (xs c ++ (l.filter acc).map (colF c)) := by
  intro l
  induction l with
  | nil => intro b xs hs hc; simp [hs]; exact hc
  | cons a l ih =>
    intro b xs hs hc
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := hstep b a hs
    cases ha : acc a with
    | true =>
      obtain ⟨e1, e2, e3⟩ := h1 ha
      obtain ⟨g1, g2, g3⟩ := ih (step b a) (fun c => xs c ++ [colF c a]) e2 (fun c hc' => by
        rw [e3 c hc']; exact (hc c hc').put64 _)
      refine ⟨g1, ?_, ?_⟩
      · rw [g2, e1, List.filter_cons, if_pos ha]; simp; omega
      · intro c hc'
        have := g3 c hc'
        rw [List.filter_cons, if_pos ha]
        simpa using this
    | false =>
      rw [h2 ha]
      obtain ⟨g1, g2, g3⟩ := ih b xs hs hc
      refine ⟨g1, ?_, ?_⟩
      · rw [g2, List.filter_cons, if_neg (by simp [ha])]
      · intro c hc'
        rw [List.filter_cons, if_neg (by simp [ha])]
        exact g3 c hc'

theorem colHolds_empty (n : Nat) : ColHolds (ByteArray.emptyWithCapacity n) [] :=
  ColHolds.nil _ rfl

/-- The lookups of a row of a table whose columns hold value lists. -/
theorem lookup_cols (t : Table) (hnd : t.vars.toList.Nodup) (vals : Nat → List UInt64)
    (hc : ∀ c < t.vars.size, ColHolds t.cols[c]! (vals c)) (i : Nat) (v : String) (c : Nat)
    (hv : t.idx v = some c) (hi : i < (vals c).length) :
    idLookup v (t.idRow i) = TableTheorems.nz ((vals c)[i]) := by
  rw [TableTheorems.lookup_idRow t hnd, TableTheorems.lookupAt_eq, hv]
  simp only []
  congr 1
  have hcl := hc c (TableTheorems.idx_some hv).1
  unfold Table.at
  exact hcl.2 i hi

theorem pw_of_get {A B : List IdRow} (hl : A.length = B.length)
    (h : ∀ i (hi : i < B.length), RowEq A[i]! B[i]) : Pw RowEq A B := by
  induction A generalizing B with
  | nil => cases B with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons a A ih =>
    cases B with
    | nil => simp at hl
    | cons b B =>
      refine .cons ?_ (ih (by simpa using hl) (fun i hi => ?_))
      · have := h 0 (by simp)
        rwa [List.getElem!_cons_zero, List.getElem_cons_zero] at this
      · have := h (i + 1) (by simpa using hi)
        rwa [List.getElem!_cons_succ, List.getElem_cons_succ] at this

/-- **A table built by a fold of `fold_cols`.** Its rows are, row for row,
    `row a` of the kept pairs, when the lookups of `row a` are the column
    values and no column value is 0. -/
theorem table_of_fold (V : Array String) (hV : V.toList.Nodup) (acc : UInt64 × UInt64 → Bool)
    (colF : Nat → UInt64 × UInt64 → UInt64)
    (step : Array ByteArray × Nat → UInt64 × UInt64 → Array ByteArray × Nat)
    (hstep : ∀ b a, b.1.size = V.size →
      (acc a = true → (step b a).2 = b.2 + 1 ∧ (step b a).1.size = V.size ∧
        ∀ c < V.size, (step b a).1[c]! = L4Factoidal.Qlvr.Side.put64 b.1[c]! (colF c a)) ∧
      (acc a = false → step b a = b))
    (n : Nat) (l : List (UInt64 × UInt64)) (row : UInt64 × UInt64 → IdRow)
    (hrow : ∀ a u, idLookup u (row a) = match V.findIdx? (· == u) with
      | some c => some (colF c a)
      | none => none)
    (hnz : ∀ a ∈ l, acc a = true → ∀ c < V.size, colF c a ≠ 0) :
    let r := l.foldl step (V.map (fun _ => ByteArray.emptyWithCapacity n), 0)
    ({ vars := V, cols := r.1, rows := r.2 } : Table).WF ∧
      Pw RowEq ({ vars := V, cols := r.1, rows := r.2 } : Table).idRows ((l.filter acc).map row) := by
  intro r
  obtain ⟨h1, h2, h3⟩ := fold_cols V.size acc colF step hstep l (V.map (fun _ => ByteArray.emptyWithCapacity n), 0)
    (fun _ => []) (by simp) (fun c hc => by
      rw [getElem!_pos _ c (by simpa using hc)]; simp only [Array.getElem_map]; exact colHolds_empty n)
  simp only [List.nil_append, Nat.zero_add] at h2 h3
  let t : Table := { vars := V, cols := r.1, rows := r.2 }
  have hrows : t.rows = (l.filter acc).length := h2
  refine ⟨⟨h1, fun c hc => ?_, hV⟩, ?_⟩
  · have hcl := (h3 c (by rw [← h1]; exact hc)).1
    rw [getElem!_pos _ c hc, List.length_map] at hcl
    show r.1[c].size = 8 * r.2
    rw [hcl, h2]
  apply pw_of_get
  · rw [TableTheorems.idRows_length, List.length_map]; exact hrows
  · intro i hi
    rw [List.length_map] at hi
    rw [TableTheorems.idRows_get t i (by rw [hrows]; exact hi)]
    intro u
    rw [TableTheorems.lookup_idRow t hV, TableTheorems.lookupAt_eq, List.getElem_map, hrow]
    show (match V.findIdx? (· == u) with
      | some c => TableTheorems.nz (t.at c i)
      | none => none) = _
    cases hc : V.findIdx? (· == u) with
    | none => rfl
    | some c =>
      simp only []
      have hcl : c < V.size := by
        have := Array.findIdx?_eq_some_iff_getElem.mp hc
        obtain ⟨h, _⟩ := this
        exact h
      have hcol := h3 c hcl
      have hat : t.at c i = colF c (l.filter acc)[i] := by
        unfold Table.at
        have := hcol.2 i (by simpa using hi)
        simpa using this
      rw [hat]
      have hmem : (l.filter acc)[i] ∈ l.filter acc := List.getElem_mem hi
      have hne := hnz _ (List.mem_filter.mp hmem).1 (List.mem_filter.mp hmem).2 c hcl
      unfold TableTheorems.nz
      simp [hne, unbound]

/-! ## `pathRowsTable`, shape by shape -/

/-- An endpoint slot as the model's endpoint. -/
def endOf : Slot → End
  | .var v => .var v
  | .const x => .const x
  | .missing => .var ""

theorem rows_vv (v w : String) (hvw : v ≠ w) (pairs : Pairs) (hnz : ∀ pr ∈ pairs.toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0) :
    (pathRowsTable (.var v) (.var w) pairs).WF ∧
      Pw RowEq (pathRowsTable (.var v) (.var w) pairs).idRows
        (pairs.toList.filterMap (idPathRow (.var v) (.var w))) := by
  have hwv : (w != v) = true := by simpa using (Ne.symm hvw)
  unfold pathRowsTable
  simp only [Id.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  simp [hwv, Ne.symm hvw]
  rw [← Array.foldl_toList]
  have hfm : pairs.toList.filterMap (idPathRow (.var v) (.var w)) =
      (pairs.toList.filter (fun _ => true)).map (fun a => [(w, a.2), (v, a.1)]) := by
    rw [List.filter_eq_self.mpr (fun _ _ => rfl), ← List.filterMap_eq_map]
    congr 1; funext a
    simp [idPathRow, idLookup, Ne.symm hvw, hvw]
  rw [hfm]
  exact table_of_fold #[v, w] (by show [v, w].Nodup; simp [hvw]) (fun _ => true)
    (fun c a => if c = 0 then a.1 else a.2) _
    (fun b a hb => ⟨fun _ => ⟨rfl, by simp [hb], fun c hc => by
        have hc' : c = 0 ∨ c = 1 := by simp at hc; omega
        rcases hc' with rfl | rfl
        · rw [getElem!_modify _ _ _ _ (by simp [hb]), getElem!_modify _ _ _ _ (by simp [hb])]; simp
        · rw [getElem!_modify _ _ _ _ (by simp [hb]), getElem!_modify _ _ _ _ (by simp [hb])]; simp⟩,
      fun h => absurd h (by simp)⟩)
    _ _ _ (fun a u => by
      by_cases hu : u = v
      · subst hu; simp [idLookup, hvw, Ne.symm hvw, Array.findIdx?, Array.findIdx?.loop]
      · by_cases hw : u = w
        · subst hw; simp [idLookup, Ne.symm hu, hu, Array.findIdx?, Array.findIdx?.loop]
        · simp [idLookup, Ne.symm hu, Ne.symm hw, hu, hw, Array.findIdx?, Array.findIdx?.loop])
    (fun a ha _ c hc => by
      have hc' : c = 0 ∨ c = 1 := by simp at hc; omega
      rcases hc' with rfl | rfl
      · simpa using (hnz a ha).1
      · simpa using (hnz a ha).2)

theorem forIn_if (pairs : Pairs) (init : Array ByteArray × Nat) (cond : UInt64 × UInt64 → Prop)
    [DecidablePred cond] (upd : Array ByteArray × Nat → UInt64 × UInt64 → Array ByteArray × Nat) :
    forIn (m := Id) pairs init (fun x s => if cond x then pure (.yield (upd s x)) else pure (.yield (s.1, s.2))) =
      pure (pairs.toList.foldl (fun s x => if cond x then upd s x else s) init) := by
  rw [← Array.forIn_toList]
  generalize pairs.toList = l
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    by_cases h : cond a
    · rw [if_pos h, if_pos h]; exact ih _
    · rw [if_neg h, if_neg h]; exact ih _

theorem lookup1 (v u : String) (y : UInt64) :
    idLookup u [(v, y)] = match (#[v] : Array String).findIdx? (· == u) with
      | some c => some ((fun (_ : Nat) => y) c)
      | none => none := by
  by_cases hu : u = v
  · subst hu; simp [idLookup, Array.findIdx?, Array.findIdx?.loop]
  · simp [idLookup, Ne.symm hu, hu, Array.findIdx?, Array.findIdx?.loop]

theorem step1 (b : Array ByteArray × Nat) (hb : b.1.size = 1) (y : UInt64) :
    ((b.1.modify 0 fun x => L4Factoidal.Qlvr.Side.put64 x y), b.2 + 1).1.size = 1 ∧
      ∀ c < 1, ((b.1.modify 0 fun x => L4Factoidal.Qlvr.Side.put64 x y), b.2 + 1).1[c]! =
        L4Factoidal.Qlvr.Side.put64 b.1[c]! y := by
  refine ⟨by simp [hb], fun c hc => ?_⟩
  have : c = 0 := by omega
  subst this
  rw [getElem!_modify _ _ _ _ (by simp [hb])]; simp

theorem rows_vsame (v : String) (pairs : Pairs) (hnz : ∀ pr ∈ pairs.toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0) :
    (pathRowsTable (.var v) (.var v) pairs).WF ∧
      Pw RowEq (pathRowsTable (.var v) (.var v) pairs).idRows
        (pairs.toList.filterMap (idPathRow (.var v) (.var v))) := by
  unfold pathRowsTable
  simp only [Id.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  simp
  rw [forIn_if]
  have hfm : pairs.toList.filterMap (idPathRow (.var v) (.var v)) =
      (pairs.toList.filter (fun a => decide (a.2 = a.1))).map (fun a => [(v, a.1)]) := by
    rw [← List.filterMap_eq_map, List.filterMap_filter]
    congr 1; funext a
    by_cases h : a.2 = a.1
    · simp [idPathRow, idLookup, h]
    · simp [idPathRow, idLookup, h, Ne.symm h]
  rw [hfm]
  exact table_of_fold #[v] (by show [v].Nodup; simp) (fun a => decide (a.2 = a.1)) (fun _ a => a.1) _
    (fun b a hb => ⟨fun h => by
        have h' : a.2 = a.1 := by simpa using h
        simp only [h', if_true]
        exact ⟨by first | rfl | trivial, (step1 b hb a.1).1, (step1 b hb a.1).2⟩,
      fun h => by
        have h' : ¬ a.2 = a.1 := by simpa using h
        simp only [h', if_false]⟩)
    _ _ _ (fun a u => lookup1 v u a.1) (fun a ha _ c _ => (hnz a ha).1)

theorem rows_vconst (v : String) (k : UInt64) (pairs : Pairs) (hnz : ∀ pr ∈ pairs.toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0) :
    (pathRowsTable (.var v) (.const k) pairs).WF ∧
      Pw RowEq (pathRowsTable (.var v) (.const k) pairs).idRows
        (pairs.toList.filterMap (idPathRow (.var v) (.const k))) := by
  unfold pathRowsTable
  simp only [Id.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  simp
  rw [forIn_if]
  have hfm : pairs.toList.filterMap (idPathRow (.var v) (.const k)) =
      (pairs.toList.filter (fun a => decide (a.2 = k))).map (fun a => [(v, a.1)]) := by
    rw [← List.filterMap_eq_map, List.filterMap_filter]
    congr 1; funext a
    by_cases h : a.2 = k
    · simp [idPathRow, h]
    · simp [idPathRow, h, Ne.symm h]
  rw [hfm]
  exact table_of_fold #[v] (by show [v].Nodup; simp) (fun a => decide (a.2 = k)) (fun _ a => a.1) _
    (fun b a hb => ⟨fun h => by
        have h' : a.2 = k := by simpa using h
        simp only [h', if_true]
        exact ⟨by first | rfl | trivial, (step1 b hb a.1).1, (step1 b hb a.1).2⟩,
      fun h => by
        have h' : ¬ a.2 = k := by simpa using h
        simp only [h', if_false]⟩)
    _ _ _ (fun a u => lookup1 v u a.1) (fun a ha _ c _ => (hnz a ha).1)

theorem rows_constv (k : UInt64) (w : String) (pairs : Pairs) (hnz : ∀ pr ∈ pairs.toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0) :
    (pathRowsTable (.const k) (.var w) pairs).WF ∧
      Pw RowEq (pathRowsTable (.const k) (.var w) pairs).idRows
        (pairs.toList.filterMap (idPathRow (.const k) (.var w))) := by
  unfold pathRowsTable
  simp only [Id.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  simp
  rw [forIn_if]
  have hfm : pairs.toList.filterMap (idPathRow (.const k) (.var w)) =
      (pairs.toList.filter (fun a => decide (a.1 = k))).map (fun a => [(w, a.2)]) := by
    rw [← List.filterMap_eq_map, List.filterMap_filter]
    congr 1; funext a
    by_cases h : a.1 = k
    · simp [idPathRow, idLookup, h]
    · simp [idPathRow, h, Ne.symm h]
  rw [hfm]
  exact table_of_fold #[w] (by show [w].Nodup; simp) (fun a => decide (a.1 = k)) (fun _ a => a.2) _
    (fun b a hb => ⟨fun h => by
        have h' : a.1 = k := by simpa using h
        simp only [h', if_true]
        exact ⟨by first | rfl | trivial, (step1 b hb a.2).1, (step1 b hb a.2).2⟩,
      fun h => by
        have h' : ¬ a.1 = k := by simpa using h
        simp only [h', if_false]⟩)
    _ _ _ (fun a u => lookup1 w u a.2) (fun a ha _ c _ => (hnz a ha).2)

theorem rows_constconst (k k' : UInt64) (pairs : Pairs) :
    (pathRowsTable (.const k) (.const k') pairs).WF ∧
      Pw RowEq (pathRowsTable (.const k) (.const k') pairs).idRows
        (pairs.toList.filterMap (idPathRow (.const k) (.const k'))) := by
  unfold pathRowsTable
  simp only [Id.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  simp
  rw [forIn_if]
  have hfm : pairs.toList.filterMap (idPathRow (.const k) (.const k')) =
      (pairs.toList.filter (fun a => decide (a.1 = k ∧ a.2 = k'))).map (fun _ => []) := by
    rw [← List.filterMap_eq_map, List.filterMap_filter]
    congr 1; funext a
    by_cases h : a.1 = k <;> by_cases h' : a.2 = k'
    · simp [idPathRow, h, h']
    · have : ¬ k' = a.2 := fun e => h' e.symm
      simp [idPathRow, h, h', this]
    · have : ¬ k = a.1 := fun e => h e.symm
      simp [idPathRow, h, this]
    · have : ¬ k = a.1 := fun e => h e.symm
      simp [idPathRow, h, this]
  rw [hfm]
  exact table_of_fold #[] (by show ([] : List String).Nodup; simp) (fun a => decide (a.1 = k ∧ a.2 = k'))
    (fun _ _ => 0) _
    (fun b a hb => ⟨fun h => by
        have h' : a.1 = k ∧ a.2 = k' := by simpa using h
        simp only [h', and_self, if_true]
        exact ⟨by first | rfl | trivial, hb, fun c hc => absurd hc (by simp)⟩,
      fun h => by
        have h' : ¬ (a.1 = k ∧ a.2 = k') := by simpa using h
        simp only [h', if_false]⟩)
    _ _ _ (fun a u => by simp [idLookup, Array.findIdx?, Array.findIdx?.loop])
    (fun a ha _ c hc => absurd hc (by simp))

/-- **`pathRowsTable`**: row for row, the rows `idPathRow` gives. -/
theorem pathRowsTable_rows (s o : Slot) (hs : s ≠ .missing) (ho : o ≠ .missing) (pairs : Pairs)
    (hnz : ∀ pr ∈ pairs.toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0) :
    (pathRowsTable s o pairs).WF ∧
      Pw RowEq (pathRowsTable s o pairs).idRows (pairs.toList.filterMap (idPathRow (endOf s) (endOf o))) := by
  cases s with
  | missing => exact absurd rfl hs
  | var v =>
    cases o with
    | missing => exact absurd rfl ho
    | var w =>
      by_cases h : v = w
      · subst h; exact rows_vsame v pairs hnz
      · exact rows_vv v w h pairs hnz
    | const k => exact rows_vconst v k pairs hnz
  | const k =>
    cases o with
    | missing => exact absurd rfl ho
    | var w => exact rows_constv k w pairs hnz
    | const k' => exact rows_constconst k k' pairs

/-! ## The pairs of `pathTableM` -/

theorem pathCands_unit (v : String) : pathCands IdGroup.unitTable v = none := by
  have : IdGroup.unitTable.idx v = none := by
    simp [L4Factoidal.Qlvr.Table.idx, IdGroup.unitTable]
  unfold pathCands
  rw [this]
  rfl

/-- The restriction `pathTableM` picks with no rows joined before. -/
def restrOf : Slot → Slot → Bool × Option (Array UInt64)
  | .const x, _ => (true, some #[x])
  | _, .const y => (false, some #[y])
  | _, _ => (true, none)

theorem pathRestr_unit (rp : RPath) (hs : rp.s ≠ .missing) (ho : rp.o ≠ .missing) :
    ((pathRestr rp IdGroup.unitTable).1, (pathRestr rp IdGroup.unitTable).2.1) = restrOf rp.s rp.o := by
  unfold pathRestr restrOf
  cases h1 : rp.s with
  | missing => exact absurd h1 hs
  | const x => rfl
  | var v =>
    cases h2 : rp.o with
    | missing => exact absurd h2 ho
    | const y => rfl
    | var w => simp [pathCands_unit]

theorem restrOf_good (s o : Slot) : IdPathClosureExec.RGood (restrOf s o).2 := by
  intro cs h
  cases s <;> cases o <;> simp [restrOf] at h <;> subst h <;> simp

/-- A pair the endpoints accept is a pair the restriction keeps. -/
theorem restrOf_keeps (s o : Slot) (hs : s ≠ .missing) (ho : o ≠ .missing) (pr : UInt64 × UInt64)
    (h : idPathRow (endOf s) (endOf o) pr ≠ none) :
    IdPathScanTheorems.Restr (restrOf s o).1 (restrOf s o).2 pr = true := by
  cases s with
  | missing => exact absurd rfl hs
  | const x =>
    simp only [restrOf, IdPathScanTheorems.Restr, if_true]
    simp only [endOf, idPathRow] at h
    by_cases hx : (x == pr.1) = true
    · have : pr.1 = x := (beq_iff_eq.mp hx).symm
      simp [this]
    · simp only [hx, Bool.false_eq_true, if_false] at h
      exact absurd rfl h
  | var v =>
    cases o with
    | missing => exact absurd rfl ho
    | var w => rfl
    | const y =>
      simp only [restrOf, IdPathScanTheorems.Restr, Bool.false_eq_true, if_false]
      simp only [endOf, idPathRow] at h
      by_cases hy : (y == pr.2) = true
      · have : pr.2 = y := (beq_iff_eq.mp hy).symm
        simp [this]
      · simp only [hy, Bool.false_eq_true, if_false] at h
        exact absurd rfl h

theorem any_arr_iff (a : Pairs) (c : UInt64) : a.any (· == (c, c)) = true ↔ (c, c) ∈ a.toList := by
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    have : a[i] = (c, c) := beq_iff_eq.mp h
    rw [← this]; exact Array.getElem_mem_toList hi
  · intro h
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
    exact ⟨i, by simpa using hi, by simp [← he]⟩

theorem any_list_iff (L : IdPairs) (c : UInt64) :
    L.any (fun pr => pr.1 == c && pr.2 == c) = true ↔ (c, c) ∈ L := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨pr, hp, h⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have : pr = (c, c) := Prod.ext h.1 h.2
    rw [← this]; exact hp
  · intro h; exact ⟨(c, c), h, by simp⟩

theorem pathPairs_core (es eo : End) (consts : List UInt64) (hc : consts = IdPath.idConsts es eo) (L : IdPairs)
    (fwd : Bool) (R : Option (Array UInt64))
    (hrk : ∀ pr, idPathRow es eo pr ≠ none → IdPathScanTheorems.Restr fwd R pr = true)
    (pairs0 : Pairs) (hp0 : pairs0.toList.Perm (L.filter (IdPathScanTheorems.Restr fwd R))) (z : Bool) :
    ((if z then pairs0 ++ (consts.filter fun c => !pairs0.any (· == (c, c))).toArray.map (fun c => (c, c))
      else pairs0).toList.filterMap (idPathRow es eo)).Perm
      (idPathRows es eo (IdPath.idConstRefl z (IdPath.idConsts es eo) L)) := by
  subst hc
  have hbase : (pairs0.toList.filterMap (idPathRow es eo)).Perm (L.filterMap (idPathRow es eo)) := by
    refine (hp0.filterMap _).trans (List.Perm.of_eq ?_)
    rw [List.filterMap_filter]
    congr 1; funext pr
    by_cases h : idPathRow es eo pr = none
    · rw [h]; split <;> rfl
    · rw [if_pos (hrk pr h)]
  unfold idPathRows IdPath.idConstRefl
  cases z with
  | false => simpa using hbase
  | true =>
    simp only [if_true, Array.toList_append, Array.toList_map, List.filterMap_append]
    refine hbase.append (List.Perm.of_eq ?_)
    simp only [List.toList_toArray, List.filterMap_map, List.filterMap_filter]
    congr 1; funext c
    simp only [Function.comp]
    by_cases h : idPathRow es eo (c, c) = none
    · rw [h]; split <;> split <;> rfl
    · have hr := hrk (c, c) h
      have e : (pairs0.any (· == (c, c))) = (L.any (fun pr => pr.1 == c && pr.2 == c)) := by
        apply Bool.eq_iff_iff.mpr
        rw [any_arr_iff, any_list_iff, hp0.mem_iff, List.mem_filter]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', hr⟩⟩
      rw [e]

/-- **The pairs of `pathTableM`**: the rows the endpoints give from the
    restricted pairs with the reflexive pairs of `pathPairsOf` are, up to
    order, those of the whole relation after `idConstRefl`. -/
theorem pathPairs_rows (rp : RPath) (hs : rp.s ≠ .missing) (ho : rp.o ≠ .missing) (L : IdPairs) (fwd : Bool)
    (R : Option (Array UInt64))
    (hrk : ∀ pr, idPathRow (endOf rp.s) (endOf rp.o) pr ≠ none → IdPathScanTheorems.Restr fwd R pr = true)
    (pairs0 : Pairs) (hp0 : pairs0.toList.Perm (L.filter (IdPathScanTheorems.Restr fwd R))) :
    ((pathPairsOf rp pairs0).toList.filterMap (idPathRow (endOf rp.s) (endOf rp.o))).Perm
      (idPathRows (endOf rp.s) (endOf rp.o) (IdPath.idConstRefl rp.zeroLen (IdPath.idConsts (endOf rp.s) (endOf rp.o)) L)) := by
  obtain ⟨s, o, ip, zl, g⟩ := rp
  simp only [] at hs ho hrk ⊢
  unfold pathPairsOf
  cases s with
  | missing => exact absurd rfl hs
  | var v =>
    cases o with
    | missing => exact absurd rfl ho
    | var w => exact pathPairs_core _ _ [] rfl L fwd R hrk pairs0 hp0 zl
    | const y => exact pathPairs_core _ _ [y] rfl L fwd R hrk pairs0 hp0 zl
  | const x =>
    cases o with
    | missing => exact absurd rfl ho
    | var w => exact pathPairs_core _ _ [x] rfl L fwd R hrk pairs0 hp0 zl
    | const y => exact pathPairs_core _ _ [x, y] rfl L fwd R hrk pairs0 hp0 zl

/-! ## `pathTableM` with no rows joined before -/

open L4Factoidal.Storage.Sbm11.BgpTableTheorems (BgpStore)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd)

/-- No id of a triple of the graph is 0. -/
theorem store_nz (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T) :
    ∀ x ∈ T, x.1 ≠ 0 ∧ x.2.2 ≠ 0 := by
  obtain ⟨prb, ms, hpm, hP⟩ := hst.perm 2 (by decide)
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hP.mem_iff.mpr hx)
  have hrR := (List.mem_filter.mp hr).1
  have hfit := ScanTableTheorems.rows_fit prb ms r hrR
  have hnz := hpm.nz r hrR
  have e : ∀ c, c < 3 → (rowCol r c).toUInt64 ≠ 0 := by
    intro c hc h
    have := congrArg UInt64.toNat h
    rw [ScanFoldTheorems.uint64_toNat_toUInt64 _ (hfit c (by omega))] at this
    exact hnz c hc (by simpa using this)
  exact ⟨e 0 (by decide), e 2 (by decide)⟩

/-- **The table of a path pattern** (`pathTableM` with no rows joined
    before, the leaf of the nested evaluator): over a store of `BgpStore`,
    the table's rows bind no variable twice and are `IdEquiv` to the model's
    rows: `idPathRows` after `idConstRefl` of `idEvalPath` over `T`. -/
theorem pathTableM_rows (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (cid : Term → Option UInt64)
    (rp : RPath) (path : L4Factoidal.SPARQL.PropertyPath) (hg : rp.g = some g)
    (hip : IdPathEval.IPathOk cid path rp.ipath) (hz : rp.zeroLen = IdPath.pathZeroLen path)
    (hs : rp.s ≠ .missing) (ho : rp.o ≠ .missing) (hc0 : ∀ x, (rp.s = .const x ∨ rp.o = .const x) → x ≠ 0) :
    ∃ tab how s, pathTableM st rp IdGroup.unitTable = pure (tab, how, s) ∧ tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv tab.idRows (idPathRows (endOf rp.s) (endOf rp.o)
        (IdPath.idConstRefl (IdPath.pathZeroLen path) (IdPath.idConsts (endOf rp.s) (endOf rp.o))
          (IdPath.idEvalPath (fun i => cid (.iri i)) path T))) := by
  have hpr := pathRestr_unit rp hs ho
  generalize hP : pathRestr rp IdGroup.unitTable = pr at hpr
  obtain ⟨fwd, R, how⟩ := pr
  simp only [] at hpr
  have hR : IdPathClosureExec.RGood R := by
    have := restrOf_good rp.s rp.o
    rw [← hpr] at this
    exact this
  obtain ⟨pairs0, s, he, hp0⟩ := IdPathEval.evalIM_spec st g T hst cid path rp.ipath hip fwd R hR
  let L := IdPath.idEvalPath (fun i => cid (.iri i)) path T
  have hTnz := store_nz st g T hst
  have hLnz : ∀ pr ∈ L, pr.1 ≠ 0 ∧ pr.2 ≠ 0 := by
    intro pr hpr'
    obtain ⟨h1, h2⟩ := IdPath.eval_nodes (fun i => cid (.iri i)) T path pr hpr'
    rw [IdPathScanTheorems.mem_graphNodes] at h1 h2
    obtain ⟨x, hx, e1 | e1⟩ := h1 <;> obtain ⟨y, hy, e2 | e2⟩ := h2 <;>
      exact ⟨e1 ▸ (by first | exact (hTnz x hx).1 | exact (hTnz x hx).2),
        e2 ▸ (by first | exact (hTnz y hy).1 | exact (hTnz y hy).2)⟩
  have hpnz : ∀ pr ∈ (pathPairsOf rp pairs0).toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0 := by
    intro pr hpr'
    unfold pathPairsOf at hpr'
    simp only [] at hpr'
    have h0 : ∀ q ∈ pairs0.toList, q.1 ≠ 0 ∧ q.2 ≠ 0 := fun q hq =>
      hLnz q (List.mem_filter.mp (hp0.mem_iff.mp hq)).1
    split at hpr'
    · rw [Array.toList_append, List.mem_append] at hpr'
      rcases hpr' with h | h
      · exact h0 pr h
      · simp only [Array.toList_map, List.toList_toArray, List.mem_map, List.mem_filter] at h
        obtain ⟨c, ⟨hc, _⟩, rfl⟩ := h
        have : c ≠ 0 := by
          revert hc
          cases h1 : rp.s <;> cases h2 : rp.o <;> simp <;>
            first
            | (intro e; subst e; exact hc0 _ (.inl h1))
            | (intro e; subst e; exact hc0 _ (.inr h2))
            | (rintro (e | e) <;> subst e <;> first | exact hc0 _ (.inl h1) | exact hc0 _ (.inr h2))
        exact ⟨this, this⟩
    · exact h0 pr hpr'
  obtain ⟨hnd, hpw⟩ := pathRowsTable_rows rp.s rp.o hs ho (pathPairsOf rp pairs0) hpnz
  have hperm := pathPairs_rows rp hs ho L fwd R (fun pr h => by
      have := restrOf_keeps rp.s rp.o hs ho pr h
      rw [← hpr] at this; exact this) pairs0 hp0
  rw [hz] at hperm
  refine ⟨pathRowsTable rp.s rp.o (pathPairsOf rp pairs0),
    s!"{how}: {(pathPairsOf rp pairs0).size} pairs, {(pathRowsTable rp.s rp.o (pathPairsOf rp pairs0)).rows} rows",
    s, ?_, hnd, BgpTableTheorems.nd_idRows _ hnd.nodup, ?_⟩
  · unfold pathTableM
    rw [hP]
    simp only []
    rw [hg, he]
    rfl
  · obtain ⟨A', hp, hw⟩ := Pw.perm_right hpw hperm
    exact ⟨A', hp, hw⟩

/-! ## `pathTableM` with rows joined before (`IdQuery.pathCands`) -/

/-- The loop of `pathCands`: it stops at the first row whose column holds
    `unbound`, else it has appended the column's value of every row. -/
theorem cands_loop (bad : Nat → Bool) (val : Nat → UInt64) :
    ∀ (L : List Nat) (acc : Array UInt64),
      let F := forIn (m := Id) L ((none : Option (Option (Array UInt64))), acc) fun i s =>
        if bad i = true then pure (ForInStep.done (some none, s.2))
        else pure (ForInStep.yield (none, s.2.push (val i)))
      F.1 = some none ∨ (F.1 = none ∧ (∀ i ∈ L, bad i = false) ∧ F.2 = acc ++ (L.map val).toArray) := by
  intro L
  induction L with
  | nil =>
    intro acc; right
    refine ⟨rfl, ?_, ?_⟩
    · intro _ h; cases h
    · show acc = acc ++ #[]; simp
  | cons i L ih =>
    intro acc
    simp only [List.forIn_cons]
    cases hb : bad i with
    | true => left; rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases ih (acc.push (val i)) with h | ⟨h1, h2, h3⟩
      · left; exact h
      · right
        refine ⟨h1, fun j hj => ?_, ?_⟩
        · rcases List.mem_cons.mp hj with e | e
          · subst e; exact hb
          · exact h2 j e
        · erw [h3]; simp

/-- What `pathCands` returns: the variable is a column, no row leaves it
    unbound, and the candidates are the column's values, sorted, each once. -/
theorem pathCands_some (t : Table) (v : String) (c : Array UInt64) (h : pathCands t v = some c) :
    ∃ col, t.idx v = some col ∧ (∀ i < t.rows, (t.at col i == unbound) = false) ∧
      c = IdPath.sortedDistinct ((List.range t.rows).map (t.at col)).toArray := by
  unfold pathCands at h
  cases hx : t.idx v with
  | none => rw [hx] at h; cases h
  | some col =>
    rw [hx] at h
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one] at h
    have hl := cands_loop (fun i => t.at col i == unbound) (t.at col) (List.range' 0 t.rows) (Array.mkEmpty t.rows)
    generalize hF : forIn (m := Id) (List.range' 0 t.rows) _ _ = F at h hl
    obtain ⟨f1, f2⟩ := F
    simp only [] at hl
    rcases hl with h1 | ⟨h1, h2, h3⟩
    · subst h1; cases h
    · subst h1
      have h' : some (IdPath.sortedDistinct f2) = some c := h
      refine ⟨col, rfl, fun i hi => h2 i (by simp [List.mem_range'_1]; omega), ?_⟩
      rw [← Option.some.inj h', show f2 = _ from h3, List.range_eq_range']
      simp [Array.mkEmpty]


/-- Candidates from `pathCands` are increasing (`RGood`), and every row of the
    table binds the variable to a candidate. -/
theorem pathCands_rows (t : Table) (ht : t.WF) (v : String) (c : Array UInt64) (h : pathCands t v = some c) :
    IdPathClosureExec.RGood (some c) ∧ ∀ r ∈ t.idRows, ∃ x, idLookup v r = some x ∧ c.contains x = true := by
  obtain ⟨col, hx, hb, hc⟩ := pathCands_some t v c h
  subst hc
  refine ⟨IdPathEval.rgood_sd _, ?_⟩
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hi' := List.mem_range.mp hi
  refine ⟨t.at col i, ?_, ?_⟩
  · rw [TableTheorems.lookup_idRow t ht.nodup]
    unfold L4Factoidal.Qlvr.Table.lookupAt
    rw [hx]
    simp [hb i hi']
  · rw [Array.contains_iff_mem, ← Array.mem_toList_iff, (IdPath.sortedDistinct_spec _).2]
    simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi', rfl⟩

/-- A filter before `filterMap` is a filter after it, when the test after
    reads what the test before reads. -/
theorem filterMap_filter_comm {α β : Type} (F : α → Option β) (q : α → Bool) (k : β → Bool)
    (hk : ∀ a b, F a = some b → k b = q a) :
    ∀ L : List α, (L.filter q).filterMap F = (L.filterMap F).filter k := by
  intro L
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.filter_cons, List.filterMap_cons]
    cases hF : F a with
    | none =>
      simp only []
      split <;> simp [hF, ih]
    | some b =>
      simp only [List.filter_cons, hk a b hF]
      split <;> simp [hF, ih]

/-- For two variable endpoints, the restriction `Restr` of the candidates
    keeps a pair exactly when the row of the pair binds the restricted
    variable to a candidate (`SemiJoin.keepRow`). -/
theorem keep_vv (v w : String) (c : Array UInt64) (fwd : Bool) (pr : UInt64 × UInt64) (r : IdRow)
    (h : idPathRow (.var v) (.var w) pr = some r) :
    SemiJoin.keepRow (if fwd then v else w) (fun x => c.contains x) r =
      IdPathScanTheorems.Restr fwd (some c) pr := by
  unfold idPathRow at h
  by_cases hvw : v = w
  · subst hvw
    simp only [idLookup, if_true] at h
    by_cases he : pr.1 = pr.2
    · simp only [he, beq_self_eq_true, if_true, Option.some.injEq] at h
      subst h
      cases fwd <;> simp [SemiJoin.keepRow, idLookup, IdPathScanTheorems.Restr, he]
    · have : (pr.1 == pr.2) = false := by simpa using he
      simp [this] at h
  · simp only [idLookup, hvw, if_false, Option.some.injEq] at h
    subst h
    have hwv : ¬ w = v := Ne.symm hvw
    cases fwd <;> simp [SemiJoin.keepRow, idLookup, IdPathScanTheorems.Restr, hwv]


/-- No id of a pair of the path relation over the graph is 0. -/
theorem eval_nz (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (cid : Term → Option UInt64) (path : L4Factoidal.SPARQL.PropertyPath) :
    ∀ pr ∈ IdPath.idEvalPath (fun i => cid (.iri i)) path T, pr.1 ≠ 0 ∧ pr.2 ≠ 0 := by
  have hTnz := store_nz st g T hst
  intro pr hpr'
  obtain ⟨h1, h2⟩ := IdPath.eval_nodes (fun i => cid (.iri i)) T path pr hpr'
  rw [IdPathScanTheorems.mem_graphNodes] at h1 h2
  obtain ⟨x, hx, e1 | e1⟩ := h1 <;> obtain ⟨y, hy, e2 | e2⟩ := h2 <;>
    exact ⟨e1 ▸ (by first | exact (hTnz x hx).1 | exact (hTnz x hx).2),
      e2 ▸ (by first | exact (hTnz y hy).1 | exact (hTnz y hy).2)⟩

/-- The model's rows for two variable endpoints: no constant, so
    `idConstRefl` adds no pair. -/
theorem model_vv (v w : String) (z : Bool) (L : IdPairs) :
    idPathRows (endOf (.var v)) (endOf (.var w)) (IdPath.idConstRefl z (IdPath.idConsts (endOf (.var v)) (endOf (.var w))) L) =
      idPathRows (.var v) (.var w) L := by
  cases z <;> simp [IdPath.idConstRefl, IdPath.idConsts, endOf]

section
variable (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (cid : Term → Option UInt64)
    (rp : RPath) (path : L4Factoidal.SPARQL.PropertyPath) (hg : rp.g = some g)
    (hip : IdPathEval.IPathOk cid path rp.ipath)
include hst hg hip

/-- `pathTableM` with candidates for a variable endpoint from the rows of
    `t`: its table, joined with `t`, gives the rows of the join of `t` with
    the model's unrestricted rows, up to order (`IdEquiv`). A pair the
    candidates drop gives a row whose restricted variable is not a
    candidate, and every row of `t` binds that variable to a candidate, so
    the row joins no row of `t` (`SemiJoin.idJoin_semijoin`). -/
theorem pathTableM_cands (v w : String) (hsv : rp.s = .var v) (hov : rp.o = .var w)
    (t : Table) (ht : t.WF) (fwd : Bool) (c : Array UInt64)
    (hR : (pathRestr rp t).1 = fwd ∧ (pathRestr rp t).2.1 = some c)
    (hc : pathCands t (if fwd then v else w) = some c) :
    ∃ tab how s, pathTableM st rp t = pure (tab, how, s) ∧ tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv (IdJoin.idJoin t.idRows tab.idRows)
        (IdJoin.idJoin t.idRows (idPathRows (.var v) (.var w) (IdPath.idEvalPath (fun i => cid (.iri i)) path T))) := by
  obtain ⟨hgood, hrows⟩ := pathCands_rows t ht _ c hc
  generalize hP : pathRestr rp t = pr at hR
  obtain ⟨fwd', R, how⟩ := pr
  obtain ⟨e1, e2⟩ := hR
  simp only [] at e1 e2
  subst e1 e2
  obtain ⟨pairs0, s, he, hp0⟩ := IdPathEval.evalIM_spec st g T hst cid path rp.ipath hip fwd' (some c) hgood
  have hpp : pathPairsOf rp pairs0 = pairs0 := by
    simp [pathPairsOf, hsv, hov]
  have hLnz := eval_nz st g T hst cid path
  have hpnz : ∀ pr ∈ pairs0.toList, pr.1 ≠ 0 ∧ pr.2 ≠ 0 := fun q hq =>
    hLnz q (List.mem_filter.mp (hp0.mem_iff.mp hq)).1
  obtain ⟨hwf, hpw⟩ := pathRowsTable_rows (.var v) (.var w) (by simp) (by simp) pairs0 hpnz
  let L := IdPath.idEvalPath (fun i => cid (.iri i)) path T
  have hperm : (pairs0.toList.filterMap (idPathRow (endOf (.var v)) (endOf (.var w)))).Perm
      ((idPathRows (.var v) (.var w) L).filter (SemiJoin.keepRow (if fwd' then v else w) (fun x => c.contains x))) := by
    refine (hp0.filterMap _).trans (List.Perm.of_eq ?_)
    unfold idPathRows
    exact filterMap_filter_comm _ _ _ (fun pr r h => keep_vv v w c fwd' pr r h) L
  obtain ⟨A', hp, hw⟩ := Pw.perm_right hpw hperm
  have hnd := BgpTableTheorems.nd_idRows t ht.nodup
  refine ⟨pathRowsTable rp.s rp.o (pathPairsOf rp pairs0),
    s!"{how}: {(pathPairsOf rp pairs0).size} pairs, {(pathRowsTable rp.s rp.o (pathPairsOf rp pairs0)).rows} rows",
    s, ?_, ?_, ?_, ?_⟩
  · unfold pathTableM
    rw [hP]
    simp only []
    rw [hg, he]
    rfl
  · rw [hpp, hsv, hov]; exact hwf
  · rw [hpp, hsv, hov]; exact BgpTableTheorems.nd_idRows _ hwf.nodup
  · rw [hpp, hsv, hov]
    have h1 := BgpTableTheorems.idJoin_equiv (IdEquiv.refl t.idRows) ⟨A', hp, hw⟩ hnd hnd
    have h2 : IdJoin.idJoin t.idRows ((idPathRows (.var v) (.var w) L).filter
        (SemiJoin.keepRow (if fwd' then v else w) (fun x => c.contains x))) =
        IdJoin.idJoin t.idRows (idPathRows (.var v) (.var w) L) :=
      SemiJoin.idJoin_semijoin _ _ _ _ hrows
    rw [h2] at h1
    exact h1

/-- `pathTableM` when the rows of `t` give no candidates (or a constant
    endpoint restricts first): the table of `pathTableM_rows`. -/
theorem pathTableM_same (hz : rp.zeroLen = IdPath.pathZeroLen path)
    (hs : rp.s ≠ .missing) (ho : rp.o ≠ .missing) (hc0 : ∀ x, (rp.s = .const x ∨ rp.o = .const x) → x ≠ 0)
    (t : Table) (ht : t.WF) (hP : pathRestr rp t = pathRestr rp IdGroup.unitTable) :
    ∃ tab how s, pathTableM st rp t = pure (tab, how, s) ∧ tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv (IdJoin.idJoin t.idRows tab.idRows)
        (IdJoin.idJoin t.idRows (idPathRows (endOf rp.s) (endOf rp.o)
          (IdPath.idConstRefl (IdPath.pathZeroLen path) (IdPath.idConsts (endOf rp.s) (endOf rp.o))
            (IdPath.idEvalPath (fun i => cid (.iri i)) path T)))) := by
  obtain ⟨tab, how, s, he, hwf, hnd, heq⟩ :=
    pathTableM_rows st g T hst cid rp path hg hip hz hs ho hc0
  have hnt := BgpTableTheorems.nd_idRows t ht.nodup
  refine ⟨tab, how, s, ?_, hwf, hnd, BgpTableTheorems.idJoin_equiv (IdEquiv.refl _) heq hnt hnt⟩
  have : pathTableM st rp t = pathTableM st rp IdGroup.unitTable := by
    unfold pathTableM; rw [hP]
  rw [this, he]

/-- **The table of a path pattern with rows joined before** (`pathTableM`
    with `t` the left side of a join, as `IdGroup.evalGroupM` runs it): over
    a store of `BgpStore`, for any well-formed `t`, the table is well formed,
    its rows bind no variable twice, and its join with the rows of `t` is,
    up to order (`IdEquiv`), the join of the rows of `t` with the model's
    rows of the path pattern (`idPathRows` after `idConstRefl` of
    `idEvalPath`), which are the rows of `pathTableM` with no rows joined
    before (`pathTableM_rows`). -/
theorem pathTableM_join (hz : rp.zeroLen = IdPath.pathZeroLen path)
    (hs : rp.s ≠ .missing) (ho : rp.o ≠ .missing) (hc0 : ∀ x, (rp.s = .const x ∨ rp.o = .const x) → x ≠ 0)
    (t : Table) (ht : t.WF) :
    ∃ tab how s, pathTableM st rp t = pure (tab, how, s) ∧ tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv (IdJoin.idJoin t.idRows tab.idRows)
        (IdJoin.idJoin t.idRows (idPathRows (endOf rp.s) (endOf rp.o)
          (IdPath.idConstRefl (IdPath.pathZeroLen path) (IdPath.idConsts (endOf rp.s) (endOf rp.o))
            (IdPath.idEvalPath (fun i => cid (.iri i)) path T)))) := by
  have same := pathTableM_same st g T hst cid rp path hg hip hz hs ho hc0 t ht
  cases hs' : rp.s with
  | missing => exact absurd hs' hs
  | const x =>
    rw [← hs']
    exact same (by simp [pathRestr, hs'])
  | var v =>
    cases ho' : rp.o with
    | missing => exact absurd ho' ho
    | const y =>
      rw [← hs', ← ho']
      exact same (by simp [pathRestr, hs', ho'])
    | var w =>
      rw [model_vv]
      cases hcv : pathCands t v with
      | some c =>
        exact pathTableM_cands st g T hst cid rp path hg hip v w hs' ho' t ht true c
          (by simp [pathRestr, hs', ho', hcv]) (by simpa using hcv)
      | none =>
        cases hcw : pathCands t w with
        | some c =>
          exact pathTableM_cands st g T hst cid rp path hg hip v w hs' ho' t ht false c
            (by simp [pathRestr, hs', ho', hcv, hcw]) (by simpa using hcw)
        | none =>
          have := same (by simp [pathRestr, hs', ho', hcv, hcw, pathCands_unit])
          rw [hs', ho', model_vv] at this
          exact this

end

end L4Factoidal.Storage.Sbm11.IdPathTable

#print axioms L4Factoidal.Storage.Sbm11.IdPathTable.pathTableM_rows
#print axioms L4Factoidal.Storage.Sbm11.IdPathTable.pathRowsTable_rows
#print axioms L4Factoidal.Storage.Sbm11.IdPathTable.pathPairs_rows
#print axioms L4Factoidal.Storage.Sbm11.IdPathTable.pathTableM_join
