/-
L4Factoidal.Storage.Sbm11.TableOuterTheorems — the merge join and the left
outer join of the SBM11 id path over the denotation of an id `Table`
(issue https://github.com/danbri/factoidal/issues/776; lemmas L5a′ and L5g″
of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

The denotation, `RowEq`, `RowsEq` and the column lemmas are those of
`TableTheorems`.

* `mergeJoin_rows` (L5a′): `Qlvr.mergeJoin l r v` of two well-formed tables
  with no `unbound` id, both in non-decreasing order of the ids of `v`
  (the precondition under which `IdQuery.evalBgpM` calls it: both tables
  have the sort variable `v`), denotes `IdJoin.idJoin` of their rows, row
  for row in the same order (with `Qlvr.MergeTheorems.mergeGo_spec`, L5a).
* `hashPairs_spec`: `OptJoin.hashPairs` gives the pairs of rows whose shared
  columns hold the same ids, in the order of `innerSpec`.
* `innerPairs_spec`: so does `OptJoin.innerPairs` on either path, when a
  table's sort variable says the truth (`SortOk`).
* `gatherOpt_holds`: `OptJoin.gatherOpt` holds the words of the rows it
  names and `unbound` for `none`.
* `leftOuterJoin_rows` (L5g″): `OptJoin.leftOuterJoin` of two well-formed
  tables whose shared columns hold no `unbound` id (`SharedBound`; the
  tables `IdQuery.flattenOptional` admits), with `SortOk` on both, denotes
  `OptJoin.idLeftJoin` of their rows (SPARQL 1.1 LeftJoin with condition
  `true`), row for row in the same order.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TableTheorems

namespace L4Factoidal.Storage.Sbm11.TableTheorems

open L4Factoidal.Qlvr (Table gather joinVars sharedCols joinOutput mergeGo mergeSpec)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound innerSpec ljSpec
  outerPairs gatherOpt hashPairs innerPairs leftOuterJoin idLeftJoin)

/-! ## Shared columns bound -/

/-- The shared columns of `l` and `r` hold no `unbound` id. -/
def SharedBound (l r : Table) : Prop :=
  ∀ p q, (p, q) ∈ sharedCols l r → (∀ i, i < l.rows → l.at p i ≠ unbound) ∧ (∀ j, j < r.rows → r.at q j ≠ unbound)

theorem sharedBound_of (l r : Table) (hl : NoUnbound l) (hr : NoUnbound r) : SharedBound l r := by
  intro p q hpq
  obtain ⟨hp, hq⟩ := mem_sharedCols.mp hpq
  exact ⟨fun i hi => hl p i hp hi, fun j hj => hr q j (idx_some hq).1 hj⟩

/-- When the shared columns hold no `unbound` id, two rows are compatible
    exactly when their shared columns hold the same ids. -/
theorem compatible_iff_shEq (l r : Table) (hr : r.vars.toList.Nodup) (hb : SharedBound l r)
    (i j : Nat) (hi : i < l.rows) (hj : j < r.rows) :
    idCompatible (l.idRow i) (r.idRow j) = shEq l r i j := by
  apply Bool.eq_iff_iff.mpr
  rw [shEq_iff, idCompatible_rows l r hr]
  constructor
  · intro h p q hpq
    obtain ⟨hp, hq⟩ := mem_sharedCols.mp hpq
    exact h p hp ((hb p q hpq).1 i hi) (r.at q j) (lookupAt_some.mpr ⟨q, hq, (hb p q hpq).2 j hj, rfl⟩)
  · intro h c hc _ y hy
    obtain ⟨q, hq, _, e⟩ := lookupAt_some.mp hy
    rw [← e]; exact h c q (mem_sharedCols.mpr ⟨hc, hq⟩)

/-- Every row index of `idJoin` over the rows of two tables. -/
theorem idJoin_rows_shEq (l r : Table) (hr : r.vars.toList.Nodup) (hb : SharedBound l r) :
    L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows =
      (innerSpec l.rows r.rows (shEq l r)).map fun p => idMerge (l.idRow p.1) (r.idRow p.2) := by
  rw [idJoin_rows, innerSpec_congr l.rows r.rows _ (shEq l r)
    (fun i j hi hj => compatible_iff_shEq l r hr hb i j hi hj)]

/-! ## `Qlvr.mergeJoin` -/

/-- The merge's test is `shEq` when `(lc, rc)` is the pair of columns of the
    merge variable. -/
theorem merge_cand (l r : Table) (v : String) (lc rc : Nat) (hlv : l.idx v = some lc)
    (hrv : r.idx v = some rc) (x y : Nat) :
    (l.at lc x == r.at rc y && ((sharedCols l r).filter fun pq => pq.1 != lc).all
        fun pq => l.at pq.1 x == r.at pq.2 y) = shEq l r x y := by
  obtain ⟨hlc, hlcv⟩ := idx_some hlv
  have hmem : (lc, rc) ∈ sharedCols l r := mem_sharedCols.mpr ⟨hlc, by rw [hlcv]; exact hrv⟩
  apply Bool.eq_iff_iff.mpr
  rw [shEq_iff, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  simp only [beq_iff_eq, Array.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · intro ⟨h1, h2⟩ a b hab
    by_cases ha : a = lc
    · subst ha
      obtain ⟨_, hb⟩ := mem_sharedCols.mp hab
      rw [hlcv, hrv] at hb
      cases hb; exact h1
    · exact h2 (a, b) ⟨hab, ha⟩
  · intro h
    exact ⟨h lc rc hmem, fun pq ⟨hpq, _⟩ => h pq.1 pq.2 hpq⟩

/-- **L5a′.** `Qlvr.mergeJoin l r v` of two well-formed tables with no
    `unbound` id, both in non-decreasing order of the ids of `v`, denotes
    SPARQL 1.1 Join of their rows (`IdJoin.idJoin`), row for row in the
    same order. -/
theorem mergeJoin_rows (l r : Table) (v : String) (hl : l.WF) (hr : r.WF) (hb : SharedBound l r)
    (lc rc : Nat) (hlv : l.idx v = some lc) (hrv : r.idx v = some rc)
    (hA : ∀ x y, x ≤ y → y < l.rows → (l.at lc x).toNat ≤ (l.at lc y).toNat)
    (hB : ∀ x y, x ≤ y → y < r.rows → (r.at rc x).toNat ≤ (r.at rc y).toNat) :
    (L4Factoidal.Qlvr.mergeJoin l r v).WF ∧
      RowsEq (L4Factoidal.Qlvr.mergeJoin l r v).idRows
        (L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows) := by
  rw [L4Factoidal.Qlvr.mergeJoin_eq, hlv, hrv]
  simp only [Option.getD_some]
  let ok : Nat → Nat → Bool := fun x y => ((sharedCols l r).filter fun pq => pq.1 != lc).all
    fun pq => l.at pq.1 x == r.at pq.2 y
  obtain ⟨h1, h2⟩ := L4Factoidal.Qlvr.mergeGo_spec (l.at lc) (r.at rc) ok l.rows r.rows hA hB
    (l.rows + r.rows + 1) 0 0 #[] #[] (by omega)
  have hs : mergeSpec (l.at lc) (r.at rc) ok l.rows r.rows 0 0 = innerSpec l.rows r.rows (shEq l r) := by
    rw [innerSpec_eq]
    unfold mergeSpec
    simp only [Nat.sub_zero]
    congr 1; funext x; congr 1
    apply List.filter_congr
    intro y _
    exact merge_cand l r v lc rc hlv hrv x y
  rw [hs, List.nil_append] at h1 h2
  have := joinOutput_rows l r hl hr _ _ _ h1 h2 (fun p hp => by
    obtain ⟨i, j⟩ := p
    obtain ⟨hi, hj, hc⟩ := mem_innerSpec.mp hp
    exact ⟨hi, hj, (shEq_iff l r i j).mp hc⟩) (some v)
  rw [idJoin_rows_shEq l r hr.nodup hb]
  exact this

#print axioms mergeJoin_rows

/-! ## `OptJoin.hashPairs` -/

/-- `OptJoin.hashPairs` on the shared columns: the pairs of rows whose shared
    columns hold the same ids, in the order of `innerSpec`. -/
theorem hashPairs_spec (l r : Table) :
    (hashPairs l r (sharedCols l r)).1.toList = (innerSpec l.rows r.rows (shEq l r)).map Prod.fst ∧
      (hashPairs l r (sharedCols l r)).2.toList = (innerSpec l.rows r.rows (shEq l r)).map Prod.snd := by
  by_cases h1 : (sharedCols l r).size = 1
  · obtain ⟨li, ri, he, e1, e2⟩ := hash_branch
      (fun j => r.at ((sharedCols l r)[0]'(by omega)).2 j)
      (fun i => l.at ((sharedCols l r)[0]'(by omega)).1 i)
      (fun j x => match x with
        | some a => some (a.push j)
        | none => some #[j]) (by intro j o; cases o <;> rfl) r.rows l.rows (fun a b => (a, b))
    have e : hashPairs l r (sharedCols l r) = (li, ri) := by
      unfold hashPairs
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
        Nat.add_sub_cancel, Nat.div_one]
      rw [dif_pos h1]
      exact he
    rw [e]
    refine ⟨?_, ?_⟩
    all_goals
      rw [innerSpec_eq]
      first | rw [e1] | rw [e2]
      congr 2
      funext i
      congr 1
      apply List.filter_congr
      intro j _
      rw [shEq_single l r h1]
  · obtain ⟨li, ri, he, e1, e2⟩ := hash_branch
      (fun j => ((sharedCols l r).map fun x => r.at x.2 j).toList)
      (fun i => ((sharedCols l r).map fun x => l.at x.1 i).toList)
      (fun j x => match x with
        | some a => some (a.push j)
        | none => some #[j]) (by intro j o; cases o <;> rfl) r.rows l.rows (fun a b => (a, b))
    have e : hashPairs l r (sharedCols l r) = (li, ri) := by
      unfold hashPairs
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
        Nat.add_sub_cancel, Nat.div_one]
      rw [dif_neg h1]
      exact he
    rw [e]
    refine ⟨?_, ?_⟩
    all_goals
      rw [innerSpec_eq]
      first | rw [e1] | rw [e2]
      congr 2
      funext i
      congr 1
      apply List.filter_congr
      intro j _
      rw [shEq_list l r]

/-! ## `OptJoin.innerPairs` -/

/-- A table's sort variable says the truth: its column is in non-decreasing
    order of the ids. -/
def SortOk (t : Table) : Prop :=
  ∀ v c, t.sortVar = some v → t.idx v = some c → ∀ x y, x ≤ y → y < t.rows → (t.at c x).toNat ≤ (t.at c y).toNat

/-- `OptJoin.innerPairs` on either path gives the pairs of rows whose shared
    columns hold the same ids, in the order of `innerSpec`. -/
theorem innerPairs_spec (l r : Table) (hsl : SortOk l) (hsr : SortOk r) :
    (innerPairs l r).1.toList = (innerSpec l.rows r.rows (shEq l r)).map Prod.fst ∧
      (innerPairs l r).2.1.toList = (innerSpec l.rows r.rows (shEq l r)).map Prod.snd := by
  have hh := hashPairs_spec l r
  unfold innerPairs
  cases hs : l.sortVar with
  | none => exact hh
  | some v =>
    simp only
    cases hlv : l.idx v with
    | none => exact hh
    | some lc =>
      cases hrv : r.idx v with
      | none => exact hh
      | some rc =>
        simp only
        by_cases hrs : (r.sortVar == some v) = true
        · rw [if_pos hrs]
          have hrs' : r.sortVar = some v := by simpa using hrs
          let ok : Nat → Nat → Bool := fun x y => ((sharedCols l r).filter fun pq => pq.1 != lc).all
            fun pq => l.at pq.1 x == r.at pq.2 y
          obtain ⟨h1, h2⟩ := L4Factoidal.Qlvr.mergeGo_spec (l.at lc) (r.at rc) ok l.rows r.rows
            (hsl v lc hs hlv) (hsr v rc hrs' hrv) (l.rows + r.rows + 1) 0 0 #[] #[] (by omega)
          have hsp : mergeSpec (l.at lc) (r.at rc) ok l.rows r.rows 0 0 = innerSpec l.rows r.rows (shEq l r) := by
            rw [innerSpec_eq]
            unfold mergeSpec
            simp only [Nat.sub_zero]
            congr 1; funext x; congr 1
            apply List.filter_congr
            intro y _
            exact merge_cand l r v lc rc hlv hrv x y
          rw [hsp, List.nil_append] at h1 h2
          exact ⟨h1, h2⟩
        · rw [if_neg hrs]; exact hh

/-! ## `OptJoin.gatherOpt` -/

/-- The word of an optional row: `unbound` for `none`. -/
def optWord (src : ByteArray) : Option Nat → UInt64
  | some j => word64 src (8 * j)
  | none => unbound

/-- `gatherOpt src idx` holds the words of the rows `idx` names, `unbound`
    for `none`, in order. -/
theorem gatherOpt_holds (src : ByteArray) (idx : Array (Option Nat))
    (h : ∀ j, some j ∈ idx.toList → 8 * (j + 1) ≤ src.size) :
    ColHolds (gatherOpt src idx) (idx.toList.map (optWord src)) := by
  unfold gatherOpt
  simp only [_root_.Id.run]
  rw [← Array.forIn_toList]
  generalize hG : forIn (m := _root_.Id) idx.toList (ByteArray.emptyWithCapacity (8 * idx.size)) _ = G
  have := forIn_list_inv idx.toList (fun k (out : ByteArray) => ColHolds out ((idx.toList.take k).map (optWord src)))
    hG (ColHolds.nil _ rfl) (by
      intro k out hk hout
      have htk : (idx.toList.take (k + 1)).map (optWord src) =
          (idx.toList.take k).map (optWord src) ++ [optWord src idx.toList[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; simp
      cases hc : idx.toList[k] with
      | none =>
        refine ⟨L4Factoidal.Qlvr.Side.put64 out unbound, rfl, ?_⟩
        rw [htk, hc]; exact hout.put64 unbound
      | some j =>
        refine ⟨src.copySlice (8 * j) out out.size 8 false, rfl, ?_⟩
        rw [htk, hc]
        have hj := h j (by rw [← hc]; exact List.getElem_mem hk)
        have hx := ColHolds.extract src j 1 (by omega)
        simp only [List.range'_one, List.map_cons, List.map_nil, Nat.mul_one] at hx
        exact hout.append hx (copySlice_data src out (8 * j) 8))
  rw [List.take_length] at this
  exact this

/-! ## `OptJoin.leftOuterJoin` -/

/-- The id of right column `q` in an optional right row. -/
def optVal (r : Table) (q : Nat) : Option Nat → UInt64
  | some j => r.at q j
  | none => unbound

/-- The output of the left outer join from its index arrays: well formed,
    and row `k` takes the left variables from row `oi[k]` of `l` and the
    others from row `oj[k]` of `r`, or `unbound` when `oj[k]` is `none`. -/
theorem outerOutput_spec (l r : Table) (hl : l.WF) (hr : r.WF) (oi : Array Nat) (oj : Array (Option Nat))
    (hsz : oi.size = oj.size) (hoi : ∀ i ∈ oi.toList, i < l.rows) (hoj : ∀ j, some j ∈ oj.toList → j < r.rows)
    (sv : Option String) :
    let T : Table := (Table.mk (joinVars l r).1 (l.cols.map (fun x => gather x oi) ++ ((joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj)) oi.size sv)
    T.WF ∧ ∀ k, k < oi.size → ∀ v, T.lookupAt k v =
      match l.idx v with
      | some c => nz (l.at c oi[k]!)
      | none => match r.idx v with
        | some q => nz (optVal r q oj[k]!)
        | none => none := by
  intro T
  have hex := joinVars_extra l r
  have hvT : T.vars.toList = l.vars.toList ++ (joinVars l r).2.toList.map (fun q => r.vars[q]!) :=
    joinVars_vars l r
  have hlc : l.cols.size = l.vars.size := hl.cols_size
  have hext : ∀ m, m < (joinVars l r).2.size → (joinVars l r).2[m]! < r.vars.size := fun m hm =>
    ((mem_extra hex).mp (mem_of_get hm)).1
  have hcolL : ∀ c, c < l.vars.size → T.cols[c]! = gather l.cols[c]! oi := by
    intro c hc
    show (l.cols.map (fun x => gather x oi) ++ (joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj)[c]! = _
    rw [getElem!_pos _ c (by simp; omega), Array.getElem_append_left (by simp; omega)]
    simp [getElem!_pos l.cols c (by omega)]
  have hcolR : ∀ m, m < (joinVars l r).2.size →
      T.cols[l.vars.size + m]! = gatherOpt r.cols[(joinVars l r).2[m]!]! oj := by
    intro m hm
    show (l.cols.map (fun x => gather x oi) ++ (joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj)[l.vars.size + m]! = _
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_append_right (by simp; omega)]
    simp only [Array.getElem_map, Array.size_map, hlc, Nat.add_sub_cancel_left]
    rw [getElem!_pos (joinVars l r).2 m hm]
  have hopt : ∀ q, q < r.vars.size → ColHolds (gatherOpt r.cols[q]! oj) (oj.toList.map (optWord r.cols[q]!)) := by
    intro q hq
    have hq' : q < r.cols.size := by rw [hr.cols_size]; exact hq
    apply gatherOpt_holds
    intro j hj
    rw [getElem!_pos r.cols q hq', hr.col_bytes q hq']
    have := hoj j hj; omega
  have hTs : T.cols.size = l.vars.size + (joinVars l r).2.size := by
    show (l.cols.map (fun x => gather x oi) ++ (joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj).size = _
    simp [hlc]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hTs, ← Array.length_toList (xs := T.vars), hvT]; simp
  · intro c hc
    have hc' : c < l.vars.size + (joinVars l r).2.size := by rw [← hTs]; exact hc
    rw [← getElem!_pos T.cols c hc]
    show T.cols[c]!.size = 8 * oi.size
    by_cases hcl : c < l.vars.size
    · rw [hcolL c hcl, gather_size l hl c hcl oi hoi]
    · have := hcolR (c - l.vars.size) (by omega)
      rw [show l.vars.size + (c - l.vars.size) = c by omega] at this
      rw [this, (hopt _ (hext _ (by omega))).1]; simp [hsz]
  · rw [hvT]; exact out_nodup l r _ hl.nodup hr.nodup hex
  · intro k hk v
    apply out_lookup_gen l r T _ k (fun c => l.at c oi[k]!) (fun q => optVal r q oj[k]!) hl.nodup hr.nodup hvT hex
    · intro c hc
      show word64 T.cols[c]! (8 * k) = _
      rw [hcolL c hc, gather_word l hl c hc oi hoi k hk]
    · intro m hm
      show word64 T.cols[l.vars.size + m]! (8 * k) = _
      rw [hcolR m hm, (hopt _ (hext m hm)).word (by simp; omega)]
      simp only [List.getElem_map, Array.getElem_toList]
      rw [← getElem!_pos oj k (by omega)]
      cases oj[k]! <;> rfl

theorem ljSpec_congr (nl nr : Nat) (c1 c2 : Nat → Nat → Bool)
    (h : ∀ i j, i < nl → j < nr → c1 i j = c2 i j) : ljSpec nl nr c1 = ljSpec nl nr c2 := by
  unfold ljSpec L4Factoidal.Storage.Sbm11.OptJoin.ljFrom
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x hx
  congr 1
  unfold L4Factoidal.Storage.Sbm11.OptJoin.rowsOf
  apply List.filter_congr
  intro y hy
  simp at hx hy
  exact h x y (by omega) hy

/-- The row of the left outer join for an output pair. -/
def ljRowOf (l r : Table) : Nat × Option Nat → IdRow
  | (i, none) => l.idRow i
  | (i, some j) => idMerge (l.idRow i) (r.idRow j)

/-- `idLeftJoin` of the rows of two tables over row indices. -/
theorem idLeftJoin_rows (l r : Table) (hr : r.vars.toList.Nodup) (hb : SharedBound l r) :
    idLeftJoin l.idRows r.idRows = (ljSpec l.rows r.rows (shEq l r)).map (ljRowOf l r) := by
  rw [L4Factoidal.Storage.Sbm11.OptJoin.idLeftJoin_eq_ljSpec, idRows_length, idRows_length,
    ljSpec_congr l.rows r.rows _ (shEq l r) (fun i j hi hj => by
      rw [idRows_get l i hi, idRows_get r j hj]; exact compatible_iff_shEq l r hr hb i j hi hj)]
  apply List.map_congr_left
  intro p hp
  obtain ⟨i, o⟩ := p
  have hi : i < l.rows := (L4Factoidal.Storage.Sbm11.OptJoin.mem_ljSpec_iff.mp hp).1
  cases o with
  | none => simp only [ljRowOf]; rw [idRows_get l i hi]
  | some j =>
    have hj := (L4Factoidal.Storage.Sbm11.OptJoin.mem_ljSpec_some.mp hp).2.1
    simp only [ljRowOf]; rw [idRows_get l i hi, idRows_get r j hj]

/-- **L5g″.** `OptJoin.leftOuterJoin` of two well-formed tables whose shared
    columns hold no `unbound` id, each in the order its sort variable says,
    denotes SPARQL 1.1 LeftJoin(Ω1, Ω2, true) of their rows
    (`OptJoin.idLeftJoin`), row for row in the same order. -/
theorem leftOuterJoin_rows (l r : Table) (hl : l.WF) (hr : r.WF) (hb : SharedBound l r)
    (hsl : SortOk l) (hsr : SortOk r) :
    (leftOuterJoin l r).1.WF ∧ RowsEq (leftOuterJoin l r).1.idRows (idLeftJoin l.idRows r.idRows) := by
  obtain ⟨hi1, hi2⟩ := innerPairs_spec l r hsl hsr
  let S := ljSpec l.rows r.rows (shEq l r)
  let oi := (outerPairs l.rows (innerPairs l r).1 (innerPairs l r).2.1).1
  let oj := (outerPairs l.rows (innerPairs l r).1 (innerPairs l r).2.1).2
  obtain ⟨ho1, ho2⟩ := L4Factoidal.Storage.Sbm11.OptJoin.outerPairs_eq l.rows r.rows (shEq l r) _ _ hi1 hi2
  have hoi : oi.toList = S.map Prod.fst := ho1
  have hoj : oj.toList = S.map Prod.snd := ho2
  have hsz1 : oi.size = S.length := by rw [← Array.length_toList, hoi, List.length_map]
  have hsz2 : oj.size = S.length := by rw [← Array.length_toList, hoj, List.length_map]
  have hmemS : ∀ p ∈ S, p.1 < l.rows ∧ ∀ j, p.2 = some j → j < r.rows ∧ shEq l r p.1 j = true := by
    intro p hp
    obtain ⟨i, o⟩ := p
    refine ⟨(L4Factoidal.Storage.Sbm11.OptJoin.mem_ljSpec_iff.mp hp).1, fun j hj => ?_⟩
    simp only at hj; subst hj
    have := L4Factoidal.Storage.Sbm11.OptJoin.mem_ljSpec_some.mp hp
    exact ⟨this.2.1, this.2.2⟩
  have hoiR : ∀ i ∈ oi.toList, i < l.rows := by
    intro i hi; rw [hoi] at hi
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hi; rw [← e]; exact (hmemS p hp).1
  have hojR : ∀ j, some j ∈ oj.toList → j < r.rows := by
    intro j hj; rw [hoj] at hj
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hj; exact ((hmemS p hp).2 j e).1
  have hT : (leftOuterJoin l r).1 = (Table.mk (joinVars l r).1 (l.cols.map (fun x => gather x oi) ++ ((joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj)) oi.size l.sortVar) := rfl
  obtain ⟨hWF, hlk⟩ := outerOutput_spec l r hl hr oi oj (by omega) hoiR hojR l.sortVar
  rw [hT]
  refine ⟨hWF, ?_⟩
  rw [idLeftJoin_rows l r hr.nodup hb]
  refine ⟨by rw [idRows_length, List.length_map, hsz1], fun k h1 h2 => ?_⟩
  have hk : k < S.length := by simpa using h2
  have hrow : (((Table.mk (joinVars l r).1 (l.cols.map (fun x => gather x oi) ++ ((joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj)) oi.size l.sortVar) : Table)).idRows[k] =
      ((Table.mk (joinVars l r).1 (l.cols.map (fun x => gather x oi) ++ ((joinVars l r).2.map fun k => gatherOpt r.cols[k]! oj)) oi.size l.sortVar) : Table).idRow k := by simp [Table.idRows]
  rw [hrow, List.getElem_map]
  have ek1 : oi[k]! = S[k].1 := by rw [arr_get oi k (by omega)]; simp only [hoi, List.getElem_map]
  have ek2 : oj[k]! = S[k].2 := by rw [arr_get oj k (by omega)]; simp only [hoj, List.getElem_map]
  obtain ⟨hiS, hjS⟩ := hmemS S[k] (List.getElem_mem hk)
  intro v
  rw [lookup_idRow _ hWF.nodup, hlk k (by omega) v, ek1, ek2]
  generalize S[k] = p at hiS hjS
  obtain ⟨i, o⟩ := p
  cases o with
  | none =>
    simp only [ljRowOf, optVal]
    rw [lookup_idRow l hl.nodup, lookupAt_eq l]
    cases l.idx v with
    | some c => rfl
    | none =>
      simp only
      cases r.idx v <;> rfl
  | some j =>
    obtain ⟨hj, hc⟩ := hjS j rfl
    simp only [ljRowOf, optVal]
    rw [lookup_idMerge, lookup_idRow l hl.nodup, lookup_idRow r hr.nodup, lookupAt_eq l, lookupAt_eq r]
    have hsh := (shEq_iff l r i j).mp hc
    cases hlv : l.idx v with
    | none => rfl
    | some c =>
      simp only
      unfold nz
      by_cases h0 : l.at c i = unbound
      · simp only [h0, beq_self_eq_true, if_true, Option.none_or]
        cases hrv : r.idx v with
        | none => rfl
        | some q =>
          obtain ⟨hcl, hcv⟩ := idx_some hlv
          have := hsh c q (mem_sharedCols.mpr ⟨hcl, by rw [hcv]; exact hrv⟩)
          simp only
          rw [← this, h0]; simp
      · have : (l.at c i == unbound) = false := by simpa using h0
        simp [this]

#print axioms hashPairs_spec
#print axioms innerPairs_spec
#print axioms gatherOpt_holds
#print axioms leftOuterJoin_rows

end L4Factoidal.Storage.Sbm11.TableTheorems
