/-
L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems — the `Table` of
`IdGroup.leftJoinCondM` for the condition `true` (OPTIONAL with no FILTER
inside; the parser's `LeftJoin(P1, P2, true)`), against the list operator
`IdGroup.idLeftJoinC` (https://github.com/danbri/factoidal/issues/776,
lemma L4p of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`leftJoinCondM` builds the compatible pairs (`IdJoin.joinPairs`, so the
merged table is `IdJoin.joinIds`), then per left row its pairs or the left
row alone (`IdGroup.ljSource`), then the columns (`IdGroup.ljColumns`).

* `ljSource_spec`: for index arrays `li` that list each left row `i`
  `cnt i` times in order, and every pair alive, the entries are, per left
  row, its pairs (from the offset `off` of the row) or `(none, i)`.
* `ljColumns_spec`, `ljTable_rows`: the table's row of `(some k, i)` is row
  `k` of the merged table, and of `(none, i)` row `i` of the left table.
* `leftJoinTrue_rows`: `leftJoinCondM` with the condition `true` returns a
  well-formed table whose rows are, row for row, the same solution mappings
  as `idLeftJoinC (fun _ => true)` of the rows of its inputs.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ExecLeafTheorems

namespace L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems

open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq RowsEq ColHolds forIn_inv forIn_inv' forIn_range_inv forIn_list_inv
  id_bind)

/-! ## Blocks of a list indexed by a range -/

def off {γ : Type} (B : Nat → List γ) (i : Nat) : Nat := ((List.range i).map fun i' => (B i').length).sum

theorem flatMap_split {γ : Type} (B : Nat → List γ) (n i : Nat) (hi : i < n) :
    (List.range n).flatMap B =
      (List.range i).flatMap B ++ B i ++ (List.range' (i + 1) (n - (i + 1))).flatMap B := by
  have : List.range n = List.range i ++ [i] ++ List.range' (i + 1) (n - (i + 1)) := by
    rw [List.range_eq_range', List.range_eq_range', List.append_assoc, List.singleton_append, ← List.range'_succ,
      show List.range' i (n - (i + 1) + 1) = List.range' (0 + i) (n - (i + 1) + 1) by rw [Nat.zero_add],
      List.range'_append_1]
    congr 1; omega
  rw [this, List.flatMap_append, List.flatMap_append]
  simp

theorem length_flatMap_range {γ : Type} (B : Nat → List γ) (i : Nat) :
    ((List.range i).flatMap B).length = off B i := by
  simp [off, List.length_flatMap]

theorem flatMap_get {γ : Type} (B : Nat → List γ) (n i t : Nat) (hi : i < n) (ht : t < (B i).length) :
    ∃ h, ((List.range n).flatMap B)[off B i + t]'h = (B i)[t] := by
  have hl := length_flatMap_range B i
  have e := flatMap_split B n i hi
  refine ⟨by rw [e]; simp only [List.length_append]; omega, ?_⟩
  simp only [e]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [hl, Nat.add_sub_cancel_left]



/-- The rows of LeftJoin per left row: the pairs `k` of row `i` (from the
    offset of `i`), else the left row alone. -/
def ljBlock (cnt : Nat → Nat) (i : Nat) : List (Option Nat × Nat) :=
  if cnt i = 0 then [(none, i)] else (List.range' (off (fun i => List.replicate (cnt i) i) i) (cnt i)).map
    fun k => (some k, i)

theorem off_succ {γ : Type} (B : Nat → List γ) (i : Nat) : off B (i + 1) = off B i + (B i).length := by
  simp [off, List.range_succ]

theorem off_mono {γ : Type} (B : Nat → List γ) : ∀ {i j : Nat}, i ≤ j → off B i ≤ off B j := by
  intro i j h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [off_succ]; omega

theorem rep_get (cnt : Nat → Nat) (nl i t : Nat) (hi : i < nl) (ht : t < cnt i) (li : Array Nat)
    (hli : li.toList = (List.range nl).flatMap fun i => List.replicate (cnt i) i) :
    off (fun i => List.replicate (cnt i) i) i + t < li.size ∧ li[off (fun i => List.replicate (cnt i) i) i + t]! = i := by
  obtain ⟨h, e⟩ := flatMap_get (fun i => List.replicate (cnt i) i) nl i t hi (by simpa using ht)
  have hs : off (fun i => List.replicate (cnt i) i) i + t < li.size := by
    rw [← Array.length_toList, hli]; exact h
  refine ⟨hs, ?_⟩
  rw [getElem!_pos li _ hs, ← Array.getElem_toList]
  simp only [hli, e, List.getElem_replicate]

theorem rep_next (cnt : Nat → Nat) (nl i : Nat) (hi : i < nl) (li : Array Nat)
    (hli : li.toList = (List.range nl).flatMap fun i => List.replicate (cnt i) i)
    (hk : off (fun i => List.replicate (cnt i) i) i + cnt i < li.size) :
    li[off (fun i => List.replicate (cnt i) i) i + cnt i]! ≠ i := by
  have e := flatMap_split (fun i => List.replicate (cnt i) i) nl i hi
  have hl := length_flatMap_range (fun i => List.replicate (cnt i) i) i
  generalize hL1 : (List.range i).flatMap (fun i => List.replicate (cnt i) i) = L1 at e hl
  generalize hL3 : (List.range' (i + 1) (nl - (i + 1))).flatMap (fun i => List.replicate (cnt i) i) = L3 at e
  have hsz : li.size = L1.length + cnt i + L3.length := by
    rw [← Array.length_toList, hli, e]; simp only [List.length_append, List.length_replicate]
  have h3 : off (fun i => List.replicate (cnt i) i) i + cnt i - (L1 ++ List.replicate (cnt i) i).length < L3.length := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [getElem!_pos li _ hk, ← Array.getElem_toList]
  simp only [hli, e]
  rw [List.getElem_append_right (by simp only [List.length_append, List.length_replicate]; omega)]
  have hm3 : ∀ x ∈ L3, i + 1 ≤ x := by
    rw [← hL3]
    intro x hx
    rw [List.mem_flatMap] at hx
    obtain ⟨i', hi', hm⟩ := hx
    rw [List.mem_range'] at hi'
    have := (List.mem_replicate.mp hm).2
    omega
  intro h
  have := hm3 _ (List.getElem_mem h3)
  rw [h] at this
  omega

theorem ljSource_spec (nl : Nat) (cnt : Nat → Nat) (li : Array Nat) (alive : Array Bool)
    (hli : li.toList = (List.range nl).flatMap fun i => List.replicate (cnt i) i)
    (halive : ∀ k, k < li.size → alive[k]! = true) :
    (IdGroup.ljSource nl li alive).toList = (List.range nl).flatMap (ljBlock cnt) := by
  let B : Nat → List Nat := fun i => List.replicate (cnt i) i
  have hsz : li.size = off B nl := by
    rw [← Array.length_toList, hli]; exact length_flatMap_range B nl
  unfold IdGroup.ljSource
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 nl) ((Array.mkEmpty (nl + li.size) : Array (Option Nat × Nat)), 0) _ = F
  have := forIn_range_inv nl (fun m (s : Array (Option Nat × Nat) × Nat) =>
      s.2 = off B m ∧ s.1.toList = (List.range m).flatMap (ljBlock cnt)) hF ⟨rfl, by simp⟩ (by
    intro m s hm ⟨h1, h2⟩
    have hle : off B m + cnt m ≤ li.size := by
      rw [hsz]; have := off_mono B (show m + 1 ≤ nl by omega); rw [off_succ] at this; simpa [B] using this
    rw [id_bind]
    generalize hI : forIn (m := _root_.Id) (List.range' 0 li.size) (s.1, s.2, false) _ = I
    have hinv := forIn_inv' (fun a (st : Array (Option Nat × Nat) × Nat × Bool) => a ≤ cnt m ∧ st.2.1 = off B m + a ∧
        st.1.toList = s.1.toList ++ (List.range' (off B m) a).map (fun k => (some k, m)) ∧ st.2.2 = decide (0 < a))
      (fun st => st.2.1 = off B m + cnt m ∧
        st.1.toList = s.1.toList ++ (List.range' (off B m) (cnt m)).map (fun k => (some k, m)) ∧
        st.2.2 = decide (0 < cnt m)) hI ⟨Nat.zero_le _, by simp [h1], by simp, rfl⟩
      (by
        intro a st _ _ ⟨ha1, ha2, ha3, ha4⟩
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
            have hal : alive[st.2.1]! = true := halive _ (by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1)
            simp only [hc, hal, if_true] at hst
            cases hst
            refine ⟨by omega, by simp [ha2]; omega, ?_, by simp⟩
            simp only [Array.toList_push, ha3, List.append_assoc]
            rw [List.range'_concat]
            simp [ha2]
          · simp only [hc, Bool.false_eq_true, if_false] at hst
            cases hst
        · intro st' hst
          by_cases hc : (decide (st.2.1 < li.size) && li[st.2.1]! == m) = true
          · have hal : alive[st.2.1]! = true := halive _ (by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1)
            simp only [hc, hal, if_true] at hst
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
        I.run.1.toList = s.1.toList ++ (List.range' (off B m) (cnt m)).map (fun k => (some k, m)) ∧
        I.run.2.2 = decide (0 < cnt m) := by
      rcases hinv with ⟨ha1, ha2, ha3, ha4⟩ | hq
      · have hae : li.size = cnt m := by simp at ha1; omega
        simp only [Nat.zero_add] at ha1 ha2 ha3 ha4
        rw [hae] at ha2 ha3 ha4
        exact ⟨ha2, ha3, ha4⟩
      · exact hq
    obtain ⟨q1, q2, q3⟩ := hQ
    by_cases h0 : cnt m = 0
    · refine ⟨(I.run.1.push (none, m), I.run.2.1), by simp [q3, h0], ?_, ?_⟩
      · simp only [q1, off_succ, B, List.length_replicate]
      · simp only [Array.toList_push, q2, h2, List.range_succ, List.flatMap_append, h0, List.range'_zero,
          List.map_nil, List.append_nil, ljBlock, if_true, List.flatMap_singleton]
    · have hpos : 0 < cnt m := Nat.pos_of_ne_zero h0
      refine ⟨(I.run.1, I.run.2.1), by simp [q3, hpos], ?_, ?_⟩
      · simp only [q1, off_succ, B, List.length_replicate]
      · simp only [q2, h2, List.range_succ, List.flatMap_append, ljBlock, h0, if_false, List.flatMap_singleton]
        rfl)
  exact this.2


/-! ## The columns -/

/-- The id of column `c` for an entry of `ljSource`. -/
def ljVal (merged l : Table) (c : Nat) (p : Option Nat × Nat) : UInt64 :=
  match p.1 with
  | some k => merged.at c k
  | none => if c < l.vars.size then l.at c p.2 else unbound

theorem put64_list (f : Option Nat × Nat → UInt64) (xs : List (Option Nat × Nat)) (n : Nat)
    {F : _root_.Id ByteArray}
    (hF : forIn xs (ByteArray.emptyWithCapacity n) (fun x (s : ByteArray) =>
      pure (ForInStep.yield (L4Factoidal.Qlvr.Side.put64 s (f x)))) = F) :
    ColHolds F.run (xs.map f) := by
  have := forIn_list_inv xs (fun k (b : ByteArray) => ColHolds b ((xs.take k).map f)) hF
    (by simpa using TableTheorems.ColHolds.nil _ rfl) (by
      intro k b hk h
      refine ⟨_, rfl, ?_⟩
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
      exact h.put64 _)
  rw [List.take_length] at this
  exact this

theorem ljColumns_spec (merged l : Table) (src : Array (Option Nat × Nat)) :
    (IdGroup.ljColumns merged l src).size = merged.vars.size ∧
      ∀ c, c < merged.vars.size →
        ColHolds (IdGroup.ljColumns merged l src)[c]! (src.toList.map (ljVal merged l c)) := by
  unfold IdGroup.ljColumns
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hC : forIn (m := _root_.Id) (List.range' 0 merged.vars.size)
    (Array.mkEmpty merged.vars.size : Array ByteArray) _ = C
  have := forIn_range_inv merged.vars.size (fun m (cs : Array ByteArray) => cs.size = m ∧
      ∀ c, c < m → ColHolds cs[c]! (src.toList.map (ljVal merged l c))) hC
    ⟨rfl, fun c hc => absurd hc (by omega)⟩ (by
      intro c cs _ ⟨h1, h2⟩
      rw [id_bind, ← Array.forIn_toList]
      generalize hO : forIn (m := _root_.Id) src.toList (ByteArray.emptyWithCapacity (8 * src.size)) _ = O
      have hcol := put64_list (ljVal merged l c) src.toList (8 * src.size) (F := O) (by
        rw [← hO]; rfl)
      refine ⟨cs.push O.run, rfl, by simp [h1], fun c' hc' => ?_⟩
      rw [getElem!_pos _ c' (by simp; omega), Array.getElem_push]
      by_cases e : c' < cs.size
      · rw [dif_pos e, ← getElem!_pos cs c' e]; exact h2 c' (by omega)
      · rw [dif_neg e]; have : c' = c := by omega
        subst this; exact hcol)
  exact this

/-! ## The table -/

/-- The table `leftJoinCondM` returns for `src`. -/
def ljTable (merged l : Table) (src : Array (Option Nat × Nat)) : Table :=
  { vars := merged.vars, cols := IdGroup.ljColumns merged l src, rows := src.size }

/-- The row of an entry of `ljSource`: a merged row, or the left row. -/
def ljRow (merged l : Table) : Option Nat × Nat → IdRow
  | (some k, _) => merged.idRow k
  | (none, i) => l.idRow i

theorem ljTable_at (merged l : Table) (src : Array (Option Nat × Nat)) (c t : Nat) (hc : c < merged.vars.size)
    (ht : t < src.size) : (ljTable merged l src).at c t = ljVal merged l c src[t] := by
  show word64 (IdGroup.ljColumns merged l src)[c]! (8 * t) = _
  rw [((ljColumns_spec merged l src).2 c hc).word (by simpa using ht)]
  simp

theorem filterMap_range_add (f : Nat → Option (String × UInt64)) (a b : Nat)
    (h : ∀ c, a ≤ c → c < a + b → f c = none) :
    (List.range (a + b)).filterMap f = (List.range a).filterMap f := by
  rw [List.range_add, List.filterMap_append]
  have : ((List.range b).map (a + ·)).filterMap f = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hy
    exact h _ (by omega) (by omega)
  rw [this, List.append_nil]

/-- The rows of `ljTable`: row `t` is the merged row or the left row its
    entry names, when the merged table's first columns are the left table's
    variables. -/
theorem ljTable_rows (merged l : Table) (hm : merged.WF) (src : Array (Option Nat × Nat))
    (hpre : l.vars.size ≤ merged.vars.size) (hv : ∀ c, c < l.vars.size → merged.vars[c]! = l.vars[c]!) :
    (ljTable merged l src).WF ∧ (ljTable merged l src).idRows = src.toList.map (ljRow merged l) := by
  obtain ⟨hcs, hcol⟩ := ljColumns_spec merged l src
  refine ⟨⟨hcs, fun c hc => ?_, hm.nodup⟩, ?_⟩
  · have hc' : c < (IdGroup.ljColumns merged l src).size := hc
    have h := (hcol c (by rw [← hcs]; exact hc')).1
    rw [getElem!_pos _ c hc', List.length_map, Array.length_toList] at h
    exact h
  · apply List.ext_getElem
    · simp [Table.idRows, ljTable]
    · intro t h1 h2
      have ht : t < src.size := by simpa [Table.idRows, ljTable] using h1
      simp only [Table.idRows, List.getElem_map, List.getElem_range, Array.getElem_toList]
      have hat : ∀ c, c < merged.vars.size → (ljTable merged l src).at c t = ljVal merged l c src[t] :=
        fun c hc => ljTable_at merged l src c t hc ht
      unfold Table.idRow
      have hvars : (ljTable merged l src).vars = merged.vars := rfl
      rw [hvars]
      generalize src[t] = e at hat ⊢
      obtain ⟨pk, i⟩ := e
      cases pk with
      | some k =>
        show _ = merged.idRow k
        unfold Table.idRow
        apply OptJoin.filterMap_congr'
        intro c hc
        rw [List.mem_range] at hc
        rw [hat c hc]
        rfl
      | none =>
        show _ = l.idRow i
        unfold Table.idRow
        rw [show merged.vars.size = l.vars.size + (merged.vars.size - l.vars.size) by omega]
        rw [filterMap_range_add _ _ _ (fun c hc hc2 => by
          rw [hat c (by omega)]
          simp [ljVal, show ¬ c < l.vars.size by omega])]
        apply OptJoin.filterMap_congr'
        intro c hc
        rw [List.mem_range] at hc
        rw [hat c (by omega), hv c hc]
        simp [ljVal, hc]

/-! ## `leftJoinCondM` with the condition `true` -/

section
open L4Factoidal.Storage.Sbm11.IdGroup (Pw idLeftJoinC NCx NSt GCtx leftJoinCondM)
open L4Factoidal.Storage.Sbm11.OptJoin (innerSpec)
open L4Factoidal.Storage.Sbm11.TableTheorems (joinPairs_spec innerSpec_eq idJoin_rows innerSpec_congr compatAt_iff
  joinIds_rows pairsTable_eq joinVars_vars)

theorem pw_flatMap_same {α : Type} (f g : Nat → List α) {R : α → α → Prop} :
    ∀ (L : List Nat), (∀ i ∈ L, Pw R (f i) (g i)) → Pw R (L.flatMap f) (L.flatMap g)
  | [], _ => .nil
  | i :: L, h => by
    simp only [List.flatMap_cons]
    exact Pw.append (h i List.mem_cons_self) (pw_flatMap_same f g L fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem pw_of_getElem {α : Type} {R : α → α → Prop} :
    ∀ (A B : List α), A.length = B.length → (∀ k (h1 : k < A.length) (h2 : k < B.length), R A[k] B[k]) → Pw R A B
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: A, b :: B, h, hk => .cons (hk 0 (by simp) (by simp)) (pw_of_getElem A B (by simpa using h)
      fun k h1 h2 => hk (k + 1) (by simpa using h1) (by simpa using h2))

theorem filterMap_ite {α β : Type} (p : α → Bool) (f : α → β) (L : List α) :
    L.filterMap (fun x => if p x then some (f x) else none) = (L.filter p).map f := by
  induction L with
  | nil => rfl
  | cons x L ih => cases h : p x <;> simp [List.filter_cons, h, ih]

theorem off_congr {γ δ : Type} (B : Nat → List γ) (B' : Nat → List δ) (h : ∀ i, (B i).length = (B' i).length)
    (i : Nat) : off B i = off B' i := by
  simp only [off, h]

theorem note_run (line : String) (nst : NSt) :
    ∃ nst', (IdGroup.note (m := Id) line).run nst = pure (PUnit.unit, nst') ∧
      nst'.vocab = nst.vocab ∧ nst'.localIdx = nst.localIdx := ⟨_, rfl, rfl, rfl⟩

theorem leftJoinTrue_run (cx : NCx Id) (g : GCtx) (l r : Table) (nst : NSt) :
    ∃ nst', (leftJoinCondM cx g l r (.boolLit true)).run nst =
      pure (ljTable (IdJoin.joinIds l r) l (IdGroup.ljSource l.rows
        (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1
        (Array.replicate (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1.size true)), nst') ∧
      nst'.vocab = nst.vocab ∧ nst'.localIdx = nst.localIdx := by
  unfold leftJoinCondM
  simp only [if_true]
  rw [StateT.run_bind, StateT.run_pure, pure_bind]
  simp only []
  rw [StateT.run_bind]
  obtain ⟨nst', hn, hv1, hv2⟩ := note_run _ nst
  exact ⟨nst', by rw [hn, pure_bind]; rfl, hv1, hv2⟩

/-- **LeftJoin with the condition `true` on id tables.** For two
    well-formed tables, `leftJoinCondM` with the condition `true` (OPTIONAL
    with no FILTER inside) returns a well-formed table whose rows are, row
    for row, the same solution mappings as `idLeftJoinC (fun _ => true)` of
    the rows of the two tables: per left row its merges with the compatible
    right rows, in order, else the left row. -/
theorem leftJoinTrue_rows (l r : Table) (hl : l.WF) (hr : r.WF) :
    let t := ljTable (IdJoin.joinIds l r) l (IdGroup.ljSource l.rows
        (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1
        (Array.replicate (IdJoin.joinPairs l r (L4Factoidal.Qlvr.sharedCols l r)).1.size true))
    t.WF ∧ Pw RowEq t.idRows (idLeftJoinC (fun _ => true) l.idRows r.idRows) := by
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
  have hsrc := ljSource_spec l.rows cnt li (Array.replicate li.size true) hli (fun k hk => by
    rw [getElem!_pos _ k (by simpa using hk)]; simp)
  -- the merged table
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
  -- the variables of the merged table start with the left table's
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
  have hspec : idLeftJoinC (fun _ => true) l.idRows r.idRows = (List.range l.rows).flatMap fun i =>
      if (Sj i).isEmpty then [l.idRow i] else (Sj i).map fun j => idMerge (l.idRow i) (r.idRow j) := by
    unfold idLeftJoinC Table.idRows
    rw [List.flatMap_map]
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro i _
    simp only [if_true]
    have he : ((List.range r.rows).map r.idRow).filterMap (fun r2 =>
          if idCompatible (l.idRow i) r2 = true then some (idMerge (l.idRow i) r2) else none) =
        (Sj i).map fun j => idMerge (l.idRow i) (r.idRow j) := by
      rw [List.filterMap_map]
      simp only [Function.comp_def]
      rw [filterMap_ite (fun j => idCompatible (l.idRow i) (r.idRow j)) (fun j => idMerge (l.idRow i) (r.idRow j)),
        List.range_eq_range']
      congr 1
      apply List.filter_congr
      intro j _
      exact (compatAt_iff l r hr.nodup i j).symm
    rw [he]
    cases h : (Sj i).isEmpty <;> simp [h]
  rw [hspec]
  apply pw_flatMap_same
  intro i hi
  rw [List.mem_range] at hi
  unfold ljBlock
  by_cases h0 : cnt i = 0
  · have hE : (Sj i).isEmpty = true := by simpa [cnt] using h0
    simp only [h0, if_true, hE, List.map_cons, List.map_nil]
    exact .cons (RowEq.refl _) .nil
  · have hE : (Sj i).isEmpty = false := by simpa [cnt] using h0
    simp only [h0, if_false, hE, Bool.false_eq_true, List.map_map]
    apply pw_of_getElem
    · simp [cnt]
    · intro t h1 h2
      simp only [List.getElem_map, List.getElem_range', Function.comp_def, ljRow]
      have hoff : off (fun i => List.replicate (cnt i) i) i = off BP i :=
        off_congr _ _ (fun i => by simp [BP, cnt]) i
      have ht : t < (BP i).length := by simpa [BP] using h2
      obtain ⟨hk, e⟩ := flatMap_get BP l.rows i t hi ht
      have hk' : off BP i + t < P.length := by rw [hP]; exact hk
      have := hmrow (off BP i + t) hk'
      have eP : P[off BP i + t] = (i, (Sj i)[t]'(by simpa [BP] using h2)) := by
        simp only [hP]; rw [e]; simp [BP]
      rw [eP] at this
      simpa [hoff] using this
end

end L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems.ljSource_spec
#print axioms L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems.ljTable_rows
#print axioms L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems.leftJoinTrue_rows
