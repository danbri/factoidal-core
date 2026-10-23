/-
L4Factoidal.Storage.Sbm11.TableTheorems — the denotation of an id `Table` as
rows of ids, and the joins and the union of the SBM11 id path over it (issue
https://github.com/danbri/factoidal/issues/776; lemmas L5b, L5l″ and the
table part of L5m of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

## The denotation

A `Qlvr.Table` holds one `ByteArray` of 8-byte little-endian ids per
variable; id 0 (`OptJoin.unbound`) is an unbound variable. `Table.idRow t i`
is row `i` as a solution mapping over ids (`OptJoin.IdRow`): the pairs
(variable, id) of the columns in order, a column holding id 0 left out.
`Table.idRows t` is the list of the rows. (The name `Table.rows` is taken:
it is the row count, a field of `Table`.)

`Table.WF t`: one column per variable, each of `8 * t.rows` bytes, no
variable twice. `NoUnbound t`: no column holds id 0 (the tables of the
triple pattern scans).

`RowEq r s`: every variable has the same lookup in `r` and `s`. A solution
mapping is a partial function (SPARQL 1.1 section 18.1.6); the order of the
pairs in an `IdRow` is not part of it. `RowsEq A B`: the same length and
`RowEq` row by row (the same solution mappings in the same order).

## Theorems

* `gather_holds`: `Qlvr.gather src idx` holds the words of rows `idx` of
  `src`, in order (`copySlice` of each run of consecutive rows).
* `joinOutput_rows`: `Qlvr.joinOutput` of the index arrays of pairs whose
  shared columns hold the same ids is well formed and its rows are the
  merges (`idMerge`) of the pairs.
* `hashJoin_rows` (L5b): `Qlvr.hashJoin` of two well-formed tables with no
  `unbound` id. Its rows are a permutation of the rows of `IdJoin.idJoin`
  (SPARQL 1.1 Join, section 18.5) of the tables' rows, each the same
  solution mapping. When the right table has at most as many rows as the
  left one (index on the right, left rows outside), the order is that of
  `idJoin` too; else the left rows are indexed and the right rows probed,
  and the order is right row first (`innerSpecR`).
* `joinPairs_spec`, `joinIds_rows` (L5l″): `IdJoin.joinIds` of two
  well-formed tables, `unbound` allowed on either side, denotes `idJoin` of
  their rows, row for row in the same order.
* `unionIds_rows` (L5m, table part): `IdJoin.unionIds` of well-formed tables
  denotes the concatenation of their rows, in order.

The loops are `for` loops in `Id`; `forIn_inv`, `forIn_list_inv` and
`forIn_range_inv` state invariants over them, `build_spec` and
`probe_spec` the hash index of `Std.HashMap.alter` (`getD_alter`), and
`mergeIdx_spec` the merge of two increasing index arrays.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdJoinTheorems
import L4Factoidal.Storage.Sbm11.ScanFoldTheorems
import L4Factoidal.Storage.Sbm11.ScanWordsTheorems

namespace L4Factoidal.Storage.Sbm11.TableTheorems

open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64 word64Slow byteAt word64_eq_slow)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound)

/-! ## Bytes -/

def ColHolds (b : ByteArray) (xs : List UInt64) : Prop :=
  b.size = 8 * xs.length ∧ ∀ k (h : k < xs.length), word64 b (8 * k) = xs[k]

theorem byteAt_eq (d : ByteArray) (i : Nat) :
    byteAt d i = ((d.data.toList[i]?).map UInt8.toUInt64).getD 0 := by
  unfold byteAt
  by_cases h : i < d.size
  · rw [dif_pos h, List.getElem?_eq_getElem (by simpa using h)]
    simp [ByteArray.getElem_eq_getElem_data]
  · rw [dif_neg h, List.getElem?_eq_none (by simp; simpa using h)]
    rfl

theorem word64_congr (a b : ByteArray) (i j : Nat)
    (h : ∀ t, t < 8 → a.data.toList[i + t]? = b.data.toList[j + t]?) : word64 a i = word64 b j := by
  rw [word64_eq_slow, word64_eq_slow]
  unfold word64Slow
  have e : ∀ t, t < 8 → byteAt a (i + t) = byteAt b (j + t) := fun t ht => by
    rw [byteAt_eq, byteAt_eq, h t ht]
  have e0 := e 0 (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega)]

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]; rfl

theorem ColHolds.append {b c b' : ByteArray} {xs ys : List UInt64} (hb : ColHolds b xs) (hc : ColHolds c ys)
    (h : b'.data.toList = b.data.toList ++ c.data.toList) : ColHolds b' (xs ++ ys) := by
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨?_, ?_⟩
  · rw [size_eq_length, h, List.length_append, ← size_eq_length, ← size_eq_length, hb1, hc1,
      List.length_append]; omega
  · intro k hk
    by_cases hlt : k < xs.length
    · rw [List.getElem_append_left hlt, ← hb2 k hlt]
      apply word64_congr
      intro t ht
      rw [h, List.getElem?_append_left (by rw [← size_eq_length]; omega)]
    · rw [List.getElem_append_right (by omega), ← hc2 (k - xs.length) (by simp at hk; omega)]
      apply word64_congr
      intro t ht
      rw [h, List.getElem?_append_right (by rw [← size_eq_length]; omega), ← size_eq_length, hb1]
      congr 1; omega

theorem ColHolds.nil (b : ByteArray) (h : b.size = 0) : ColHolds b [] :=
  ⟨by simpa using h, fun k hk => absurd hk (by simp)⟩

theorem ColHolds.one (x : UInt64) : ColHolds (L4Factoidal.Storage.Sbm11.FrameWords.words #[x.toNat]) [x] := by
  have hd := L4Factoidal.Storage.Sbm11.FrameWords.words_data #[x.toNat]
  refine ⟨?_, ?_⟩
  · rw [size_eq_length, hd]; simp [L4Factoidal.Storage.Sbm11.FrameWords.put64_length]
  · intro k hk
    have : k = 0 := by simpa using hk
    subst this
    have := L4Factoidal.Storage.Sbm11.ScanTheorems.at64_words #[x.toNat] 0 (by simp)
    unfold L4Factoidal.Storage.Sbm11.IdQuery.at64 at this
    simpa using this

theorem ColHolds.put64 {b : ByteArray} {xs : List UInt64} (hb : ColHolds b xs) (x : UInt64) :
    ColHolds (L4Factoidal.Qlvr.Side.put64 b x) (xs ++ [x]) := by
  apply hb.append (ColHolds.one x)
  rw [L4Factoidal.Storage.Sbm11.ScanFoldTheorems.side_put64_data,
    L4Factoidal.Storage.Sbm11.FrameWords.words_data]
  simp

/-- The words of rows `[s, s + n)` of a column. -/
theorem ColHolds.extract (src : ByteArray) (s n : Nat) (h : 8 * (s + n) ≤ src.size) :
    ColHolds (src.extract (8 * s) (8 * s + 8 * n)) ((List.range' s n).map fun j => word64 src (8 * j)) := by
  refine ⟨by simp; omega, ?_⟩
  intro k hk
  simp only [List.length_map, List.length_range'] at hk
  rw [L4Factoidal.Storage.Sbm11.ScanFoldTheorems.word64_extract _ _ _ _ (by omega) (by omega)]
  simp [List.getElem_range']
  congr 1; omega

theorem copySlice_data (src dest : ByteArray) (so len : Nat) :
    (src.copySlice so dest dest.size len false).data.toList =
      dest.data.toList ++ (src.extract so (so + len)).data.toList := by
  simp only [ByteArray.copySlice, ByteArray.extract, Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero]
  have h1 : dest.size = dest.data.toList.length := size_eq_length dest
  have h2 : dest.data.size = dest.data.toList.length := by rw [Array.length_toList]
  rw [h1, h2, List.take_of_length_le (Nat.le_refl _)]
  simp

/-! ## Loops -/

theorem forIn_inv {β : Type} (P : Nat → β → Prop) (Q : β → Prop) (f : Nat → β → _root_.Id (ForInStep β)) :
    ∀ (n s : Nat) (b : β), P s b →
      (∀ a b, s ≤ a → a < s + n → P a b →
        (∀ b', (f a b).run = .yield b' → P (a + 1) b') ∧ (∀ b', (f a b).run = .done b' → Q b')) →
      P (s + n) (forIn (List.range' s n) b f).run ∨ Q (forIn (List.range' s n) b f).run := by
  intro n
  induction n with
  | zero => intro s b h _; left; simpa using h
  | succ n ih =>
    intro s b h hs
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨hy, hd⟩ := hs s b (Nat.le_refl _) (by omega) h
    cases e : (f s b).run with
    | done b' =>
      right
      have : f s b = pure (.done b') := by rw [← e]; rfl
      rw [this]; simpa using hd b' e
    | yield b' =>
      have : f s b = pure (.yield b') := by rw [← e]; rfl
      rw [this]
      simp only [pure_bind]
      have := ih (s + 1) b' (hy b' e) (fun a b2 h1 h2 h3 => hs a b2 (by omega) (by omega) h3)
      rw [show s + 1 + n = s + (n + 1) by omega] at this
      exact this

theorem forIn_inv' {β : Type} (P : Nat → β → Prop) (Q : β → Prop) {f : Nat → β → _root_.Id (ForInStep β)}
    {n s : Nat} {b : β} {F : _root_.Id β} (hF : forIn (List.range' s n) b f = F) (h0 : P s b)
    (hs : ∀ a b, s ≤ a → a < s + n → P a b →
        (∀ b', (f a b).run = .yield b' → P (a + 1) b') ∧ (∀ b', (f a b).run = .done b' → Q b')) :
    P (s + n) F.run ∨ Q F.run := by
  subst hF; exact forIn_inv P Q f n s b h0 hs

/-- An invariant for a `for` loop over a list without `break`: every step
    yields. -/
theorem forIn_list_inv {α β : Type} :
    ∀ (l : List α) (P : Nat → β → Prop) {f : α → β → _root_.Id (ForInStep β)} {b : β} {F : _root_.Id β},
      forIn l b f = F → P 0 b →
      (∀ k b (hk : k < l.length), P k b → ∃ b', (f l[k] b).run = .yield b' ∧ P (k + 1) b') →
      P l.length F.run := by
  intro l
  induction l with
  | nil => intro P f b F hF h0 _; subst hF; exact h0
  | cons a rest ih =>
    intro P f b F hF h0 hs
    subst hF
    obtain ⟨b', hb, hP⟩ := hs 0 b (by simp) h0
    rw [List.forIn_cons]
    have : f a b = pure (.yield b') := by rw [← hb]; rfl
    rw [this, pure_bind]
    exact ih (fun k b => P (k + 1) b) rfl hP (fun k b2 hk h => hs (k + 1) b2 (by simp; omega) h)

/-! ## `gather` -/

/-- `gather src idx` holds the words of rows `idx` of `src`, in order. -/
theorem gather_holds (src : ByteArray) (idx : Array Nat) (hsrc : ∀ j ∈ idx.toList, 8 * (j + 1) ≤ src.size) :
    ColHolds (gather src idx) (idx.toList.map fun j => word64 src (8 * j)) := by
  unfold gather
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : [:idx.size].size = idx.size := by simp [Std.Legacy.Range.size]
  rw [hsz]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 idx.size) (ByteArray.emptyWithCapacity (8 * idx.size), 0) _ = F
  show ColHolds F.run.1 _
  let w : Nat → UInt64 := fun j => word64 src (8 * j)
  have key := forIn_inv' (fun a (st : ByteArray × Nat) => a ≤ st.2 ∧ st.2 ≤ idx.size ∧
      ColHolds st.1 ((idx.toList.take st.2).map w))
    (fun st => st.2 = idx.size ∧ ColHolds st.1 ((idx.toList.take st.2).map w)) hF
    ⟨Nat.le_refl _, Nat.zero_le _, ColHolds.nil _ rfl⟩ ?step
  · rcases key with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · have : F.run.2 = idx.size := by omega
      rw [this, List.take_of_length_le (by simp)] at h3; exact h3
    · rw [h1, List.take_of_length_le (by simp)] at h2; exact h2
  case step =>
    intro a st _ ha ⟨hk1, hk2, hk3⟩
    by_cases hge : st.2 ≥ idx.size
    · simp only [if_pos hge]
      refine ⟨fun b' hb => by simp at hb, fun b' hb => ?_⟩
      simp only [_root_.Id.run_pure, ForInStep.done.injEq] at hb; subst hb
      exact ⟨by omega, hk3⟩
    · simp only [if_neg hge]
      generalize hG : forIn (m := _root_.Id) (List.range' 0 idx.size) (st.2 + 1) _ = G
      have inner := forIn_inv' (fun _ e => st.2 + 1 ≤ e ∧ e ≤ idx.size ∧
          ∀ t, st.2 ≤ t → t < e → idx[t]! = idx[st.2]! + (t - st.2))
        (fun e => st.2 + 1 ≤ e ∧ e ≤ idx.size ∧
          ∀ t, st.2 ≤ t → t < e → idx[t]! = idx[st.2]! + (t - st.2)) hG
        ⟨Nat.le_refl _, by omega, fun t h1 h2 => by rw [show t = st.2 by omega]; simp⟩ ?istep
      · have hI : st.2 + 1 ≤ G.run ∧ G.run ≤ idx.size ∧
            ∀ t, st.2 ≤ t → t < G.run → idx[t]! = idx[st.2]! + (t - st.2) := by
          rcases inner with h | h <;> exact h
        obtain ⟨hI1, hI2, hI3⟩ := hI
        refine ⟨fun b' hb => ?_, fun b' hb => by simp at hb⟩
        simp only [_root_.Id.run_pure, _root_.Id.run_bind, ForInStep.yield.injEq] at hb; subst hb
        refine ⟨by simp; omega, by simpa using hI2, ?_⟩
        simp only
        have hsplit : idx.toList.take G.run =
            idx.toList.take st.2 ++ List.range' idx[st.2]! (G.run - st.2) := by
          rw [← List.take_append_drop st.2 (idx.toList.take G.run), List.take_take,
            Nat.min_eq_left (by omega)]
          congr 1
          apply List.ext_getElem
          · simp; omega
          · intro i h1 h2
            simp only [List.getElem_drop, List.getElem_take, List.getElem_range', Nat.one_mul]
            have := hI3 (st.2 + i) (by omega) (by simp at h1; omega)
            rw [getElem!_pos idx _ (by simp at h1; omega)] at this
            simp only [Array.getElem_toList]
            rw [this]; omega
        rw [hsplit, List.map_append]
        have hlast : 8 * (idx[st.2]! + (G.run - st.2)) ≤ src.size := by
          have h1 := hI3 (G.run - 1) (by omega) (by omega)
          have hm : idx[G.run - 1]! ∈ idx.toList := by
            rw [getElem!_pos idx _ (by omega)]; simp
          have := hsrc _ hm
          rw [h1] at this
          have : idx[st.2]! + (G.run - 1 - st.2) + 1 = idx[st.2]! + (G.run - st.2) := by omega
          omega
        exact hk3.append (ColHolds.extract src _ _ hlast) (by
          rw [copySlice_data])
      case istep =>
        intro a' e _ _ ⟨he1, he2, he3⟩
        by_cases hc : (decide (e < idx.size) && idx[e]! == idx[st.2]! + (e - st.2)) = true
        · simp only [if_pos hc]
          refine ⟨fun b' hb => ?_, fun b' hb => by simp at hb⟩
          simp only [_root_.Id.run_pure, ForInStep.yield.injEq] at hb; subst hb
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          refine ⟨by omega, by omega, fun t h1 h2 => ?_⟩
          by_cases ht : t < e
          · exact he3 t h1 ht
          · have : t = e := by omega
            subst this; exact hc.2
        · simp only [if_neg hc]
          refine ⟨fun b' hb => by simp at hb, fun b' hb => ?_⟩
          simp only [_root_.Id.run_pure, ForInStep.done.injEq] at hb; subst hb
          exact ⟨he1, he2, he3⟩


end L4Factoidal.Storage.Sbm11.TableTheorems

/-! ## The denotation -/

namespace L4Factoidal.Qlvr

open L4Factoidal.Storage.Sbm11.OptJoin (IdRow unbound)

/-- Row `i` of `t` as a solution mapping over ids: (variable, id) per column
    in order, a column holding `unbound` (id 0) left out. -/
def Table.idRow (t : Table) (i : Nat) : IdRow :=
  (List.range t.vars.size).filterMap fun c =>
    if t.at c i == unbound then none else some (t.vars[c]!, t.at c i)

/-- The rows of `t` as solution mappings over ids, in order. -/
def Table.idRows (t : Table) : List IdRow := (List.range t.rows).map t.idRow

/-- The id of variable `v` in row `i`, `none` when `t` has no column `v` or
    the column holds `unbound`. -/
def Table.lookupAt (t : Table) (i : Nat) (v : String) : Option UInt64 :=
  match t.idx v with
  | some c => if t.at c i == unbound then none else some (t.at c i)
  | none => none

/-- One column per variable, each of `8 * t.rows` bytes, and no variable
    twice. -/
structure Table.WF (t : Table) : Prop where
  cols_size : t.cols.size = t.vars.size
  col_bytes : ∀ c (h : c < t.cols.size), t.cols[c].size = 8 * t.rows
  nodup : t.vars.toList.Nodup

end L4Factoidal.Qlvr

namespace L4Factoidal.Storage.Sbm11.TableTheorems

open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound)

/-- Two rows of ids are the same solution mapping. -/
def RowEq (r s : IdRow) : Prop := ∀ v, idLookup v r = idLookup v s

theorem RowEq.refl (r : IdRow) : RowEq r r := fun _ => rfl
theorem RowEq.symm {r s : IdRow} (h : RowEq r s) : RowEq s r := fun v => (h v).symm
theorem RowEq.trans {r s u : IdRow} (h1 : RowEq r s) (h2 : RowEq s u) : RowEq r u :=
  fun v => (h1 v).trans (h2 v)

theorem lookup_filterMap (vars : Array String) (x : Nat → UInt64) (v : String) (c0 : Nat) :
    ∀ (cs : List Nat), (∀ c ∈ cs, vars[c]! = v → c = c0) →
      idLookup v (cs.filterMap fun c => if x c == unbound then none else some (vars[c]!, x c)) =
        if c0 ∈ cs ∧ vars[c0]! = v ∧ x c0 ≠ unbound then some (x c0) else none := by
  intro cs
  induction cs with
  | nil => intro _; simp [idLookup]
  | cons c rest ih =>
    intro h
    have hr := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    rw [List.filterMap_cons]
    by_cases hx : x c = unbound
    · simp only [hx, beq_self_eq_true, if_true]
      rw [hr]
      by_cases hv : vars[c]! = v
      · have := h c (by simp) hv
        subst this
        simp [hx]
      · congr 1
        apply propext
        constructor
        · intro ⟨a, b, d⟩; exact ⟨List.mem_cons_of_mem _ a, b, d⟩
        · intro ⟨a, b, d⟩
          rcases List.mem_cons.mp a with e | e
          · subst e; exact absurd b hv
          · exact ⟨e, b, d⟩
    · have hx' : (x c == unbound) = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, if_false, idLookup]
      by_cases hv : vars[c]! = v
      · have := h c (by simp) hv
        subst this
        simp [hv, hx]
      · rw [if_neg hv, hr]
        congr 1
        apply propext
        constructor
        · intro ⟨a, b, d⟩; exact ⟨List.mem_cons_of_mem _ a, b, d⟩
        · intro ⟨a, b, d⟩
          rcases List.mem_cons.mp a with e | e
          · subst e; exact absurd b hv
          · exact ⟨e, b, d⟩

theorem idx_some {t : Table} {v : String} {c : Nat} (h : t.idx v = some c) :
    c < t.vars.size ∧ t.vars[c]! = v := by
  unfold Table.idx at h
  obtain ⟨hc, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hc, by rw [getElem!_pos t.vars c hc]; simpa using hp⟩

theorem idx_none {t : Table} {v : String} (h : t.idx v = none) : ∀ c, c < t.vars.size → t.vars[c]! ≠ v := by
  unfold Table.idx at h
  have := Array.findIdx?_eq_none_iff.mp h
  intro c hc e
  rw [getElem!_pos t.vars c hc] at e
  have := this t.vars[c] (Array.getElem_mem hc)
  simp [e] at this

theorem nodup_idx {vars : Array String} (hnd : vars.toList.Nodup) {c c' : Nat} (hc : c < vars.size)
    (hc' : c' < vars.size) (h : vars[c]! = vars[c']!) : c = c' := by
  rw [getElem!_pos vars c hc, getElem!_pos vars c' hc'] at h
  exact (List.getElem_inj (xs := vars.toList) (h₀ := by simpa using hc) (h₁ := by simpa using hc')
    hnd).mp (by simpa using h)

theorem idx_of_getElem {t : Table} (hnd : t.vars.toList.Nodup) {c : Nat} (hc : c < t.vars.size) :
    t.idx t.vars[c]! = some c := by
  cases h : t.idx t.vars[c]! with
  | none => exact absurd rfl (idx_none h c hc)
  | some c' =>
    obtain ⟨h1, h2⟩ := idx_some h
    rw [nodup_idx hnd h1 hc h2]

/-- The lookup of a variable in a row of `t` is the id in its column. -/
theorem lookup_idRow (t : Table) (hnd : t.vars.toList.Nodup) (i : Nat) (v : String) :
    idLookup v (t.idRow i) = t.lookupAt i v := by
  unfold Table.idRow Table.lookupAt
  cases h : t.idx v with
  | some c =>
    obtain ⟨hc, hv⟩ := idx_some h
    rw [lookup_filterMap t.vars (fun c => t.at c i) v c _ (fun c' hc' e =>
      nodup_idx hnd (by simpa using hc') hc (e.trans hv.symm))]
    by_cases hx : t.at c i = unbound
    · simp [hx]
    · rw [getElem!_pos t.vars c hc] at hv
      simp [hx, hc, hv]
  | none =>
    rw [lookup_filterMap t.vars (fun c => t.at c i) v 0 _ (fun c' hc' e =>
      absurd e (idx_none h c' (by simpa using hc')))]
    rw [if_neg]
    intro ⟨a, b, _⟩
    exact idx_none h 0 (by simpa using a) b

/-! ## Lookups in merged and compatible rows -/

theorem lookup_idMerge (w : String) :
    ∀ (r2 r1 : IdRow), idLookup w (idMerge r1 r2) = (idLookup w r1).or (idLookup w r2) := by
  intro r2
  induction r2 with
  | nil => intro r1; simp [idMerge, idLookup]
  | cons a rest ih =>
    intro r1
    obtain ⟨v, x⟩ := a
    simp only [idMerge]
    cases h : idLookup v r1 with
    | some y =>
      simp only
      rw [ih r1]
      by_cases hw : v = w
      · subst hw; simp [h]
      · simp [idLookup, hw]
    | none =>
      simp only
      rw [ih ((v, x) :: r1)]
      by_cases hw : v = w
      · subst hw; simp [idLookup, h]
      · simp [idLookup, hw]

theorem idCompatible_iff : ∀ (r1 r2 : IdRow),
    idCompatible r1 r2 = true ↔ ∀ p ∈ r1, ∀ y, idLookup p.1 r2 = some y → p.2 = y := by
  intro r1
  induction r1 with
  | nil => intro r2; simp [idCompatible]
  | cons a rest ih =>
    intro r2
    obtain ⟨v, x⟩ := a
    simp only [idCompatible, Bool.and_eq_true, ih r2, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨fun y hy => ?_, h2⟩
      rw [hy] at h1; simpa using h1
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases hl : idLookup v r2 with
      | none => rfl
      | some y => simpa using h1 y hl

theorem mem_idRow {t : Table} {i : Nat} {p : String × UInt64} :
    p ∈ t.idRow i ↔ ∃ c, c < t.vars.size ∧ t.at c i ≠ unbound ∧ p = (t.vars[c]!, t.at c i) := by
  unfold Table.idRow
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · intro ⟨c, hc, h⟩
    by_cases hx : t.at c i = unbound
    · simp [hx] at h
    · simp only [hx, beq_iff_eq, if_false, Option.some.injEq] at h
      exact ⟨c, hc, hx, h.symm⟩
  · intro ⟨c, hc, hx, e⟩
    exact ⟨c, hc, by simp [hx, e]⟩

/-- Two table rows are compatible exactly when, in every column of the left
    row that holds an id, the right row's id for that variable, if any, is
    the same. -/
theorem idCompatible_rows (l r : Table) (hr : r.vars.toList.Nodup) (i j : Nat) :
    idCompatible (l.idRow i) (r.idRow j) = true ↔
      ∀ c, c < l.vars.size → l.at c i ≠ unbound → ∀ y, r.lookupAt j l.vars[c]! = some y → l.at c i = y := by
  rw [idCompatible_iff]
  constructor
  · intro h c hc hx y hy
    exact h _ (mem_idRow.mpr ⟨c, hc, hx, rfl⟩) y (by rw [lookup_idRow r hr]; exact hy)
  · intro h p hp y hy
    obtain ⟨c, hc, hx, e⟩ := mem_idRow.mp hp
    subst e
    exact h c hc hx y (by rw [← lookup_idRow r hr]; exact hy)

theorem mem_sharedCols {l r : Table} {p q : Nat} :
    (p, q) ∈ L4Factoidal.Qlvr.sharedCols l r ↔ p < l.vars.size ∧ r.idx l.vars[p]! = some q := by
  unfold L4Factoidal.Qlvr.sharedCols
  simp only [Array.mem_filterMap, List.mem_toArray, List.mem_range, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · intro ⟨a, ha, b, hb, e1, e2⟩
    subst e1; subst e2; exact ⟨ha, hb⟩
  · intro ⟨h1, h2⟩
    exact ⟨p, h1, q, h2, rfl, rfl⟩

/-! ## Sorted index lists -/

/-- Two lists in strictly increasing order with the same members are
    equal. -/
theorem eq_of_sorted_mem : ∀ (a b : List Nat), a.Pairwise (· < ·) → b.Pairwise (· < ·) →
    (∀ x, x ∈ a ↔ x ∈ b) → a = b := by
  intro a
  induction a with
  | nil =>
    intro b _ _ h
    cases b with
    | nil => rfl
    | cons y ys => exact absurd ((h y).mpr (by simp)) (by simp)
  | cons x xs ih =>
    intro b ha hb h
    cases b with
    | nil => exact absurd ((h x).mp (by simp)) (by simp)
    | cons y ys =>
      rw [List.pairwise_cons] at ha hb
      have hxy : x = y := by
        have h1 := (h x).mp (by simp)
        have h2 := (h y).mpr (by simp)
        rcases List.mem_cons.mp h1 with e | e
        · exact e
        · rcases List.mem_cons.mp h2 with e' | e'
          · exact e'.symm
          · have := hb.1 x e; have := ha.1 y e'; omega
      subst hxy
      congr 1
      apply ih ys ha.2 hb.2
      intro z
      constructor
      · intro hz
        have := (h z).mp (by simp [hz])
        rcases List.mem_cons.mp this with e | e
        · have := ha.1 z hz; omega
        · exact e
      · intro hz
        have := (h z).mpr (by simp [hz])
        rcases List.mem_cons.mp this with e | e
        · have := hb.1 z hz; omega
        · exact e

theorem pairwise_lt_of_getElem {a : Array Nat} (h : ∀ k k', k < k' → k' < a.size → a[k]! < a[k']!) :
    a.toList.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro k k' hk hk' hlt
  have := h k k' hlt (by simpa using hk')
  rw [getElem!_pos a k (by simp at hk; omega), getElem!_pos a k' (by simpa using hk')] at this
  simpa using this

theorem mem_array_iff {a : Array Nat} {x : Nat} : x ∈ a.toList ↔ ∃ k, k < a.size ∧ a[k]! = x := by
  rw [List.mem_iff_getElem]
  constructor
  · intro ⟨k, hk, e⟩
    refine ⟨k, by simpa using hk, ?_⟩
    rw [getElem!_pos a k (by simpa using hk)]; simpa using e
  · intro ⟨k, hk, e⟩
    refine ⟨k, by simpa using hk, ?_⟩
    rw [getElem!_pos a k hk] at e; simpa using e

/-- `IdJoin.mergeIdx` of two strictly increasing index arrays with no
    common member is strictly increasing and holds the members of both. -/
theorem mergeIdx_spec (a b : Array Nat)
    (hA : ∀ k k', k < k' → k' < a.size → a[k]! < a[k']!)
    (hB : ∀ k k', k < k' → k' < b.size → b[k]! < b[k']!)
    (hD : ∀ k k', k < a.size → k' < b.size → a[k]! ≠ b[k']!) :
    (L4Factoidal.Storage.Sbm11.IdJoin.mergeIdx a b).toList.Pairwise (· < ·) ∧
      ∀ x, x ∈ (L4Factoidal.Storage.Sbm11.IdJoin.mergeIdx a b).toList ↔ x ∈ a.toList ∨ x ∈ b.toList := by
  unfold L4Factoidal.Storage.Sbm11.IdJoin.mergeIdx
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : [:a.size + b.size].size = a.size + b.size := by simp [Std.Legacy.Range.size]
  rw [hsz]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 (a.size + b.size)) (Array.mkEmpty (a.size + b.size), 0, 0) _ = F
  show (F.run.1).toList.Pairwise (· < ·) ∧ ∀ x, x ∈ F.run.1.toList ↔ x ∈ a.toList ∨ x ∈ b.toList
  let P : Nat → Array Nat × Nat × Nat → Prop := fun t st =>
    st.2.1 ≤ a.size ∧ st.2.2 ≤ b.size ∧ st.2.1 + st.2.2 = t ∧ st.1.toList.Pairwise (· < ·) ∧
      (∀ x, x ∈ st.1.toList ↔ (∃ k, k < st.2.1 ∧ a[k]! = x) ∨ (∃ k, k < st.2.2 ∧ b[k]! = x)) ∧
      (∀ x ∈ st.1.toList, (∀ k, st.2.1 ≤ k → k < a.size → x < a[k]!) ∧
        (∀ k, st.2.2 ≤ k → k < b.size → x < b[k]!))
  have key := forIn_inv' P (fun _ => False) hF
    ⟨Nat.zero_le _, Nat.zero_le _, rfl, by simp, by simp, by simp⟩ ?step
  · rcases key with ⟨h1, h2, h3, h4, h5, _⟩ | h
    · refine ⟨h4, fun x => ?_⟩
      have ei : F.run.2.1 = a.size := by omega
      have ej : F.run.2.2 = b.size := by omega
      rw [h5, ei, ej, mem_array_iff, mem_array_iff]
    · exact h.elim
  case step =>
    intro t st _ ht ⟨hi, hj, hij, hp, hm, hb⟩
    obtain ⟨out, i, j⟩ := st
    simp only at hi hj hij hp hm hb ⊢
    refine ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩
    rotate_left
    · split at hb' <;> (try split at hb') <;> simp at hb'
    by_cases hia : i < a.size
    · rw [if_pos hia] at hb'
      by_cases hc : (decide (j < b.size) && decide (b[j]! < a[i]!)) = true
      · rw [if_pos hc] at hb'
        simp only [_root_.Id.run_pure, ForInStep.yield.injEq] at hb'; subst hb'; dsimp only [P]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        refine ⟨hi, by omega, by omega, ?_, ?_, ?_⟩
        · rw [Array.toList_push, List.pairwise_append]
          exact ⟨hp, by simp, fun x hx y hy => by simp at hy; subst hy; exact (hb x hx).2 j (Nat.le_refl _) hc.1⟩
        · intro x
          rw [Array.toList_push, List.mem_append, hm]
          constructor
          · rintro ((h | ⟨k, hk, e⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨k, by omega, e⟩
            · simp at h; exact Or.inr ⟨j, by omega, h.symm⟩
          · rintro (h | ⟨k, hk, e⟩)
            · exact Or.inl (Or.inl h)
            · by_cases hkj : k < j
              · exact Or.inl (Or.inr ⟨k, hkj, e⟩)
              · have : k = j := by omega
                subst this; simp [e]
        · intro x hx
          rw [Array.toList_push, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ⟨(hb x hx).1, fun k h1 h2 => (hb x hx).2 k (by omega) h2⟩
          · simp at hx; subst hx
            refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => hB j k (by omega) h2⟩
            rcases Nat.eq_or_lt_of_le h1 with e | e
            · subst e; exact hc.2
            · exact Nat.lt_trans hc.2 (hA i k e h2)
      · rw [if_neg hc] at hb'
        simp only [_root_.Id.run_pure, ForInStep.yield.injEq] at hb'; subst hb'; dsimp only [P]
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at hc
        refine ⟨by omega, hj, by omega, ?_, ?_, ?_⟩
        · rw [Array.toList_push, List.pairwise_append]
          exact ⟨hp, by simp, fun x hx y hy => by simp at hy; subst hy; exact (hb x hx).1 i (Nat.le_refl _) hia⟩
        · intro x
          rw [Array.toList_push, List.mem_append, hm]
          constructor
          · rintro ((⟨k, hk, e⟩ | h) | h)
            · exact Or.inl ⟨k, by omega, e⟩
            · exact Or.inr h
            · simp at h; exact Or.inl ⟨i, by omega, h.symm⟩
          · rintro (⟨k, hk, e⟩ | h)
            · by_cases hki : k < i
              · exact Or.inl (Or.inl ⟨k, hki, e⟩)
              · have : k = i := by omega
                subst this; simp [e]
            · exact Or.inl (Or.inr h)
        · intro x hx
          rw [Array.toList_push, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ⟨fun k h1 h2 => (hb x hx).1 k (by omega) h2, (hb x hx).2⟩
          · simp at hx; subst hx
            refine ⟨fun k h1 h2 => hA i k (by omega) h2, fun k h1 h2 => ?_⟩
            have hle := hc (by omega)
            have hne := hD i j hia (by omega)
            have hlt : a[i]! < b[j]! := by omega
            rcases Nat.eq_or_lt_of_le h1 with e | e
            · subst e; exact hlt
            · exact Nat.lt_trans hlt (hB j k e h2)
    · rw [if_neg hia] at hb'
      by_cases hjb : j < b.size
      · rw [if_pos hjb] at hb'
        simp only [_root_.Id.run_pure, ForInStep.yield.injEq] at hb'; subst hb'; dsimp only [P]
        refine ⟨hi, by omega, by omega, ?_, ?_, ?_⟩
        · rw [Array.toList_push, List.pairwise_append]
          exact ⟨hp, by simp, fun x hx y hy => by simp at hy; subst hy; exact (hb x hx).2 j (Nat.le_refl _) hjb⟩
        · intro x
          rw [Array.toList_push, List.mem_append, hm]
          constructor
          · rintro ((h | ⟨k, hk, e⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨k, by omega, e⟩
            · simp at h; exact Or.inr ⟨j, by omega, h.symm⟩
          · rintro (h | ⟨k, hk, e⟩)
            · exact Or.inl (Or.inl h)
            · by_cases hkj : k < j
              · exact Or.inl (Or.inr ⟨k, hkj, e⟩)
              · have : k = j := by omega
                subst this; simp [e]
        · intro x hx
          rw [Array.toList_push, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ⟨(hb x hx).1, fun k h1 h2 => (hb x hx).2 k (by omega) h2⟩
          · simp at hx; subst hx
            exact ⟨fun k h1 h2 => absurd h2 (by omega), fun k h1 h2 => hB j k (by omega) h2⟩
      · exfalso; omega

/-! ## The layout of a join's output -/

/-- An id, `none` for `unbound`. -/
def nz (x : UInt64) : Option UInt64 := if x == unbound then none else some x

theorem lookupAt_eq (t : Table) (i : Nat) (v : String) :
    t.lookupAt i v = match t.idx v with
      | some c => nz (t.at c i)
      | none => none := by
  unfold Table.lookupAt nz; rfl

theorem arr_get {α : Type} [Inhabited α] (a : Array α) (c : Nat) (h : c < a.size) :
    a[c]! = a.toList[c]'(by simpa using h) := by
  rw [getElem!_pos a c h]; simp

theorem joinVars_extra (l r : Table) :
    (L4Factoidal.Qlvr.joinVars l r).2.toList =
      (List.range r.vars.size).filter (fun q => !l.vars.contains r.vars[q]!) := by
  simp [L4Factoidal.Qlvr.joinVars]

theorem joinVars_vars (l r : Table) :
    (L4Factoidal.Qlvr.joinVars l r).1.toList =
      l.vars.toList ++ (L4Factoidal.Qlvr.joinVars l r).2.toList.map (fun q => r.vars[q]!) := by
  simp [L4Factoidal.Qlvr.joinVars]

theorem mem_extra {l r : Table} {extra : Array Nat}
    (hex : extra.toList = (List.range r.vars.size).filter (fun q => !l.vars.contains r.vars[q]!))
    {q : Nat} : q ∈ extra.toList ↔ q < r.vars.size ∧ r.vars[q]! ∉ l.vars := by
  rw [hex]; simp

theorem out_nodup (l r : Table) (extra : Array Nat) (hl : l.vars.toList.Nodup) (hr : r.vars.toList.Nodup)
    (hex : extra.toList = (List.range r.vars.size).filter (fun q => !l.vars.contains r.vars[q]!)) :
    (l.vars.toList ++ extra.toList.map (fun q => r.vars[q]!)).Nodup := by
  rw [List.nodup_append]
  refine ⟨hl, ?_, ?_⟩
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    have hp : extra.toList.Pairwise (· < ·) := by
      rw [hex]; exact List.pairwise_lt_range.filter _
    apply hp.imp_of_mem
    intro a b ha hb hab e
    have ha' := (mem_extra hex).mp ha
    have hb' := (mem_extra hex).mp hb
    have := nodup_idx hr ha'.1 hb'.1 e
    omega
  · intro a ha b hb e
    subst e
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hb
    have := ((mem_extra hex).mp hq).2
    rw [e] at this
    exact this (by simpa using ha)

/-- The lookup in a row of a join's output: a variable of the left table
    has the id of its output column (`Lv`), a variable of the right table
    only the id `Rv q` of its right column `q`. -/
theorem out_lookup_gen (l r T : Table) (extra : Array Nat) (k : Nat) (Lv Rv : Nat → UInt64)
    (hl : l.vars.toList.Nodup) (hr : r.vars.toList.Nodup)
    (hv : T.vars.toList = l.vars.toList ++ extra.toList.map (fun q => r.vars[q]!))
    (hex : extra.toList = (List.range r.vars.size).filter (fun q => !l.vars.contains r.vars[q]!))
    (hL : ∀ c, c < l.vars.size → T.at c k = Lv c)
    (hR : ∀ m, m < extra.size → T.at (l.vars.size + m) k = Rv extra[m]!) (v : String) :
    T.lookupAt k v = match l.idx v with
      | some c => nz (Lv c)
      | none => match r.idx v with
        | some q => nz (Rv q)
        | none => none := by
  have hnd : T.vars.toList.Nodup := by rw [hv]; exact out_nodup l r extra hl hr hex
  have hTs : T.vars.size = l.vars.size + extra.size := by
    rw [← Array.length_toList, hv]; simp
  have hTl : ∀ c, c < l.vars.size → T.vars[c]! = l.vars[c]! := by
    intro c hc
    rw [arr_get T.vars c (by omega), arr_get l.vars c hc]
    simp only [hv]
    rw [List.getElem_append_left (by simpa using hc)]
  have hTr : ∀ m, m < extra.size → T.vars[l.vars.size + m]! = r.vars[extra[m]!]! := by
    intro m hm
    rw [arr_get T.vars _ (by omega), arr_get extra m hm]
    simp only [hv]
    rw [List.getElem_append_right (by simp)]
    simp
  rw [lookupAt_eq]
  cases hlv : l.idx v with
  | some c =>
    obtain ⟨hc, hcv⟩ := idx_some hlv
    have hT : T.idx v = some c := by
      rw [← hcv, ← hTl c hc]; exact idx_of_getElem hnd (by omega)
    simp only [hT, hL c hc]
  | none =>
    simp only
    cases hrv : r.idx v with
    | some q =>
      obtain ⟨hq, hqv⟩ := idx_some hrv
      have hmem : q ∈ extra.toList := (mem_extra hex).mpr ⟨hq, by
        rw [hqv]; intro h
        obtain ⟨c, hc, e⟩ := Array.mem_iff_getElem.mp h
        exact idx_none hlv c hc (by rw [getElem!_pos l.vars c hc]; exact e)⟩
      obtain ⟨m, hm, e⟩ := List.mem_iff_getElem.mp hmem
      have hm' : m < extra.size := by simpa using hm
      have he : extra[m]! = q := by rw [arr_get extra m hm']; exact e
      have hT : T.idx v = some (l.vars.size + m) := by
        rw [← hqv, ← he, ← hTr m hm']; exact idx_of_getElem hnd (by omega)
      simp only [hT, hR m hm', he]
    | none =>
      have hT : T.idx v = none := by
        cases h : T.idx v with
        | none => rfl
        | some c' =>
          exfalso
          obtain ⟨hc', hcv⟩ := idx_some h
          by_cases hcl : c' < l.vars.size
          · rw [hTl c' hcl] at hcv; exact idx_none hlv c' hcl hcv
          · have hm : c' - l.vars.size < extra.size := by omega
            have := hTr (c' - l.vars.size) hm
            rw [show l.vars.size + (c' - l.vars.size) = c' by omega] at this
            rw [this] at hcv
            have hq : extra[c' - l.vars.size]! ∈ extra.toList := by
              rw [arr_get extra _ hm]; simp
            exact idx_none hrv _ ((mem_extra hex).mp hq).1 hcv
      simp only [hT]

/-- The lookup in a row of a join's output: a variable of the left table
    has the id of its output column (`Lv`), any other variable the id of the
    right row `j`. -/
theorem out_lookup (l r T : Table) (extra : Array Nat) (k j : Nat) (Lv : Nat → UInt64)
    (hl : l.vars.toList.Nodup) (hr : r.vars.toList.Nodup)
    (hv : T.vars.toList = l.vars.toList ++ extra.toList.map (fun q => r.vars[q]!))
    (hex : extra.toList = (List.range r.vars.size).filter (fun q => !l.vars.contains r.vars[q]!))
    (hL : ∀ c, c < l.vars.size → T.at c k = Lv c)
    (hR : ∀ m, m < extra.size → T.at (l.vars.size + m) k = r.at extra[m]! j) (v : String) :
    T.lookupAt k v = match l.idx v with
      | some c => nz (Lv c)
      | none => r.lookupAt j v := by
  rw [out_lookup_gen l r T extra k Lv (fun q => r.at q j) hl hr hv hex hL hR v, lookupAt_eq r]

/-! ## Rows of a join's output -/

/-- Two lists of rows of ids hold the same solution mappings in the same
    order. -/
def RowsEq (A B : List IdRow) : Prop :=
  A.length = B.length ∧ ∀ k (h1 : k < A.length) (h2 : k < B.length), RowEq A[k] B[k]

theorem RowsEq.refl (A : List IdRow) : RowsEq A A := ⟨rfl, fun _ _ _ => RowEq.refl _⟩

theorem RowsEq.trans {A B C : List IdRow} (h1 : RowsEq A B) (h2 : RowsEq B C) : RowsEq A C :=
  ⟨h1.1.trans h2.1, fun k a c => (h1.2 k a (by rw [← h1.1]; exact a)).trans (h2.2 k (by rw [← h1.1]; exact a) c)⟩

theorem ColHolds.word {b : ByteArray} {xs : List UInt64} (h : ColHolds b xs) {k : Nat} (hk : k < xs.length) :
    word64 b (8 * k) = xs[k] := h.2 k hk

/-- A column of a well-formed table: rows `idx` gathered. -/
theorem gather_at (t : Table) (ht : t.WF) (c : Nat) (hc : c < t.vars.size) (idx : Array Nat)
    (hidx : ∀ i ∈ idx.toList, i < t.rows) :
    ColHolds (gather t.cols[c]! idx) (idx.toList.map fun i => t.at c i) := by
  have hc' : c < t.cols.size := by rw [ht.cols_size]; exact hc
  have := gather_holds t.cols[c]! idx (fun i hi => by
    rw [getElem!_pos t.cols c hc', ht.col_bytes c hc']
    have := hidx i hi; omega)
  exact this

theorem gather_word (t : Table) (ht : t.WF) (c : Nat) (hc : c < t.vars.size) (idx : Array Nat)
    (hidx : ∀ i ∈ idx.toList, i < t.rows) (k : Nat) (hk : k < idx.size) :
    word64 (gather t.cols[c]! idx) (8 * k) = t.at c idx[k]! := by
  rw [(gather_at t ht c hc idx hidx).word (by simpa using hk)]
  simp [getElem!_pos idx k hk]

theorem gather_size (t : Table) (ht : t.WF) (c : Nat) (hc : c < t.vars.size) (idx : Array Nat)
    (hidx : ∀ i ∈ idx.toList, i < t.rows) : (gather t.cols[c]! idx).size = 8 * idx.size := by
  rw [(gather_at t ht c hc idx hidx).1]; simp

theorem joinOutput_cols (l r : Table) (li ri : Array Nat) (sv : Option String) :
    (L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1 (L4Factoidal.Qlvr.joinVars l r).2
      li ri sv).cols =
      l.cols.map (gather · li) ++ (L4Factoidal.Qlvr.joinVars l r).2.map fun q => gather r.cols[q]! ri := rfl

/-- `Qlvr.joinOutput` of index arrays of rows of `l` and `r`: a well-formed
    table whose row `k` takes the left variables from row `li[k]` of `l`
    and the others from row `ri[k]` of `r`. -/
theorem joinOutput_spec (l r : Table) (hl : l.WF) (hr : r.WF) (li ri : Array Nat) (hsz : li.size = ri.size)
    (hli : ∀ i ∈ li.toList, i < l.rows) (hri : ∀ j ∈ ri.toList, j < r.rows) (sv : Option String) :
    let T := L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1 (L4Factoidal.Qlvr.joinVars l r).2
      li ri sv
    T.WF ∧ T.rows = li.size ∧ ∀ k, k < li.size → ∀ v, T.lookupAt k v =
      match l.idx v with
      | some c => nz (l.at c li[k]!)
      | none => r.lookupAt ri[k]! v := by
  intro T
  have hex := joinVars_extra l r
  have hvT : T.vars.toList = l.vars.toList ++ (L4Factoidal.Qlvr.joinVars l r).2.toList.map (fun q => r.vars[q]!) :=
    joinVars_vars l r
  have hlc : l.cols.size = l.vars.size := hl.cols_size
  have hcols : T.cols = l.cols.map (gather · li) ++ (L4Factoidal.Qlvr.joinVars l r).2.map fun q => gather r.cols[q]! ri :=
    joinOutput_cols l r li ri sv
  have hext : ∀ m, m < (L4Factoidal.Qlvr.joinVars l r).2.size → (L4Factoidal.Qlvr.joinVars l r).2[m]! < r.vars.size := by
    intro m hm
    have : (L4Factoidal.Qlvr.joinVars l r).2[m]! ∈ (L4Factoidal.Qlvr.joinVars l r).2.toList := by
      rw [arr_get _ m hm]; simp
    exact ((mem_extra hex).mp this).1
  have hcolL : ∀ c, c < l.vars.size → T.cols[c]! = gather l.cols[c]! li := by
    intro c hc
    rw [hcols, getElem!_pos _ c (by simp; omega), Array.getElem_append_left (by simp; omega)]
    simp [getElem!_pos l.cols c (by omega)]
  have hcolR : ∀ m, m < (L4Factoidal.Qlvr.joinVars l r).2.size →
      T.cols[l.vars.size + m]! = gather r.cols[(L4Factoidal.Qlvr.joinVars l r).2[m]!]! ri := by
    intro m hm
    rw [hcols, getElem!_pos _ _ (by simp; omega), Array.getElem_append_right (by simp; omega)]
    simp only [Array.getElem_map]
    rw [getElem!_pos (L4Factoidal.Qlvr.joinVars l r).2 m hm]
    simp [hlc]
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩
  · rw [hcols, ← Array.length_toList, ← Array.length_toList (xs := T.vars), hvT]; simp [hlc]
  · intro c hc
    have hc' : c < l.vars.size + (L4Factoidal.Qlvr.joinVars l r).2.size := by
      rw [hcols] at hc; simp at hc; omega
    have e := (getElem!_pos T.cols c hc).symm
    rw [e]
    show T.cols[c]!.size = 8 * li.size
    by_cases hcl : c < l.vars.size
    · rw [hcolL c hcl, gather_size l hl c hcl li hli]
    · have := hcolR (c - l.vars.size) (by omega)
      rw [show l.vars.size + (c - l.vars.size) = c by omega] at this
      rw [this, gather_size r hr _ (hext _ (by omega)) ri hri, hsz]
  · rw [hvT]; exact out_nodup l r _ hl.nodup hr.nodup hex
  · intro k hk v
    apply out_lookup l r T _ k ri[k]! (fun c => l.at c li[k]!) hl.nodup hr.nodup hvT hex
    · intro c hc
      show word64 T.cols[c]! (8 * k) = _
      rw [hcolL c hc, gather_word l hl c hc li hli k hk]
    · intro m hm
      show word64 T.cols[l.vars.size + m]! (8 * k) = _
      rw [hcolR m hm, gather_word r hr _ (hext m hm) ri hri k (by omega)]

/-- A row of `joinOutput` is the merge of its two rows when their shared
    columns hold the same ids. -/
theorem joinOutput_rowEq (l r : Table) (hl : l.WF) (hr : r.WF) (li ri : Array Nat) (hsz : li.size = ri.size)
    (hli : ∀ i ∈ li.toList, i < l.rows) (hri : ∀ j ∈ ri.toList, j < r.rows) (sv : Option String)
    (k : Nat) (hk : k < li.size)
    (hsh : ∀ p q, (p, q) ∈ L4Factoidal.Qlvr.sharedCols l r → l.at p li[k]! = r.at q ri[k]!) :
    RowEq ((L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1 (L4Factoidal.Qlvr.joinVars l r).2
      li ri sv).idRow k) (idMerge (l.idRow li[k]!) (r.idRow ri[k]!)) := by
  obtain ⟨hT, _, hlk⟩ := joinOutput_spec l r hl hr li ri hsz hli hri sv
  intro v
  rw [lookup_idRow _ hT.nodup, hlk k hk v, lookup_idMerge, lookup_idRow l hl.nodup,
    lookup_idRow r hr.nodup, lookupAt_eq l]
  cases hlv : l.idx v with
  | none => simp
  | some c =>
    simp only
    unfold nz
    by_cases h0 : l.at c li[k]! = unbound
    · simp only [h0, beq_self_eq_true, if_true, Option.none_or]
      rw [lookupAt_eq r]
      cases hrv : r.idx v with
      | none => rfl
      | some q =>
        obtain ⟨hc, hcv⟩ := idx_some hlv
        have := hsh c q (mem_sharedCols.mpr ⟨hc, by rw [hcv]; exact hrv⟩)
        simp only
        rw [← this, h0]; simp [nz]
    · have : (l.at c li[k]! == unbound) = false := by simpa using h0
      simp [this]

/-! ## Compatibility on tables -/

/-- No column of `t` holds `unbound` (the tables of triple pattern scans). -/
def NoUnbound (t : Table) : Prop := ∀ c i, c < t.vars.size → i < t.rows → t.at c i ≠ unbound

theorem lookupAt_some {t : Table} {i : Nat} {v : String} {y : UInt64} :
    t.lookupAt i v = some y ↔ ∃ q, t.idx v = some q ∧ t.at q i ≠ unbound ∧ t.at q i = y := by
  rw [lookupAt_eq]
  cases h : t.idx v with
  | none => simp
  | some q =>
    simp only [nz, Option.some.injEq, exists_eq_left']
    by_cases h0 : t.at q i = unbound
    · simp [h0]
    · have : (t.at q i == unbound) = false := by simpa using h0
      simp [this, h0]

/-- `IdJoin.compatAt` is the compatibility of the two rows. -/
theorem compatAt_iff (l r : Table) (hr : r.vars.toList.Nodup) (i j : Nat) :
    L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j =
      idCompatible (l.idRow i) (r.idRow j) := by
  apply Bool.eq_iff_iff.mpr
  rw [idCompatible_rows l r hr]
  unfold L4Factoidal.Storage.Sbm11.IdJoin.compatAt
  rw [Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h c hc hx y hy
    obtain ⟨q, hq, hq0, e⟩ := lookupAt_some.mp hy
    have := h (c, q) (mem_sharedCols.mpr ⟨hc, hq⟩)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with (h1 | h1) | h1
    · exact absurd h1 hx
    · exact absurd h1 hq0
    · rw [h1, e]
  · intro h pq hpq
    obtain ⟨p, q⟩ := pq
    obtain ⟨hp, hq⟩ := mem_sharedCols.mp hpq
    simp only [Bool.or_eq_true, beq_iff_eq]
    by_cases ha : l.at p i = unbound
    · exact Or.inl (Or.inl ha)
    by_cases hb : r.at q j = unbound
    · exact Or.inl (Or.inr hb)
    exact Or.inr (h p hp ha (r.at q j) (lookupAt_some.mpr ⟨q, hq, hb, rfl⟩))

/-- On tables with no `unbound` id, two rows are compatible exactly when
    their shared columns hold the same ids. -/
theorem compatible_iff_shared (l r : Table) (hr : r.vars.toList.Nodup) (hlu : NoUnbound l)
    (hru : NoUnbound r) (i j : Nat) (hi : i < l.rows) (hj : j < r.rows) :
    idCompatible (l.idRow i) (r.idRow j) = true ↔
      ∀ p q, (p, q) ∈ L4Factoidal.Qlvr.sharedCols l r → l.at p i = r.at q j := by
  rw [idCompatible_rows l r hr]
  constructor
  · intro h p q hpq
    obtain ⟨hp, hq⟩ := mem_sharedCols.mp hpq
    have hqs := (idx_some hq).1
    exact h p hp (hlu p i hp hi) (r.at q j) (lookupAt_some.mpr ⟨q, hq, hru q j hqs hj, rfl⟩)
  · intro h c hc _ y hy
    obtain ⟨q, hq, _, e⟩ := lookupAt_some.mp hy
    rw [← e]; exact h c q (mem_sharedCols.mpr ⟨hc, hq⟩)

/-! ## `idJoin` over index pairs -/

open L4Factoidal.Storage.Sbm11.OptJoin (innerSpec innerFrom rowsOf)

theorem mem_innerSpec {nl nr : Nat} {cand : Nat → Nat → Bool} {i j : Nat} :
    (i, j) ∈ innerSpec nl nr cand ↔ i < nl ∧ j < nr ∧ cand i j = true := by
  unfold innerSpec innerFrom rowsOf
  simp only [List.mem_flatMap, List.mem_range', List.mem_map, List.mem_filter, List.mem_range,
    Prod.mk.injEq, Nat.sub_zero]
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, y, ⟨hy, hc⟩, rfl, rfl⟩
    exact ⟨by omega, hy, by simpa using hc⟩
  · rintro ⟨hi, hj, hc⟩
    exact ⟨i, ⟨i, hi, by omega⟩, j, ⟨hj, hc⟩, rfl, rfl⟩

theorem innerSpec_congr (nl nr : Nat) (c1 c2 : Nat → Nat → Bool)
    (h : ∀ i j, i < nl → j < nr → c1 i j = c2 i j) : innerSpec nl nr c1 = innerSpec nl nr c2 := by
  unfold innerSpec innerFrom rowsOf
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x hx
  congr 1
  apply List.filter_congr
  intro y hy
  simp at hx hy
  exact h x y (by omega) hy

/-- `idJoin` is the merge of each pair of `innerSpec` with id compatibility
    as the candidate relation. -/
theorem idJoin_eq_innerSpec (L R : List IdRow) :
    L4Factoidal.Storage.Sbm11.IdJoin.idJoin L R =
      (innerSpec L.length R.length fun i j => idCompatible L[i]! R[j]!).map fun p => idMerge L[p.1]! R[p.2]! := by
  unfold L4Factoidal.Storage.Sbm11.IdJoin.idJoin innerSpec innerFrom
  rw [L4Factoidal.Storage.Sbm11.OptJoin.flatMap_range' _ L 0 [] rfl, List.map_flatMap, Nat.sub_zero]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro i _
  simp only [List.nil_append]
  have e := L4Factoidal.Storage.Sbm11.OptJoin.filterMap_range' (idCompatible L[i]!) (idMerge L[i]!) R 0 [] rfl
  simp only [List.nil_append] at e
  rw [e, rowsOf, List.range_eq_range', List.map_map]
  rfl

theorem idRows_length (t : Table) : t.idRows.length = t.rows := by simp [Table.idRows]

theorem idRows_get (t : Table) (i : Nat) (hi : i < t.rows) : t.idRows[i]! = t.idRow i := by
  rw [getElem!_pos t.idRows i (by rw [idRows_length]; exact hi)]
  simp [Table.idRows]

/-- `idJoin` of the rows of two tables over row indices. -/
theorem idJoin_rows (l r : Table) :
    L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows =
      (innerSpec l.rows r.rows fun i j => idCompatible (l.idRow i) (r.idRow j)).map
        fun p => idMerge (l.idRow p.1) (r.idRow p.2) := by
  rw [idJoin_eq_innerSpec, idRows_length, idRows_length]
  rw [innerSpec_congr l.rows r.rows _ (fun i j => idCompatible (l.idRow i) (r.idRow j))
    (fun i j hi hj => by rw [idRows_get l i hi, idRows_get r j hj])]
  apply List.map_congr_left
  intro p hp
  obtain ⟨i, j⟩ := p
  obtain ⟨hi, hj, _⟩ := mem_innerSpec.mp hp
  simp only
  rw [idRows_get l i hi, idRows_get r j hj]

/-! ## Hash index loops -/

theorem forIn_range_inv {β : Type} (n : Nat) (P : Nat → β → Prop) {f : Nat → β → _root_.Id (ForInStep β)}
    {b : β} {F : _root_.Id β} (hF : forIn (List.range' 0 n) b f = F) (h0 : P 0 b)
    (hs : ∀ k b, k < n → P k b → ∃ b', (f k b).run = .yield b' ∧ P (k + 1) b') : P n F.run := by
  have := forIn_list_inv (List.range' 0 n) P hF h0 (fun k b hk h => by
    simp only [List.length_range'] at hk
    simpa [List.getElem_range'] using hs k b hk h)
  simpa using this

theorem range'_succ_filter (n : Nat) (p : Nat → Bool) :
    (List.range' 0 (n + 1)).filter p = (List.range' 0 n).filter p ++ (if p n then [n] else []) := by
  rw [List.range'_concat, List.filter_append]
  simp only [Nat.zero_add, Nat.one_mul]
  by_cases h : p n <;> simp [h]

theorem getD_alter_push {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] (hm : Std.HashMap κ (Array Nat))
    (k k' : κ) (j : Nat) (f : Option (Array Nat) → Option (Array Nat))
    (hf : ∀ o, f o = some ((o.getD #[]).push j)) :
    (hm.alter k f).getD k' #[] = if k == k' then (hm.getD k' #[]).push j else hm.getD k' #[] := by
  rw [Std.HashMap.getD_alter]
  by_cases e : k = k'
  · subst e; simp [hf, Std.HashMap.getD_eq_getD_getElem?]
  · have : (k == k') = false := by simpa using e
    simp [this]

/-- The hash index built by `alter` with a push for rows `0 .. n-1`: the
    bucket of a key holds the rows with that key, in order. -/
theorem build_spec {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] (K : Nat → κ)
    (g : Nat → Option (Array Nat) → Option (Array Nat)) (hg : ∀ j o, g j o = some ((o.getD #[]).push j))
    (n : Nat) {H : _root_.Id (Std.HashMap κ (Array Nat))}
    (hH : forIn (List.range' 0 n) (∅ : Std.HashMap κ (Array Nat))
      (fun j s => pure (.yield (s.alter (K j) (g j)))) = H) :
    ∀ k, (H.run.getD k #[]).toList = (List.range' 0 n).filter (fun j => K j == k) := by
  apply forIn_range_inv n (fun m (s : Std.HashMap κ (Array Nat)) =>
    ∀ k, (s.getD k #[]).toList = (List.range' 0 m).filter (fun j => K j == k)) hH
  · intro k; simp [Std.HashMap.getD_empty]
  · intro m s _ hs
    refine ⟨_, rfl, fun k => ?_⟩
    rw [Std.HashMap.getD_alter, range'_succ_filter, ← hs k]
    by_cases e : K m = k
    · subst e
      simp [hg, Std.HashMap.getD_eq_getD_getElem?]
    · have : (K m == k) = false := by simpa using e
      simp [this]

/-- The probe loop of a hash join, left rows outside: per left row `i` in
    order, the pairs `(i, j)` of its bucket. -/
theorem probe_spec (B : Nat → Array Nat) (n : Nat) {F : _root_.Id (Array Nat × Array Nat)}
    (hF : forIn (List.range' 0 n) ((#[], #[]) : Array Nat × Array Nat) (fun i s1 => do
      let s ← forIn (B i) (s1.1, s1.2) (fun j (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push j)))
      pure (.yield (s.1, s.2))) = F) :
    F.run.1.toList = ((List.range' 0 n).flatMap fun i => (B i).toList.map fun j => (i, j)).map Prod.fst ∧
      F.run.2.toList = ((List.range' 0 n).flatMap fun i => (B i).toList.map fun j => (i, j)).map Prod.snd := by
  apply forIn_range_inv n (fun m (s : Array Nat × Array Nat) =>
    s.1.toList = ((List.range' 0 m).flatMap fun i => (B i).toList.map fun j => (i, j)).map Prod.fst ∧
    s.2.toList = ((List.range' 0 m).flatMap fun i => (B i).toList.map fun j => (i, j)).map Prod.snd) hF
  · simp
  · intro m s _ ⟨h1, h2⟩
    have inner : ∀ (xs : List Nat) (a b : Array Nat),
        forIn (m := _root_.Id) xs (a, b) (fun j (s : Array Nat × Array Nat) => pure (.yield (s.1.push m, s.2.push j))) =
          ((⟨a.toList ++ xs.map (fun _ => m)⟩, ⟨b.toList ++ xs⟩) : Array Nat × Array Nat) := by
      intro xs
      induction xs with
      | nil => intro a b; simp; rfl
      | cons x xs ih =>
        intro a b
        rw [List.forIn_cons]
        simp only [pure_bind]
        rw [ih]; simp
    refine ⟨_, rfl, ?_⟩
    rw [← Array.forIn_toList]
    erw [inner]
    simp only [List.range'_concat, Nat.zero_add, Nat.one_mul, List.flatMap_append, List.map_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, ← h1, ← h2, List.map_map]
    exact ⟨rfl, by simp [Function.comp_def]⟩

/-- The probe loop with the right rows outside: per right row `j` in order,
    the pairs `(i, j)` of its bucket. -/
theorem probeR_spec (B : Nat → Array Nat) (n : Nat) {F : _root_.Id (Array Nat × Array Nat)}
    (hF : forIn (List.range' 0 n) ((#[], #[]) : Array Nat × Array Nat) (fun j s1 => do
      let s ← forIn (B j) (s1.1, s1.2) (fun i (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push j)))
      pure (.yield (s.1, s.2))) = F) :
    F.run.1.toList = ((List.range' 0 n).flatMap fun j => (B j).toList.map fun i => (i, j)).map Prod.fst ∧
      F.run.2.toList = ((List.range' 0 n).flatMap fun j => (B j).toList.map fun i => (i, j)).map Prod.snd := by
  apply forIn_range_inv n (fun m (s : Array Nat × Array Nat) =>
    s.1.toList = ((List.range' 0 m).flatMap fun j => (B j).toList.map fun i => (i, j)).map Prod.fst ∧
    s.2.toList = ((List.range' 0 m).flatMap fun j => (B j).toList.map fun i => (i, j)).map Prod.snd) hF
  · simp
  · intro m s _ ⟨h1, h2⟩
    have inner : ∀ (xs : List Nat) (a b : Array Nat),
        forIn (m := _root_.Id) xs (a, b) (fun i (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push m))) =
          ((⟨a.toList ++ xs⟩, ⟨b.toList ++ xs.map (fun _ => m)⟩) : Array Nat × Array Nat) := by
      intro xs
      induction xs with
      | nil => intro a b; simp; rfl
      | cons x xs ih =>
        intro a b
        rw [List.forIn_cons]
        simp only [pure_bind]
        rw [ih]; simp
    refine ⟨_, rfl, ?_⟩
    rw [← Array.forIn_toList]
    erw [inner]
    simp only [List.range'_concat, Nat.zero_add, Nat.one_mul, List.flatMap_append, List.map_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, ← h1, ← h2, List.map_map]
    exact ⟨by simp [Function.comp_def], rfl⟩

/-- A hash join loop pair: build an index of rows `0 .. nb-1` keyed by `KB`,
    then probe it with rows `0 .. np-1` keyed by `KP`, probe rows outside. -/
theorem hash_branch {κ β : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] (KB KP : Nat → κ)
    (g : Nat → Option (Array Nat) → Option (Array Nat)) (hg : ∀ j o, g j o = some ((o.getD #[]).push j))
    (nb np : Nat) (out : Array Nat → Array Nat → β) :
    ∃ li ri : Array Nat, (do
      let hm ← forIn (List.range' 0 nb) (∅ : Std.HashMap κ (Array Nat)) (fun j s => pure (.yield (s.alter (KB j) (g j))))
      let s ← forIn (List.range' 0 np) ((#[], #[]) : Array Nat × Array Nat) (fun i s1 => do
        let s ← forIn (hm.getD (KP i) #[]) (s1.1, s1.2)
          (fun j (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push j)))
        pure (.yield (s.1, s.2)))
      pure (out s.1 s.2) : _root_.Id β) = out li ri ∧
    li.toList = ((List.range' 0 np).flatMap fun i =>
      ((List.range' 0 nb).filter fun j => KB j == KP i).map fun j => (i, j)).map Prod.fst ∧
    ri.toList = ((List.range' 0 np).flatMap fun i =>
      ((List.range' 0 nb).filter fun j => KB j == KP i).map fun j => (i, j)).map Prod.snd := by
  let H := (forIn (List.range' 0 nb) (∅ : Std.HashMap κ (Array Nat))
    (fun j s => pure (.yield (s.alter (KB j) (g j)))) : _root_.Id _)
  let F := (forIn (List.range' 0 np) ((#[], #[]) : Array Nat × Array Nat) (fun i s1 => do
        let s ← forIn (H.run.getD (KP i) #[]) (s1.1, s1.2)
          (fun j (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push j)))
        pure (.yield (s.1, s.2))) : _root_.Id _)
  refine ⟨F.run.1, F.run.2, rfl, ?_⟩
  have hb := build_spec KB g hg nb (H := H) rfl
  obtain ⟨h1, h2⟩ := probe_spec (fun i => H.run.getD (KP i) #[]) np (F := F) rfl
  simp only [hb] at h1 h2
  exact ⟨h1, h2⟩

/-- The same, right rows outside: the index is on the left rows. -/
theorem hash_branchR {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] (KB KP : Nat → κ)
    (g : Nat → Option (Array Nat) → Option (Array Nat)) (hg : ∀ j o, g j o = some ((o.getD #[]).push j))
    (nb np : Nat) (out : Array Nat → Array Nat → Table) :
    ∃ li ri : Array Nat, (do
      let hm ← forIn (List.range' 0 nb) (∅ : Std.HashMap κ (Array Nat)) (fun i s => pure (.yield (s.alter (KB i) (g i))))
      let s ← forIn (List.range' 0 np) ((#[], #[]) : Array Nat × Array Nat) (fun j s1 => do
        let s ← forIn (hm.getD (KP j) #[]) (s1.1, s1.2)
          (fun i (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push j)))
        pure (.yield (s.1, s.2)))
      pure (out s.1 s.2) : _root_.Id Table) = out li ri ∧
    li.toList = ((List.range' 0 np).flatMap fun j =>
      ((List.range' 0 nb).filter fun i => KB i == KP j).map fun i => (i, j)).map Prod.fst ∧
    ri.toList = ((List.range' 0 np).flatMap fun j =>
      ((List.range' 0 nb).filter fun i => KB i == KP j).map fun i => (i, j)).map Prod.snd := by
  let H := (forIn (List.range' 0 nb) (∅ : Std.HashMap κ (Array Nat))
    (fun i s => pure (.yield (s.alter (KB i) (g i)))) : _root_.Id _)
  let F := (forIn (List.range' 0 np) ((#[], #[]) : Array Nat × Array Nat) (fun j s1 => do
        let s ← forIn (H.run.getD (KP j) #[]) (s1.1, s1.2)
          (fun i (s : Array Nat × Array Nat) => pure (.yield (s.1.push i, s.2.push j)))
        pure (.yield (s.1, s.2))) : _root_.Id _)
  refine ⟨F.run.1, F.run.2, rfl, ?_⟩
  have hb := build_spec KB g hg nb (H := H) rfl
  obtain ⟨h1, h2⟩ := probeR_spec (fun j => H.run.getD (KP j) #[]) np (F := F) rfl
  simp only [hb] at h1 h2
  exact ⟨h1, h2⟩

/-! ## `Qlvr.hashJoin` -/

/-- The shared columns of row `i` of `l` and row `j` of `r` hold the same
    ids. -/
def shEq (l r : Table) (i j : Nat) : Bool :=
  (L4Factoidal.Qlvr.sharedCols l r).all fun pq => l.at pq.1 i == r.at pq.2 j

/-- The pairs `(i, j)` with `cand i j`, right row outside. -/
def innerSpecR (nl nr : Nat) (cand : Nat → Nat → Bool) : List (Nat × Nat) :=
  (List.range' 0 nr).flatMap fun j => ((List.range' 0 nl).filter fun i => cand i j).map fun i => (i, j)

theorem innerSpec_eq (nl nr : Nat) (cand : Nat → Nat → Bool) :
    innerSpec nl nr cand =
      (List.range' 0 nl).flatMap fun i => ((List.range' 0 nr).filter fun j => cand i j).map fun j => (i, j) := by
  unfold innerSpec innerFrom rowsOf
  rw [Nat.sub_zero, List.range_eq_range']

theorem all_single {α : Type} (a : Array α) (h : a.size = 1) (f : α → Bool) :
    a.all f = f (a[0]'(by omega)) := by
  have : a = #[a[0]'(by omega)] := by
    apply Array.ext
    · simp [h]
    · intro i h1 _
      have : i = 0 := by omega
      subst this; simp
  conv => lhs; rw [this]
  simp

theorem beq_comm' (a b : UInt64) : (a == b) = (b == a) := by
  cases h : a == b <;> cases h' : b == a <;> simp_all

theorem list_beq_comm (a b : List UInt64) : (a == b) = (b == a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem shEq_single (l r : Table) (h : (L4Factoidal.Qlvr.sharedCols l r).size = 1) (i j : Nat) :
    shEq l r i j = (r.at ((L4Factoidal.Qlvr.sharedCols l r)[0]'(by omega)).2 j ==
      l.at ((L4Factoidal.Qlvr.sharedCols l r)[0]'(by omega)).1 i) := by
  unfold shEq; rw [all_single _ h, beq_comm']

theorem shEq_list (l r : Table) (i j : Nat) :
    shEq l r i j = (((L4Factoidal.Qlvr.sharedCols l r).map fun x => r.at x.2 j).toList ==
      ((L4Factoidal.Qlvr.sharedCols l r).map fun x => l.at x.1 i).toList) := by
  unfold shEq
  apply Bool.eq_iff_iff.mpr
  rw [Array.all_eq_true_iff_forall_mem, beq_iff_eq, Array.toList_map, Array.toList_map, List.map_inj_left]
  simp only [Array.mem_toList_iff, beq_iff_eq]
  exact ⟨fun h x hx => (h x hx).symm, fun h x hx => (h x hx).symm⟩

/-- The index arrays `Qlvr.hashJoin` builds its output from: the pairs of
    rows whose shared columns hold the same ids, left rows outside when the
    right table is not larger, else right rows outside. -/
theorem hashJoin_pairs (l r : Table) :
    ∃ li ri sv, L4Factoidal.Qlvr.hashJoin l r =
      L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1 (L4Factoidal.Qlvr.joinVars l r).2 li ri sv ∧
      ((r.rows ≤ l.rows ∧ li.toList = (innerSpec l.rows r.rows (shEq l r)).map Prod.fst ∧
          ri.toList = (innerSpec l.rows r.rows (shEq l r)).map Prod.snd) ∨
        (¬ r.rows ≤ l.rows ∧ li.toList = (innerSpecR l.rows r.rows (shEq l r)).map Prod.fst ∧
          ri.toList = (innerSpecR l.rows r.rows (shEq l r)).map Prod.snd)) := by
  unfold L4Factoidal.Qlvr.hashJoin
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  by_cases hle : r.rows ≤ l.rows
  · rw [if_pos hle]
    by_cases h1 : (L4Factoidal.Qlvr.sharedCols l r).size = 1
    · rw [dif_pos h1]
      obtain ⟨li, ri, he, e1, e2⟩ := hash_branch
        (fun j => r.at ((L4Factoidal.Qlvr.sharedCols l r)[0]'(by omega)).2 j)
        (fun i => l.at ((L4Factoidal.Qlvr.sharedCols l r)[0]'(by omega)).1 i)
        (fun j x => match x with
          | some a => some (a.push j)
          | none => some #[j]) (by intro j o; cases o <;> rfl) r.rows l.rows
        (fun li ri => L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
          (L4Factoidal.Qlvr.joinVars l r).2 li ri l.sortVar)
      refine ⟨li, ri, l.sortVar, he, Or.inl ⟨hle, ?_, ?_⟩⟩
      all_goals
        rw [innerSpec_eq]
        first | rw [e1] | rw [e2]
        congr 2
        funext i
        congr 1
        apply List.filter_congr
        intro j _
        rw [shEq_single l r h1]
    · rw [dif_neg h1]
      obtain ⟨li, ri, he, e1, e2⟩ := hash_branch
        (fun j => ((L4Factoidal.Qlvr.sharedCols l r).map fun x => r.at x.2 j).toList)
        (fun i => ((L4Factoidal.Qlvr.sharedCols l r).map fun x => l.at x.1 i).toList)
        (fun j x => match x with
          | some a => some (a.push j)
          | none => some #[j]) (by intro j o; cases o <;> rfl) r.rows l.rows
        (fun li ri => L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
          (L4Factoidal.Qlvr.joinVars l r).2 li ri l.sortVar)
      refine ⟨li, ri, l.sortVar, he, Or.inl ⟨hle, ?_, ?_⟩⟩
      all_goals
        rw [innerSpec_eq]
        first | rw [e1] | rw [e2]
        congr 2
        funext i
        congr 1
        apply List.filter_congr
        intro j _
        rw [shEq_list l r]
  · rw [if_neg hle]
    by_cases h1 : (L4Factoidal.Qlvr.sharedCols l r).size = 1
    · rw [dif_pos h1]
      obtain ⟨li, ri, he, e1, e2⟩ := hash_branchR
        (fun i => l.at ((L4Factoidal.Qlvr.sharedCols l r)[0]'(by omega)).1 i)
        (fun j => r.at ((L4Factoidal.Qlvr.sharedCols l r)[0]'(by omega)).2 j)
        (fun j x => match x with
          | some a => some (a.push j)
          | none => some #[j]) (by intro j o; cases o <;> rfl) l.rows r.rows
        (fun li ri => L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
          (L4Factoidal.Qlvr.joinVars l r).2 li ri
          (match r.sortVar with
           | some v => if (l.vars.contains v || r.vars.contains v) = true then some v else none
           | none => none))
      refine ⟨li, ri, _, he, Or.inr ⟨hle, ?_, ?_⟩⟩
      all_goals
        unfold innerSpecR
        first | rw [e1] | rw [e2]
        congr 2
        funext j
        congr 1
        apply List.filter_congr
        intro i _
        rw [shEq_single l r h1, beq_comm']
    · rw [dif_neg h1]
      obtain ⟨li, ri, he, e1, e2⟩ := hash_branchR
        (fun i => ((L4Factoidal.Qlvr.sharedCols l r).map fun x => l.at x.1 i).toList)
        (fun j => ((L4Factoidal.Qlvr.sharedCols l r).map fun x => r.at x.2 j).toList)
        (fun j x => match x with
          | some a => some (a.push j)
          | none => some #[j]) (by intro j o; cases o <;> rfl) l.rows r.rows
        (fun li ri => L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
          (L4Factoidal.Qlvr.joinVars l r).2 li ri
          (match r.sortVar with
           | some v => if (l.vars.contains v || r.vars.contains v) = true then some v else none
           | none => none))
      refine ⟨li, ri, _, he, Or.inr ⟨hle, ?_, ?_⟩⟩
      all_goals
        unfold innerSpecR
        first | rw [e1] | rw [e2]
        congr 2
        funext j
        congr 1
        apply List.filter_congr
        intro i _
        rw [shEq_list l r, list_beq_comm]

/-- `joinOutput` of the pairs `P` (each of a row of `l` and a row of `r`
    whose shared columns hold the same ids): a well-formed table whose rows
    are the merges of the pairs, in order. -/
theorem joinOutput_rows (l r : Table) (hl : l.WF) (hr : r.WF) (li ri : Array Nat) (P : List (Nat × Nat))
    (h1 : li.toList = P.map Prod.fst) (h2 : ri.toList = P.map Prod.snd)
    (hP : ∀ p ∈ P, p.1 < l.rows ∧ p.2 < r.rows ∧
      ∀ a b, (a, b) ∈ L4Factoidal.Qlvr.sharedCols l r → l.at a p.1 = r.at b p.2)
    (sv : Option String) :
    (L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1 (L4Factoidal.Qlvr.joinVars l r).2
      li ri sv).WF ∧
    RowsEq (L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1 (L4Factoidal.Qlvr.joinVars l r).2
      li ri sv).idRows (P.map fun p => idMerge (l.idRow p.1) (r.idRow p.2)) := by
  have hls : li.size = P.length := by rw [← Array.length_toList, h1, List.length_map]
  have hrs : ri.size = P.length := by rw [← Array.length_toList, h2, List.length_map]
  have hli : ∀ i ∈ li.toList, i < l.rows := by
    intro i hi; rw [h1] at hi
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hi; rw [← e]; exact (hP p hp).1
  have hri : ∀ j ∈ ri.toList, j < r.rows := by
    intro j hj; rw [h2] at hj
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hj; rw [← e]; exact (hP p hp).2.1
  obtain ⟨hT, hrows, _⟩ := joinOutput_spec l r hl hr li ri (by omega) hli hri sv
  refine ⟨hT, ?_, ?_⟩
  · rw [idRows_length, hrows, hls, List.length_map]
  · intro k hk1 hk2
    have hk : k < P.length := by simpa using hk2
    have ek1 : li[k]! = P[k].1 := by
      rw [arr_get li k (by omega)]; simp only [h1, List.getElem_map]
    have ek2 : ri[k]! = P[k].2 := by
      rw [arr_get ri k (by omega)]; simp only [h2, List.getElem_map]
    have hrow : (L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
        (L4Factoidal.Qlvr.joinVars l r).2 li ri sv).idRows[k] =
        (L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
        (L4Factoidal.Qlvr.joinVars l r).2 li ri sv).idRow k := by
      simp [Table.idRows]
    rw [hrow, List.getElem_map]
    have := joinOutput_rowEq l r hl hr li ri (by omega) hli hri sv k (by omega)
      (fun a b hab => by rw [ek1, ek2]; exact (hP P[k] (List.getElem_mem hk)).2.2 a b hab)
    rw [ek1, ek2] at this
    exact this

theorem mem_innerSpecR {nl nr : Nat} {cand : Nat → Nat → Bool} {i j : Nat} :
    (i, j) ∈ innerSpecR nl nr cand ↔ i < nl ∧ j < nr ∧ cand i j = true := by
  unfold innerSpecR
  simp only [List.mem_flatMap, List.mem_range', List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, x, ⟨⟨k', hk', rfl⟩, hc⟩, rfl, rfl⟩
    exact ⟨by omega, by omega, hc⟩
  · rintro ⟨hi, hj, hc⟩
    exact ⟨j, ⟨j, hj, by omega⟩, i, ⟨⟨i, hi, by omega⟩, hc⟩, rfl, rfl⟩

theorem nodup_pairsL (xs : List Nat) (f : Nat → List Nat) (hxs : xs.Nodup) (hf : ∀ x, (f x).Nodup) :
    (xs.flatMap fun i => (f i).map fun j => (i, j)).Nodup := by
  rw [List.Nodup, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (hf i).imp fun h e => h (by simp at e; exact e)
  · apply hxs.imp
    intro a b hab x hx y hy e
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    simp at e; exact hab e.1

theorem nodup_pairsR (xs : List Nat) (f : Nat → List Nat) (hxs : xs.Nodup) (hf : ∀ x, (f x).Nodup) :
    (xs.flatMap fun j => (f j).map fun i => (i, j)).Nodup := by
  rw [List.Nodup, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (hf i).imp fun h e => h (by simp at e; exact e)
  · apply hxs.imp
    intro a b hab x hx y hy e
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    simp at e; exact hab e.2

theorem nodup_range'_filter (s n : Nat) (p : Nat → Bool) : ((List.range' s n).filter p).Nodup :=
  (List.nodup_range').filter p

/-- The right-outside order is a permutation of the left-outside order. -/
theorem innerSpecR_perm (nl nr : Nat) (cand : Nat → Nat → Bool) :
    (innerSpecR nl nr cand).Perm (innerSpec nl nr cand) := by
  rw [List.perm_ext_iff_of_nodup]
  · intro p
    obtain ⟨i, j⟩ := p
    rw [mem_innerSpecR, mem_innerSpec]
  · exact nodup_pairsR _ _ List.nodup_range' (fun j => nodup_range'_filter _ _ _)
  · rw [innerSpec_eq]; exact nodup_pairsL _ _ List.nodup_range' (fun i => nodup_range'_filter _ _ _)

theorem shEq_iff (l r : Table) (i j : Nat) :
    shEq l r i j = true ↔ ∀ a b, (a, b) ∈ L4Factoidal.Qlvr.sharedCols l r → l.at a i = r.at b j := by
  unfold shEq
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [beq_iff_eq]
  exact ⟨fun h a b hab => h (a, b) hab, fun h pq hpq => h pq.1 pq.2 hpq⟩

/-- **L5b.** `Qlvr.hashJoin` of two well-formed tables with no `unbound`
    id denotes SPARQL 1.1 Join of their rows (`IdJoin.idJoin`) as a
    multiset: its rows are, in order, a permutation of the rows of
    `idJoin`, each as the same solution mapping. When the right table is
    not larger than the left one (index on the right, left rows outside),
    the rows are those of `idJoin` in the same order. -/
theorem hashJoin_rows (l r : Table) (hl : l.WF) (hr : r.WF) (hlu : NoUnbound l) (hru : NoUnbound r) :
    (L4Factoidal.Qlvr.hashJoin l r).WF ∧
    ∃ M, M.Perm (L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows) ∧
      RowsEq (L4Factoidal.Qlvr.hashJoin l r).idRows M ∧
      (r.rows ≤ l.rows → M = L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows) := by
  have hcand : ∀ i j, i < l.rows → j < r.rows →
      shEq l r i j = idCompatible (l.idRow i) (r.idRow j) := by
    intro i j hi hj
    apply Bool.eq_iff_iff.mpr
    rw [shEq_iff, compatible_iff_shared l r hr.nodup hlu hru i j hi hj]
  have hJ : L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows =
      (innerSpec l.rows r.rows (shEq l r)).map fun p => idMerge (l.idRow p.1) (r.idRow p.2) := by
    rw [idJoin_rows, innerSpec_congr l.rows r.rows _ _ (fun i j hi hj => (hcand i j hi hj).symm)]
  obtain ⟨li, ri, sv, he, hcase⟩ := hashJoin_pairs l r
  rw [he]
  rcases hcase with ⟨hle, h1, h2⟩ | ⟨hle, h1, h2⟩
  · obtain ⟨hT, hR⟩ := joinOutput_rows l r hl hr li ri _ h1 h2 (fun p hp => by
      obtain ⟨i, j⟩ := p
      obtain ⟨hi, hj, hc⟩ := mem_innerSpec.mp hp
      exact ⟨hi, hj, (shEq_iff l r i j).mp hc⟩) sv
    exact ⟨hT, _, by rw [hJ], hR, fun _ => hJ.symm⟩
  · obtain ⟨hT, hR⟩ := joinOutput_rows l r hl hr li ri _ h1 h2 (fun p hp => by
      obtain ⟨i, j⟩ := p
      obtain ⟨hi, hj, hc⟩ := mem_innerSpecR.mp hp
      exact ⟨hi, hj, (shEq_iff l r i j).mp hc⟩) sv
    exact ⟨hT, _, by rw [hJ]; exact (innerSpecR_perm _ _ _).map _, hR, fun h => absurd h hle⟩

/-! ## `IdJoin.joinPairs` -/

theorem id_bind {α β : Type} (x : _root_.Id α) (f : α → _root_.Id β) : x >>= f = f x.run := rfl

theorem lt_of_pairwise {a : Array Nat} (h : a.toList.Pairwise (· < ·)) :
    ∀ k k', k < k' → k' < a.size → a[k]! < a[k']! := by
  intro k k' hk hk'
  rw [arr_get a k (by omega), arr_get a k' hk']
  exact List.pairwise_iff_getElem.mp h k k' _ _ hk

theorem mem_of_get {a : Array Nat} {k : Nat} (hk : k < a.size) : a[k]! ∈ a.toList := by
  rw [arr_get a k hk]; simp

/-- The inner probe loop with a test: the pairs `(i, j)`, `j` in `xs` in
    order, that pass `c`. -/
theorem probe_filter (i : Nat) (c : Nat → Bool) : ∀ (xs : List Nat) (a b : Array Nat),
    forIn (m := _root_.Id) xs (a, b) (fun j (s : Array Nat × Array Nat) =>
      if c j = true then pure (.yield (s.1.push i, s.2.push j)) else pure (.yield (s.1, s.2))) =
      ((⟨a.toList ++ (xs.filter c).map (fun _ => i)⟩, ⟨b.toList ++ xs.filter c⟩) : Array Nat × Array Nat) := by
  intro xs
  induction xs with
  | nil => intro a b; simp; rfl
  | cons x xs ih =>
    intro a b
    rw [List.forIn_cons]
    by_cases hc : c x = true
    · simp only [hc, if_true, pure_bind]
      rw [ih]; simp [hc]
    · simp only [hc, Bool.false_eq_true, if_false, pure_bind]
      rw [ih]; simp [hc]

/-- **The pairs of `IdJoin.joinPairs`.** For any shared columns, the pairs
    `(i, j)` whose rows pass `compatAt`, in the order of `i`, then `j`
    (`innerSpec`): the hash bucket and the rows with an unbound shared
    column, merged in order (`mergeIdx`), hold every compatible row of a
    left row whose shared columns are bound. -/
theorem joinPairs_spec (l r : Table) (shared : Array (Nat × Nat)) :
    (L4Factoidal.Storage.Sbm11.IdJoin.joinPairs l r shared).1.toList =
        (innerSpec l.rows r.rows (L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r shared)).map Prod.fst ∧
      (L4Factoidal.Storage.Sbm11.IdJoin.joinPairs l r shared).2.toList =
        (innerSpec l.rows r.rows (L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r shared)).map Prod.snd := by
  let KR : Nat → List UInt64 := fun j => (shared.map fun x => r.at x.2 j).toList
  let KL : Nat → List UInt64 := fun i => (shared.map fun x => l.at x.1 i).toList
  let bnd : Nat → Bool := fun j => (KR j).all (· != unbound)
  let cmp := L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r shared
  unfold L4Factoidal.Storage.Sbm11.IdJoin.joinPairs
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hB : forIn (m := _root_.Id) (List.range' 0 r.rows)
    ((∅ : Std.HashMap (List UInt64) (Array Nat)), (#[] : Array Nat)) _ = B
  have hb := forIn_range_inv r.rows (fun m (s : Std.HashMap (List UInt64) (Array Nat) × Array Nat) =>
      (∀ k, (s.1.getD k #[]).toList = (List.range' 0 m).filter (fun j => bnd j && KR j == k)) ∧
      s.2.toList = (List.range' 0 m).filter (fun j => !bnd j)) hB
    ⟨fun k => by simp [Std.HashMap.getD_empty], by simp⟩ (by
      intro m s _ ⟨h1, h2⟩
      by_cases hc : bnd m = true
      · refine ⟨(s.1.alter (KR m) fun x => match x with
            | some a => some (a.push m)
            | none => some #[m], s.2), ?_, fun k => ?_, ?_⟩
        · simp only [bnd, KR] at hc
          rw [if_pos hc]; rfl
        · rw [getD_alter_push _ _ _ m _ (by intro o; cases o <;> rfl), range'_succ_filter, ← h1 k]
          by_cases e : KR m = k
          · simp [hc, e]
          · simp [e]
        · rw [range'_succ_filter, ← h2]; simp [hc]
      · refine ⟨(s.1, s.2.push m), ?_, fun k => ?_, ?_⟩
        · simp only [bnd, KR] at hc
          rw [if_neg hc]; rfl
        · rw [h1 k, range'_succ_filter]; simp [hc]
        · rw [range'_succ_filter, Array.toList_push, h2]; simp [hc])
  obtain ⟨hb1, hb2⟩ := hb
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 l.rows) ((#[] : Array Nat), (#[] : Array Nat)) _ = F
  rw [id_bind]
  show F.run.1.toList = _ ∧ F.run.2.toList = _
  rw [innerSpec_eq]
  apply forIn_range_inv l.rows (fun m (s : Array Nat × Array Nat) =>
    s.1.toList = ((List.range' 0 m).flatMap fun i => ((List.range' 0 r.rows).filter (cmp i)).map fun j => (i, j)).map Prod.fst ∧
    s.2.toList = ((List.range' 0 m).flatMap fun i => ((List.range' 0 r.rows).filter (cmp i)).map fun j => (i, j)).map Prod.snd) hF
  · simp
  · intro m s _ ⟨h1, h2⟩
    have hnext : ∀ (xs : List Nat), xs = (List.range' 0 r.rows).filter (cmp m) →
        ((⟨s.1.toList ++ xs.map (fun _ => m)⟩ : Array Nat).toList =
          ((List.range' 0 (m + 1)).flatMap fun i => ((List.range' 0 r.rows).filter (cmp i)).map fun j => (i, j)).map Prod.fst ∧
        (⟨s.2.toList ++ xs⟩ : Array Nat).toList =
          ((List.range' 0 (m + 1)).flatMap fun i => ((List.range' 0 r.rows).filter (cmp i)).map fun j => (i, j)).map Prod.snd) := by
      intro xs hxs
      subst hxs
      simp only [List.range'_concat, Nat.zero_add, Nat.one_mul, List.flatMap_append, List.map_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, ← h1, ← h2, List.map_map]
      exact ⟨by simp [Function.comp_def], by simp [Function.comp_def]⟩
    by_cases hbk : ((Array.map (fun x => l.at x.fst m) shared).toList.all fun x => x != unbound) = true
    · rw [if_pos hbk]
      refine ⟨_, rfl, ?_⟩
      rw [← Array.forIn_toList]
      erw [probe_filter]
      apply hnext
      -- the candidates: the bucket of the left key and the rows with an unbound shared column
      let bucket := B.run.1.getD (KL m) #[]
      let loose := B.run.2
      have hbu : bucket.toList = (List.range' 0 r.rows).filter (fun j => bnd j && KR j == KL m) := hb1 (KL m)
      have hlo : loose.toList = (List.range' 0 r.rows).filter (fun j => !bnd j) := hb2
      have hpb : bucket.toList.Pairwise (· < ·) := by rw [hbu]; exact (List.pairwise_lt_range').filter _
      have hpl : loose.toList.Pairwise (· < ·) := by rw [hlo]; exact (List.pairwise_lt_range').filter _
      obtain ⟨hmp, hmm⟩ := mergeIdx_spec bucket loose (lt_of_pairwise hpb) (lt_of_pairwise hpl) (by
        intro k k' hk hk' e
        have m1 := mem_of_get hk
        have m2 := mem_of_get hk'
        rw [hbu] at m1; rw [hlo] at m2
        simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at m1 m2
        rw [e] at m1
        rw [m1.2.1] at m2; exact absurd m2.2 (by simp))
      apply eq_of_sorted_mem _ _ (hmp.filter _) ((List.pairwise_lt_range').filter _)
      intro x
      simp only [List.mem_filter]
      rw [hmm x, hbu, hlo]
      simp only [List.mem_filter, List.mem_range', Nat.zero_add, Nat.one_mul]
      constructor
      · rintro ⟨(⟨hk, _⟩ | ⟨hk, _⟩), hc⟩
        · exact ⟨hk, hc⟩
        · exact ⟨hk, hc⟩
      · rintro ⟨hk, hc⟩
        refine ⟨?_, hc⟩
        by_cases hbx : bnd x = true
        · left
          refine ⟨hk, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq]
          refine ⟨hbx, ?_⟩
          simp only [KR, KL, Array.toList_map]
          rw [List.map_inj_left]
          intro pq hpq
          simp only [bnd, KR, Array.toList_map, List.all_map, List.all_eq_true, Function.comp_def,
            bne_iff_ne, ne_eq] at hbx hbk
          have hc' := hc
          simp only [cmp, L4Factoidal.Storage.Sbm11.IdJoin.compatAt, Array.all_eq_true_iff_forall_mem,
            Bool.or_eq_true, beq_iff_eq] at hc'
          rcases hc' pq (by simpa using hpq) with (h | h) | h
          · exact absurd h (hbk pq hpq)
          · exact absurd h (hbx pq hpq)
          · exact h.symm
        · right
          exact ⟨hk, by simpa using hbx⟩
    · rw [if_neg hbk]
      refine ⟨_, rfl, ?_⟩
      erw [probe_filter]
      exact hnext _ rfl

/-! ## `IdJoin.pairsTable` -/

theorem push_loop {γ : Type} (G : Nat → γ) : ∀ (xs : List Nat) (acc : Array γ),
    forIn (m := _root_.Id) xs acc (fun k (s : Array γ) => pure (.yield (s.push (G k)))) =
      (acc ++ (xs.map G).toArray : Array γ) := by
  intro xs
  induction xs with
  | nil => intro acc; simp; rfl
  | cons x xs ih =>
    intro acc
    rw [List.forIn_cons]
    simp only [pure_bind]
    rw [ih]; simp

theorem map_toList_eq_range (a : Array Nat) (f : Nat → UInt64) :
    a.toList.map f = (List.range a.size).map fun k => f a[k]! := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [arr_get a k (by simpa using h1)]

/-- The id `pairsTable` writes in left column `c` for the pair `k`. -/
def pairVal (l r : Table) (shared : Array (Nat × Nat)) (li ri : Array Nat) (c k : Nat) : UInt64 :=
  match shared.find? (fun x => x.1 == c) with
  | none => l.at c li[k]!
  | some (_, q) => if l.at c li[k]! == unbound then r.at q ri[k]! else l.at c li[k]!

theorem put64_loop (f : Nat → UInt64) (n : Nat) {F : _root_.Id ByteArray}
    (hF : forIn (List.range' 0 n) (ByteArray.emptyWithCapacity (8 * n))
      (fun k (s : ByteArray) => pure (.yield (L4Factoidal.Qlvr.Side.put64 s (f k)))) = F) :
    ColHolds F.run ((List.range n).map f) := by
  have := forIn_range_inv n (fun m (s : ByteArray) => ColHolds s ((List.range m).map f)) hF
    (ColHolds.nil _ rfl) (fun m s _ h => ⟨_, rfl, by rw [List.range_succ, List.map_append]; exact h.put64 _⟩)
  exact this

/-- The columns of `pairsTable`: per left column the ids `pairVal`, then the
    right columns the left table does not have, gathered. -/
theorem pairsTable_eq (l r : Table) (hl : l.WF) (shared : Array (Nat × Nat)) (li ri : Array Nat)
    (hli : ∀ i ∈ li.toList, i < l.rows) :
    ∃ cols : Array ByteArray, ∃ sv,
      L4Factoidal.Storage.Sbm11.IdJoin.pairsTable l r shared li ri =
        { vars := (L4Factoidal.Qlvr.joinVars l r).1, cols, rows := li.size, sortVar := sv } ∧
      cols.size = l.vars.size + (L4Factoidal.Qlvr.joinVars l r).2.size ∧
      (∀ c, c < l.vars.size → ColHolds cols[c]! ((List.range li.size).map (pairVal l r shared li ri c))) ∧
      (∀ m, m < (L4Factoidal.Qlvr.joinVars l r).2.size →
        cols[l.vars.size + m]! = gather r.cols[(L4Factoidal.Qlvr.joinVars l r).2[m]!]! ri) := by
  unfold L4Factoidal.Storage.Sbm11.IdJoin.pairsTable
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hC : forIn (m := _root_.Id) (List.range' 0 l.vars.size)
    (Array.mkEmpty (L4Factoidal.Qlvr.joinVars l r).1.size : Array ByteArray) _ = C
  have hc := forIn_range_inv l.vars.size (fun m (cs : Array ByteArray) => cs.size = m ∧
      ∀ c, c < m → ColHolds cs[c]! ((List.range li.size).map (pairVal l r shared li ri c))) hC
    ⟨rfl, fun c hc => absurd hc (by omega)⟩ (by
      intro c cs hcl ⟨h1, h2⟩
      have hpush : ∀ col, ColHolds col ((List.range li.size).map (pairVal l r shared li ri c)) →
          (cs.push col).size = c + 1 ∧
          ∀ c', c' < c + 1 → ColHolds (cs.push col)[c']! ((List.range li.size).map (pairVal l r shared li ri c')) := by
        intro col hcol
        refine ⟨by simp [h1], fun c' hc' => ?_⟩
        rw [getElem!_pos _ c' (by simp; omega), Array.getElem_push]
        by_cases e : c' < cs.size
        · rw [dif_pos e, ← getElem!_pos cs c' e]; exact h2 c' (by omega)
        · rw [dif_neg e]; have : c' = c := by omega
          subst this; exact hcol
      cases hfind : Array.find? (fun x => x.fst == c) shared with
      | none =>
        refine ⟨_, rfl, hpush _ ?_⟩
        have := gather_at l hl c hcl li hli
        rw [map_toList_eq_range] at this
        have e : (List.range li.size).map (pairVal l r shared li ri c) =
            (List.range li.size).map (fun k => l.at c li[k]!) := by
          apply List.map_congr_left; intro k _; simp [pairVal, hfind]
        rw [e]; exact this
      | some pq =>
        obtain ⟨p0, q⟩ := pq
        simp only
        generalize hO : forIn (m := _root_.Id) (List.range' 0 li.size) (ByteArray.emptyWithCapacity (8 * li.size)) _ = O
        refine ⟨_, rfl, hpush _ ?_⟩
        have := put64_loop (fun k => if (l.at c li[k]! == unbound) = true then r.at q ri[k]! else l.at c li[k]!) li.size hO
        have e : (List.range li.size).map (pairVal l r shared li ri c) =
            (List.range li.size).map (fun k => if (l.at c li[k]! == unbound) = true then r.at q ri[k]! else l.at c li[k]!) := by
          apply List.map_congr_left; intro k _; simp [pairVal, hfind]
        rw [e]; exact this)
  obtain ⟨hc1, hc2⟩ := hc
  rw [id_bind, ← Array.forIn_toList]
  erw [push_loop (fun k => gather r.cols[k]! ri)]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp [hc1]
  · intro c hcl
    rw [getElem!_pos _ c (by simp; omega), Array.getElem_append_left (by omega), ← getElem!_pos C.run c (by omega)]
    exact hc2 c hcl
  · intro m hm
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_append_right (by omega)]
    simp only [hc1, Nat.add_sub_cancel_left, List.getElem_toArray, List.getElem_map, Array.getElem_toList]
    rw [getElem!_pos (L4Factoidal.Qlvr.joinVars l r).2 m hm]

theorem rowsEq_of_pairs (T : Table) (P : List (Nat × Nat)) (f : Nat × Nat → IdRow) (hrows : T.rows = P.length)
    (h : ∀ k (hk : k < P.length), RowEq (T.idRow k) (f P[k])) : RowsEq T.idRows (P.map f) := by
  refine ⟨by rw [idRows_length, hrows, List.length_map], fun k h1 h2 => ?_⟩
  have hk : k < P.length := by simpa using h2
  have : T.idRows[k] = T.idRow k := by simp [Table.idRows]
  rw [this, List.getElem_map]
  exact h k hk

theorem get_of_map {a : Array Nat} {P : List (Nat × Nat)} {g : Nat × Nat → Nat} (h : a.toList = P.map g)
    {k : Nat} (hk : k < P.length) : a[k]! = g P[k] := by
  have hs : k < a.size := by rw [← Array.length_toList, h, List.length_map]; exact hk
  rw [arr_get a k hs]; simp only [h, List.getElem_map]

/-- **L5l″.** `IdJoin.joinIds` of two well-formed tables (either may hold
    `unbound`) denotes SPARQL 1.1 Join of their rows (`IdJoin.idJoin`):
    the same solution mappings in the same order. -/
theorem joinIds_rows (l r : Table) (hl : l.WF) (hr : r.WF) :
    (L4Factoidal.Storage.Sbm11.IdJoin.joinIds l r).WF ∧
      RowsEq (L4Factoidal.Storage.Sbm11.IdJoin.joinIds l r).idRows
        (L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows) := by
  let shared := L4Factoidal.Qlvr.sharedCols l r
  let P := innerSpec l.rows r.rows (L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r shared)
  let li := (L4Factoidal.Storage.Sbm11.IdJoin.joinPairs l r shared).1
  let ri := (L4Factoidal.Storage.Sbm11.IdJoin.joinPairs l r shared).2
  have hJ : L4Factoidal.Storage.Sbm11.IdJoin.joinIds l r =
      L4Factoidal.Storage.Sbm11.IdJoin.pairsTable l r shared li ri := rfl
  obtain ⟨h1, h2⟩ := joinPairs_spec l r shared
  have hP : ∀ p ∈ P, p.1 < l.rows ∧ p.2 < r.rows := by
    intro p hp; obtain ⟨i, j⟩ := p
    obtain ⟨hi, hj, _⟩ := mem_innerSpec.mp hp; exact ⟨hi, hj⟩
  have hls : li.size = P.length := by rw [← Array.length_toList, h1, List.length_map]
  have hrs : ri.size = P.length := by rw [← Array.length_toList, h2, List.length_map]
  have hli : ∀ i ∈ li.toList, i < l.rows := by
    intro i hi; rw [h1] at hi
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hi; rw [← e]; exact (hP p hp).1
  have hri : ∀ j ∈ ri.toList, j < r.rows := by
    intro j hj; rw [h2] at hj
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hj; rw [← e]; exact (hP p hp).2
  obtain ⟨cols, sv, hT, hsz, hL, hR⟩ := pairsTable_eq l r hl shared li ri hli
  rw [hJ, hT]
  have hex := joinVars_extra l r
  have hext : ∀ m, m < (L4Factoidal.Qlvr.joinVars l r).2.size → (L4Factoidal.Qlvr.joinVars l r).2[m]! < r.vars.size := by
    intro m hm
    exact ((mem_extra hex).mp (mem_of_get hm)).1
  let T : Table := { vars := (L4Factoidal.Qlvr.joinVars l r).1, cols, rows := li.size, sortVar := sv }
  have hvT : T.vars.toList = l.vars.toList ++ (L4Factoidal.Qlvr.joinVars l r).2.toList.map (fun q => r.vars[q]!) :=
    joinVars_vars l r
  have hnd : T.vars.toList.Nodup := by rw [hvT]; exact out_nodup l r _ hl.nodup hr.nodup hex
  have hTs : T.vars.size = l.vars.size + (L4Factoidal.Qlvr.joinVars l r).2.size := by
    rw [← Array.length_toList, hvT]; simp
  have hWF : T.WF := by
    refine ⟨by rw [hTs, hsz], fun c hc => ?_, hnd⟩
    show cols[c].size = 8 * li.size
    have hc0 : c < cols.size := hc
    have hc' : c < l.vars.size + (L4Factoidal.Qlvr.joinVars l r).2.size := by omega
    rw [← getElem!_pos cols c hc0]
    by_cases hcl : c < l.vars.size
    · rw [(hL c hcl).1]; simp
    · have := hR (c - l.vars.size) (by omega)
      rw [show l.vars.size + (c - l.vars.size) = c by omega] at this
      rw [this, gather_size r hr _ (hext _ (by omega)) ri hri]; omega
  refine ⟨hWF, ?_⟩
  have hjoin : L4Factoidal.Storage.Sbm11.IdJoin.idJoin l.idRows r.idRows =
      P.map fun p => idMerge (l.idRow p.1) (r.idRow p.2) := by
    rw [idJoin_rows]
    congr 1
    apply innerSpec_congr
    intro i j _ _
    exact (compatAt_iff l r hr.nodup i j).symm
  rw [hjoin]
  apply rowsEq_of_pairs T P _ (by show li.size = P.length; exact hls)
  intro k hk v
  have ek1 : li[k]! = P[k].1 := get_of_map h1 hk
  have ek2 : ri[k]! = P[k].2 := get_of_map h2 hk
  have hlk := out_lookup l r T _ k ri[k]! (fun c => pairVal l r shared li ri c k) hl.nodup hr.nodup hvT hex
    (fun c hc => by
      show word64 cols[c]! (8 * k) = _
      rw [(hL c hc).word (by simp; omega)]; simp)
    (fun m hm => by
      show word64 cols[l.vars.size + m]! (8 * k) = _
      rw [hR m hm, gather_word r hr _ (hext m hm) ri hri k (by omega)]) v
  rw [lookup_idRow T hnd, hlk, lookup_idMerge, lookup_idRow l hl.nodup, lookup_idRow r hr.nodup,
    lookupAt_eq l, ← ek1, ← ek2]
  cases hlv : l.idx v with
  | none => rfl
  | some c =>
    simp only
    obtain ⟨hc, hcv⟩ := idx_some hlv
    unfold pairVal
    cases hf : Array.find? (fun x => x.1 == c) shared with
    | none =>
      simp only
      rw [lookupAt_eq r]
      cases hrv : r.idx v with
      | none => cases nz (l.at c li[k]!) <;> rfl
      | some q =>
        exfalso
        have := Array.find?_eq_none.mp hf (c, q) (mem_sharedCols.mpr ⟨hc, by rw [hcv]; exact hrv⟩)
        simp at this
    | some pq =>
      obtain ⟨p0, q⟩ := pq
      simp only
      have hp0 : p0 = c := by simpa using Array.find?_some hf
      subst hp0
      have hmem := Array.mem_of_find?_eq_some hf
      obtain ⟨_, hq⟩ := mem_sharedCols.mp hmem
      rw [hcv] at hq
      rw [lookupAt_eq r, hq]
      simp only [nz]
      by_cases h0 : l.at p0 li[k]! = unbound
      · simp [h0]
      · have : (l.at p0 li[k]! == unbound) = false := by simpa using h0
        simp [this]

/-! ## `IdJoin.unionIds` -/

/-- The id of variable `v` in row `i` of `t`, `unbound` when `t` has no
    column `v`. -/
def colVal (t : Table) (v : String) (i : Nat) : UInt64 :=
  match t.idx v with
  | some k => t.at k i
  | none => unbound

theorem lookupAt_colVal (t : Table) (i : Nat) (v : String) : t.lookupAt i v = nz (colVal t v i) := by
  rw [lookupAt_eq]; unfold colVal
  cases t.idx v <;> rfl

theorem col_holds (t : Table) (ht : t.WF) (k : Nat) (hk : k < t.vars.size) :
    ColHolds t.cols[k]! ((List.range t.rows).map (t.at k)) := by
  have hk' : k < t.cols.size := by rw [ht.cols_size]; exact hk
  refine ⟨by rw [getElem!_pos t.cols k hk', ht.col_bytes k hk']; simp, fun i hi => ?_⟩
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem addVars_spec : ∀ (xs : List String) (vs : Array String), vs.toList.Nodup →
    let R := (forIn (m := _root_.Id) xs vs (fun v (s : Array String) =>
      if (!s.contains v) = true then pure (.yield (s.push v)) else pure (.yield s))).run
    R.toList.Nodup ∧ (∀ v ∈ vs.toList, v ∈ R.toList) ∧ (∀ v ∈ xs, v ∈ R.toList) := by
  intro xs
  induction xs with
  | nil => intro vs h; exact ⟨h, fun v hv => hv, fun v hv => by simp at hv⟩
  | cons x xs ih =>
    intro vs h
    simp only [List.forIn_cons]
    by_cases hc : (!vs.contains x) = true
    · simp only [hc, if_true, pure_bind]
      have hnd : (vs.push x).toList.Nodup := by
        rw [Array.toList_push, List.nodup_append]
        refine ⟨h, by simp, fun a ha b hb e => ?_⟩
        simp at hb; subst hb; subst e
        simp at hc; exact hc (by simpa using ha)
      obtain ⟨h1, h2, h3⟩ := ih (vs.push x) hnd
      refine ⟨h1, fun v hv => h2 v (by simp [hv]), fun v hv => ?_⟩
      rcases List.mem_cons.mp hv with e | e
      · subst e; exact h2 v (by simp)
      · exact h3 v e
    · simp only [hc, Bool.false_eq_true, if_false, pure_bind]
      obtain ⟨h1, h2, h3⟩ := ih vs h
      refine ⟨h1, h2, fun v hv => ?_⟩
      rcases List.mem_cons.mp hv with e | e
      · subst e; simp at hc; exact h2 v (by simpa using hc)
      · exact h3 v e

theorem put64_unbound_loop (n : Nat) : ∀ (m : Nat) (b : ByteArray) (xs : List UInt64), ColHolds b xs →
    ColHolds (forIn (m := _root_.Id) (List.range' m n) b
      (fun _ (s : ByteArray) => pure (.yield (L4Factoidal.Qlvr.Side.put64 s unbound)))).run
      (xs ++ List.replicate n unbound) := by
  induction n with
  | zero => intro m b xs h; simpa using h
  | succ n ih =>
    intro m b xs h
    rw [List.range'_succ, List.forIn_cons]
    simp only [pure_bind]
    have := ih (m + 1) _ _ (h.put64 unbound)
    rw [List.append_assoc] at this
    simpa [List.replicate_succ] using this

/-- The pairs (table, row) of a list of tables, in order. -/
def tableRows (L : List Table) : List (Table × Nat) :=
  L.flatMap fun t => (List.range t.rows).map fun i => (t, i)

theorem tableRows_append (A B : List Table) : tableRows (A ++ B) = tableRows A ++ tableRows B := by
  simp [tableRows]

theorem tableRows_length (L : List Table) : (tableRows L).length = (L.map Table.rows).sum := by
  induction L with
  | nil => rfl
  | cons t L ih => simp [tableRows] at ih ⊢

/-- **L5m, table part.** `IdJoin.unionIds` of well-formed tables denotes
    the concatenation of their rows (SPARQL 1.1 Union, multiset union, as a
    list): the same solution mappings in the same order. -/
theorem unionIds_rows (ts : Array Table) (hts : ∀ t ∈ ts.toList, t.WF) :
    (L4Factoidal.Storage.Sbm11.IdJoin.unionIds ts).WF ∧
      RowsEq (L4Factoidal.Storage.Sbm11.IdJoin.unionIds ts).idRows (ts.toList.flatMap Table.idRows) := by
  unfold L4Factoidal.Storage.Sbm11.IdJoin.unionIds
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hV : forIn (m := _root_.Id) ts (#[] : Array String) _ = V
  rw [← Array.forIn_toList] at hV
  have hv := forIn_list_inv ts.toList (fun k (vs : Array String) => vs.toList.Nodup ∧
      ∀ t ∈ ts.toList.take k, ∀ v ∈ t.vars.toList, v ∈ vs.toList) hV ⟨by simp, by simp⟩ (by
    intro k vs hk ⟨h1, h2⟩
    refine ⟨_, rfl, ?_⟩
    rw [← Array.forIn_toList]
    obtain ⟨r1, r2, r3⟩ := addVars_spec ts.toList[k].vars.toList vs h1
    refine ⟨r1, fun t ht v hv => ?_⟩
    rw [List.take_add_one, List.mem_append, List.getElem?_eq_getElem hk] at ht
    rcases ht with ht | ht
    · exact r2 v (h2 t ht v hv)
    · simp only [Option.toList_some, List.mem_singleton] at ht; subst ht; exact r3 v hv)
  obtain ⟨hvnd, hvsub⟩ := hv
  rw [List.take_length] at hvsub
  rw [id_bind]
  generalize hC : forIn (m := _root_.Id) ts ((Array.map (fun _ => ByteArray.empty) V.run, 0) : Array ByteArray × Nat) _ = C
  rw [← Array.forIn_toList] at hC
  let pre : Nat → Nat → List UInt64 := fun k c =>
    (tableRows (ts.toList.take k)).map fun p => colVal p.1 V.run[c]! p.2
  have hc := forIn_list_inv ts.toList (fun k (st : Array ByteArray × Nat) => st.1.size = V.run.size ∧
      st.2 = ((ts.toList.take k).map Table.rows).sum ∧ ∀ c, c < V.run.size → ColHolds st.1[c]! (pre k c)) hC
    ⟨by simp, by simp, fun c hc => ColHolds.nil _ (by
      rw [getElem!_pos _ c (by simpa using hc)]; simp)⟩ (by
    intro k st hk ⟨h1, h2, h3⟩
    let t := ts.toList[k]
    have ht : t.WF := hts t (List.getElem_mem hk)
    have hpre : ∀ c, pre (k + 1) c = pre k c ++ (List.range t.rows).map (colVal t V.run[c]!) := by
      intro c
      simp only [pre, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, tableRows_append,
        List.map_append]
      simp [tableRows, t]
    generalize hI : forIn (m := _root_.Id) (List.range' 0 V.run.size) st.1 _ = I
    have hi := forIn_range_inv V.run.size (fun m (cs : Array ByteArray) => cs.size = V.run.size ∧
        ∀ c, c < V.run.size → ColHolds cs[c]! (pre k c ++ if c < m then
          (List.range t.rows).map (colVal t V.run[c]!) else [])) hI
      ⟨h1, fun c hc => by simpa using h3 c hc⟩ (by
        intro m cs hm ⟨g1, g2⟩
        cases hidx : t.idx V.run[m]! with
        | some q =>
          refine ⟨cs.modify m fun x => x ++ t.cols[q]!, ?_, by simp [g1], fun c hc => ?_⟩
          · rfl
          · rw [getElem!_pos _ c (by simp; omega), Array.getElem_modify]
            by_cases e : m = c
            · subst e
              simp only [if_true, Nat.lt_succ_self]
              have hq := (idx_some hidx).1
              have hcol := col_holds t ht q hq
              have e2 : (List.range t.rows).map (colVal t V.run[m]!) = (List.range t.rows).map (t.at q) := by
                apply List.map_congr_left; intro i _; simp [colVal, hidx]
              rw [e2]
              have := g2 m hc
              rw [if_neg (Nat.lt_irrefl m), List.append_nil, getElem!_pos cs m (by omega)] at this
              exact this.append hcol (by rw [ByteArray.data_append, Array.toList_append])
            · rw [if_neg e, ← getElem!_pos cs c (by omega)]
              have := g2 c hc
              by_cases hcm : c < m
              · rw [if_pos hcm] at this; rw [if_pos (by omega)]; exact this
              · rw [if_neg hcm] at this; rw [if_neg (by omega)]; exact this
        | none =>
          simp only [t] at hidx
          refine ⟨cs.set! m (forIn (m := _root_.Id) (List.range' 0 t.rows) cs[m]!
              (fun _ (s : ByteArray) => pure (.yield (L4Factoidal.Qlvr.Side.put64 s unbound)))).run, ?_, ?_⟩
          · rfl
          have hX := put64_unbound_loop t.rows 0 cs[m]!
          generalize (forIn (m := _root_.Id) (List.range' 0 t.rows) cs[m]!
              (fun _ (s : ByteArray) => pure (.yield (L4Factoidal.Qlvr.Side.put64 s unbound)))).run = X at hX ⊢
          refine ⟨by simp [g1], fun c hc => ?_⟩
          rw [Array.set!_eq_setIfInBounds, getElem!_pos _ c (by simp; omega), Array.getElem_setIfInBounds (by omega)]
          by_cases e : m = c
          · subst e
            simp only [if_true, Nat.lt_succ_self]
            have e2 : (List.range t.rows).map (colVal t V.run[m]!) = List.replicate t.rows unbound := by
              apply List.ext_getElem
              · simp
              · intro i _ _
                simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
                unfold colVal
                rw [show t.idx V.run[m]! = none from hidx]
            rw [e2]
            have := g2 m hc
            rw [if_neg (Nat.lt_irrefl m), List.append_nil] at this
            exact hX _ this
          · rw [if_neg e, ← getElem!_pos cs c (by omega)]
            have := g2 c hc
            by_cases hcm : c < m
            · rw [if_pos hcm] at this; rw [if_pos (by omega)]; exact this
            · rw [if_neg hcm] at this; rw [if_neg (by omega)]; exact this)
    obtain ⟨i1, i2⟩ := hi
    refine ⟨(I.run, st.2 + t.rows), rfl, i1, ?_, fun c hc => ?_⟩
    · rw [h2, List.take_add_one, List.getElem?_eq_getElem hk]; simp [t]
    · rw [hpre c]; have := i2 c hc; rw [if_pos hc] at this; exact this)
  obtain ⟨c1, c2, c3⟩ := hc
  rw [List.take_length] at c2
  rw [id_bind]
  let Q := tableRows ts.toList
  have hpre : ∀ c, pre ts.toList.length c = Q.map fun p => colVal p.1 V.run[c]! p.2 := by
    intro c; simp only [pre, Q, List.take_length]
  have hQ : Q.length = C.run.2 := by rw [tableRows_length, c2]
  have hmemQ : ∀ p ∈ Q, p.1 ∈ ts.toList ∧ p.2 < p.1.rows := by
    intro p hp
    simp only [Q, tableRows, List.mem_flatMap, List.mem_map, List.mem_range] at hp
    obtain ⟨t, ht, i, hi, rfl⟩ := hp
    exact ⟨ht, hi⟩
  let U : Table := { vars := V.run, cols := C.run.1, rows := C.run.2 }
  show U.WF ∧ RowsEq U.idRows _
  have hWF : U.WF := by
    refine ⟨c1, fun c hc => ?_, hvnd⟩
    have hc' : c < V.run.size := by rw [← c1]; exact hc
    have := (c3 c hc').1
    rw [getElem!_pos _ c hc, hpre c] at this
    show C.run.1[c].size = 8 * C.run.2
    rw [this, List.length_map, hQ]
  refine ⟨hWF, ?_⟩
  have htgt : ts.toList.flatMap Table.idRows = Q.map fun p => p.1.idRow p.2 := by
    simp only [Q, tableRows, List.map_flatMap, List.map_map]
    rfl
  rw [htgt]
  refine ⟨by rw [idRows_length, List.length_map, hQ], fun g h1 h2 => ?_⟩
  have hg : g < Q.length := by simpa using h2
  have : U.idRows[g] = U.idRow g := by simp [Table.idRows]
  rw [this, List.getElem_map]
  obtain ⟨htm, hi⟩ := hmemQ Q[g] (List.getElem_mem hg)
  have htw : Q[g].1.WF := hts _ htm
  intro v
  rw [lookup_idRow U hvnd, lookup_idRow _ htw.nodup, lookupAt_colVal Q[g].1, lookupAt_eq U]
  cases hv : U.idx v with
  | some c =>
    obtain ⟨hc, hcv⟩ := idx_some hv
    have hw : U.at c g = colVal Q[g].1 V.run[c]! Q[g].2 := by
      show word64 C.run.1[c]! (8 * g) = _
      rw [(c3 c hc).word (by rw [hpre]; simpa using hg)]
      simp only [hpre, List.getElem_map]
    show nz (U.at c g) = _
    rw [hw]
    have : V.run[c]! = v := hcv
    rw [this]
  | none =>
    have hnot : Q[g].1.idx v = none := by
      cases h : Q[g].1.idx v with
      | none => rfl
      | some k =>
        exfalso
        obtain ⟨hk, hkv⟩ := idx_some h
        have hmem : v ∈ V.run.toList := hvsub _ htm v (by rw [← hkv, arr_get _ k hk]; simp)
        obtain ⟨c, hc, e⟩ := List.mem_iff_getElem.mp hmem
        exact idx_none hv c (by simpa using hc) (by rw [arr_get _ c (by simpa using hc)]; exact e)
    show none = _
    unfold colVal
    rw [hnot]; rfl

#print axioms gather_holds
#print axioms joinOutput_rows
#print axioms hashJoin_rows
#print axioms joinPairs_spec
#print axioms joinIds_rows
#print axioms unionIds_rows

end L4Factoidal.Storage.Sbm11.TableTheorems
