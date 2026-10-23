/-
L4Factoidal.Storage.Sbm11.LocalTableTheorems — the operators of the nested
evaluator that give terms query-local ids: VALUES (`IdQuery.resolveValuesVocabM`)
(https://github.com/danbri/factoidal/issues/776; lemma L4r of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `forIn_ends`: a loop in `ExceptT String Id` whose every step refuses with a
  `LocalVocab.LocalRefusal` or yields keeps an invariant.
* `resolveValues_spec`: for one VALUES block whose variables are distinct
  and whose terms are their own `normalizeTerm`, `resolveValuesVocabM`
  refuses (`LocalRefusal`) or returns one well-formed table with the
  block's variables and one row per block row, each cell the id of the
  block's term in the new vocabulary (`CellOk`: an id of the state, not 0,
  that decodes to the term), or `unbound` for UNDEF and for a cell a short
  row lacks; the vocabulary keeps its invariant and grows.
* `values_rows`: decoding the rows of that table gives `evalValues` of the
  block, row for row, as solution mappings (`BindEq`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.LocalVocabTheorems

namespace L4Factoidal.Storage.Sbm11.LocalTable

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Binding SolutionSeq evalValues zipBindings)
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow decRow RowIds unbound idLookup)
open L4Factoidal.Storage.Sbm11.TableTheorems (ColHolds)
open L4Factoidal.Storage.Sbm11.LocalVocab
open L4Factoidal.Codec.Zstd (word64)

/-! ## Loops that refuse or yield -/

theorem forIn_ends {α β : Type} (f : α → β → ExceptT String Id (ForInStep β)) :
    ∀ (xs : List α) (P : Nat → β → Prop) (b0 : β), P 0 b0 →
      (∀ k (hk : k < xs.length) b, P k b →
        (∃ e, f xs[k] b = throw e ∧ LocalRefusal e) ∨ ∃ b', f xs[k] b = pure (.yield b') ∧ P (k + 1) b') →
      (∃ e, forIn xs b0 f = throw e ∧ LocalRefusal e) ∨ ∃ b', forIn xs b0 f = pure b' ∧ P xs.length b'
  | [], _, b0, h0, _ => Or.inr ⟨b0, rfl, h0⟩
  | a :: as, P, b0, h0, hs => by
    rw [List.forIn_cons]
    rcases hs 0 (by simp) b0 h0 with ⟨e, he, hr⟩ | ⟨b1, h1, hP1⟩
    · left
      simp only [List.getElem_cons_zero] at he
      exact ⟨e, by rw [he]; rfl, hr⟩
    · simp only [List.getElem_cons_zero] at h1
      rw [h1, pure_bind]
      simp only []
      rcases forIn_ends f as (fun k b => P (k + 1) b) b1 hP1
        (fun k hk b hb => by
          have := hs (k + 1) (by simp; omega) b hb
          simpa using this) with h | ⟨b', hb', hP'⟩
      · exact Or.inl h
      · exact Or.inr ⟨b', hb', by simpa using hP'⟩

theorem forIn_yields {α β : Type} (f : α → β → ExceptT String Id (ForInStep β)) :
    ∀ (xs : List α) (P : Nat → β → Prop) (b0 : β), P 0 b0 →
      (∀ k (hk : k < xs.length) b, P k b → ∃ b', f xs[k] b = pure (.yield b') ∧ P (k + 1) b') →
      ∃ b', forIn xs b0 f = pure b' ∧ P xs.length b'
  | [], _, b0, h0, _ => ⟨b0, rfl, h0⟩
  | a :: as, P, b0, h0, hs => by
    rw [List.forIn_cons]
    obtain ⟨b1, h1, hP1⟩ := hs 0 (by simp) b0 h0
    simp only [List.getElem_cons_zero] at h1
    rw [h1, pure_bind]
    obtain ⟨b', hb', hP'⟩ := forIn_yields f as (fun k b => P (k + 1) b) b1 hP1
      (fun k hk b hb => by
        have := hs (k + 1) (by simp; omega) b hb
        simpa using this)
    exact ⟨b', hb', by simpa using hP'⟩

/-! ## The cells of a VALUES block -/

/-- The term of cell `c` of a VALUES row: `none` for UNDEF and for a cell a
    short row lacks. -/
def cellOf (row : Array (Option Term)) (c : Nat) : Option Term :=
  match row[c]? with
  | some (some t) => some t
  | _ => none

/-- The id of a cell in a state whose vocabulary is `voc`: an id of the state,
    not `unbound`, that decodes to the term; `unbound` for no term. -/
def CellOk (dec : UInt64 → Term) (ok : UInt64 → Prop) (voc : Array Term) : Option Term → UInt64 → Prop
  | some t, x => okV ok voc x ∧ x ≠ unbound ∧ decV dec voc x = t
  | none, x => x = unbound

theorem cellOk_mono (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60) :
    ∀ (c : Option Term) (x : UInt64), CellOk dec ok voc1 c x → CellOk dec ok voc2 c x
  | some _, _, ⟨h1, h2, h3⟩ => ⟨okV_mono hp h1, h2, by rw [decV_mono dec hloc hp hsz h1]; exact h3⟩
  | none, _, h => h

/-- The columns built so far: `i` rows, plus row `i` in the columns before
    `c`. -/
def ColsOk (dec : UInt64 → Term) (ok : UInt64 → Prop) (voc : Array Term) (rows : List (Array (Option Term)))
    (nv i c : Nat) (cols : Array ByteArray) : Prop :=
  cols.size = nv ∧ ∀ c', c' < nv → ∃ xs : List UInt64, ColHolds cols[c']! xs ∧
    xs.length = i + (if c' < c then 1 else 0) ∧
    ∀ j (hj : j < xs.length), CellOk dec ok voc (cellOf rows[j]! c') xs[j]

theorem colsOk_mono (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60)
    {rows : List (Array (Option Term))} {nv i c : Nat} {cols : Array ByteArray}
    (h : ColsOk dec ok voc1 rows nv i c cols) : ColsOk dec ok voc2 rows nv i c cols := by
  refine ⟨h.1, fun c' hc' => ?_⟩
  obtain ⟨xs, h1, h2, h3⟩ := h.2 c' hc'
  exact ⟨xs, h1, h2, fun j hj => cellOk_mono dec hloc hp hsz _ _ (h3 j hj)⟩

/-- One step of the column loop: column `c` of row `i` gets `x`. -/
theorem colsOk_step (dec : UInt64 → Term) (ok : UInt64 → Prop) (voc : Array Term)
    (rows : List (Array (Option Term))) (nv i c : Nat) (hc : c < nv) (cols : Array ByteArray)
    (h : ColsOk dec ok voc rows nv i c cols) (x : UInt64) (hx : CellOk dec ok voc (cellOf rows[i]! c) x) :
    ColsOk dec ok voc rows nv i (c + 1) (cols.modify c fun b => L4Factoidal.Qlvr.Side.put64 b x) := by
  obtain ⟨hsz, hcol⟩ := h
  refine ⟨by rw [Array.size_modify]; exact hsz, fun c' hc' => ?_⟩
  obtain ⟨xs, h1, h2, h3⟩ := hcol c' hc'
  have hc'' : c' < cols.size := by omega
  by_cases e : c' = c
  · subst e
    refine ⟨xs ++ [x], ?_, ?_, ?_⟩
    · rw [getElem!_pos _ c' (by rw [Array.size_modify]; exact hc''), Array.getElem_modify, if_pos rfl]
      rw [getElem!_pos _ c' hc''] at h1
      exact h1.put64 x
    · simp only [List.length_append, List.length_singleton, Nat.lt_irrefl, if_false] at h2 ⊢
      simp only [Nat.lt_succ_self, if_true]; omega
    · intro j hj
      simp only [Nat.lt_irrefl, if_false, Nat.add_zero] at h2
      by_cases hj' : j < xs.length
      · rw [List.getElem_append_left hj']; exact h3 j hj'
      · have : j = xs.length := by simp at hj; omega
        subst this
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_singleton]
        rw [h2]; exact hx
  · refine ⟨xs, ?_, ?_, h3⟩
    · rw [getElem!_pos _ c' (by rw [Array.size_modify]; exact hc''), Array.getElem_modify, if_neg (Ne.symm e)]
      rw [getElem!_pos _ c' hc''] at h1
      exact h1
    · rw [h2]
      by_cases h' : c' < c
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

/-- One step of the column loop of `resolveValuesVocabM` for row `row`. -/
def cellStep (st : Store Id) (row : Array (Option Term)) (c : Nat)
    (s : Array Term × Std.HashMap Term Nat × Array ByteArray) :
    ExceptT String Id (ForInStep (Array Term × Std.HashMap Term Nat × Array ByteArray)) :=
  match row[c]? with
  | some (some t) => do
    let r ← termIdM st s.1 s.2.1 t
    pure (.yield (r.2.1, r.2.2, s.2.2.modify c fun b => L4Factoidal.Qlvr.Side.put64 b r.1))
  | _ => pure (.yield (s.1, s.2.1, s.2.2.modify c fun b => L4Factoidal.Qlvr.Side.put64 b unbound))

/-- One step of the row loop of `resolveValuesVocabM`. -/
def rowStep (st : Store Id) (nv : Nat) (row : Array (Option Term))
    (s : Array Term × Std.HashMap Term Nat × Array ByteArray) :
    ExceptT String Id (ForInStep (Array Term × Std.HashMap Term Nat × Array ByteArray)) := do
  let s' ← forIn (List.range' 0 nv) s (cellStep st row)
  pure (.yield s')

theorem resolveValues_eq (st : Store Id) (b : ValuesBlock) (voc : Array Term) (ix : Std.HashMap Term Nat) :
    resolveValuesVocabM st #[b] voc ix = (do
      let s ← forIn b.rows.toList (voc, ix, b.vars.map fun _ => ByteArray.empty) (rowStep st b.vars.size)
      pure (#[{ vars := b.vars, cols := s.2.2, rows := b.rows.size }], s.1, s.2.1)) := by
  unfold resolveValuesVocabM
  simp only [← Array.forIn_toList, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
  rfl

section
variable (st : Store Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)

/-- The column loop of one row: each cell gets its id (`CellOk`), or the loop
    refuses. -/
theorem cells_spec (hid : ∀ t, st.idOf t = pure (cid t)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (rows : List (Array (Option Term))) (nv i : Nat) (row : Array (Option Term)) (hrow : rows[i]! = row)
    (hn : ∀ c t, cellOf row c = some t → normalizeTerm t = t) (voc0 : Array Term)
    (vocR : Array Term) (ixR : Std.HashMap Term Nat) (cols : Array ByteArray)
    (hR : VocInv cid vocR ixR) (hpR : voc0.toList <+: vocR.toList)
    (hcR : ColsOk dec ok vocR rows nv i 0 cols) :
    (∃ e, forIn (List.range' 0 nv) (vocR, ixR, cols) (cellStep st row) = throw e ∧ LocalRefusal e) ∨
      ∃ s', forIn (List.range' 0 nv) (vocR, ixR, cols) (cellStep st row) = pure s' ∧
        VocInv cid s'.1 s'.2.1 ∧ voc0.toList <+: s'.1.toList ∧ ColsOk dec ok s'.1 rows nv i nv s'.2.2 := by
  have := forIn_ends (cellStep st row) (List.range' 0 nv)
    (fun c (s : Array Term × Std.HashMap Term Nat × Array ByteArray) =>
      VocInv cid s.1 s.2.1 ∧ voc0.toList <+: s.1.toList ∧ ColsOk dec ok s.1 rows nv i c s.2.2)
    (vocR, ixR, cols) ⟨hR, hpR, hcR⟩ (by
      intro c hc s ⟨hs1, hs2, hs3⟩
      rw [List.length_range'] at hc
      rw [List.getElem_range', Nat.zero_add, Nat.one_mul]
      unfold cellStep
      cases hcell : row[c]? with
      | some o =>
        cases o with
        | some t =>
          have hct : cellOf rows[i]! c = some t := by rw [hrow]; unfold cellOf; rw [hcell]
          have hnt := hn c t (by unfold cellOf; rw [hcell])
          rcases termIdM_spec st cid hid dec ok hcid hcidok hcidN hloc hcid0 s.1 s.2.1 hs1 t with
            ⟨e, he, hr⟩ | ⟨y, voc', ix', he, h1, h2, h3, h4, h5⟩
          · left; exact ⟨e, by simp only []; rw [he]; rfl, hr⟩
          · right
            refine ⟨(voc', ix', s.2.2.modify c fun x_1 => L4Factoidal.Qlvr.Side.put64 x_1 y), ?_, h1,
              hs2.trans h2, ?_⟩
            · simp only []; rw [he]; rfl
            · apply colsOk_step dec ok voc' _ _ i c hc _ (colsOk_mono dec hloc h2 h1.size hs3)
              rw [hct]
              exact ⟨h3, h4, by rw [h5, hnt]⟩
        | none =>
          right
          refine ⟨(s.1, s.2.1, s.2.2.modify c fun x_1 => L4Factoidal.Qlvr.Side.put64 x_1 unbound), rfl, hs1, hs2, ?_⟩
          apply colsOk_step dec ok s.1 _ _ i c hc _ hs3
          rw [hrow]; unfold cellOf; rw [hcell]; rfl
      | none =>
        right
        refine ⟨(s.1, s.2.1, s.2.2.modify c fun x_1 => L4Factoidal.Qlvr.Side.put64 x_1 unbound), rfl, hs1, hs2, ?_⟩
        apply colsOk_step dec ok s.1 _ _ i c hc _ hs3
        rw [hrow]; unfold cellOf; rw [hcell]; rfl)
  rw [List.length_range'] at this
  exact this

theorem colsOk_next {dec : UInt64 → Term} {ok : UInt64 → Prop} {voc : Array Term}
    {rows : List (Array (Option Term))} {nv i : Nat} {cols : Array ByteArray}
    (h : ColsOk dec ok voc rows nv i nv cols) : ColsOk dec ok voc rows nv (i + 1) 0 cols := by
  refine ⟨h.1, fun c' hc' => ?_⟩
  obtain ⟨xs, h1, h2, h3⟩ := h.2 c' hc'
  rw [if_pos hc'] at h2
  exact ⟨xs, h1, by simp [h2], h3⟩

/-- **One VALUES block on ids.** `resolveValuesVocabM` refuses
    (`LocalRefusal`) or returns one table with the block's variables and one
    row per block row, each column holding the ids of its cells
    (`ColsOk`); the vocabulary keeps its invariant and grows. -/
theorem resolveValues_spec (hid : ∀ t, st.idOf t = pure (cid t)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (b : ValuesBlock) (hn : ∀ row ∈ b.rows.toList, ∀ c t, cellOf row c = some t → normalizeTerm t = t)
    (voc : Array Term) (ix : Std.HashMap Term Nat) (hinv : VocInv cid voc ix) :
    (∃ e, resolveValuesVocabM st #[b] voc ix = throw e ∧ LocalRefusal e) ∨
      ∃ cols voc' ix', resolveValuesVocabM st #[b] voc ix =
          pure (#[{ vars := b.vars, cols, rows := b.rows.size }], voc', ix') ∧ VocInv cid voc' ix' ∧
        voc.toList <+: voc'.toList ∧ ColsOk dec ok voc' b.rows.toList b.vars.size b.rows.size 0 cols := by
  rw [resolveValues_eq]
  have h0 : ColsOk dec ok voc b.rows.toList b.vars.size 0 0 (b.vars.map fun _ => ByteArray.empty) := by
    refine ⟨by simp, fun c' hc' => ⟨[], ?_, by simp, fun j hj => by simp at hj⟩⟩
    rw [getElem!_pos _ c' (by simpa using hc')]
    exact ColHolds.nil _ (by simp)
  have := forIn_ends (rowStep st b.vars.size) b.rows.toList
    (fun i (s : Array Term × Std.HashMap Term Nat × Array ByteArray) =>
      VocInv cid s.1 s.2.1 ∧ voc.toList <+: s.1.toList ∧ ColsOk dec ok s.1 b.rows.toList b.vars.size i 0 s.2.2)
    (voc, ix, b.vars.map fun _ => ByteArray.empty) ⟨hinv, List.prefix_refl _, h0⟩ (by
      intro i hi s ⟨hs1, hs2, hs3⟩
      unfold rowStep
      rcases cells_spec st cid dec ok hid hcid hcidok hcidN hloc hcid0 b.rows.toList b.vars.size i (b.rows.toList[i]'hi)
        (getElem!_pos b.rows.toList i hi) (hn _ (List.getElem_mem hi)) voc s.1 s.2.1 s.2.2 hs1 hs2 hs3 with
        ⟨e, he, hr⟩ | ⟨s', he, h1, h2, h3⟩
      · left; exact ⟨e, by rw [he]; rfl, hr⟩
      · right; exact ⟨s', by rw [he]; rfl, h1, h2, colsOk_next h3⟩)
  rcases this with ⟨e, he, hr⟩ | ⟨s', he, h1, h2, h3⟩
  · left; exact ⟨e, by rw [he]; rfl, hr⟩
  · right
    refine ⟨s'.2.2, s'.1, s'.2.1, by rw [he]; rfl, h1, h2, ?_⟩
    simpa using h3

/-! ## The rows of the VALUES table -/

/-- The term of cell `c` of a VALUES row given as a list. -/
def cellL (row : List (Option Term)) (c : Nat) : Option Term :=
  match row[c]? with
  | some (some t) => some t
  | _ => none

theorem lookup_bind' (v w : String) (t : Term) (mu : Binding) :
    (mu.bind v t).lookup w = if v = w then some t else mu.lookup w := by
  simp [Binding.bind, Binding.lookup]

theorem zip_notin (w : String) : ∀ (vars : List String) (row : List (Option Term)) (mu : Binding),
    w ∉ vars → (zipBindings vars row mu).lookup w = mu.lookup w
  | [], row, mu, _ => by cases row <;> rfl
  | _ :: _, [], mu, _ => rfl
  | v :: vs, some t :: ts, mu, h => by
    simp only [zipBindings]
    rw [zip_notin w vs ts _ (fun h' => h (List.mem_cons_of_mem _ h')), lookup_bind']
    rw [if_neg (fun e => h (by rw [e]; exact List.mem_cons_self))]
  | v :: vs, none :: ts, mu, h => by
    simp only [zipBindings]
    exact zip_notin w vs ts mu (fun h' => h (List.mem_cons_of_mem _ h'))

theorem zip_at (w : String) : ∀ (vars : List String) (row : List (Option Term)) (mu : Binding),
    vars.Nodup → ∀ c (hc : c < vars.length), vars[c] = w →
      (zipBindings vars row mu).lookup w = match cellL row c with
        | some t => some t
        | none => mu.lookup w
  | [], _, _, _, c, hc, _ => absurd hc (by simp)
  | v :: vs, row, mu, hnd, 0, _, e => by
    simp only [List.getElem_cons_zero] at e
    subst e
    have hvs : v ∉ vs := (List.nodup_cons.mp hnd).1
    cases row with
    | nil => rfl
    | cons x ts =>
      cases x with
      | some t =>
        simp only [zipBindings, cellL, List.getElem?_cons_zero]
        rw [zip_notin v vs ts _ hvs, lookup_bind', if_pos rfl]
      | none =>
        simp only [zipBindings, cellL, List.getElem?_cons_zero]
        exact zip_notin v vs ts mu hvs
  | v :: vs, row, mu, hnd, c + 1, hc, e => by
    simp only [List.getElem_cons_succ] at e
    have hvs : v ∉ vs := (List.nodup_cons.mp hnd).1
    have hvw : v ≠ w := fun h => hvs (h ▸ e ▸ List.getElem_mem _)
    have ih := zip_at w vs
    cases row with
    | nil => rfl
    | cons x ts =>
      cases x with
      | some t =>
        simp only [zipBindings]
        rw [ih ts _ (List.nodup_cons.mp hnd).2 c (by simp at hc; omega) e]
        simp only [cellL, List.getElem?_cons_succ]
        split <;> simp_all [lookup_bind']
      | none =>
        simp only [zipBindings]
        rw [ih ts _ (List.nodup_cons.mp hnd).2 c (by simp at hc; omega) e]
        simp only [cellL, List.getElem?_cons_succ]

theorem pw_of_get {α : Type} {R : α → α → Prop} : ∀ (A B : List α), A.length = B.length →
    (∀ j (h1 : j < A.length) (h2 : j < B.length), R A[j] B[j]) → IdGroup.Pw R A B
  | [], [], _, _ => .nil
  | a :: A, b :: B, hl, h => .cons (h 0 (by simp) (by simp)) (pw_of_get A B (by simpa using hl)
      fun j h1 h2 => h (j + 1) (by simp; omega) (by simp; omega))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **The VALUES table.** The table of one VALUES block with distinct
    variables, its columns as `resolveValues_spec` gives them, is well formed,
    its rows decode with the decoder of the state to `evalValues` of the
    block, row for row (`BindEq`), and its ids are ids of the state. -/
theorem values_table (voc : Array Term) (vars : List String)
    (rows : List (List (Option Term))) (hnd : vars.Nodup) (cols : Array ByteArray)
    (hc : ColsOk dec ok voc (rows.map List.toArray) vars.length rows.length 0 cols) :
    (Table.WF { vars := vars.toArray, cols, rows := rows.length }) ∧
      IdGroup.Pw IdGroup.BindEq (evalValues vars rows)
        ((Table.idRows { vars := vars.toArray, cols, rows := rows.length }).map (decRow (decV dec voc))) ∧
      ∀ r ∈ Table.idRows { vars := vars.toArray, cols, rows := rows.length }, RowIds (okV ok voc) r := by
  generalize hT : ({ vars := vars.toArray, cols, rows := rows.length } : Table) = T
  have hTv : T.vars = vars.toArray := by rw [← hT]
  have hTc : T.cols = cols := by rw [← hT]
  have hTr : T.rows = rows.length := by rw [← hT]
  have hnd' : T.vars.toList.Nodup := by rw [hTv]; simpa using hnd
  obtain ⟨hsz, hcol⟩ := hc
  -- the cells of the table
  have hat : ∀ c, c < vars.length → ∀ j, j < rows.length →
      CellOk dec ok voc (cellL rows[j]! c) (T.at c j) := by
    intro c hc j hj
    obtain ⟨xs, h1, h2, h3⟩ := hcol c hc
    simp only [Nat.not_lt_zero, if_false, Nat.add_zero] at h2
    have hw : T.at c j = xs[j]'(by omega) := by
      show word64 T.cols[c]! (8 * j) = _
      rw [hTc]; exact h1.word (by omega)
    rw [hw]
    have := h3 j (by omega)
    have e : cellOf (rows.map List.toArray)[j]! c = cellL rows[j]! c := by
      rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
      simp [cellOf, cellL]
    rw [e] at this
    exact this
  refine ⟨⟨by rw [hTc, hTv]; simpa using hsz, fun c hc => ?_, hnd'⟩, ?_, ?_⟩
  · obtain ⟨xs, h1, h2, _⟩ := hcol c (by rw [hTc] at hc; omega)
    simp only [Nat.not_lt_zero, if_false, Nat.add_zero] at h2
    have := h1.1
    simp only [hTc, hTr]
    rw [getElem!_pos _ c (by rw [hTc] at hc; exact hc)] at this
    rw [this, h2]
  · apply pw_of_get
    · simp [evalValues, Table.idRows, hTr]
    · intro j h1 h2
      have hj : j < rows.length := by simpa [evalValues] using h1
      simp only [evalValues, List.getElem_map, Table.idRows, List.getElem_range]
      intro w
      rw [OptJoin.lookup_decRow, TableTheorems.lookup_idRow T hnd' j w]
      unfold Table.lookupAt
      cases hx : T.idx w with
      | some c =>
        obtain ⟨hc, hcw⟩ := TableTheorems.idx_some hx
        have hc' : c < vars.length := by rw [hTv] at hc; simpa using hc
        have hvc : vars[c] = w := by
          have hc2 : c < vars.toArray.size := by simpa using hc'
          rw [hTv, getElem!_pos _ c hc2] at hcw; simpa using hcw
        rw [zip_at w vars rows[j] Binding.empty hnd c hc' hvc]
        have hcell := hat c hc' j hj
        rw [getElem!_pos rows j hj] at hcell
        cases hce : cellL rows[j] c with
        | some t =>
          rw [hce] at hcell
          obtain ⟨_, hne, hd⟩ := hcell
          simp only [beq_iff_eq, hne, if_false, Option.map_some, hd]
        | none =>
          rw [hce] at hcell
          simp only [CellOk] at hcell
          simp only [hcell, beq_self_eq_true, if_true, Option.map_none]
          rfl
      | none =>
        have hnot : w ∉ vars := by
          intro hm
          obtain ⟨c, hc, e⟩ := List.getElem_of_mem hm
          exact TableTheorems.idx_none hx c (by rw [hTv]; simpa using hc) (by rw [hTv, getElem!_pos _ c (by simpa using hc)]; simpa using e)
        rw [zip_notin w vars rows[j] Binding.empty hnot]
        rfl
  · intro r hr
    simp only [Table.idRows, List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    intro p hp
    obtain ⟨c, hc, hne, rfl⟩ := TableTheorems.mem_idRow.mp hp
    have hc' : c < vars.length := by rw [hTv] at hc; simpa using hc
    have hcell := hat c hc' j (by rw [hTr] at hj; exact hj)
    cases hce : cellL rows[j]! c with
    | some t => rw [hce] at hcell; exact hcell.1
    | none => rw [hce] at hcell; exact absurd hcell hne

/-- **VALUES as the nested evaluator runs it** (`IdGroup.valuesNM`): from a
    state with the invariant, it refuses (`LocalRefusal`) or returns a
    well-formed table whose rows decode, with the decoder of the new state,
    to `evalValues` of the block row for row, with ids of the new state; the
    new state keeps the invariant and extends the vocabulary. -/
theorem valuesNM_spec (cx : IdGroup.NCx Id) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (vars : List String) (rows : List (List (Option Term))) (hnd : vars.Nodup)
    (hn : ∀ row ∈ rows, ∀ t, some t ∈ row → normalizeTerm t = t) (nst : IdGroup.NSt) (hi : Inv cid nst) :
    Ends ((IdGroup.valuesNM cx vars rows).run nst) fun T nst' =>
      T.WF ∧ IdGroup.Pw IdGroup.BindEq (evalValues vars rows) (T.idRows.map (decRow (decV dec nst'.vocab))) ∧
        (∀ r ∈ T.idRows, RowIds (okV ok nst'.vocab) r) ∧ Inv cid nst' ∧ nst.vocab.toList <+: nst'.vocab.toList := by
  let b : ValuesBlock := { vars := vars.toArray, rows := (rows.map List.toArray).toArray }
  have hnb : ∀ row ∈ b.rows.toList, ∀ c t, cellOf row c = some t → normalizeTerm t = t := by
    intro row hrow c t ht
    simp only [b, List.mem_map] at hrow
    obtain ⟨r, hr, rfl⟩ := hrow
    apply hn r hr t
    unfold cellOf at ht
    rw [List.getElem?_toArray] at ht
    cases e : r[c]? with
    | none => rw [e] at ht; cases ht
    | some o =>
      rw [e] at ht
      cases o with
      | none => cases ht
      | some t' => cases ht; exact List.mem_of_getElem? e
  unfold IdGroup.valuesNM IdGroup.liftE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
  rcases resolveValues_spec cx.st cid dec ok hid hcid hcidok hcidN hloc hcid0 b hnb nst.vocab nst.localIdx hi with
    ⟨e, he, hr⟩ | ⟨cols, voc', ix', he, h1, h2, h3⟩
  · left
    refine ⟨e, ?_, hr⟩
    rw [he]; rfl
  · right
    rw [he]
    refine ⟨{ vars := b.vars, cols, rows := b.rows.size }, { nst with vocab := voc', localIdx := ix' }, rfl, ?_⟩
    have hc : ColsOk dec ok voc' (rows.map List.toArray) vars.length rows.length 0 cols := by
      simpa [b] using h3
    obtain ⟨t1, t2, t3⟩ := values_table dec ok voc' vars rows hnd cols hc
    simp only [b, List.size_toArray, List.length_map]
    exact ⟨t1, t2, t3, h1, h2⟩

end

end L4Factoidal.Storage.Sbm11.LocalTable

#print axioms L4Factoidal.Storage.Sbm11.LocalTable.forIn_ends
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.resolveValues_spec
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.values_table
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.valuesNM_spec
