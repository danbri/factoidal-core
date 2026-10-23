/-
L4Factoidal.Storage.Sbm11.LocalTableTheorems — the operators of the nested
evaluator that give terms query-local ids: VALUES (`IdQuery.resolveValuesVocabM`)
(https://github.com/danbri/factoidal/issues/776; lemma L4r of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `forIn_ends`: a loop in `ExceptT String Id` whose every step refuses with a
  `LocalVocab.LocalRefusal` or yields keeps an invariant.
* `resolveValues_spec`: for one VALUES block whose variables are distinct,
  `resolveValuesVocabM` refuses (`LocalRefusal`, among them a term that is
  not its own `normalizeTerm`, `IdQuery.valueIdM`) or returns one well-formed table with the
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
    let r ← valueIdM st s.1 s.2.1 t
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
    (voc0 : Array Term)
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
          rcases valueIdM_spec st cid hid dec ok hcid hcidok hcidN hloc hcid0 s.1 s.2.1 hs1 t with
            ⟨e, he, hr⟩ | ⟨y, voc', ix', he, h1, h2, h3, h4, h5⟩
          · left; exact ⟨e, by simp only []; rw [he]; rfl, hr⟩
          · right
            refine ⟨(voc', ix', s.2.2.modify c fun x_1 => L4Factoidal.Qlvr.Side.put64 x_1 y), ?_, h1,
              hs2.trans h2, ?_⟩
            · simp only []; rw [he]; rfl
            · apply colsOk_step dec ok voc' _ _ i c hc _ (colsOk_mono dec hloc h2 h1.size hs3)
              rw [hct]
              exact ⟨h3, h4, h5⟩
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
    (b : ValuesBlock)
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
        (getElem!_pos b.rows.toList i hi) voc s.1 s.2.1 s.2.2 hs1 hs2 hs3 with
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
    (nst : IdGroup.NSt) (hi : Inv cid nst) :
    Ends ((IdGroup.valuesNM cx vars rows).run nst) fun T nst' =>
      T.WF ∧ IdGroup.Pw IdGroup.BindEq (evalValues vars rows) (T.idRows.map (decRow (decV dec nst'.vocab))) ∧
        (∀ r ∈ T.idRows, RowIds (okV ok nst'.vocab) r) ∧ Inv cid nst' ∧ nst.vocab.toList <+: nst'.vocab.toList := by
  let b : ValuesBlock := { vars := vars.toArray, rows := (rows.map List.toArray).toArray }
  unfold IdGroup.valuesNM IdGroup.liftE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
  rcases resolveValues_spec cx.st cid dec ok hid hcid hcidok hcidN hloc hcid0 b nst.vocab nst.localIdx hi with
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

/-! ## BIND: `IdQuery.extendM` -/

open L4Factoidal.SPARQL (Expr EvalEnv bindRowsFresh fxKeyRow fxKeyOcc)
open L4Factoidal.Storage.Sbm11.ExprLocalTheorems (IsFx)

/-- One step of the loop of `extendM` that builds the mapping of the
    variables `e` reads, in row `i`. -/
def muStep (dst : Store Id) (t : Table) (vs : Array String) (cols : Array (Option Nat)) (i k : Nat)
    (mu : Binding) : ExceptT String Id (ForInStep Binding) :=
  match cols[k]! with
  | some c =>
    if (t.at c i != unbound) = true then do
      let term ← dst.termOf (t.at c i)
      pure (.yield (mu ++ [(vs[k]!, term)]))
    else pure (.yield mu)
  | none => pure (.yield mu)

/-- The state of the row loop of `extendM`: vocabulary, its index, the memo
    of values by the ids `e` reads, the column. -/
abbrev BSt := Array Term × Std.HashMap Term Nat × Std.HashMap (List UInt64) UInt64 × ByteArray

/-- One step of the row loop of `extendM`. -/
def bindStep (st : Store Id) (env : EvalEnv) (t : Table) (e : Expr) (v : String) (vs : Array String)
    (cols : Array (Option Nat)) (dst : Store Id) (existing : Option Nat) (i : Nat) (s : BSt) :
    ExceptT String Id (ForInStep BSt) :=
  let old := match existing with | some c => t.at c i | none => unbound
  if (old == unbound) = true then
    let ids := (cols.map fun c => match c with | some c => t.at c i | none => unbound).toList
    match s.2.2.1.get? ids with
    | some y => pure (.yield (s.1, s.2.1, s.2.2.1, L4Factoidal.Qlvr.Side.put64 s.2.2.2 y))
    | none => do
      let mu ← forIn (List.range' 0 vs.size) ([] : Binding) (muStep dst t vs cols i)
      match refBinder env e Graph.empty (Binding.withFreshnessCtx (toString i) v mu) with
      | some term => do
        let r ← valueIdM st s.1 s.2.1 term
        pure (.yield (r.2.1, r.2.2, s.2.2.1.insert ids r.1, L4Factoidal.Qlvr.Side.put64 s.2.2.2 r.1))
      | none => pure (.yield (s.1, s.2.1, s.2.2.1.insert ids old, L4Factoidal.Qlvr.Side.put64 s.2.2.2 old))
  else pure (.yield (s.1, s.2.1, s.2.2.1, L4Factoidal.Qlvr.Side.put64 s.2.2.2 old))

/-- The table `extendM` returns for the column `out` of `?v`. -/
def extTable (t : Table) (v : String) (existing : Option Nat) (out : ByteArray) : Table :=
  match existing with
  | some c => { t with cols := t.cols.set! c out }
  | none => { t with vars := t.vars.push v, cols := t.cols.push out }

theorem extendM_eq (st : Store Id) (env : EvalEnv) (t : Table) (e : Expr) (v : String) (voc0 : Array Term)
    (ix0 : Std.HashMap Term Nat) :
    extendM st env t e v voc0 ix0 = (do
      let s ← forIn (List.range' 0 t.rows) (voc0, ix0, (∅ : Std.HashMap (List UInt64) UInt64),
          ByteArray.emptyWithCapacity (8 * t.rows))
        (bindStep st env t e v ((residualVars e).getD #[]) (((residualVars e).getD #[]).map t.idx)
          (st.withLocal voc0) (t.idx v))
      pure (extTable t v (t.idx v) s.2.2.2, s.1, s.2.1)) := by
  unfold extendM
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem lookup_append_one (w a : String) (b : Term) :
    ∀ (mu : Binding), Binding.lookup w (mu ++ [(a, b)]) =
      match Binding.lookup w mu with
      | some x => some x
      | none => if a = w then some b else none
  | [] => by simp [Binding.lookup]
  | (a', b') :: rest => by
    simp only [List.cons_append, Binding.lookup]
    split
    · rfl
    · exact lookup_append_one w a b rest

theorem lookup_fresh (s o : String) (mu : Binding) (w : String) (hw : ¬ IsFx w) :
    (Binding.withFreshnessCtx s o mu).lookup w = mu.lookup w := by
  unfold Binding.withFreshnessCtx
  simp only [Binding.lookup]
  rw [if_neg (fun h => hw (Or.inl h.symm)), if_neg (fun h => hw (Or.inr h.symm))]

/-- **The value of a BIND expression is local**: on two mappings with the
    same lookup for each variable of `residualVars e`, with any freshness
    contexts, an EXISTS-free expression that reads no freshness key has the
    same value. -/
theorem refBinder_local (env : EvalEnv) (e : Expr) (vs : Array String) (hvs : residualVars e = some vs)
    (hef : e.existsFree = true) (hfx : ∀ w ∈ e.refVars, ¬ IsFx w) (a1 a2 : Graph) (s1 s2 o : String)
    (mu1 mu2 : Binding) (h : ∀ w ∈ vs.toList, Binding.lookup w mu1 = Binding.lookup w mu2) :
    refBinder env e a1 (Binding.withFreshnessCtx s1 o mu1) = refBinder env e a2 (Binding.withFreshnessCtx s2 o mu2) := by
  unfold refBinder
  simp only []
  rw [IdPostTheorems.substituteExistentials_existsFree env a1 _ e hef,
    IdPostTheorems.substituteExistentials_existsFree env a2 _ e hef]
  congr 1
  apply ExprLocalTheorems.evalIn_congr env env _ _ e _ (Or.inr (ExprLocalTheorems.EnvAgree.refl env))
  intro w hw
  rw [ExprLocalTheorems.lookup_merge_empty, ExprLocalTheorems.lookup_merge_empty,
    lookup_fresh _ _ _ w (hfx w hw), lookup_fresh _ _ _ w (hfx w hw)]
  rcases ExprLocalTheorems.residualVars_spec e vs hvs w hw with h' | h'
  · exact h w h'
  · exact absurd h' (hfx w hw)

section
variable (st : Store Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)

/-- The mapping `extendM` builds for row `i`: for each variable of `vs`, the
    decoded id of its column in row `i`. -/
theorem mu_spec (htermOf : ∀ x, ok x → st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc0 : Array Term} {ix0 : Std.HashMap Term Nat} (hinv : VocInv cid voc0 ix0)
    (t : Table) (hnd : t.vars.toList.Nodup) (vs : Array String) (i : Nat)
    (hrow : RowIds (okV ok voc0) (t.idRow i)) :
    ∃ mu, forIn (List.range' 0 vs.size) ([] : Binding)
        (muStep (st.withLocal voc0) t vs (vs.map t.idx) i) = pure mu ∧
      ∀ w ∈ vs.toList, Binding.lookup w mu = Binding.lookup w (decRow (decV dec voc0) (t.idRow i)) := by
  -- the lookup of the decoded row
  have hrl : ∀ w, (decRow (decV dec voc0) (t.idRow i)).lookup w = (t.lookupAt i w).map (decV dec voc0) := by
    intro w; rw [OptJoin.lookup_decRow, TableTheorems.lookup_idRow t hnd i w]
  have hold : ∀ (n : Nat) (w : String), w ≠ vs[n]! →
      ((∃ k, k < n + 1 ∧ vs[k]! = w) ↔ ∃ k, k < n ∧ vs[k]! = w) := by
    intro n w hw
    constructor
    · rintro ⟨k, hk, e⟩
      refine ⟨k, ?_, e⟩
      rcases Nat.lt_or_ge k n with h | h
      · exact h
      · have : k = n := by omega
        subst this; exact absurd e.symm hw
    · rintro ⟨k, hk, e⟩; exact ⟨k, by omega, e⟩
  obtain ⟨mu, h1, h2⟩ := forIn_yields (muStep (st.withLocal voc0) t vs (vs.map t.idx) i) (List.range' 0 vs.size)
    (fun n (mu : Binding) => ∀ w, mu.lookup w =
      if ∃ k, k < n ∧ vs[k]! = w then (t.lookupAt i w).map (decV dec voc0) else none)
    [] (fun w => by simp [Binding.lookup]) (by
      intro n hn mu h2
      rw [List.length_range'] at hn
      rw [List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hcol : (vs.map t.idx)[n]! = t.idx vs[n]! := by
        rw [getElem!_pos _ n (by simp; omega), getElem!_pos vs n (by omega)]; simp
      unfold muStep
      rw [hcol]
      cases hx : t.idx vs[n]! with
      | none =>
        refine ⟨mu, rfl, fun w => ?_⟩
        rw [h2 w]
        by_cases hw : w = vs[n]!
        · subst hw
          have hl : t.lookupAt i vs[n]! = none := by unfold Table.lookupAt; rw [hx]
          rw [hl]; simp
        · simp only [hold n w hw]
      | some c =>
        dsimp only
        by_cases hb : (t.at c i != unbound) = true
        · rw [if_pos hb]
          have hmem : (vs[n]!, t.at c i) ∈ t.idRow i := by
            obtain ⟨hc, hv⟩ := TableTheorems.idx_some hx
            rw [TableTheorems.mem_idRow]
            exact ⟨c, hc, by simpa using hb, by rw [hv]⟩
          have hok := hrow _ hmem
          rw [termOf_withLocal st cid dec ok htermOf hloc hinv _ hok]
          refine ⟨mu ++ [(vs[n]!, decV dec voc0 (t.at c i))], rfl, fun w => ?_⟩
          rw [lookup_append_one, h2 w]
          by_cases hw : w = vs[n]!
          · subst hw
            have hl : t.lookupAt i vs[n]! = some (t.at c i) := by
              unfold Table.lookupAt; rw [hx]; simp only []; rw [if_neg (by simpa using hb)]
            rw [hl, if_pos (⟨n, by omega, rfl⟩ : ∃ k, k < n + 1 ∧ vs[k]! = vs[n]!)]
            by_cases hseen : ∃ k, k < n ∧ vs[k]! = vs[n]!
            · rw [if_pos hseen]; rfl
            · rw [if_neg hseen]; simp
          · rw [if_neg (Ne.symm hw)]
            simp only [hold n w hw]
            by_cases hs : ∃ k, k < n ∧ vs[k]! = w
            · rw [if_pos hs]; cases Option.map (decV dec voc0) (t.lookupAt i w) <;> rfl
            · rw [if_neg hs]
        · rw [if_neg hb]
          refine ⟨mu, rfl, fun w => ?_⟩
          rw [h2 w]
          by_cases hw : w = vs[n]!
          · subst hw
            have hl : t.lookupAt i vs[n]! = none := by
              unfold Table.lookupAt; rw [hx]; simp only []; rw [if_pos (by simpa using hb)]
            rw [hl]; simp
          · simp only [hold n w hw])
  refine ⟨mu, h1, fun w hw => ?_⟩
  rw [List.length_range'] at h2
  rw [h2 w, hrl w, if_pos]
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hw
  exact ⟨k, by simpa using hk, by rw [getElem!_pos vs k (by simpa using hk)]; simpa using e⟩

/-- The id of `?v` in row `i` before the BIND (`unbound` when `t` has no
    column `?v`). -/
def oldOf (t : Table) (v : String) (i : Nat) : UInt64 :=
  match t.idx v with
  | some c => t.at c i
  | none => unbound

/-- The ids `extendM` memoises the value of row `i` by. -/
def idsOf (t : Table) (vs : Array String) (i : Nat) : List UInt64 :=
  ((vs.map t.idx).map fun c => match c with | some c => t.at c i | none => unbound).toList

/-- The value of the BIND expression on row `i` of `t`, decoded by `D`, with
    the freshness context of row `i`. -/
def bvOf (env : EvalEnv) (e : Expr) (v : String) (D : UInt64 → Term) (t : Table) (i : Nat) : Option Term :=
  refBinder env e Graph.empty (Binding.withFreshnessCtx (toString i) v (decRow D (t.idRow i)))

/-- The id `extendM` writes in row `i`: the old id when there is one, else
    the id of the value (`CellOk`). -/
def ValOk (dec : UInt64 → Term) (ok : UInt64 → Prop) (voc : Array Term) (old : UInt64) (b : Option Term)
    (x : UInt64) : Prop :=
  if old = unbound then CellOk dec ok voc b x else x = old

theorem valOk_mono (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60) {old : UInt64}
    {b : Option Term} {x : UInt64} (h : ValOk dec ok voc1 old b x) : ValOk dec ok voc2 old b x := by
  unfold ValOk at h ⊢
  split at h
  · rw [if_pos (by assumption)]; exact cellOk_mono dec hloc hp hsz _ _ h
  · rw [if_neg (by assumption)]; exact h

/-- Rows with the same ids in the columns of `vs` give the expression the same
    value. -/
theorem bv_eq (env : EvalEnv) (e : Expr) (v : String) (D : UInt64 → Term) (vs : Array String)
    (hvs : residualVars e = some vs) (hef : e.existsFree = true) (hfx : ∀ w ∈ e.refVars, ¬ IsFx w)
    (t : Table) (hnd : t.vars.toList.Nodup) (i j : Nat) (h : idsOf t vs i = idsOf t vs j) :
    bvOf env e v D t i = bvOf env e v D t j := by
  unfold bvOf
  apply refBinder_local env e vs hvs hef hfx
  intro w hw
  rw [OptJoin.lookup_decRow, OptJoin.lookup_decRow, TableTheorems.lookup_idRow t hnd i w,
    TableTheorems.lookup_idRow t hnd j w]
  obtain ⟨k, hk, ek⟩ := List.getElem_of_mem hw
  simp only [Array.length_toList] at hk
  have hk' := congrArg (fun l : List UInt64 => l[k]?) h
  simp only [idsOf, Array.toList_map, List.getElem?_map, Array.getElem?_toList] at hk'
  rw [Array.getElem?_eq_getElem hk] at hk'
  simp only [Option.map_some, Option.some.injEq, Array.getElem_toList] at hk' ek
  rw [ek] at hk'
  unfold Table.lookupAt
  cases hx : t.idx w with
  | none => rfl
  | some c => rw [hx] at hk'; simp only [] at hk' ⊢; rw [hk']

section
variable (st : Store Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)

/-- **The row loop of `extendM`.** -/
theorem extendM_spec (hid : ∀ t, st.idOf t = pure (cid t)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (htermOf : ∀ x, ok x → st.termOf x = pure (dec x))
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (env : EvalEnv) (e : Expr) (v : String) (vs : Array String) (hvs : residualVars e = some vs)
    (hef : e.existsFree = true) (hfx : ∀ w ∈ e.refVars, ¬ IsFx w)
    (t : Table) (hnd : t.vars.toList.Nodup) (voc0 : Array Term) (ix0 : Std.HashMap Term Nat)
    (hinv : VocInv cid voc0 ix0) (hrows : ∀ i, i < t.rows → RowIds (okV ok voc0) (t.idRow i)) :
    (∃ e', extendM st env t e v voc0 ix0 = throw e' ∧ LocalRefusal e') ∨
      ∃ out voc' ix', extendM st env t e v voc0 ix0 = pure (extTable t v (t.idx v) out, voc', ix') ∧
        VocInv cid voc' ix' ∧ voc0.toList <+: voc'.toList ∧
        ∃ xs : List UInt64, ColHolds out xs ∧ xs.length = t.rows ∧
          ∀ j (hj : j < xs.length), ValOk dec ok voc' (oldOf t v j) (bvOf env e v (decV dec voc0) t j) xs[j] := by
  rw [extendM_eq, hvs, Option.getD_some]
  let P : Nat → BSt → Prop := fun i s =>
    VocInv cid s.1 s.2.1 ∧ voc0.toList <+: s.1.toList ∧
    (∃ xs : List UInt64, ColHolds s.2.2.2 xs ∧ xs.length = i ∧
      ∀ j (hj : j < xs.length), ValOk dec ok s.1 (oldOf t v j) (bvOf env e v (decV dec voc0) t j) xs[j]) ∧
    ∀ ids y, s.2.2.1[ids]? = some y → ∃ j, j < i ∧ idsOf t vs j = ids ∧ oldOf t v j = unbound ∧
      CellOk dec ok s.1 (bvOf env e v (decV dec voc0) t j) y
  have := forIn_ends (bindStep st env t e v vs (vs.map t.idx) (st.withLocal voc0) (t.idx v)) (List.range' 0 t.rows) P
    (voc0, ix0, ∅, ByteArray.emptyWithCapacity (8 * t.rows))
    ⟨hinv, List.prefix_refl _, ⟨[], ColHolds.nil _ rfl, rfl, fun j hj => absurd hj (by simp)⟩,
      fun ids y h => by simp at h⟩ (by
      intro i hi s ⟨hs1, hs2, ⟨xs, hx1, hx2, hx3⟩, hs4⟩
      rw [List.length_range'] at hi
      rw [List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hold : (match t.idx v with | some c => t.at c i | none => unbound) = oldOf t v i := rfl
      -- the column after appending `x` with `ValOk` at row `i`
      have hcol : ∀ (voc' : Array Term) (x : UInt64), voc0.toList <+: voc'.toList → s.1.toList <+: voc'.toList →
          voc'.size ≤ two60 → ValOk dec ok voc' (oldOf t v i) (bvOf env e v (decV dec voc0) t i) x →
          ∃ xs' : List UInt64, ColHolds (L4Factoidal.Qlvr.Side.put64 s.2.2.2 x) xs' ∧ xs'.length = i + 1 ∧
            ∀ j (hj : j < xs'.length), ValOk dec ok voc' (oldOf t v j) (bvOf env e v (decV dec voc0) t j) xs'[j] := by
        intro voc' x _ hp' hsz hv
        refine ⟨xs ++ [x], hx1.put64 x, by simp [hx2], fun j hj => ?_⟩
        by_cases hj' : j < xs.length
        · rw [List.getElem_append_left hj']; exact valOk_mono dec hloc hp' hsz (hx3 j hj')
        · have : j = xs.length := by simp at hj; omega
          subst this
          rw [List.getElem_append_right (by omega)]
          simp only [Nat.sub_self, List.getElem_singleton]
          rw [hx2]; exact hv
      unfold bindStep
      simp only []
      rw [hold]
      by_cases hob : (oldOf t v i == unbound) = true
      · rw [if_pos hob]
        have hou : oldOf t v i = unbound := by simpa using hob
        rw [Std.HashMap.get?_eq_getElem?]
        have hids : (Array.map (fun c => match c with | some c => t.at c i | none => unbound)
            (Array.map t.idx vs)).toList = idsOf t vs i := rfl
        rw [hids]
        cases hm : s.2.2.1[idsOf t vs i]? with
        | some y =>
          obtain ⟨j, hj, hjids, hjold, hjc⟩ := hs4 _ y hm
          have hbv : bvOf env e v (decV dec voc0) t i = bvOf env e v (decV dec voc0) t j := bv_eq env e v _ vs hvs hef hfx t hnd i j hjids.symm
          right
          refine ⟨(s.1, s.2.1, s.2.2.1, L4Factoidal.Qlvr.Side.put64 s.2.2.2 y), rfl,
            hs1, hs2, hcol s.1 y hs2 (List.prefix_refl _) hs1.size (by unfold ValOk; rw [if_pos hou, hbv]; exact hjc),
            fun ids y' h => let ⟨j', h1, h2, h3, h4⟩ := hs4 ids y' h; ⟨j', by omega, h2, h3, h4⟩⟩
        | none =>
          obtain ⟨mu, hmu, hml⟩ := mu_spec st cid dec ok htermOf hloc hinv t hnd vs i (hrows i hi)
          have hbmu : refBinder env e Graph.empty (Binding.withFreshnessCtx (toString i) v mu) = bvOf env e v (decV dec voc0) t i :=
            refBinder_local env e vs hvs hef hfx _ _ _ _ v _ _ hml
          simp only [hmu, pure_bind, hbmu]
          cases hb : bvOf env e v (decV dec voc0) t i with
          | none =>
            right
            refine ⟨(s.1, s.2.1, s.2.2.1.insert (idsOf t vs i) (oldOf t v i),
              L4Factoidal.Qlvr.Side.put64 s.2.2.2 (oldOf t v i)), rfl, hs1, hs2, hcol s.1 _ hs2 (List.prefix_refl _)
              hs1.size (by unfold ValOk; rw [if_pos hou, hb, hou]; rfl), ?_⟩
            intro ids y h
            rw [Std.HashMap.getElem?_insert] at h
            split at h
            · next he =>
              cases h
              exact ⟨i, by omega, by simpa [idsOf] using he, hou, by rw [hb]; exact hou⟩
            · obtain ⟨j', h1, h2, h3, h4⟩ := hs4 ids y h
              exact ⟨j', by omega, h2, h3, h4⟩
          | some r =>
            rcases valueIdM_spec st cid hid dec ok hcid hcidok hcidN hloc hcid0 s.1 s.2.1 hs1 r with
              ⟨e', he, hr'⟩ | ⟨y, voc', ix', he, h1, h2, h3, h4, h5⟩
            · left; exact ⟨e', by simp only []; rw [he]; rfl, hr'⟩
            · right
              have hcv : CellOk dec ok voc' (bvOf env e v (decV dec voc0) t i) y := by rw [hb]; exact ⟨h3, h4, h5⟩
              refine ⟨(voc', ix', s.2.2.1.insert (idsOf t vs i) y, L4Factoidal.Qlvr.Side.put64 s.2.2.2 y),
                by simp only []; rw [he]; rfl, h1, hs2.trans h2, hcol voc' y (hs2.trans h2) h2 h1.size
                (by unfold ValOk; rw [if_pos hou]; exact hcv), ?_⟩
              intro ids y' h
              simp only [] at h
              rw [Std.HashMap.getElem?_insert] at h
              split at h
              · next he' =>
                cases h
                exact ⟨i, by omega, by simpa [idsOf] using he', hou, hcv⟩
              · obtain ⟨j', h1', h2', h3', h4'⟩ := hs4 ids y' h
                exact ⟨j', by omega, h2', h3', cellOk_mono dec hloc h2 h1.size _ _ h4'⟩
      · rw [if_neg hob]
        right
        refine ⟨(s.1, s.2.1, s.2.2.1, L4Factoidal.Qlvr.Side.put64 s.2.2.2 (oldOf t v i)), rfl, hs1, hs2,
          hcol s.1 _ hs2 (List.prefix_refl _) hs1.size (by unfold ValOk; rw [if_neg (by simpa using hob)]), ?_⟩
        intro ids y h
        obtain ⟨j', h1, h2, h3, h4⟩ := hs4 ids y h
        exact ⟨j', by omega, h2, h3, h4⟩)
  rw [List.length_range'] at this
  rcases this with ⟨e', he, hr⟩ | ⟨s', he, h1, h2, ⟨xs, hx1, hx2, hx3⟩, _⟩
  · left; exact ⟨e', by rw [he]; rfl, hr⟩
  · right
    exact ⟨s'.2.2.2, s'.1, s'.2.1, by rw [he]; rfl, h1, h2, xs, hx1, hx2, hx3⟩

end

/-! ## The table `extendM` returns -/

theorem lookupAt_old (t : Table) (v : String) (j : Nat) :
    t.lookupAt j v = if oldOf t v j = unbound then none else some (oldOf t v j) := by
  unfold Table.lookupAt oldOf
  cases t.idx v with
  | none => simp
  | some c => simp only [beq_iff_eq]

/-- The table `extendM` returns: well formed, and its lookups are those of
    `t`, but `?v`, which holds the new column. -/
theorem ext_table (t : Table) (ht : t.WF) (v : String) (out : ByteArray) (xs : List UInt64)
    (hx1 : ColHolds out xs) (hx2 : xs.length = t.rows) :
    (extTable t v (t.idx v) out).WF ∧ (extTable t v (t.idx v) out).rows = t.rows ∧
      ∀ j, j < t.rows → ∀ w, (extTable t v (t.idx v) out).lookupAt j w =
        if w = v then (if xs[j]! = unbound then none else some xs[j]!) else t.lookupAt j w := by
  have hout : out.size = 8 * t.rows := by rw [hx1.1, hx2]
  have hword : ∀ j, j < t.rows → word64 out (8 * j) = xs[j]! := by
    intro j hj
    rw [getElem!_pos xs j (by omega)]
    exact hx1.word (by omega)
  unfold extTable
  cases hv : t.idx v with
  | some c =>
    obtain ⟨hc, hcv⟩ := TableTheorems.idx_some hv
    have hcs : c < t.cols.size := by rw [ht.cols_size]; exact hc
    have hat : ∀ c' j, ({ t with cols := t.cols.set! c out } : Table).at c' j =
        if c' = c then word64 out (8 * j) else t.at c' j := by
      intro c' j
      show word64 (t.cols.set! c out)[c']! (8 * j) = _
      rw [Array.set!_eq_setIfInBounds]
      by_cases e : c' = c
      · subst e
        rw [if_pos rfl, getElem!_pos _ c' (by simpa using hcs), Array.getElem_setIfInBounds_self]
      · rw [if_neg e]
        show _ = word64 t.cols[c']! (8 * j)
        congr 1
        by_cases hc' : c' < t.cols.size
        · rw [getElem!_pos _ c' (by simpa using hc'), getElem!_pos _ c' hc',
            Array.getElem_setIfInBounds_ne hc' (Ne.symm e)]
        · rw [getElem!_neg _ c' (by simpa using hc'), getElem!_neg _ c' hc']
    refine ⟨⟨by simpa using ht.cols_size, fun c' hc' => ?_, ht.nodup⟩, rfl, fun j hj w => ?_⟩
    · simp only [Array.size_set!] at hc'
      show (t.cols.set! c out)[c'].size = 8 * t.rows
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds hc']
      split
      · exact hout
      · exact ht.col_bytes c' hc'
    · show (match t.idx w with
        | some c' => if ({ t with cols := t.cols.set! c out } : Table).at c' j == unbound then none
            else some (({ t with cols := t.cols.set! c out } : Table).at c' j)
        | none => none) = _
      by_cases hw : w = v
      · subst hw
        rw [hv, if_pos rfl]
        simp only []
        rw [hat, if_pos rfl, hword j hj]
        simp only [beq_iff_eq]
      · rw [if_neg hw]
        unfold Table.lookupAt
        cases hx : t.idx w with
        | none => rfl
        | some c' =>
          have hne : c' ≠ c := by
            intro e; subst e
            obtain ⟨_, h1⟩ := TableTheorems.idx_some hx
            exact hw (h1.symm.trans hcv)
          simp only []
          rw [hat, if_neg hne]
  | none =>
    have hnot : v ∉ t.vars.toList := by
      intro hm
      obtain ⟨c, hc, e⟩ := List.getElem_of_mem hm
      exact TableTheorems.idx_none hv c (by simpa using hc) (by rw [getElem!_pos _ c (by simpa using hc)]; simpa using e)
    have hat : ∀ c' j, ({ t with vars := t.vars.push v, cols := t.cols.push out } : Table).at c' j =
        if c' = t.cols.size then word64 out (8 * j) else t.at c' j := by
      intro c' j
      show word64 (t.cols.push out)[c']! (8 * j) = _
      by_cases e : c' = t.cols.size
      · subst e
        rw [if_pos rfl, getElem!_pos _ _ (by simp), Array.getElem_push_eq]
      · rw [if_neg e]
        show _ = word64 t.cols[c']! (8 * j)
        congr 1
        by_cases hc' : c' < t.cols.size
        · rw [getElem!_pos _ c' (by simp; omega), getElem!_pos _ c' hc', Array.getElem_push_lt]
        · rw [getElem!_neg _ c' (by simp; omega), getElem!_neg _ c' hc']
    have hidx : ∀ w, ({ t with vars := t.vars.push v, cols := t.cols.push out } : Table).idx w =
        if w = v then some t.cols.size else t.idx w := by
      intro w
      show (t.vars.push v).findIdx? (· == w) = _
      rw [Array.findIdx?_push]
      by_cases e : w = v
      · subst e
        have : t.vars.findIdx? (· == w) = none := hv
        rw [this, if_pos rfl, ht.cols_size]; simp
      · rw [if_neg e]
        have : (v == w) = false := by simpa using Ne.symm e
        rw [this]
        simp only [Bool.false_eq_true, if_false, Option.or_none]
        rfl
    refine ⟨⟨by simp [ht.cols_size], fun c' hc' => ?_, ?_⟩, rfl, fun j hj w => ?_⟩
    · simp only [Array.size_push] at hc'
      show (t.cols.push out)[c'].size = 8 * t.rows
      by_cases e : c' = t.cols.size
      · subst e; rw [Array.getElem_push_eq]; exact hout
      · rw [Array.getElem_push_lt (by omega)]; exact ht.col_bytes c' (by omega)
    · show (t.vars.push v).toList.Nodup
      rw [Array.toList_push]
      exact List.nodup_append.mpr ⟨ht.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, by
        intro a ha b hb e; simp at hb; subst hb; subst e; exact hnot ha⟩
    · show (match ({ t with vars := t.vars.push v, cols := t.cols.push out } : Table).idx w with
        | some c' => if ({ t with vars := t.vars.push v, cols := t.cols.push out } : Table).at c' j == unbound then none
            else some (({ t with vars := t.vars.push v, cols := t.cols.push out } : Table).at c' j)
        | none => none) = _
      rw [hidx w]
      by_cases hw : w = v
      · rw [if_pos hw, if_pos hw]
        simp only []
        rw [hat, if_pos rfl, hword j hj]
        simp only [beq_iff_eq]
      · rw [if_neg hw, if_neg hw]
        unfold Table.lookupAt
        cases hx : t.idx w with
        | none => rfl
        | some c' =>
          obtain ⟨h1, _⟩ := TableTheorems.idx_some hx
          have hne : c' ≠ t.cols.size := by rw [ht.cols_size]; omega
          simp only []
          rw [hat, if_neg hne]

/-- One row of `bindRowsFresh`. -/
def bindRow (b : Graph → Binding → Option Term) (a : Graph) (v : String) (mu : Binding) (i : Nat) : Binding :=
  match b a (Binding.withFreshnessCtx (toString i) v mu) with
  | some t => match Binding.lookup v mu with
    | some _ => mu
    | none => mu.bind v t
  | none => mu

theorem bindRowsFresh_length (b : Graph → Binding → Option Term) (a : Graph) (v : String) :
    ∀ (L : List Binding) (k : Nat), (bindRowsFresh b a v L k).length = L.length
  | [], _ => rfl
  | _ :: L, k => by simp [bindRowsFresh, bindRowsFresh_length b a v L (k + 1)]

theorem bindRowsFresh_get (b : Graph → Binding → Option Term) (a : Graph) (v : String) :
    ∀ (L : List Binding) (k j : Nat) (h1 : j < (bindRowsFresh b a v L k).length) (h2 : j < L.length),
      (bindRowsFresh b a v L k)[j] = bindRow b a v L[j] (k + j)
  | [], _, _, _, h2 => absurd h2 (by simp)
  | mu :: L, k, 0, _, _ => by simp [bindRowsFresh, bindRow]; rfl
  | mu :: L, k, j + 1, h1, h2 => by
    simp only [bindRowsFresh, List.getElem_cons_succ]
    rw [bindRowsFresh_get b a v L (k + 1) j (by simp [bindRowsFresh_length] at h1 ⊢; omega) (by simp at h2; omega)]
    congr 1
    omega

section
variable (st : Store Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)

/-- **The rows of the BIND table.** Decoded with the decoder of the final
    state, the rows of the table `extendM` returns are `bindRowsFresh` of the
    reference binder (`IdGroup.binderFn`) on the decoded rows of `t`, row for
    row (`BindEq`), and its ids are ids of the final state. -/
theorem ext_rows (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (env : EvalEnv) (e : Expr) (v : String) (vs : Array String)
    (hvs : residualVars e = some vs) (hef : e.existsFree = true) (hfx : ∀ w ∈ e.refVars, ¬ IsFx w)
    (t : Table) (ht : t.WF) (voc0 vocF : Array Term) (hp : voc0.toList <+: vocF.toList) (hsz : vocF.size ≤ two60)
    (hrows : ∀ i, i < t.rows → RowIds (okV ok voc0) (t.idRow i)) (out : ByteArray) (xs : List UInt64)
    (hx1 : ColHolds out xs) (hx2 : xs.length = t.rows)
    (hx3 : ∀ j (hj : j < xs.length), ValOk dec ok vocF (oldOf t v j) (bvOf env e v (decV dec voc0) t j) xs[j])
    (a : Graph) :
    IdGroup.Pw IdGroup.BindEq (bindRowsFresh (IdGroup.binderFn env e) a v (t.idRows.map (decRow (decV dec vocF))) 0)
        ((extTable t v (t.idx v) out).idRows.map (decRow (decV dec vocF))) ∧
      ∀ r ∈ (extTable t v (t.idx v) out).idRows, RowIds (okV ok vocF) r := by
  obtain ⟨hwf, hrw, hlk⟩ := ext_table t ht v out xs hx1 hx2
  have hrowF : ∀ j, j < t.rows → decRow (decV dec vocF) (t.idRow j) = decRow (decV dec voc0) (t.idRow j) :=
    fun j hj => decRow_mono dec hloc hp hsz _ (hrows j hj)
  -- the decoders agree on the ids of `t`
  have hmapF : ∀ j, j < t.rows → ∀ w, (t.lookupAt j w).map (decV dec vocF) = (t.lookupAt j w).map (decV dec voc0) := by
    intro j hj w
    cases hl : t.lookupAt j w with
    | none => rfl
    | some x =>
      have hm : (w, x) ∈ t.idRow j := by
        have := TableTheorems.lookup_idRow t ht.nodup j w
        rw [hl] at this
        exact OptJoin.idLookup_mem this
      simp only [Option.map_some, decV_mono dec hloc hp hsz (hrows j hj _ hm)]
  have hval : ∀ j (hj : j < t.rows), ValOk dec ok vocF (oldOf t v j) (bvOf env e v (decV dec voc0) t j) xs[j]! := by
    intro j hj; rw [getElem!_pos xs j (by omega)]; exact hx3 j (by omega)
  refine ⟨?_, ?_⟩
  · apply pw_of_get
    · rw [bindRowsFresh_length]; simp [Table.idRows, hrw]
    · intro j h1 h2
      have hj : j < t.rows := by simpa [Table.idRows, hrw] using h2
      rw [bindRowsFresh_get _ _ _ _ _ _ h1 (by simpa [Table.idRows] using hj)]
      simp only [List.getElem_map, Table.idRows, List.getElem_range, Nat.zero_add]
      rw [hrowF j hj]
      have hb : IdGroup.binderFn env e a (Binding.withFreshnessCtx (toString j) v (decRow (decV dec voc0) (t.idRow j))) =
          bvOf env e v (decV dec voc0) t j :=
        refBinder_local env e vs hvs hef hfx a Graph.empty _ _ v _ _ (fun _ _ => rfl)
      intro w
      rw [OptJoin.lookup_decRow, TableTheorems.lookup_idRow _ hwf.nodup j w, hlk j hj w]
      have hmu : ∀ w', Binding.lookup w' (decRow (decV dec voc0) (t.idRow j)) = (t.lookupAt j w').map (decV dec voc0) :=
        fun w' => by rw [OptJoin.lookup_decRow, TableTheorems.lookup_idRow t ht.nodup j w']
      have hv := hval j hj
      unfold bindRow
      rw [hb]
      by_cases hw : w = v
      · subst hw
        rw [if_pos rfl, hmu, lookupAt_old]
        unfold ValOk at hv
        by_cases ho : oldOf t w j = unbound
        · rw [if_pos ho] at hv ⊢
          simp only [Option.map_none]
          cases hbv : bvOf env e w (decV dec voc0) t j with
          | none =>
            rw [hbv] at hv
            simp only [CellOk] at hv
            simp only [hv, if_true, Option.map_none]
            rw [hmu, lookupAt_old, if_pos ho]; rfl
          | some term =>
            rw [hbv] at hv
            obtain ⟨_, hne, hd⟩ := hv
            simp only []
            rw [if_neg hne, Option.map_some, hd, lookup_bind', if_pos rfl]
        · rw [if_neg ho] at hv ⊢
          rw [hv, if_neg ho]
          simp only [Option.map_some]
          have hold : (oldOf t w j) ∈ (t.idRow j).map Prod.snd := by
            have := TableTheorems.lookup_idRow t ht.nodup j w
            rw [lookupAt_old, if_neg ho] at this
            exact List.mem_map.mpr ⟨_, OptJoin.idLookup_mem this, rfl⟩
          obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hold
          have hokq := hrows j hj q hq
          rw [hqe] at hokq
          rw [decV_mono dec hloc hp hsz hokq]
          split <;> (try split) <;> (rw [hmu, lookupAt_old, if_neg ho]; rfl)
      · rw [if_neg hw, hmapF j hj w]
        have hlw : ∀ (mu : Binding) (term : Term), Binding.lookup w (mu.bind v term) = Binding.lookup w mu := by
          intro mu term; rw [lookup_bind', if_neg (Ne.symm hw)]
        split
        · split
          · rw [hmu]
          · rw [hlw, hmu]
        · rw [hmu]
  · intro r hr pr hpr
    simp only [Table.idRows, List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    rw [hrw] at hj
    have hl := BgpTableTheorems.nd_mem_lookup (BgpTableTheorems.nd_idRows _ hwf.nodup _
      (List.mem_map.mpr ⟨j, List.mem_range.mpr (by rw [hrw]; exact hj), rfl⟩)) pr hpr
    rw [TableTheorems.lookup_idRow _ hwf.nodup j pr.1, hlk j hj pr.1] at hl
    by_cases hw : pr.1 = v
    · rw [if_pos hw] at hl
      have hv := hval j hj
      by_cases hu : xs[j]! = unbound
      · rw [if_pos hu] at hl; cases hl
      · rw [if_neg hu] at hl
        have hp2 : pr.2 = xs[j]! := (Option.some.inj hl).symm
        rw [hp2]
        unfold ValOk at hv
        split at hv
        · cases hbv : bvOf env e v (decV dec voc0) t j with
          | none => rw [hbv] at hv; exact absurd hv hu
          | some _ => rw [hbv] at hv; exact hv.1
        · next ho =>
          rw [hv]
          have := TableTheorems.lookup_idRow t ht.nodup j v
          rw [lookupAt_old, if_neg ho] at this
          exact okV_mono hp (hrows j hj _ (OptJoin.idLookup_mem this))
    · rw [if_neg hw] at hl
      have := TableTheorems.lookup_idRow t ht.nodup j pr.1
      rw [hl] at this
      exact okV_mono hp (hrows j hj _ (OptJoin.idLookup_mem this))

/-- **BIND as the nested evaluator runs it** (`IdGroup.extendNM`): from a
    state with the invariant, for an EXISTS-free expression whose variables
    `residualVars` lists and that reads no freshness key, it refuses
    (`LocalRefusal`, among them a value that is not its own `normalizeTerm`,
    `IdQuery.valueIdM`) or returns a well-formed table whose rows decode, with
    the decoder of the new state, to `bindRowsFresh` of the reference binder
    on the decoded rows of `t`, row for row. The reference binder is the one
    of the environment `env`, which agrees with the id path's environment
    `cx.env` on `ext`, `now` and `base` (`henv`); the dataset may differ. -/
theorem extendNM_spec (cx : IdGroup.NCx Id) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x))
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (env : EvalEnv) (henv : ExprLocalTheorems.EnvAgree cx.env env) (e : Expr) (v : String) (vs : Array String)
    (hvs : residualVars e = some vs) (hef : e.existsFree = true) (hfx : ∀ w ∈ e.refVars, ¬ IsFx w)
    (t : Table) (ht : t.WF) (nst : IdGroup.NSt) (hi : Inv cid nst)
    (hrows : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r) (a : Graph) :
    Ends ((IdGroup.extendNM cx t e v).run nst) fun T nst' =>
      T.WF ∧ IdGroup.Pw IdGroup.BindEq
          (bindRowsFresh (IdGroup.binderFn env e) a v (t.idRows.map (decRow (decV dec nst'.vocab))) 0)
          (T.idRows.map (decRow (decV dec nst'.vocab))) ∧
        (∀ r ∈ T.idRows, RowIds (okV ok nst'.vocab) r) ∧ Inv cid nst' ∧ nst.vocab.toList <+: nst'.vocab.toList := by
  have hrows' : ∀ i, i < t.rows → RowIds (okV ok nst.vocab) (t.idRow i) :=
    fun i hi' => hrows _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩)
  -- the code binds with its own environment `cx.env`; on an EXISTS-free
  -- expression the binder reads only what `henv` says the two share
  have hb : IdGroup.binderFn env e = IdGroup.binderFn cx.env e := by
    funext a' row
    simp only [IdGroup.binderFn, IdPostTheorems.substituteExistentials_existsFree _ _ _ e hef,
      ExprLocalTheorems.evalIn_agree henv]
  rw [hb]
  unfold IdGroup.extendNM IdGroup.liftE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
  rcases extendM_spec cx.st cid dec ok hid hcid hcidok hcidN htermOf hloc hcid0 cx.env e v vs hvs hef hfx t ht.nodup
    nst.vocab nst.localIdx hi hrows' with ⟨e', he, hr⟩ | ⟨out, voc', ix', he, h1, h2, xs, hx1, hx2, hx3⟩
  · left
    refine ⟨e', ?_, hr⟩
    rw [he]; rfl
  · right
    rw [he]
    obtain ⟨hwf, _, _⟩ := ext_table t ht v out xs hx1 hx2
    obtain ⟨hpw, hok⟩ := ext_rows dec ok hloc cx.env e v vs hvs hef hfx t ht nst.vocab voc' h2 h1.size hrows' out xs
      hx1 hx2 hx3 a
    exact ⟨extTable t v (t.idx v) out, _, rfl, hwf, hpw, hok, h1, h2⟩

end

end

end L4Factoidal.Storage.Sbm11.LocalTable


#print axioms L4Factoidal.Storage.Sbm11.LocalTable.forIn_ends
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.resolveValues_spec
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.values_table
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.valuesNM_spec
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.extendM_spec
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.ext_rows
#print axioms L4Factoidal.Storage.Sbm11.LocalTable.extendNM_spec
