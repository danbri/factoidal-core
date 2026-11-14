/-
L4Factoidal.Rendering.Grid.Placement — placing grid items (CSS Grid Layout 2 §8.5, the
grid item placement algorithm).

Input: for each grid item, in order-modified document order, a definite start track or
"automatic" in each axis, and a span (`Item`); the number of columns the grid has before
auto-placement; and the packing mode (sparse or dense). Lines are already resolved to
track indices of the implicit grid, counted from 0 (`Grid.Lines` does that, and `shift`
below moves positions that are before the explicit grid to index 0).

Output: one grid area for each item.

The algorithm follows §8.5 for `grid-auto-flow: row`; for `column` the caller swaps the
axes of the items before and of the areas after (`Item.swap`, `Area.swap`).

Proved here (kinds and limits on each theorem):
* every item is placed exactly once (`placeAll_indices`);
* a definite position and every span are kept (`placeAll_honoured`);
* an item with an automatic position overlaps no item placed before it, and so no item
  with a definite position in both axes (`placeAll_disjoint`);
* with sparse packing the auto-placement cursor never moves backwards (`step_cursor_le`,
  `foldl_step_cursor_le`);
* every area lies inside the grid whose size the placement reports (`placeRows_inside`);
-/
import Std

namespace L4Factoidal.Rendering.Grid

/-- A grid area in tracks of the implicit grid, counted from 0: rows `row` up to
`row + rowSpan`, columns `col` up to `col + colSpan`. -/
structure Area where
  row : Nat
  rowSpan : Nat
  col : Nat
  colSpan : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Area

def rowEnd (a : Area) : Nat := a.row + a.rowSpan
def colEnd (a : Area) : Nat := a.col + a.colSpan

/-- The area with rows and columns exchanged (for `grid-auto-flow: column`). -/
def swap (a : Area) : Area := ⟨a.col, a.colSpan, a.row, a.rowSpan⟩

/-- Two areas share a cell. -/
def overlaps (a b : Area) : Bool :=
  decide (a.row < b.rowEnd) && decide (b.row < a.rowEnd) &&
  decide (a.col < b.colEnd) && decide (b.col < a.colEnd)

/-- Kind: algebraic law. Says: sharing a cell is symmetric. Does not say: anything about
areas with a span of 0, which share no cell with any area. -/
theorem overlaps_comm (a b : Area) : a.overlaps b = b.overlaps a := by
  unfold overlaps
  generalize decide (a.row < b.rowEnd) = p
  generalize decide (b.row < a.rowEnd) = q
  generalize decide (a.col < b.colEnd) = r
  generalize decide (b.col < a.colEnd) = s
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem swap_swap (a : Area) : a.swap.swap = a := rfl

end Area

/-- A grid item for placement: in each axis a definite start track (`some`) or an
automatic position (`none`), and a span of at least 1. -/
structure Item where
  row : Option Nat
  rowSpan : Nat := 1
  col : Option Nat
  colSpan : Nat := 1
  deriving Repr, BEq, Inhabited

/-- The item with its axes exchanged. -/
def Item.swap (it : Item) : Item := ⟨it.col, it.colSpan, it.row, it.rowSpan⟩

/-- A definite position in both axes (§8.5 step 1). -/
def Item.explicit (it : Item) : Bool := it.row.isSome && it.col.isSome

/-- A placed item: its index in the input, whether both its positions were definite, and
its area. -/
structure Placed where
  index : Nat
  explicit : Bool
  area : Area
  deriving Repr, BEq, Inhabited

/-- No placed item shares a cell with `a`. -/
def free (placed : List Placed) (a : Area) : Bool := placed.all fun p => !a.overlaps p.area

/-- The number of rows the placed items reach. -/
def rowsUsed (placed : List Placed) : Nat := placed.foldl (fun m p => max m p.area.rowEnd) 0
/-- The number of columns the placed items reach. -/
def colsUsed (placed : List Placed) : Nat := placed.foldl (fun m p => max m p.area.colEnd) 0

theorem foldl_max_ge {α : Type} (f : α → Nat) (l : List α) (m : Nat) :
    m ≤ l.foldl (fun m p => max m (f p)) m := by
  induction l generalizing m with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_mem {α : Type} (f : α → Nat) (l : List α) (m : Nat) (x : α) (h : x ∈ l) :
    f x ≤ l.foldl (fun m p => max m (f p)) m := by
  induction l generalizing m with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge f ys _)
    · exact ih _ h

theorem rowEnd_le_rowsUsed (placed : List Placed) (p : Placed) (h : p ∈ placed) :
    p.area.rowEnd ≤ rowsUsed placed := foldl_max_mem (fun p => p.area.rowEnd) placed 0 p h

theorem colEnd_le_colsUsed (placed : List Placed) (p : Placed) (h : p ∈ placed) :
    p.area.colEnd ≤ colsUsed placed := foldl_max_mem (fun p => p.area.colEnd) placed 0 p h

/-- Kind: safety of the fallback. Says: an area that starts at or after the last row any
placed item reaches shares no cell with them. Does not say: that it is the earliest
such area. -/
theorem free_of_row_ge (placed : List Placed) (a : Area) (h : rowsUsed placed ≤ a.row) :
    free placed a = true := by
  simp only [free, List.all_eq_true, Bool.not_eq_true']
  intro p hp
  have := rowEnd_le_rowsUsed placed p hp
  simp only [Area.overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left; left; left; omega

theorem free_of_col_ge (placed : List Placed) (a : Area) (h : colsUsed placed ≤ a.col) :
    free placed a = true := by
  simp only [free, List.all_eq_true, Bool.not_eq_true']
  intro p hp
  have := colEnd_le_colsUsed placed p hp
  simp only [Area.overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left; right; omega

/-- `a` when it is free; else `a` moved down to the first row after every placed item. -/
def freeByRow (placed : List Placed) (a : Area) : Area :=
  if free placed a then a else {a with row := max a.row (rowsUsed placed)}

/-- `a` when it is free; else `a` moved to the first column after every placed item. -/
def freeByCol (placed : List Placed) (a : Area) : Area :=
  if free placed a then a else {a with col := max a.col (colsUsed placed)}

theorem freeByRow_free (placed : List Placed) (a : Area) : free placed (freeByRow placed a) = true := by
  unfold freeByRow
  split
  · assumption
  · exact free_of_row_ge placed _ (Nat.le_max_right _ _)

theorem freeByCol_free (placed : List Placed) (a : Area) : free placed (freeByCol placed a) = true := by
  unfold freeByCol
  split
  · assumption
  · exact free_of_col_ge placed _ (Nat.le_max_right _ _)

theorem freeByRow_keeps (placed : List Placed) (a : Area) :
    (freeByRow placed a).col = a.col ∧ (freeByRow placed a).rowSpan = a.rowSpan ∧
    (freeByRow placed a).colSpan = a.colSpan ∧ a.row ≤ (freeByRow placed a).row := by
  unfold freeByRow
  split
  · exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  · exact ⟨rfl, rfl, rfl, Nat.le_max_left _ _⟩

theorem freeByCol_keeps (placed : List Placed) (a : Area) :
    (freeByCol placed a).row = a.row ∧ (freeByCol placed a).rowSpan = a.rowSpan ∧
    (freeByCol placed a).colSpan = a.colSpan ∧ a.col ≤ (freeByCol placed a).col := by
  unfold freeByCol
  split
  · exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  · exact ⟨rfl, rfl, rfl, Nat.le_max_left _ _⟩

/-- The first column at or after `col` where an item of the given rows and span is free
(§8.5 step 2). `fuel` bounds the search: a column at or after `colsUsed` is always free. -/
def firstFreeCol (placed : List Placed) (row rowSpan colSpan : Nat) : Nat → Nat → Nat
  | 0, col => col
  | fuel + 1, col =>
    if free placed ⟨row, rowSpan, col, colSpan⟩ then col
    else firstFreeCol placed row rowSpan colSpan fuel (col + 1)

/-- The first row at or after `row` where an item of the given columns and span is free
(§8.5 step 4, an item with a definite column). -/
def firstFreeRow (placed : List Placed) (rowSpan col colSpan : Nat) : Nat → Nat → Nat
  | 0, row => row
  | fuel + 1, row =>
    if free placed ⟨row, rowSpan, col, colSpan⟩ then row
    else firstFreeRow placed rowSpan col colSpan fuel (row + 1)

theorem firstFreeCol_ge (placed : List Placed) (row rowSpan colSpan fuel col : Nat) :
    col ≤ firstFreeCol placed row rowSpan colSpan fuel col := by
  induction fuel generalizing col with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    unfold firstFreeCol
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ _) (ih _)

theorem firstFreeRow_ge (placed : List Placed) (rowSpan col colSpan fuel row : Nat) :
    row ≤ firstFreeRow placed rowSpan col colSpan fuel row := by
  induction fuel generalizing row with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    unfold firstFreeRow
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ _) (ih _)

/-- The first column at or after `col` in `row` where the item is free and ends inside
the `ncols` columns; `none` when the row has no such column. -/
def fitInRow (placed : List Placed) (ncols row rowSpan colSpan : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, col =>
    if col + colSpan > ncols then none
    else if free placed ⟨row, rowSpan, col, colSpan⟩ then some col
    else fitInRow placed ncols row rowSpan colSpan fuel (col + 1)

theorem fitInRow_ge (placed : List Placed) (ncols row rowSpan colSpan fuel col c : Nat)
    (h : fitInRow placed ncols row rowSpan colSpan fuel col = some c) : col ≤ c := by
  induction fuel generalizing col with
  | zero => simp [fitInRow] at h
  | succ n ih =>
    unfold fitInRow at h
    split at h
    · cases h
    · split at h
      · cases h; exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ _) (ih _ h)

/-- Kind: conformance (§8.5: "the earliest" column). Says: every column from `col` up to
the one `firstFreeCol` answers is taken: the item would overlap a placed item there. -/
theorem firstFreeCol_earliest (placed : List Placed) (row rowSpan colSpan fuel col c : Nat)
    (h₁ : col ≤ c) (h₂ : c < firstFreeCol placed row rowSpan colSpan fuel col) :
    free placed ⟨row, rowSpan, c, colSpan⟩ = false := by
  induction fuel generalizing col with
  | zero => simp only [firstFreeCol] at h₂; omega
  | succ n ih =>
    unfold firstFreeCol at h₂
    split at h₂
    · omega
    · rename_i hf
      by_cases hc : c = col
      · subst hc; simpa using hf
      · exact ih (col + 1) (by omega) h₂

/-- Kind: conformance (§8.5: "the earliest" row). Says: every row from `row` up to the one
`firstFreeRow` answers is taken. -/
theorem firstFreeRow_earliest (placed : List Placed) (rowSpan col colSpan fuel row r : Nat)
    (h₁ : row ≤ r) (h₂ : r < firstFreeRow placed rowSpan col colSpan fuel row) :
    free placed ⟨r, rowSpan, col, colSpan⟩ = false := by
  induction fuel generalizing row with
  | zero => simp only [firstFreeRow] at h₂; omega
  | succ n ih =>
    unfold firstFreeRow at h₂
    split at h₂
    · omega
    · rename_i hf
      by_cases hr : r = row
      · subst hr; simpa using hf
      · exact ih (row + 1) (by omega) h₂

/-- Kind: conformance (§8.5 step 4: the first column in the row where the item fits).
Says: when `fitInRow` finds column `c`, every column from `col` before it is taken. -/
theorem fitInRow_earliest (placed : List Placed) (ncols row rowSpan colSpan fuel col c c' : Nat)
    (h : fitInRow placed ncols row rowSpan colSpan fuel col = some c) (h₁ : col ≤ c') (h₂ : c' < c) :
    free placed ⟨row, rowSpan, c', colSpan⟩ = false := by
  induction fuel generalizing col with
  | zero => simp [fitInRow] at h
  | succ n ih =>
    unfold fitInRow at h
    split at h
    · cases h
    · split at h
      · cases h; omega
      · rename_i _ hf
        by_cases hc : c' = col
        · subst hc; simpa using hf
        · exact ih (col + 1) h (by omega)

/-- The slot of an item with an automatic position in both axes (§8.5 step 4): from the
cursor `(row, col)`, the first column of the row where it fits, else the next rows from
their first column. When `fuel` rows have been tried, the row after every placed item. -/
def findSlot (placed : List Placed) (ncols rowSpan colSpan : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, row, _ => (max row (rowsUsed placed) + 1, 0)
  | fuel + 1, row, col =>
    match fitInRow placed ncols row rowSpan colSpan (ncols + 1) col with
    | some c => (row, c)
    | none => findSlot placed ncols rowSpan colSpan fuel (row + 1) 0

/-- `(r₁, c₁)` is at or before `(r₂, c₂)` in row-major order. -/
def cursorLE (r₁ c₁ r₂ c₂ : Nat) : Prop := r₁ < r₂ ∨ (r₁ = r₂ ∧ c₁ ≤ c₂)

theorem findSlot_ge (placed : List Placed) (ncols rowSpan colSpan fuel row col : Nat) :
    cursorLE row col (findSlot placed ncols rowSpan colSpan fuel row col).1
      (findSlot placed ncols rowSpan colSpan fuel row col).2 := by
  induction fuel generalizing row col with
  | zero =>
    left
    simp only [findSlot]
    omega
  | succ n ih =>
    unfold findSlot
    split
    · rename_i c hc
      right; exact ⟨rfl, fitInRow_ge _ _ _ _ _ _ _ _ hc⟩
    · left
      rcases ih (row + 1) 0 with h | h
      · omega
      · omega

/-- The state of the placement: the items placed so far (newest first), the number of
columns of the implicit grid, the auto-placement cursor, and for each row that §8.5
step 2 placed an item in, the column after that item (newest first). -/
structure State where
  placed : List Placed := []
  ncols : Nat := 0
  cursorRow : Nat := 0
  cursorCol : Nat := 0
  rowCursors : List (Nat × Nat) := []
  deriving Repr

def State.add (st : State) (p : Placed) : State :=
  {st with placed := p :: st.placed, ncols := max st.ncols p.area.colEnd}

/-- The area of an item locked to row `r` (§8.5 step 2): the first free column, from the
column after the last item this step placed in that row (sparse) or from the first
column (dense). -/
def rowLockedArea (dense : Bool) (st : State) (it : Item) (r : Nat) : Area :=
  freeByCol st.placed ⟨r, it.rowSpan,
    firstFreeCol st.placed r it.rowSpan it.colSpan (colsUsed st.placed + 1)
      (if dense then 0 else (st.rowCursors.lookup r).getD 0), it.colSpan⟩

/-- The area of an item with a definite column `c` and an automatic row (§8.5 step 4):
the first free row, from the cursor's row (the next row when the column is before the
cursor's) or, dense, from the first row. -/
def colLockedArea (dense : Bool) (st : State) (it : Item) (c : Nat) : Area :=
  freeByRow st.placed ⟨firstFreeRow st.placed it.rowSpan c it.colSpan (rowsUsed st.placed + 1)
      (if dense then 0 else if c < st.cursorCol then st.cursorRow + 1 else st.cursorRow),
    it.rowSpan, c, it.colSpan⟩

/-- The slot search of an item automatic in both axes: from the cursor (sparse) or from
the first cell (dense). -/
def autoSlot (dense : Bool) (st : State) (it : Item) : Nat × Nat :=
  findSlot st.placed st.ncols it.rowSpan it.colSpan (rowsUsed st.placed + 2)
    (if dense then 0 else st.cursorRow) (if dense then 0 else st.cursorCol)

/-- The area of an item with an automatic position in both axes (§8.5 step 4). -/
def autoArea (dense : Bool) (st : State) (it : Item) : Area :=
  freeByRow st.placed ⟨(autoSlot dense st it).1, it.rowSpan, (autoSlot dense st it).2, it.colSpan⟩

/-- Sparse packing moves the cursor to the item just placed; dense packing has no cursor. -/
def State.moveCursor (dense : Bool) (st : State) (a : Area) : State :=
  if dense then st else {st with cursorRow := a.row, cursorCol := a.col}

theorem State.moveCursor_placed (dense : Bool) (st : State) (a : Area) :
    (st.moveCursor dense a).placed = st.placed := by
  unfold State.moveCursor; split <;> rfl

/-- One item placed (§8.5 steps 1, 2 and 4, by the kind of the item). -/
def step (dense : Bool) (st : State) (x : Item × Nat) : State :=
  match x.1.row, x.1.col with
  | some r, some c => st.add ⟨x.2, true, ⟨r, x.1.rowSpan, c, x.1.colSpan⟩⟩
  | some r, none =>
    {st.add ⟨x.2, false, rowLockedArea dense st x.1 r⟩ with
      rowCursors := (r, (rowLockedArea dense st x.1 r).colEnd) :: st.rowCursors}
  | none, some c =>
    (st.add ⟨x.2, false, colLockedArea dense st x.1 c⟩).moveCursor dense (colLockedArea dense st x.1 c)
  | none, none =>
    (st.add ⟨x.2, false, autoArea dense st x.1⟩).moveCursor dense (autoArea dense st x.1)

theorem rowLockedArea_spec (dense : Bool) (st : State) (it : Item) (r : Nat) :
    (rowLockedArea dense st it r).row = r ∧ (rowLockedArea dense st it r).rowSpan = it.rowSpan ∧
    (rowLockedArea dense st it r).colSpan = it.colSpan ∧
    free st.placed (rowLockedArea dense st it r) = true := by
  unfold rowLockedArea
  exact ⟨(freeByCol_keeps _ _).1, (freeByCol_keeps _ _).2.1, (freeByCol_keeps _ _).2.2.1, freeByCol_free _ _⟩

theorem colLockedArea_spec (dense : Bool) (st : State) (it : Item) (c : Nat) :
    (colLockedArea dense st it c).col = c ∧ (colLockedArea dense st it c).rowSpan = it.rowSpan ∧
    (colLockedArea dense st it c).colSpan = it.colSpan ∧
    free st.placed (colLockedArea dense st it c) = true := by
  unfold colLockedArea
  exact ⟨(freeByRow_keeps _ _).1, (freeByRow_keeps _ _).2.1, (freeByRow_keeps _ _).2.2.1, freeByRow_free _ _⟩

theorem autoArea_spec (dense : Bool) (st : State) (it : Item) :
    (autoArea dense st it).rowSpan = it.rowSpan ∧ (autoArea dense st it).colSpan = it.colSpan ∧
    free st.placed (autoArea dense st it) = true := by
  unfold autoArea
  exact ⟨(freeByRow_keeps _ _).2.1, (freeByRow_keeps _ _).2.2.1, freeByRow_free _ _⟩

theorem colLockedArea_cursor (st : State) (it : Item) (c : Nat) :
    cursorLE st.cursorRow st.cursorCol (colLockedArea false st it c).row (colLockedArea false st it c).col := by
  unfold colLockedArea
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize hrow0 : (if c < st.cursorCol then st.cursorRow + 1 else st.cursorRow) = row0
  have hf := firstFreeRow_ge st.placed it.rowSpan c it.colSpan (rowsUsed st.placed + 1) row0
  generalize firstFreeRow st.placed it.rowSpan c it.colSpan (rowsUsed st.placed + 1) row0 = r at hf ⊢
  have hk := freeByRow_keeps st.placed ⟨r, it.rowSpan, c, it.colSpan⟩
  generalize freeByRow st.placed ⟨r, it.rowSpan, c, it.colSpan⟩ = a at hk ⊢
  dsimp only at hk
  unfold cursorLE
  split at hrow0 <;> omega

theorem autoArea_cursor (st : State) (it : Item) :
    cursorLE st.cursorRow st.cursorCol (autoArea false st it).row (autoArea false st it).col := by
  unfold autoArea autoSlot
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hs := findSlot_ge st.placed st.ncols it.rowSpan it.colSpan (rowsUsed st.placed + 2)
    st.cursorRow st.cursorCol
  generalize findSlot st.placed st.ncols it.rowSpan it.colSpan (rowsUsed st.placed + 2)
    st.cursorRow st.cursorCol = slot at hs ⊢
  have hk := freeByRow_keeps st.placed ⟨slot.1, it.rowSpan, slot.2, it.colSpan⟩
  generalize freeByRow st.placed ⟨slot.1, it.rowSpan, slot.2, it.colSpan⟩ = a at hk ⊢
  dsimp only at hk
  unfold cursorLE at hs ⊢
  omega

/-- The area of `p` is what item `it` asks for: its spans, and its start track in each
axis where that is definite. -/
def Honoured (it : Item) (p : Placed) : Prop :=
  p.area.rowSpan = it.rowSpan ∧ p.area.colSpan = it.colSpan ∧
  (∀ r, it.row = some r → p.area.row = r) ∧ (∀ c, it.col = some c → p.area.col = c) ∧
  p.explicit = it.explicit

/-- One step adds exactly one placed item, with the index of the item, an area the item
asks for, and (unless both positions are definite) free of every item placed before. -/
theorem step_spec (dense : Bool) (st : State) (x : Item × Nat) :
    ∃ p, (step dense st x).placed = p :: st.placed ∧ p.index = x.2 ∧ Honoured x.1 p ∧
      (p.explicit = false → free st.placed p.area = true) := by
  unfold step
  split
  · rename_i r c hr hc
    refine ⟨⟨x.2, true, ⟨r, x.1.rowSpan, c, x.1.colSpan⟩⟩, rfl, rfl, ⟨rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
    · intro r' h; rw [hr] at h; cases h; rfl
    · intro c' h; rw [hc] at h; cases h; rfl
    · simp [Item.explicit, hr, hc]
    · intro h; cases h
  · rename_i r hr hc
    have hs := rowLockedArea_spec dense st x.1 r
    refine ⟨⟨x.2, false, rowLockedArea dense st x.1 r⟩, rfl, rfl, ⟨hs.2.1, hs.2.2.1, ?_, ?_, ?_⟩, ?_⟩
    · intro r' h; rw [hr] at h; cases h; exact hs.1
    · intro c' h; rw [hc] at h; cases h
    · simp [Item.explicit, hr, hc]
    · intro _; exact hs.2.2.2
  · rename_i c hr hc
    have hs := colLockedArea_spec dense st x.1 c
    refine ⟨⟨x.2, false, colLockedArea dense st x.1 c⟩, ?_, rfl, ⟨hs.2.1, hs.2.2.1, ?_, ?_, ?_⟩, ?_⟩
    · rw [State.moveCursor_placed]; rfl
    · intro r' h; rw [hr] at h; cases h
    · intro c' h; rw [hc] at h; cases h; exact hs.1
    · simp [Item.explicit, hr, hc]
    · intro _; exact hs.2.2.2
  · rename_i hr hc
    have hs := autoArea_spec dense st x.1
    refine ⟨⟨x.2, false, autoArea dense st x.1⟩, ?_, rfl, ⟨hs.1, hs.2.1, ?_, ?_, ?_⟩, ?_⟩
    · rw [State.moveCursor_placed]; rfl
    · intro r' h; rw [hr] at h; cases h
    · intro c' h; rw [hc] at h; cases h
    · simp [Item.explicit, hr, hc]
    · intro _; exact hs.2.2

/-- Kind: invariant of sparse packing (§8.5 "auto-placement cursor"). Says: with sparse
packing one step leaves the cursor where it was or moves it forward in row-major order.
Does not say: anything for dense packing, which starts each search from the first row. -/
theorem step_cursor_le (st : State) (x : Item × Nat) :
    cursorLE st.cursorRow st.cursorCol (step false st x).cursorRow (step false st x).cursorCol := by
  unfold step
  split
  · right; exact ⟨rfl, Nat.le_refl _⟩
  · right; exact ⟨rfl, Nat.le_refl _⟩
  · rename_i c _ _
    exact colLockedArea_cursor st x.1 c
  · exact autoArea_cursor st x.1

theorem cursorLE_trans {r₁ c₁ r₂ c₂ r₃ c₃ : Nat} (h₁ : cursorLE r₁ c₁ r₂ c₂) (h₂ : cursorLE r₂ c₂ r₃ c₃) :
    cursorLE r₁ c₁ r₃ c₃ := by
  unfold cursorLE at *; omega

/-- Kind: invariant of sparse packing over a whole placement. Says: after any number of
steps of sparse packing the cursor is at or after where it started. -/
theorem foldl_step_cursor_le (order : List (Item × Nat)) (st : State) :
    cursorLE st.cursorRow st.cursorCol (order.foldl (step false) st).cursorRow
      (order.foldl (step false) st).cursorCol := by
  induction order generalizing st with
  | nil => right; exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih => exact cursorLE_trans (step_cursor_le st x) (ih _)

/-- The order in which §8.5 places the items: those with both positions definite (step
1), those locked to a row (step 2), then the others (step 4); each group in the order
given. Each item carries its index in the input. -/
def placementOrder (items : List Item) : List (Item × Nat) :=
  let all := items.zipIdx
  let rest := all.filter fun x => !x.1.explicit
  all.filter (fun x => x.1.explicit) ++
    (rest.filter (fun x => x.1.row.isSome) ++ rest.filter (fun x => !x.1.row.isSome))

/-- Kind: structural. Says: the placement order holds every item of the input exactly
once (it is a permutation of the items with their indices). -/
theorem placementOrder_perm (items : List Item) : (placementOrder items).Perm items.zipIdx := by
  unfold placementOrder
  have h1 := List.filter_append_perm (fun x : Item × Nat => x.1.explicit) items.zipIdx
  have h2 := List.filter_append_perm (fun x : Item × Nat => x.1.row.isSome)
    (items.zipIdx.filter fun x => !x.1.explicit)
  exact (List.Perm.append_left _ h2).trans h1

/-- The columns the grid has before auto-placement (§8.5 step 3): the explicit columns,
the end of every item with a definite column, and the widest span of the others. -/
def initialCols (explicitCols : Nat) (items : List Item) : Nat :=
  items.foldl (fun m it => max m (match it.col with | some c => c + it.colSpan | none => it.colSpan)) explicitCols

/-- All the items placed: the state after every step, in placement order. -/
def placeAll (dense : Bool) (explicitCols : Nat) (items : List Item) : State :=
  (placementOrder items).foldl (step dense) {ncols := initialCols explicitCols items}

theorem foldl_step_indices (dense : Bool) (order : List (Item × Nat)) (st : State) :
    ((order.foldl (step dense) st).placed.map (·.index)) =
      (order.map (·.2)).reverse ++ st.placed.map (·.index) := by
  induction order generalizing st with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨p, hp, hi, _⟩ := step_spec dense st x
    simp only [List.foldl_cons, List.map_cons, List.reverse_cons, List.append_assoc]
    rw [ih, hp]
    simp [hi]

/-- Kind: totality of placement. Says: the indices of the placed items are a permutation
of the indices of the input: every grid item is placed exactly once. Does not say:
where. -/
theorem placeAll_indices (dense : Bool) (explicitCols : Nat) (items : List Item) :
    ((placeAll dense explicitCols items).placed.map (·.index)).Perm (items.zipIdx.map (·.2)) := by
  unfold placeAll
  rw [foldl_step_indices]
  simp only [List.map_nil, List.append_nil]
  exact (List.reverse_perm _).trans ((placementOrder_perm items).map _)

theorem foldl_step_honoured (dense : Bool) (all order : List (Item × Nat)) (st : State)
    (h : ∀ p ∈ st.placed, ∃ x ∈ all, p.index = x.2 ∧ Honoured x.1 p)
    (hsub : ∀ x ∈ order, x ∈ all) :
    ∀ p ∈ (order.foldl (step dense) st).placed, ∃ x ∈ all, p.index = x.2 ∧ Honoured x.1 p := by
  induction order generalizing st with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · obtain ⟨p, hp, hi, hh, _⟩ := step_spec dense st x
      rw [hp]
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst hq; exact ⟨x, hsub x (List.mem_cons_self), hi, hh⟩
      · exact h q hq
    · intro y hy; exact hsub y (List.mem_cons_of_mem _ hy)

/-- Kind: conformance of placement (§8.5 step 1, and the definite axis of steps 2 and 4).
Says: every placed item is an item of the input, with the spans it asks for, and at the
start track it asks for in each axis where that is definite. Does not say: that lines were
resolved to those tracks correctly (`Grid.Lines`). -/
theorem placeAll_honoured (dense : Bool) (explicitCols : Nat) (items : List Item) :
    ∀ p ∈ (placeAll dense explicitCols items).placed,
      ∃ x ∈ items.zipIdx, p.index = x.2 ∧ Honoured x.1 p := by
  unfold placeAll
  apply foldl_step_honoured
  · intro p hp; cases hp
  · intro x hx; exact (placementOrder_perm items).mem_iff.mp hx

/-- A placed item as an item with that area as its definite position. -/
def Placed.asItem (p : Placed) : Item := ⟨some p.area.row, p.area.rowSpan, some p.area.col, p.area.colSpan⟩

theorem fst_mem_of_mem_zipIdx {α : Type} (l : List α) (n : Nat) (x : α × Nat) (h : x ∈ l.zipIdx n) :
    x.1 ∈ l := by
  induction l generalizing n with
  | nil => simp [List.zipIdx] at h
  | cons a as ih =>
    simp only [List.zipIdx, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (n + 1) h)

/-- Kind: idempotence. Says: placing again, as definite positions, the areas a placement
gave puts every item back in the same area: each placed item of the second placement is
the item it was made from. -/
theorem placeAll_idem (dense : Bool) (explicitCols : Nat) (ps : List Placed) :
    ∀ p ∈ (placeAll dense explicitCols (ps.map Placed.asItem)).placed,
      ∃ x ∈ (ps.map Placed.asItem).zipIdx, p.index = x.2 ∧ p.asItem = x.1 := by
  intro p hp
  obtain ⟨x, hx, hi, hrs, hcs, hr, hc, _⟩ := placeAll_honoured dense explicitCols _ p hp
  refine ⟨x, hx, hi, ?_⟩
  obtain ⟨q, _, hq⟩ := List.mem_map.mp (fst_mem_of_mem_zipIdx _ 0 x hx)
  rw [← hq] at hrs hcs hr hc ⊢
  have e1 := hr q.area.row rfl
  have e2 := hc q.area.col rfl
  simp only [Placed.asItem] at hrs hcs ⊢
  rw [hrs, hcs, e1, e2]

/-- Newer placed items (first in the list) against older ones: when either of two items
had an automatic position, their areas share no cell. -/
def Disjoint (placed : List Placed) : Prop :=
  placed.Pairwise fun newer older =>
    (newer.explicit = false ∨ older.explicit = false) → newer.area.overlaps older.area = false

theorem free_iff (placed : List Placed) (a : Area) :
    free placed a = true ↔ ∀ p ∈ placed, a.overlaps p.area = false := by
  simp [free]

theorem foldl_step_explicit (dense : Bool) (order : List (Item × Nat)) (st : State)
    (h : ∀ p ∈ st.placed, p.explicit = true) (ho : ∀ x ∈ order, x.1.explicit = true) :
    ∀ p ∈ (order.foldl (step dense) st).placed, p.explicit = true := by
  induction order generalizing st with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · obtain ⟨p, hp, _, hh, _⟩ := step_spec dense st x
      rw [hp]
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst hq; rw [hh.2.2.2.2]; exact ho x (List.mem_cons_self)
      · exact h q hq
    · intro y hy; exact ho y (List.mem_cons_of_mem _ hy)

theorem foldl_step_disjoint (dense : Bool) (order : List (Item × Nat)) (st : State)
    (h : Disjoint st.placed) (ho : ∀ x ∈ order, x.1.explicit = false) :
    Disjoint (order.foldl (step dense) st).placed := by
  induction order generalizing st with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · obtain ⟨p, hp, _, hh, hf⟩ := step_spec dense st x
      rw [hp]
      unfold Disjoint
      rw [List.pairwise_cons]
      refine ⟨?_, h⟩
      intro q hq _
      have he : p.explicit = false := by rw [hh.2.2.2.2]; exact ho x (List.mem_cons_self)
      exact (free_iff st.placed p.area).mp (hf he) q hq
    · intro y hy; exact ho y (List.mem_cons_of_mem _ hy)

/-- Kind: safety of auto-placement (§8.5 steps 2 and 4: "will not overlap any occupied
grid cells"). Says: of any two placed items of which at least one had an automatic
position, the areas share no cell. So auto-placement never puts an item over an item with
a definite position, and never puts two auto-placed items over each other. Does not say:
that two items that both have definite positions in both axes do not overlap (the author
may ask for that), or that each slot is the earliest free one. -/
theorem placeAll_disjoint (dense : Bool) (explicitCols : Nat) (items : List Item) :
    Disjoint (placeAll dense explicitCols items).placed := by
  unfold placeAll placementOrder
  rw [List.foldl_append]
  apply foldl_step_disjoint
  · -- after step 1 every placed item is explicit, so the relation holds vacuously
    have hall := foldl_step_explicit dense
      (items.zipIdx.filter fun x => x.1.explicit) {ncols := initialCols explicitCols items}
      (by intro p hp; cases hp)
      (by intro x hx; exact (List.mem_filter.mp hx).2)
    unfold Disjoint
    apply List.Pairwise.imp_of_mem (R := fun _ _ => True)
    · intro a b ha hb _ hab
      rcases hab with hab | hab
      · rw [hall a ha] at hab; cases hab
      · rw [hall b hb] at hab; cases hab
    · exact List.pairwise_of_forall (fun _ _ => trivial)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := (List.mem_filter.mp (List.mem_filter.mp hx).1).2
      simpa using this
    · have := (List.mem_filter.mp (List.mem_filter.mp hx).1).2
      simpa using this

/-- The result of placement: the area of each item (by input index), and the size of the
implicit grid in tracks. -/
structure Placement where
  areas : Array Area
  rows : Nat
  cols : Nat
  deriving Repr

/-- The areas by input index. An index with no placed item (there is none, by
`placeAll_indices`) gets the first cell. -/
def areasOf (n : Nat) (placed : List Placed) : Array Area :=
  placed.foldl (fun acc p => acc.setIfInBounds p.index p.area) (Array.replicate n ⟨0, 1, 0, 1⟩)

/-- §8.5 for row flow: the area of each item, and the rows and columns of the implicit
grid (at least the explicit ones). -/
def placeRows (dense : Bool) (explicitRows explicitCols : Nat) (items : List Item) : Placement :=
  let st := placeAll dense explicitCols items
  { areas := areasOf items.length st.placed,
    rows := max explicitRows (rowsUsed st.placed),
    cols := max (max explicitCols st.ncols) (colsUsed st.placed) }

/-- §8.5 for either flow: column flow is row flow with the axes exchanged. -/
def place (columnFlow dense : Bool) (explicitRows explicitCols : Nat) (items : List Item) : Placement :=
  if columnFlow then
    let p := placeRows dense explicitCols explicitRows (items.map Item.swap)
    { areas := p.areas.map Area.swap, rows := p.cols, cols := p.rows }
  else placeRows dense explicitRows explicitCols items

/-- Kind: bound. Says: every placed item ends at or before the last row and the last
column that `placeRows` reports, so every area lies inside the implicit grid. -/
theorem placeRows_inside (dense : Bool) (explicitRows explicitCols : Nat) (items : List Item) :
    ∀ p ∈ (placeAll dense explicitCols items).placed,
      p.area.rowEnd ≤ (placeRows dense explicitRows explicitCols items).rows ∧
      p.area.colEnd ≤ (placeRows dense explicitRows explicitCols items).cols := by
  intro p hp
  constructor
  · exact Nat.le_trans (rowEnd_le_rowsUsed _ p hp) (Nat.le_max_right _ _)
  · exact Nat.le_trans (colEnd_le_colsUsed _ p hp) (Nat.le_max_right _ _)

theorem areasOf_size (n : Nat) (placed : List Placed) : (areasOf n placed).size = n := by
  unfold areasOf
  have : ∀ (acc : Array Area), (placed.foldl (fun acc p => acc.setIfInBounds p.index p.area) acc).size = acc.size := by
    induction placed with
    | nil => intro acc; rfl
    | cons p ps ih => intro acc; simp only [List.foldl_cons]; rw [ih]; simp
  rw [this]; simp

/-- Kind: totality. Says: placement answers one area for each item of the input. -/
theorem place_size (columnFlow dense : Bool) (explicitRows explicitCols : Nat) (items : List Item) :
    (place columnFlow dense explicitRows explicitCols items).areas.size = items.length := by
  unfold place
  split
  · simp [placeRows, areasOf_size]
  · simp [placeRows, areasOf_size]

/-! ### Positions before the explicit grid

A line before the first line of the explicit grid (a negative index past the start, or a
span back from a line near the start) gives a start "track" below 0. The implicit grid
grows at its start to hold it: every definite position moves by the same amount. -/

/-- A position in one axis as the author gave it, resolved against the explicit grid:
automatic, or a start track that may be before the explicit grid. -/
structure RawItem where
  row : Option Int
  rowSpan : Nat := 1
  col : Option Int
  colSpan : Nat := 1
  deriving Repr, Inhabited

/-- The lines a placement may name, counted from the first explicit line: from
`-maxLine` to `maxLine` (CSS Grid 2 §8.1 lets a user agent clamp the implicit grid; this
is the limit Gecko uses). A page that names a line further out, or a longer span, gets
the clamped one, so the grid it asks for stays within a bound it can not raise. -/
def maxLine : Int := 10000

/-- A start line, clamped so that at least one track follows it before `maxLine`. -/
def clampStart (v : Int) : Int := max (-maxLine) (min (maxLine - 1) v)

/-- A span, clamped so that it ends at or before `maxLine`. -/
def clampSpan (start : Option Int) (n : Nat) : Nat :=
  match start with
  | some s => max 1 (min n (maxLine - clampStart s).toNat)
  | none => max 1 (min n maxLine.toNat)

/-- The item with its lines and spans clamped. -/
def RawItem.clamp (r : RawItem) : RawItem :=
  {row := r.row.map clampStart, rowSpan := clampSpan r.row r.rowSpan,
   col := r.col.map clampStart, colSpan := clampSpan r.col r.colSpan}

/-- Kind: resource bound (local-lean-rules §11). Says: a clamped start is a line within
`[-maxLine, maxLine)` and a clamped span starting there ends at or before `maxLine`. -/
theorem clamp_bounds (v : Int) (n : Nat) :
    -maxLine ≤ clampStart v ∧ clampStart v < maxLine ∧
    clampStart v + (clampSpan (some v) n : Int) ≤ maxLine ∧ 1 ≤ clampSpan (some v) n := by
  simp only [clampStart, clampSpan, maxLine]
  omega

/-- Kind: resource bound. Says: an automatic span is at most `maxLine` tracks. -/
theorem clampSpan_none (n : Nat) : clampSpan none n ≤ 10000 := by
  simp only [clampSpan, maxLine]; omega

#guard (RawItem.clamp {row := some 1000000000, rowSpan := 5, col := some (-99999999), colSpan := 1000000}).row == some 9999
#guard (RawItem.clamp {row := some 1000000000, rowSpan := 5, col := some (-99999999), colSpan := 1000000}).rowSpan == 1
#guard (RawItem.clamp {row := some 1000000000, rowSpan := 5, col := some (-99999999), colSpan := 1000000}).colSpan == 20000
#guard (RawItem.clamp {row := some 2, rowSpan := 3, col := none, colSpan := 2}).rowSpan == 3

/-- How many tracks the implicit grid needs before the explicit grid in an axis. -/
def leading (starts : List (Option Int)) : Nat :=
  starts.foldl (fun m s => match s with | some v => max m (-v).toNat | none => m) 0

/-- The items in tracks of the implicit grid, and the implicit tracks added before the
explicit rows and columns. -/
def shift (raw : List RawItem) : List Item × Nat × Nat :=
  let rowLead := leading (raw.map (·.row))
  let colLead := leading (raw.map (·.col))
  (raw.map fun r =>
    { row := r.row.map fun v => (v + Int.ofNat rowLead).toNat, rowSpan := max 1 r.rowSpan,
      col := r.col.map fun v => (v + Int.ofNat colLead).toNat, colSpan := max 1 r.colSpan },
   rowLead, colLead)

theorem shift_length (raw : List RawItem) : (shift raw).1.length = raw.length := by
  simp [shift]

/-! ### Examples (WPT css/css-grid/placement/grid-auto-flow-sparse-001.html, a 4 by 4 grid) -/

private def demo (dense : Bool) (items : List Item) : List (Nat × Nat × Nat × Nat) :=
  (placeRows dense 4 4 items).areas.toList.map fun a => (a.row, a.col, a.rowSpan, a.colSpan)

-- firstRowSecondColumn, auto span 2, auto, auto span 2, auto span 2, auto
#guard demo false [⟨some 0, 1, some 1, 1⟩, ⟨none, 1, none, 2⟩, ⟨none, 1, none, 1⟩, ⟨none, 1, none, 2⟩,
    ⟨none, 1, none, 2⟩, ⟨none, 1, none, 1⟩] ==
  [(0, 1, 1, 1), (0, 2, 1, 2), (1, 0, 1, 1), (1, 1, 1, 2), (2, 0, 1, 2), (2, 2, 1, 1)]
-- autoRowSecondColumn, auto span 2, autoRowFirstColumn, autoRowThirdColumn, auto, auto,
-- auto row span 2 column span 3, auto
#guard demo false [⟨none, 1, some 1, 1⟩, ⟨none, 1, none, 2⟩, ⟨none, 1, some 0, 1⟩, ⟨none, 1, some 2, 1⟩,
    ⟨none, 1, none, 1⟩, ⟨none, 1, none, 1⟩, ⟨none, 2, none, 3⟩, ⟨none, 1, none, 1⟩] ==
  [(0, 1, 1, 1), (0, 2, 1, 2), (1, 0, 1, 1), (1, 2, 1, 1), (1, 3, 1, 1), (2, 0, 1, 1), (2, 1, 2, 3), (3, 0, 1, 1)]
-- firstRowAutoColumn, secondRowAutoColumn, autoRowSecondColumn, autoRowFirstColumn, auto
#guard demo false [⟨some 0, 1, none, 1⟩, ⟨some 1, 1, none, 1⟩, ⟨none, 1, some 1, 1⟩, ⟨none, 1, some 0, 1⟩,
    ⟨none, 1, none, 1⟩] ==
  [(0, 0, 1, 1), (1, 0, 1, 1), (0, 1, 1, 1), (2, 0, 1, 1), (2, 1, 1, 1)]
-- dense packing fills the hole a wide item left
#guard demo true [⟨none, 1, none, 3⟩, ⟨none, 1, none, 2⟩, ⟨none, 1, none, 1⟩] ==
  [(0, 0, 1, 3), (1, 0, 1, 2), (0, 3, 1, 1)]
#guard demo false [⟨none, 1, none, 3⟩, ⟨none, 1, none, 2⟩, ⟨none, 1, none, 1⟩] ==
  [(0, 0, 1, 3), (1, 0, 1, 2), (1, 2, 1, 1)]
-- an item wider than the explicit grid adds implicit columns
#guard (placeRows false 1 2 [⟨none, 1, none, 3⟩, ⟨none, 1, none, 1⟩]).cols == 3
-- a position before the explicit grid moves every definite position
#guard (shift [⟨some (-2), 1, some 0, 1⟩, ⟨some 0, 1, none, 1⟩]).1.map (·.row) == [some 0, some 2]

end L4Factoidal.Rendering.Grid
