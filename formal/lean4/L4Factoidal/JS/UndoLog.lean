import Std.Data.HashSet

/-! # An undo log for one array of the heap

A page whose scripts may make a sync `XMLHttpRequest` runs each action so that it can be undone:
when a script asks for a sync request, the engine goes back to the session from before the action
and does the action again with the host's answer (`WebScripts.actLean`). Keeping the whole session
for that made the action's first write copy the heap's object and environment arrays, and its end
free the old ones: work in proportion to the heap at every turn (a news page with a timer every
70 ms paid about 33 ms a turn, and never went idle).

An undo log keeps instead the old value of each cell that the action writes, the first time it
writes it, and the size of the array before the action. Undoing puts those values back and drops
what the action added. An action pays for the cells it changes, not for the heap.

`UndoLog.restore_of_inv` with the steps `inv_start`, `inv_note`, `inv_set`, `inv_push`: whatever
sequence of noted writes and pushes an action makes, `restore` gives back the array from before
it, every cell, touched or not. -/

namespace L4Factoidal.JS

/-- The old values of the cells of one array that an action wrote. `base`: the size of the array
when the action began (0: no log is kept, and `note` does nothing). `cells`: each written cell's
index and its value before the action, in the order of the first writes. `seen`: the indices in
`cells`, so a cell is logged once however often it is written. -/
structure UndoLog (α : Type) where
  base : Nat := 0
  cells : Array (Nat × α) := #[]
  seen : Std.HashSet Nat := {}

instance {α : Type} : Inhabited (UndoLog α) := ⟨{}⟩

namespace UndoLog

variable {α : Type}

/-- A log for an array of `n` cells. -/
def start (n : Nat) : UndoLog α := { base := n }

/-- Put back one logged value. -/
@[inline] def step (p : Nat × α) (a : Array α) : Array α := a.setIfInBounds p.1 p.2

/-- Log cell `i` of `a`, unless it is logged already or is not a cell of `a`. The array is
passed through so that the caller's write comes after this read. -/
@[noinline] def noteAt (L : UndoLog α) (a : Array α) (i : Nat) : UndoLog α × Array α :=
  if L.seen.contains i then (L, a)
  else if h : i < a.size then ({ L with cells := L.cells.push (i, a[i]), seen := L.seen.insert i }, a)
  else (L, a)

/-- Before a write of cell `i` of `a`: log it when it was there when the action began. One
comparison when no log is kept (`base` 0) or the cell is new. -/
@[inline] def note (L : UndoLog α) (a : Array α) (i : Nat) : UndoLog α × Array α :=
  if i < L.base then L.noteAt a i else (L, a)

/-- The array from before the action: the logged values put back (the first write's, which is
the oldest), and the cells the action added dropped. In place when `a` is not shared; costs the
logged cells and the added ones. -/
def restore (L : UndoLog α) (a : Array α) : Array α :=
  (L.cells.foldr step a).shrink L.base

/-! ## Correctness -/

/-- What holds of a log `L` of an array that was `old` and is now `a`: every logged index is a
cell of `old`; every index in `seen` is logged; `restore` gives `old`; `a` is no shorter. -/
structure Inv (old : Array α) (L : UndoLog α) (a : Array α) : Prop where
  base : L.base = old.size
  size : old.size ≤ a.size
  below : ∀ p ∈ L.cells.toList, p.1 < L.base
  seen : ∀ i, L.seen.contains i = true → ∃ p ∈ L.cells.toList, p.1 = i
  back : L.restore a = old

theorem size_foldr_step (xs : List (Nat × α)) (a : Array α) :
    (xs.foldr step a).size = a.size := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simp [step, ih]

/-- A write of a cell that no logged value covers commutes with putting them back. -/
theorem foldr_step_set_comm (xs : List (Nat × α)) (a : Array α) (j : Nat) (v : α)
    (hj : ∀ p ∈ xs, p.1 ≠ j) :
    xs.foldr step (a.setIfInBounds j v) = (xs.foldr step a).setIfInBounds j v := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [List.foldr_cons]
    rw [ih (fun q hq => hj q (List.mem_cons_of_mem _ hq))]
    exact Array.setIfInBounds_comm _ _ (hj p (List.mem_cons_self ..)).symm

/-- A write of a cell that a logged value covers is undone by putting them back. -/
theorem foldr_step_set_covered (xs : List (Nat × α)) (a : Array α) (i : Nat) (v : α)
    (hi : ∃ p ∈ xs, p.1 = i) :
    xs.foldr step (a.setIfInBounds i v) = xs.foldr step a := by
  induction xs with
  | nil => simp at hi
  | cons p xs ih =>
    simp only [List.foldr_cons]
    by_cases h : ∃ q ∈ xs, q.1 = i
    · rw [ih h]
    · have hne : ∀ q ∈ xs, q.1 ≠ i := fun q hq e => h ⟨q, hq, e⟩
      have hp : p.1 = i := by
        obtain ⟨q, hq, e⟩ := hi
        rcases List.mem_cons.mp hq with rfl | hq
        · exact e
        · exact absurd e (hne q hq)
      rw [foldr_step_set_comm xs a i v hne]
      simp [step, hp]

/-- A push commutes with putting back logged values of cells that were there before it. -/
theorem foldr_step_push (xs : List (Nat × α)) (a : Array α) (v : α)
    (hj : ∀ p ∈ xs, p.1 < a.size) :
    xs.foldr step (a.push v) = (xs.foldr step a).push v := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [List.foldr_cons]
    rw [ih (fun q hq => hj q (List.mem_cons_of_mem _ hq))]
    have hp : p.1 < (xs.foldr step a).size := by rw [size_foldr_step]; exact hj p (List.mem_cons_self ..)
    simp only [step]
    apply Array.ext
    · simp
    · intro k h1 h2
      simp only [Array.size_push, Array.size_setIfInBounds] at h1 h2
      rw [Array.getElem_setIfInBounds (by simpa using h1)]
      by_cases hk : k < (xs.foldr step a).size
      · rw [Array.getElem_push_lt (by simpa using hk), Array.getElem_push_lt (by simpa using hk),
          Array.getElem_setIfInBounds hk]
      · have : k = (xs.foldr step a).size := by omega
        subst this
        rw [if_neg (by omega)]
        simp [Array.getElem_push]

theorem foldr_eq (L : UndoLog α) (a : Array α) : L.cells.foldr step a = L.cells.toList.foldr step a :=
  (Array.foldr_toList ..).symm

/-- A new log of `old` holds. -/
theorem inv_start (old : Array α) : Inv old (start old.size) old where
  base := rfl
  size := Nat.le_refl _
  below := by simp [start]
  seen := by intro i h; simp [start] at h
  back := by
    simp only [restore, start, Array.foldr_empty]
    rw [Array.shrink_eq_take, Array.take_eq_extract, Array.extract_size]

/-- Noting a cell keeps the invariant (the array is unchanged). -/
theorem inv_note (old : Array α) (L : UndoLog α) (a : Array α) (i : Nat) (h : Inv old L a) :
    Inv old (L.note a i).1 (L.note a i).2 := by
  unfold note noteAt
  by_cases hb : i < L.base
  · simp only [hb, if_true]
    by_cases hs : L.seen.contains i = true
    · simp only [hs, if_true]; exact h
    · simp only [hs]
      by_cases hi : i < a.size
      · simp only [hi, dite_true, Bool.false_eq_true, if_false]
        refine ⟨h.base, h.size, ?_, ?_, ?_⟩
        · intro p hp
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact h.below p hp
          · exact hb
        · intro k hk
          simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hk
          rcases hk with rfl | hk
          · exact ⟨(i, a[i]), by simp, rfl⟩
          · obtain ⟨p, hp, e⟩ := h.seen k hk
            exact ⟨p, by simp [hp], e⟩
        · have hback := h.back
          simp only [restore] at hback ⊢
          rw [Array.foldr_push]
          simp only [step]
          have : a.setIfInBounds i a[i] = a := by
            apply Array.ext
            · simp
            · intro k h1 h2
              rw [Array.getElem_setIfInBounds h2]
              split <;> simp_all
          rw [this]; exact hback
      · simp only [hi, dite_false, Bool.false_eq_true, if_false]; exact h
  · simp only [hb, if_false]; exact h

/-- A write of a cell keeps the invariant when the cell is logged, was not there when the action
began, or is not a cell of the array. -/
theorem inv_set (old : Array α) (L : UndoLog α) (a : Array α) (i : Nat) (v : α) (h : Inv old L a)
    (hc : L.base ≤ i ∨ L.seen.contains i = true ∨ a.size ≤ i) :
    Inv old L (a.setIfInBounds i v) := by
  refine ⟨h.base, by simpa using h.size, h.below, h.seen, ?_⟩
  have hback := h.back
  simp only [restore, foldr_eq] at hback ⊢
  rcases hc with hc | hc | hc
  · rw [foldr_step_set_comm _ _ _ _ (fun p hp e => by have := h.below p hp; omega)]
    rw [← hback, Array.shrink_eq_take, Array.shrink_eq_take]
    apply Array.ext
    · simp
    · intro k h1 h2
      have hk : k < L.base := by
        simp only [Array.take_eq_extract, Array.size_extract, Array.size_setIfInBounds] at h1
        omega
      simp only [Array.take_eq_extract, Array.getElem_extract, Nat.zero_add]
      rw [Array.getElem_setIfInBounds, if_neg (by omega)]
  · obtain ⟨p, hp, e⟩ := h.seen i hc
    rw [foldr_step_set_covered _ _ _ _ ⟨p, hp, e⟩]; exact hback
  · rw [Array.setIfInBounds_eq_of_size_le hc]; exact hback

/-- A push keeps the invariant. -/
theorem inv_push (old : Array α) (L : UndoLog α) (a : Array α) (v : α) (h : Inv old L a) :
    Inv old L (a.push v) := by
  refine ⟨h.base, by simp; have := h.size; omega, h.below, h.seen, ?_⟩
  have hback := h.back
  simp only [restore, foldr_eq] at hback ⊢
  rw [foldr_step_push _ _ _ (fun p hp => by have := h.below p hp; have := h.size; have := h.base; omega)]
  rw [← hback, Array.shrink_eq_take, Array.shrink_eq_take]
  have hs : L.base ≤ (L.cells.toList.foldr step a).size := by
    rw [size_foldr_step]; have := h.size; have := h.base; omega
  apply Array.ext
  · simp only [Array.take_eq_extract, Array.size_extract, Array.size_push]; omega
  · intro k h1 h2
    have hk : k < L.base := by
      simp only [Array.take_eq_extract, Array.size_extract, Array.size_push] at h1
      omega
    simp only [Array.take_eq_extract, Array.getElem_extract, Nat.zero_add]
    rw [Array.getElem_push_lt (by omega)]

/-- Undo: under the invariant, `restore` gives back the array from before the action, every cell
(the ones the action wrote and the ones it did not), and its size. -/
theorem restore_of_inv (old : Array α) (L : UndoLog α) (a : Array α) (h : Inv old L a) :
    L.restore a = old := h.back

/-- A write noted first keeps the invariant: `note` then `setIfInBounds` at the same cell, as
the heap's writes do (`JS.modifyObj`, `JS.updateObj`, `JS.pushEnv`, ...). -/
theorem inv_write (old : Array α) (L : UndoLog α) (a : Array α) (i : Nat) (v : α) (h : Inv old L a) :
    Inv old (L.note a i).1 ((L.note a i).2.setIfInBounds i v) := by
  apply inv_set _ _ _ _ _ (inv_note old L a i h)
  unfold note noteAt
  by_cases hb : i < L.base
  · simp only [hb, if_true]
    by_cases hs : L.seen.contains i = true
    · simp [hs]
    · by_cases hi : i < a.size
      · simp [hs, hi]
      · simp [hs, hi]; omega
  · simp only [hb, if_false]; omega

/-- With no log (`base` 0), `note` does nothing: a page that keeps no undo pays one comparison. -/
theorem note_off (L : UndoLog α) (a : Array α) (i : Nat) (h : L.base = 0) : L.note a i = (L, a) := by
  simp [note, h]

end UndoLog

end L4Factoidal.JS
