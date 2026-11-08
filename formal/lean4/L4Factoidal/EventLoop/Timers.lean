/-!
# Timers (WHATWG HTML §8.6)

The list of armed timers, kept in the order in which they fire, and the
timeout clamp.

HTML §8.6 "run steps after a timeout" says that an invocation waits "until any
invocations of this algorithm that had the same method context, that started
before this one, and whose timeout is equal to or less than this one's, have
completed". So timers fire in order of due time, and timers with the same due
time fire in the order in which they were set. Each armed timer carries `seq`,
the count of arms before it. The key of a timer is `(due, seq)`, and the list
is sorted by that key (`Sorted`, kept by `insert`, proved in `insert_sorted`).

Only Lean core. Every function here is a loop or a core combinator with a
tail-recursive replacement (`takeWhile`, `dropWhile`, `filter`, `++`).
-/
namespace L4Factoidal.EventLoop

/-- An opaque callback. The host or the script engine runs it; the model only
decides what runs and when. -/
abbrev Handle := Nat

/-- One armed timer. `timeout` is the timeout as the script gave it (made a
natural number), kept for `setInterval` (`periodic`); `due` is the clock value at which it
fires; `nesting` is the timer nesting level of the task it queues. -/
structure Timer where
  id : Nat
  callback : Handle
  due : Nat
  seq : Nat
  timeout : Nat
  periodic : Bool
  nesting : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `a` fires no later than `b`: earlier due time, or the same due time and set
no later. -/
def keyLe (a b : Timer) : Bool :=
  decide (a.due < b.due) || (decide (a.due = b.due) && decide (a.seq ≤ b.seq))

theorem keyLe_iff {a b : Timer} :
    keyLe a b = true ↔ a.due < b.due ∨ (a.due = b.due ∧ a.seq ≤ b.seq) := by
  simp [keyLe]

theorem keyLe_trans {a b c : Timer} (h₁ : keyLe a b = true) (h₂ : keyLe b c = true) :
    keyLe a c = true := by
  rw [keyLe_iff] at *; omega

theorem keyLe_total {a b : Timer} (h : keyLe a b = false) : keyLe b a = true := by
  have : ¬ (a.due < b.due ∨ (a.due = b.due ∧ a.seq ≤ b.seq)) := by
    intro k; rw [← keyLe_iff] at k; simp [k] at h
  rw [keyLe_iff]; omega

/-- A timer list in firing order. -/
def Sorted (l : List Timer) : Prop := l.Pairwise (fun a b => keyLe a b = true)

/-- Insert after every timer that fires no later. -/
def insert (t : Timer) (l : List Timer) : List Timer :=
  l.takeWhile (fun x => keyLe x t) ++ t :: l.dropWhile (fun x => keyLe x t)

theorem mem_takeWhile_imp {p : α → Bool} : ∀ {l : List α} {x : α}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.1 h with e | h
      · subst e; assumption
      · exact mem_takeWhile_imp h
    · simp at h

theorem dropWhile_head {p : α → Bool} : ∀ {l : List α} {h : α} {r : List α},
    l.dropWhile p = h :: r → p h = false
  | [], _, _, e => by simp at e
  | y :: ys, h, r, e => by
    rw [List.dropWhile_cons] at e
    split at e
    · exact dropWhile_head e
    · cases e; simp_all

theorem mem_insert {t x : Timer} {l : List Timer} : x ∈ insert t l ↔ x = t ∨ x ∈ l := by
  have split := List.takeWhile_append_dropWhile (p := fun x => keyLe x t) (l := l)
  constructor
  · intro h
    simp only [insert, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact .inr (List.takeWhile_subset _ h)
    · exact .inl h
    · exact .inr (List.dropWhile_subset _ h)
  · intro h
    simp only [insert, List.mem_append, List.mem_cons]
    rcases h with h | h
    · exact .inr (.inl h)
    · rw [← split, List.mem_append] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inr h)

/-- Insertion keeps the list in firing order. -/
theorem insert_sorted {t : Timer} {l : List Timer} (h : Sorted l) : Sorted (insert t l) := by
  have split := List.takeWhile_append_dropWhile (p := fun x => keyLe x t) (l := l)
  unfold Sorted at *
  rw [← split, List.pairwise_append] at h
  obtain ⟨hA, hB, hAB⟩ := h
  unfold insert
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hA, ⟨?_, hB⟩, ?_⟩
  · -- `t` fires no later than every timer after it.
    intro b hb
    cases e : l.dropWhile (fun x => keyLe x t) with
    | nil => rw [e] at hb; simp at hb
    | cons h r =>
      have first : keyLe t h = true := keyLe_total (dropWhile_head (p := fun x => keyLe x t) e)
      rw [e] at hb hB
      rcases List.mem_cons.1 hb with hb | hb
      · subst hb; exact first
      · exact keyLe_trans first ((List.pairwise_cons.1 hB).1 b hb)
  · intro a ha b hb
    rcases List.mem_cons.1 hb with hb | hb
    · rw [hb]; exact mem_takeWhile_imp (p := fun x => keyLe x t) ha
    · exact hAB a ha b hb

theorem filter_sorted {p : Timer → Bool} {l : List Timer} (h : Sorted l) : Sorted (l.filter p) :=
  List.Pairwise.sublist List.filter_sublist h

/-- HTML §8.6 timer initialization steps 4 and 5: "If nesting level is greater
than 5, and timeout is less than 4, then set timeout to 4." A negative or NaN
timeout is 0 before this step; the host gives a natural number. -/
def clamp (nesting timeout : Nat) : Nat :=
  if 5 < nesting ∧ timeout < 4 then 4 else timeout

theorem clamp_ge (nesting timeout : Nat) : timeout ≤ clamp nesting timeout := by
  unfold clamp; split <;> omega

theorem clamp_shallow {nesting timeout : Nat} (h : nesting ≤ 5) : clamp nesting timeout = timeout := by
  unfold clamp; split <;> omega

theorem clamp_deep {nesting timeout : Nat} (h : 5 < nesting) : clamp nesting timeout = max 4 timeout := by
  unfold clamp; split <;> omega

theorem clamp_long (nesting : Nat) {timeout : Nat} (h : 4 ≤ timeout) : clamp nesting timeout = timeout := by
  unfold clamp; split <;> omega

/-- The timers due at `clock`, in firing order, and the timers left. -/
def due (clock : Nat) (l : List Timer) : List Timer × List Timer :=
  (l.takeWhile (fun t => decide (t.due ≤ clock)), l.dropWhile (fun t => decide (t.due ≤ clock)))

theorem due_parts {clock : Nat} {l : List Timer} : (due clock l).1 ++ (due clock l).2 = l :=
  List.takeWhile_append_dropWhile

/-- The fired timers are in firing order, each fired timer fires no later than
each timer left, and each fired timer is due. -/
theorem due_sorted {clock : Nat} {l : List Timer} (h : Sorted l) :
    Sorted (due clock l).1 ∧ Sorted (due clock l).2 ∧
    (∀ a ∈ (due clock l).1, ∀ b ∈ (due clock l).2, keyLe a b = true) ∧
    (∀ a ∈ (due clock l).1, a.due ≤ clock) := by
  unfold Sorted at *
  rw [← (due_parts (clock := clock) (l := l)), List.pairwise_append] at h
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  intro a ha
  have := mem_takeWhile_imp ha
  simpa using this

end L4Factoidal.EventLoop
