import L4Factoidal.EventLoop.Theorems

namespace L4Factoidal.EventLoop

private theorem due_later {clock : Nat} {l : List Timer} (h : Sorted l)
    {t : Timer} (ht : t ∈ (due clock l).2) : clock < t.due := by
  induction l with
  | nil => simp [due] at ht
  | cons a rest ih =>
    have hs := List.pairwise_cons.mp h
    by_cases ha : a.due ≤ clock
    · apply ih hs.2
      simpa [due, List.dropWhile_cons, ha] using ht
    · have hm : t ∈ a :: rest := by
        simpa [due, List.dropWhile_cons, ha] using ht
      rcases List.mem_cons.mp hm with he | hr
      · subst t
        omega
      · have hk := keyLe_iff.mp (hs.1 t hr)
        omega

/-- Kind: functional law.
Says: the selected prefix contains exactly the timers due at this clock, for a
queue in firing order.
Does not say: that a selected timer's callback has run. -/
theorem mem_due_now_iff {clock : Nat} {l : List Timer} (h : Sorted l) (t : Timer) :
    t ∈ (due clock l).1 ↔ t ∈ l ∧ t.due ≤ clock := by
  have parts := due_parts (clock := clock) (l := l)
  constructor
  · intro ht
    refine ⟨?_, (due_sorted (clock := clock) h).2.2.2 t ht⟩
    rw [← parts, List.mem_append]
    exact Or.inl ht
  · rintro ⟨ht, hd⟩
    rw [← parts, List.mem_append] at ht
    rcases ht with hnow | hlater
    · exact hnow
    · have := due_later h hlater
      omega

/-- Kind: functional law.
Says: the retained suffix contains exactly the timers whose due times exceed
this clock, for a queue in firing order.
Does not say: that a later operation cannot rearm a timer. -/
theorem mem_due_later_iff {clock : Nat} {l : List Timer} (h : Sorted l) (t : Timer) :
    t ∈ (due clock l).2 ↔ t ∈ l ∧ clock < t.due := by
  have parts := due_parts (clock := clock) (l := l)
  constructor
  · intro ht
    refine ⟨?_, due_later h ht⟩
    rw [← parts, List.mem_append]
    exact Or.inr ht
  · rintro ⟨ht, hd⟩
    rw [← parts, List.mem_append] at ht
    rcases ht with hnow | hlater
    · have hle := ((mem_due_now_iff h t).mp hnow).2
      omega
    · exact hlater

/-- Kind: state invariant.
Says: firing an ordered timer queue leaves only timers due strictly after the
resulting clock.
Does not say: when the host advances the clock or runs a queued callback. -/
theorem fire_no_due (st : State) (h : Sorted st.timers) :
    ∀ t ∈ (st.fire).1.timers, (st.fire).1.clock < t.due := by
  obtain ⟨hqueue, _, hclock, _⟩ := fire_parts st
  rw [hqueue, hclock]
  intro t ht
  exact ((mem_due_later_iff h t).mp ht).2

private theorem fire_idle (st : State) (h : ∀ t ∈ st.timers, st.clock < t.due) :
    st.fire = (st, []) := by
  have hd : due st.clock st.timers = ([], st.timers) := by
    cases hq : st.timers with
    | nil => simp [due]
    | cons t ts =>
      have ht : t ∈ st.timers := by simp [hq]
      have hlate : ¬ t.due ≤ st.clock := Nat.not_le.mpr (h t ht)
      simp [due, hlate]
  cases st
  simp [State.fire, hd]

/-- Kind: functional law.
Says: firing an ordered queue twice, with no intervening operation, leaves
the state from the first firing unchanged and reports no newly fired timers.
Does not say: that running a callback leaves the timer queue unchanged. -/
theorem fire_idempotent (st : State) (h : Sorted st.timers) :
    (st.fire).1.fire = ((st.fire).1, []) :=
  fire_idle (st.fire).1 (fire_no_due st h)

/-- Kind: functional law.
Says: for an ordered timer queue, the two partitions equal the stable filters
by the clock, preserving relative order and multiplicity.
Does not say: that a due timer has a runnable callback. -/
theorem due_eq_filters {clock : Nat} {l : List Timer} (h : Sorted l) :
    (due clock l).1 = l.filter (fun t => decide (t.due ≤ clock)) ∧
      (due clock l).2 = l.filter (fun t => decide (clock < t.due)) := by
  have hnow : ∀ t ∈ (due clock l).1, t.due ≤ clock :=
    (due_sorted (clock := clock) h).2.2.2
  have hlater : ∀ t ∈ (due clock l).2, clock < t.due :=
    fun _ ht => due_later h ht
  have hnowKeep : ((due clock l).1.filter fun t => decide (t.due ≤ clock)) = (due clock l).1 :=
    List.filter_eq_self.mpr (fun t ht => by simp [hnow t ht])
  have hlaterKeep : ((due clock l).2.filter fun t => decide (clock < t.due)) = (due clock l).2 :=
    List.filter_eq_self.mpr (fun t ht => by simp [hlater t ht])
  have hnowDrop : ((due clock l).1.filter fun t => decide (clock < t.due)) = [] :=
    List.filter_eq_nil_iff.mpr (fun t ht => by simp [Nat.not_lt.mpr (hnow t ht)])
  have hlaterDrop : ((due clock l).2.filter fun t => decide (t.due ≤ clock)) = [] :=
    List.filter_eq_nil_iff.mpr (fun t ht => by simp [Nat.not_le.mpr (hlater t ht)])
  have parts := due_parts (clock := clock) (l := l)
  constructor
  · calc
      (due clock l).1 =
          (((due clock l).1 ++ (due clock l).2).filter fun t => decide (t.due ≤ clock)) := by
        rw [List.filter_append, hnowKeep, hlaterDrop, List.append_nil]
      _ = _ := congrArg (List.filter fun t : Timer => decide (t.due ≤ clock)) parts
  · calc
      (due clock l).2 =
          (((due clock l).1 ++ (due clock l).2).filter fun t => decide (clock < t.due)) := by
        rw [List.filter_append, hnowDrop, hlaterKeep, List.nil_append]
      _ = _ := congrArg (List.filter fun t : Timer => decide (clock < t.due)) parts

/-- Kind: functional law.
Says: firing an ordered timer queue returns exactly the stable selection at
the current clock, retains the later timers, and appends one task per selected
timer with its source, callback, timer, event, and nesting fields fixed.
Does not say: that a queued task is selected or executed. -/
theorem fire_eq_filter_tasks (st : State) (h : Sorted st.timers) :
    (st.fire).2 = st.timers.filter (fun t => decide (t.due ≤ st.clock)) ∧
      (st.fire).1.timers = st.timers.filter (fun t => decide (st.clock < t.due)) ∧
      (st.fire).1.tasks = st.tasks ++
        (st.timers.filter (fun t => decide (t.due ≤ st.clock))).map (fun t =>
          { source := .timer, callback := t.callback, timer := some t, event := none,
            nesting := t.nesting }) := by
  obtain ⟨hnow, hlater⟩ := due_eq_filters (clock := st.clock) h
  change (due st.clock st.timers).1 = _ ∧ (due st.clock st.timers).2 = _ ∧
    st.tasks ++ (due st.clock st.timers).1.map (fun t =>
      { source := .timer, callback := t.callback, timer := some t, event := none,
        nesting := t.nesting }) = _
  rw [hnow, hlater] <;> exact ⟨rfl, rfl, rfl⟩

#print axioms mem_due_now_iff
#print axioms mem_due_later_iff
#print axioms fire_no_due
#print axioms fire_idempotent
#print axioms due_eq_filters
#print axioms fire_eq_filter_tasks

end L4Factoidal.EventLoop
