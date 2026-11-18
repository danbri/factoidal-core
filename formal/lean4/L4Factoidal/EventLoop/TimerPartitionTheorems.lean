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

#print axioms mem_due_now_iff
#print axioms mem_due_later_iff
#print axioms fire_no_due
#print axioms fire_idempotent

end L4Factoidal.EventLoop
