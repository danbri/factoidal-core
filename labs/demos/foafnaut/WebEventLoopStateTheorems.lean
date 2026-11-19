import WebEventLoop
import L4Factoidal.EventLoop.Theorems

namespace WebEventLoop

open L4Factoidal
open L4Factoidal.EventLoop

/-- Kind: timer order lemma.
Says: checking consecutive timer keys suffices to establish the pairwise
firing order, because the key comparison is transitive.
Does not say: that sequence numbers alone increase through the list. -/
private theorem sorted_of_adjacent (timers : List Timer)
    (h : (timers.zip timers.tail).all (fun (a, b) => keyLe a b) = true) :
    Sorted timers := by
  induction timers with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.Pairwise.cons (by intro _ hmem; cases hmem) List.Pairwise.nil
    | cons b rest =>
      simp only [List.tail_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      have htail : Sorted (b :: rest) := ih h.2
      refine List.pairwise_cons.mpr ⟨?_, htail⟩
      intro t hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact h.1
      · exact keyLe_trans h.1 ((List.pairwise_cons.mp htail).1 t hmem)

/-- Kind: admission check soundness.
Says: the successful timer guards establish firing order and an upper bound
on every armed timer's sequence number.
Does not say: that the other fields of the state came from a prior model step. -/
private theorem inv_of_timer_guard (st : State)
    (h : ¬ ((!(st.timers.zip st.timers.tail).all (fun (a, b) => keyLe a b) ||
      !(st.timers.all fun t => decide (t.seq < st.nextSeq))) = true)) : Inv st := by
  have checks := Bool.eq_false_iff.mpr h
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at checks
  exact ⟨sorted_of_adjacent _ checks.1,
    fun t ht => of_decide_eq_true (List.all_eq_true.mp checks.2 t ht)⟩

/-- Kind: JSON adapter and event-loop model invariant.
Says: every state admitted by the browser's actual state parser has its
armed timers ordered by firing key, with each sequence number below the
next sequence number.
Does not say: that the state came from an earlier engine response, that
timer IDs match the active set, or that the JSON transport round-trips. -/
theorem stateOf_inv (j : JSON.Json) (st : State) (h : stateOf j = .ok st) : Inv st := by
  unfold stateOf at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' first
    | contradiction
    | split at h
  all_goals
    rename_i hguard
    cases h
    exact inv_of_timer_guard _ hguard

#print axioms stateOf_inv

end WebEventLoop
