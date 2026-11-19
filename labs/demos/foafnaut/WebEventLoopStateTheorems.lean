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

/-- Kind: executable writer and reader counterexample (factoidal-core issue 630).
Says: advancing the empty model to the largest accepted clock and arming a
one-unit timer keeps the model invariant but produces a due time outside the
reader's bound. The reader refuses the actual writer's state.
Does not say: that a deployed host reached this clock or that callback
execution at this boundary was observed. -/
theorem stateJson_can_exceed_stateOf_timer_bound :
    let advanced := ((Input.advance 4294967295).apply ({} : State)).1
    let armed := ((Input.call (.setTimer 3 1 false)).apply advanced).1
    Inv armed ∧ armed.timers.map Timer.due = [4294967296] ∧
      stateOf (stateJson armed) = .error "eventLoop: number exceeds bound" := by
  dsimp only
  refine ⟨(Input.apply_keep (i := .call (.setTimer 3 1 false))
    (Input.apply_keep (i := .advance 4294967295) initial_inv).1).1, ?_, ?_⟩
  · decide +kernel
  · let advanced := ((Input.advance 4294967295).apply ({} : State)).1
    let armed := ((Input.call (.setTimer 3 1 false)).apply advanced).1
    change stateOf (stateJson armed) = .error "eventLoop: number exceeds bound"
    have herror : (match stateOf (stateJson armed) with
      | .ok _ => none
      | .error why => some why) = some "eventLoop: number exceeds bound" := by
      dsimp only [armed, advanced]
      decide +kernel
    split at herror
    · cases herror
    · rename_i why hstate
      rw [hstate]
      exact congrArg Except.error (Option.some.inj herror)

#print axioms stateOf_inv
#print axioms stateJson_can_exceed_stateOf_timer_bound

end WebEventLoop
