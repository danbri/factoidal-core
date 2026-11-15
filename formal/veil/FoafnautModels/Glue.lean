import Veil
import L4Factoidal.EventLoop.Theorems

/-!
# Veil as glue: the engine's event loop as a component of a system model

The engine's event-loop model (`formal/lean4/L4Factoidal/EventLoop/Model.lean`, WHATWG HTML event
loop: task queues, microtasks, timers, animation frames) is a pure Lean state machine with its
own proved invariant, `EventLoop.Inv` (armed timers in firing order, each armed before
`nextSeq`), kept by every input (`EventLoop.Input.apply_keep`).

Here that state machine is used unchanged, compiled from the engine's source, as the per-page
component of a Veil system: each page has its own event loop, and the host gives one input to
one page at a time. The system invariant, every page's event loop satisfies `Inv`, is proved by
the component's theorem, not by SMT: Veil generates the verification conditions and the
component's lemmas discharge them. The same pattern would put the host contract's trace
conformance, the URL parser or the GPU residency plan in the same system model.
-/

veil module PageLoops

type page

function loop : page → L4Factoidal.EventLoop.State

#gen_state

after_init {
  loop P := ({} : L4Factoidal.EventLoop.State)
}

/- The host gives input `i` (a callback's call, a clock advance, a task step, a rendering
opportunity, a frame step) to page `p`'s event loop. -/
transition input {
  ∃ (p : page) (i : L4Factoidal.EventLoop.Input),
    ∀ q, loop' q = if q = p then (i.apply (loop q)).1 else loop q
}

invariant [loops_ok] L4Factoidal.EventLoop.Inv (loop P)

#gen_spec

-- The empty event loop satisfies the component's invariant.
prove_veil_invariant_goal initializer loops_ok using wp by
  exact ⟨List.Pairwise.nil, fun t ht => by simp at ht⟩

-- An input to one page keeps every page's invariant: the input's page by the component's
-- theorem `Input.apply_keep`, the others because their state is unchanged.
prove_veil_invariant_goal input loops_ok using tr by
  obtain ⟨p, i, h⟩ := htr
  rw [h P]
  split
  · exact (L4Factoidal.EventLoop.Input.apply_keep (hinv P)).1
  · exact hinv P

#check_invariants

end PageLoops
