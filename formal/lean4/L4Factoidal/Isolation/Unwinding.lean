/-! # Origin isolation, the generic part (lemma L0): unwinding conditions give noninterference

Issue 518 and `docs/designissues/2026-11-16-origin-isolation.md` (section 4). A system is a
step relation with an invariant kept by steps; an observer (an origin) has a view of states and
of events. If the observer's view is unchanged by every event that is not its own (local
respect) and two of its events that look the same to it, from states that look the same, give
states that look the same (step consistency), then two runs from states with the same view in
which the observer makes and receives the same events end in states with the same view
(`noninterference`), whatever the other events of each run were. The engine instance (lemma
L15) supplies `Unwinding` for the whole step from the per-module lemmas L1 to L14.

No imports: only Lean core. -/
namespace L4Factoidal.Isolation


variable {State Event View Vis : Type}

/-- A system: which events may happen in a state, and the state after. -/
structure Sys (State Event : Type) where
  step : State → Event → State → Prop
  /-- Well-formed states (labels consistent, frame records narrow, tables within bounds). -/
  inv : State → Prop
  inv_step : ∀ s e s', inv s → step s e s' → inv s'

/-- Runs of a system. -/
inductive Sys.Run (S : Sys State Event) : State → List Event → State → Prop
  | nil (s : State) : Sys.Run S s [] s
  | cons {s : State} {e : Event} {s' : State} {es : List Event} {s'' : State} :
      S.step s e s' → Sys.Run S s' es s'' → Sys.Run S s (e :: es) s''

/-- An observer (an origin): its view of a state, and its view of an event
(`none`: the event is not one the observer makes or receives). -/
structure Observer (State Event View Vis : Type) where
  view : State → View
  vis : Event → Option Vis

/-- The observer's inputs in a run: its view of each event it makes or receives, in order. -/
def Observer.purge (O : Observer State Event View Vis) (es : List Event) : List Vis := es.filterMap O.vis

/-- The two unwinding conditions, on well-formed states. -/
structure Unwinding (S : Sys State Event) (O : Observer State Event View Vis) : Prop where
  /-- Local respect: an event that is not the observer's leaves its view as it was. -/
  local_respect : ∀ s e s', S.inv s → S.step s e s' → O.vis e = none → O.view s' = O.view s
  /-- Step consistency: from states with the same view, two events that look the same to the
  observer give states with the same view. -/
  step_consistent : ∀ s₁ s₂ e₁ e₂ s₁' s₂', S.inv s₁ → S.inv s₂ → O.view s₁ = O.view s₂ →
    S.step s₁ e₁ s₁' → S.step s₂ e₂ s₂' → O.vis e₁ = O.vis e₂ → O.vis e₁ ≠ none → O.view s₁' = O.view s₂'

theorem run_invisible {S : Sys State Event} {O : Observer State Event View Vis} (h : Unwinding S O) :
    ∀ {s es s'}, S.Run s es s' → S.inv s → O.purge es = [] → O.view s' = O.view s := by
  intro s es s' r
  induction r with
  | nil s => intro _ _; rfl
  | @cons s e s' es s'' hstep _ ih =>
    intro hi hp
    cases hv : O.vis e with
    | none =>
      have hp' : O.purge es = [] := by simpa [Observer.purge, List.filterMap_cons, hv] using hp
      rw [ih (S.inv_step _ _ _ hi hstep) hp', h.local_respect _ _ _ hi hstep hv]
    | some v => simp [Observer.purge, hv] at hp

/-- Noninterference: two runs from well-formed states with the same view, in which the
observer makes and receives the same events in the same order, end in states with the same
view, whatever the other events of each run were. -/
theorem noninterference {S : Sys State Event} {O : Observer State Event View Vis} (h : Unwinding S O) :
    ∀ {s₁ es₁ s₁'}, S.Run s₁ es₁ s₁' → ∀ {s₂ es₂ s₂'}, S.Run s₂ es₂ s₂' →
      S.inv s₁ → S.inv s₂ → O.view s₁ = O.view s₂ → O.purge es₁ = O.purge es₂ → O.view s₁' = O.view s₂' := by
  intro s₁ es₁ s₁' r₁
  induction r₁ with
  | nil s =>
    intro s₂ es₂ s₂' r₂ _ hi₂ hv hp
    rw [run_invisible h r₂ hi₂ (by simpa [Observer.purge] using hp.symm)]; exact hv
  | @cons s e s' es s'' hstep hrun ih =>
    intro s₂ es₂ s₂' r₂ hi₁ hi₂ hv hp
    cases hvis : O.vis e with
    | none =>
      apply ih r₂ (S.inv_step _ _ _ hi₁ hstep) hi₂
      · rw [h.local_respect _ _ _ hi₁ hstep hvis]; exact hv
      · simpa [Observer.purge, List.filterMap_cons, hvis] using hp
    | some v =>
      have hp' : v :: O.purge es = O.purge es₂ := by
        simpa [Observer.purge, List.filterMap_cons, hvis] using hp
      clear hp
      induction r₂ with
      | nil t => simp [Observer.purge] at hp'
      | @cons t e₂ t' es₂ t'' hstep₂ hrun₂ ih₂ =>
        cases hvis₂ : O.vis e₂ with
        | none =>
          apply ih₂ (S.inv_step _ _ _ hi₂ hstep₂)
          · rw [h.local_respect _ _ _ hi₂ hstep₂ hvis₂]; exact hv
          · simpa [Observer.purge, List.filterMap_cons, hvis₂] using hp'
        | some v₂ =>
          have hp'' : v :: O.purge es = v₂ :: O.purge es₂ := by
            simpa [Observer.purge, List.filterMap_cons, hvis₂] using hp'
          injection hp'' with hvv htl
          apply ih hrun₂ (S.inv_step _ _ _ hi₁ hstep) (S.inv_step _ _ _ hi₂ hstep₂)
          · exact h.step_consistent _ _ _ _ _ _ hi₁ hi₂ hv hstep hstep₂ (by rw [hvis, hvis₂, hvv])
              (by rw [hvis]; simp)
          · exact htl

end L4Factoidal.Isolation
