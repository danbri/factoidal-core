import L4Factoidal.JS.Interp

/-!
# Fuel monotonicity of the BubblePopJS evaluator: the relation and its rules

Every function of the evaluator's mutual block (`JS/Interp.lean`) takes a fuel argument and
answers `halt "fuel"` when it runs out. The property every whole-run theorem needs
(`docs/bubblepopjs-jit.md`, design review on issue 471): if a function ends at fuel `n` with
anything but `halt "fuel"`, it ends the same way at every fuel `m ≥ n`.

This file has the relation `Le x y` ("`x` ran out of fuel, or `x` and `y` give the same
result, from every heap") and its rules for the monad's combinators, so that the property of a
function body follows from the property of the calls in it. A handler that keeps going after a
halt breaks the rule for `tryCatch` (`Le.tryCatch` needs the handler to pass `halt "fuel"` on);
`catchJS` passes every halt on, so its rule has no side condition (`Le.catchJS`).

The register machine is a parameter of the run (`HeapOf.useVm`); the relation is over every
heap, so it covers the machine off (the reference) and on.
-/

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

variable {H : Type} {α β : Type}

/-- The run ended out of fuel. -/
def Out (r : EStateM.Result Abrupt (HeapOf H) α) : Prop :=
  ∃ s, r = .error (.halt "fuel") s

/-- `x` (at a smaller fuel) ran out of fuel, or it ends as `y` (at a larger fuel) does, from
every heap. Reflexive and transitive. -/
def Le (x y : JSM H α) : Prop := ∀ s, Out (x s) ∨ x s = y s

theorem Le.refl (x : JSM H α) : Le x x := fun _ => Or.inr rfl

theorem Le.trans {x y z : JSM H α} (hxy : Le x y) (hyz : Le y z) : Le x z := by
  intro s
  rcases hxy s with h | h
  · exact Or.inl h
  · rcases hyz s with h' | h'
    · exact Or.inl (h ▸ h')
    · exact Or.inr (h.trans h')

theorem Le.of_out {x y : JSM H α} (h : ∀ s, Out (x s)) : Le x y := fun s => Or.inl (h s)

theorem Le.fuel (y : JSM H α) : Le (throw (.halt "fuel")) y :=
  Le.of_out fun s => ⟨s, rfl⟩

theorem Le.bind {x1 x2 : JSM H α} {k1 k2 : α → JSM H β} (hx : Le x1 x2)
    (hk : ∀ a, Le (k1 a) (k2 a)) : Le (x1 >>= k1) (x2 >>= k2) := by
  intro s
  show Out (EStateM.bind x1 k1 s) ∨ EStateM.bind x1 k1 s = EStateM.bind x2 k2 s
  unfold EStateM.bind
  rcases hx s with ⟨s', h⟩ | h
  · left; rw [h]; exact ⟨s', rfl⟩
  · rw [← h]
    cases x1 s with
    | ok a s' => exact hk a s'
    | error e s' => exact Or.inr rfl

/-- The handler must pass an out-of-fuel halt on. -/
theorem Le.tryCatch {x1 x2 : JSM H α} {k1 k2 : Abrupt → JSM H α} (hx : Le x1 x2)
    (hk : ∀ a, Le (k1 a) (k2 a)) (hf : ∀ s, Out (k1 (.halt "fuel") s)) :
    Le (tryCatch x1 k1) (tryCatch x2 k2) := by
  intro s
  show Out (EStateM.tryCatch x1 k1 s) ∨ EStateM.tryCatch x1 k1 s = EStateM.tryCatch x2 k2 s
  unfold EStateM.tryCatch
  rcases hx s with ⟨s', h⟩ | h
  · left; rw [h]; exact hf _
  · rw [← h]
    cases x1 s with
    | ok a s' => exact Or.inr rfl
    | error e s' => exact hk e _

theorem catchJS_fuel (k : Abrupt → JSM H α) (s : HeapOf H) :
    Out ((fun a => match a with | .halt w => throw (.halt w) | a => k a : Abrupt → JSM H α)
      (.halt "fuel") s) := ⟨s, rfl⟩

theorem Le.catchJS {x1 x2 : JSM H α} {k1 k2 : Abrupt → JSM H α} (hx : Le x1 x2)
    (hk : ∀ a, Le (k1 a) (k2 a)) : Le (catchJS x1 k1) (catchJS x2 k2) := by
  unfold L4Factoidal.JS.catchJS
  refine Le.tryCatch hx ?_ (catchJS_fuel k1)
  intro a
  cases a with
  | halt w => exact Le.refl _
  | throw v => exact hk _

/-- A handler that drops every completion breaks the rule: from a run out of fuel it goes on.
This is the shape `catchJS` replaced (IteratorClose after a throw). -/
theorem drop_not_out (s : HeapOf H) :
    ¬ Out ((tryCatch (throw (.halt "fuel")) (fun _ => pure ()) : JSM H Unit) s) := by
  rintro ⟨s', h⟩
  cases h

/-- What `Le` gives for a run: at the larger fuel, the same result, unless the smaller ran out. -/
theorem Le.eq_of_not_out {x y : JSM H α} (h : Le x y) (s : HeapOf H) (hn : ¬ Out (x s)) :
    y s = x s :=
  ((h s).resolve_left hn).symm

theorem Le.unfold {x x' y y' : JSM H α} (hx : x = x') (hy : y = y') (h : Le x' y') : Le x y := by
  subst hx; subst hy; exact h

-- `Le` is opened only by the rules above, so that the walk below never unfolds it.
attribute [irreducible] Le

/-! ## Walking a body

`fuel_mono` takes a goal `Le (body at n) (body at m)`, where the two bodies are the same term
but for the fuel of the calls in them, apart: binds, handlers and matches are split, equal
pieces close by `Le.refl`, and a call closes by a hypothesis (the induction hypothesis for
that function). -/

syntax "fuel_mono_step" : tactic
macro_rules
  | `(tactic| fuel_mono_step) => `(tactic| first
      | with_reducible exact Le.refl _
      | exact Le.fuel _
      | (apply Le.bind)
      | (apply Le.catchJS)
      | (intro _)
      | split)

syntax "fuel_mono" : tactic
macro_rules
  | `(tactic| fuel_mono) => `(tactic| repeat' (first | fuel_mono_step | (apply_assumption)))

end L4Factoidal.JS.FuelMono
