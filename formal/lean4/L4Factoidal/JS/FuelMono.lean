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
heap, so it covers the machine off (the reference) and on. Equal results include equal heaps,
so equal steps left: a host call (`hostCall`, which receives the steps left) sees the same
count at either fuel.

## State of the proof (2026-11-15)

`JS/FuelMonoSteps.lean` is written by `tools/fuelmono-gen.py` from `JS/Interp.lean`: the
induction hypothesis `IH H n m` over the 116 functions of the block that take fuel, and one
step lemma per function (its body at `n + 1` against `m + 1`, from `IH H n m`), proved by the
walk below with no hand-written proof. Proved today: 75 of the 116 steps, in 31 s (peak
3.1 GB). Not proved:

- 21 bodies with local functions (`do` join points `__do_jp`, local helpers such as `field`,
  `keyOf`): the two sides bind different closures (one calls at `n`, the other at `m`), and the
  walk stops at `Le (jpL x) (jpR x)`. Inlining them (zeta-delta) duplicates bodies and ran out
  of memory (7 GB in 90 s on `binop`). Needed: a tactic that pairs the two let-bound closures
  and proves `∀ x, Le (jpL x) (jpR x)` once by walking their bodies.
- The 20 largest bodies (40 to 2,079 lines: `evalExpr`, `evalStmt`, `vmLoop`, the generator
  machine, `callNative`, `extraNative`, `moreNative`): not tried after the first full run,
  which with the earlier walk reached 17 GB. Their equation lemmas alone take 25 s
  (`evalExpr.eq_2`), 111 s (`extraNative`) and 573 s (`callNative`).

So `IH_all` (monotonicity of the whole block) is not proved yet. The rules and the steps that
are proved use only `propext`, `Classical.choice` and `Quot.sound`.

Fuel monotonicity was false before `catchJS`: a `for`-`of` whose body throws, over an iterator
whose `return` nests calls, ended `ok [caught]` at fuels 18 to 59 and `ok [closed, caught]`
above (IteratorClose dropped the out-of-fuel halt of `return`). `drop_not_out` below is the
shape of that handler.
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


/-! ## Rules for the loops and maps of the library -/

theorem Le.map {x1 x2 : JSM H α} (f : α → β) (hx : Le x1 x2) : Le (f <$> x1) (f <$> x2) := by
  intro s
  show Out (EStateM.map f x1 s) ∨ EStateM.map f x1 s = EStateM.map f x2 s
  unfold EStateM.map
  rcases hx s with ⟨s', h⟩ | h
  · left; rw [h]; exact ⟨s', rfl⟩
  · rw [← h]
    exact Or.inr rfl

theorem Le.forIn_list {xs : List α} {b : β} {f1 f2 : α → β → JSM H (ForInStep β)}
    (hf : ∀ a b, Le (f1 a b) (f2 a b)) : Le (forIn xs b f1) (forIn xs b f2) := by
  induction xs generalizing b with
  | nil => exact Le.refl _
  | cons a as ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine Le.bind (hf a b) fun r => ?_
    cases r with
    | done b' => exact Le.refl _
    | yield b' => exact ih

theorem Le.forIn_array {xs : Array α} {b : β} {f1 f2 : α → β → JSM H (ForInStep β)}
    (hf : ∀ a b, Le (f1 a b) (f2 a b)) : Le (forIn xs b f1) (forIn xs b f2) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact Le.forIn_list hf

theorem Le.forIn_range {r : Std.Legacy.Range} {b : β} {f1 f2 : Nat → β → JSM H (ForInStep β)}
    (hf : ∀ a b, Le (f1 a b) (f2 a b)) : Le (forIn r b f1) (forIn r b f2) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact Le.forIn_list hf

theorem Le.mapM_list {xs : List α} {f1 f2 : α → JSM H β}
    (hf : ∀ a, Le (f1 a) (f2 a)) : Le (xs.mapM f1) (xs.mapM f2) := by
  induction xs with
  | nil => exact Le.refl _
  | cons a as ih =>
    rw [List.mapM_cons, List.mapM_cons]
    exact Le.bind (hf a) fun _ => Le.bind ih fun _ => Le.refl _

theorem Le.mapM_array {xs : Array α} {f1 f2 : α → JSM H β}
    (hf : ∀ a, Le (f1 a) (f2 a)) : Le (xs.mapM f1) (xs.mapM f2) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  exact Le.map _ (Le.mapM_list hf)

theorem Le.foldlM_list {xs : List α} {b : β} {f1 f2 : β → α → JSM H β}
    (hf : ∀ b a, Le (f1 b a) (f2 b a)) : Le (xs.foldlM f1 b) (xs.foldlM f2 b) := by
  induction xs generalizing b with
  | nil => exact Le.refl _
  | cons a as ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    exact Le.bind (hf b a) fun _ => ih

theorem Le.foldlM_array {xs : Array α} {b : β} {f1 f2 : β → α → JSM H β}
    (hf : ∀ b a, Le (f1 b a) (f2 b a)) : Le (xs.foldlM f1 b) (xs.foldlM f2 b) := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact Le.foldlM_list hf

theorem Le.filterMapM_list {xs : List α} {f1 f2 : α → JSM H (Option β)}
    (hf : ∀ a, Le (f1 a) (f2 a)) : Le (xs.filterMapM f1) (xs.filterMapM f2) := by
  induction xs with
  | nil => exact Le.refl _
  | cons a as ih =>
    rw [List.filterMapM_cons, List.filterMapM_cons]
    refine Le.bind (hf a) fun r => ?_
    cases r with
    | none => exact ih
    | some b => exact Le.bind ih fun _ => Le.refl _

-- `Le` is opened only by the rules above, so that the walk below never unfolds it.
attribute [irreducible] Le

/-! ## Walking a body

`fuel_mono` takes a goal `Le (body at n) (body at m)`, where the two bodies are the same term
but for the fuel of the calls in them, apart: binds, handlers and matches are split, equal
pieces close by `Le.refl`, and a call closes by a hypothesis (the induction hypothesis for
that function). -/

syntax "fuel_mono_pre" : tactic
macro_rules
  | `(tactic| fuel_mono_pre) => `(tactic| first
      | with_reducible (cases ‹_ + 1 = Nat.succ _›)
      | with_reducible exact Le.refl _
      | with_reducible exact Le.fuel _
      | with_reducible apply Le.bind
      | with_reducible apply Le.catchJS)

syntax "fuel_mono_post" : tactic
macro_rules
  | `(tactic| fuel_mono_post) => `(tactic| first
      | with_reducible apply Le.forIn_range
      | with_reducible apply Le.forIn_list
      | with_reducible apply Le.forIn_array
      | with_reducible apply Le.mapM_list
      | with_reducible apply Le.mapM_array
      | with_reducible apply Le.foldlM_list
      | with_reducible apply Le.foldlM_array
      | with_reducible apply Le.filterMapM_list
      | with_reducible apply Le.map
      | (intro _)
      | (lift_lets; extract_lets)
      | split
      | (dsimp (config := { zeta := false }) only))

/-- At fuel 0 `iterCloseAbrupt` is out of fuel, as every function of the block is. It threw its
completion there (with no call), so a run could end differently at fuel 0 than at fuel 1. -/
theorem iterCloseAbrupt_zero (it : Value) (a : Abrupt) :
    iterCloseAbrupt (H := H) 0 it a = throw (.halt "fuel") :=
  (iterCloseAbrupt.eq_def 0 it a).trans rfl

/-- So, at fuel 0, it is below itself at every fuel. -/
theorem iterCloseAbrupt_zero_le (m : Nat) (it : Value) (a : Abrupt) :
    Le (iterCloseAbrupt (H := H) 0 it a) (iterCloseAbrupt m it a) := by
  rw [iterCloseAbrupt_zero]
  exact Le.fuel _

end L4Factoidal.JS.FuelMono
