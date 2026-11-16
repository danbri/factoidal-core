import Lean.Elab.Tactic
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

/-- `if` on the same condition on both sides, without `split` (which rewrites the whole goal
with the condition afterwards: over a built-in's body that rewrite ran out of steps). -/
theorem Le.ite {c : Prop} [Decidable c] {t1 t2 e1 e2 : JSM H α} (ht : c → Le t1 t2)
    (he : ¬c → Le e1 e2) : Le (if c then t1 else e1) (if c then t2 else e2) := by
  by_cases h : c
  · simp only [if_pos h]; exact ht h
  · simp only [if_neg h]; exact he h

theorem Le.dite {c : Prop} [Decidable c] {t1 t2 : c → JSM H α} {e1 e2 : ¬c → JSM H α}
    (ht : ∀ h, Le (t1 h) (t2 h)) (he : ∀ h, Le (e1 h) (e2 h)) :
    Le (if h : c then t1 h else e1 h) (if h : c then t2 h else e2 h) := by
  by_cases h : c
  · simp only [dif_pos h]; exact ht h
  · simp only [dif_neg h]; exact he h

/-- `discard x` (`Functor.mapConst ()`, for `EStateM` the map of a constant function). -/
theorem Le.discard {x1 x2 : JSM H α} (hx : Le x1 x2) : Le (discard x1) (discard x2) :=
  Le.map (fun _ => PUnit.unit) hx

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

theorem Le.filterM_array {xs : Array α} {p1 p2 : α → JSM H Bool}
    (hp : ∀ a, Le (p1 a) (p2 a)) : Le (xs.filterM p1) (xs.filterM p2) := by
  unfold Array.filterM
  exact Le.foldlM_array fun acc a => Le.bind (hp a) fun _ => Le.refl _

theorem Le.filterMapM_array {xs : Array α} {f1 f2 : α → JSM H (Option β)}
    (hf : ∀ a, Le (f1 a) (f2 a)) : Le (xs.filterMapM f1) (xs.filterMapM f2) := by
  unfold Array.filterMapM
  exact Le.foldlM_array fun acc a => Le.bind (hf a) fun _ => Le.refl _

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

open Lean Meta Elab Tactic in
/-- A join point (a `do` block's `__do_jp`, or a local helper) after `extract_lets`: the goal is
`Le (f a…) (g b…)` with `f` and `g` let-bound locals, one closure per side (one calling at `n`,
the other at `m`). Put each value in place of its head, at that use only, and beta-reduce: the
walk then goes on into the two bodies as a pair. Unfolding only at the use keeps the term small
(inlining every let up front duplicated whole bodies and ran out of memory). -/
elab "fuel_jp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 2 do throwError "fuel_jp: not a Le goal"
    let x := args[args.size - 2]!
    let y := args[args.size - 1]!
    let unfoldHead (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
      let f := e.getAppFn
      unless f.isFVar do return none
      let some v := (← f.fvarId!.getDecl).value? | return none
      return some (mkAppN v e.getAppArgs).headBeta
    let x' ← unfoldHead x
    let y' ← unfoldHead y
    if x'.isNone && y'.isNone then throwError "fuel_jp: no let-bound head"
    let t' := mkAppN t.getAppFn ((args.set! (args.size - 2) (x'.getD x)).set! (args.size - 1) (y'.getD y))
    replaceMainGoal [← g.replaceTargetDefEq t']

open Lean Meta in
/-- A local whose type ends in the monad (`JSM H α`, possibly after arguments): a closure of a
body (join point, local helper, or a computation kept in a `let`), to pair across the two sides,
never generalised as data. -/
def isMonadicType (t : Lean.Expr) : MetaM Bool :=
  forallTelescope t fun _ b => pure (b.isAppOf ``JSM || b.isAppOf ``EStateM)

open Lean Meta Elab Tactic in
/-- `split` cannot case on a discriminant that is a let-bound local (after `extract_lets`, the
`do` block's own `let x := …` of data). Both sides share that local, so its value is not needed:
replace its uses in the goal by a fresh variable. Join points (locals of function type) are left
to `fuel_jp`. -/
elab "fuel_gen_lets" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let mut args : Array GeneralizeArg := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if d.value?.isNone then continue
      if (← whnfR d.type).isForall then continue
      if ← isMonadicType d.type then continue
      if t.containsFVar d.fvarId then
        args := args.push { expr := d.toExpr }
    if args.isEmpty then throwError "fuel_gen_lets: no let-bound data in the goal"
    let (_, g') ← g.generalize args
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- When `split` gives up on a match (a match whose arms are functions of the heap, after the
`do` elaborator pushed the state argument inside), case on its discriminants directly: they are
the same terms on both sides, so generalising them and casing gives both sides the same
constructor, and `dsimp only` then reduces both matches. -/
def fuelCasesCore (bigOnly : Bool) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 2 do throwError "fuel_cases: not a Le goal"
    let x := args[args.size - 2]!
    let env ← getEnv
    let some e := x.find? (fun e => (Lean.Meta.isMatcherAppCore? env e).isSome) | throwError "fuel_cases: no match"
    let some m ← matchMatcherApp? e | throwError "fuel_cases: no matcher app"
    if bigOnly then
      unless m.alts.size ≥ 24 do throwError "fuel_cases: small match"
      unless m.discrs.size ≥ 1 && m.discrs[0]!.isFVar do throwError "fuel_cases: not on a variable"
    -- only a discriminant that is not yet a constructor (else `dsimp only` reduces the match)
    -- a discriminant that is not a constructor yet; inside a constructor (`match (a, b) with`),
    -- its first argument that is not one
    let rec firstOpen (fuel : Nat) (d : Lean.Expr) : MetaM (Option Lean.Expr) := do
      if d.hasLooseBVars then return none
      -- never a string, character or machine number (literal patterns that cases cannot
      -- reach); a natural number is cased one successor at a time, which ends past the largest
      -- literal of the match (`dsimp only` then reduces it)
      let ty ← whnfR (← inferType d)
      if ty.isConstOf ``Int || ty.isConstOf ``String || ty.isConstOf ``Char
          || ty.isConstOf ``Float || ty.isConstOf ``UInt8 || ty.isConstOf ``UInt16
          || ty.isConstOf ``UInt32 || ty.isConstOf ``UInt64 then return none
      if !(← isConstructorApp d) then return some d
      match fuel with
      | 0 => return none
      | k + 1 =>
        for a in d.getAppArgs do
          if (← inferType a).isSort then continue
          if let some e ← firstOpen k a then return some e
        return none
    let mut pick : Option Lean.Expr := none
    for d in m.discrs do
      if let some e ← firstOpen 8 d then
        pick := some e
        break
    let some d := pick | throwError "fuel_cases: every discriminant is a constructor"
    let plainFVar ← if d.isFVar then pure (← d.fvarId!.getDecl).value?.isNone else pure false
    let (fv, g1) ← if plainFVar then pure (d.fvarId!, g)
      else do
        let (fvs, g1) ← g.generalize #[{ expr := d }]
        pure (fvs[0]!, g1)
    let subs ← g1.cases fv
    replaceMainGoal (subs.map (·.mvarId)).toList

open Lean Meta Elab Tactic in
elab "fuel_cases" : tactic => fuelCasesCore false

open Lean Meta Elab Tactic in
/-- `fuel_cases` only for a match of many alternatives on a variable (a built-in's `match id with`
over hundreds of natives), where `split` would first build the matcher's splitter: minutes for
hundreds of alternatives. -/
elab "fuel_cases_big" : tactic => fuelCasesCore true

open Lean Meta Elab Tactic in
/-- `Le x x`, when the two sides are the same term (no call in them, or calls already paired).
Structural equality of the terms, not unification: unification of two large bodies that differ
deep inside walked the whole term at every step of the walk (quadratic, gigabytes). -/
elab "fuel_refl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 4 do throwError "fuel_refl: not a Le goal"
    let x := args[args.size - 2]!
    let y := args[args.size - 1]!
    unless x == y do
      -- the two sides differ: worth a (reducible) unification only when they mention the same
      -- natural-number locals, i.e. no call at fuel `n` on one side against `m` on the other;
      -- else it fails anyway, after walking both terms (quadratic over a walk)
      let natFVars (e : Lean.Expr) : MetaM (Array FVarId) := do
        let fs := (Lean.collectFVars {} e).fvarIds
        fs.filterM fun f => do return (← whnfR (← f.getType)).isConstOf ``Nat
      let fx ← natFVars x
      let fy ← natFVars y
      unless fx.all (fy.contains ·) && fy.all (fx.contains ·) do throwError "fuel_refl: fuels differ"
      unless ← withReducible (isDefEq x y) do throwError "fuel_refl: sides differ"
    g.assign (mkAppN (mkConst ``Le.refl (t.getAppFn.constLevels!)) #[args[0]!, args[1]!, x])
    replaceMainGoal []

open Lean Meta Elab Tactic in
/-- Join points paired once. After `extract_lets` the context holds the let-bound closures of both
sides (`do` join points, local helpers): those the left side reaches and those the right side
reaches, in the same order, one pair per closure of the source. For each pair `(f, g)` a new goal
`∀ xs, Le (f xs) (g xs)` is made (proved by the walk, after `fuel_jp` puts the two bodies in
place, with the earlier pairs as hypotheses) and the main goal gets it as a hypothesis, which
`fuel_hyp` uses at every call. Proving each pair once, before the walk splits the main body,
keeps the proof linear: unfolding a join point at each use repeated its whole body in every
branch (`binop`: over 7 GB). -/
elab "fuel_jp_pairs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 4 do throwError "fuel_jp_pairs: not a Le goal"
    let lctx ← getLCtx
    -- function-typed let-bound locals, in context order
    let mut lets : Array LocalDecl := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      if d.value?.isNone then continue
      unless ← isMonadicType d.type do continue
      lets := lets.push d
    -- leave out the closures already paired (a hypothesis `∀ xs, Le (f xs) _` is in context)
    let mut paired : Array FVarId := #[]
    for d in lctx do
      let b := (← instantiateMVars d.type).getForallBody
      if b.isAppOf ``Le then
        let ba := b.getAppArgs
        if ba.size ≥ 4 then
          if ba[2]!.getAppFn.isFVar then paired := paired.push ba[2]!.getAppFn.fvarId!
          if ba[3]!.getAppFn.isFVar then paired := paired.push ba[3]!.getAppFn.fvarId!
    lets := lets.filter fun d => !paired.contains d.fvarId
    if lets.isEmpty then throwError "fuel_jp_pairs: no let-bound closures"
    -- the locals a term reaches, through the values of the lets it mentions
    let reach (e : Lean.Expr) : Array FVarId := Id.run do
      let mut seen : Array FVarId := #[]
      let mut todo : Array Lean.Expr := #[e]
      while !todo.isEmpty do
        let cur := todo.back!
        todo := todo.pop
        for d in lets do
          if cur.containsFVar d.fvarId && !seen.contains d.fvarId then
            seen := seen.push d.fvarId
            todo := todo.push d.value
      return seen
    let rx := reach args[2]!
    let ry := reach args[3]!
    let ls := lets.filter fun d => rx.contains d.fvarId && !ry.contains d.fvarId
    let rs := lets.filter fun d => ry.contains d.fvarId && !rx.contains d.fvarId
    unless ls.size == rs.size && ls.size > 0 do throwError "fuel_jp_pairs: unpaired closures"
    let mut main := g
    let mut side : Array MVarId := #[]
    for i in [0:ls.size] do
      let l := ls[i]!
      let r := rs[i]!
      let ty ← main.withContext do
        forallTelescope l.type fun xs _ => do
          let lhs := mkAppN l.toExpr xs
          let rhs := mkAppN r.toExpr xs
          let lt ← inferType lhs
          let rt ← inferType rhs
          unless ← isDefEq lt rt do throwError "fuel_jp_pairs: closure types differ"
          let le ← mkAppM ``Le #[lhs, rhs]
          mkForallFVars xs le
      let pf ← main.withContext (mkFreshExprSyntheticOpaqueMVar ty)
      side := side.push pf.mvarId!
      let m' ← main.assert (← mkFreshUserName `hjp) ty pf
      let (_, m'') ← m'.intro1P
      main := m''
    replaceMainGoal (side.toList ++ [main])

open Lean Meta Elab Tactic in
/-- Close `Le (f a…) (g a…)` by a hypothesis `∀ xs, Le (f xs) (g xs)` (from `fuel_jp_pairs`). -/
elab "fuel_hyp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 4 do throwError "fuel_hyp: not a Le goal"
    let x0 := args[2]!
    -- a built-in's call into the evaluator, `core.f a…` (`CoreFn.f`, reducible), is `core (.f a…)`
    let x ← if x0.getAppFn.isFVar then pure x0 else whnfR x0
    unless x.getAppFn.isFVar do throwError "fuel_hyp: no local head"
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.getForallBody.isAppOf ``Le do continue
      let body := ty.getForallBody
      let bargs := body.getAppArgs
      unless bargs.size ≥ 4 && bargs[2]!.getAppFn == x.getAppFn do continue
      let xs := x.getAppArgs
      unless xs.size == ty.getForallArity do continue
      let pf := mkAppN d.toExpr xs
      -- default transparency: a built-in's request answers in `CoreOp.Res op`, which reduces
      -- to the type the call site has
      if ← isDefEq (← inferType pf) t then
        g.assign pf
        replaceMainGoal []
        return
    throwError "fuel_hyp: no hypothesis"

open Lean Meta Elab Tactic in
/-- Close `Le (f n a…) (f m a…)`, `f` a function of the evaluator's block, by the field `h_f` of the
induction hypothesis `ih : IH H n m` (`JS/FuelMonoSteps.lean`), built directly: no elaboration
of a term per candidate field. -/
elab "fuel_call" ih:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 4 do throwError "fuel_call: not a Le goal"
    let x := args[2]!
    let some fName := x.getAppFn.constName? | throwError "fuel_call: no constant head"
    let last := match fName with | .str _ s => s | _ => ""
    let field := Name.mkStr `L4Factoidal.JS.FuelMono.IH ("h_" ++ last)
    unless (← getEnv).contains field do throwError "fuel_call: {fName} is not in the block"
    let ihE ← getFVarFromUserName ih.getId
    let ihT ← whnfR (← inferType ihE)
    -- x = f (H := H) n a0 … ak
    let xs := x.getAppArgs
    unless xs.size ≥ 2 do throwError "fuel_call: no arguments"
    let pf := mkAppN (mkAppN (mkConst field) ihT.getAppArgs) (#[ihE] ++ xs.extract 2 xs.size)
    -- default transparency: in `coreRun` the answer's type is `CoreOp.Res op`, which reduces to
    -- the function's result type
    if ← isDefEq (← inferType pf) t then
      g.assign pf
      replaceMainGoal []
    else throwError "fuel_call: field does not fit"

open Lean Meta Elab Tactic in
/-- Run a step with its own heartbeat budget (in thousands, as `maxHeartbeats`); past it the step
fails as an ordinary error, so the walk's `first` goes on to the next rule. (A heartbeat timeout
is a runtime exception, which `first` does not catch.) -/
elab "fuel_capped " n:num t:tactic : tactic => do
  let st ← saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := n.getNat * 1000 }) <|
      withCurrHeartbeats (evalTactic t))
    (fun _ => do
      st.restore
      throwError "fuel_capped: over budget")

open Lean Meta Elab Tactic in
/-- A match whose discriminants are constructors now (after `fuel_cases`), on both sides: take
the alternative by the matcher's own reduction, without `dsimp`, which walks the whole term (a
built-in's `match id with` has hundreds of alternatives, and is reduced once per built-in). -/
elab "fuel_match_reduce" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.isAppOf ``Le && args.size ≥ 4 do throwError "fuel_match_reduce: not a Le goal"
    let red (e : Lean.Expr) : MetaM Lean.Expr := do
      -- default transparency for the discriminants: a literal pattern over a natural number
      -- (`iterEager 3`) is decided by `Nat.decEq`, which reducible transparency does not open
      match ← withTransparency .default (reduceMatcher? e) with
      | ReduceMatcherResult.reduced e2 => return e2.headBeta
      | _ => throwError "fuel_match_reduce: no reducible match"
    let x' ← red args[2]!
    let y' ← red args[3]!
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN t.getAppFn ((args.set! 2 x').set! 3 y'))]

syntax "fuel_mono_pre" : tactic
macro_rules
  | `(tactic| fuel_mono_pre) => `(tactic| first
      | with_reducible (cases ‹_ + 1 = Nat.succ _›)
      | fuel_refl
      | with_reducible exact Le.fuel _
      | with_reducible apply Le.bind
      | with_reducible apply Le.catchJS
      | with_reducible apply Le.tryCatch
      | (show Out _; set_option maxHeartbeats 400000 in exact ⟨_, rfl⟩))

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
      | with_reducible apply Le.filterM_array
      | with_reducible apply Le.inRealm
      | with_reducible apply Le.filterMapM_array
      | with_reducible apply Le.map
      | apply Le.discard
      | (intro _)
      | (lift_lets; extract_lets; try fuel_jp_pairs)
      | fuel_hyp
      | with_reducible apply natives_iterEach_mono
      | with_reducible apply natives_moreNative_mono
      | with_reducible apply natives_extraNative_mono
      | with_reducible apply natives_callNative_mono
      | fuel_jp
      | fuel_match_reduce
      | with_reducible apply Le.ite
      | with_reducible apply Le.dite
      | fuel_capped 3000 split
      | fuel_cases_big
      | fuel_capped 1000 (dsimp (config := { zeta := false }) only)
      | fuel_gen_lets
      | fuel_cases
      | fuel_capped 1000 dsimp only
      | (apply Le.of_out; intro _; set_option maxHeartbeats 400000 in exact ⟨_, rfl⟩)
      -- last: `split` with a large budget, for a big match no other rule takes (a literal
      -- pattern over a natural number that is past every literal)
      | fuel_capped 60000 split)


open Lean Meta Elab Tactic in
/-- The walk: `fuel_mono_pre`, then `fuel_call ih` (when an induction hypothesis is named), then
`fuel_mono_post`, on every goal and the goals each step makes, until none applies (as
`repeat'`). It runs with info trees off: the elaborator otherwise keeps the goals of every one of
the thousands of steps for an editor to show, which took gigabytes on the large bodies
(`extraNative`: 2.2 GB after 4,000 steps with them, 0.4 GB without). -/
elab "fuel_walk" ih:(ppSpace ident)? : tactic => withEnableInfoTree false do
  let pre ← `(tactic| fuel_mono_pre)
  let post ← `(tactic| fuel_mono_post)
  let call? ← match ih with
    | some i => some <$> `(tactic| fuel_call $i)
    | none => pure none
  let tacs := #[pre] ++ (match call? with | some c => #[c] | none => #[]) ++ #[post]
  let mut todo := (← getGoals)
  let mut left : Array MVarId := #[]
  while true do
    match todo with
    | [] => break
    | g :: rest =>
      if ← g.isAssigned then
        todo := rest
        continue
      let mut next : Option (List MVarId) := none
      for tac in tacs do
        if next.isSome then continue
        setGoals [g]
        try
          evalTactic tac
          next := some (← getGoals)
        catch _ => pure ()
      match next with
      | some gs => todo := gs ++ rest
      | none =>
        left := left.push g
        todo := rest
  setGoals left.toList

/-- A call that runs in another realm (`inRealm`: switch, run, switch back on a throw too). -/
theorem Le.inRealm (k : Nat) {x1 x2 : JSM H α} (hx : Le x1 x2) :
    Le (L4Factoidal.JS.inRealm k x1) (L4Factoidal.JS.inRealm k x2) := by
  unfold L4Factoidal.JS.inRealm
  fuel_walk

end L4Factoidal.JS.FuelMono
