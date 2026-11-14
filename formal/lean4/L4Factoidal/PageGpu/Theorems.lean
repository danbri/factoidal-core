/-
L4Factoidal.PageGpu.Theorems: what Lean proves about page GPU commands
(record: docs/designissues/2026-11-08-page-gpu.md, section 4).

- `compile_inSubset`, `compile_cost`, `compile_loops`: a shader that reaches the host is
  in the subset, each entry point's static cost is at most `maxCost`, and every `for`
  loop runs at most `maxLoop` times and does not assign its counter.
- `compile_clamped`: every index of a shader that reaches the host is
  `base[min(u32(i), (n-1)u)]` with `n` the declared length of `base`.
- `step_safe` and its unpackings: `write_in_bounds`, `draw_in_bounds`, `buffer_usage`,
  `canvas_usage`, `refs_owned`.
- `step_createBuffer_clears`: a new buffer is zeroed before anything can read it.
- `run_inv`: the quotas hold across any command sequence.
-/
import L4Factoidal.PageGpu.Model

namespace L4Factoidal.PageGpu
open Wgsl

/-! ## The WGSL subset -/

/-- The subset, stated over every node of the module. -/
structure InSubset (m : Module) : Prop where
  structs : m.structs.length ≤ maxStructs
  fns : m.fns.length ≤ maxFns
  exprs : ∀ e ∈ m.exprs, exprNodeOk (m.structs.map (·.name)) e = true
  stmts : ∀ s ∈ m.stmts, stmtNodeOk (m.structs.map (·.name)) s = true
  cost : ∀ f ∈ m.fns, f.body.cost ≤ maxCost
  /-- Compute entry points have a workgroup of at most `maxInvocations` invocations. -/
  workgroup : ∀ f ∈ m.fns, wgOk f = true
  /-- Storage variables are of the subset; bindings are distinct and below `maxBindings`. -/
  bindings : bindingsOk (m.structs.map (·.name)) m = true

theorem validate_sound (m : Module) (h : validate m = true) : InSubset m := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hf⟩, _⟩, _⟩, hb⟩, _⟩, hfns⟩, hst⟩, hex⟩, _⟩ := h
  refine ⟨hs, hf, hex, hst, ?_, ?_, hb⟩
  · intro f hmem
    have := hfns f hmem
    simp only [fnOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · intro f hmem
    have := hfns f hmem
    simp only [fnOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.2

theorem finish_spec {m h : Module} (hf : finish m = .ok h) : harden m = some h ∧ validate h = true := by
  unfold finish at hf
  by_cases hv : validate m = true
  · rw [if_pos hv] at hf
    cases hh : harden m with
    | none => rw [hh] at hf; cases hf
    | some h' =>
      rw [hh] at hf
      simp only at hf
      by_cases hv' : validate h' = true
      · rw [if_pos hv'] at hf; cases hf; exact ⟨rfl, hv'⟩
      · rw [if_neg hv'] at hf; cases hf
  · rw [if_neg hv] at hf; cases hf

theorem compile_finish {src : String} {h : Module} (hc : compile src = .ok h) : ∃ m, finish m = .ok h := by
  unfold compile at hc
  simp only [bind, Except.bind] at hc
  split at hc
  · cases hc
  · rename_i m _; exact ⟨m, hc⟩

theorem compile_validated {src : String} {h : Module} (hc : compile src = .ok h) : validate h = true := by
  obtain ⟨m, hm⟩ := compile_finish hc
  exact (finish_spec hm).2

/-- A shader the host receives is in the subset. -/
theorem compile_inSubset {src : String} {h : Module} (hc : compile src = .ok h) : InSubset h :=
  validate_sound h (compile_validated hc)

/-- Termination: each entry point of a shader the host receives has static cost at most
`maxCost` (no recursion, no user calls, literal-bounded loops). -/
theorem compile_cost {src : String} {h : Module} (hc : compile src = .ok h) :
    ∀ f ∈ h.fns, f.body.cost ≤ maxCost :=
  (compile_inSubset hc).cost

/-- Every `for` loop of a shader the host receives runs at most `maxLoop` times and its
body never assigns its counter. -/
theorem compile_loops {src : String} {h : Module} (hc : compile src = .ok h)
    {v : String} {ty : Scalar} {lo hi : Nat} {incl : Bool} {b : Stmts}
    (hs : Stmt.forS v ty lo hi incl b ∈ h.stmts) :
    trips lo hi incl ≤ maxLoop ∧ ∀ t ∈ b.nodes, ∀ l op e, t = .assign l op e → l.root ≠ some v := by
  have := (compile_inSubset hc).stmts _ hs
  simp only [stmtNodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
  obtain ⟨⟨⟨_, ht⟩, _⟩, hb⟩ := this
  refine ⟨ht, ?_⟩
  intro t ht' l op e he
  have := hb t ht'
  subst he
  simpa using this

/-- Every `for` loop capped by `min(e, C)` in a shader the host receives runs at most
`maxCapLoop` times (its counter starts at `lo`, rises by one each iteration, is never
assigned in the body, and stops below `cap`). -/
theorem compile_capLoops {src : String} {h : Module} (hc : compile src = .ok h)
    {v : String} {ty : Scalar} {lo cap : Nat} {e : Expr} {b : Stmts}
    (hs : Stmt.forCap v ty lo e cap b ∈ h.stmts) :
    trips lo cap false ≤ maxCapLoop ∧ ∀ t ∈ b.nodes, ∀ l op e, t = .assign l op e → l.root ≠ some v := by
  have := (compile_inSubset hc).stmts _ hs
  simp only [stmtNodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
  obtain ⟨⟨⟨_, ht⟩, _⟩, hb⟩ := this
  refine ⟨ht, ?_⟩
  intro t ht' l op e he
  have := hb t ht'
  subst he
  simpa using this

/-- Each compute entry point of a shader the host receives has a workgroup of at most
`maxInvocations` invocations. -/
theorem compile_workgroup {src : String} {h : Module} (hc : compile src = .ok h)
    {f : Fn} (hf : f ∈ h.fns) (hs : f.stage = .compute) :
    0 < f.workgroup.1 ∧ 0 < f.workgroup.2.1 ∧ 0 < f.workgroup.2.2 ∧
    f.workgroup.1 * f.workgroup.2.1 * f.workgroup.2.2 ≤ maxInvocations := by
  have := (compile_inSubset hc).workgroup f hf
  simp only [wgOk, hs, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2⟩

/-! ## Index clamping -/

mutual
/-- Every index of `e` is `base[min(u32(j), k u)]` with `k + 1` the length of `base`'s
type in scope `env`. -/
def clampedE (structs : List StructDecl) (env : Env) : Expr → Bool
  | .lit _ | .name _ => true
  | .unary _ a => clampedE structs env a
  | .binary _ a b => clampedE structs env a && clampedE structs env b
  | .call _ as => clampedA structs env as
  | .member a _ => clampedE structs env a
  | .index a i =>
    match i with
    | .call (.fn "min") (.cons (.call (.ty (.scalar .u32)) (.cons j .nil)) (.cons (.lit (.int k "u")) .nil)) =>
      (tyOf structs env a).bind Ty.len == some (k + 1) && clampedE structs env a && clampedE structs env j
    -- a runtime-sized array, through its own name: `a[min(u32(j), arrayLength(&a) - 1u)]`
    | .call (.fn "min") (.cons (.call (.ty (.scalar .u32)) (.cons j .nil))
        (.cons (.binary "-" (.call (.fn "arrayLength") (.cons (.name v) .nil)) (.lit (.int 1 "u"))) .nil)) =>
      (match a with | .name w => w == v | _ => false) && (tyOf structs env a).bind Ty.len == some 0 &&
        clampedE structs env j
    | _ => false

def clampedA (structs : List StructDecl) (env : Env) : Args → Bool
  | .nil => true
  | .cons e rest => clampedE structs env e && clampedA structs env rest
end

/-- What `clampAt` builds: an index of the hardened base, clamped to the literal length,
or, for a runtime-sized array, through its name to `arrayLength`. -/
theorem clampAt_spec {a' i' e' : Expr} {n : Nat} (h : clampAt a' i' n = some e') :
    (n ≠ 0 ∧ e' = .index a' (clampIdx i' n)) ∨ (n = 0 ∧ ∃ v, a' = .name v ∧ e' = .index a' (clampRt i' v)) := by
  unfold clampAt at h
  split at h
  · rename_i hn
    split at h
    · rename_i v; cases h; exact .inr ⟨hn, v, rfl, rfl⟩
    · cases h
  · rename_i hn; cases h; exact .inl ⟨hn, rfl⟩

mutual
theorem hardenE_tyOf (structs : List StructDecl) (env : Env) :
    ∀ (e e' : Expr), hardenE structs env e = some e' → tyOf structs env e' = tyOf structs env e
  | .lit l, e', h => by simp [hardenE] at h; subst h; rfl
  | .name n, e', h => by simp [hardenE] at h; subst h; rfl
  | .unary op a, e', h => by
    simp only [hardenE, Option.map_eq_some_iff] at h
    obtain ⟨a', _, rfl⟩ := h; rfl
  | .binary op a b, e', h => by
    simp only [hardenE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | .call f as, e', h => by
    simp only [hardenE, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; cases f <;> rfl
  | .member a f, e', h => by
    simp only [hardenE, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp only [tyOf]; rw [hardenE_tyOf structs env a a' ha]
  | .index a i, e', h => by
    simp only [hardenE] at h
    split at h
    · next n a' i' hn ha hi =>
      rcases clampAt_spec h with ⟨_, rfl⟩ | ⟨_, v, _, rfl⟩ <;>
        (simp only [tyOf]; rw [hardenE_tyOf structs env a a' ha])
    · cases h
end

mutual
theorem hardenE_clamped (structs : List StructDecl) (env : Env) :
    ∀ (e e' : Expr), hardenE structs env e = some e' → clampedE structs env e' = true
  | .lit l, e', h => by simp [hardenE] at h; subst h; simp [clampedE]
  | .name n, e', h => by simp [hardenE] at h; subst h; simp [clampedE]
  | .unary op a, e', h => by
    simp only [hardenE, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp only [clampedE]; exact hardenE_clamped structs env a a' ha
  | .binary op a b, e', h => by
    simp only [hardenE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [clampedE, Bool.and_eq_true]
    exact ⟨hardenE_clamped structs env a a' ha, hardenE_clamped structs env b b' hb⟩
  | .call f as, e', h => by
    simp only [hardenE, Option.map_eq_some_iff] at h
    obtain ⟨as', has, rfl⟩ := h
    simp only [clampedE]; exact hardenA_clamped structs env as as' has
  | .member a f, e', h => by
    simp only [hardenE, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp only [clampedE]; exact hardenE_clamped structs env a a' ha
  | .index a i, e', h => by
    simp only [hardenE] at h
    split at h
    · next n a' i' hn ha hi =>
      rcases clampAt_spec h with ⟨hn0, rfl⟩ | ⟨hn0, v, hv, rfl⟩
      · simp only [clampedE, clampIdx, Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨?_, hardenE_clamped structs env a a' ha⟩, hardenE_clamped structs env i i' hi⟩
        rw [hardenE_tyOf structs env a a' ha, hn]
        congr 1; omega
      · subst hv
        simp only [clampedE, clampRt, lastRt, Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨by simp, ?_⟩, hardenE_clamped structs env i i' hi⟩
        rw [hardenE_tyOf structs env a _ ha, hn, hn0]
    · cases h

theorem hardenA_clamped (structs : List StructDecl) (env : Env) :
    ∀ (as as' : Args), hardenA structs env as = some as' → clampedA structs env as' = true
  | .nil, as', h => by simp [hardenA] at h; subst h; simp [clampedA]
  | .cons e rest, as', h => by
    simp only [hardenA, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨e', he, r', hr, rfl⟩ := h
    simp only [clampedA, Bool.and_eq_true]
    exact ⟨hardenE_clamped structs env e e' he, hardenA_clamped structs env rest r' hr⟩
end

theorem hardenO_clamped (structs : List StructDecl) (env : Env) (e : Option Expr) (e' : Option Expr)
    (h : hardenO structs env e = some e') : ∀ x ∈ e', clampedE structs env x = true := by
  cases e with
  | none => simp [hardenO] at h; subst h; simp
  | some x =>
    simp only [hardenO, Option.map_eq_some_iff] at h
    obtain ⟨x', hx, rfl⟩ := h
    intro y hy; cases hy; exact hardenE_clamped structs env x x' hx

theorem hardenO_tyOf (structs : List StructDecl) (env : Env) (e : Option Expr) (e' : Option Expr)
    (h : hardenO structs env e = some e') : e'.bind (tyOf structs env) = e.bind (tyOf structs env) := by
  cases e with
  | none => simp [hardenO] at h; subst h; rfl
  | some x =>
    simp only [hardenO, Option.map_eq_some_iff] at h
    obtain ⟨x', hx, rfl⟩ := h
    simp [hardenE_tyOf structs env x x' hx]

theorem hardenS_bindOf (structs : List StructDecl) (env : Env) (s s' : Stmt)
    (h : hardenS structs env s = some s') : Wgsl.bindOf structs env s' = Wgsl.bindOf structs env s := by
  cases s with
  | letS n t e =>
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨e', he, rfl⟩ := h
    simp only [Wgsl.bindOf]; rw [hardenE_tyOf structs env e e' he]
  | varS n t e =>
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨e', he, rfl⟩ := h
    simp only [Wgsl.bindOf]; rw [hardenO_tyOf structs env e e' he]
  | assign l op e =>
    simp only [hardenS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | ret e =>
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  | ifS c t f =>
    simp only [hardenS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, _, rfl⟩ := h; rfl
  | forS v ty lo hi incl b =>
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  | forCap v ty lo e cap b =>
    simp only [hardenS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | block b =>
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; rfl

mutual
/-- Every index of every expression of `s` is clamped, in the scope the statement sees. -/
def clampedS (structs : List StructDecl) (env : Env) : Stmt → Bool
  | .letS _ _ e => clampedE structs env e
  | .varS _ _ e => e.all (clampedE structs env)
  | .assign l _ e => clampedE structs env l && clampedE structs env e
  | .ret e => e.all (clampedE structs env)
  | .ifS c t f => clampedE structs env c && clampedSs structs env t && clampedSs structs env f
  | .forS v ty _ _ _ b => clampedSs structs ((v, .scalar ty) :: env) b
  | .forCap v ty _ e _ b => clampedE structs ((v, .scalar ty) :: env) e && clampedSs structs ((v, .scalar ty) :: env) b
  | .block b => clampedSs structs env b

def clampedSs (structs : List StructDecl) (env : Env) : Stmts → Bool
  | .nil => true
  | .cons s rest => clampedS structs env s && clampedSs structs (Wgsl.bindOf structs env s) rest
end

mutual
theorem hardenS_clamped (structs : List StructDecl) (env : Env) :
    ∀ (s s' : Stmt), hardenS structs env s = some s' → clampedS structs env s' = true
  | .letS n t e, s', h => by
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨e', he, rfl⟩ := h
    exact hardenE_clamped structs env e e' he
  | .varS n t e, s', h => by
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨e', he, rfl⟩ := h
    simp only [clampedS, Option.all_eq_true]
    exact hardenO_clamped structs env e e' he
  | .assign l op e, s', h => by
    simp only [hardenS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨l', hl, e', he, rfl⟩ := h
    simp only [clampedS, Bool.and_eq_true]
    exact ⟨hardenE_clamped structs env l l' hl, hardenE_clamped structs env e e' he⟩
  | .ret e, s', h => by
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨e', he, rfl⟩ := h
    simp only [clampedS, Option.all_eq_true]
    exact hardenO_clamped structs env e e' he
  | .ifS c t f, s', h => by
    simp only [hardenS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c', hc, t', ht, f', hf, rfl⟩ := h
    simp only [clampedS, Bool.and_eq_true]
    exact ⟨⟨hardenE_clamped structs env c c' hc, hardenSs_clamped structs env t t' ht⟩,
      hardenSs_clamped structs env f f' hf⟩
  | .forS v ty lo hi incl b, s', h => by
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    exact hardenSs_clamped structs _ b b' hb
  | .forCap v ty lo e cap b, s', h => by
    simp only [hardenS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨e', he, b', hb, rfl⟩ := h
    simp only [clampedS, Bool.and_eq_true]
    exact ⟨hardenE_clamped structs _ e e' he, hardenSs_clamped structs _ b b' hb⟩
  | .block b, s', h => by
    simp only [hardenS, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    exact hardenSs_clamped structs env b b' hb

theorem hardenSs_clamped (structs : List StructDecl) (env : Env) :
    ∀ (ss ss' : Stmts), hardenSs structs env ss = some ss' → clampedSs structs env ss' = true
  | .nil, ss', h => by simp [hardenSs] at h; subst h; simp [clampedSs]
  | .cons s rest, ss', h => by
    simp only [hardenSs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨s', hs, r', hr, rfl⟩ := h
    simp only [clampedSs, Bool.and_eq_true]
    refine ⟨hardenS_clamped structs env s s' hs, ?_⟩
    rw [hardenS_bindOf structs env s s' hs]
    exact hardenSs_clamped structs _ rest r' hr
end

theorem optMap_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, optMap f xs = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by simp [optMap] at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [optMap, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    intro z hz
    cases hz with
    | head => exact ⟨x, .head _, hy⟩
    | tail _ hz =>
      obtain ⟨w, hw, hf⟩ := optMap_mem hys z hz
      exact ⟨w, .tail _ hw, hf⟩

/-- Hardening: every function of the result is a function of the source with the same
parameters, and every index in its body is clamped to the declared length of its base. -/
theorem harden_clamped {m h : Module} (hh : harden m = some h) :
    h.structs = m.structs ∧ h.uniform = m.uniform ∧
    ∀ f' ∈ h.fns, ∃ f ∈ m.fns, f'.params = f.params ∧ f'.stage = f.stage ∧
      clampedSs m.structs (fnEnv m f) f'.body = true := by
  simp only [harden, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hh
  obtain ⟨fns, hf, consts, _, rfl⟩ := hh
  refine ⟨rfl, rfl, ?_⟩
  intro f' hmem
  obtain ⟨f, hfm, hfe⟩ := optMap_mem hf f' hmem
  simp only [hardenFn, Option.map_eq_some_iff] at hfe
  obtain ⟨b, hb, rfl⟩ := hfe
  exact ⟨f, hfm, rfl, rfl, hardenSs_clamped _ _ _ _ hb⟩

/-- A WebGL program the host receives (`Glsl.compileProgram`, a `createProgram` command)
is in the subset, with every index clamped: it is the `finish` of its translation. -/
theorem program_finish {vs fs : String} {h : Module} {i : Glsl.Info}
    (hc : Glsl.compileProgram vs fs = .ok (h, i)) : ∃ m, finish m = .ok h := by
  unfold Glsl.compileProgram at hc
  simp only [bind, Except.bind] at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc
      · rename_i p _
        split at hc
        · cases hc
        · rename_i h' hf
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, _⟩ := hc
          exact ⟨_, hf⟩

theorem program_inSubset {vs fs : String} {h : Module} {i : Glsl.Info}
    (hc : Glsl.compileProgram vs fs = .ok (h, i)) : InSubset h ∧ ∃ m, harden m = some h := by
  obtain ⟨m, hm⟩ := program_finish hc
  exact ⟨validate_sound h (finish_spec hm).2, m, (finish_spec hm).1⟩

/-- A shader the host receives has every index clamped (`clampedE`): it is the
hardening of a parsed, validated module. -/
theorem compile_clamped {src : String} {h : Module} (hc : compile src = .ok h) :
    ∃ m, harden m = some h := by
  obtain ⟨m, hm⟩ := compile_finish hc
  exact ⟨m, (finish_spec hm).1⟩

/-! ## Commands -/

/-- What an accepted `step` did: the plan, every emitted command passing the final check,
the frame's work within `maxFrameWork`, the change applied, and the work counted. -/
theorem step_ok {s s' : State} {c : Command} {out : List HostCmd}
    (h : step s c = .ok (s', out)) :
    ∃ ch s'', plan s c = .ok (ch, out) ∧ (∀ x ∈ out, x.safe s = true) ∧
      s.work + workOf out ≤ maxFrameWork ∧ apply s ch = .ok s'' ∧
      s' = { s'' with work := s.work + workOf out } := by
  simp only [step, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    obtain ⟨ch, o⟩ := p
    split at h
    · cases h
    · rename_i hall
      split at h
      · cases h
      · rename_i hw
        split at h
        · cases h
        · rename_i s'' ha
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hall
          rw [List.all_eq_true] at hall
          exact ⟨ch, s'', hp, hall, by simp only at hw; omega, ha, rfl⟩

theorem step_safe {s s' : State} {c : Command} {out : List HostCmd}
    (h : step s c = .ok (s', out)) : ∀ x ∈ out, x.safe s = true := by
  obtain ⟨_, _, _, hall, _⟩ := step_ok h
  exact hall

/-- A page `writeBuffer` reaches the host only inside the buffer. -/
theorem write_in_bounds {s : State} {g : Gid} {offset : Nat} {data : ByteArray}
    (h : (HostCmd.writeBuffer g offset data).safe s = true) :
    g.page = s.page ∧ ∃ size usage, bufferOf s g.id = some (size, usage) ∧ offset + data.size ≤ size := by
  simp only [HostCmd.safe, owned, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hp, _⟩, _⟩, _⟩, hb⟩ := h
  refine ⟨hp, ?_⟩
  split at hb
  · rename_i size usage hbuf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨size, usage, hbuf, hb.2⟩
  · cases hb

/-- Every vertex buffer a draw uses holds every byte the draw reads. -/
theorem draw_in_bounds {s : State} {d : HostDraw} (h : drawSafe s d = true) :
    d.pipeline.page = s.page ∧ d.count * d.instances ≤ maxVertices ∧
    ∃ layouts u, pipelineOf s d.pipeline.id = some (layouts, u) ∧
      ∀ p ∈ layouts.zip d.vbufs, p.2.page = s.page ∧
        ∃ size usage, bufferOf s p.2.id = some (size, usage) ∧ vertexNeed p.1 d.first d.count ≤ size := by
  simp only [drawSafe, owned, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, _⟩, hv⟩, hrest⟩ := h
  refine ⟨hp, hv, ?_⟩
  split at hrest
  · cases hrest
  · rename_i layouts u hpl
    refine ⟨layouts, u, hpl, ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true] at hrest
    obtain ⟨⟨_, hz⟩, _⟩ := hrest
    intro p hpmem
    have := hz p hpmem
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨hpg, _⟩, hb⟩ := this
    refine ⟨hpg, ?_⟩
    split at hb
    · rename_i size usage hbuf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨size, usage, hbuf, hb.2⟩
    · cases hb

/-- A page buffer never gets `MAP_WRITE`, `INDEX`, `INDIRECT` or `QUERY_RESOLVE`; a
buffer that can be read back (`MAP_READ`) is `MAP_READ | COPY_DST` and nothing else, so
it is never bound, drawn from or copied out of on the GPU. -/
theorem buffer_usage {s : State} {g : Gid} {size usage : Nat}
    (h : (HostCmd.createBuffer g size usage).safe s = true) :
    usage &&& forbiddenUsage = 0 ∧ (usage &&& usageMapRead = 0 ∨ usage = usageMapRead ||| usageCopyDst) ∧
      size ≤ maxBuffer := by
  simp only [HostCmd.safe, usageOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, ⟨⟨hf, _⟩, hm⟩⟩, hz⟩, _⟩ := h
  exact ⟨hf, hm, hz⟩

/-- A page canvas texture is a render target that Lean samples; nothing can copy it out. -/
theorem canvas_usage {s : State} {g : Gid} {node w h usage : Nat}
    (hs : (HostCmd.createCanvas g node w h usage).safe s = true) :
    usage = canvasUsage ∧ w ≤ maxCanvas ∧ h ≤ maxCanvas := by
  simp only [HostCmd.safe, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  exact ⟨hs.1.1.1.1.2, hs.1.1.2, hs.2⟩

/-- Every pass draws on a canvas of this page, and every draw is in bounds. -/
theorem pass_owned {s : State} {c : Gid} {clear : Rgba} {draws : List HostDraw}
    (h : (HostCmd.pass c clear draws).safe s = true) :
    c.page = s.page ∧ isCanvas s c.id = true ∧ draws.length ≤ maxDraws ∧ ∀ d ∈ draws, drawSafe s d = true := by
  simp only [HostCmd.safe, owned, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- `createBuffer` emits the buffer and its clear, nothing else. -/
theorem plan_createBuffer_clears {s : State} {id size usage : Nat} {ch : Change} {out : List HostCmd}
    (h : plan s (.createBuffer id size usage) = .ok (ch, out)) :
    ∃ g z u, out = [.createBuffer g z u, .clearBuffer g z] := by
  simp only [plan, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact ⟨_, _, _, rfl⟩

theorem step_createBuffer_clears {s s' : State} {id size usage : Nat} {out : List HostCmd}
    (h : step s (.createBuffer id size usage) = .ok (s', out)) :
    ∃ g z u, out = [.createBuffer g z u, .clearBuffer g z] := by
  obtain ⟨_, _, hp, _⟩ := step_ok h
  exact plan_createBuffer_clears hp

/-! ## Compute (record section 6a) -/

/-- A bound buffer of a compute bind group is this page's, has the usage its binding's
space needs, is bound whole, and holds at least the binding's least size. -/
theorem bindEntry_bounds {s : State} {needs : List BindingNeed} {e : Nat × Gid × Nat}
    (h : bindEntryOk s needs e = true) :
    e.2.1.page = s.page ∧ ∃ n size usage, needs.find? (·.binding == e.1) = some n ∧
      bufferOf s e.2.1.id = some (size, usage) ∧ usage &&& spaceUsage n.space ≠ 0 ∧
      n.minSize ≤ size ∧ e.2.2 = size := by
  simp only [bindEntryOk, owned, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hp, _⟩, hb⟩ := h
  refine ⟨hp, ?_⟩
  split at hb
  · rename_i n size usage hn hbuf
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at hb
    exact ⟨n, size, usage, hn, hbuf, hb.1.1, hb.1.2, hb.2⟩
  · cases hb

/-- A compute bind group's entries are exactly the pipeline's bindings, no buffer twice,
each a buffer of this page as `bindEntry_bounds` says. -/
theorem entries_bounds {s : State} {needs : List BindingNeed} {es : List (Nat × Gid × Nat)}
    (h : entriesOk s needs es = true) :
    es.map (·.1) = needs.map (·.binding) ∧ (es.map (·.2.1.id)).Nodup ∧ ∀ e ∈ es, bindEntryOk s needs e = true := by
  simp only [entriesOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A compute bind group is made only for this page's compute pipeline, from this page's
buffers. -/
theorem computeBind_owned {s : State} {g p : Gid} {es : List (Nat × Gid × Nat)}
    (h : (HostCmd.createComputeBind g p es).safe s = true) :
    g.page = s.page ∧ p.page = s.page ∧ ∃ inv cost needs, computePipelineOf s p.id = some (inv, cost, needs) ∧
      entriesOk s needs es = true := by
  simp only [HostCmd.safe, fresh, owned, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hg, _⟩, hp, _⟩, hr⟩ := h
  refine ⟨hg, hp, ?_⟩
  split at hr
  · rename_i inv cost needs hc; exact ⟨inv, cost, needs, hc, hr⟩
  · cases hr

/-- One dispatch the host receives: its pipeline is this page's compute pipeline, with a
workgroup of at most `maxInvocations` invocations and an entry point of static cost at
most `maxCost`; at most `maxWorkgroups` workgroups in each dimension; its counted work is
workgroups × invocations × cost; and it binds only this page's bind group of that
pipeline, whose buffers are this page's (`entriesOk`), each holding at least its
binding's least size, which is positive (a runtime-sized array has at least one
element, so `arrayLength(&a) - 1u` does not wrap). -/
theorem dispatch_bounds {s : State} {d : HostDispatch} (h : dispatchSafe s d = true) :
    d.pipeline.page = s.page ∧ d.x ≤ maxWorkgroups ∧ d.y ≤ maxWorkgroups ∧ d.z ≤ maxWorkgroups ∧
    ∃ inv cost needs, computePipelineOf s d.pipeline.id = some (inv, cost, needs) ∧
      inv ≤ maxInvocations ∧ cost ≤ maxCost ∧ d.work = d.x * d.y * d.z * inv * cost ∧
      (∀ n ∈ needs, 0 < n.minSize) ∧
      ((needs = [] ∧ d.bind = none) ∨ ∃ b p es, d.bind = some b ∧ b.page = s.page ∧
        computeBindOf s b.id = some (p, es) ∧ p = d.pipeline.id ∧ entriesOk s needs (hostEntries s es) = true) := by
  simp only [dispatchSafe, owned, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hp, _⟩, hx⟩, hy⟩, hz⟩, hr⟩ := h
  refine ⟨hp, hx, hy, hz, ?_⟩
  split at hr
  · cases hr
  · rename_i inv cost needs hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hr
    obtain ⟨⟨⟨⟨hi, hco⟩, hw⟩, hpos⟩, hb⟩ := hr
    refine ⟨inv, cost, needs, hc, hi, hco, hw, hpos, ?_⟩
    split at hb
    · exact .inl ⟨rfl, by assumption⟩
    · rename_i b hbind
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨hbp, _⟩, hb2⟩ := hb
      split at hb2
      · rename_i p es hcb
        simp only [Bool.and_eq_true, beq_iff_eq] at hb2
        exact .inr ⟨b, p, es, hbind, hbp, hcb, hb2.1, hb2.2⟩
      · cases hb2
    · cases hb

/-- A compute pass has at most `maxDispatches` dispatches, each as `dispatch_bounds` says. -/
theorem computePass_owned {s : State} {ds : List HostDispatch}
    (h : (HostCmd.computePass ds).safe s = true) :
    ds.length ≤ maxDispatches ∧ ∀ d ∈ ds, dispatchSafe s d = true := by
  simp only [HostCmd.safe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h

/-- A copy is between two different buffers of this page, the source with `COPY_SRC`,
the target with `COPY_DST`, and both ranges inside their buffers. -/
theorem copy_in_bounds {s : State} {src dst : Gid} {so do_ size : Nat}
    (h : (HostCmd.copyBuffer src so dst do_ size).safe s = true) :
    src.page = s.page ∧ dst.page = s.page ∧ src.id ≠ dst.id ∧
    ∃ ss su ds du, bufferOf s src.id = some (ss, su) ∧ bufferOf s dst.id = some (ds, du) ∧
      su &&& usageCopySrc ≠ 0 ∧ du &&& usageCopyDst ≠ 0 ∧ so + size ≤ ss ∧ do_ + size ≤ ds := by
  simp only [HostCmd.safe, owned, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, _⟩, hd, _⟩, hne⟩, _⟩, _⟩, _⟩, hr⟩ := h
  refine ⟨hs, hd, hne, ?_⟩
  split at hr
  · rename_i ss su ds du h1 h2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hr
    exact ⟨ss, su, ds, du, h1, h2, hr.1.1.1, hr.1.1.2, hr.1.2, hr.2⟩
  · cases hr

/-- The only readback the host is asked for is of a buffer of this page that has
`MAP_READ` (so, by `buffer_usage`, `MAP_READ | COPY_DST` exactly: its contents come only
from copies of this page's buffers), of its whole size. -/
theorem readBuffer_owned {s : State} {g : Gid} {size t : Nat}
    (h : (HostCmd.readBuffer g size t).safe s = true) :
    g.page = s.page ∧ ∃ usage, bufferOf s g.id = some (size, usage) ∧ usage &&& usageMapRead ≠ 0 := by
  simp only [HostCmd.safe, owned, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hp, _⟩, hr⟩ := h
  refine ⟨hp, ?_⟩
  split at hr
  · rename_i bsize usage hb
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr
    obtain ⟨hu, rfl⟩ := hr
    exact ⟨usage, hb, hu⟩
  · cases hr

theorem workOf_append (a b : List HostCmd) : workOf (a ++ b) = workOf a + workOf b := by
  simp [workOf, List.sum_append]

/-- A step counts the work of what it emits, and keeps the frame's work within
`maxFrameWork`. -/
theorem step_work {s s' : State} {c : Command} {out : List HostCmd} (h : step s c = .ok (s', out)) :
    s'.work = s.work + workOf out ∧ s'.work ≤ maxFrameWork := by
  obtain ⟨_, _, _, _, hw, _, rfl⟩ := step_ok h
  exact ⟨rfl, hw⟩

theorem foldl_work (w0 : Nat) (cs : List Command) : ∀ acc : State × List HostCmd,
    acc.1.work = w0 + workOf acc.2 → acc.1.work ≤ maxFrameWork →
    (cs.foldl stepOr acc).1.work = w0 + workOf (cs.foldl stepOr acc).2 ∧ (cs.foldl stepOr acc).1.work ≤ maxFrameWork := by
  induction cs with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons c cs ih =>
    intro acc h1 h2
    apply ih
    · unfold stepOr
      split
      · rename_i s' out hs
        rw [(step_work hs).1, workOf_append]; omega
      · exact h1
    · unfold stepOr
      split
      · rename_i s' out hs; exact (step_work hs).2
      · exact h2

/-- Work per frame: from a new frame (`newFrame`, when the host has taken the page's
commands), the compute work of everything a command sequence emits is at most
`maxFrameWork` operations, whatever is refused on the way. -/
theorem run_frameWork (s : State) (cs : List Command) :
    workOf (run s.newFrame cs).2 ≤ maxFrameWork := by
  have := foldl_work 0 cs (s.newFrame, []) (by simp [State.newFrame, workOf]) (by simp [State.newFrame])
  unfold run; omega

/-- The host's answer to a readback is taken only for a waiting ticket, of exactly the
size asked for; it changes no object and adds the bytes as the buffer's mapped copy. -/
theorem deliver_spec {s s' : State} {t : Nat} {data : ByteArray} (h : deliver s t data = some s') :
    ∃ id size, (t, id, size) ∈ s.pending ∧ data.size = size ∧ s'.objs = s.objs ∧
      s'.mapped = (id, data) :: s.mapped := by
  unfold deliver at h
  split at h
  · rename_i r id size hf
    split at h
    · rename_i hz
      cases h
      have hm := List.mem_of_find?_eq_some hf
      have ht := List.find?_some hf
      simp only [beq_iff_eq] at ht hz
      subst ht
      exact ⟨id, size, hm, hz, rfl, rfl⟩
    · cases h
  · cases h

/-! ### Readback memory -/

/-- The readback bytes Lean holds or waits for stay within `maxMapped`. -/
def MapInv (s : State) : Prop := s.mappedBytes ≤ maxMapped

theorem sum_filter_le {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.filter_cons]; split <;> simp <;> omega

theorem sum_filter_out {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) (x : α)
    (hx : x ∈ l) (hp : p x = false) : ((l.filter p).map f).sum + f x ≤ (l.map f).sum := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.filter_cons]
    cases hx with
    | head => simp [hp]; have := sum_filter_le ys p f; omega
    | tail _ hm => have := ih hm; split <;> simp <;> omega

theorem apply_mapInv {s s' : State} {ch : Change} (hi : MapInv s) (h : apply s ch = .ok s') : MapInv s' := by
  cases ch with
  | none => simp [apply] at h; subst h; exact hi
  | add id o =>
    simp only [apply] at h
    unfold add at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; exact hi
  | remove id =>
    simp only [apply, Except.ok.injEq] at h
    subst h
    simp only [MapInv, State.mappedBytes, remove] at *
    have := sum_filter_le s.pending (·.2.1 != id) (·.2.2)
    have := sum_filter_le s.mapped (·.1 != id) (·.2.size)
    omega
  | read t id size =>
    simp only [apply] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ hq
        cases h
        simp only [MapInv, State.mappedBytes, List.map_cons, List.sum_cons] at *
        omega
  | unmap id =>
    simp only [apply, Except.ok.injEq] at h
    subst h
    simp only [MapInv, State.mappedBytes] at *
    have := sum_filter_le s.mapped (·.1 != id) (·.2.size)
    omega

theorem step_mapInv {s s' : State} {c : Command} {out : List HostCmd} (hi : MapInv s)
    (h : step s c = .ok (s', out)) : MapInv s' := by
  obtain ⟨_, s'', _, _, _, ha, rfl⟩ := step_ok h
  have := apply_mapInv hi ha
  exact this

theorem deliver_mapInv {s s' : State} {t : Nat} {data : ByteArray} (hi : MapInv s)
    (h : deliver s t data = some s') : MapInv s' := by
  unfold deliver at h
  split at h
  · rename_i t' id size hf
    split at h
    · rename_i hz
      cases h
      have hm := List.mem_of_find?_eq_some hf
      have ht := List.find?_some hf
      simp only [beq_iff_eq] at ht hz
      simp only [MapInv, State.mappedBytes, List.map_cons, List.sum_cons] at *
      have h2 : ((s.pending.filter (·.1 != t)).map (·.2.2)).sum + size ≤ (s.pending.map (·.2.2)).sum :=
        sum_filter_out s.pending (·.1 != t) (·.2.2) (t', id, size) hm (by simp [ht])
      omega
    · cases h
  · cases h

theorem fail_mapInv {s : State} {t : Nat} (hi : MapInv s) : MapInv (fail s t) := by
  simp only [MapInv, State.mappedBytes, fail] at *
  have := sum_filter_le s.pending (·.1 != t) (·.2.2)
  omega

/-- The readback bytes held for a page, waiting or answered, stay within `maxMapped` over
any command sequence (and over the host's answers, `deliver_mapInv`, `fail_mapInv`). -/
theorem run_mapInv (s : State) (cs : List Command) (hi : MapInv s) : MapInv (run s cs).1 := by
  unfold run
  suffices ∀ acc : State × List HostCmd, MapInv acc.1 → MapInv (cs.foldl stepOr acc).1 from this _ hi
  induction cs with
  | nil => intro acc h; exact h
  | cons c cs ih =>
    intro acc h
    apply ih
    unfold stepOr
    split
    · rename_i s' out hs; exact step_mapInv h hs
    · exact h

/-! ## Quotas -/

theorem used_filter (l : List (Nat × Obj)) (p : Nat × Obj → Bool) :
    ((l.filter p).map (·.2.bytes)).sum ≤ (l.map (·.2.bytes)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split <;> simp <;> omega

theorem inv_empty (page : Nat) : Inv (State.empty page) := by
  simp [Inv, State.empty, State.used, maxBytes, maxObjects]

theorem add_inv {s s' : State} {id : Nat} {o : Obj} (hi : Inv s) (h : add s id o = .ok s') : Inv s' := by
  unfold add at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ h1 h2
        cases h
        simp only [Inv, State.used, List.map_cons, List.sum_cons, List.length_cons] at *
        constructor <;> omega

theorem apply_inv {s s' : State} {ch : Change} (hi : Inv s) (h : apply s ch = .ok s') : Inv s' := by
  cases ch with
  | none => simp [apply] at h; subst h; exact hi
  | add id o => exact add_inv hi h
  | remove id =>
    simp only [apply, Except.ok.injEq] at h
    subst h
    simp only [Inv, State.used, remove] at *
    exact ⟨Nat.le_trans (used_filter _ _) hi.1, Nat.le_trans (List.length_filter_le _ _) hi.2⟩
  | read t id size =>
    simp only [apply] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact hi
  | unmap id => simp only [apply, Except.ok.injEq] at h; subst h; exact hi

theorem step_inv {s s' : State} {c : Command} {out : List HostCmd} (hi : Inv s)
    (h : step s c = .ok (s', out)) : Inv s' := by
  obtain ⟨_, s'', _, _, _, ha, rfl⟩ := step_ok h
  have := apply_inv hi ha
  exact this

theorem stepOr_inv (acc : State × List HostCmd) (c : Command) (hi : Inv acc.1) : Inv (stepOr acc c).1 := by
  unfold stepOr
  split
  · rename_i s' out h; exact step_inv hi h
  · exact hi

theorem foldl_inv (cs : List Command) : ∀ acc : State × List HostCmd, Inv acc.1 → Inv (cs.foldl stepOr acc).1 := by
  induction cs with
  | nil => intro acc h; exact h
  | cons c cs ih => intro acc h; exact ih _ (stepOr_inv acc c h)

/-- The quotas hold across any command sequence: page GPU bytes at most `maxBytes`,
objects at most `maxObjects`, whatever is refused on the way. -/
theorem run_inv (s : State) (cs : List Command) (hi : Inv s) : Inv (run s cs).1 :=
  foldl_inv cs (s, []) hi

theorem run_quota (page : Nat) (cs : List Command) :
    (run (State.empty page) cs).1.used ≤ maxBytes ∧ (run (State.empty page) cs).1.objs.length ≤ maxObjects :=
  run_inv _ cs (inv_empty page)

end L4Factoidal.PageGpu
