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

theorem validate_sound (m : Module) (h : validate m = true) : InSubset m := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hf⟩, _⟩, _⟩, _⟩, hfns⟩, hst⟩, hex⟩, _⟩ := h
  refine ⟨hs, hf, hex, hst, ?_⟩
  intro f hmem
  have := hfns f hmem
  simp only [fnOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

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
    | _ => false

def clampedA (structs : List StructDecl) (env : Env) : Args → Bool
  | .nil => true
  | .cons e rest => clampedE structs env e && clampedA structs env rest
end

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
      split at h
      · cases h
      · cases h; simp only [tyOf]; rw [hardenE_tyOf structs env a a' ha]
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
      split at h
      · cases h
      · rename_i hn0
        cases h
        simp only [clampedE, clampIdx, Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨?_, hardenE_clamped structs env a a' ha⟩, hardenE_clamped structs env i i' hi⟩
        rw [hardenE_tyOf structs env a a' ha, hn]
        congr 1; omega
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

theorem step_safe {s s' : State} {c : Command} {out : List HostCmd}
    (h : step s c = .ok (s', out)) : ∀ x ∈ out, x.safe s = true := by
  simp only [step, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i hall
      split at h
      · cases h
      · cases h
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hall
        rw [List.all_eq_true] at hall
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

/-- A page buffer never gets a usage that maps it or copies out of it. -/
theorem buffer_usage {s : State} {g : Gid} {size usage : Nat}
    (h : (HostCmd.createBuffer g size usage).safe s = true) :
    usage &&& forbiddenUsage = 0 ∧ size ≤ maxBuffer := by
  simp only [HostCmd.safe, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.2⟩

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
  simp only [step, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        obtain ⟨ch, o⟩ := p
        exact plan_createBuffer_clears hp

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

theorem step_inv {s s' : State} {c : Command} {out : List HostCmd} (hi : Inv s)
    (h : step s c = .ok (s', out)) : Inv s' := by
  simp only [step, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p _
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s'' ha
        cases h
        exact apply_inv hi ha

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
