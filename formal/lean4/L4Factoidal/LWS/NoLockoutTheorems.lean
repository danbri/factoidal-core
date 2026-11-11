/-
L4Factoidal.LWS.NoLockoutTheorems — the no-lockout guard of the LWS request
handler (`Handler.lockoutGuard`, `L4Factoidal.LWS.NoLockout`), stated over
`Handler.step`, the function every request of an LWS storage handle runs
(`Wasm.Ops.lwsStepWith`).

* `step_keeps_root_control`: with authorization on, if before a request some
  agent has `acl:Control` on the storage root (`NoLockout.RootControl`, Web
  Access Control's `Solid.Server.allowed`), then after it some agent has.
* `decided_served_guarded`: a request the guard refuses answers 409
  (`lockoutGuard_refused`) and keeps the state it was stepped against: no
  resource, no notification state, no access grant, no search results record
  and no redirect changes, the host is told `changed: false`, and no delivery
  is made. Every other served request passed the guard.
* `lockoutGuard_fires`: with authorization on, the guard refuses every request
  whose storage operation changed the root ACL and left no agent with
  `acl:Control` on the root (`NoLockout.lockout_iff`).
-/
import L4Factoidal.LWS.AccessTheorems

namespace L4Factoidal.LWS.NoLockoutTheorems

open L4Factoidal.HTTP (Request Response)
open L4Factoidal.LWS.Handler
open L4Factoidal.LWS.AccessTheorems (memOf)

/-- The configuration a request is stepped under has the storage's base IRI. -/
theorem effectiveCfg_baseIri (cfg : Config) (a : Authorization.AuthzConfig) (x : Extra) :
    (effectiveCfg cfg a x).baseIri = cfg.baseIri := by
  unfold effectiveCfg
  cases x.agent? with
  | none => rfl
  | some ag => by_cases h : a.insecureNoAuth <;> simp [h]

/-- **A refused request answers 409.** (What `decided` keeps for it is the
state it was stepped against, `decided_lockout_refused`.) -/
theorem lockoutGuard_refused (cfg : Config) (a : Authorization.AuthzConfig) (r : Request)
    (mem mem' : IxState LwsBackend) {resp : Response}
    (h : lockoutGuard cfg a r mem mem' = some resp) :
    a.insecureNoAuth = false ∧
    NoLockout.lockout IS Solid.Server.aclGraphOf cfg.baseIri mem mem' = true ∧
    resp.status = 409 := by
  unfold lockoutGuard at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    refine ⟨hc.1, hc.2, ?_⟩
    simp only [Cors.decorate, HTTP.Cors.decorate]
    split <;> rfl
  · cases h

/-- **The guard refuses every lockout**, with authorization on. -/
theorem lockoutGuard_fires (cfg : Config) (a : Authorization.AuthzConfig) (r : Request)
    (mem mem' : IxState LwsBackend) (ha : a.insecureNoAuth = false)
    (hl : NoLockout.lockout IS Solid.Server.aclGraphOf cfg.baseIri mem mem' = true) :
    (lockoutGuard cfg a r mem mem').isSome := by
  simp [lockoutGuard, ha, hl]

/-- A request the guard let through, with authorization on, did not lock out. -/
theorem lockoutGuard_none (cfg : Config) (a : Authorization.AuthzConfig) (r : Request)
    (mem mem' : IxState LwsBackend) (ha : a.insecureNoAuth = false)
    (h : lockoutGuard cfg a r mem mem' = none) :
    NoLockout.lockout IS Solid.Server.aclGraphOf cfg.baseIri mem mem' = false := by
  cases hl : NoLockout.lockout IS Solid.Server.aclGraphOf cfg.baseIri mem mem'
  · rfl
  · have := lockoutGuard_fires cfg a r mem mem' ha hl
    rw [h] at this
    cases this

/-- **No served request leaves a lockout.** With authorization on, every
`served` outcome of the layers that decide either is the guard's refusal (409),
which keeps the state the request was stepped against (`mem`), the
notification state, the access state, the search results and the redirects,
says `changed: false` and makes no delivery; or its storage operation passed
the guard. -/
theorem decided_served_guarded (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request)
    (x : Extra) (mem : IxState LwsBackend) (ha : s.authz.insecureNoAuth = false)
    {resp : Response} {s' : State} {ch : Bool} {ds : List Notifications.Delivery}
    (h : decided V env s r x mem = .served resp s' ch ds) :
    (resp.status = 409 ∧ s' = { s with mem := mem } ∧ ch = false ∧ ds = []) ∨
    NoLockout.lockout IS Solid.Server.aclGraphOf env.cfg.baseIri mem s'.mem = false := by
  unfold decided at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp at h
    · split at h
      · simp at h
      · simp at h
      · split at h
        · simp at h
        · rename_i resp0 mem0 ns0 acc0 ds0 hc
          split at h
          · rename_i refused hg
            simp only [Outcome.served.injEq] at h
            obtain ⟨h1, h2, h3, h4⟩ := h
            subst h1 h2 h3 h4
            exact .inl ⟨(lockoutGuard_refused _ _ _ _ _ hg).2.2, rfl, rfl, rfl⟩
          · rename_i hg
            simp only [Outcome.served.injEq] at h
            obtain ⟨_, h2, _, _⟩ := h
            subst h2
            have hl := lockoutGuard_none _ _ _ _ _ ha hg
            rw [effectiveCfg_baseIri] at hl
            exact .inr hl

theorem decided_keeps_root_control (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request)
    (x : Extra) (mem : IxState LwsBackend) (ha : s.authz.insecureNoAuth = false)
    {resp : Response} {s' : State} {ch : Bool} {ds : List Notifications.Delivery}
    (h : decided V env s r x mem = .served resp s' ch ds)
    (hb : NoLockout.RootControl IS Solid.Server.aclGraphOf env.cfg.baseIri mem) :
    NoLockout.RootControl IS Solid.Server.aclGraphOf env.cfg.baseIri s'.mem := by
  rcases decided_served_guarded V env s r x mem ha h with ⟨_, hs, _, _⟩ | hl
  · subst hs; exact hb
  · exact NoLockout.accepted_keeps_control _ _ _ _ _ hl hb

/-- **`step_keeps_root_control`.** For every request handled with
authorization on: if before it some agent has `acl:Control` on the storage
root, then after it some agent has. "Before" is the storage the request is
stepped against (`memOf`: the handle's storage with the host's clock). -/
theorem step_keeps_root_control (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request)
    (x : Extra) (ha : s.authz.insecureNoAuth = false)
    {resp : Response} {s' : State} {ch : Bool} {ds : List Notifications.Delivery}
    (h : Handler.step V env s r x = .served resp s' ch ds)
    (hb : NoLockout.RootControl IS Solid.Server.aclGraphOf env.cfg.baseIri (memOf s x)) :
    NoLockout.RootControl IS Solid.Server.aclGraphOf env.cfg.baseIri s'.mem := by
  rcases AccessTheorems.step_cases V env s r x with ⟨_, _, ho⟩ | ⟨_, _, ho⟩ | ⟨_, ho⟩
  · rw [ho] at h; cases h
  · rw [ho] at h; cases h
  · rw [ho] at h
    exact decided_keeps_root_control V env s r x _ ha h hb

end L4Factoidal.LWS.NoLockoutTheorems
