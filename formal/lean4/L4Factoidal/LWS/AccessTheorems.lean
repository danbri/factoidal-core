/-
L4Factoidal.LWS.AccessTheorems — only the LWS request handler, with its
authorization decision, reads or changes the data of an LWS storage that
Factoidal hosts.

Owner requirement for 0.21.0: "only LWS code within Factoidal can access the
data in an LWS storage that Factoidal hosts, stores or serves."

## What is proved

The theorem `lws_data_only_through_authorized_step` is about
`Handler.step`, the function the op `lwsStep` runs for every request. For
every outcome of a request:

* `early`: the answer of the `Host` and `Origin` guard or of the CORS
  preflight. It is the same answer for every state of the storage
  (`early_reads_no_state`): it reads no resource.
* `read`, `resolve`, `fetch`: names of body files, an inbox host name, or an
  authorization server document to fetch; no resource content. `resolve`
  comes only after `Authorization.decide` let the request proceed.
* `redirect`: a 301 with no content, only when `Authorization.decide` lets
  the same request at the current identifier proceed.
* `results`: the search results layer answered after `Authorization.decide`
  let the request proceed, or it answered the decision's own refusal and
  changed no record.
* `served`: the storage answered after `Authorization.decide` let the
  request proceed, or it answered the decision's own refusal (decorated with
  CORS and Merkle fields) and the resources, the subscriptions, the access
  requests and grants and the search records did not change.

`agent_ignored_under_authorization`: under authorization, the agent the host
names in a request document is not used; the decision names the agent.

Below `Authorization.decide`, the layers decide per resource with the same
policy: `Notifications.routed_authorized`, `Search.searchAnswer_authorized`,
`SearchResults.resultsGet_creator_only`, `AccessGrants.accessStep_grant_needs_controller`.

## The one explicit exception

The configuration member `insecureNoAuth: true` (`factoidal lws-serve
--insecure-no-auth`, the `insecureNoAuth` option of `openLwsStorage`; a
development mode). Then `Authorization.decide` lets every request proceed
(`Authorization.decide_insecure`), and the agent the host names stands. The
theorems still hold: the step goes through the handler, but the decision
admits every request. `Authorization.default_not_insecure`: the default
configuration is not this mode.

## The handle and the other ops

The state of a storage lives in a handle table of `Wasm/Ops/Lws.lean`, which
is `private` to that file: no other module of the engine can name it. The ops
of that file are classified in `Wasm.Ops.lwsOpRole`; the theorem
`Wasm.Ops.lws_only_lwsStep_serves` there says `lwsStep` is the only op that
answers a request with resource content. The other ops are the persistence
ops (`lwsOpen`, `lwsLoad`, `lwsRead`, `lwsPersist`, `lwsSnapshot`: the
durable form between the handle and the host's files, sealed under the
storage key `FACTOIDAL_LWS_KEY` when one is given), the delivery ops
(`lwsDelivered`, `lwsFlush`: the delivery state of notifications that
routing already authorized), `lwsFetched` (issuer keys), `lwsClose`, and
three ops that read no storage. A Solid handle refuses a storage that LWS
wrote (`Wasm.Ops.solidRefusesLws`).

## What is NOT covered

* Anyone with file system access to the storage directory reads its files.
  Encryption at rest (`FACTOIDAL_LWS_KEY`) addresses that.
* JavaScript in the same process as the engine: it can call any op,
  including `lwsSnapshot` (the whole storage, sealed only under a storage
  key), and it sets the clock (`now`) a request is decided at.
* The correctness of the decision itself (Web Access Control, the token
  checks): that is `Authorization.lean` and its theorems, not this file.
* Anything outside Factoidal.
-/
import L4Factoidal.LWS.Handler

namespace L4Factoidal.LWS.AccessTheorems

open L4Factoidal.HTTP (Request Response)
open L4Factoidal.LWS.Handler

variable {σ : Type}

/-- The decision `d` either let the request proceed, or refused it with the
answer `resp`. -/
def RefusedWith (d : Authorization.Decision) (resp : Response) : Prop :=
  d = .respond resp

/-! ## The layers -/

/-- **Notifications and the storage operation.** -/
theorem notifications_decided (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Notifications.Signer) (now : Nat)
    (r : Request) (st : σ) (ns : Notifications.NotifState)
    {resp : Response} {st' : σ} {ns' : Notifications.NotifState}
    {ds : List Notifications.Delivery}
    (h : Notifications.serverStep V S cfg a signer now r st ns = .inr (resp, st', ns', ds)) :
    (Authorization.decide V S cfg a now r st = .respond resp ∧ st' = st ∧ ns' = ns ∧ ds = []) ∨
    ∃ ag, Authorization.decide V S cfg a now r st = .proceed ag := by
  unfold Notifications.serverStep at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i resp0 hd
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    subst h1 h2 h3 h4
    exact .inl ⟨hd, rfl, rfl, rfl⟩
  · rename_i ag hd
    exact .inr ⟨ag, hd⟩

/-- **The index services, then notifications.** -/
theorem search_decided (V : JOSE.Verifiers) (S : Store σ) (L : StoreLaws S) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Notifications.Signer) (now : Nat)
    (r : Request) (st : IxState S) (ns : Notifications.NotifState)
    {resp : Response} {st' : IxState S} {ns' : Notifications.NotifState}
    {ds : List Notifications.Delivery}
    (h : Search.serverStep V S L cfg a signer now r st ns = .inr (resp, st', ns', ds)) :
    (Authorization.decide V (IndexedStore S L) cfg a now r st = .respond resp ∧
      st' = st ∧ ns' = ns ∧ ds = []) ∨
    ∃ ag, Authorization.decide V (IndexedStore S L) cfg a now r st = .proceed ag := by
  unfold Search.serverStep at h
  split at h
  split at h
  · dsimp only at h
    split at h
    · simp at h
    · rename_i resp0 hd
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1 h2 h3 h4
      exact .inl ⟨hd, rfl, rfl, rfl⟩
    · rename_i ag hd
      exact .inr ⟨ag, hd⟩
  · exact notifications_decided V _ cfg a signer now r st ns h

/-- **Access requests and grants, then the next layer.** -/
theorem access_decided (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Notifications.Signer) (now : Nat)
    (r : Request) (st : σ) (ns : Notifications.NotifState)
    (next : Request → σ → Notifications.NotifState →
      Sum (String × String) (Response × σ × Notifications.NotifState × List Notifications.Delivery))
    (hnext : ∀ {resp : Response} {st' : σ} {ns' : Notifications.NotifState}
      {ds : List Notifications.Delivery}, next r st ns = .inr (resp, st', ns', ds) →
      (Authorization.decide V S cfg a now r st = .respond resp ∧ st' = st ∧ ns' = ns ∧ ds = []) ∨
      ∃ ag, Authorization.decide V S cfg a now r st = .proceed ag)
    {resp : Response} {st' : σ} {ns' : Notifications.NotifState}
    {acc' : AccessPolicy.AccessState} {ds : List Notifications.Delivery}
    (h : AccessGrants.serverStepWith V S cfg a signer now r st ns next =
      .inr (resp, st', ns', acc', ds)) :
    (Authorization.decide V S cfg a now r st = .respond resp ∧ st' = st ∧ ns' = ns ∧
      acc' = a.access ∧ ds = []) ∨
    ∃ ag, Authorization.decide V S cfg a now r st = .proceed ag := by
  unfold AccessGrants.serverStepWith at h
  split at h
  split at h
  · split at h
    · simp at h
    · rename_i resp0 hd
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      subst h1 h2 h3 h4 h5
      exact .inl ⟨hd, rfl, rfl, rfl, rfl⟩
    · rename_i ag hd
      exact .inr ⟨ag, hd⟩
  · split at h
    · simp at h
    · rename_i resp0 st0 ns0 ds0 hn
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      subst h1 h2 h3 h4 h5
      rcases hnext hn with ⟨d1, d2, d3, d4⟩ | hp
      · exact .inl ⟨d1, d2, d3, rfl, d4⟩
      · exact .inr hp

/-- **Search results resources.** The layer changes no resource; a refused
request keeps the records. -/
theorem results_decided (V : JOSE.Verifiers) (S : Store σ) (L : StoreLaws S) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (rand : Option ByteArray) (r : Request)
    (st : IxState S) (rs : SearchResults.ResultsState)
    {resp : Response} {rs' : SearchResults.ResultsState}
    (h : SearchResults.serverStep V S L cfg a now rand r st rs = .handled resp rs') :
    (Authorization.decide V (IndexedStore S L) cfg a now r st = .respond resp ∧ rs' = rs) ∨
    ∃ ag, Authorization.decide V (IndexedStore S L) cfg a now r st = .proceed ag := by
  unfold SearchResults.serverStep at h
  split at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · rename_i resp0 hd
        simp only [SearchResults.Outcome.handled.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1 h2
        exact .inl ⟨hd, rfl⟩
      · rename_i ag hd
        exact .inr ⟨ag, hd⟩
    · split at h
      · split at h
        · simp at h
        · rename_i resp0 hd
          simp only [SearchResults.Outcome.handled.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1 h2
          exact .inl ⟨hd, rfl⟩
        · rename_i ag hd
          exact .inr ⟨ag, hd⟩
      · simp at h

/-- **Moved resources.** A 301 only when the same request at the current
identifier may proceed; it carries no content. -/
theorem redirect_decided (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (r : Request) (st : σ)
    (es : List (String × String)) {resp : Response}
    (h : MoveRedirect.answer? V S cfg a now r st es = some (.inr resp)) :
    ∃ (r' : Request) (ag : Option String),
      r'.method = r.method ∧ r'.headers = r.headers ∧
      Authorization.decide V S cfg a now r' st = .proceed ag ∧
      resp.status = 301 ∧ resp.body = "" ∧ resp.bytes = none := by
  unfold MoveRedirect.answer? at h
  split at h
  · simp at h
  · split at h
    dsimp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · try dsimp only at h
        split at h
        · simp at h
        · simp at h
        · rename_i ag hd
          simp only [Option.some.injEq, Sum.inr.injEq] at h
          subst h
          refine ⟨_, ag, ?_, ?_, hd, rfl, rfl, rfl⟩ <;> rfl

/-! ## The handler -/

/-- The store, the configuration and the clock a request is decided at. -/
abbrev memOf (s : State) (x : Extra) : IxState LwsBackend := clocked s.mem x.now?
abbrev cfgOf (env : Env) (s : State) (x : Extra) : Config := effectiveCfg env.cfg s.authz x
abbrev nowOf (s : State) (x : Extra) : Nat := x.now?.getD (memOf s x).mem.clock

/-- The decision of the request itself. -/
abbrev decisionOf (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra) :
    Authorization.Decision :=
  Authorization.decide V IS (cfgOf env s x) s.authz (nowOf s x) r (memOf s x)

/-- **Under authorization the host names no agent.** The agent of a request
document stands only with `insecureNoAuth`. -/
theorem agent_ignored_under_authorization (cfg : Config) (a : Authorization.AuthzConfig)
    (x : Extra) (h : a.insecureNoAuth = false) :
    (effectiveCfg cfg a x).agent = cfg.agent := by
  unfold effectiveCfg
  cases x.agent? <;> simp [h]

/-- The three ways `step` ends: an early answer, the body files to read, or
the layers that decide (`decided`). -/
theorem step_cases (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra) :
    (∃ resp, early? env r = some resp ∧ Handler.step V env s r x = .early resp) ∨
    (early? env r = none ∧ ∃ need, Handler.step V env s r x = .read need) ∨
    (early? env r = none ∧ Handler.step V env s r x = decided V env s r x (memOf s x)) := by
  unfold Handler.step
  split
  · rename_i resp he
    exact .inl ⟨resp, he, rfl⟩
  · rename_i he
    dsimp only
    split
    · exact .inr (.inr ⟨he, rfl⟩)
    · exact .inr (.inl ⟨he, _, rfl⟩)

/-- **The early answers read no state.** The guard and the CORS preflight
answer the same for every state of the storage and every document member. -/
theorem early_reads_no_state (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request)
    (x : Extra) {resp : Response} (h : Handler.step V env s r x = .early resp) :
    early? env r = some resp ∧
    ∀ (s₂ : State) (x₂ : Extra), Handler.step V env s₂ r x₂ = .early resp := by
  have he : early? env r = some resp := by
    rcases step_cases V env s r x with ⟨resp0, he0, h0⟩ | ⟨_, need, h0⟩ | ⟨he0, h0⟩
    · rw [h0] at h; cases h; exact he0
    · rw [h0] at h; cases h
    · rw [h0] at h
      unfold decided at h
      dsimp only at h
      repeat (first | (split at h) | simp at h)
  refine ⟨he, fun s₂ x₂ => ?_⟩
  unfold Handler.step
  simp [he]

/-- The outcomes of `decided` other than `resolve`, `redirect`, `results`,
`served` and `fetch` do not occur. -/
theorem decided_resolve (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra)
    (mem : IxState LwsBackend) {host : String}
    (h : decided V env s r x mem = .resolve host) :
    ∃ ag, Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
      (x.now?.getD mem.mem.clock) r mem = .proceed ag := by
  unfold decided at h
  dsimp only at h
  split at h
  · rename_i host0 hr
    unfold Notifications.resolveNeeded? at hr
    revert hr
    cases Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
        (x.now?.getD mem.mem.clock) r mem with
    | proceed ag => intro _; exact ⟨ag, rfl⟩
    | fetch _ _ => simp
    | respond _ => simp
  · repeat (first | (split at h) | simp at h)

theorem decided_redirect (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra)
    (mem : IxState LwsBackend) {resp : Response}
    (h : decided V env s r x mem = .redirect resp) :
    ∃ (r' : Request) (ag : Option String),
      r'.method = r.method ∧ r'.headers = r.headers ∧
      Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
        (x.now?.getD mem.mem.clock) r' mem = .proceed ag ∧
      resp.status = 301 ∧ resp.body = "" ∧ resp.bytes = none := by
  unfold decided at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i resp0 hm
      simp only [Outcome.redirect.injEq] at h
      subst h
      obtain ⟨r', ag, h1, h2, h3, h4, h5, h6⟩ := redirect_decided _ _ _ _ _ _ _ _ hm
      refine ⟨r', ag, h1, h2, h3, ?_, ?_, ?_⟩ <;>
        simp only [Cors.decorate, HTTP.Cors.decorate] <;> split <;> simp [h4, h5, h6]
    · repeat (first | (split at h) | simp at h)

theorem decided_results (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra)
    (mem : IxState LwsBackend) {resp : Response} {rs' : SearchResults.ResultsState}
    (h : decided V env s r x mem = .results resp rs') :
    (∃ ag, Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
        (x.now?.getD mem.mem.clock) r mem = .proceed ag) ∨
    (∃ resp0, Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
        (x.now?.getD mem.mem.clock) r mem = .respond resp0 ∧ rs' = s.results ∧
      resp = Cors.decorate (effectiveCfg env.cfg s.authz x) r resp0) := by
  unfold decided at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp at h
    · split at h
      · simp at h
      · rename_i resp0 rs0 hr
        simp only [Outcome.results.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1 h2
        rcases results_decided _ _ _ _ _ _ _ _ _ _ hr with ⟨d1, d2⟩ | hp
        · exact .inr ⟨resp0, d1, d2, rfl⟩
        · exact .inl hp
      · repeat (first | (split at h) | simp at h)

theorem decided_served (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra)
    (mem : IxState LwsBackend) {resp : Response} {s' : State} {ch : Bool}
    {ds : List Notifications.Delivery}
    (h : decided V env s r x mem = .served resp s' ch ds) :
    (∃ ag, Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
        (x.now?.getD mem.mem.clock) r mem = .proceed ag) ∨
    (∃ resp0, Authorization.decide V IS (effectiveCfg env.cfg s.authz x) s.authz
        (x.now?.getD mem.mem.clock) r mem = .respond resp0 ∧
      s'.mem = mem ∧ s'.notif = s.notif ∧ s'.authz = s.authz ∧
      s'.results = s.results ∧ ds = [] ∧
      ∃ vis, resp = Cors.decorate (effectiveCfg env.cfg s.authz x) r
        (Merkle.decorate LwsBase (effectiveCfg env.cfg s.authz x) mem.base vis r resp0)) := by
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
          simp only [Outcome.served.injEq] at h
          obtain ⟨h1, h2, _, h4⟩ := h
          rcases access_decided V IS _ _ env.signer _ r _ _ _
              (fun hn => search_decided V LwsBackend lwsBackendLaws _ _ env.signer _ r _ _ hn)
              hc with ⟨d1, d2, d3, d4, d5⟩ | hp
          · subst d2 d3 d4 d5 h1 h2 h4
            exact .inr ⟨resp0, d1, rfl, rfl, rfl, rfl, rfl, _, rfl⟩
          · exact .inl hp

/-- **`lws_data_only_through_authorized_step`.** Every outcome of the LWS
request handler is accounted for: the early answers read no state; a
`resolve`, a `redirect`, a `results` or a `served` outcome comes from
`Authorization.decide`, which either let the request proceed or refused it,
and a refused request changes nothing and answers the refusal. `read` names
body files and `fetch` names an authorization server document: no resource
content. -/
theorem lws_data_only_through_authorized_step (V : JOSE.Verifiers) (env : Env) (s : State)
    (r : Request) (x : Extra) :
    match Handler.step V env s r x with
    | .early resp => ∀ (s₂ : State) (x₂ : Extra), Handler.step V env s₂ r x₂ = .early resp
    | .read _ => True
    | .fetch _ _ => True
    | .resolve _ => ∃ ag, decisionOf V env s r x = .proceed ag
    | .redirect resp =>
        ∃ (r' : Request) (ag : Option String),
          r'.method = r.method ∧ r'.headers = r.headers ∧
          Authorization.decide V IS (cfgOf env s x) s.authz (nowOf s x) r' (memOf s x) = .proceed ag ∧
          resp.status = 301 ∧ resp.body = "" ∧ resp.bytes = none
    | .results resp rs' =>
        (∃ ag, decisionOf V env s r x = .proceed ag) ∨
        (∃ resp0, decisionOf V env s r x = .respond resp0 ∧ rs' = s.results ∧
          resp = Cors.decorate (cfgOf env s x) r resp0)
    | .served resp s' _ ds =>
        (∃ ag, decisionOf V env s r x = .proceed ag) ∨
        (∃ resp0, decisionOf V env s r x = .respond resp0 ∧
          s'.mem = memOf s x ∧ s'.notif = s.notif ∧ s'.authz = s.authz ∧
          s'.results = s.results ∧ ds = [] ∧
          ∃ vis, resp = Cors.decorate (cfgOf env s x) r
            (Merkle.decorate LwsBase (cfgOf env s x) (memOf s x).base vis r resp0)) := by
  rcases step_cases V env s r x with ⟨resp, _, ho⟩ | ⟨_, need, ho⟩ | ⟨_, ho⟩
  · rw [ho]; exact (early_reads_no_state V env s r x ho).2
  · rw [ho]; trivial
  · rw [ho]
    cases hd : decided V env s r x (memOf s x) with
    | early resp =>
        unfold decided at hd
        dsimp only at hd
        repeat (first | (split at hd) | simp at hd)
    | read _ => trivial
    | fetch _ _ => trivial
    | resolve _ => exact decided_resolve V env s r x _ hd
    | redirect resp => exact decided_redirect V env s r x _ hd
    | results resp rs' => exact decided_results V env s r x _ hd
    | served resp s' ch ds => exact decided_served V env s r x _ hd

/-- **The exception.** With `insecureNoAuth`, every decision lets the request
proceed as the configured agent (`Authorization.decide_insecure`); it is not
the default (`Authorization.default_not_insecure`). -/
theorem insecureNoAuth_is_the_exception (V : JOSE.Verifiers) (env : Env) (s : State)
    (r : Request) (x : Extra) (h : s.authz.insecureNoAuth = true) :
    decisionOf V env s r x = .proceed (cfgOf env s x).agent :=
  Authorization.decide_insecure V IS _ _ _ r _ h

end L4Factoidal.LWS.AccessTheorems
