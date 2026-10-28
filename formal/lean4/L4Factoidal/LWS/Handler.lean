/-
L4Factoidal.LWS.Handler — the LWS request handler: one request against one
storage, as a total function.

`Wasm.Ops.lwsStepWith` (the op `lwsStep`) reads the handle, decodes the
request document, calls `Handler.step`, and stores the state it answers.
Every decision of a request is here; the op only moves bytes and keeps the
handle table. `L4Factoidal.LWS.AccessTheorems` proves what this function
does with the authorization decision (`Authorization.decide`).

The order of the layers is the order `lwsStepWith` had before this module
(https://github.com/danbri/factoidal/issues/1124 for the guard, 923 for
CORS, 918 for the body files, 915 for the inbox host, 914 for moved
resources, 922 for search results, 920 for access requests and grants, 919
for the Merkle fields):

1. the `Host` and `Origin` guard of a storage with no authorization, and
   the CORS preflight: both are functions of the request and the
   configuration only, and read no state;
2. the body files the step needs (a storage kept in files): their names;
3. the inbox host to resolve before a subscription;
4. the previous identifier of a moved resource (301);
5. the search results resources;
6. access requests and grants, the index services, notifications and the
   storage operation (`AccessGrants.serverStepWith` over `Search.serverStep`
   over `Notifications.serverStep`).

Layers 3 to 6 each ask `Authorization.decide` before they read or change a
resource.
-/
import L4Factoidal.LWS.MerkleHttp
import L4Factoidal.LWS.Cors
import L4Factoidal.LWS.Bodies
import L4Factoidal.LWS.MoveRedirect
import L4Factoidal.LWS.SearchResults
import L4Factoidal.LWS.AccessGrants
import L4Factoidal.LWS.Search
import L4Factoidal.LWS.Move
import L4Factoidal.HTTP.LocalGuard

namespace L4Factoidal.LWS.Handler

open L4Factoidal.HTTP (Request Response)

/-- The state of one storage that a request reads or changes. -/
structure State where
  mem : IxState LwsBackend
  authz : Authorization.AuthzConfig
  notif : Notifications.NotifState
  results : SearchResults.ResultsState
  moved : List (String × String)

/-- What the handle holds besides the state: the configuration, the signer
of webhook deliveries, the `Host` and `Origin` guard, and whether the
storage is kept in files. -/
structure Env where
  cfg : Config
  signer : Option Notifications.Signer
  guard : Option L4Factoidal.HTTP.LocalGuard.LocalGuard
  files : Bool

/-- The members of a request document besides the request: the clock the
host sets, the agent the host names, the addresses the host resolved, and
random bytes for a search results name. -/
structure Extra where
  now? : Option Nat := none
  agent? : Option String := none
  resolved : List (String × List String) := []
  rand : Option ByteArray := none

/-- The outcome of one request. -/
inductive Outcome where
  /-- Answered before any state is read: the guard or the CORS preflight. -/
  | early (resp : Response)
  /-- Read these body files and step the same request again. -/
  | read (need : List (String × BodyStub))
  /-- Resolve the addresses of this inbox host and step again. -/
  | resolve (host : String)
  /-- Fetch this authorization server document and step again. -/
  | fetch (issuer url : String)
  /-- The 301 of the previous identifier of a moved resource. -/
  | redirect (resp : Response)
  /-- The answer of the search results layer, and its records after. -/
  | results (resp : Response) (rs : SearchResults.ResultsState)
  /-- The answer of the storage, the state after it, whether it changed, and
  the webhook deliveries to make. -/
  | served (resp : Response) (st : State) (changed : Bool) (ds : List Notifications.Delivery)

/-- The configuration a request is stepped under. The agent the host names
stands only in the explicit no-authorization mode (`insecureNoAuth`); the
resolved addresses are data. -/
def effectiveCfg (cfg : Config) (a : Authorization.AuthzConfig) (x : Extra) : Config :=
  let cfg := match x.agent? with
    | some ag => if a.insecureNoAuth then { cfg with agent := some ag } else cfg
    | none => cfg
  { cfg with resolved := x.resolved }

/-- The store a request is stepped against: the host's clock, when given. -/
def clocked (mem : IxState LwsBackend) (now? : Option Nat) : IxState LwsBackend :=
  match now? with
  | some t => mem.withClockM t
  | none => mem

/-- The store type of every layer. -/
abbrev IS := IndexedStore LwsBackend lwsBackendLaws

/-- The answer before any state is read: the guard, then the preflight. -/
def early? (env : Env) (r : Request) : Option Response :=
  match env.guard.bind (fun g => L4Factoidal.HTTP.LocalGuard.admit g r) with
  | some resp => some resp
  | none => Cors.preflight? env.cfg r

/-- Layer 6: access requests and grants, the index services, notifications
and the storage operation. -/
def core (V : JOSE.Verifiers) (env : Env) (cfg : Config) (a : Authorization.AuthzConfig)
    (now : Nat) (r : Request) (mem : IxState LwsBackend) (ns : Notifications.NotifState) :
    Sum (String × String) (Response × IxState LwsBackend × Notifications.NotifState ×
      AccessPolicy.AccessState × List Notifications.Delivery) :=
  AccessGrants.serverStepWith V IS cfg a env.signer now r mem ns
    (fun r st ns => Search.serverStep V LwsBackend lwsBackendLaws cfg a env.signer now r st ns)

/-- The body files a step needs first (a storage kept in files): names only. -/
def needOf (env : Env) (s : State) (r : Request) (mem : IxState LwsBackend) :
    List (String × BodyStub) :=
  if env.files then
    Bodies.bodiesNeeded env.cfg (env.cfg.notifications && !s.notif.subs.isEmpty) r mem
  else []

/-- Layers 3 to 6: every one asks `Authorization.decide`. -/
def decided (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra)
    (mem : IxState LwsBackend) : Outcome :=
  let cfg := effectiveCfg env.cfg s.authz x
  let now := x.now?.getD mem.mem.clock
  match Notifications.resolveNeeded? V IS cfg s.authz now r mem with
  | some host => .resolve host
  | none =>
  match MoveRedirect.answer? V IS cfg s.authz now r mem s.moved with
  | some (.inl (issuer, url)) => .fetch issuer url
  | some (.inr resp) => .redirect (Cors.decorate cfg r resp)
  | none =>
  let plan? := movePlanOf? IS cfg.baseIri cfg.moves cfg.moveContainers r mem
  match SearchResults.serverStep V LwsBackend lwsBackendLaws cfg s.authz now x.rand r mem s.results with
  | .fetch issuer url => .fetch issuer url
  | .handled resp rs' => .results (Cors.decorate cfg r resp) rs'
  | .pass =>
  match core V env cfg s.authz now r mem s.notif with
  | .inl (issuer, url) => .fetch issuer url
  | .inr (resp, mem', notif', access', ds) =>
      let authz' := { s.authz with access := access' }
      let moved' := MoveRedirect.after IS cfg.redirectsMax plan? resp.status mem' s.moved
      let resp := Merkle.decorate LwsBase cfg mem'.base
        (fun _ => Merkle.rootsVisible V IS cfg authz' now r mem') r resp
      let resp := Cors.decorate cfg r resp
      -- Every mutation advances the clock (`StoreLaws.nowTick`), so a changed
      -- clock is exactly "the storage changed".
      let changed := mem'.mem.clock != mem.mem.clock ||
        notif'.revision != s.notif.revision ||
        access'.revision != s.authz.access.revision ||
        moved' != s.moved
      .served resp { s with mem := mem', notif := notif', authz := authz', moved := moved' }
        changed ds

/-- One request. -/
def step (V : JOSE.Verifiers) (env : Env) (s : State) (r : Request) (x : Extra) : Outcome :=
  match early? env r with
  | some resp => .early resp
  | none =>
  let mem := clocked s.mem x.now?
  let need := needOf env s r mem
  if need.isEmpty then decided V env s r x mem else .read need

end L4Factoidal.LWS.Handler
