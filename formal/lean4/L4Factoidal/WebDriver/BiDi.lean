/-
L4Factoidal.WebDriver.BiDi: WebDriver BiDi over the WebDriver endpoint (W3C WebDriver BiDi,
editor's draft; stage 1 of docs/designissues/2026-11-27-foafnaut-webdriver-bidi.md).

The host's listener accepts a WebSocket upgrade on the WebDriver endpoint's port and gives its
path and two headers to `connect`; then it gives each frame of the connection to `handle` and
sends the message that `handle` answers. Every decision of the protocol is here; the host moves
bytes.

- `connect`: the gate first (`Gate.admit`, the same gate state as classic requests), then the
  resource: `/session` (a BiDi-only connection, for `session.new`) or `/session/<id>` of the
  active classic session that asked for `webSocketUrl`. Anything else is refused.
- `handle`: "handle an incoming message" (BiDi section 4): a binary frame or text that is not
  JSON is `invalid argument` with id null; a connection whose session has ended gets no answer;
  a message that is not a command is `unknown command` (a `method` that names no command) or
  `invalid argument`; then `exec`.
- `exec`: the session check (only `session.status` and `session.new` are static), then
  `session.status`, `session.new`, `session.end`, `session.subscribe`, `session.unsubscribe`,
  `browsingContext.getTree`, `browsingContext.navigate`. Any other command of the specification
  is `unknown command` for now (https://github.com/danbri/factoidal-core/issues/1203).

Proved: `connect_refused` (an upgrade the gate refuses gives no connection and changes no
session), `connect_no_secret`, `connect_origin`, `parseMessage_unknown` (a `method` that names
no command gives `unknown command`), `exec_no_session` (with no live session, every command but
the two static ones is `invalid session id`), `handle_error_keeps` (a message answered with an
error changes no state), `handle_binary` (a binary frame is `invalid argument` and changes
nothing).
Tested: `#guard`s below, from `webdriver/tests/bidi/` (errors, session, browsing_context).
-/
import L4Factoidal.WebDriver.Protocol
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.WebDriver.BiDi
open L4Factoidal.JSON

/-! ## Errors and messages (BiDi section 3.5, 3.6) -/

/-- The error codes this stage gives (BiDi `ErrorCode`; the specification has 30). -/
inductive ErrorCode where
  | invalidArgument | invalidSessionId | noSuchFrame | noSuchUserContext
  | sessionNotCreated | unknownCommand | unknownError
  deriving DecidableEq, Repr, Inhabited

def ErrorCode.name : ErrorCode → String
  | .invalidArgument => "invalid argument"
  | .invalidSessionId => "invalid session id"
  | .noSuchFrame => "no such frame"
  | .noSuchUserContext => "no such user context"
  | .sessionNotCreated => "session not created"
  | .unknownCommand => "unknown command"
  | .unknownError => "unknown error"

structure Error where
  code : ErrorCode
  message : String := ""
  deriving DecidableEq, Repr, Inhabited

def num (n : Nat) : Json := .number (toString n)

/-- `ErrorResponse`: `id` is null when the message had no usable id. -/
def errorMessage (id : Option Nat) (e : Error) : Json :=
  .object [("type", .string "error"), ("id", match id with | some n => num n | none => .null),
    ("error", .string e.code.name), ("message", .string e.message), ("stacktrace", .string "")]

/-- `CommandResponse`. -/
def successMessage (id : Nat) (result : Json) : Json :=
  .object [("type", .string "success"), ("id", num id), ("result", result)]

/-- `Event` (stage 1 sends none; `subscribed` decides who gets one). -/
def eventMessage (method : String) (params : Json) : Json :=
  .object [("type", .string "event"), ("method", .string method), ("params", params)]

/-! ## Names -/

/-- The events of the specification, by module. -/
def modules : List (String × List String) := [
  ("browsingContext", ["contextCreated", "contextDestroyed", "navigationStarted", "fragmentNavigated",
    "historyUpdated", "domContentLoaded", "load", "downloadWillBegin", "downloadEnd", "navigationAborted",
    "navigationCommitted", "navigationFailed", "userPromptClosed", "userPromptOpened"]),
  ("input", ["fileDialogOpened"]),
  ("log", ["entryAdded"]),
  ("network", ["authRequired", "beforeRequestSent", "fetchError", "responseCompleted", "responseStarted"]),
  ("script", ["message", "realmCreated", "realmDestroyed"])]

def eventNames : List String := modules.flatMap fun (m, es) => es.map (m ++ "." ++ ·)

/-- The commands of the specification ("the set of all command names"). -/
def commandNames : List String := [
  "browser.close", "browser.createUserContext", "browser.getClientWindows", "browser.getUserContexts",
  "browser.removeUserContext", "browser.setClientWindowState", "browser.setDownloadBehavior",
  "browsingContext.activate", "browsingContext.captureScreenshot", "browsingContext.close",
  "browsingContext.create", "browsingContext.getTree", "browsingContext.handleUserPrompt",
  "browsingContext.locateNodes", "browsingContext.navigate", "browsingContext.print",
  "browsingContext.reload", "browsingContext.setViewport", "browsingContext.startScreencast",
  "browsingContext.stopScreencast", "browsingContext.traverseHistory",
  "emulation.setForcedColorsModeThemeOverride", "emulation.setGeolocationOverride",
  "emulation.setLocaleOverride", "emulation.setNetworkConditions", "emulation.setScreenOrientationOverride",
  "emulation.setScreenSettingsOverride", "emulation.setScriptingEnabled", "emulation.setTimezoneOverride",
  "emulation.setTouchOverride", "emulation.setUserAgentOverride",
  "input.performActions", "input.releaseActions", "input.setFiles",
  "network.addDataCollector", "network.addIntercept", "network.continueRequest", "network.continueResponse",
  "network.continueWithAuth", "network.disownData", "network.failRequest", "network.getData",
  "network.provideResponse", "network.removeDataCollector", "network.removeIntercept",
  "network.setCacheBehavior", "network.setExtraHeaders",
  "script.addPreloadScript", "script.callFunction", "script.disown", "script.evaluate", "script.getRealms",
  "script.removePreloadScript",
  "session.end", "session.new", "session.status", "session.subscribe", "session.unsubscribe",
  "storage.deleteCookies", "storage.getCookies", "storage.setCookie",
  "webExtension.install", "webExtension.uninstall"]

/-! ## Parsing a message -/

/-- A WebSocket frame as the host gives it. -/
inductive Frame where
  | text (s : String)
  | binary
  deriving DecidableEq, Repr, Inhabited

/-- A `js-uint`: an integer from 0 to 2^53 - 1. -/
def jsUint (j : Json) : Option Nat := Protocol.safeInteger j

structure Command where
  id : Nat
  method : String
  params : Json
  deriving Repr

/-- Match parsed JSON against the `Command` production (step 6 and 7 of "handle an incoming
message"). On no match: the id is the message's `id` when it is a `js-uint`, else none; the
code is `unknown command` when `method` is a string that names no command, else
`invalid argument`. -/
def parseMessage (j : Json) : Except (Option Nat × Error) Command :=
  let id := (j.field? "id").bind jsUint
  match j.field? "method" with
  | some (.string m) =>
    if !commandNames.contains m then .error (id, { code := .unknownCommand, message := m ++ " is not a command" })
    else match j, id, j.field? "params" with
      | .object _, some n, some (.object ps) => .ok { id := n, method := m, params := .object ps }
      | _, _, _ => .error (id, { code := .invalidArgument, message := "the message is not a command" })
  | _ => .error (id, { code := .invalidArgument, message := "the message is not a command" })

/-! ## State -/

/-- A subscription (`session.subscribe`): its id, its event names (modules expanded), and the
contexts or user contexts it is for (both empty: a global subscription). -/
structure Subscription where
  id : String
  events : List String
  contexts : List String := []
  userContexts : List String := []
  deriving DecidableEq, Repr, Inhabited

def Subscription.global (s : Subscription) : Bool := s.contexts.isEmpty && s.userContexts.isEmpty

/-- The BiDi part of the active session. -/
structure Session where
  id : String
  subscriptions : List Subscription := []
  deriving DecidableEq, Repr, Inhabited

structure State where
  session : Option Session := none
  deriving DecidableEq, Repr, Inhabited

/-- A WebSocket connection: the session it belongs to (none: a BiDi-only connection before
`session.new`). Made only by `connect` and `session.new`. -/
structure Conn where
  session : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- A top-level browsing context as the host has it (stage 1: the one window). -/
structure Context where
  id : String
  url : String := "about:blank"
  clientWindow : String
  deriving DecidableEq, Repr, Inhabited

/-- What a message is handled with: the browser, its contexts, and 16 fresh bytes of the
machine's generator (for ids). -/
structure Env where
  browser : Protocol.Browser := {}
  contexts : List Context := []
  entropy : ByteArray := ByteArray.empty

/-- What the host does after it sends the reply. -/
inductive Effect where
  | none
  /-- load `url` in context `context` before the reply is sent -/
  | navigate (context url : String)
  /-- close every connection of the ended session after the reply is sent -/
  | close
  deriving DecidableEq, Repr, Inhabited

/-- The connection's session, when it is the active session. -/
def liveSession (srv : Protocol.Server) (conn : Conn) : Option Protocol.Session :=
  match conn.session, srv.session with
  | some c, some s => if c == s.id then some s else none
  | _, _ => none

/-- A version 4 UUID from 16 bytes of the generator (RFC 9562 section 5.4). -/
def uuid4 (entropy : ByteArray) : String :=
  let b := entropy.set! 6 ((entropy.get! 6 &&& 0x0f) ||| 0x40)
  let b := b.set! 8 ((b.get! 8 &&& 0x3f) ||| 0x80)
  Protocol.sessionIdOf b

/-! ## Parameters -/

private def bad (message : String) : Error := { code := .invalidArgument, message }

/-- An optional parameter that is a non-empty list of strings. -/
def stringList? (p : Json) (name : String) : Except Error (Option (List String)) :=
  match p.field? name with
  | none => .ok none
  | some (.array xs) =>
    if xs.isEmpty then .error (bad (name ++ " is empty")) else
    match xs.mapM (fun x => match x with | .string s => some s | _ => none) with
    | some ss => .ok (some ss)
    | none => .error (bad (name ++ " has a member that is not a string"))
  | some _ => .error (bad (name ++ " is not a list"))

/-- An event name or a module name, as event names ("obtain a set of event names"). -/
def expand (name : String) : Except Error (List String) :=
  if name.toList.contains '.' then
    if eventNames.contains name then .ok [name] else .error (bad (name ++ " is not an event"))
  else match modules.find? (·.1 == name) with
    | some (m, es) => .ok (es.map (m ++ "." ++ ·))
    | none => .error (bad (name ++ " is not a module with events"))

def expandAll (names : List String) : Except Error (List String) :=
  (names.mapM expand).map fun xss => xss.flatten.eraseDups

/-! ## Commands -/

def subscribe (env : Env) (s : Session) (p : Json) : Except Error (Session × Json) := do
  let events ← match ← stringList? p "events" with
    | some es => pure es
    | none => throw (bad "events is missing")
  let contexts ← stringList? p "contexts"
  let users ← stringList? p "userContexts"
  if contexts.isSome && users.isSome then throw (bad "contexts and userContexts are both given")
  let names ← expandAll events
  let cs := contexts.getD []
  if let some c := cs.find? (fun c => !env.contexts.any (·.id == c)) then
    throw { code := .noSuchFrame, message := c ++ " is not a browsing context" }
  let us := users.getD []
  if let some u := us.find? (· != "default") then
    throw { code := .noSuchUserContext, message := u ++ " is not a user context" }
  if env.entropy.size < Gate.secretBytes then throw { code := .unknownError, message := "no entropy for an id" }
  let id := uuid4 env.entropy
  pure ({ s with subscriptions := s.subscriptions ++ [{ id := id, events := names, contexts := cs.eraseDups, userContexts := us.eraseDups }] },
    .object [("subscription", .string id)])

def unsubscribe (s : Session) (p : Json) : Except Error Session :=
  match p.field? "subscriptions", p.field? "events" with
  | some _, _ => do
    let ids ← match ← stringList? p "subscriptions" with
      | some ids => pure ids
      | none => throw (bad "subscriptions is missing")
    if ids.all (fun i => s.subscriptions.any (·.id == i)) then
      pure { s with subscriptions := s.subscriptions.filter (fun x => !ids.contains x.id) }
    else throw (bad "a subscription id is not known")
  | none, some _ => do
    let events ← match ← stringList? p "events" with
      | some es => pure es
      | none => throw (bad "events is missing")
    let names ← expandAll events
    let globals := s.subscriptions.filter (·.global)
    if names.all (fun n => globals.any (·.events.contains n)) then
      let subs := s.subscriptions.filterMap fun x =>
        if !x.global then some x else
        match x.events.filter (fun e => !names.contains e) with
        | [] => none
        | es => some { x with events := es }
      pure { s with subscriptions := subs }
    else throw (bad "an event has no global subscription")
  | none, none => .error (bad "neither subscriptions nor events is given")

/-- `browsingContext.Info` of a top-level context (stage 1: no child contexts). -/
def info (maxDepth : Option Nat) (c : Context) : Json :=
  .object [("children", if maxDepth == some 0 then .null else .array []), ("clientWindow", .string c.clientWindow),
    ("context", .string c.id), ("originalOpener", .null), ("parent", .null), ("url", .string c.url),
    ("userContext", .string "default")]

def getTree (env : Env) (p : Json) : Except Error Json := do
  let maxDepth ← match p.field? "maxDepth" with
    | none | some .null => pure none
    | some j => match jsUint j with
      | some n => pure (some n)
      | none => throw (bad "maxDepth is not an integer from 0 to 2^53 - 1")
  let roots ← match p.field? "root" with
    | none | some .null => pure env.contexts
    | some (.string r) => match env.contexts.find? (·.id == r) with
      | some c => pure [c]
      | none => throw { code := .noSuchFrame, message := r ++ " is not a browsing context" }
    | some _ => throw (bad "root is not a string")
  pure (.object [("contexts", .array (roots.map (info maxDepth)))])

def navigate (env : Env) (p : Json) : Except Error (String × String × Json) := do
  let ctx ← match p.field? "context" with
    | some (.string c) => pure c
    | _ => throw (bad "context is not a string")
  let url ← match p.field? "url" with
    | some (.string u) => pure u
    | _ => throw (bad "url is not a string")
  match p.field? "wait" with
    | none => pure ()
    | some (.string w) => if ["none", "interactive", "complete"].contains w then pure () else throw (bad "wait is not none, interactive or complete")
    | some _ => throw (bad "wait is not a string")
  unless env.contexts.any (·.id == ctx) do throw { code := .noSuchFrame, message := ctx ++ " is not a browsing context" }
  let parsed ← match L4Factoidal.WHATWG.URL.parseUrl url with
    | some u => pure u
    | none => throw (bad "url is not an absolute URL")
  if env.entropy.size < Gate.secretBytes then throw { code := .unknownError, message := "no entropy for an id" }
  pure (ctx, parsed.href, .object [("navigation", .string (uuid4 env.entropy)), ("url", .string parsed.href)])

/-- The new state after a command that succeeded. -/
structure Result where
  srv : Protocol.Server
  st : State
  conn : Conn
  value : Json
  effect : Effect := .none

/-- `session.new` on a BiDi-only connection: a session with no HTTP flag. -/
def newSession (env : Env) (srv : Protocol.Server) (_st : State) (conn : Conn) (p : Json) : Except Error Result := do
  if conn.session.isSome then throw { code := .sessionNotCreated, message := "the connection has a session" }
  if srv.session.isSome then throw { code := .sessionNotCreated, message := "a session is active" }
  if env.entropy.size < Gate.secretBytes then throw { code := .sessionNotCreated, message := "no entropy for a session id" }
  let caps ← match Protocol.processCapabilities env.browser p with
    | .ok c => pure c
    | .error e => throw { code := if e.code == .sessionNotCreated then .sessionNotCreated else .invalidArgument, message := e.message }
  let id := Protocol.sessionIdOf env.entropy
  let caps := caps.map fun (k, x) => if k == "webSocketUrl" then (k, Json.string (env.browser.socketBase ++ "/session/" ++ id)) else (k, x)
  pure { srv := { srv with session := some { id := id, capabilities := caps, http := false } }, st := { session := some { id := id } }, conn := { session := some id }, value := .object [("sessionId", .string id), ("capabilities", .object caps)] }

/-- One command. -/
def exec (env : Env) (srv : Protocol.Server) (st : State) (conn : Conn) (c : Command) : Except Error Result :=
  if c.method == "session.status" then
    .ok { srv := srv, st := st, conn := conn, value := .object [("ready", .bool srv.session.isNone), ("message", .string (if srv.session.isNone then "ready" else "a session is active"))] }
  else if c.method == "session.new" then newSession env srv st conn c.params
  else match liveSession srv conn with
    | none => .error { code := .invalidSessionId, message := "no session" }
    | some live =>
      let s : Session := match st.session with
        | some b => if b.id == live.id then b else { id := live.id }
        | none => { id := live.id }
      if c.method == "session.end" then
        .ok { srv := { srv with session := none }, st := {}, conn := conn, value := .object [], effect := .close }
      else if c.method == "session.subscribe" then
        (subscribe env s c.params).map fun (s, v) => { srv := srv, st := { session := some s }, conn := conn, value := v }
      else if c.method == "session.unsubscribe" then
        (unsubscribe s c.params).map fun s => { srv := srv, st := { session := some s }, conn := conn, value := .object [] }
      else if c.method == "browsingContext.getTree" then
        (getTree env c.params).map fun v => { srv := srv, st := st, conn := conn, value := v }
      else if c.method == "browsingContext.navigate" then
        (navigate env c.params).map fun (ctx, url, v) => { srv := srv, st := st, conn := conn, value := v, effect := .navigate ctx url }
      else .error { code := .unknownCommand, message := c.method ++ " is not implemented in Foafnaut yet (https://github.com/danbri/factoidal-core/issues/1203)" }

/-- What `handle` answers: a message and what to do after it, or nothing. -/
inductive Outcome where
  | reply (message : Json) (effect : Effect)
  /-- the connection's session has ended: no answer (step 5) -/
  | silent
  deriving Inhabited

/-- "Handle an incoming message". -/
def handle (env : Env) (srv : Protocol.Server) (st : State) (conn : Conn) (frame : Frame) :
    Protocol.Server × State × Conn × Outcome :=
  match frame with
  | .binary => (srv, st, conn, .reply (errorMessage none (bad "a binary frame")) .none)
  | .text text =>
    match parseJson text with
    | .error _ => (srv, st, conn, .reply (errorMessage none (bad "the message is not JSON")) .none)
    | .ok j =>
      if conn.session.isSome && (liveSession srv conn).isNone then (srv, st, conn, .silent) else
      match parseMessage j with
      | .error (id, e) => (srv, st, conn, .reply (errorMessage id e) .none)
      | .ok c =>
        match exec env srv st conn c with
        | .error e => (srv, st, conn, .reply (errorMessage (some c.id) e) .none)
        | .ok r => (r.srv, r.st, r.conn, .reply (successMessage c.id r.value) r.effect)

/-- Whether an event in a context goes to the session (stage 1 sends none). -/
def subscribed (s : Session) (event context : String) : Bool :=
  s.subscriptions.any fun x => x.events.contains event && (x.global || x.contexts.contains context)

/-! ## Connecting -/

/-- An upgrade request: the gate first, then the resource. 403: the gate refused; 404: no such
resource (the specification: "act as if the requested service is not available"). -/
def connect (cfg : Gate.Config) (srv : Protocol.Server) (st : State) (r : Gate.Request) :
    Protocol.Server × State × Except Nat Conn :=
  match Gate.admit cfg srv.gate r with
  | (gate, .error _) => ({ srv with gate }, st, .error 403)
  | (gate, .ok segs) =>
    let srv := { srv with gate }
    match segs with
    | ["session"] => (srv, st, .ok {})
    | ["session", sid] =>
      match srv.session with
      | some s =>
        if Gate.sameText sid s.id && s.http && (s.capabilities.find? (·.1 == "webSocketUrl")).isSome then
          (srv, (if st.session.map (·.id) == some s.id then st else { session := some { id := s.id } }), .ok { session := some s.id })
        else (srv, st, .error 404)
      | none => (srv, st, .error 404)
    | _ => (srv, st, .error 404)

/-! ## Theorems -/

/-- Refused upgrade. Says: when the gate refuses the upgrade request (no secret, an `Origin`, a
foreign `Host`, the lock), no connection is made, the session and the BiDi state are as before,
and the answer is 403. Does not say: that the host closes the socket (host plumbing). -/
theorem connect_refused (cfg : Gate.Config) (srv : Protocol.Server) (st : State) (r : Gate.Request)
    (gate : Gate.State) (why : Gate.Refusal) (h : Gate.admit cfg srv.gate r = (gate, .error why)) :
    (connect cfg srv st r).1.session = srv.session ∧ (connect cfg srv st r).2.1 = st ∧
      (connect cfg srv st r).2.2 = .error 403 := by
  simp [connect, h]

/-- No secret. Says: an upgrade whose path does not start with the secret makes no connection.
Does not say: more than `connect_refused` with `Gate.admit_no_secret`. -/
theorem connect_no_secret (cfg : Gate.Config) (srv : Protocol.Server) (st : State) (r : Gate.Request)
    (h : (Gate.splitPath r.path).1 ≠ cfg.secret) :
    (connect cfg srv st r).1.session = srv.session ∧ (connect cfg srv st r).2.2 = .error 403 := by
  obtain ⟨g, why, ha⟩ := Gate.admit_no_secret cfg srv.gate r h
  have := connect_refused cfg srv st r g why ha
  exact ⟨this.1, this.2.2⟩

/-- Pages. Says: an upgrade with an `Origin` header (every WebSocket a page opens) makes no
connection, even with the secret. Does not say: anything of a client that sends no `Origin`. -/
theorem connect_origin (cfg : Gate.Config) (srv : Protocol.Server) (st : State) (r : Gate.Request)
    (o : String) (h : r.origin = some o) :
    (connect cfg srv st r).1.session = srv.session ∧ (connect cfg srv st r).2.2 = .error 403 := by
  obtain ⟨g, why, ha⟩ := Gate.admit_origin cfg srv.gate r o h
  have := connect_refused cfg srv st r g why ha
  exact ⟨this.1, this.2.2⟩

/-- Unknown command. Says: a message whose `method` is a string that names no command of the
specification is answered `unknown command`, whatever else it holds. Does not say: which id the
answer carries (the message's `id` when it is a `js-uint`). -/
theorem parseMessage_unknown (j : Json) (m : String) (hm : j.field? "method" = some (.string m))
    (hc : commandNames.contains m = false) :
    ∃ id msg, parseMessage j = .error (id, { code := .unknownCommand, message := msg }) := by
  have hn : m ∉ commandNames := by simpa using hc
  simp [parseMessage, hm, hn]

/-- No session. Says: when the connection has no live session, every command but
`session.status` and `session.new` is `invalid session id`. Does not say: anything of a
connection whose session has ended (`handle` gives it no answer at all). -/
theorem exec_no_session (env : Env) (srv : Protocol.Server) (st : State) (conn : Conn) (c : Command)
    (h1 : c.method ≠ "session.status") (h2 : c.method ≠ "session.new") (hs : liveSession srv conn = none) :
    ∃ msg, exec env srv st conn c = .error { code := .invalidSessionId, message := msg } := by
  simp [exec, h1, h2, hs]

/-- Errors change nothing. Says: a message that is answered with an error message (of any kind:
not JSON, not a command, no session, bad parameters) leaves the protocol server, the BiDi state
and the connection exactly as they were. Does not say: that the error code is the right one. -/
theorem handle_error_keeps (env : Env) (srv : Protocol.Server) (st : State) (conn : Conn) (f : Frame)
    (m : Json) (eff : Effect) (h : (handle env srv st conn f).2.2.2 = .reply m eff)
    (he : m.field? "type" = some (.string "error")) :
    (handle env srv st conn f).1 = srv ∧ (handle env srv st conn f).2.1 = st ∧ (handle env srv st conn f).2.2.1 = conn := by
  unfold handle at h ⊢
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl⟩
    | (simp_all [successMessage, Json.field?]; obtain ⟨h1, _⟩ := h; subst h1; simp at he)
    | (simp_all [successMessage, Json.field?]; done)

/-- Binary frames. Says: a binary frame is answered `invalid argument` with id null and changes
nothing. -/
theorem handle_binary (env : Env) (srv : Protocol.Server) (st : State) (conn : Conn) :
    handle env srv st conn .binary =
      (srv, st, conn, .reply (errorMessage none { code := .invalidArgument, message := "a binary frame" }) .none) := rfl

/-! ## Tests -/

private def cfg : Gate.Config := { secret := "00112233445566778899aabbccddeeff", port := 4444 }
private def entropy : ByteArray := ByteArray.mk ((Array.range 16).map (·.toUInt8))
private def env : Env := {
  browser := { version := "0.36", socketBase := "ws://127.0.0.1:4444/00112233445566778899aabbccddeeff" },
  contexts := [{ id := "foafnaut-window-1", url := "about:blank", clientWindow := "foafnaut-window-1" }], entropy }
private def sid : String := "00010203-0405-0607-0809-0a0b0c0d0e0f"
/-- A classic session that asked for `webSocketUrl`, and its connection. -/
private def classic : Protocol.Server :=
  (Protocol.handle cfg env.browser {} { method := "POST", path := "/00112233445566778899aabbccddeeff/session", host := "127.0.0.1:4444", body := "{\"capabilities\":{\"alwaysMatch\":{\"webSocketUrl\":true}}}", entropy }).1
private def up (srv : Protocol.Server) (path : String) (origin : Option String := none) : Protocol.Server × State × Except Nat Conn :=
  connect cfg srv {} { path := "/00112233445566778899aabbccddeeff" ++ path, host := "127.0.0.1:4444", origin }
private def conn : Conn := { session := some sid }
private def send (srv : Protocol.Server) (st : State) (c : Conn) (text : String) : Protocol.Server × State × Conn × Outcome :=
  handle env srv st c (.text text)
private def msgOf : Outcome → Json
  | .reply m _ => m
  | .silent => .null
private def errorOf (o : Outcome) : String :=
  match (msgOf o).field? "error" with
  | some (.string e) => e
  | _ => ""
private def typeOf (o : Outcome) : String :=
  match (msgOf o).field? "type" with
  | some (.string e) => e
  | _ => ""
private def idOf (o : Outcome) : Json := ((msgOf o).field? "id").getD (.string "absent")
private def resultOf (o : Outcome) : Json := ((msgOf o).field? "result").getD .null
private def cmd (id : Nat) (method params : String) : String :=
  "{\"id\":" ++ toString id ++ ",\"method\":\"" ++ method ++ "\",\"params\":" ++ params ++ "}"
private def live : State := (connect cfg classic {} { path := "/00112233445566778899aabbccddeeff/session/" ++ sid, host := "127.0.0.1:4444" }).2.1
private def ask (method params : String) (st : State := live) : Protocol.Server × State × Conn × Outcome :=
  send classic st conn (cmd 1 method params)

-- webSocketUrl: the classic session's URL holds the secret and the session id
#guard (classic.session.bind fun s => (s.capabilities.find? (·.1 == "webSocketUrl")).map (·.2)) ==
  some (.string ("ws://127.0.0.1:4444/00112233445566778899aabbccddeeff/session/" ++ sid))
-- connect: the gate, then the resource
#guard (up classic ("/session/" ++ sid)).2.2.toOption == some conn
#guard (up {} "/session").2.2.toOption == some {}
#guard (up classic "/session/nope").2.2 == .error 404
#guard (up {} ("/session/" ++ sid)).2.2 == .error 404
#guard (up classic "/other").2.2 == .error 404
#guard (up classic ("/session/" ++ sid) (some "https://evil.example")).2.2 == .error 403
#guard (connect cfg classic {} { path := "/session/" ++ sid, host := "127.0.0.1:4444" }).2.2 == .error 403
#guard (connect cfg classic {} { path := "/00112233445566778899aabbccddeeff/session/" ++ sid, host := "evil.example:4444" }).2.2 == .error 403
-- refusals count in the gate shared with classic requests
#guard (connect cfg classic {} { path := "/session", host := "127.0.0.1:4444" }).1.gate.failures == 1
-- a classic session without webSocketUrl gets no connection
private def plain : Protocol.Server :=
  (Protocol.handle cfg env.browser {} { method := "POST", path := "/00112233445566778899aabbccddeeff/session", host := "127.0.0.1:4444", body := "{\"capabilities\":{}}", entropy }).1
#guard (up plain ("/session/" ++ sid)).2.2 == .error 404
-- bidi/errors/errors.py: unknown commands; message errors
#guard errorOf (ask "invalidmodule.somecommand" "{}").2.2.2 == "unknown command"
#guard errorOf (ask "session.wrongcommand" "{}").2.2.2 == "unknown command"
#guard idOf (ask "session.wrongcommand" "{}").2.2.2 == .number "1"
#guard errorOf (handle env classic live conn .binary).2.2.2 == "invalid argument"
#guard idOf (handle env classic live conn .binary).2.2.2 == .null
#guard errorOf (send classic live conn "not json").2.2.2 == "invalid argument"
#guard errorOf (send classic live conn "[1,2]").2.2.2 == "invalid argument"
#guard errorOf (send classic live conn "{\"id\":-1,\"method\":\"session.status\",\"params\":{}}").2.2.2 == "invalid argument"
#guard idOf (send classic live conn "{\"id\":-1,\"method\":\"session.status\",\"params\":{}}").2.2.2 == .null
#guard errorOf (send classic live conn "{\"id\":7,\"method\":\"session.status\"}").2.2.2 == "invalid argument"
#guard idOf (send classic live conn "{\"id\":7,\"method\":\"session.status\"}").2.2.2 == .number "7"
#guard errorOf (send classic live conn "{\"id\":7,\"method\":\"nope.nope\"}").2.2.2 == "unknown command"
#guard errorOf (send classic live conn "{\"id\":7,\"method\":\"session.status\",\"params\":[]}").2.2.2 == "invalid argument"
-- session.status
#guard typeOf (ask "session.status" "{}").2.2.2 == "success"
#guard resultOf (ask "session.status" "{}").2.2.2 == .object [("ready", .bool false), ("message", .string "a session is active")]
#guard resultOf (send {} {} {} (cmd 2 "session.status" "{}")).2.2.2 == .object [("ready", .bool true), ("message", .string "ready")]
-- no session: only the static commands
#guard errorOf (send {} {} {} (cmd 2 "browsingContext.getTree" "{}")).2.2.2 == "invalid session id"
#guard errorOf (send {} {} {} (cmd 2 "session.subscribe" "{\"events\":[\"log\"]}")).2.2.2 == "invalid session id"
-- a connection whose session ended gets no answer
#guard match (send {} {} conn (cmd 2 "session.status" "{}")).2.2.2 with | .silent => true | _ => false
-- session.new on a BiDi-only connection
private def made : Protocol.Server × State × Conn × Outcome := send {} {} {} (cmd 3 "session.new" "{\"capabilities\":{}}")
#guard typeOf made.2.2.2 == "success"
#guard made.2.2.1 == conn
#guard (made.1.session.map (·.http)) == some false
#guard ((resultOf made.2.2.2).field? "sessionId") == some (.string sid)
#guard errorOf (send made.1 made.2.1 made.2.2.1 (cmd 4 "session.new" "{\"capabilities\":{}}")).2.2.2 == "session not created"
#guard errorOf (send classic {} {} (cmd 4 "session.new" "{\"capabilities\":{}}")).2.2.2 == "session not created"
#guard errorOf (send {} {} {} (cmd 4 "session.new" "{}")).2.2.2 == "invalid argument"
#guard errorOf (send {} {} {} (cmd 4 "session.new" "{\"capabilities\":{\"alwaysMatch\":{\"browserName\":\"other\"}}}")).2.2.2 == "session not created"
#guard typeOf (send made.1 made.2.1 made.2.2.1 (cmd 5 "browsingContext.getTree" "{}")).2.2.2 == "success"
-- session.end
#guard (ask "session.end" "{}").1.session.isNone
#guard (match (ask "session.end" "{}").2.2.2 with | .reply _ e => e == .close | _ => false)
#guard resultOf (ask "session.end" "{}").2.2.2 == .object []
-- session.subscribe (bidi/session/subscribe/invalid.py)
private def subErr (params : String) : String := errorOf (ask "session.subscribe" params).2.2.2
#guard subErr "{}" == "invalid argument"
#guard subErr "{\"events\":null}" == "invalid argument" && subErr "{\"events\":true}" == "invalid argument"
#guard subErr "{\"events\":\"foo\"}" == "invalid argument" && subErr "{\"events\":{}}" == "invalid argument"
#guard subErr "{\"events\":[]}" == "invalid argument"
#guard subErr "{\"events\":[null]}" == "invalid argument" && subErr "{\"events\":[[]]}" == "invalid argument"
#guard subErr "{\"events\":[\"\"]}" == "invalid argument" && subErr "{\"events\":[\"foo\"]}" == "invalid argument"
#guard subErr "{\"events\":[\"foo.bar\"]}" == "invalid argument" && subErr "{\"events\":[\"log.invalidEvent\"]}" == "invalid argument"
#guard subErr "{\"events\":[\"log.entryAdded\",\"some.invalidEvent\"]}" == "invalid argument"
#guard (ask "session.subscribe" "{\"events\":[\"log.entryAdded\",\"some.invalidEvent\"]}").2.1 == live
#guard subErr "{\"events\":[\"log.entryAdded\"],\"contexts\":[]}" == "invalid argument"
#guard subErr "{\"events\":[\"log.entryAdded\"],\"contexts\":\"foo\"}" == "invalid argument"
#guard subErr "{\"events\":[\"log.entryAdded\"],\"contexts\":[42]}" == "invalid argument"
#guard subErr "{\"events\":[\"log.entryAdded\"],\"contexts\":[\"foo\"]}" == "no such frame"
#guard subErr "{\"events\":[\"log.entryAdded\"],\"contexts\":[\"foafnaut-window-1\",\"foo\"]}" == "no such frame"
#guard subErr "{\"events\":[\"browsingContext.load\"],\"userContexts\":[]}" == "invalid argument"
#guard subErr "{\"events\":[\"browsingContext.load\"],\"userContexts\":[\"foo\"]}" == "no such user context"
#guard subErr "{\"events\":[\"browsingContext.load\"],\"userContexts\":[\"default\"],\"contexts\":[\"foafnaut-window-1\"]}" == "invalid argument"
private def subbed : Protocol.Server × State × Conn × Outcome := ask "session.subscribe" "{\"events\":[\"log\"]}"
#guard ((resultOf subbed.2.2.2).field? "subscription") == some (.string "00010203-0405-4607-8809-0a0b0c0d0e0f")
#guard (subbed.2.1.session.map fun s => subscribed s "log.entryAdded" "foafnaut-window-1") == some true
#guard (subbed.2.1.session.map fun s => subscribed s "browsingContext.load" "foafnaut-window-1") == some false
-- session.unsubscribe (bidi/session/unsubscribe/invalid.py)
private def unsubErr (st : State) (params : String) : String := errorOf (ask "session.unsubscribe" params st).2.2.2
#guard unsubErr live "{}" == "invalid argument"
#guard unsubErr live "{\"events\":[]}" == "invalid argument" && unsubErr live "{\"events\":[\"foo.bar\"]}" == "invalid argument"
#guard unsubErr live "{\"events\":[\"log.entryAdded\"]}" == "invalid argument"
#guard unsubErr subbed.2.1 "{\"events\":[\"log.entryAdded\",\"some.invalidEvent\"]}" == "invalid argument"
#guard unsubErr live "{\"subscriptions\":[\"\"]}" == "invalid argument"
#guard unsubErr live "{\"subscriptions\":[\"12345678-1234-5678-1234-567812345678\"]}" == "invalid argument"
#guard unsubErr live "{\"subscriptions\":\"foo\"}" == "invalid argument" && unsubErr live "{\"subscriptions\":[42]}" == "invalid argument"
#guard ((ask "session.unsubscribe" "{\"subscriptions\":[\"00010203-0405-4607-8809-0a0b0c0d0e0f\"]}" subbed.2.1).2.1.session.map (·.subscriptions)) == some []
#guard ((ask "session.unsubscribe" "{\"events\":[\"log.entryAdded\"]}" subbed.2.1).2.1.session.map (·.subscriptions)) == some []
-- by events: one event out of a module, then the module is refused
private def bc : State := (ask "session.subscribe" "{\"events\":[\"browsingContext\"]}").2.1
private def bc1 : State := (ask "session.unsubscribe" "{\"events\":[\"browsingContext.domContentLoaded\"]}" bc).2.1
#guard (bc1.session.map fun s => subscribed s "browsingContext.domContentLoaded" "x") == some false
#guard (bc1.session.map fun s => subscribed s "browsingContext.load" "x") == some true
#guard unsubErr bc1 "{\"events\":[\"browsingContext\"]}" == "invalid argument"
-- an event subscribed for one context is not unsubscribed globally
private def perCtx : State := (ask "session.subscribe" "{\"events\":[\"log.entryAdded\"],\"contexts\":[\"foafnaut-window-1\"]}").2.1
#guard unsubErr perCtx "{\"events\":[\"log.entryAdded\"]}" == "invalid argument"
-- browsingContext.getTree (bidi/browsing_context/get_tree)
private def treeErr (params : String) : String := errorOf (ask "browsingContext.getTree" params).2.2.2
#guard treeErr "{\"maxDepth\":false}" == "invalid argument" && treeErr "{\"maxDepth\":\"foo\"}" == "invalid argument"
#guard treeErr "{\"maxDepth\":-1}" == "invalid argument" && treeErr "{\"maxDepth\":1.1}" == "invalid argument"
#guard treeErr "{\"maxDepth\":9007199254740992}" == "invalid argument"
#guard treeErr "{\"root\":false}" == "invalid argument" && treeErr "{\"root\":42}" == "invalid argument"
#guard treeErr "{\"root\":\"foo\"}" == "no such frame"
#guard resultOf (ask "browsingContext.getTree" "{}").2.2.2 == .object [("contexts", .array [.object [("children", .array []),
  ("clientWindow", .string "foafnaut-window-1"), ("context", .string "foafnaut-window-1"), ("originalOpener", .null),
  ("parent", .null), ("url", .string "about:blank"), ("userContext", .string "default")]])]
#guard ((resultOf (ask "browsingContext.getTree" "{\"maxDepth\":0}").2.2.2).field? "contexts") ==
  some (.array [info (some 0) env.contexts.head!])
#guard ((resultOf (ask "browsingContext.getTree" "{\"root\":\"foafnaut-window-1\"}").2.2.2).field? "contexts") ==
  some (.array [info none env.contexts.head!])
-- browsingContext.navigate (bidi/browsing_context/navigate/invalid.py)
private def navErr (params : String) : String := errorOf (ask "browsingContext.navigate" params).2.2.2
#guard navErr "{\"context\":null,\"url\":\"http://a.test/\"}" == "invalid argument"
#guard navErr "{\"context\":42,\"url\":\"http://a.test/\"}" == "invalid argument"
#guard navErr "{\"context\":\"\",\"url\":\"http://a.test/\"}" == "no such frame"
#guard navErr "{\"context\":\"somestring\",\"url\":\"http://a.test/\"}" == "no such frame"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":null}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"1foo://\"}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"http://foo bar\"}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"http://localhost:-1\"}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"http://:80\"}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"/foo\"}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"http://#foo\"}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"http://a.test/\",\"wait\":false}" == "invalid argument"
#guard navErr "{\"context\":\"foafnaut-window-1\",\"url\":\"http://a.test/\",\"wait\":\"somestring\"}" == "invalid argument"
private def nav : Protocol.Server × State × Conn × Outcome :=
  ask "browsingContext.navigate" "{\"context\":\"foafnaut-window-1\",\"url\":\"http://a.test/x?y=1\",\"wait\":\"complete\"}"
#guard ((resultOf nav.2.2.2).field? "url") == some (.string "http://a.test/x?y=1")
#guard ((resultOf nav.2.2.2).field? "navigation") == some (.string "00010203-0405-4607-8809-0a0b0c0d0e0f")
#guard (match nav.2.2.2 with | .reply _ e => e == .navigate "foafnaut-window-1" "http://a.test/x?y=1" | _ => false)

/-! ## Expected failures (https://github.com/danbri/factoidal-core/issues/1203)

Each `#guard` below holds today's result, which the specification does not want. It fails when
the behaviour changes: then replace it with the right assertion and tick the issue's item. -/

-- 1203 item 2: browsingContext.create is not implemented (the WPT fixture new_tab needs it)
#guard errorOf (ask "browsingContext.create" "{\"type\":\"tab\"}").2.2.2 == "unknown command"
-- 1203 item 3: a subscription is kept, but no command gives an event to send
#guard (match nav.2.2.2 with | .reply _ (.navigate _ _) => true | _ => false)
-- 1203 item 5: wait "none" gives the same effect as "complete" (the host waits for the load)
#guard (match (ask "browsingContext.navigate" "{\"context\":\"foafnaut-window-1\",\"url\":\"http://a.test/\",\"wait\":\"none\"}").2.2.2 with
  | .reply _ (.navigate _ _) => true | _ => false)

end L4Factoidal.WebDriver.BiDi
