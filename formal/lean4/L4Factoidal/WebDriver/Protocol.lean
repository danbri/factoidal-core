/-
L4Factoidal.WebDriver.Protocol: the WebDriver protocol up to the page (W3C WebDriver §6
to §9): which command a request is, whether its session exists, session creation with
capabilities processing, timeouts, and the form of every response.

The listener (host plumbing) reads an HTTP request and gives its method, path, `Host`
and `Origin` headers and body to `handle`. `handle` answers with a response (status and
JSON body), or says that the command needs the page (`Outcome.page`): the engine then
runs it on the session's page (`labs/demos/foafnaut/WebDriverPage.lean`) and its result
is wrapped by `successBody` or `Error.body`. Every decision of the protocol is here or
there; the listener decides nothing.

- `endpoints`: the table of §6.2 (method, path template, command).
- `route`: the command of a request; `unknown command` (404) for a path of no endpoint,
  `unknown method` (405) for an endpoint's path with another method.
- `handle`: the gate first (`Gate.admit`: a refused request changes nothing but the
  gate's count), then the route, then the session check (`invalid session id`), then New
  Session, Delete Session, Status, Get Timeouts and Set Timeouts here; the rest to the
  page.
- Capabilities processing (§7.2): validation, merging `alwaysMatch` with each
  `firstMatch`, matching against this browser.

Proved: `endpoints_nodup` (no two endpoints share a method and path template),
`endpoints_session` (every endpoint but Status and New Session is under
`session/{session id}`), `route_error` (a request with no endpoint answers 404 or 405),
`handle_refused` (a request the gate refuses changes no session and nothing of the page),
`handle_no_secret` (the same for any request without the secret), `handle_no_session`
(with no session, a command that needs one answers `invalid session id` and changes
nothing).
Tested: `#guard`s from `webdriver/tests/classic/new_session` and `set_timeouts`; that the
timeouts a session reports read back as themselves.
-/
import L4Factoidal.WebDriver.Errors
import L4Factoidal.WebDriver.Gate
import L4Factoidal.JSON.Parser

namespace L4Factoidal.WebDriver.Protocol
open L4Factoidal.JSON

/-! ## Commands and endpoints (§6.2) -/

inductive Command where
  | status | newSession | deleteSession | getTimeouts | setTimeouts
  | navigateTo | getCurrentUrl | back | forward | refresh | getTitle
  | getWindowHandle | closeWindow | switchToWindow | getWindowHandles | newWindow
  | switchToFrame | switchToParentFrame
  | getWindowRect | setWindowRect | maximizeWindow | minimizeWindow | fullscreenWindow
  | getActiveElement | getElementShadowRoot
  | findElement | findElements | findElementFromElement | findElementsFromElement
  | findElementFromShadowRoot | findElementsFromShadowRoot
  | isElementSelected | getElementAttribute | getElementProperty | getElementCssValue
  | getElementText | getElementTagName | getElementRect | isElementEnabled
  | getComputedRole | getComputedLabel
  | elementClick | elementClear | elementSendKeys
  | getPageSource | executeScript | executeAsyncScript
  | getAllCookies | getNamedCookie | addCookie | deleteCookie | deleteAllCookies
  | performActions | releaseActions
  | dismissAlert | acceptAlert | getAlertText | sendAlertText
  | takeScreenshot | takeElementScreenshot | printPage
  deriving DecidableEq, Repr, Inhabited

/-- A segment of a path template: a fixed word or a parameter. -/
inductive Seg where
  | lit (s : String)
  | var
  deriving DecidableEq, Repr, Inhabited

private def l (s : String) : Seg := .lit s
private def v : Seg := .var
/-- `session/{session id}` and the rest. -/
private def s (rest : List Seg) : List Seg := l "session" :: v :: rest
private def el (rest : List Seg) : List Seg := s (l "element" :: v :: rest)

/-- The endpoints of WebDriver §6.2: method, path template, command. -/
def endpoints : List (String × List Seg × Command) := [
  ("GET", [l "status"], .status),
  ("POST", [l "session"], .newSession),
  ("DELETE", s [], .deleteSession),
  ("GET", s [l "timeouts"], .getTimeouts),
  ("POST", s [l "timeouts"], .setTimeouts),
  ("POST", s [l "url"], .navigateTo),
  ("GET", s [l "url"], .getCurrentUrl),
  ("POST", s [l "back"], .back),
  ("POST", s [l "forward"], .forward),
  ("POST", s [l "refresh"], .refresh),
  ("GET", s [l "title"], .getTitle),
  ("GET", s [l "window"], .getWindowHandle),
  ("DELETE", s [l "window"], .closeWindow),
  ("POST", s [l "window"], .switchToWindow),
  ("GET", s [l "window", l "handles"], .getWindowHandles),
  ("POST", s [l "window", l "new"], .newWindow),
  ("POST", s [l "frame"], .switchToFrame),
  ("POST", s [l "frame", l "parent"], .switchToParentFrame),
  ("GET", s [l "window", l "rect"], .getWindowRect),
  ("POST", s [l "window", l "rect"], .setWindowRect),
  ("POST", s [l "window", l "maximize"], .maximizeWindow),
  ("POST", s [l "window", l "minimize"], .minimizeWindow),
  ("POST", s [l "window", l "fullscreen"], .fullscreenWindow),
  ("GET", s [l "element", l "active"], .getActiveElement),
  ("GET", el [l "shadow"], .getElementShadowRoot),
  ("POST", s [l "element"], .findElement),
  ("POST", s [l "elements"], .findElements),
  ("POST", el [l "element"], .findElementFromElement),
  ("POST", el [l "elements"], .findElementsFromElement),
  ("POST", s [l "shadow", v, l "element"], .findElementFromShadowRoot),
  ("POST", s [l "shadow", v, l "elements"], .findElementsFromShadowRoot),
  ("GET", el [l "selected"], .isElementSelected),
  ("GET", el [l "attribute", v], .getElementAttribute),
  ("GET", el [l "property", v], .getElementProperty),
  ("GET", el [l "css", v], .getElementCssValue),
  ("GET", el [l "text"], .getElementText),
  ("GET", el [l "name"], .getElementTagName),
  ("GET", el [l "rect"], .getElementRect),
  ("GET", el [l "enabled"], .isElementEnabled),
  ("GET", el [l "computedrole"], .getComputedRole),
  ("GET", el [l "computedlabel"], .getComputedLabel),
  ("POST", el [l "click"], .elementClick),
  ("POST", el [l "clear"], .elementClear),
  ("POST", el [l "value"], .elementSendKeys),
  ("GET", s [l "source"], .getPageSource),
  ("POST", s [l "execute", l "sync"], .executeScript),
  ("POST", s [l "execute", l "async"], .executeAsyncScript),
  ("GET", s [l "cookie"], .getAllCookies),
  ("GET", s [l "cookie", v], .getNamedCookie),
  ("POST", s [l "cookie"], .addCookie),
  ("DELETE", s [l "cookie", v], .deleteCookie),
  ("DELETE", s [l "cookie"], .deleteAllCookies),
  ("POST", s [l "actions"], .performActions),
  ("DELETE", s [l "actions"], .releaseActions),
  ("POST", s [l "alert", l "dismiss"], .dismissAlert),
  ("POST", s [l "alert", l "accept"], .acceptAlert),
  ("GET", s [l "alert", l "text"], .getAlertText),
  ("POST", s [l "alert", l "text"], .sendAlertText),
  ("GET", s [l "screenshot"], .takeScreenshot),
  ("GET", el [l "screenshot"], .takeElementScreenshot),
  ("POST", s [l "print"], .printPage)]

/-- The parameters of a path that fits a template. -/
def matchPath : List Seg → List String → Option (List String)
  | [], [] => some []
  | .lit a :: ps, x :: xs => if a == x then matchPath ps xs else none
  | .var :: ps, x :: xs => (matchPath ps xs).map (x :: ·)
  | _, _ => none

/-- A request's command, with its session id and the other path parameters. -/
structure Routed where
  command : Command
  session : Option String := none
  params : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- The template is under `session/{session id}`. -/
def underSession : List Seg → Bool
  | .lit "session" :: .var :: _ => true
  | _ => false

def route (method : String) (segs : List String) : Except Error Routed :=
  match endpoints.findSome? (fun e => if e.1 == method then (matchPath e.2.1 segs).map (fun vars => (e, vars)) else none) with
  | some (e, vars) =>
    .ok (if underSession e.2.1 then { command := e.2.2, session := vars.head?, params := vars.drop 1 }
         else { command := e.2.2, params := vars })
  | none =>
    if endpoints.any (fun e => (matchPath e.2.1 segs).isSome) then
      .error { code := .unknownMethod, message := method ++ " is not a method of this endpoint" }
    else .error { code := .unknownCommand, message := "no endpoint at /" ++ "/".intercalate segs }

/-! ## Numbers -/

/-- A JSON number that is an integer from 0 to 2^53 - 1 (a "safe integer"; a fraction of
zeros is allowed, as `2.0`), as a `Nat`. The bound is checked on the digits, so no number
above it is ever made. -/
def safeInteger : Json → Option Nat
  | .number n =>
    let cs := n.toList
    let whole := cs.takeWhile Char.isDigit
    let rest := cs.dropWhile Char.isDigit
    let fracOk := match rest with
      | [] => true
      | '.' :: f => !f.isEmpty && f.all (· == '0')
      | _ => false
    let digits := whole.dropWhile (· == '0')
    let max := "9007199254740991".toList
    if whole.isEmpty || !fracOk then none
    else if digits.length < max.length || (digits.length == max.length && String.ofList digits ≤ String.ofList max) then
      some (digits.foldl (fun k c => k * 10 + (c.toNat - 48)) 0)
    else none
  | _ => none

/-! ## Timeouts (§9) -/

structure Timeouts where
  /-- `none`: no script timeout (JSON null). -/
  script : Option Nat := some 30000
  pageLoad : Nat := 300000
  implicit : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def Timeouts.toJson (t : Timeouts) : Json :=
  .object [("script", match t.script with | some n => .number (toString n) | none => .null),
    ("pageLoad", .number (toString t.pageLoad)), ("implicit", .number (toString t.implicit))]

/-- "Deserialize as timeouts" (§9): an object whose members are `script` (null or a safe
integer), `pageLoad` and `implicit` (safe integers); any other member is refused. -/
def Timeouts.merge (t : Timeouts) (j : Json) : Except Error Timeouts :=
  match j with
  | .object fields =>
    fields.foldlM (init := t) fun t (k, val) =>
      if k == "script" then
        match val, safeInteger val with
        | .null, _ => .ok { t with script := none }
        | _, some n => .ok { t with script := some n }
        | _, none => .error { code := .invalidArgument, message := "script is not null or an integer from 0 to 2^53 - 1" }
      else if k == "pageLoad" then
        match safeInteger val with
        | some n => .ok { t with pageLoad := n }
        | none => .error { code := .invalidArgument, message := "pageLoad is not an integer from 0 to 2^53 - 1" }
      else if k == "implicit" then
        match safeInteger val with
        | some n => .ok { t with implicit := n }
        | none => .error { code := .invalidArgument, message := "implicit is not an integer from 0 to 2^53 - 1" }
      else .error { code := .invalidArgument, message := k ++ " is not a timeout" }
  | _ => .error { code := .invalidArgument, message := "timeouts is not an object" }

/-! ## Capabilities (§7) -/

/-- What this browser is, for matching. -/
structure Browser where
  name : String := "foafnaut"
  version : String := ""
  platform : String := "linux"
  userAgent : String := "Foafnaut"
  /-- The endpoint's address for the BiDi upgrade (`ws://host:port/secret`). -/
  socketBase : String := ""
  deriving Repr, Inhabited

def promptBehaviors : List String := ["dismiss", "accept", "dismiss and notify", "accept and notify", "ignore"]
def promptTypes : List String := ["alert", "beforeUnload", "confirm", "default", "file", "prompt"]
def proxyTypes : List String := ["pac", "direct", "autodetect", "system", "manual"]
def proxyMembers : List String := ["proxyType", "proxyAutoconfigUrl", "ftpProxy", "httpProxy", "noProxy", "sslProxy", "socksProxy", "socksVersion"]

private def badCap (name what : String) : Error := { code := .invalidArgument, message := name ++ " " ++ what }

/-- "Validate capabilities" (§7.2) for one member: its value as it is kept, or
`invalid argument`. A member that is null is left out by the caller. -/
def validateCapability (name : String) (val : Json) : Except Error Json :=
  match name with
  | "acceptInsecureCerts" | "strictFileInteractability" | "setWindowRect" | "webSocketUrl" =>
    match val with
    | .bool _ => .ok val
    | _ => .error (badCap name "is not a boolean")
  | "browserName" | "browserVersion" | "platformName" | "userAgent" =>
    match val with
    | .string _ => .ok val
    | _ => .error (badCap name "is not a string")
  | "pageLoadStrategy" =>
    match val with
    | .string v => if ["none", "eager", "normal"].contains v then .ok val else .error (badCap name "is not none, eager or normal")
    | _ => .error (badCap name "is not a string")
  | "timeouts" => (Timeouts.merge {} val).map fun _ => val
  | "unhandledPromptBehavior" =>
    match val with
    | .string v => if promptBehaviors.contains v then .ok val else .error (badCap name "is not a prompt behavior")
    | .object fields =>
      if fields.all (fun (k, x) => promptTypes.contains k && (match x with | .string b => promptBehaviors.contains b | _ => false))
      then .ok val else .error (badCap name "has a member that is not a prompt type with a prompt behavior")
    | _ => .error (badCap name "is not a string or an object")
  | "proxy" =>
    match val with
    | .object fields =>
      let typeOk := match (Json.object fields).field? "proxyType" with
        | some (.string t) => proxyTypes.contains t
        | _ => false
      if typeOk && fields.all (fun (k, _) => proxyMembers.contains k) then .ok val
      else .error (badCap name "is not a proxy configuration")
    | _ => .error (badCap name "is not an object")
  | _ =>
    -- an extension capability has a colon in its name; any other name is refused
    if name.toList.contains ':' then .ok val else .error (badCap name "is not a capability")

/-- Validate an object of capabilities: null members are dropped. -/
def validate (j : Json) : Except Error (List (String × Json)) :=
  match j with
  | .object fields =>
    fields.foldlM (init := []) fun acc (k, val) =>
      match val with
      | .null => .ok acc
      | _ => (validateCapability k val).map fun x => acc ++ [(k, x)]
  | _ => .error { code := .invalidArgument, message := "capabilities are not an object" }

/-- "Merging capabilities" (§7.2): a name in both is `invalid argument`. -/
def mergeCaps (always first : List (String × Json)) : Except Error (List (String × Json)) :=
  if first.any (fun (k, _) => always.any (·.1 == k)) then
    .error { code := .invalidArgument, message := "a capability is in alwaysMatch and in firstMatch" }
  else .ok (always ++ first)

/-- "Matching capabilities" (§7.2): the capabilities of the session, or none when this
browser is not what was asked for. -/
def matchCaps (b : Browser) (caps : List (String × Json)) : Option (List (String × Json)) :=
  let get := fun (k : String) => (caps.find? (·.1 == k)).map (·.2)
  let strOk := fun (k want : String) => match get k with
    | some (.string v) => v == want
    | _ => true
  if !strOk "browserName" b.name || !strOk "platformName" b.platform then none
  else if (match get "browserVersion" with | some (.string v) => !(v == b.version || v == "") | _ => false) then none
  else if get "acceptInsecureCerts" == some (.bool true) then none
  else if (match get "proxy" with | some (.object fs) => !fs.isEmpty | _ => false) then none
  else
    let timeouts := match get "timeouts" with
      | some t => match Timeouts.merge {} t with
        | .ok x => x
        | .error _ => {}
      | none => {}
    let extensions := caps.filter fun (k, _) => k.toList.contains ':'
    some ([("browserName", .string b.name), ("browserVersion", .string b.version), ("platformName", .string b.platform),
      ("acceptInsecureCerts", .bool false),
      ("pageLoadStrategy", (get "pageLoadStrategy").getD (.string "normal")),
      ("proxy", .object []), ("setWindowRect", .bool true),
      ("strictFileInteractability", (get "strictFileInteractability").getD (.bool false)),
      ("timeouts", timeouts.toJson),
      ("unhandledPromptBehavior", (get "unhandledPromptBehavior").getD (.string "dismiss and notify")),
      ("userAgent", .string b.userAgent)] ++
      (if get "webSocketUrl" == some (.bool true) then [("webSocketUrl", .bool true)] else []) ++ extensions)

/-- "Process capabilities" (§7.2) of a New Session request. -/
def processCapabilities (b : Browser) (parameters : Json) : Except Error (List (String × Json)) := do
  let request ← match parameters.field? "capabilities" with
    | some (.object fs) => pure (Json.object fs)
    | _ => throw { code := .invalidArgument, message := "capabilities is not an object" }
  let always ← match request.field? "alwaysMatch" with
    | none => pure []
    | some j => validate j
  let firsts ← match request.field? "firstMatch" with
    | none => pure [Json.object []]
    | some (.array xs) => if xs.isEmpty then throw { code := .invalidArgument, message := "firstMatch is empty" } else pure xs
    | some _ => throw { code := .invalidArgument, message := "firstMatch is not an array" }
  let merged ← firsts.mapM fun f => do mergeCaps always (← validate f)
  match merged.findSome? (matchCaps b) with
  | some caps => pure caps
  | none => throw { code := .sessionNotCreated, message := "no capabilities match this browser" }

/-! ## Sessions -/

structure Session where
  id : String
  capabilities : List (String × Json) := []
  timeouts : Timeouts := {}
  deriving Repr, Inhabited

/-- The session id of 16 bytes of the machine's generator: a UUID's 32 hexadecimal digits
in its five groups. -/
def sessionIdOf (entropy : ByteArray) : String :=
  let hex := (Gate.secretOf entropy).toList
  String.ofList (hex.take 8 ++ ['-'] ++ (hex.drop 8).take 4 ++ ['-'] ++ (hex.drop 12).take 4 ++ ['-'] ++
    (hex.drop 16).take 4 ++ ['-'] ++ hex.drop 20)

/-- The protocol's state: the gate, and the one session there may be. -/
structure Server where
  gate : Gate.State := {}
  session : Option Session := none
  deriving Repr, Inhabited

/-- A request as the listener gives it. `entropy`: 16 fresh bytes of the machine's
generator (for a session id). -/
structure Request where
  method : String
  path : String
  host : String := ""
  origin : Option String := none
  body : String := ""
  entropy : ByteArray := ByteArray.empty

/-- What `handle` answers: a response, or a command for the session's page. -/
inductive Outcome where
  | reply (status : Nat) (body : Json)
  | page (command : Command) (params : List String) (body : Json) (session : Session)

instance : Inhabited Outcome := ⟨.reply 500 .null⟩

def Outcome.ofError (e : Error) : Outcome := .reply e.code.status e.body

/-- The body of a request that needs one: a JSON object (§6.3 "process a command", step
5); none of a GET or DELETE is read. -/
def parameters (method body : String) : Except Error Json :=
  if method != "POST" then .ok (.object []) else
  match parseJson body with
  | .ok (.object fs) => .ok (.object fs)
  | _ => .error { code := .invalidArgument, message := "the body is not a JSON object" }

/-- One request. -/
def handle (cfg : Gate.Config) (b : Browser) (srv : Server) (r : Request) : Server × Outcome :=
  match Gate.admit cfg srv.gate { path := r.path, host := r.host, origin := r.origin } with
  | (gate, .error _) =>
    -- refused: nothing but the gate's count changes, and the answer says nothing
    ({ srv with gate }, .reply 403 (Error.body { code := .unknownError, message := "refused" }))
  | (gate, .ok segs) =>
    let srv := { srv with gate }
    match route r.method segs with
    | .error e => (srv, .ofError e)
    | .ok routed =>
      match parameters r.method r.body with
      | .error e => (srv, .ofError e)
      | .ok params =>
        if routed.command == .status then
          (srv, .reply 200 (successBody (.object [("ready", .bool srv.session.isNone),
            ("message", .string (if srv.session.isNone then "ready" else "a session is active"))])))
        else if routed.command == .newSession then
          if srv.session.isSome then (srv, .ofError { code := .sessionNotCreated, message := "a session is active" })
          else if r.entropy.size < Gate.secretBytes then
            (srv, .ofError { code := .sessionNotCreated, message := "no entropy for a session id" })
          else match processCapabilities b params with
            | .error e => (srv, .ofError e)
            | .ok caps =>
              let id := sessionIdOf r.entropy
              let caps := caps.map fun (k, x) =>
                if k == "webSocketUrl" then (k, Json.string (b.socketBase ++ "/session/" ++ id)) else (k, x)
              let timeouts := match (caps.find? (·.1 == "timeouts")).map (·.2) with
                | some t => match Timeouts.merge {} t with
                  | .ok x => x
                  | .error _ => {}
                | none => {}
              ({ srv with session := some { id, capabilities := caps, timeouts } },
                .reply 200 (successBody (.object [("sessionId", .string id), ("capabilities", .object caps)])))
        else
          match srv.session, routed.session with
          | some session, some sid =>
            if !Gate.sameText sid session.id then (srv, .ofError { code := .invalidSessionId, message := "no such session" })
            else match routed.command with
              | .deleteSession => ({ srv with session := none }, .reply 200 (successBody .null))
              | .getTimeouts => (srv, .reply 200 (successBody session.timeouts.toJson))
              | .setTimeouts =>
                match session.timeouts.merge params with
                | .ok t => ({ srv with session := some { session with timeouts := t } }, .reply 200 (successBody .null))
                | .error e => (srv, .ofError e)
              | c => (srv, .page c routed.params params session)
          | _, _ => (srv, .ofError { code := .invalidSessionId, message := "no such session" })

/-! ## Theorems -/

/-- No duplicates. Says: no two endpoints have the same method and path template, so a
request has at most one command by the table. Does not say: that two templates never fit
one path (`session/{id}/element/active` also fits `session/{id}/element/{id}` templates
of other methods; `route` takes the first of the request's method). -/
theorem endpoints_nodup : (endpoints.map fun e => (e.1, e.2.1)).Nodup := by decide

/-- Sessions. Says: every endpoint but Status and New Session is under
`session/{session id}`: no other command can be reached without naming a session. Does
not say: that the session exists (`handle_no_session`). -/
theorem endpoints_session :
    endpoints.all (fun e => e.2.2 == .status || e.2.2 == .newSession || underSession e.2.1) = true := by decide

/-- Unknown requests. Says: a request that `route` refuses answers `unknown command`
(404) or `unknown method` (405), never a success. Does not say: which of the two (405
exactly when another method has an endpoint at the path). -/
theorem route_error (method : String) (segs : List String) (e : Error) (h : route method segs = .error e) :
    e.code = .unknownCommand ∨ e.code = .unknownMethod := by
  unfold route at h
  split at h
  · simp at h
  · split at h <;> simp only [Except.error.injEq] at h <;> subst h <;> simp

/-- Refusal changes nothing. Says: a request the gate refuses (no secret, an `Origin`
header, a foreign `Host`, or a locked gate) leaves the session exactly as it was and is
never handed to the page; only the gate's count of refusals may change. Does not say:
that the refusal is logged (host plumbing). -/
theorem handle_refused (cfg : Gate.Config) (b : Browser) (srv : Server) (r : Request)
    (gate : Gate.State) (why : Gate.Refusal)
    (h : Gate.admit cfg srv.gate { path := r.path, host := r.host, origin := r.origin } = (gate, .error why)) :
    (handle cfg b srv r).1.session = srv.session ∧
      (handle cfg b srv r).2 matches .reply 403 _ := by
  simp [handle, h]

/-- No secret, no change. Says: a request whose path does not start with the secret
changes no session and reaches no page, whatever its method, body and headers. Does not
say: more than `handle_refused` with `Gate.admit_no_secret`; it is the form the security
record cites. -/
theorem handle_no_secret (cfg : Gate.Config) (b : Browser) (srv : Server) (r : Request)
    (h : (Gate.splitPath r.path).1 ≠ cfg.secret) :
    (handle cfg b srv r).1.session = srv.session ∧ (handle cfg b srv r).2 matches .reply 403 _ := by
  obtain ⟨gate, why, hadmit⟩ := Gate.admit_no_secret cfg srv.gate { path := r.path, host := r.host, origin := r.origin } h
  exact handle_refused cfg b srv r gate why hadmit

/-- No session. Says: when no session exists, a request that is let in for a command
other than Status and New Session changes nothing and reaches no page: it is answered
with an error. Does not say: the same for a wrong session id while a session exists (the
definition's next branch; tested). -/
theorem handle_no_session (cfg : Gate.Config) (b : Browser) (srv : Server) (r : Request)
    (gate : Gate.State) (segs : List String) (routed : Routed) (params : Json)
    (ha : Gate.admit cfg srv.gate { path := r.path, host := r.host, origin := r.origin } = (gate, .ok segs))
    (hr : route r.method segs = .ok routed) (hp : parameters r.method r.body = .ok params)
    (h1 : routed.command ≠ .status) (h2 : routed.command ≠ .newSession) (hs : srv.session = none) :
    (handle cfg b srv r).1.session = none ∧
      (handle cfg b srv r).2 matches .reply 404 _ := by
  simp [handle, ha, hr, hp, h1, h2, hs, Outcome.ofError, Code.status]

/-! ## Tests -/

private def cfg : Gate.Config := { secret := "00112233445566778899aabbccddeeff", port := 4444 }
private def browser : Browser := { version := "0.36", platform := "linux", socketBase := "ws://127.0.0.1:4444/00112233445566778899aabbccddeeff" }
private def entropy : ByteArray := ByteArray.mk ((Array.range 16).map (·.toUInt8))
private def send (srv : Server) (method path : String) (body : String := "") : Server × Outcome :=
  handle cfg browser srv { method, path := "/00112233445566778899aabbccddeeff" ++ path, host := "127.0.0.1:4444", body, entropy }
private def statusOf : Outcome → Nat
  | .reply st _ => st
  | .page .. => 0
private def errorOf : Outcome → String
  | .reply _ body => match (body.field? "value").bind (·.field? "error") with
    | some (.string e) => e
    | _ => ""
  | .page .. => "page"
private def newSession (caps : String) : Server × Outcome := send {} "POST" "/session" ("{\"capabilities\":" ++ caps ++ "}")
private def sid : String := "00010203-0405-0607-0809-0a0b0c0d0e0f"
private def live : Server := (newSession "{}").1

#guard (route "GET" ["status"]).toOption == some { command := .status }
#guard (route "POST" ["session", "abc", "element", "e1", "click"]).toOption == some { command := .elementClick, session := some "abc", params := ["e1"] }
#guard (route "GET" ["session", "abc", "element", "active"]).toOption == some { command := .getActiveElement, session := some "abc" }
#guard (route "GET" ["session", "abc", "element", "e1", "attribute", "id"]).toOption == some { command := .getElementAttribute, session := some "abc", params := ["e1", "id"] }
#guard (match route "PUT" ["session"] with | .error e => e.code == .unknownMethod | _ => false)
#guard (match route "GET" ["session"] with | .error e => e.code == .unknownMethod | _ => false)
#guard (match route "GET" ["nope"] with | .error e => e.code == .unknownCommand | _ => false)
#guard safeInteger (.number "0") == some 0 && safeInteger (.number "2.0") == some 2 && safeInteger (.number "9007199254740991") == some 9007199254740991
#guard safeInteger (.number "9007199254740992") == none && safeInteger (.number "2.5") == none && safeInteger (.number "-1") == none && safeInteger (.string "10") == none
-- new_session: defaults, sessionId, one session at a time
#guard statusOf (newSession "{}").2 == 200 && (live.session.map (·.id)) == some sid
#guard statusOf (newSession "{\"alwaysMatch\":{\"pageLoadStrategy\":\"eager\",\"timeouts\":{\"script\":50,\"pageLoad\":25}}}").2 == 200
#guard ((newSession "{\"alwaysMatch\":{\"timeouts\":{\"script\":50,\"pageLoad\":2.0}}}").1.session.map (·.timeouts)) == some { script := some 50, pageLoad := 2, implicit := 0 }
#guard errorOf (send live "POST" "/session" "{\"capabilities\":{}}").2 == "session not created"
-- invalid_capabilities.py
#guard errorOf (send {} "POST" "/session" "{}").2 == "invalid argument"
#guard errorOf (send {} "POST" "/session" "{\"capabilities\":[]}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":[]}").2 == "invalid argument"
#guard errorOf (newSession "{\"firstMatch\":[]}").2 == "invalid argument"
#guard errorOf (newSession "{\"firstMatch\":{}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"pageLoadStrategy\":\"Eager\"}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"timeouts\":{\"pageLoad\":2.5}}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"timeouts\":{\"pageLoad\":9007199254740992}}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"timeouts\":{\"invalid\":10}}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"unhandledPromptBehavior\":\"ACCEPT\"}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"unhandledPromptBehavior\":{\"foo\":\"accept\"}}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"proxy\":{\"proxyType\":\"SYSTEM\"}}}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"chromeOptions\":{}}}").2 == "invalid argument"
#guard statusOf (newSession "{\"alwaysMatch\":{\"test:extension\":{\"key\":\"value\"},\"acceptInsecureCerts\":null}}").2 == 200
-- merge.py: a capability in both; matching
#guard errorOf (newSession "{\"alwaysMatch\":{\"pageLoadStrategy\":\"none\"},\"firstMatch\":[{},{\"pageLoadStrategy\":\"eager\"}]}").2 == "invalid argument"
#guard errorOf (newSession "{\"alwaysMatch\":{\"browserName\":\"other\"}}").2 == "session not created"
#guard statusOf (newSession "{\"firstMatch\":[{\"browserName\":\"other\"},{\"browserName\":\"foafnaut\",\"pageLoadStrategy\":\"eager\"}]}").2 == 200
-- sessions and timeouts
#guard errorOf (send live "GET" "/session/nope/timeouts").2 == "invalid session id"
#guard errorOf (send {} "GET" ("/session/" ++ sid ++ "/timeouts")).2 == "invalid session id"
#guard statusOf (send live "GET" ("/session/" ++ sid ++ "/timeouts")).2 == 200
#guard ((send live "POST" ("/session/" ++ sid ++ "/timeouts") "{\"script\":null,\"implicit\":5}").1.session.map (·.timeouts)) == some { script := none, pageLoad := 300000, implicit := 5 }
#guard errorOf (send live "POST" ("/session/" ++ sid ++ "/timeouts") "{\"foo\":1}").2 == "invalid argument"
#guard errorOf (send live "POST" ("/session/" ++ sid ++ "/timeouts") "[]").2 == "invalid argument"
#guard (send live "DELETE" ("/session/" ++ sid)).1.session.isNone
-- the timeouts a session reports read back as themselves
#guard (Timeouts.merge {} ({ script := none, pageLoad := 7, implicit := 9 } : Timeouts).toJson).toOption == some { script := none, pageLoad := 7, implicit := 9 }
#guard (Timeouts.merge {} ({} : Timeouts).toJson).toOption == some {}
#guard errorOf (send live "POST" ("/session/" ++ sid ++ "/url") "{\"url\":\"about:blank\"}").2 == "page"
-- the gate: without the secret nothing happens
#guard statusOf (handle cfg browser live { method := "DELETE", path := "/session/" ++ sid, host := "127.0.0.1:4444" }).2 == 403
#guard (handle cfg browser live { method := "DELETE", path := "/session/" ++ sid, host := "127.0.0.1:4444" }).1.session.isSome
#guard (handle cfg browser live { method := "DELETE", path := "/00112233445566778899aabbccddeeff/session/" ++ sid, host := "127.0.0.1:4444", origin := some "https://evil.example" }).1.session.isSome

end L4Factoidal.WebDriver.Protocol
