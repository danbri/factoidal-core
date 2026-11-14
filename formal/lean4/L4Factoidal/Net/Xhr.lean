/-
L4Factoidal.Net.Xhr — XMLHttpRequest (https://xhr.spec.whatwg.org/) as a state machine on
`Net.PageFetch`, for page scripts on both JavaScript engines
(https://github.com/danbri/factoidal-core/issues/374; the record of the design is in
`docs/designissues/2026-11-11-page-network.md`).

The state of each object, what a method may do, the order of its events and the text of
its answer are here. `tools/wasmvm/quickjs/prelude.js` holds a class whose methods call
`web_api` ops 60 to 79 (`Hosts.WebApi`), and fires the events this file lists.

Sync requests are made by undo and redo (`syncWanted`, `syncAnswers`): an embedder that
cannot undo a run (`syncOk` false: the AOT path, or a later action of a page whose scripts
never name `XMLHttpRequest`, `mayBlock`) gets NotSupportedError. Cookies are never sent
or stored (`Net.PageFetch`). The response types `""`, `"text"`, `"json"`, `"arraybuffer"`,
`"blob"` and `"document"` have a value.

Each event is one `next` call of the page's task, so a script that runs in the middle of a
sequence sees the state of that point. `Ev.setState`, `.guardDone` and `.startFetch` are
the steps that are not events, in the place the standard has them.
-/
import L4Factoidal.Net.PageFetch
import L4Factoidal.Net.BlobUrls
import L4Factoidal.Net.Integrity
import L4Factoidal.Net.CspPolicy
import L4Factoidal.Net.WebSocket
import L4Factoidal.Crypto.WebHacl
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.Net.Xhr
open L4Factoidal.WHATWG L4Factoidal.Net.PageFetch

/-- Codes of `web_api`, as the prelude turns them into exceptions: as `Hosts.WebApi`'s where
it has one. -/
def errInvalidState : Int := -31
def errSecurity : Int := -32
def errType : Int := -20
def errSyntax : Int := -24
def errNotSupported : Int := -23
def errAccess : Int := -25
def errNetwork : Int := -33
/-- A sync request waits for the host: the run is undone and done again. -/
def errNeedHost : Int := -40

/-- One step of the sequence a task runs: an event to fire, or a change between events. -/
inductive Ev where
  | setState (n : Nat)
  /-- "If xhr's state is not done, then return": a handler may have reopened it. -/
  | guardDone
  /-- The end of `abort`: done goes to unsent, without an event. -/
  | unsent
  /-- `send` fires `loadstart`, then this starts the fetch, unless a handler stopped it. -/
  | startFetch
  | fire (upload : Bool) (type : String) (loaded total : Nat) (computable : Bool)
  deriving Inhabited, Repr, DecidableEq

structure Xhr where
  /-- UNSENT 0, OPENED 1, HEADERS_RECEIVED 2, LOADING 3, DONE 4. -/
  state : Nat := 0
  sendFlag : Bool := false
  async : Bool := true
  method : String := ""
  url : String := ""
  headers : Array (String × String) := #[]
  body : Option ByteArray := none
  cred : Bool := false
  /-- Fetch credentials mode "omit": no cookie is sent with the request or stored from its answer. -/
  omitCred : Bool := false
  /-- Fetch mode "same-origin" (`fetch`); XHR is always "cors". -/
  sameOnly : Bool := false
  /-- Fetch redirect mode "error" (`fetch`); XHR always follows. -/
  redirectError : Bool := false
  /-- Fetch mode "no-cors" (`fetch`): `PageFetch.Transfer.noCors`. -/
  noCors : Bool := false
  /-- Fetch redirect mode "manual" (`fetch`): `PageFetch.Transfer.redirectManual`. -/
  redirectManual : Bool := false
  /-- The request's integrity metadata (`fetch`'s `integrity`): a response whose bytes do not
  match is a network error (`Net.Integrity.okFor`). -/
  integrity : String := ""
  /-- A request the engine makes for an element (op 165, never a page's script): its
  destination (Fetch §2.2.5, `"empty"` for `fetch` and `XMLHttpRequest`), and `raw`: the
  answer's own status and bytes are kept even when it is opaque, since the element uses them
  (an image is decoded, a classic script runs); the response still says it is opaque. -/
  destination : String := "empty"
  raw : Bool := false
  /-- The request's referrer (`fetch`'s `referrer`): `none` is the client's URL, `some ""`
  no referrer, else a URL of the page's own origin (`setReferrer`). -/
  referrer : Option String := none
  /-- The request's own referrer policy (`fetch`'s `referrerPolicy`); `none`: the client's. -/
  policy : Option ReferrerPolicy.Policy := none
  /-- The document that asks, when it is not the session's own (a same-origin frame's
  document in this realm): its URL, of the page's origin, and its policy (`setClient`). -/
  client : Option (String × ReferrerPolicy.Policy) := none
  timeout : Nat := 0
  responseType : String := ""
  mimeOverride : Option String := none
  uploadComplete : Bool := false
  uploadListener : Bool := false
  response : Option Response := none
  /-- `send` could not start (policy): the error steps wait for the page's next task. -/
  deferFail : Bool := false
  /-- A response made here (a `data:` URL): it is given at the page's next task. -/
  deferred : Option Response := none
  transfer : Option Nat := none
  /-- The page's callback that runs the events of this object when the host answers. -/
  cb : Nat := 0
  events : Array Ev := #[]
  deriving Inhabited

structure State where
  /-- The embedder turned the network on (`network:true`). -/
  enabled : Bool := false
  page : Page := Page.ofUrl ""
  /-- The URL of the client (the page's document, a worker's script), from the embedder: the
  referrer of a request that names none (Fetch §2.2.5 "client"). `""`: none is sent. -/
  client : String := ""
  /-- The client's referrer policy: its `Referrer-Policy` response field, when the embedder
  gave it (`policyOfHeader`). -/
  policy : ReferrerPolicy.Policy := .default
  /-- The client's Content Security Policy (`cspOf`: its response's fields and its `meta`
  elements, from the embedder). Every request of the session is checked against it
  (`connect-src`), and the prelude asks for scripts, workers, inline blocks and `eval`
  (ops 150 to 153). -/
  csp : List CspPolicy.Policy := []
  /-- Violations not yet reported (`report`): one record each, taken by op 150. -/
  violations : Array String := #[]
  /-- The blob URLs of the session (`URL.createObjectURL`), each its origin's (`Net.BlobUrls`). -/
  blobs : L4Factoidal.Net.BlobUrls.Store := {}
  /-- The page session's cookies (`Net.Cookies`), in memory only: `document.cookie` (web_api 96,
  97) and the network (the `Cookie` field of a request made with credentials, the `Set-Cookie`
  fields of its answer) share them. -/
  cookies : Cookies.Jar := {}
  /-- The latest time in seconds a script gave (`send`, `document.cookie`): cookie expiry. -/
  now : Nat := 0
  /-- The address chosen for each name this session resolved (`Egress.choose`, at most
  `maxPins`): a later request to that name starts with it pinned, with no second resolve. -/
  pins : Array (String × String) := #[]
  xhrs : Array Xhr := #[]
  /-- The page's WebSocket connections (`Net.WebSocket`), by id (ids are `nextTransfer`'s). -/
  sockets : Array WebSocket.Sock := #[]
  /-- Fetches the host has not answered: its id, the object's handle, and its transfer. -/
  live : Array (Nat × Nat × Transfer) := #[]
  nextTransfer : Nat := 1
  /-- Requests the embedder has not been told yet (a turn takes them). -/
  outbox : Array Wire := #[]
  /-- Fetches the embedder may stop. -/
  cancels : Array Nat := #[]
  /-- Response bytes held for the page. -/
  held : Nat := 0
  /-- Sync `send` works by undo and rerun: the embedder runs this action only when it can
  redo it (not the AOT path). -/
  syncOk : Bool := false
  /-- Answers to the sync requests of this run, in order (given when the run is redone). -/
  syncAnswers : Array Answer := #[]
  syncUsed : Nat := 0
  /-- A sync request this run needs the host for: the run is thrown away, the host answers
  it, and the run happens again with one more answer (`WebScripts`, action `syncAnswer`). -/
  syncWanted : Option Wire := none
  /-- The page's scripts name `XMLHttpRequest`, so a later action may make a sync request:
  the embedder keeps the session before each action to undo it (only such pages pay). -/
  mayBlock : Bool := false
  /-- The objects belong to a `Window` (false: a worker's, `LeanJSWorkers.workerNet`). XHR
  forbids some uses of sync requests in a window only (`timeout`, `responseType`) and takes
  no `"document"` response type outside one. -/
  window : Bool := true
  deriving Inhabited

/-- For a `blob:` URL: the type and bytes that a request of this page reads, from the entry
its own origin made (`BlobUrls.resolve`: another origin's URL gives nothing). -/
def State.blobOf (s : State) (url : String) : Option (String × ByteArray) :=
  if url.startsWith "blob:" then (L4Factoidal.Net.BlobUrls.resolve s.blobs s.page.origin url).map fun e => (e.type, e.body) else none

/-- The most names a session keeps an address for. -/
def maxPins : Nat := 64

/-- The pin a new request to `url` starts with: the address this session chose for its name. -/
def State.pinFor (s : State) (url : String) : Option (String × String) :=
  match URL.parseUrl url with
  | some u => s.pins.find? (·.1 == lower u.hostname)
  | none => none

/-- Keep the pin a transfer chose (the first for each name). -/
def State.notePin (s : State) (t : Transfer) : State :=
  match t.pin with
  | some p => if s.pins.any (·.1 == p.1) || s.pins.size ≥ maxPins then s else { s with pins := s.pins.push p }
  | none => s

/-- A page's objects (each handle is its index plus one). -/
def maxObjects : Nat := 65536
/-- The largest response: 64 MiB, the output buffer of `n.api` (`LeanJS.outCap`). -/
def maxBody : Nat := 1 <<< 26
/-- The response bytes one page holds: 256 MiB. -/
def maxHeld : Nat := 1 <<< 28

/-- Requests are waiting: settling stops here. -/
def State.waiting (s : State) : Bool := !s.live.isEmpty

def State.get? (s : State) (h : Nat) : Option Xhr :=
  if h == 0 then none else s.xhrs[h - 1]?

def State.set (s : State) (h : Nat) (x : Xhr) : State :=
  { s with xhrs := s.xhrs.set! (h - 1) x }

private def rsc : Ev := .fire false "readystatechange" 0 0 false

/-- A token (RFC 9110 §5.6.2). -/
def isToken (s : String) : Bool :=
  !s.isEmpty && s.all fun (c : Char) =>
    c.isAlphanum || "!#$%&'*+-.^_`|~".contains c

/-- Normalize a method (Fetch §2.2.1). -/
def normalizeMethod (m : String) : String :=
  let u := m.toUpper
  if ["DELETE", "GET", "HEAD", "OPTIONS", "POST", "PUT"].contains u then u else m

/-- Stop the object's fetch. -/
private def stopFetch (s : State) (x : Xhr) : State × Xhr :=
  match x.transfer with
  | some id => ({ s with live := s.live.filter (·.1 != id), cancels := s.cancels.push id }, { x with transfer := none })
  | none => (s, x)

/-- The request error steps (XHR §4.5.3): `e` is `error`, `abort` or `timeout`. -/
def requestError (s : State) (h : Nat) (x : Xhr) (e : String) : State :=
  let (s, x) := stopFetch s x
  let up := !x.uploadComplete
  let upEvents : Array Ev :=
    if up && x.uploadListener then #[.fire true e 0 0 false, .fire true "loadend" 0 0 false] else #[]
  let evs : Array Ev := #[rsc] ++ upEvents ++ #[.fire false e 0 0 false, .fire false "loadend" 0 0 false]
  s.set h { x with state := 4, sendFlag := false, response := none, deferFail := false, deferred := none, uploadComplete := true,
                   events := x.events ++ evs }

/-- `open(method, url, async, ...)`. -/
def openX (s : State) (h : Nat) (method url base : String) (async : Bool) : State × Except Int String :=
  match s.get? h with
  | none => (s, .error errType)
  | some x =>
  if !isToken method then (s, .error errSyntax) else
  if forbiddenMethod method then (s, .error errSecurity) else
  match URL.parseUrl url (if base.isEmpty then none else some base) with
  | none => (s, .error errSyntax)
  | some u =>
    if s.window && !async && (x.timeout != 0 || x.responseType != "") then (s, .error errAccess) else
    let u' := { u with username := "", password := "" }
    let (s, x) := stopFetch s x
    let x' := { x with method := normalizeMethod method, url := u'.serialize true, async, headers := #[], body := none,
                       sendFlag := false, uploadListener := false, uploadComplete := false, response := none,
                       deferFail := false, deferred := none, events := #[] }
    let x' := if x.state != 1 then { x' with state := 1, events := #[rsc] } else x'
    (s.set h x', .ok "")

/-- `setRequestHeader(name, value)`. -/
def setHeaderX (s : State) (h : Nat) (name value : String) : State × Except Int String :=
  match s.get? h with
  | none => (s, .error errType)
  | some x =>
  if x.state != 1 || x.sendFlag then (s, .error errInvalidState) else
  if value.any (fun (c : Char) => c.toNat > 255) then (s, .error errType) else
  let value := trimWs value
  if !isToken name || value.any (fun (c : Char) => c == '\x00' || c == '\n' || c == '\r') then (s, .error errSyntax) else
  if forbiddenRequestHeader name || forbiddenOverride name value then (s, .ok "") else
  let n := lower name
  let found := x.headers.findIdx? fun (k, _) => lower k == n
  let hs := match found with
    | some i => x.headers.modify i fun (k, v) => (k, v ++ ", " ++ value)
    | none => x.headers.push (name, value)
  (s.set h { x with headers := hs }, .ok "")

/-- A MIME type's `charset` parameter, ASCII case-insensitive, quotes removed. -/
def mimeCharset (ct : String) : Option String :=
  (ct.splitOn ";").drop 1 |>.findSome? fun p =>
    match (trimWs p).splitOn "=" with
    | k :: v :: _ =>
      if lower (trimWs k) == "charset" then
        let t := trimWs v
        some (if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" then ((t.drop 1).dropEnd 1).toString else t)
      else none
    | _ => none

/-! ## Content Security Policy at the session (CSP §4.1 Fetch integration, §5 reporting) -/

/-- The policies of a client: the `Content-Security-Policy` fields of its response (joined
with commas), its `Content-Security-Policy-Report-Only` fields, and the `content` of its
`meta http-equiv` elements (HTML §4.2.5.3: enforced, and without `report-uri`,
`frame-ancestors` and `sandbox`, which a `meta` may not give). -/
def cspOf (header reportOnly metas : String) : List CspPolicy.Policy :=
  CspPolicy.parseList header ++ CspPolicy.parseList reportOnly true ++
    (CspPolicy.parseList metas).map fun p =>
      { p with directives := p.directives.filter fun d => !["report-uri", "frame-ancestors", "sandbox"].contains d.name }

/-- A URL as CSP's source lists read it. -/
def cspUrl (u : URL.Url) : Csp.Url := { scheme := u.scheme, host := u.hostname, port := u.port, path := u.pathname }

/-- The page's origin as the URL `'self'` is matched against (an opaque origin matches no
host). -/
def cspSelf (p : Page) : Csp.Url :=
  match URL.parseUrl p.origin with
  | some o => if p.origin == "null" then { scheme := "", host := "" } else { scheme := o.scheme, host := o.hostname, port := o.port }
  | none => { scheme := "", host := "" }

/-- CSP §5.4 "strip URL for use in reports": an `http` or `https` URL without its fragment and
credentials; of any other, the scheme. -/
def reportUrl (u : URL.Url) : String :=
  if u.scheme == "http" || u.scheme == "https" then ({ u with username := "", password := "" } : URL.Url).serialize true
  else u.scheme

/-- Queue the violations `vs` of directive `name` for `blocked` (a stripped URL, `inline` or
`eval`) at node `node` (0: the document): the record is the effective directive, the blocked
URI, the policy as written, `enforce` or `report`, the node, and a sample (U+0000 between). -/
def report (s : State) (vs : List CspPolicy.Policy) (name blocked : String) (node : Nat := 0) (sample : String := "") : State :=
  { s with violations := s.violations ++ (vs.map fun v =>
      "\x00".intercalate [name, blocked, v.text, if v.reportOnly then "report" else "enforce", toString node, sample]).toArray }

/-- A request of kind `name` (a directive name) to `url` under the session's policy: the
state with its violations queued, and whether an enforced policy blocks it. A URL that does
not parse is blocked when any policy governs the kind. -/
def cspRequest (s : State) (name url : String) (redirected : Bool := false) (nonce : String := "")
    (parserInserted : Bool := false) (node : Nat := 0) : State × Bool :=
  if s.csp.isEmpty then (s, false) else
  match URL.parseUrl url with
  | none => (s, s.csp.any fun p => !p.reportOnly && (p.directiveFor name).isSome)
  | some u =>
    let vs := CspPolicy.violationsRequest s.csp name (cspSelf s.page) (cspUrl u) redirected nonce parserInserted
    (report s vs name (reportUrl u) node, CspPolicy.enforced vs)

/-- An inline script or style under the session's policy (`CspPolicy.violationsInline`, with
HACL*'s SHA-2 for hash sources): the violations queued, and whether it is blocked. The sample
is the first 40 characters of the text when the policy asks for one (`'report-sample'`). -/
def cspInline (s : State) (script element : Bool) (nonce source : String) (node : Nat := 0) : State × Bool :=
  if s.csp.isEmpty then (s, false) else
  let vs := CspPolicy.violationsInline L4Factoidal.Crypto.WebHacl.hashFast s.csp script element nonce source.toUTF8
  (report s vs (CspPolicy.inlineName script element) "inline" node, CspPolicy.enforced vs)

/-- `eval`, `new Function` and string timers under the session's policy. -/
def cspEval (s : State) : State × Bool :=
  if s.csp.isEmpty then (s, false) else
  let vs := CspPolicy.violationsEval s.csp
  (report s vs "script-src" "eval", CspPolicy.enforced vs)

/-! ## The referrer of a request (Fetch §2.2.5, §5.4 `Request` constructor steps 14 and 15) -/

/-- A URL of the page's own origin, serialized; `none` for any other (and for a page of an
opaque origin, which has no such URL). -/
def ownUrl (p : Page) (url : String) : Option String :=
  match URL.parseUrl url with
  | some u => if sameOrigin p u then some u.serialize else none
  | none => none

/-- `fetch`'s `referrer` for object `h`: `""` is no referrer; a URL of the page's origin is
that URL; anything else (`about:client`, a URL of another origin, not a URL) is the client
(Fetch §5.4 step 14.3: a page names only its own origin's URLs as the referrer). -/
def setReferrer (s : State) (h : Nat) (referrer : String) : State :=
  match s.get? h with
  | none => s
  | some x => s.set h { x with referrer := if referrer.isEmpty then some "" else ownUrl s.page referrer }

/-- The document that asks for object `h` (`node_query` 210 names it: the page's, or a
frame's in this realm; the container's URL for a `srcdoc` document): its URL is kept only
when it is of the page's origin (frames of another origin have a session of their own).
Any other (`about:blank`, a `blob:` document, a URL of another origin) is a client with no
URL: its requests carry no referrer. -/
def setClient (s : State) (h : Nat) (url : String) (policy : String) : State :=
  match s.get? h with
  | none => s
  | some x =>
    let pol := (ReferrerPolicy.Policy.ofToken policy).getD s.policy
    match ownUrl s.page url with
    | some u => s.set h { x with client := some (u, pol) }
    | none => s.set h { x with client := some ("", pol) }

/-- The referrer of object `x`'s request: the one it names, else its document's URL, else the
session's client. -/
def referrerFor (s : State) (x : Xhr) : String :=
  match x.referrer with
  | some r => r
  | none => match x.client with
    | some (u, _) => u
    | none => s.client

/-- The referrer policy of object `x`'s request: its own, else its document's, else the
session's client's. -/
def policyFor (s : State) (x : Xhr) : ReferrerPolicy.Policy :=
  match x.policy with
  | some p => p
  | none => match x.client with
    | some (_, p) => p
    | none => s.policy

/-- The policy a `Referrer-Policy` response field gives a client (the default when it names
none). -/
def policyOfHeader (value : String) : ReferrerPolicy.Policy :=
  (ReferrerPolicy.Policy.ofHeader value).getD .default

/-- What a sync fetch came to. -/
inductive SyncOutcome where
  | done (r : Response)
  | failed
  | need
  deriving Inhabited

/-- Run a fetch on the answers given so far: the `k`-th request of this run takes the `k`-th
answer (determinism of the run is what makes the numbering stable: the redone run is the same
run, with the same clock, random numbers and order). -/
def syncFetch (s : State) (t0 : Transfer) : State × SyncOutcome := Id.run do
  let mut s := s
  let mut step := plan t0
  let mut hops := t0.redirects
  for _ in [0:4 * maxRedirects + 8] do
    match step with
    | .fail _ => return (s, .failed)
    | .deliver _ r => return (s, .done r)
    | .send t w =>
      s := s.notePin t
      -- a redirect's target is checked against the policy as the first URL was (CSP §4.1.2)
      if t.redirects != hops then
        let (s', blocked) := cspRequest s "connect-src" t.url true
        s := s'
        hops := t.redirects
        if blocked then return (s, .failed)
      match s.syncAnswers[s.syncUsed]? with
      -- the first request the run needs wins: a page that catches the throw and goes on
      -- does not change what the host is asked (`syncWanted` is set once in a run)
      | none => return ({ s with syncWanted := s.syncWanted.orElse fun _ => some w }, .need)
      | some a =>
        -- the answer's cookies first: the next hop of a redirect carries them
        let jar := t.storeCookies s.cookies a
        s := { s with syncUsed := s.syncUsed + 1, cookies := jar }
        step := onAnswer { t with jar } a
  return (s, .failed)

/-- Sync `send` (XHR §4.5.2 step 12): the fetch happens now; on failure a `NetworkError` is
thrown; on success the object is done with its last events. `send` has no `loadstart` in
this mode (the steps "if xhr's synchronous flag is unset" hold it). -/
def syncSend (s : State) (h : Nat) (x : Xhr) : State × Except Int String :=
  let id := s.nextTransfer
  let s := { s with nextTransfer := id + 1 }
  let t : Transfer := { id, page := s.page, method := x.method, url := x.url, headers := x.headers.toList, body := x.body, credentials := x.cred, sameOriginOnly := x.sameOnly, redirectError := x.redirectError, blob := s.blobOf x.url, referrer := referrerFor s x, referrerPolicy := policyFor s x, noCors := x.noCors, redirectManual := x.redirectManual, omitCredentials := x.omitCred, jar := s.cookies, now := s.now, pin := s.pinFor x.url, destination := x.destination }
  let (s, blocked) := cspRequest s "connect-src" x.url
  let (s, out) := if blocked then (s, SyncOutcome.failed) else syncFetch s t
  match out with
  | .need => (s.set h { x with events := #[] }, .error errNeedHost)
  | .failed => (s.set h { x with state := 4, sendFlag := false, response := none, events := #[] }, .error errNetwork)
  | .done r =>
    if r.body.size > maxBody || s.held + r.body.size > maxHeld then
      (s.set h { x with state := 4, sendFlag := false, response := none, events := #[] }, .error errNetwork)
    else
      let bodySize := r.body.size
      let total := match headerGet r.headers "content-length" with
        | some v => (trimWs v).toNat?.getD 0
        | none => 0
      let evs : Array Ev := #[.setState 4, rsc, .guardDone, .fire false "load" bodySize total (total > 0),
        .fire false "loadend" bodySize total (total > 0)]
      ((s.set h { x with response := some r, events := evs }) |> fun s => { s with held := s.held + r.body.size }, .ok "")

def textDefault : String := "text/plain;charset=UTF-8"

/-- `send(body)`. `ctDefault`: the type of the body when the page did not set one, as "extract a body"
gives it (XHR §4.5.1): empty for bytes; for a string, `text/plain;charset=UTF-8`, whose
charset is then also corrected in a type the page gave. -/
def sendX (s : State) (h : Nat) (body : Option ByteArray) (ctDefault : String) (cb : Nat) (listener : Bool) :
    State × Except Int String :=
  match s.get? h with
  | none => (s, .error errType)
  | some x =>
  if x.state != 1 || x.sendFlag then (s, .error errInvalidState) else
  if !x.async && !s.syncOk then (s, .error errNotSupported) else
  let body := if x.method == "GET" || x.method == "HEAD" then none else body
  let headers :=
    if body.isSome && !ctDefault.isEmpty then
      match x.headers.findIdx? fun (k, _) => lower k == "content-type" with
      | some i =>
        -- a charset that is not UTF-8 is corrected (XHR §4.5.1 step 5.3)
        x.headers.modify i fun (k, v) =>
          match mimeCharset v with
          | some c => if lower c == "utf-8" || ctDefault != textDefault then (k, v) else
            let parts := v.splitOn ";"
            (k, ";".intercalate (parts.map fun p => if lower ((trimWs p).take 7).toString == "charset" then "charset=UTF-8" else p))
          | none => (k, v)
      | none => x.headers.push ("Content-Type", ctDefault)
    else x.headers
  let headers := if headers.any (fun (k, _) => lower k == "accept") then headers else headers.push ("Accept", "*/*")
  let total := (body.map ByteArray.size).getD 0
  if !x.async then syncSend s h { x with body, headers, sendFlag := true, uploadComplete := true, response := none } else
  let up := body.isSome
  let up' := up && listener
  let evs : Array Ev :=
    #[.fire false "loadstart" 0 0 false] ++ (if up' then #[.fire true "loadstart" 0 total (total > 0)] else #[]) ++ #[.startFetch]
  (s.set h { x with body, headers, sendFlag := true, uploadComplete := !up, uploadListener := listener, cb, events := evs, response := none }, .ok "")

/-- Start the fetch, unless a handler of `loadstart` stopped it. -/
def beginFetch (s : State) (h : Nat) (x : Xhr) : State :=
  if x.state != 1 || !x.sendFlag then s else
  -- Content Security Policy: `connect-src` governs `fetch` and `XMLHttpRequest` (CSP §6.1.3)
  let (s, blocked) := cspRequest s "connect-src" x.url
  if blocked then s.set h { x with deferFail := true } else
  let id := s.nextTransfer
  let s := { s with nextTransfer := id + 1 }
  let t : Transfer := { id, page := s.page, method := x.method, url := x.url, headers := x.headers.toList, body := x.body, credentials := x.cred, sameOriginOnly := x.sameOnly, redirectError := x.redirectError, blob := s.blobOf x.url, referrer := referrerFor s x, referrerPolicy := policyFor s x, noCors := x.noCors, redirectManual := x.redirectManual, omitCredentials := x.omitCred, jar := s.cookies, now := s.now, pin := s.pinFor x.url, destination := x.destination }
  match plan t with
  | .send t' w => (s.set h { x with transfer := some id }) |> fun s => { s with live := s.live.push (id, h, t'), outbox := s.outbox.push w }
  | .deliver _ r =>
    if Integrity.okFor x.integrity r.tainting r.body then s.set h { x with deferred := some r }
    else s.set h { x with deferFail := true }
  | .fail _ => s.set h { x with deferFail := true }

/-- The next event to fire for object `h`, running the steps before it. -/
def next (s : State) (h : Nat) : State × Option (Bool × String × Nat × Nat × Bool) := Id.run do
  let mut s := s
  let fuel := match s.get? h with
    | some x => x.events.size + 32
    | none => 0
  for _ in [0:fuel] do
    match s.get? h with
    | none => return (s, none)
    | some x =>
      match x.events[0]? with
      | none => return (s, none)
      | some ev =>
        let x := { x with events := x.events.extract 1 x.events.size }
        s := s.set h x
        match ev with
        | .fire u t l tt c => return (s, some (u, t, l, tt, c))
        | .setState n => s := s.set h (if n == 4 then { x with state := 4, sendFlag := false } else { x with state := n })
        | .guardDone => if x.state != 4 then s := s.set h { x with events := #[] }
        | .unsent => if x.state == 4 then s := s.set h { x with state := 0, response := none }
        | .startFetch => s := beginFetch s h x
  return (s, none)

/-- `abort()`. -/
def abortX (s : State) (h : Nat) : State × Except Int String :=
  match s.get? h with
  | none => (s, .error errType)
  | some x =>
  if (x.state == 1 && x.sendFlag) || x.state == 2 || x.state == 3 then
    let s := requestError s h { x with events := #[] } "abort"
    match s.get? h with
    | some x' => (s.set h { x' with events := x'.events.push .unsent }, .ok "")
    | none => (s, .ok "")
  else if x.state == 4 then (s.set h { x with state := 0, response := none, events := #[] }, .ok "")
  else (s, .ok "")

/-- The timeout elapsed while the fetch was running. -/
def timeoutX (s : State) (h : Nat) : State × Except Int String :=
  match s.get? h with
  | none => (s, .error errType)
  | some x =>
  if x.sendFlag && x.state != 4 then (requestError s h { x with events := #[] } "timeout", .ok "")
  else (s, .ok "")

/-- The events of a complete response (XHR §4.5.3 "handle response end-of-body"; the whole
body arrives at once, so one `progress`). -/
def responseEvents (x : Xhr) (r : Response) : Array Ev :=
  let bodySize := r.body.size
  let total := match headerGet r.headers "content-length" with
    | some v => (trimWs v).toNat?.getD 0
    | none => 0
  let upload : Array Ev :=
    if x.uploadComplete then #[] else
    if x.uploadListener then
      let t := (x.body.map ByteArray.size).getD 0
      #[.fire true "progress" t t true, .fire true "load" t t true, .fire true "loadend" t t true]
    else #[]
  let loading : Array Ev :=
    if bodySize == 0 then #[] else #[.setState 3, rsc, .fire false "progress" bodySize total (total > 0)]
  upload ++ #[.setState 2, rsc] ++ loading ++
    #[.setState 4, rsc, .guardDone, .fire false "load" bodySize total (total > 0), .fire false "loadend" bodySize total (total > 0)]

/-- What an element's request delivers (`Xhr.raw`): the answer's status, fields (no
`Set-Cookie`) and bytes, with the tainting of the response a script would get. -/
def rawResponse (t : Transfer) (a : Answer) (r : Response) : Response :=
  { status := a.status, statusText := a.statusText, url := if a.url.isEmpty then t.url else a.url,
    headers := a.headers.filter fun (n, _) => !forbiddenResponseHeader n, body := a.body, tainting := r.tainting }

/-- Kind: security lemma. Says: an element's response keeps the tainting a script's would
have (an opaque answer stays marked opaque) and never carries `Set-Cookie`. -/
theorem rawResponse_tainting (t : Transfer) (a : Answer) (r : Response) :
    (rawResponse t a r).tainting = r.tainting ∧ ∀ f ∈ (rawResponse t a r).headers, forbiddenResponseHeader f.1 = false := by
  refine ⟨rfl, fun f hf => ?_⟩
  simp only [rawResponse, List.mem_filter, Bool.not_eq_true'] at hf
  exact hf.2

/-- The host's answer to a fetch. The callback of the object, when a task is to run it. -/
def give (s : State) (id : Nat) (a : Answer) : State × Option Nat :=
  match s.sockets.findIdx? (·.id == id) with
  | some i =>
    -- a WebSocket connection's answer (Net.WebSocket.onAnswer, with the engine's SHA-1)
    let (k, ws) := WebSocket.onAnswer (Crypto.WebHacl.hashFast .sha1) s.sockets[i]! a
    ({ s with sockets := s.sockets.set! i k, outbox := s.outbox ++ ws.toArray }, if k.events.isEmpty then none else some k.cb)
  | none =>
  match s.live.find? (·.1 == id) with
  | none => (s, none)
  | some (_, h, t) =>
    match s.get? h with
    | none => ({ s with live := s.live.filter (·.1 != id) }, none)
    | some x =>
    -- the answer's cookies first: the next hop of a redirect carries them
    let jar := t.storeCookies s.cookies a
    let s := { s with cookies := jar }
    let s1 := { s with live := s.live.filter (·.1 != id) }
    match onAnswer { t with jar } a with
    | .send t' w =>
      let s := s.notePin t'
      -- a redirect's target is checked against the policy as the first URL was (CSP §4.1.2)
      let (s, blocked) := if t'.redirects != t.redirects then cspRequest s "connect-src" t'.url true else (s, false)
      if blocked then (requestError { s with live := s.live.filter (·.1 != id) } h { x with transfer := none } "error", some x.cb) else
      ({ s with live := s.live.map (fun e => if e.1 == id then (id, h, t') else e), outbox := s.outbox.push w }, none)
    | .fail _ => (requestError s1 h { x with transfer := none } "error", some x.cb)
    | .deliver _ r =>
      let r := if x.raw then rawResponse t a r else r
      -- Subresource Integrity: bytes that do not match the request's metadata never reach the page
      if !Integrity.okFor x.integrity r.tainting r.body then
        (requestError s1 h { x with transfer := none } "error", some x.cb) else
      if r.body.size > maxBody || s.held + r.body.size > maxHeld then
        (requestError s1 h { x with transfer := none } "error", some x.cb)
      else
        let x' := { x with transfer := none, response := some r, uploadComplete := true, events := x.events ++ responseEvents x r }
        ((s1.set h x') |> fun s => { s with held := s.held + r.body.size }, some x.cb)

/-- `readyState`, gated reads. -/
def statusOf (x : Xhr) : Nat :=
  match x.response with
  | some r => if x.state ≥ 2 then r.status else 0
  | none => 0

/-- The encoding of the text of the response (XHR §3.6 "get a text response"). -/
def textEncoding (x : Xhr) (r : Response) : Encoding.Encoding :=
  let override := x.mimeOverride.bind mimeCharset
  let header := (headerGet r.headers "content-type").bind mimeCharset
  let label := override.orElse fun _ => header
  (label.bind Encoding.getEncoding).getD .utf_8

/-- The text of the response, decoded by the Encoding Standard (`Encoding.decode`: BOM
sniff, then `textEncoding`, in replacement mode). -/
def responseText (x : Xhr) : String :=
  match x.response with
  | some r => if x.state ≥ 3 then Encoding.decode r.body (textEncoding x r) else ""
  | none => ""

/-- The essence of a MIME type (lowercase, parameters removed). -/
def mimeEssence (ct : String) : String := lower (trimWs ((ct.splitOn ";").headD ""))

/-- Which document `responseXML` makes (XHR "set a document response"): `"xml"`, `"html"`
(only when `responseType` is `document`), or `""` (none). -/
def docKind (x : Xhr) : String :=
  match x.response with
  | none => ""
  | some r =>
    if x.state != 4 || !(x.responseType == "" || x.responseType == "document") then "" else
    let ct := match x.mimeOverride, headerGet r.headers "content-type" with
      | some m, _ => m
      | none, some c => c
      | none, none => "text/xml"
    let e := mimeEssence ct
    if e == "text/html" then (if x.responseType == "document" then "html" else "")
    else if e == "text/xml" || e == "application/xml" || e.endsWith "+xml" then "xml"
    else ""

/-- The final MIME type (XHR §3.6.6, for a `blob` response's type): the override, else the
response's `Content-Type`, else `""`. -/
def finalMime (x : Xhr) : String :=
  match x.mimeOverride, x.response.bind fun r => headerGet r.headers "content-type" with
  | some m, _ => m
  | none, some c => c
  | none, none => ""

/-! ## `multipart/form-data` (HTML §4.10.21.8, the encoding of a `FormData` body) -/

/-- Line breaks normalized to CRLF (HTML "convert to a list of name-value pairs"). -/
def crlf (s : String) : String :=
  ((s.replace "\r\n" "\n").replace "\r" "\n").replace "\n" "\r\n"

/-- A name or filename in a `Content-Disposition` field: LF, CR and `"` percent-encoded. -/
def escapeField (s : String) : String :=
  ((s.replace "\n" "%0A").replace "\r" "%0D").replace "\"" "%22"

/-- One entry: a name, and a string value or a file (filename, type, bytes). -/
inductive FormValue where
  | text (v : String)
  | file (name type : String) (bytes : ByteArray)

/-- The bytes of one value as the body carries them. -/
def FormValue.bytes : FormValue → ByteArray
  | .text v => (crlf v).toUTF8
  | .file _ _ b => b

/-- The first boundary of the form `----FoafnautFormBoundary<k>` that occurs in no value (a
boundary must not occur in the parts, RFC 2046 §5.1.1). -/
def boundaryFor (vs : List FormValue) : String := Id.run do
  let texts := vs.map fun v => PageFetch.isoString v.bytes
  for k in [0:vs.length + 2] do
    let b := s!"----FoafnautFormBoundary{k}"
    if texts.all fun t => (t.splitOn b).length == 1 then return b
  return s!"----FoafnautFormBoundary{vs.length + 2}"

/-- The `multipart/form-data` body of a form data set, with the boundary from `boundaryFor`. -/
def formDataBody (entries : List (String × FormValue)) : ByteArray := Id.run do
  let b := boundaryFor (entries.map (·.2))
  let mut out := ByteArray.empty
  for (name, v) in entries do
    let head := s!"--{b}\r\nContent-Disposition: form-data; name=\"{escapeField (crlf name)}\"" ++
      (match v with
       | .text _ => ""
       | .file fname type _ => s!"; filename=\"{escapeField fname}\"\r\nContent-Type: {if type.isEmpty then "application/octet-stream" else type}") ++
      "\r\n\r\n"
    out := out ++ head.toUTF8 ++ v.bytes ++ "\r\n".toUTF8
  return out ++ s!"--{b}--\r\n".toUTF8

/-- `getAllResponseHeaders()`: names lowercased and sorted, one `name: value` CRLF each. -/
def allHeaders (x : Xhr) : String :=
  match x.response with
  | none => ""
  | some r =>
    if x.state < 2 then "" else
    let hs := r.headers.map fun (n, v) => (lower n, v)
    let sorted := hs.mergeSort fun a b => decide (a.1 ≤ b.1)
    String.join (sorted.map fun (n, v) => n ++ ": " ++ v ++ "\r\n")

/-- One field of a `web_api` call as a string. -/
private def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

private def natAt (fs : Array ByteArray) (i : Nat) : Nat := (strAt fs i).toNat?.getD 0

private def okStr (x : String) : Except Int ByteArray := .ok x.toUTF8

/-- The Content Security Policy ops (150 to 153), for the prelude's enforcement points. -/
def cspOp (s : State) (code : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  match code with
  | 150 =>
    -- the violations not yet reported, one a line (U+0001 between records), and the queue is
    -- emptied: the prelude fires a `securitypolicyviolation` event for each
    -- with the field "?": only whether the session has a policy or a violation to report
    -- (the prelude asks once, so a page with no policy pays one call)
    if strAt fs 0 == "?" then (s, okStr (if s.csp.isEmpty && s.violations.isEmpty then "0" else "1")) else
    ({ s with violations := #[] }, okStr ("\x01".intercalate s.violations.toList))
  | 151 =>
    -- may a request of this kind go: the directive name, the URL, the element's nonce, "1"
    -- for a parser-inserted script, the node the violation is reported at; "1" when blocked
    let (s, blocked) := cspRequest s (strAt fs 0) (strAt fs 1) false (strAt fs 2) (strAt fs 3 == "1") (natAt fs 4)
    (s, okStr (if blocked then "1" else "0"))
  | 152 =>
    -- may an inline script or style run or apply: "1" for a script, "1" for an element (a
    -- `script` or `style` element; else an attribute), the nonce, the text, the node
    let (s, blocked) := cspInline s (strAt fs 0 == "1") (strAt fs 1 == "1") (strAt fs 2) (strAt fs 3) (natAt fs 4)
    (s, okStr (if blocked then "1" else "0"))
  | 153 =>
    -- may `eval` and its kin compile a string
    let (s, blocked) := cspEval s
    (s, okStr (if blocked then "1" else "0"))
  | _ => (s, .error (-2))

/-- The WebSocket ops (`web_api` 156 to 161), with fresh entropy from the engine's generator
for the key and the masking keys. 156 `new WebSocket` (base URL, URL, callback, the
subprotocols): `ok NUL id NUL url` or `err NUL name NUL message`; 157 `send` (id, "t" or
"b", bytes); 158 `close` (id, code or "", reason); 159 a read (id; 0 readyState,
1 bufferedAmount, 2 protocol, 3 url); 160 the next event (id): "", `open NUL protocol`,
`text NUL data`, `binary`, `error`, `close NUL code NUL reason NUL 1|0`; 161 the bytes of the
last `binary`. -/
def wsOp (s : State) (code : Nat) (fs : Array ByteArray) (entropy : ByteArray) : State × Except Int ByteArray :=
  let str := fun (i : Nat) => (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""
  let nat := fun (i : Nat) => (str i).toNat?.getD 0
  let ok := fun (t : String) => Except.ok (α := ByteArray) (ε := Int) t.toUTF8
  let at? := fun (id : Nat) => s.sockets.findIdx? (·.id == id)
  match code with
  | 156 =>
    let protocols := ((List.range fs.size).drop 3).map str
    match WebSocket.openCheck (str 0) (str 1) protocols s.page.secure with
    | .error (n, m) => (s, ok ("err\u0000" ++ n ++ "\u0000" ++ m))
    | .ok u =>
      if s.sockets.size ≥ 256 then (s, ok "err\u0000SyntaxError\u0000Too many WebSocket connections.") else
      let id := s.nextTransfer
      let (k, ws) := WebSocket.connect s.page id (nat 2) u protocols entropy
      ({ s with nextTransfer := id + 1, sockets := s.sockets.push k, outbox := s.outbox ++ ws.toArray },
        ok ("ok\u0000" ++ toString id ++ "\u0000" ++ k.url))
  | 157 =>
    match at? (nat 0) with
    | none => (s, .error errType)
    | some i =>
      match WebSocket.send s.sockets[i]! (str 1 == "b") (fs.getD 2 ByteArray.empty).toList (entropy.extract 0 4).toList with
      | none => (s, ok "err\u0000InvalidStateError\u0000Still in CONNECTING state.")
      | some (k, ws) => ({ s with sockets := s.sockets.set! i k, outbox := s.outbox ++ ws.toArray }, ok "")
  | 158 =>
    match at? (nat 0) with
    | none => (s, .error errType)
    | some i =>
      let code := (str 1).toNat?
      match WebSocket.closeCheck code (str 2) with
      | some (n, m) => (s, ok ("err\u0000" ++ n ++ "\u0000" ++ m))
      | none =>
        let (k, ws) := WebSocket.close s.sockets[i]! code (str 2) (entropy.extract 0 4).toList
        ({ s with sockets := s.sockets.set! i k, outbox := s.outbox ++ ws.toArray }, ok "")
  | 159 =>
    match at? (nat 0) with
    | none => (s, .error errType)
    | some i =>
      let k := s.sockets[i]!
      (s, ok (match nat 1 with
        | 0 => toString k.readyState | 1 => toString k.buffered | 2 => k.protocol | _ => k.url))
  | 160 =>
    match at? (nat 0) with
    | none => (s, .error errType)
    | some i =>
      let k := s.sockets[i]!
      match k.events[0]? with
      | none => (s, ok "")
      | some e =>
        let k := { k with events := k.events.extract 1 k.events.size }
        let (k, t) := match e with
          | .opened p => (k, "open\u0000" ++ p)
          | .text d => (k, "text\u0000" ++ d)
          | .binary b => ({ k with lastBinary := b }, "binary")
          | .error => (k, "error")
          | .closed c r cl => (k, "close\u0000" ++ toString c ++ "\u0000" ++ r ++ "\u0000" ++ (if cl then "1" else "0"))
        ({ s with sockets := s.sockets.set! i k }, ok t)
  | 161 =>
    match at? (nat 0) with
    | none => (s, .error errType)
    | some i => (s, .ok s.sockets[i]!.lastBinary)
  | _ => (s, .error (-2))

/-- A `web_api` op on the network objects: ops 60 to 79, 98, 99 and 150 to 153 (answers -2 when the embedder
did not turn the network on, so `XMLHttpRequest` is then not defined). -/
def op (s : State) (code : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  -- the policy's questions are answered whether or not the embedder turned the network on
  if 150 ≤ code && code ≤ 153 then cspOp s code fs else
  if !s.enabled then (s, .error (-2)) else
  match code with
  | 60 =>
    if s.xhrs.size ≥ maxObjects then (s, .error (-5))
    else ({ s with xhrs := s.xhrs.push {} }, okStr (toString (s.xhrs.size + 1)))
  | 61 =>
    match openX s (natAt fs 0) (strAt fs 1) (strAt fs 2) (strAt fs 3) (natAt fs 4 != 0) with
    | (s, .ok a) => (s, okStr a)
    | (s, .error e) => (s, .error e)
  | 62 =>
    match setHeaderX s (natAt fs 0) (strAt fs 1) (strAt fs 2) with
    | (s, .ok a) => (s, okStr a)
    | (s, .error e) => (s, .error e)
  | 63 =>
    -- send: handle, cb, listener, hasBody, isText, body, the time in seconds
    let body := if natAt fs 3 != 0 then some (fs.getD 5 ByteArray.empty) else none
    let s := { s with now := max s.now (natAt fs 6) }
    match sendX s (natAt fs 0) body (strAt fs 4) (natAt fs 1) (natAt fs 2 != 0) with
    | (s, .ok a) => (s, okStr a)
    | (s, .error e) => (s, .error e)
  | 64 =>
    match next s (natAt fs 0) with
    | (s, some (up, t, l, tt, c)) =>
      (s, okStr ("\x00".intercalate [if up then "1" else "0", t, toString l, toString tt, if c then "1" else "0"]))
    | (s, none) => (s, okStr "")
  | 65 =>
    match abortX s (natAt fs 0) with
    | (s, .ok a) => (s, okStr a)
    | (s, .error e) => (s, .error e)
  | 66 =>
    match timeoutX s (natAt fs 0) with
    | (s, .ok a) => (s, okStr a)
    | (s, .error e) => (s, .error e)
  | 67 =>
    -- reads: 0 readyState, 1 status, 2 statusText, 3 responseURL, 4 text, 5 deferFail,
    -- 9 the response's tainting (`Response.type` of `fetch`: basic, cors, opaque), 10 null body
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      let body := match natAt fs 1 with
        | 0 => toString x.state
        | 1 => toString (statusOf x)
        | 2 => (x.response.map fun r => if x.state ≥ 2 then r.statusText else "").getD ""
        | 3 => (x.response.map fun r => if x.state ≥ 2 then r.url else "").getD ""
        | 4 => responseText x
        | 5 => if x.deferFail || x.deferred.isSome then "1" else "0"
        | 6 => x.responseType
        | 7 => docKind x
        | 8 => finalMime x
        | 9 => (x.response.map fun r => if x.state ≥ 2 then r.tainting else "").getD ""
        -- 10: "1" when the response's body is null (`PageFetch.nullBody`: a null body status
        -- or a HEAD request)
        | 10 => if PageFetch.nullBody x.method (statusOf x) then "1" else "0"
        | _ => ""
      (s, okStr body)
  | 68 =>
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      match x.response.filter (fun _ => x.state ≥ 2) with
      | none => (s, .error (-1))
      | some r =>
        match headerGet (r.headers) (lower (strAt fs 1)) with
        | none => (s, .error (-1))
        | some v => (s, okStr v)
  | 69 =>
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s, okStr (allHeaders x))
  | 70 =>
    -- overrideMimeType
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      if x.state == 3 || x.state == 4 then (s, .error errInvalidState)
      else
        let m := strAt fs 1
        (s.set (natAt fs 0) { x with mimeOverride := some (if m.contains '/' then m else "application/octet-stream") }, okStr "")
  | 71 =>
    -- responseType
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      let t := strAt fs 1
      -- a value outside the enum is ignored (WebIDL), and outside a window so is
      -- "document" (XHR §4.6.4 step 1), before the state checks
      if !["", "arraybuffer", "blob", "document", "json", "text"].contains t then (s, okStr "") else
      if !s.window && t == "document" then (s, okStr "") else
      if x.state == 3 || x.state == 4 then (s, .error errInvalidState) else
      if s.window && !x.async && x.state != 0 then (s, .error errAccess) else
      (s.set (natAt fs 0) { x with responseType := t }, okStr "")
  | 72 =>
    -- timeout
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      if s.window && !x.async && x.state != 0 then (s, .error errAccess)
      else (s.set (natAt fs 0) { x with timeout := natAt fs 1 }, okStr "")
  | 73 =>
    -- withCredentials (0, 1) or fetch's credentials mode (0 same-origin, 1 include, 2 omit)
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      if x.state > 1 || x.sendFlag then (s, .error errInvalidState)
      else (s.set (natAt fs 0) { x with cred := natAt fs 1 == 1, omitCred := natAt fs 1 == 2 }, okStr "")
  | 75 => (s, okStr "1")
  | 78 =>
    -- the multipart/form-data body of a FormData: five fields an entry (name, "1" for a
    -- file, filename, type, bytes)
    let n := fs.size / 5
    let entries := (List.range n).map fun i =>
      let name := strAt fs (5 * i)
      let v : FormValue := if strAt fs (5 * i + 1) == "1"
        then .file (strAt fs (5 * i + 2)) (strAt fs (5 * i + 3)) (fs.getD (5 * i + 4) ByteArray.empty)
        else .text (strAt fs (5 * i + 4))
      (name, v)
    let body := formDataBody entries
    if body.size > maxBody then (s, .error (-5)) else (s, .ok body)
  | 165 =>
    -- an element's request (the prelude's own, never a page's): handle, destination, "1" raw
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with destination := strAt fs 1, raw := strAt fs 2 == "1" }, okStr "")
  | 79 =>
    -- the redirect mode (`fetch`): 1 "error" (`PageFetch.onAnswer_redirect_error`), 2 "manual"
    -- (an opaque-redirect response), else "follow"
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with redirectError := natAt fs 1 == 1, redirectManual := natAt fs 1 == 2 }, okStr "")
  | 98 =>
    -- the request's referrer and referrer policy (`fetch`): handle, referrer ("" none,
    -- "about:client" the client, else a URL: `setReferrer`), policy token ("" the
    -- client's), then the document that asks when it is a frame's (URL and policy token,
    -- both "" for the session's own)
    let h := natAt fs 0
    match s.get? h with
    | none => (s, .error errType)
    | some _ =>
      let s := if strAt fs 3 == "" && strAt fs 4 == "" then s else setClient s h (strAt fs 3) (strAt fs 4)
      let s := if strAt fs 1 == "about:client" then s else setReferrer s h (strAt fs 1)
      match s.get? h with
      | none => (s, .error errType)
      | some x => (s.set h { x with policy := ReferrerPolicy.Policy.ofToken (strAt fs 2) }, okStr "")
  | 99 =>
    -- the request's integrity metadata (`fetch`'s `integrity`)
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with integrity := strAt fs 1 }, okStr "")
  | 77 =>
    -- the mode (`fetch`): 1 "same-origin", 2 "no-cors", else "cors"
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with sameOnly := natAt fs 1 == 1, noCors := natAt fs 1 == 2 }, okStr "")
  | 76 =>
    -- the deferred error of a `send` that the policy refused, or the response made here (a
    -- `data:` URL), at the page's next task
    let h := natAt fs 0
    match s.get? h with
    | some x =>
      match x.deferred with
      | some r =>
        if !x.sendFlag || x.state != 1 then (s.set h { x with deferred := none }, okStr "") else
        if r.body.size > maxBody || s.held + r.body.size > maxHeld then (requestError s h x "error", okStr "") else
        ((s.set h { x with deferred := none, response := some r, uploadComplete := true, events := x.events ++ responseEvents x r })
          |> fun s => { s with held := s.held + r.body.size }, okStr "")
      | none => if x.deferFail then (requestError s h x "error", okStr "") else (s, okStr "")
    | none => (s, .error errType)
  | 74 =>
    -- the body as bytes (responseType "arraybuffer")
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      match x.response.filter (fun _ => x.state == 4) with
      | some r => (s, .ok r.body)
      | none => (s, .ok ByteArray.empty)
  | _ => (s, .error (-2))

/-! ## Checks (`#guard` is a test) -/

#guard PageFetch.isoString (formDataBody [("a", .text "x\ny"), ("f\"", .file "n.txt" "" "hi".toUTF8)]) ==
  "------FoafnautFormBoundary0\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nx\r\ny\r\n" ++
  "------FoafnautFormBoundary0\r\nContent-Disposition: form-data; name=\"f%22\"; filename=\"n.txt\"\r\nContent-Type: application/octet-stream\r\n\r\nhi\r\n" ++
  "------FoafnautFormBoundary0--\r\n"
#guard boundaryFor [.text "----FoafnautFormBoundary0"] == "----FoafnautFormBoundary1"
#guard PageFetch.isoString (formDataBody []) == "------FoafnautFormBoundary0--\r\n"

private def st : State := { enabled := true, page := Page.ofUrl "http://a.example/x" }

private def run1 (s : State) (c : Nat) (args : List String) : State × String :=
  match op s c (args.map String.toUTF8).toArray with
  | (s, .ok b) => (s, String.fromUTF8! b)
  | (s, .error e) => (s, s!"err {e}")

-- open, send, the host's request; a same-origin GET has no Origin header
private def sent : State :=
  let s := (run1 st 60 []).1
  let s := (run1 s 61 ["1", "get", "y", "http://a.example/d/x", "1"]).1
  (run1 s 63 ["1", "7", "0", "0", "", ""]).1

#guard (sent.get? 1).any (·.state == 1)
#guard (run1 sent 64 ["1"]).2 == "0\x00loadstart\x000\x000\x000"

-- the page is not local: the name is resolved first, then the request goes to that address
private def started0 : State := (run1 (run1 sent 64 ["1"]).1 64 ["1"]).1

#guard started0.outbox.size == 1 && (started0.outbox[0]?).any (·.resolve)

private def started : State := (give started0 1 { addresses := ["93.184.215.14"] }).1

#guard started.outbox.size == 2
#guard (started.outbox[1]?).any fun w => w.url == "http://a.example/d/y" && w.method == "GET" &&
  w.headers == [("Accept", "*/*")] && w.address == "93.184.215.14" && w.port == 80 && !w.resolve
#guard (run1 started 67 ["1", "0"]).2 == "1"
#guard started.waiting

-- the answer: events in order of the standard, text decoded
private def answered : State :=
  (give started 1 { status := 200, statusText := "OK", headers := [("content-type", "text/plain; charset=utf-8")], body := "héllo".toUTF8 }).1

private def drain (s : State) : List String := Id.run do
  let mut s := s
  let mut out : List String := []
  for _ in [0:16] do
    let (s', a) := run1 s 64 ["1"]
    s := s'
    if a.isEmpty then break
    out := out ++ [(a.splitOn "\x00").getD 1 ""]
  return out

#guard drain answered == ["readystatechange", "readystatechange", "progress", "readystatechange", "load", "loadend"]
#guard (run1 (run1 answered 64 ["1"]).1 67 ["1", "1"]).2 == "200"

-- a cross-origin URL with no ACAO: error, no status
private def refused : State :=
  let s := (run1 st 60 []).1
  let s := (run1 s 61 ["1", "GET", "http://b.example/", "", "1"]).1
  let s := (run1 s 63 ["1", "9", "0", "0", "", ""]).1
  let s := (run1 (run1 s 64 ["1"]).1 64 ["1"]).1
  let s := (give s 1 { addresses := ["93.184.215.14"] }).1
  (give s 1 ({ status := 200, body := "secret".toUTF8 } : Answer)).1

#guard drain refused == ["readystatechange", "error", "loadend"]
#guard (run1 refused 67 ["1", "1"]).2 == "0"
#guard (run1 refused 67 ["1", "4"]).2 == ""

-- a local target from a public page never reaches the outbox
private def localTarget : State :=
  let s := (run1 st 60 []).1
  let s := (run1 s 61 ["1", "GET", "http://127.0.0.1/", "", "1"]).1
  let s := (run1 s 63 ["1", "9", "0", "0", "", ""]).1
  (run1 (run1 s 64 ["1"]).1 64 ["1"]).1

#guard localTarget.outbox.isEmpty

-- off unless the embedder turned it on
#guard (run1 {} 60 []).2 == "err -2"

-- The referrer (Fetch §5.4 `Request` constructor steps 14 and 15; fetch/api/request/request-init-002,
-- fetch/api/basic/referrer.any.js): the client's URL unless the page names one of its own origin
private def stc : State := { st with client := "http://a.example/dir/page.html?q#f", page := { st.page with isLocal := true } }
private def wireOf (s : State) (url : String) (opts : List String) : Option Wire :=
  let s := (run1 s 60 []).1
  let s := (run1 s 61 ["1", "GET", url, "", "1"]).1
  let s := if opts.isEmpty then s else (run1 s 98 ("1" :: opts)).1
  let s := (run1 s 63 ["1", "7", "0", "0", "", ""]).1
  let s := (run1 (run1 s 64 ["1"]).1 64 ["1"]).1
  s.outbox[0]?
private def refOf (s : State) (url : String) (opts : List String) : Option String :=
  (wireOf s url opts).bind fun w => headerGet w.headers "referer"
#guard refOf stc "http://a.example/y" [] == some "http://a.example/dir/page.html?q"
#guard refOf stc "http://b.example/y" [] == some "http://a.example/"
#guard refOf stc "http://a.example/y" ["", "", "", ""] == none
#guard refOf stc "http://a.example/y" ["about:client", "origin", "", ""] == some "http://a.example/"
#guard refOf stc "http://a.example/y" ["http://a.example/other#x", "", "", ""] == some "http://a.example/other"
-- a URL of another origin is not taken: the client's is used
#guard refOf stc "http://a.example/y" ["http://evil.example/other", "", "", ""] == some "http://a.example/dir/page.html?q"
#guard refOf stc "http://b.example/y" ["about:client", "unsafe-url", "", ""] == some "http://a.example/dir/page.html?q"
#guard refOf stc "http://b.example/y" ["about:client", "no-referrer", "", ""] == none
-- the client's policy (its Referrer-Policy field) when the request names none
#guard refOf { stc with policy := policyOfHeader "origin" } "http://a.example/y" [] == some "http://a.example/"
#guard refOf { stc with policy := policyOfHeader "bogus, no-referrer" } "http://a.example/y" [] == none
#guard policyOfHeader "bogus" == .strictOriginWhenCrossOrigin
-- a same-origin frame's document asks: its URL and its policy; a document of another
-- origin, or with no URL of its own, is never named: no referrer
#guard refOf stc "http://a.example/y" ["about:client", "", "http://a.example/frame.html", ""] == some "http://a.example/frame.html"
#guard refOf stc "http://a.example/y" ["about:client", "", "http://a.example/frame.html", "origin"] == some "http://a.example/"
#guard refOf stc "http://a.example/y" ["about:client", "", "http://evil.example/frame.html", ""] == none
#guard refOf stc "http://a.example/y" ["about:client", "", "about:blank", "unsafe-url"] == none
-- an embedder that names no client: no Referer at all
#guard refOf { stc with client := "" } "http://b.example/y" [] == none

-- fetch's mode "no-cors" (op 77 with 2): the answer of another origin is opaque, with no
-- text, no status and no fields for the page; the same answer in mode "cors" is refused
private def modeRun (mode : String) : State :=
  let s := (run1 stc 60 []).1
  let s := (run1 s 61 ["1", "GET", "http://b.example/", "", "1"]).1
  let s := (run1 s 77 ["1", mode]).1
  let s := (run1 s 63 ["1", "9", "0", "0", "", ""]).1
  let s := (run1 (run1 s 64 ["1"]).1 64 ["1"]).1
  (give s 1 ({ status := 200, headers := [("X-S", "1")], body := "secret".toUTF8 } : Answer)).1
#guard drain (modeRun "2") == ["readystatechange", "readystatechange", "load", "loadend"]
private def drained (s : State) : State := Id.run do
  let mut s := s
  for _ in [0:16] do
    let (s', a) := run1 s 64 ["1"]
    s := s'
    if a.isEmpty then break
  return s
#guard (run1 (drained (modeRun "2")) 67 ["1", "9"]).2 == "opaque"
#guard (run1 (drained (modeRun "2")) 67 ["1", "1"]).2 == "0" && (run1 (drained (modeRun "2")) 67 ["1", "4"]).2 == ""
#guard (run1 (drained (modeRun "2")) 69 ["1"]).2 == ""
#guard drain (modeRun "0") == ["readystatechange", "error", "loadend"]

-- Content Security Policy: connect-src governs the requests of fetch and XMLHttpRequest
-- (WPT content-security-policy/connect-src); a blocked one is a network error with one
-- violation to report; a report-only policy reports and lets it go; a meta may not report
private def stp (header : String) (ro : String := "") : State := { stc with csp := cspOf header ro "" }
private def tryGet (s : State) (url : String) : State :=
  let s := (run1 s 60 []).1
  let s := (run1 s 61 ["1", "GET", url, "", "1"]).1
  let s := (run1 s 63 ["1", "7", "0", "0", "", ""]).1
  (run1 (run1 s 64 ["1"]).1 64 ["1"]).1
#guard (tryGet (stp "connect-src 'self'") "http://a.example/y").outbox.size == 1
#guard (tryGet (stp "connect-src 'self'") "http://b.example/y").outbox.size == 0
#guard (tryGet (stp "connect-src 'self'") "http://b.example/y").violations.toList ==
  ["connect-src\x00http://b.example/y\x00connect-src 'self'\x00enforce\x000\x00"]
#guard (tryGet (stp "default-src 'none'") "http://a.example/y").outbox.size == 0
#guard (tryGet (stp "img-src 'none'") "http://b.example/y").outbox.size == 1
#guard (tryGet (stp "" "connect-src 'none'") "http://b.example/y#frag").outbox.size == 1
#guard (tryGet (stp "" "connect-src 'none'") "http://b.example/y#frag").violations.toList ==
  ["connect-src\x00http://b.example/y\x00connect-src 'none'\x00report\x000\x00"]
#guard (run1 (tryGet (stp "connect-src 'self'") "http://b.example/y") 150 []).1.violations.isEmpty
#guard (run1 (stp "connect-src 'self'") 150 ["?"]).2 == "1" && (run1 stc 150 ["?"]).2 == "0"
-- a redirect to a URL the policy forbids is a network error
#guard drain (give (tryGet (stp "connect-src http://a.example") "http://a.example/y") 1
    ({ status := 302, headers := [("Location", "http://b.example/z")] } : Answer)).1 == ["readystatechange", "error", "loadend"]
-- the questions the prelude asks: a script element, an inline script, eval; and with the
-- network off they are still answered
#guard (run1 (stp "script-src 'self'") 151 ["script-src-elem", "http://b.example/a.js", "", "0", "7"]).2 == "1"
#guard (run1 (stp "script-src 'self'") 151 ["script-src-elem", "http://a.example/a.js", "", "0", "7"]).2 == "0"
#guard (run1 (stp "script-src 'nonce-n1'") 151 ["script-src-elem", "http://b.example/a.js", "n1", "0", "7"]).2 == "0"
#guard (run1 (stp "script-src 'self'") 152 ["1", "1", "", "alert(1)", "9"]).2 == "1"
#guard (run1 (stp "script-src 'unsafe-inline'") 152 ["1", "1", "", "alert(1)", "9"]).2 == "0"
#guard (run1 (stp "script-src 'self'") 153 []).2 == "1" && (run1 (stp "script-src 'unsafe-eval'") 153 []).2 == "0"
#guard (run1 { stp "script-src 'self'" with enabled := false } 153 []).2 == "1"
#guard (run1 stc 152 ["1", "1", "", "alert(1)", "9"]).2 == "0"
#guard (cspOf "" "" "script-src 'none'; report-uri /r; sandbox").map (·.directives.map (·.name)) == [["script-src"]]

/-- Kind: resource bound. Says: a session keeps at most `maxPins` addresses. -/
theorem notePin_bounded (s : State) (t : Transfer) (h : s.pins.size ≤ maxPins) : (s.notePin t).pins.size ≤ maxPins := by
  unfold State.notePin
  split
  · rename_i p _
    by_cases h1 : (s.pins.any (·.1 == p.1) || decide (s.pins.size ≥ maxPins)) = true
    · simp only [h1, if_true]; exact h
    · simp only [h1, if_false, Bool.false_eq_true, Array.size_push]
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at h1
      omega
  · exact h

/-- Kind: lemma (DNS pins). Says: the pin a new request starts with is one this session chose
for the name of the request's URL. -/
theorem pinFor_name (s : State) (url : String) (p : String × String) (h : s.pinFor url = some p) :
    p ∈ s.pins ∧ ∃ u, URL.parseUrl url = some u ∧ p.1 = lower u.hostname := by
  unfold State.pinFor at h
  split at h
  · rename_i u hu
    have hm := Array.mem_of_find?_eq_some h
    have hp := Array.find?_some h
    exact ⟨hm, u, hu, by simpa using hp⟩
  · simp at h

/-- Kind: security theorem (DNS pins). Says: a name's pin is never replaced: once the session
holds an address for a name, keeping another transfer's pin leaves that name's first pin as
it was, so a pinned name never resolves to a different address within the session (a later
answer of the name server cannot move the page to another host, DNS rebinding). -/
theorem notePin_keeps (s : State) (t : Transfer) (n : String) (p : String × String)
    (h : s.pins.find? (·.1 == n) = some p) : (s.notePin t).pins.find? (·.1 == n) = some p := by
  unfold State.notePin
  split
  · rename_i q _
    split
    · exact h
    · rw [← Array.find?_toList] at h ⊢
      simp only [Array.toList_push, List.find?_append, h, Option.some_or]
  · exact h

/-- Kind: security theorem (DNS pins). Says: over any sequence of transfers the session keeps,
the pin a request to a pinned URL starts with stays the same. -/
theorem pinFor_stable (s : State) (ts : List Transfer) (url : String) (p : String × String)
    (h : s.pinFor url = some p) : (ts.foldl State.notePin s).pinFor url = some p := by
  induction ts generalizing s with
  | nil => exact h
  | cons t ts ih =>
    apply ih
    unfold State.pinFor at h ⊢
    cases hu : URL.parseUrl url with
    | none => simp [hu] at h
    | some u =>
      simp only [hu] at h ⊢
      exact notePin_keeps s t _ p h

/-- Kind: privacy lemma. Says: a URL the page names as a referrer, or a frame document's URL
named as the client, is kept only when it parses and is of the page's own origin, and then
in its serialized form: `fetch(url, {referrer})` cannot make the engine send another
origin's URL as the `Referer`. Does not say: what is then sent of it (`PageFetch.referrerOf`
and its theorems). -/
theorem ownUrl_same (p : Page) (url r : String) (h : ownUrl p url = some r) :
    ∃ u, URL.parseUrl url = some u ∧ sameOrigin p u = true ∧ r = u.serialize := by
  unfold ownUrl at h
  split at h
  · rename_i u hu
    split at h
    · rename_i hs
      exact ⟨u, hu, hs, by simpa using h.symm⟩
    · simp at h
  · simp at h

/-- Kind: policy theorem. Says: with the network off (the embedder did not say
`network:true`), no op of the network objects does anything: each answers -2 and the state
is unchanged, so no request can be made. The four Content Security Policy ops (150 to 153)
are not network ops: they answer in every session and make no request (`cspOp` writes only
`violations`). -/
theorem op_off (s : State) (c : Nat) (fs : Array ByteArray) (h : s.enabled = false)
    (hc : ¬(150 ≤ c ∧ c ≤ 153)) : op s c fs = (s, .error (-2)) := by
  have : (decide (150 ≤ c) && decide (c ≤ 153)) = false := by
    simpa using hc
  simp [op, h, this]

/-- Kind: security invariant (blob URLs). Says: the bytes a request of this page reads for a
`blob:` URL are those of an entry that the page's own origin made: no page reads another
origin's blob through its URL. Does not say: anything of `http` requests (`Net.PageFetch`). -/
theorem blobOf_own (s : State) (url : String) (r : String × ByteArray) (h : s.blobOf url = some r) :
    ∃ e, L4Factoidal.Net.BlobUrls.resolve s.blobs s.page.origin url = some e ∧
      e.origin = s.page.origin ∧ r = (e.type, e.body) := by
  unfold State.blobOf at h
  split at h
  · cases hr : L4Factoidal.Net.BlobUrls.resolve s.blobs s.page.origin url with
    | none => simp [hr] at h
    | some e =>
      simp [hr] at h
      exact ⟨e, rfl, L4Factoidal.Net.BlobUrls.resolve_origin _ _ _ _ hr, h.symm⟩
  · simp at h

end L4Factoidal.Net.Xhr
