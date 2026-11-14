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
  /-- Fetch mode "same-origin" (`fetch`); XHR is always "cors". -/
  sameOnly : Bool := false
  /-- Fetch redirect mode "error" (`fetch`); XHR always follows. -/
  redirectError : Bool := false
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
  /-- The blob URLs of the session (`URL.createObjectURL`), each its origin's (`Net.BlobUrls`). -/
  blobs : L4Factoidal.Net.BlobUrls.Store := {}
  xhrs : Array Xhr := #[]
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
  for _ in [0:4 * maxRedirects + 8] do
    match step with
    | .fail _ => return (s, .failed)
    | .deliver _ r => return (s, .done r)
    | .send t w =>
      match s.syncAnswers[s.syncUsed]? with
      -- the first request the run needs wins: a page that catches the throw and goes on
      -- does not change what the host is asked (`syncWanted` is set once in a run)
      | none => return ({ s with syncWanted := s.syncWanted.orElse fun _ => some w }, .need)
      | some a =>
        s := { s with syncUsed := s.syncUsed + 1 }
        step := onAnswer t a
  return (s, .failed)

/-- Sync `send` (XHR §4.5.2 step 12): the fetch happens now; on failure a `NetworkError` is
thrown; on success the object is done with its last events. `send` has no `loadstart` in
this mode (the steps "if xhr's synchronous flag is unset" hold it). -/
def syncSend (s : State) (h : Nat) (x : Xhr) : State × Except Int String :=
  let id := s.nextTransfer
  let s := { s with nextTransfer := id + 1 }
  let t : Transfer := { id, page := s.page, method := x.method, url := x.url, headers := x.headers.toList, body := x.body, credentials := x.cred, sameOriginOnly := x.sameOnly, redirectError := x.redirectError, blob := s.blobOf x.url, referrer := referrerFor s x, referrerPolicy := policyFor s x }
  let (s, out) := syncFetch s t
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
  let id := s.nextTransfer
  let s := { s with nextTransfer := id + 1 }
  let t : Transfer := { id, page := s.page, method := x.method, url := x.url, headers := x.headers.toList, body := x.body, credentials := x.cred, sameOriginOnly := x.sameOnly, redirectError := x.redirectError, blob := s.blobOf x.url, referrer := referrerFor s x, referrerPolicy := policyFor s x }
  match plan t with
  | .send t' w => (s.set h { x with transfer := some id }) |> fun s => { s with live := s.live.push (id, h, t'), outbox := s.outbox.push w }
  | .deliver _ r => s.set h { x with deferred := some r }
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

/-- The host's answer to a fetch. The callback of the object, when a task is to run it. -/
def give (s : State) (id : Nat) (a : Answer) : State × Option Nat :=
  match s.live.find? (·.1 == id) with
  | none => (s, none)
  | some (_, h, t) =>
    match s.get? h with
    | none => ({ s with live := s.live.filter (·.1 != id) }, none)
    | some x =>
    let s1 := { s with live := s.live.filter (·.1 != id) }
    match onAnswer t a with
    | .send t' w => ({ s with live := s.live.map (fun e => if e.1 == id then (id, h, t') else e), outbox := s.outbox.push w }, none)
    | .fail _ => (requestError s1 h { x with transfer := none } "error", some x.cb)
    | .deliver _ r =>
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

/-- A `web_api` op on the network objects: ops 60 to 79 and 98 (answers -2 when the embedder
did not turn the network on, so `XMLHttpRequest` is then not defined). -/
def op (s : State) (code : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
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
    -- send: handle, cb, listener, hasBody, isText, body
    let body := if natAt fs 3 != 0 then some (fs.getD 5 ByteArray.empty) else none
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
    -- reads: 0 readyState, 1 status, 2 statusText, 3 responseURL, 4 text, 5 deferFail
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
    -- withCredentials: only the CORS check changes (no credentials exist to send)
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      if x.state > 1 || x.sendFlag then (s, .error errInvalidState)
      else (s.set (natAt fs 0) { x with cred := natAt fs 1 != 0 }, okStr "")
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
  | 79 =>
    -- redirect mode "error" (`fetch`): `PageFetch.onAnswer_redirect_error`
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with redirectError := natAt fs 1 != 0 }, okStr "")
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
  | 77 =>
    -- mode same-origin (`fetch`)
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with sameOnly := natAt fs 1 != 0 }, okStr "")
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

/-- Kind: invariant of `sendX` and `next`. Says: when the object is not enabled the op
answers -2 and changes nothing, so a page in a host that did not turn the network on has
no `XMLHttpRequest` and no request can be sent. Does not say: anything else of ops. -/
theorem op_off (s : State) (c : Nat) (fs : Array ByteArray) (h : s.enabled = false) :
    op s c fs = (s, .error (-2)) := by
  simp [op, h]

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
