/-
L4Factoidal.Net.Xhr — XMLHttpRequest (https://xhr.spec.whatwg.org/) as a state machine on
`Net.PageFetch`, for page scripts on both JavaScript engines
(https://github.com/danbri/factoidal-core/issues/374; the record of the design is in
`docs/designissues/2026-11-10-page-network.md` when it lands).

The state of each object, what a method may do, the order of its events and the text of
its answer are here. `tools/wasmvm/quickjs/prelude.js` holds a class whose methods call
`web_api` ops 60 to 79 (`Hosts.WebApi`), and fires the events this file lists.

Sync requests are not yet done (`send` answers NotSupportedError). Cookies are never sent
or stored (`Net.PageFetch`). Only `""`, `"text"`, `"json"` and `"arraybuffer"` response
types have a value; the others answer `null`.

Each event is one `next` call of the page's task, so a script that runs in the middle of a
sequence sees the state of that point. `Ev.setState`, `.guardDone` and `.startFetch` are
the steps that are not events, in the place the standard has them.
-/
import L4Factoidal.Net.PageFetch
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
  timeout : Nat := 0
  responseType : String := ""
  mimeOverride : Option String := none
  uploadComplete : Bool := false
  uploadListener : Bool := false
  response : Option Response := none
  /-- `send` could not start (policy): the error steps wait for the page's next task. -/
  deferFail : Bool := false
  transfer : Option Nat := none
  /-- The page's callback that runs the events of this object when the host answers. -/
  cb : Nat := 0
  events : Array Ev := #[]
  deriving Inhabited

structure State where
  /-- The embedder turned the network on (`network:true`). -/
  enabled : Bool := false
  page : Page := Page.ofUrl ""
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
  deriving Inhabited

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
  s.set h { x with state := 4, sendFlag := false, response := none, deferFail := false, uploadComplete := true,
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
    if !async && (x.timeout != 0 || x.responseType != "") then (s, .error errAccess) else
    let u' := { u with username := "", password := "" }
    let (s, x) := stopFetch s x
    let x' := { x with method := normalizeMethod method, url := u'.serialize true, async, headers := #[], body := none,
                       sendFlag := false, uploadListener := false, uploadComplete := false, response := none,
                       deferFail := false, events := #[] }
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
  if forbiddenRequestHeader name then (s, .ok "") else
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
  for _ in [0:2 * maxRedirects + 8] do
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
  let t : Transfer := { id, page := s.page, method := x.method, url := x.url, headers := x.headers.toList, body := x.body, credentials := x.cred, sameOriginOnly := x.sameOnly }
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
  let t : Transfer := { id, page := s.page, method := x.method, url := x.url, headers := x.headers.toList, body := x.body, credentials := x.cred, sameOriginOnly := x.sameOnly }
  match plan t with
  | .send t' w => (s.set h { x with transfer := some id }) |> fun s => { s with live := s.live.push (id, h, t'), outbox := s.outbox.push w }
  | .fail _ | .deliver .. => s.set h { x with deferFail := true }

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

/-- `getAllResponseHeaders()`: names lowercased and sorted, one `name: value` CRLF each. -/
def allHeaders (x : Xhr) : String :=
  match x.response with
  | none => ""
  | some r =>
    if x.state < 2 then "" else
    let hs := r.headers.map fun (n, v) => (lower n, v)
    let sorted := (hs.toArray.qsort (fun a b => a.1 < b.1)).toList
    String.join (sorted.map fun (n, v) => n ++ ": " ++ v ++ "\r\n")

/-- One field of a `web_api` call as a string. -/
private def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

private def natAt (fs : Array ByteArray) (i : Nat) : Nat := (strAt fs i).toNat?.getD 0

private def okStr (x : String) : Except Int ByteArray := .ok x.toUTF8

/-- A `web_api` op on the network objects: ops 60 to 79 (answers -2 when the embedder
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
        | 5 => if x.deferFail then "1" else "0"
        | 6 => x.responseType
        | 7 => docKind x
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
      if x.state == 3 || x.state == 4 then (s, .error errInvalidState) else
      if !x.async && x.state != 0 then (s, .error errAccess) else
      let t := strAt fs 1
      if ["", "arraybuffer", "blob", "document", "json", "text"].contains t then
        (s.set (natAt fs 0) { x with responseType := t }, okStr "")
      else (s, okStr "")
  | 72 =>
    -- timeout
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      if !x.async && x.state != 0 then (s, .error errAccess)
      else (s.set (natAt fs 0) { x with timeout := natAt fs 1 }, okStr "")
  | 73 =>
    -- withCredentials: only the CORS check changes (no credentials exist to send)
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x =>
      if x.state > 1 || x.sendFlag then (s, .error errInvalidState)
      else (s.set (natAt fs 0) { x with cred := natAt fs 1 != 0 }, okStr "")
  | 75 => (s, okStr "1")
  | 77 =>
    -- mode same-origin (`fetch`)
    match s.get? (natAt fs 0) with
    | none => (s, .error errType)
    | some x => (s.set (natAt fs 0) { x with sameOnly := natAt fs 1 != 0 }, okStr "")
  | 76 =>
    -- the deferred error of a `send` that the policy refused (the page's next task)
    match s.get? (natAt fs 0) with
    | some x => if x.deferFail then (requestError s (natAt fs 0) x "error", okStr "") else (s, okStr "")
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

private def started : State := (run1 (run1 sent 64 ["1"]).1 64 ["1"]).1

#guard started.outbox.size == 1
#guard (started.outbox[0]?).any fun w => w.url == "http://a.example/d/y" && w.method == "GET" && w.headers == [("Accept", "*/*")]
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

/-- Kind: invariant of `sendX` and `next`. Says: when the object is not enabled the op
answers -2 and changes nothing, so a page in a host that did not turn the network on has
no `XMLHttpRequest` and no request can be sent. Does not say: anything else of ops. -/
theorem op_off (s : State) (c : Nat) (fs : Array ByteArray) (h : s.enabled = false) :
    op s c fs = (s, .error (-2)) := by
  simp [op, h]

end L4Factoidal.Net.Xhr
