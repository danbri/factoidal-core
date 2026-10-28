/-
L4Factoidal.XMPP.HttpRequester — the REQUESTER side of HTTP over XMPP
(XEP-0332), for the local proxy `factoidal xmpp-http-proxy`.
https://github.com/danbri/factoidal/issues/1107, step 2 of the order the
owner approved on 2026-10-28. Design record:
`docs/designissues/2026-10-28-http-over-xmpp.md`, section "Step 2".

The serving side is `HttpOverXmpp` (`plan`, `finish`). This module is the
other end: an HTTP request record goes in, the stanzas to send come out; the
`resp` (and its `chunk` messages) come back in, an HTTP response record comes
out. It is a total state machine with four entries:

  `send`     an HTTP request to the stanzas to send to `Config.target`, or
             a local refusal (an HTTP response made here)
  `receive`  one stanza from the XMPP stream: a response, an error, a chunk
  `tick`     the host's clock: requests past their deadline get 504
  `abortAll` the stream ended: every waiting request gets 502

The host moves bytes: it reads the HTTP request from its loopback listener,
gives it to `send` (through the wasm op `xmppClientRequest`), writes the
stanzas on the client stream (`ClientStream`), gives each stanza it reads to
`receive`, calls `tick` with its clock, and writes each finished response.

Invariants (design record, "Step 2: invariants"; the theorems are at the end):

* The proxy sends stanzas to `Config.target` and to no other JID
  (`send_to_target`, `receive_to_target`, `tick_to_target`). An `Addressed`
  stanza is rendered with its `to` field as the `to` attribute
  (`Addressed.render`), so the theorems are about the wire addressee.
* A stanza from any JID other than `Config.target` changes nothing and
  answers nothing (`receiveNode_other_sender`).
* The headers sent are the client's headers less the hop-by-hop ones
  (RFC 9110 section 7.6.1): a sublist, so the proxy adds no header, no
  credential of its own (`forwardHeaders_sublist`); `Authorization` passes
  unchanged (`forwardHeaders_keeps_authorization`). `Proxy-Authorization`
  is for this proxy and is not forwarded.
* Limits: a request body above `maxBodyBytes` gets 413 and nothing is sent;
  more than `maxPending` waiting requests, 503; a response above
  `maxResponseBytes`, 502 and a `close` for its stream; a request with no
  answer by its deadline, 504.

Choices (implementer; XEP-0332 does not make them):

1. Request bodies are always `base64` (up to `inlineLimit` bytes) or
   `chunkedBase64`: byte-exact. `text` and `xml` are not used for requests,
   because an XML reader normalises line ends and the `xml` form keeps the
   element, not the bytes.
2. Only origin-form request targets (`/path`) and `*` for OPTIONS are
   sent. An absolute-form target (`http://other.example/`) gets 400: this is
   not a forward proxy. CONNECT gets 405 here (XEP-0332 excludes it).
3. Stanza errors map to HTTP statuses (`statusOfCondition`): `forbidden` and
   `not-authorized` 403, `not-allowed` 405, `bad-request` 400,
   `feature-not-implemented` 501, `resource-constraint` 503,
   `remote-server-timeout` 504, every other condition 502.
4. A response's `content-length`, `transfer-encoding` and the other
   hop-by-hop headers are dropped; the host frames the body.
5. JID comparison of the sender with the target: full JID, domain part in
   lower case, local part and resource exact. PRECIS is not applied
   (https://github.com/danbri/factoidal/issues/676).

No `partial`, no `sorry`, no `axiom`. Lists over input-proportional data go
through core combinators (`filter`, `map`, `foldl`) and
`HttpOverXmpp.splitChunks`/`assembleChunks`, which are tail calls.
-/
import L4Factoidal.XMPP.HttpOverXmpp

namespace L4Factoidal.XMPP.HttpRequester

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP.Server (elemName elemAttr elemChildren)
open L4Factoidal.XMPP.HttpOverXmpp (Req Resp Envelope Chunk Body nsHttp kid? attr)

structure Config where
  /-- The full JID of the serving side (`webdav-serve --xmpp`). The only
  addressee of every stanza this module makes. -/
  target : String
  /-- Milliseconds a request waits for its response. -/
  timeoutMs : Nat := 60000
  /-- The largest request body sent. -/
  maxBodyBytes : Nat := 16 * 1024 * 1024
  /-- The largest response body accepted (in chunks). -/
  maxResponseBytes : Nat := 64 * 1024 * 1024
  /-- A request body longer than this goes `chunkedBase64`. -/
  inlineLimit : Nat := 65536
  /-- Content bytes per request chunk, and the `maxChunkSize` asked for. -/
  chunkSize : Nat := 65536
  /-- Requests waiting for their response at once. -/
  maxPending : Nat := 16
deriving Inhabited

/-- An HTTP request as the host's listener read it. -/
structure HttpRequest where
  method : String
  target : String
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
deriving Inhabited

/-- An HTTP response for the host's listener to write. -/
structure HttpResponse where
  status : Nat
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
deriving Inhabited

/-- A request sent, waiting for its `resp` (and chunks). -/
structure Waiting where
  id : String
  method : String
  deadline : Nat
  /-- The `resp` of a chunked response, while its chunks arrive. -/
  resp : Option Resp := none
  streamId : Option String := none
  chunks : List Chunk := []
  bytes : Nat := 0
deriving Inhabited

structure State where
  serial : Nat := 0
  waiting : List Waiting := []
deriving Inhabited

/-- A stanza to send. `render` writes `to` as the `to` attribute; `attrs`
never holds `to` (every `Addressed` is made in this module). -/
structure Addressed where
  to : String
  kind : String
  attrs : List Attribute
  children : List Node
deriving Inhabited

def Addressed.render (a : Addressed) : String :=
  L4Factoidal.XMPP.Wire.render (.element a.kind (⟨"to", a.to⟩ :: a.attrs) a.children)

/-- A finished request: its id and the response for the listener. -/
structure Done where
  id : String
  response : HttpResponse

structure Step where
  st : State
  send : List Addressed := []
  done : List Done := []

/-! ## Headers -/

/-- RFC 9110 section 7.6.1 connection-specific fields, plus
`proxy-authorization` and `proxy-authenticate` (for this proxy only). -/
def hopByHop : List String :=
  ["connection", "keep-alive", "proxy-connection", "proxy-authorization", "proxy-authenticate",
   "te", "trailer", "transfer-encoding", "upgrade"]

def forwardHeaders (hs : List (String × String)) : List (String × String) :=
  hs.filter (fun h => !hopByHop.contains h.1.toLower)

/-- Response headers for the listener: hop-by-hop ones and
`content-length` dropped (choice 4). -/
def responseHeaders (hs : List (String × String)) : List (String × String) :=
  hs.filter (fun h => let n := h.1.toLower; !hopByHop.contains n && n != "content-length")

/-! ## Local responses -/

def plain (status : Nat) (msg : String) : HttpResponse :=
  { status, headers := [("content-type", "text/plain; charset=utf-8")], body := (msg ++ "\n").toUTF8 }

/-- Choice 3. -/
def statusOfCondition (c : String) : Nat :=
  if c == "forbidden" || c == "not-authorized" then 403
  else if c == "not-allowed" then 405
  else if c == "bad-request" then 400
  else if c == "feature-not-implemented" then 501
  else if c == "resource-constraint" then 503
  else if c == "remote-server-timeout" then 504
  else 502

/-- The defined condition of an `<iq type='error'>`. -/
def errorCondition (n : Node) : String :=
  match kid? n "error" with
  | none => "undefined-condition"
  | some e =>
    match (HttpOverXmpp.kids e).filterMap (fun c =>
        match elemName c with
        | some t => if t == "text" then none else some t
        | none => none) with
    | t :: _ => t
    | [] => "undefined-condition"

/-! ## Sending -/

def clampChunk (n : Nat) : Nat := min 65536 (max 256 n)

def iqAddressed (target id : String) (r : Req) : Addressed :=
  { to := target, kind := "iq", attrs := [⟨"type", "set"⟩, ⟨"id", id⟩], children := [HttpOverXmpp.reqNode r] }

def chunkAddressed (target : String) (c : Chunk) : Addressed :=
  { to := target, kind := "message", attrs := [], children := [HttpOverXmpp.chunkNode c] }

def closeAddressed (target sid : String) : Addressed :=
  { to := target, kind := "message", attrs := [],
    children := [.element "close" [⟨"xmlns", nsHttp⟩, ⟨"streamId", sid⟩] []] }

/-- Why a request is answered here and not sent, or `none`. -/
def refusal (cfg : Config) (st : State) (r : HttpRequest) : Option HttpResponse :=
  if r.method == "CONNECT" then some (plain 405 "CONNECT is not carried over XMPP (XEP-0332)")
  else if !HttpOverXmpp.methods.contains r.method then some (plain 501 s!"method {r.method} is not carried")
  else if !(r.target.startsWith "/" || (r.target == "*" && r.method == "OPTIONS")) then
    some (plain 400 "only origin-form request targets (/path) are sent: this is not a forward proxy")
  else if r.body.size > cfg.maxBodyBytes then
    some (plain 413 s!"the request body is larger than {cfg.maxBodyBytes} bytes")
  else if st.waiting.length ≥ cfg.maxPending then
    some (plain 503 s!"{cfg.maxPending} requests already wait for an answer")
  else none

/-- The `req` for an accepted request (choice 1 for the body). -/
def reqOf (cfg : Config) (r : HttpRequest) (sid : String) : Req :=
  { method := r.method, resource := r.target, version := "1.1"
    maxChunkSize := some (clampChunk cfg.chunkSize)
    headers := forwardHeaders r.headers
    body := if r.body.size == 0 then .empty
            else if r.body.size ≤ cfg.inlineLimit then .base64 r.body
            else .chunked sid }

/-- An HTTP request from the listener at time `now` (milliseconds). The id
names the request in `Done`. -/
def send (cfg : Config) (st : State) (now : Nat) (r : HttpRequest) : String × Step :=
  let n := st.serial + 1
  let id := s!"fxp{n}"
  let st1 := { st with serial := n }
  match refusal cfg st r with
  | some resp => (id, { st := st1, done := [⟨id, resp⟩] })
  | none =>
    let sid := s!"fxq{n}"
    let q := reqOf cfg r sid
    let chunks := match q.body with
      | .chunked s => HttpOverXmpp.splitChunks s r.body (clampChunk cfg.chunkSize)
      | _ => []
    let w : Waiting := { id, method := r.method, deadline := now + cfg.timeoutMs }
    (id, { st := { st1 with waiting := st1.waiting ++ [w] },
           send := iqAddressed cfg.target id q :: chunks.map (chunkAddressed cfg.target) })

/-! ## Receiving -/

/-- Full JID, domain part in lower case (choice 5). -/
def fullKey (s : String) : Option String :=
  (Jid.parse s).map (fun j => Jid.render { j with domainpart := j.domainpart.toLower })

def fromTarget (cfg : Config) (from_ : Option String) : Bool :=
  match from_.bind fullKey, fullKey cfg.target with
  | some a, some b => a == b
  | _, _ => false

def toHttp (resp : Resp) (body : ByteArray) : HttpResponse :=
  if resp.statusCode < 100 || resp.statusCode > 599 then
    plain 502 s!"the XMPP target answered status {resp.statusCode}"
  else { status := resp.statusCode, headers := responseHeaders resp.headers, body }

def without (st : State) (id : String) : State :=
  { st with waiting := st.waiting.filter (·.id != id) }

/-- An `iq` result or error answering a waiting request. -/
def onIq (cfg : Config) (st : State) (n : Node) : Step :=
  let id := (attr n "id").getD ""
  match st.waiting.find? (·.id == id) with
  | none => { st }
  | some w =>
    if attr n "type" == some "error" then
      let c := errorCondition n
      { st := without st id, done := [⟨id, plain (statusOfCondition c) s!"xmpp error from {cfg.target}: {c}"⟩] }
    else if attr n "type" == some "result" then
      match HttpOverXmpp.respOfIq? n with
      | none => { st := without st id, done := [⟨id, plain 502 "the XMPP target sent a malformed resp"⟩] }
      | some (_, resp) =>
        match resp.body with
        | .chunked sid =>
          { st := { st with waiting := st.waiting.map (fun x =>
              if x.id == id then { x with resp := some resp, streamId := some sid } else x) } }
        | b =>
          let body := if w.method == "HEAD" then ByteArray.empty else (b.bytes?.getD ByteArray.empty)
          { st := without st id, done := [⟨id, toHttp resp body⟩] }
    else { st }

/-- A `chunk` of a waiting chunked response. -/
def onChunk (cfg : Config) (st : State) (c : Chunk) : Step :=
  match st.waiting.find? (fun w => w.streamId == some c.streamId && w.resp.isSome) with
  | none => { st }
  | some w =>
    let w := { w with chunks := c :: w.chunks.filter (·.nr != c.nr), bytes := w.bytes + c.data.size }
    if w.bytes > cfg.maxResponseBytes then
      { st := without st w.id, send := [closeAddressed cfg.target c.streamId],
        done := [⟨w.id, plain 502 s!"the response body is larger than {cfg.maxResponseBytes} bytes"⟩] }
    else
      match HttpOverXmpp.assembleChunks w.chunks, w.resp with
      | some body, some resp => { st := without st w.id, done := [⟨w.id, toHttp resp body⟩] }
      | _, _ => { st := { st with waiting := st.waiting.map (fun x => if x.id == w.id then w else x) } }

/-- One stanza from the stream, as an element. A stanza that is not from
`Config.target` changes nothing (`receiveNode_other_sender`). -/
def receiveNode (cfg : Config) (st : State) (n : Node) : Step :=
  if !fromTarget cfg (attr n "from") then { st }
  else if elemName n == some "iq" then onIq cfg st n
  else if elemName n == some "message" then
    match (kid? n "chunk" (some nsHttp)).bind HttpOverXmpp.chunkOf? with
    | some c => onChunk cfg st c
    | none => { st }
  else { st }

/-- One stanza from the stream, as its wire text. -/
def receive (cfg : Config) (st : State) (text : String) : Step :=
  match L4Factoidal.XMPP.Wire.parseElement text with
  | none => { st }
  | some n => receiveNode cfg st n

/-- The host's clock: every request past its deadline gets 504; a chunked
response in progress gets a `close`. -/
def tick (cfg : Config) (st : State) (now : Nat) : Step :=
  let late := st.waiting.filter (fun w => w.deadline ≤ now)
  { st := { st with waiting := st.waiting.filter (fun w => !(w.deadline ≤ now)) }
    send := late.filterMap (fun w => w.streamId.map (closeAddressed cfg.target))
    done := late.map (fun w => ⟨w.id, plain 504 s!"no answer from {cfg.target} in {cfg.timeoutMs} ms"⟩) }

/-- The stream ended: every waiting request gets 502. -/
def abortAll (_cfg : Config) (st : State) (reason : String) : Step :=
  { st := { st with waiting := [] }
    done := st.waiting.map (fun w => ⟨w.id, plain 502 s!"the XMPP connection closed: {reason}"⟩) }

/-! ## Theorems: the invariants -/

theorem send_to_target (cfg : Config) (st : State) (now : Nat) (r : HttpRequest) :
    ∀ a ∈ (send cfg st now r).2.send, a.to = cfg.target := by
  intro a ha
  unfold send at ha
  split at ha
  · simp at ha
  · simp only [List.mem_cons, List.mem_map] at ha
    rcases ha with h | ⟨c, _, h⟩
    · subst h; rfl
    · subst h; rfl

theorem onIq_send (cfg : Config) (st : State) (n : Node) : (onIq cfg st n).send = [] := by
  unfold onIq
  dsimp only
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem onChunk_to_target (cfg : Config) (st : State) (c : Chunk) :
    ∀ a ∈ (onChunk cfg st c).send, a.to = cfg.target := by
  intro a ha
  unfold onChunk at ha
  split at ha
  · simp at ha
  · dsimp only at ha
    split at ha
    · simp at ha; subst ha; rfl
    · split at ha <;> simp at ha

theorem receiveNode_to_target (cfg : Config) (st : State) (n : Node) :
    ∀ a ∈ (receiveNode cfg st n).send, a.to = cfg.target := by
  intro a ha
  unfold receiveNode at ha
  split at ha
  · simp at ha
  · split at ha
    · rw [onIq_send] at ha; simp at ha
    · split at ha
      · split at ha
        · exact onChunk_to_target cfg st _ a ha
        · simp at ha
      · simp at ha

theorem receive_to_target (cfg : Config) (st : State) (text : String) :
    ∀ a ∈ (receive cfg st text).send, a.to = cfg.target := by
  intro a ha
  unfold receive at ha
  split at ha
  · simp at ha
  · exact receiveNode_to_target cfg st _ a ha

theorem tick_to_target (cfg : Config) (st : State) (now : Nat) :
    ∀ a ∈ (tick cfg st now).send, a.to = cfg.target := by
  intro a ha
  simp only [tick, List.mem_filterMap, Option.map_eq_some_iff] at ha
  rcases ha with ⟨_, _, _, _, h⟩
  subst h; rfl

/-- A stanza from any JID other than the target changes nothing and
answers nothing. -/
theorem receiveNode_other_sender (cfg : Config) (st : State) (n : Node)
    (h : fromTarget cfg (attr n "from") = false) :
    receiveNode cfg st n = { st } := by
  simp [receiveNode, h]

/-- The proxy adds no header: what it sends is a sublist of what the client
sent. -/
theorem forwardHeaders_sublist (hs : List (String × String)) :
    (forwardHeaders hs).Sublist hs :=
  List.filter_sublist

/-- `Authorization` passes unchanged. -/
theorem forwardHeaders_keeps_authorization (hs : List (String × String)) (n v : String)
    (hn : n.toLower = "authorization") (h : (n, v) ∈ hs) :
    (n, v) ∈ forwardHeaders hs := by
  simp only [forwardHeaders, List.mem_filter]
  refine ⟨h, ?_⟩
  simp only [hn]
  decide

/-- The request sent carries exactly the forwarded headers. -/
theorem reqOf_headers (cfg : Config) (r : HttpRequest) (sid : String) :
    (reqOf cfg r sid).headers = forwardHeaders r.headers := rfl

/-! ## `#guard`s -/

def tcfg : Config := { target := "bob@example.org/dav", timeoutMs := 1000, inlineLimit := 512, chunkSize := 300 }

def getReq : HttpRequest :=
  { method := "GET", target := "/notes/a.txt",
    headers := [("Host", "127.0.0.1:8090"), ("Authorization", "Basic YTpi"), ("Connection", "keep-alive"),
                ("Proxy-Authorization", "Basic eDp5")] }

/-- Every stanza made goes to the target, by its wire `to` attribute. -/
def wireTo (a : Addressed) : Option String :=
  (L4Factoidal.XMPP.Wire.parseElement a.render).bind (attr · "to")

-- A GET: one iq to the target; the headers less the hop-by-hop ones.
#guard
  let (id, s) := send tcfg {} 0 getReq
  id == "fxp1" && s.send.length == 1 && s.done.isEmpty && s.st.waiting.length == 1 &&
  s.send.all (wireTo · == some "bob@example.org/dav") &&
  match HttpOverXmpp.parseReqIq (s.send.head!.render) with
  | some (env, .ok q) =>
    env.id == "fxp1" && env.to == some "bob@example.org/dav" && q.method == "GET" &&
    q.headers == [("Host", "127.0.0.1:8090"), ("Authorization", "Basic YTpi")]
  | _ => false

-- The serving side answers 200 from the target: the response comes out.
#guard
  let (_, s) := send tcfg {} 0 getReq
  let env : Envelope := { from_ := some "alice@example.org/proxy", to := some "bob@example.org/dav", id := "fxp1" }
  let r := receive tcfg s.st (HttpOverXmpp.renderRespIq env
    { statusCode := 200, headers := [("content-type", "text/plain"), ("content-length", "5")], body := .text "hello" })
  r.st.waiting.isEmpty && r.send.isEmpty &&
  r.done.map (fun d => (d.id, d.response.status, d.response.headers, d.response.body.toList)) ==
    [("fxp1", 200, [("content-type", "text/plain")], "hello".toUTF8.toList)]

-- The same stanza from another JID is dropped: the request still waits.
#guard
  let (_, s) := send tcfg {} 0 getReq
  let env : Envelope := { from_ := some "alice@example.org/proxy", to := some "mallory@example.org/x", id := "fxp1" }
  let r := receive tcfg s.st (HttpOverXmpp.renderRespIq env { statusCode := 200, body := .text "forged" })
  r.done.isEmpty && r.st.waiting.length == 1

-- A stanza error from the target: forbidden is 403.
#guard
  let (_, s) := send tcfg {} 0 getReq
  let err := L4Factoidal.XMPP.Server.stanzaError .iq (some "fxp1") (some "alice@example.org/proxy")
    (some "bob@EXAMPLE.org/dav") "auth" "forbidden"
  let r := receive tcfg s.st err
  r.done.map (fun d => d.response.status) == [403] && r.st.waiting.isEmpty

-- A chunked response: the resp, then chunks out of order.
def bytes1000 : ByteArray := ByteArray.mk ((List.range 1000).map (fun i => UInt8.ofNat (i % 251))).toArray
#guard
  let (_, s) := send tcfg {} 0 getReq
  let env : Envelope := { from_ := some "alice@example.org/proxy", to := some "bob@example.org/dav", id := "fxp1" }
  let r1 := receive tcfg s.st (HttpOverXmpp.renderRespIq env { statusCode := 200, body := .chunked "fhx0" })
  let msgs := HttpOverXmpp.renderChunkMessages (some "bob@example.org/dav") (some "alice@example.org/proxy")
    (HttpOverXmpp.splitChunks "fhx0" bytes1000 256)
  let r := msgs.reverse.foldl (fun (acc : Step) m =>
    let x := receive tcfg acc.st m
    { x with done := acc.done ++ x.done }) r1
  r1.done.isEmpty && r.done.map (fun d => (d.response.status, d.response.body.toList)) == [(200, bytes1000.toList)]

-- A large request body goes in chunks to the target; they reassemble.
#guard
  let (_, s) := send tcfg {} 0 { method := "PUT", target := "/notes/b.bin", body := bytes1000 }
  s.send.length == 5 && s.send.all (wireTo · == some "bob@example.org/dav") &&
  let cs := (s.send.drop 1).filterMap (fun a => (HttpOverXmpp.parseChunk a.render).map (·.2))
  (HttpOverXmpp.assembleChunks cs).map (·.toList) == some bytes1000.toList

-- Refusals made here: CONNECT, absolute-form, too large, too many waiting.
#guard ((send tcfg {} 0 { method := "CONNECT", target := "/" }).2.done.map (·.response.status)) == [405]
#guard ((send tcfg {} 0 { method := "GET", target := "http://other.example/" }).2.done.map (·.response.status)) == [400]
#guard ((send { tcfg with maxBodyBytes := 10 } {} 0 { method := "PUT", target := "/x", body := bytes1000 }).2.done.map
          (·.response.status)) == [413]
#guard
  let st : State := { waiting := (List.range 16).map (fun i => { id := s!"w{i}", method := "GET", deadline := 99 }) }
  let (_, s) := send tcfg st 0 getReq
  s.done.map (·.response.status) == [503] && s.send.isEmpty

-- Timeout: past the deadline, 504; before it, nothing.
#guard
  let (_, s) := send tcfg {} 0 getReq
  (tick tcfg s.st 999).done.isEmpty &&
  (tick tcfg s.st 1000).done.map (fun d => (d.id, d.response.status)) == [("fxp1", 504)] &&
  (tick tcfg s.st 1000).st.waiting.isEmpty

-- The stream ends: every waiting request gets 502.
#guard
  let (_, s) := send tcfg {} 0 getReq
  (abortAll tcfg s.st "x").done.map (·.response.status) == [502]

end L4Factoidal.XMPP.HttpRequester
