/-
L4Factoidal.XMPP.HttpOverXmpp — HTTP over XMPP (XEP-0332), stage 1.
https://github.com/danbri/factoidal/issues/1107
Design record: `docs/designissues/2026-10-28-http-over-xmpp.md`.

XEP-0332 "HTTP over XMPP transport", version 0.5.1 (2020-03-31), status
Deferred (https://xmpp.org/extensions/xep-0332.html). A request is an
`<iq type='set'>` with a `<req xmlns='urn:xmpp:http'>` child; the answer is an
`<iq type='result'>` with a `<resp>` child. Headers are XEP-0131 stanza
headers (`http://jabber.org/protocol/shim`). The body is one child of
`<data>`: `text`, `xml`, `base64` or `chunkedBase64`. A `chunkedBase64` body
is sent in `<chunk streamId nr last>` messages; the receiver stops a stream
with `<close streamId>`.

This module holds every decision; a host only moves stanza text:

* the codec: `parseReqIq` / `renderReqIq`, `parseRespIq` / `renderRespIq`,
  `parseChunk` / `renderChunkMessages`, `parseClose` / `renderClose`,
  `assembleChunks`;
* the mapping to and from the request and response records that
  `webdav-serve` steps (`WebDAV.DavRequest`, `WebDAV.DavResponse`):
  `Req.toDav`, `respOfDav` (with `chooseEncoding`);
* the access decision: `allowed` (the sender's bare JID is in an allow list);
* `step`: one incoming stanza to the stanzas to send, as a WebDAV program
  (`WebDAV.Prog`), so the same storage loopbacks the WebDAV tests use run it.

Choices that the XEP does not make (marked "implementer" in the design
record):

1. Methods: the XEP's eight (OPTIONS GET HEAD POST PUT DELETE TRACE PATCH)
   plus the WebDAV methods PROPFIND PROPPATCH MKCOL COPY MOVE LOCK UNLOCK
   (RFC 4918), because the target is `webdav-serve`. CONNECT is refused with
   `not-allowed` (the XEP excludes it); any other method with
   `feature-not-implemented`.
2. Access: only a sender whose bare JID is in `Config.allow`. No roster
   logic yet (the XEP's public, manual, private and provisioned profiles are
   not implemented). A refused sender gets `forbidden` (type `auth`), and
   the request is not parsed further.
3. Body encoding of a response: empty body, no `<data>`; a body longer than
   `Config.inlineLimit` bytes, `chunkedBase64`; an XML media type whose body
   parses, `xml`; a text media type whose body is UTF-8 with only XML
   characters and no carriage return (an XML reader normalises CR), `text`;
   otherwise `base64`. `xml` keeps the element, not the bytes (the XML
   declaration is dropped).
4. `maxChunkSize` counts content bytes before base64 (the XEP does not say).
   The chunk size is `min maxChunkSize Config.chunkSize`.
5. Bodies sent as `sipub`, `ibb` or `jingle` are refused with
   `feature-not-implemented`.
6. Chunked request bodies wait in `State.pending` until the chunk marked
   `last` and every chunk before it have arrived; a request whose chunks
   pass `Config.maxBodyBytes`, or more than `Config.maxPending` waiting
   requests, is refused with `resource-constraint`.
7. JID comparison: domain part case-insensitive (RFC 7622 §3.2), local part
   exact. PRECIS (RFC 8265) is not applied
   (https://github.com/danbri/factoidal/issues/676).

No `partial`, no `sorry`. Every loop over input-proportional data is a tail
call or a core combinator with a tail-recursive `csimp` form.
-/
import L4Factoidal.XMPP.Server
import L4Factoidal.XML.Enc
import L4Factoidal.WebDAV.Server

namespace L4Factoidal.XMPP.HttpOverXmpp

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP.Server (elemName elemAttr elemChildren)
open L4Factoidal.WebDAV (DavRequest DavResponse DavState Ctx Prog)

def nsHttp : String := "urn:xmpp:http"
def nsShim : String := "http://jabber.org/protocol/shim"

/-! ## Methods -/

/-- The methods this implementation carries: the XEP's eight, then the
RFC 4918 methods (implementer choice 1). -/
def xepMethods : List String := ["OPTIONS", "GET", "HEAD", "POST", "PUT", "DELETE", "TRACE", "PATCH"]
def davMethods : List String := ["PROPFIND", "PROPPATCH", "MKCOL", "COPY", "MOVE", "LOCK", "UNLOCK"]
def methods : List String := xepMethods ++ davMethods

/-! ## Records -/

/-- The content of `<data>`. `xml` holds the rendered child element. -/
inductive Body where
  | empty
  | text (s : String)
  | xml (fragment : String)
  | base64 (b : ByteArray)
  | chunked (streamId : String)
deriving Inhabited

/-- A comparable form of a body (for tests and for `BEq`). -/
def Body.key : Body → String × List UInt8
  | .empty => ("empty", [])
  | .text s => ("text:" ++ s, [])
  | .xml f => ("xml:" ++ f, [])
  | .base64 b => ("base64", b.toList)
  | .chunked sid => ("chunked:" ++ sid, [])

instance : BEq Body := ⟨fun a b => a.key == b.key⟩

/-- The bytes of a body carried in the stanza itself; `none` for a chunked
body, whose bytes come in `chunk` messages. -/
def Body.bytes? : Body → Option ByteArray
  | .empty => some ByteArray.empty
  | .text s => some s.toUTF8
  | .xml f => some f.toUTF8
  | .base64 b => some b
  | .chunked _ => none

structure Req where
  method : String
  resource : String
  version : String := "1.1"
  maxChunkSize : Option Nat := none
  /-- Header names as sent. -/
  headers : List (String × String) := []
  body : Body := .empty
deriving Inhabited, BEq

structure Resp where
  version : String := "1.1"
  statusCode : Nat
  statusMessage : Option String := none
  headers : List (String × String) := []
  body : Body := .empty
deriving Inhabited, BEq

/-- An `iq` envelope around a `req` or a `resp`. -/
structure Envelope where
  from_ : Option String := none
  to : Option String := none
  id : String
deriving Inhabited, BEq

structure Chunk where
  streamId : String
  nr : Nat
  last : Bool := false
  data : ByteArray
deriving Inhabited

def Chunk.key (c : Chunk) : String × Nat × Bool × List UInt8 := (c.streamId, c.nr, c.last, c.data.toList)
instance : BEq Chunk := ⟨fun a b => a.key == b.key⟩

/-! ## Small XML helpers -/

def attr (n : Node) (name : String) : Option String := elemAttr n name

/-- The child elements of `n`, without text, comments or processing
instructions. -/
def kids (n : Node) : List Node :=
  (elemChildren n).filter (fun c => match c with | .element .. => true | _ => false)

/-- The first child element called `tag` (with `xmlns` = `ns` when given). -/
def kid? (n : Node) (tag : String) (ns : Option String := none) : Option Node :=
  (kids n).find? (fun c => elemName c == some tag && (ns.isNone || attr c "xmlns" == ns))

/-- The character data directly inside an element (text and CDATA). -/
def charData (n : Node) : String :=
  String.join ((elemChildren n).filterMap (fun c =>
    match c with | .text t => some t | .cdata t => some t | _ => none))

def digitsOnly (s : String) : Bool := !s.isEmpty && s.toList.all Char.isDigit

/-- XEP-0332 `Version`: `\d[.]\d`. -/
def versionOk (v : String) : Bool :=
  match v.toList with
  | [a, '.', b] => a.isDigit && b.isDigit
  | _ => false

def base64Of (b : ByteArray) : String := L4Factoidal.XML.Enc.base64 b
def base64Decode? (s : String) : Option ByteArray := L4Factoidal.XML.Enc.base64Decode? s

/-! ## Headers and data -/

def headersNode (hs : List (String × String)) : Node :=
  .element "headers" [⟨"xmlns", nsShim⟩] (hs.map (fun (n, v) => .element "header" [⟨"name", n⟩] [.text v]))

def parseHeaders (n : Node) : Option (List (String × String)) :=
  match kid? n "headers" (some nsShim) with
  | none => some []
  | some h =>
    let hs := (kids h).filter (fun c => elemName c == some "header")
    if hs.length != (kids h).length then none
    else hs.foldr (fun c acc => acc.bind fun l => (attr c "name").map (fun nm => (nm, charData c) :: l)) (some [])

def dataNode? : Body → Option Node
  | .empty => none
  | .text s => some (.element "data" [] [.element "text" [] [.text s]])
  | .xml f =>
    let inner := match L4Factoidal.XMPP.Wire.parseElement f with
      | some e => [e]
      | none => []
    some (.element "data" [] [.element "xml" [] inner])
  | .base64 b => some (.element "data" [] [.element "base64" [] [.text (base64Of b)]])
  | .chunked sid => some (.element "data" [] [.element "chunkedBase64" [⟨"streamId", sid⟩] []])

/-- Why a `<data>` element was not read. -/
inductive BodyError where
  | malformed
  | unsupported (encoding : String)
deriving Repr, BEq

def parseBody (n : Node) : Except BodyError Body :=
  match kid? n "data" with
  | none => .ok .empty
  | some d =>
    match kids d with
    | [e] =>
      match elemName e with
      | some "text" => .ok (.text (charData e))
      | some "xml" =>
        match kids e with
        | [] => .ok (.xml "")
        | [x] => .ok (.xml (L4Factoidal.XMPP.Wire.render x))
        | _ => .error .malformed
      | some "base64" =>
        match base64Decode? (charData e) with
        | some b => .ok (.base64 b)
        | none => .error .malformed
      | some "chunkedBase64" =>
        match attr e "streamId" with
        | some sid => if sid.isEmpty then .error .malformed else .ok (.chunked sid)
        | none => .error .malformed
      | some other => .error (.unsupported other)
      | none => .error .malformed
    | _ => .error .malformed

/-! ## `req` -/

def envAttrs (env : Envelope) (type_ : String) : List Attribute :=
  (env.from_.map (Attribute.mk "from")).toList ++ (env.to.map (Attribute.mk "to")).toList ++
  [⟨"type", type_⟩, ⟨"id", env.id⟩]

def reqNode (r : Req) : Node :=
  .element "req"
    ([⟨"xmlns", nsHttp⟩, ⟨"method", r.method⟩, ⟨"resource", r.resource⟩, ⟨"version", r.version⟩] ++
     (r.maxChunkSize.map (fun m => Attribute.mk "maxChunkSize" (toString m))).toList)
    ([headersNode r.headers] ++ (dataNode? r.body).toList)

/-- An `<iq type='set'>` carrying a request (the client side; used by the
local proxy of stage 2 and by the tests). -/
def renderReqIq (env : Envelope) (r : Req) : String :=
  L4Factoidal.XMPP.Wire.render (.element "iq" (envAttrs env "set") [reqNode r])

/-- Why a request was refused. Each maps to one stanza error
(`Refusal.condition`). -/
inductive Refusal where
  /-- The sender is not in the allow list. -/
  | forbidden
  /-- CONNECT, which XEP-0332 excludes. -/
  | connect
  | unknownMethod (m : String)
  | unsupportedEncoding (e : String)
  | badRequest (why : String)
  | resourceConstraint (why : String)
deriving Repr, BEq

/-- RFC 6120 §8.3.3: error type and defined condition. -/
def Refusal.condition : Refusal → String × String
  | .forbidden => ("auth", "forbidden")
  | .connect => ("cancel", "not-allowed")
  | .unknownMethod _ => ("cancel", "feature-not-implemented")
  | .unsupportedEncoding _ => ("cancel", "feature-not-implemented")
  | .badRequest _ => ("modify", "bad-request")
  | .resourceConstraint _ => ("wait", "resource-constraint")

/-- The `req` element of an `iq`, when the stanza is an `<iq type='set'>`
whose child is `req` in `urn:xmpp:http`. Any other stanza is not for this
module (`none`). -/
def reqElement? (n : Node) : Option (Envelope × Node) :=
  if elemName n != some "iq" || attr n "type" != some "set" then none
  else match kid? n "req" (some nsHttp) with
    | none => none
    | some r => some ({ from_ := attr n "from", to := attr n "to", id := (attr n "id").getD "" }, r)

/-- Read a `req` element (after the access decision). -/
def parseReq (r : Node) : Except Refusal Req :=
  match attr r "method", attr r "resource", attr r "version" with
  | some m, some res, some v =>
    if m == "CONNECT" then .error .connect
    else if !methods.contains m then .error (.unknownMethod m)
    else if !versionOk v then .error (.badRequest "version is not \\d.\\d")
    else
      let mcs : Except Refusal (Option Nat) := match attr r "maxChunkSize" with
        | none => .ok none
        | some s =>
          if digitsOnly s && 256 ≤ s.toNat! && s.toNat! ≤ 65536 then .ok (some s.toNat!)
          else .error (.badRequest "maxChunkSize is not an integer from 256 to 65536")
      match mcs with
      | .error e => .error e
      | .ok mcs =>
        match parseHeaders r with
        | none => .error (.badRequest "headers")
        | some hs =>
          match parseBody r with
          | .error .malformed => .error (.badRequest "data")
          | .error (.unsupported e) => .error (.unsupportedEncoding e)
          | .ok b => .ok { method := m, resource := res, version := v, maxChunkSize := mcs, headers := hs, body := b }
  | _, _, _ => .error (.badRequest "method, resource and version are required")

/-- Parse a request stanza text. `none`: not an HTTP-over-XMPP request. -/
def parseReqIq (s : String) : Option (Envelope × Except Refusal Req) :=
  (L4Factoidal.XMPP.Wire.parseElement s).bind reqElement? |>.map (fun (env, r) => (env, parseReq r))

/-! ## `resp` -/

def respNode (r : Resp) : Node :=
  .element "resp"
    ([⟨"xmlns", nsHttp⟩, ⟨"version", r.version⟩, ⟨"statusCode", toString r.statusCode⟩] ++
     (r.statusMessage.map (Attribute.mk "statusMessage")).toList)
    ([headersNode r.headers] ++ (dataNode? r.body).toList)

/-- The `<iq type='result'>` answering `env`: addresses swapped. -/
def renderRespIq (env : Envelope) (r : Resp) : String :=
  L4Factoidal.XMPP.Wire.render
    (.element "iq" (envAttrs { from_ := env.to, to := env.from_, id := env.id } "result") [respNode r])

/-- Parse a response stanza (the client side). The envelope is as written
in the stanza. -/
def parseRespIq (s : String) : Option (Envelope × Resp) := do
  let n ← L4Factoidal.XMPP.Wire.parseElement s
  if elemName n != some "iq" || attr n "type" != some "result" then none
  let r ← kid? n "resp" (some nsHttp)
  let v ← attr r "version"
  let sc ← attr r "statusCode"
  if !digitsOnly sc || !versionOk v then none
  let hs ← parseHeaders r
  let b ← (parseBody r).toOption
  some ({ from_ := attr n "from", to := attr n "to", id := (attr n "id").getD "" },
        { version := v, statusCode := sc.toNat!, statusMessage := attr r "statusMessage", headers := hs, body := b })

/-- The `<iq type='error'>` answering `env` (RFC 6120 §8.3). -/
def renderRefusal (env : Envelope) (why : Refusal) : String :=
  let (t, c) := why.condition
  L4Factoidal.XMPP.Server.stanzaError .iq (some env.id) env.from_ env.to t c

/-! ## Chunks -/

def chunkNode (c : Chunk) : Node :=
  .element "chunk"
    ([⟨"xmlns", nsHttp⟩, ⟨"streamId", c.streamId⟩, ⟨"nr", toString c.nr⟩] ++
     (if c.last then [⟨"last", "true"⟩] else []))
    [.text (base64Of c.data)]

def messageAttrs (from_ to : Option String) : List Attribute :=
  (from_.map (Attribute.mk "from")).toList ++ (to.map (Attribute.mk "to")).toList

/-- Split `b` into chunks of at most `size` bytes (at least one chunk, the
last marked). A tail call per chunk. -/
def splitChunks (streamId : String) (b : ByteArray) (size : Nat) : List Chunk :=
  let size := max size 1
  let rec go (fuel off nr : Nat) (acc : List Chunk) : List Chunk :=
    match fuel with
    | 0 => acc.reverse
    | f + 1 =>
      let stop := off + size
      if stop ≥ b.size then
        ({ streamId, nr, last := true, data := b.extract off b.size } :: acc).reverse
      else go f stop (nr + 1) ({ streamId, nr, data := b.extract off stop } :: acc)
  go (b.size / size + 1) 0 0 []

/-- The `chunk` messages of a stream, from the server's address to the
requester's. -/
def renderChunkMessages (from_ to : Option String) (cs : List Chunk) : List String :=
  cs.map (fun c => L4Factoidal.XMPP.Wire.render (.element "message" (messageAttrs from_ to) [chunkNode c]))

def boolAttr (v : Option String) : Option Bool :=
  match v with
  | none => some false
  | some "true" | some "1" => some true
  | some "false" | some "0" => some false
  | some _ => none

/-- Read a `chunk` element (the child of a `message`). -/
def chunkOf? (c : Node) : Option Chunk := do
  if elemName c != some "chunk" || attr c "xmlns" != some nsHttp then none
  let sid ← attr c "streamId"
  let nr ← attr c "nr"
  if !digitsOnly nr then none
  let last ← boolAttr (attr c "last")
  let data ← base64Decode? (charData c)
  some { streamId := sid, nr := nr.toNat!, last, data }

/-- Parse a `<message>` carrying a `chunk`: the sender and the chunk. -/
def parseChunk (s : String) : Option (Option String × Chunk) := do
  let n ← L4Factoidal.XMPP.Wire.parseElement s
  if elemName n != some "message" then none
  let c ← kid? n "chunk" (some nsHttp)
  let ch ← chunkOf? c
  some (attr n "from", ch)

/-- A `<message>` that stops a chunked stream (sent by the receiver). -/
def renderClose (from_ to : Option String) (streamId : String) : String :=
  L4Factoidal.XMPP.Wire.render
    (.element "message" (messageAttrs from_ to) [.element "close" [⟨"xmlns", nsHttp⟩, ⟨"streamId", streamId⟩] []])

def parseClose (s : String) : Option (Option String × String) := do
  let n ← L4Factoidal.XMPP.Wire.parseElement s
  if elemName n != some "message" then none
  let c ← kid? n "close" (some nsHttp)
  let sid ← attr c "streamId"
  some (attr n "from", sid)

/-- The bytes of a complete stream: chunks numbered 0 to n with no gap, the
one numbered n (and no other) marked `last`, in any arrival order (XEP-0332
§4.2.4 note 3). `none` while incomplete or when inconsistent. -/
def assembleChunks (cs : List Chunk) : Option ByteArray :=
  match cs.find? (·.last) with
  | none => none
  | some lastC =>
    let n := lastC.nr
    if cs.length != n + 1 || (cs.filter (·.last)).length != 1 then none
    else
      let slots : Array (Option ByteArray) := cs.foldl
        (fun a c => if c.nr < a.size then a.set! c.nr (some c.data) else a) (Array.replicate (n + 1) none)
      slots.foldl (fun acc s => match acc, s with
        | some out, some d => some (out ++ d)
        | _, _ => none) (some ByteArray.empty)

/-! ## The mapping to `webdav-serve` -/

/-- The request record `WebDAV.handle` steps. Header names in lower case, as
`DavRequest` requires. `none` for a chunked body (`toDavWith` after the
chunks are assembled). -/
def Req.toDavWith (r : Req) (body : ByteArray) : DavRequest :=
  { method := r.method, target := r.resource, headers := r.headers.map (fun (n, v) => (n.toLower, v)), body }

def Req.toDav (r : Req) : Option DavRequest := r.body.bytes?.map r.toDavWith

structure Config where
  /-- Bare JIDs that may send requests. -/
  allow : List String
  /-- A response body longer than this goes `chunkedBase64`. -/
  inlineLimit : Nat := 65536
  /-- Content bytes per chunk when the requester gives no `maxChunkSize`. -/
  chunkSize : Nat := 65536
  /-- The largest chunked request body accepted. -/
  maxBodyBytes : Nat := 16 * 1024 * 1024
  /-- Requests waiting for chunks at once. -/
  maxPending : Nat := 16
deriving Inhabited

def mediaType (ct : Option String) : String :=
  match ct with
  | none => ""
  | some v => ((v.splitOn ";").headD "").trimAscii.toString.toLower

def isXmlType (mt : String) : Bool :=
  mt == "application/xml" || mt == "text/xml" || mt.endsWith "+xml"

def isTextType (mt : String) : Bool :=
  mt.startsWith "text/" || mt == "application/json" || mt.endsWith "+json" ||
  mt == "application/n-triples" || mt == "application/n-quads" || mt == "application/trig" ||
  mt == "application/sparql-query" || mt == "application/sparql-update" || mt == "application/javascript"

/-- XML 1.0 §2.2 `Char`, without CR (implementer choice 3). -/
def xmlTextChar (c : Char) : Bool :=
  let x := c.toNat
  x == 0x9 || x == 0xA || (0x20 ≤ x && x ≤ 0xD7FF) || (0xE000 ≤ x && x ≤ 0xFFFD) || 0x10000 ≤ x

/-- The encoding of a response body (implementer choice 3). `streamId` is
used only when the body is chunked. -/
def chooseEncoding (cfg : Config) (contentType : Option String) (body : ByteArray) (streamId : String) : Body :=
  if body.size == 0 then .empty
  else if body.size > cfg.inlineLimit then .chunked streamId
  else
    let mt := mediaType contentType
    match String.fromUTF8? body with
    | some s =>
      if isXmlType mt then
        match L4Factoidal.XMPP.Wire.parseElement s with
        | some e => .xml (L4Factoidal.XMPP.Wire.render e)
        | none => if s.toList.all xmlTextChar then .text s else .base64 body
      else if isTextType mt && s.toList.all xmlTextChar then .text s
      else .base64 body
    | none => .base64 body

def chunkSizeFor (cfg : Config) (r : Req) : Nat :=
  match r.maxChunkSize with
  | some m => min m cfg.chunkSize
  | none => cfg.chunkSize

/-- A WebDAV response as a `resp`, plus the chunks to send after it. -/
def respOfDav (cfg : Config) (r : Req) (d : DavResponse) (streamId : String) : Resp × List Chunk :=
  let ct := (d.headers.find? (·.1 == "content-type")).map (·.2)
  let body := chooseEncoding cfg ct d.body streamId
  let chunks := match body with
    | .chunked sid => splitChunks sid d.body (chunkSizeFor cfg r)
    | _ => []
  ({ version := "1.1", statusCode := d.status, statusMessage := some (L4Factoidal.WebDAV.reason d.status),
     headers := d.headers, body }, chunks)

/-! ## The access decision -/

/-- Bare JID, domain part in lower case (implementer choice 7). -/
def bareKey (s : String) : Option String :=
  (Jid.parse s).map (fun j => Jid.render { j with domainpart := j.domainpart.toLower, resourcepart := none })

/-- May `from_` send requests? Only when its bare JID is in `allow`. No
roster logic yet. -/
def allowed (allow : List String) (from_ : Option String) : Bool :=
  match from_.bind bareKey with
  | none => false
  | some k => allow.any (fun a => bareKey a == some k)

/-! ## One stanza in, stanzas out -/

/-- A request waiting for its chunked body. -/
structure Pending where
  env : Envelope
  req : Req
  streamId : String
  chunks : List Chunk := []
  bytes : Nat := 0
deriving Inhabited

structure State where
  pending : List Pending := []
  /-- Serial for the stream ids of chunked responses. -/
  serial : Nat := 0
deriving Inhabited

structure StepOut where
  /-- Stanzas to send, in order. -/
  out : List String
  dav : DavState
  st : State
  /-- `false`: the stanza is not HTTP over XMPP; the host passes it on. -/
  handled : Bool := true

/-- What one incoming stanza asks for, decided before any storage
operation. `step` is `plan`, then `WebDAV.handle` for `serve`, then
`finish`. A host that runs the WebDAV request through its own handle (the
client stream of `factoidal webdav-serve --xmpp`, `Wasm/Ops/XmppClient.lean`)
calls `plan` and `finish` and carries the request between them; the
decisions are the same functions. -/
inductive Plan where
  /-- Stanzas to send now (a refusal; none while a chunked body waits),
  and the new state. -/
  | answer (out : List String) (st : State)
  /-- A complete request to serve against `webdav-serve`. -/
  | serve (st : State) (env : Envelope) (r : Req) (body : ByteArray)
  /-- Not HTTP over XMPP: the host passes the stanza on. -/
  | skip

/-- One incoming stanza, up to the WebDAV request. A request from a sender
not in `cfg.allow` is refused with `forbidden` before its `req` is read
further. -/
def plan (cfg : Config) (st : State) (stanza : String) : Plan :=
  match L4Factoidal.XMPP.Wire.parseElement stanza with
  | none => .skip
  | some n =>
  match reqElement? n with
  | some (env, rn) =>
    if !allowed cfg.allow env.from_ then .answer [renderRefusal env .forbidden] st
    else
    match parseReq rn with
    | .error why => .answer [renderRefusal env why] st
    | .ok r =>
      match r.body with
      | .chunked sid =>
        if st.pending.length ≥ cfg.maxPending then
          .answer [renderRefusal env (.resourceConstraint "too many requests wait for chunks")] st
        else .answer [] { st with pending := st.pending ++ [{ env, req := r, streamId := sid }] }
      | b => .serve st env r (b.bytes?.getD ByteArray.empty)
  | none =>
  if elemName n != some "message" then .skip
  else
  let sender := attr n "from"
  let same (p : Pending) (sid : String) : Bool := p.streamId == sid && p.env.from_ == sender
  match (kid? n "chunk" (some nsHttp)).bind chunkOf?, (kid? n "close" (some nsHttp)).bind (attr · "streamId") with
  | some c, _ =>
    match st.pending.find? (same · c.streamId) with
    | none => .answer [] st
    | some p =>
      let rest := st.pending.filter (fun q => !same q c.streamId)
      let p := { p with chunks := c :: p.chunks.filter (·.nr != c.nr), bytes := p.bytes + c.data.size }
      if p.bytes > cfg.maxBodyBytes then
        .answer [renderRefusal p.env (.resourceConstraint "the chunked body is too large")] { st with pending := rest }
      else
      match assembleChunks p.chunks with
      | none => .answer [] { st with pending := rest ++ [p] }
      | some body => .serve { st with pending := rest } p.env p.req body
  | none, some sid => .answer [] { st with pending := st.pending.filter (fun q => !same q sid) }
  | none, none => .skip

/-- The WebDAV response to a planned request, as the stanzas to send: the
`resp` iq, then any `chunk` messages. A HEAD response has no body. -/
def finish (cfg : Config) (st : State) (env : Envelope) (r : Req) (d : DavResponse) : List String × State :=
  let d := if r.method == "HEAD" then { d with body := ByteArray.empty } else d
  let sid := "fhx" ++ toString st.serial
  let (resp, chunks) := respOfDav cfg r d sid
  let st' := if chunks.isEmpty then st else { st with serial := st.serial + 1 }
  (renderRespIq env resp :: renderChunkMessages env.to env.from_ chunks, st')

/-- Serve one complete request against `webdav-serve`. -/
def serve (cfg : Config) (cx : Ctx) (dav : DavState) (st : State) (env : Envelope) (r : Req) (body : ByteArray) :
    Prog StepOut := do
  let (d, dav') ← L4Factoidal.WebDAV.handle cx dav (r.toDavWith body)
  let (out, st') := finish cfg st env r d
  return { out, dav := dav', st := st' }

/-- One incoming stanza: `plan`, then `WebDAV.handle` and `finish`. -/
def step (cfg : Config) (cx : Ctx) (dav : DavState) (st : State) (stanza : String) : Prog StepOut :=
  match plan cfg st stanza with
  | .answer out st' => pure { out, dav, st := st' }
  | .serve st' env r body => serve cfg cx dav st' env r body
  | .skip => pure { out := [], dav, st, handled := false }

/-! ## `#guard`s: the codec -/

def env1 : Envelope := { from_ := some "alice@example.org/laptop", to := some "dav@example.net/box", id := "r1" }

def roundReq (r : Req) : Bool :=
  match parseReqIq (renderReqIq env1 r) with
  | some (e, .ok r') => e == env1 && r' == r
  | _ => false

def roundResp (r : Resp) : Bool :=
  let swapped : Envelope := { from_ := env1.to, to := env1.from_, id := env1.id }
  match parseRespIq (renderRespIq env1 r) with
  | some (e, r') => e == swapped && r' == r
  | _ => false

def binBytes : ByteArray := ByteArray.mk #[0, 1, 2, 255, 13, 10, 60, 38]

#guard roundReq { method := "GET", resource := "/m/a.txt", headers := [("Host", "localhost")] }
#guard roundReq { method := "PUT", resource := "/m/a.txt", headers := [("Content-Type", "text/plain")],
                  body := .text "a < b & c > d" }
#guard roundReq { method := "PROPFIND", resource := "/m/", headers := [("Depth", "1")],
                  body := .xml "<D:propfind xmlns:D=\"DAV:\"><D:allprop/></D:propfind>" }
#guard roundReq { method := "PUT", resource := "/m/b.bin", body := .base64 binBytes }
#guard roundReq { method := "POST", resource := "/sparql", maxChunkSize := some 4096, body := .chunked "s1" }
#guard roundResp { statusCode := 200, statusMessage := some "OK", headers := [("content-type", "text/plain")],
                   body := .text "hello" }
#guard roundResp { statusCode := 207, statusMessage := some "Multi-Status",
                   body := .xml "<D:multistatus xmlns:D=\"DAV:\"/>" }
#guard roundResp { statusCode := 200, body := .base64 binBytes }
#guard roundResp { statusCode := 200, body := .chunked "fhx0" }
#guard roundResp { statusCode := 204 }

-- The XEP's own example 1 (OPTIONS) reads.
#guard match parseReqIq ("<iq type='set' from='httpclient@example.org/browser' to='httpserver@example.org' id='1'>" ++
    "<req xmlns='urn:xmpp:http' method='OPTIONS' resource='*' version='1.1'>" ++
    "<headers xmlns='http://jabber.org/protocol/shim'><header name='Host'>example.org</header></headers>" ++
    "</req></iq>") with
  | some (e, .ok r) => e.id == "1" && r.method == "OPTIONS" && r.resource == "*" && r.headers == [("Host", "example.org")]
  | _ => false

-- CONNECT and an unknown method are refused; other stanzas are not ours.
def reqText (m : String) : String :=
  s!"<iq type='set' from='a@b' id='x'><req xmlns='urn:xmpp:http' method='{m}' resource='/' version='1.1'/></iq>"
#guard match parseReqIq (reqText "CONNECT") with | some (_, .error .connect) => true | _ => false
#guard match parseReqIq (reqText "BREW") with | some (_, .error (.unknownMethod "BREW")) => true | _ => false
#guard match parseReqIq (reqText "MKCOL") with | some (_, .ok r) => r.method == "MKCOL" | _ => false
#guard (parseReqIq "<iq type='get' id='x'><req xmlns='urn:xmpp:http' method='GET' resource='/' version='1.1'/></iq>").isNone
#guard (parseReqIq "<iq type='set' id='x'><req xmlns='urn:other' method='GET' resource='/' version='1.1'/></iq>").isNone
#guard match parseReqIq "<iq type='set' id='x'><req xmlns='urn:xmpp:http' method='GET' resource='/' version='11'/></iq>" with
  | some (_, .error (.badRequest _)) => true | _ => false
#guard match parseReqIq ("<iq type='set' id='x'><req xmlns='urn:xmpp:http' method='GET' resource='/' version='1.1' " ++
    "maxChunkSize='100'/></iq>") with
  | some (_, .error (.badRequest _)) => true | _ => false
#guard match parseReqIq ("<iq type='set' id='x'><req xmlns='urn:xmpp:http' method='GET' resource='/' version='1.1'>" ++
    "<data><ibb sid='s'/></data></req></iq>") with
  | some (_, .error (.unsupportedEncoding "ibb")) => true | _ => false

-- Chunks: split, render, parse, and reassemble in any order.
def bigBytes : ByteArray := ByteArray.mk ((List.range 1000).map (fun i => UInt8.ofNat (i % 251))).toArray
#guard (splitChunks "s" bigBytes 256).length == 4
#guard (splitChunks "s" bigBytes 256).map (·.last) == [false, false, false, true]
#guard (splitChunks "s" ByteArray.empty 256).length == 1
#guard (assembleChunks (splitChunks "s" bigBytes 256)).map (·.toList) == some bigBytes.toList
#guard (assembleChunks (splitChunks "s" bigBytes 256).reverse).map (·.toList) == some bigBytes.toList
#guard (assembleChunks ((splitChunks "s" bigBytes 256).drop 1)).isNone
#guard
  let cs := splitChunks "s" bigBytes 300
  let back := (renderChunkMessages (some "dav@example.net") (some "alice@example.org/l") cs).filterMap parseChunk
  back.map (·.2) == cs && back.all (·.1 == some "dav@example.net")
#guard parseClose (renderClose (some "a@b/c") (some "d@e") "s9") == some (some "a@b/c", "s9")

-- Encoding choice.
def cfg0 : Config := { allow := ["alice@example.org"], inlineLimit := 512 }
#guard chooseEncoding cfg0 (some "text/plain; charset=utf-8") "hi".toUTF8 "s" == .text "hi"
#guard chooseEncoding cfg0 (some "text/plain") "a\r\nb".toUTF8 "s" == .base64 "a\r\nb".toUTF8
#guard chooseEncoding cfg0 (some "application/xml") "<?xml version=\"1.0\"?><a b=\"1\"/>".toUTF8 "s" == .xml "<a b=\"1\"/>"
#guard chooseEncoding cfg0 (some "image/png") binBytes "s" == .base64 binBytes
#guard chooseEncoding cfg0 (some "text/plain") bigBytes "s7" == .chunked "s7"
#guard chooseEncoding cfg0 none ByteArray.empty "s" == .empty
#guard (respOfDav cfg0 { method := "GET", resource := "/", maxChunkSize := some 256 }
          { status := 200, body := bigBytes } "s").2.length == 4

-- Access: the bare JID decides; the domain part ignores case.
#guard allowed ["alice@example.org"] (some "alice@EXAMPLE.org/phone")
#guard !allowed ["alice@example.org"] (some "mallory@example.org/x")
#guard !allowed ["alice@example.org"] none
#guard !allowed [] (some "alice@example.org")

end L4Factoidal.XMPP.HttpOverXmpp
