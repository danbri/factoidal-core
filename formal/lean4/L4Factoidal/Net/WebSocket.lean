/-
L4Factoidal.Net.WebSocket — the decisions of the WebSocket API (WHATWG WebSockets Standard,
https://websockets.spec.whatwg.org/) and of the protocol's client side (RFC 6455): the URL
and the subprotocols a page may ask for, `close()`'s arguments, the opening handshake, and
the frames.

The host moves bytes on one TCP (or TLS) connection a socket; what is sent, what an answer
means and when the connection fails is decided here.

## Decisions

* The URL (§3.1 steps 1 to 5): parsed against the page's base URL; `http` becomes `ws` and
  `https` becomes `wss`; any other scheme, or a fragment, is a `SyntaxError`.
* A page loaded over `https` never opens a `ws:` connection (Mixed Content §5.1):
  `SecurityError`, as browsers throw it.
* A blocked port (Fetch §2.10 "bad port") is a failed connection: nothing is sent.
* Subprotocols (§3.1 step 7): each is a token (RFC 9110 §5.6.2), and none occurs twice
  (compared as strings).
* `close(code, reason)` (§3.2): a code is 1000 or 3000 to 4999 (`InvalidAccessError`); the
  reason is at most 123 bytes of UTF-8 (`SyntaxError`).
* The opening handshake (RFC 6455 §4.1): `Sec-WebSocket-Key` is 16 bytes of the engine's
  entropy in base64; the answer must be `101`, `Upgrade: websocket`, `Connection: upgrade`,
  `Sec-WebSocket-Accept` = base64(SHA-1(key ++ GUID)), no extension (none is asked for), and
  a subprotocol only when it is one the page asked for. Anything else fails the connection.
* Frames (RFC 6455 §5): every frame the client sends is masked with 4 fresh bytes; a frame
  from the server must not be masked, must have no RSV bit and a known opcode; control
  frames are at most 125 bytes and never fragmented; a text message must be UTF-8. A frame
  that breaks a rule fails the connection (close code 1002, or 1007 for bad UTF-8).
* A message larger than `maxMessage` fails the connection (1009).

## What is proved

`mask_mask`: masking twice with the same key gives the payload back (the server's unmasking
of the client's frame). `openCheck_ok`: an accepted URL is `ws` or `wss` without a fragment,
an `https` page only opens `wss`, and the subprotocols are valid. `closeCheck_code`: an
accepted code is 1000 or in 3000 to 4999. `parse_masked`: a masked frame from the server is
never read as a frame. `parse_frame`: a frame read is never larger than `maxMessage`, and a
control frame read is whole (FIN) and at most 125 bytes.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.WHATWG.Base64
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Net.PageFetch

namespace L4Factoidal.Net.WebSocket
open L4Factoidal.WHATWG

/-! ## The URL and the subprotocols (§3.1) -/

/-- Fetch §2.10: the ports a request never goes to. -/
def badPorts : List Nat :=
  [0, 1, 7, 9, 11, 13, 15, 17, 19, 20, 21, 22, 23, 25, 37, 42, 43, 53, 69, 77, 79, 87, 95, 101, 102, 103,
   104, 109, 110, 111, 113, 115, 117, 119, 123, 135, 137, 139, 143, 161, 179, 389, 427, 465, 512, 513, 514,
   515, 526, 530, 531, 532, 540, 548, 554, 556, 563, 587, 601, 636, 989, 990, 993, 995, 1719, 1720, 1723,
   2049, 3659, 4045, 4190, 5060, 5061, 6000, 6566, 6665, 6666, 6667, 6668, 6669, 6679, 6697, 10080]

/-- The port a `ws`/`wss` URL connects to. -/
def portOf (u : URL.Url) : Nat := u.port.getD (if u.scheme == "wss" then 443 else 80)

/-- A token character (RFC 9110 §5.6.2). -/
def tchar (c : Char) : Bool := c.isAlphanum || "!#$%&'*+-.^_`|~".contains c

/-- A subprotocol list the page may ask for. -/
def validProtocols (ps : List String) : Bool :=
  ps.all (fun p => !p.isEmpty && p.all tchar) && ps.eraseDups.length == ps.length

/-- `new WebSocket(url, protocols)` (§3.1 steps 1 to 7) on a page whose URL is secure or not:
the URL to connect to, or the exception (name, message). -/
def openCheck (base input : String) (protocols : List String) (secure : Bool) :
    Except (String × String) URL.Url :=
  match URL.parseUrl input (some base) with
  | none => .error ("SyntaxError", s!"The URL '{input}' is invalid.")
  | some u0 =>
    let u := if u0.scheme == "http" then { u0 with scheme := "ws" }
      else if u0.scheme == "https" then { u0 with scheme := "wss" } else u0
    if u.scheme != "ws" && u.scheme != "wss" then
      .error ("SyntaxError", s!"The URL's scheme must be either 'http', 'https', 'ws', or 'wss'. '{u0.scheme}' is not allowed.")
    else if u.fragment.isSome then
      .error ("SyntaxError", s!"The URL contains a fragment identifier ('{u.fragment.getD ""}'). Fragment identifiers are not allowed in WebSocket URLs.")
    else if secure && u.scheme == "ws" then
      .error ("SecurityError", "An insecure WebSocket connection may not be initiated from a page loaded over HTTPS.")
    else if !validProtocols protocols then
      .error ("SyntaxError", "The subprotocol list is invalid: each must be a token, and none may be given twice.")
    else .ok u

/-- `close(code, reason)` (§3.2 steps 1 and 2): `none` when the arguments may be used. -/
def closeCheck (code : Option Nat) (reason : String) : Option (String × String) :=
  match code with
  | some c =>
    if !(c == 1000 || (3000 ≤ c && c ≤ 4999)) then
      some ("InvalidAccessError", s!"The close code must be either 1000, or between 3000 and 4999. {c} is neither.")
    else if reason.utf8ByteSize > 123 then some ("SyntaxError", "The close reason must not be greater than 123 UTF-8 bytes.")
    else none
  | none =>
    if reason.utf8ByteSize > 123 then some ("SyntaxError", "The close reason must not be greater than 123 UTF-8 bytes.") else none

/-! ## The opening handshake (RFC 6455 §4.1, §4.2.2) -/

/-- The GUID of RFC 6455 §1.3. -/
def guid : String := "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- The `Sec-WebSocket-Key` of 16 bytes of entropy. -/
def keyOf (entropy : ByteArray) : String := Base64.encode (entropy.extract 0 16)

/-- The expected `Sec-WebSocket-Accept` for `key`, with the engine's SHA-1. -/
def acceptOf (sha1 : ByteArray → ByteArray) (key : String) : String := Base64.encode (sha1 (key ++ guid).toUTF8)

/-- ASCII lower case. -/
def lower (s : String) : String := s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Trim spaces and tabs. -/
def trim (s : String) : String :=
  String.ofList (((s.toList.dropWhile (fun c => c == ' ' || c == '\t')).reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

/-- A field of a header list, by name (ASCII case-insensitive), its values joined by ", ". -/
def field (hs : List (String × String)) (name : String) : Option String :=
  match hs.filter (fun (n, _) => lower n == lower name) with
  | [] => none
  | xs => some (", ".intercalate (xs.map (·.2)))

/-- The request of the opening handshake: the fields after the request line, which the host
writes as `GET <path> HTTP/1.1` to the URL's host. `origin`: the page's origin. -/
def handshakeFields (u : URL.Url) (key origin : String) (protocols : List String) : List (String × String) :=
  [("Host", u.hostname ++ (match u.port with | some p => ":" ++ toString p | none => "")),
   ("Upgrade", "websocket"), ("Connection", "Upgrade"), ("Sec-WebSocket-Key", key),
   ("Sec-WebSocket-Version", "13"), ("Origin", origin)] ++
  (if protocols.isEmpty then [] else [("Sec-WebSocket-Protocol", ", ".intercalate protocols)])

/-- The answer to the opening handshake (RFC 6455 §4.1, the client's checks): the subprotocol
the server chose ("" for none), or why the connection fails. -/
def handshakeCheck (sha1 : ByteArray → ByteArray) (key : String) (protocols : List String)
    (status : Nat) (hs : List (String × String)) : Except String String :=
  if status != 101 then .error s!"Unexpected response code: {status}" else
  if (field hs "upgrade").map (lower ∘ trim) != some "websocket" then .error "Error during WebSocket handshake: 'Upgrade' header is missing" else
  if !(((field hs "connection").getD "").splitOn ",").any (fun t => lower (trim t) == "upgrade") then
    .error "Error during WebSocket handshake: 'Connection' header is missing" else
  if (field hs "sec-websocket-accept").map trim != some (acceptOf sha1 key) then
    .error "Error during WebSocket handshake: Incorrect 'Sec-WebSocket-Accept' header value" else
  if (field hs "sec-websocket-extensions").isSome then
    .error "Error during WebSocket handshake: an extension the client did not ask for" else
  match field hs "sec-websocket-protocol" with
  | none => .ok ""
  | some p =>
    let p := trim p
    if protocols.contains p then .ok p
    else .error "Error during WebSocket handshake: the server chose a subprotocol the client did not ask for"

/-! ## Frames (RFC 6455 §5.2) -/

/-- XOR each byte with the key's byte at its position mod 4 (§5.3). -/
def mask (key : List UInt8) (p : List UInt8) : List UInt8 :=
  p.zipIdx.map fun (b, i) => b ^^^ key.getD (i % 4) 0

/-- The length field: 7 bits, or 126 and 16 bits, or 127 and 64 bits, big-endian. -/
def lengthBytes (n : Nat) : List UInt8 :=
  if n < 126 then [n.toUInt8]
  else if n < 65536 then [126, (n / 256).toUInt8, (n % 256).toUInt8]
  else [127] ++ (List.range 8).reverse.map fun i => ((n / 256 ^ i) % 256).toUInt8

/-- A frame the client sends: FIN set, the opcode, masked with `key` (4 bytes). -/
def encodeClient (key : List UInt8) (opcode : Nat) (payload : List UInt8) : List UInt8 :=
  match lengthBytes payload.length with
  | [] => []
  | l :: ls => [(0x80 ||| opcode).toUInt8, l ||| 0x80] ++ ls ++ key ++ mask key payload

/-- A frame as the server writes it (no mask): for the checks below. -/
def encodeServer (fin : Bool) (opcode : Nat) (payload : List UInt8) : List UInt8 :=
  [((if fin then 0x80 else 0) ||| opcode).toUInt8] ++ lengthBytes payload.length ++ payload

/-- One frame read from the server. -/
structure Frame where
  fin : Bool
  opcode : Nat
  payload : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Reading the bytes at the front of the buffer. -/
inductive Read where
  /-- Not a whole frame yet. -/
  | more
  /-- A frame and the bytes after it. -/
  | frame (f : Frame) (rest : List UInt8)
  /-- The bytes break the protocol: the close code and why. -/
  | bad (code : Nat) (why : String)
  deriving Inhabited

/-- Big-endian number of a byte list. -/
def beNat (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 0

/-- The largest message (and frame) the engine takes. -/
def maxMessage : Nat := 1 <<< 26

/-- A known opcode: continuation, text, binary, close, ping, pong. -/
def knownOpcode (op : Nat) : Bool := op == 0 || op == 1 || op == 2 || op == 8 || op == 9 || op == 10

/-- The first two bytes of a frame (§5.2). -/
structure Head where
  fin : Bool
  rsv : Bool
  op : Nat
  masked : Bool
  len7 : Nat
  deriving Inhabited

def headOf (b0 b1 : UInt8) : Head :=
  { fin := b0 &&& 0x80 != 0, rsv := b0 &&& 0x70 != 0, op := (b0 &&& 0x0F).toNat,
    masked := b1 &&& 0x80 != 0, len7 := (b1 &&& 0x7F).toNat }

/-- Why a frame's first two bytes break the protocol (the close code and the reason). -/
def check (h : Head) : Option (Nat × String) :=
  if h.rsv then some (1002, "a reserved bit is set")
  else if !knownOpcode h.op then some (1002, s!"unknown opcode {h.op}")
  else if h.masked then some (1002, "a frame from the server is masked")
  else if h.op ≥ 8 && (!h.fin || h.len7 > 125) then some (1002, "a control frame is fragmented or too long")
  else none

/-- The payload length and the bytes after the length field (`none`: not all there yet). -/
def lenOf (len7 : Nat) (rest : List UInt8) : Option (Nat × List UInt8) :=
  if len7 < 126 then some (len7, rest)
  else if len7 == 126 then (if rest.length < 2 then none else some (beNat (rest.take 2), rest.drop 2))
  else (if rest.length < 8 then none else some (beNat (rest.take 8), rest.drop 8))

/-- Read the rest of a frame whose first two bytes are `h`. -/
def parseWith (h : Head) (rest : List UInt8) : Read :=
  match check h with
  | some (c, why) => .bad c why
  | none =>
    match lenOf h.len7 rest with
    | none => .more
    | some (n, after) =>
      if n > maxMessage then .bad 1009 "a frame is too large"
      else if after.length < n then .more
      else .frame { fin := h.fin, opcode := h.op, payload := after.take n } (after.drop n)

/-- Read one frame from the server at the front of `buf` (§5.2; §5.5 for control frames). -/
def parse : List UInt8 → Read
  | b0 :: b1 :: rest => parseWith (headOf b0 b1) rest
  | _ => .more

/-! ## A connection (WebSockets §4, RFC 6455 §4 to §7) -/

/-- What the page hears of a connection, in order. -/
inductive Ev where
  | opened (protocol : String)
  | text (s : String)
  | binary (b : ByteArray)
  | error
  | closed (code : Nat) (reason : String) (clean : Bool)
  deriving Inhabited

/-- One connection of the page. The host is told to connect (`Wire` method `WEBSOCKET`, with
the handshake's fields), to write (`WEBSOCKET-SEND`, the frame's bytes) and to close
(`WEBSOCKET-CLOSE`); its answers are the handshake's response (status, fields, the bytes after
it) and then each piece of bytes read (status 1), or the end of the connection (status 0). -/
structure Sock where
  id : Nat
  /-- The URL as the page gave it, resolved (`ws`/`wss`). -/
  url : String
  /-- The request for the address rule (resolve, pin): the URL in its `http`/`https` form. -/
  t : PageFetch.Transfer
  key : String
  protocols : List String
  origin : String
  /-- CONNECTING 0, OPEN 1, CLOSING 2, CLOSED 3. -/
  readyState : Nat := 0
  protocol : String := ""
  handshaken : Bool := false
  buf : List UInt8 := []
  frag : Option (Nat × List UInt8) := none
  buffered : Nat := 0
  closeSent : Bool := false
  closeRecv : Option (Nat × String) := none
  /-- Masking keys for frames the engine sends on its own (pong, the reply to a close): fresh
  entropy given at the start and with each `send`. -/
  pool : List UInt8 := []
  events : Array Ev := #[]
  cb : Nat := 0
  /-- The bytes of the last binary message the page took (`web_api` 161). -/
  lastBinary : ByteArray := ByteArray.empty
  deriving Inhabited

/-- The `http`/`https` form of a `ws`/`wss` URL (WebSockets §4.1 step 1). -/
def httpForm (u : URL.Url) : URL.Url := { u with scheme := if u.scheme == "wss" then "https" else "http" }

/-- A wire to the host for this connection. -/
def sockWire (s : Sock) (method : String) (body : Option ByteArray := none) : PageFetch.Wire :=
  { id := s.id, method, url := s.url, headers := [], body }

/-- The connection fails (RFC 6455 §7.1.7): the host closes it; the page hears `error` and
`close` (1006, not clean), once. -/
def fail (s : Sock) : Sock × List PageFetch.Wire :=
  if s.readyState == 3 then (s, []) else
  ({ s with readyState := 3, events := s.events.push .error |>.push (.closed 1006 "" false) }, [sockWire s "WEBSOCKET-CLOSE"])

/-- The wire that opens the connection from a planned request (resolve-only first, then the
connection with the handshake to the chosen address). -/
def connectWire (s : Sock) (w : PageFetch.Wire) : PageFetch.Wire :=
  if w.resolve then w
  else match URL.parseUrl s.url with
    | some u =>
      { id := s.id, method := "WEBSOCKET", url := s.url, headers := handshakeFields u s.key s.origin s.protocols, body := none, address := w.address, port := w.port }
    | none => w

/-- Plan the connection (the scheme, local-address, mixed-content and DNS rules of the page's
requests, `PageFetch.plan`), or fail it. -/
def planStep (s : Sock) (st : PageFetch.Step) : Sock × List PageFetch.Wire :=
  match st with
  | .send t w => ({ s with t }, [connectWire s w])
  | _ => fail s

/-- Start a connection: `u` passed `openCheck`; `entropy`: at least 16 bytes for the key and
more for masking keys. A blocked port fails at once. -/
def connect (page : PageFetch.Page) (id cb : Nat) (u : URL.Url) (protocols : List String) (entropy : ByteArray) :
    Sock × List PageFetch.Wire :=
  let t : PageFetch.Transfer :=
    { id, page, method := "GET", url := (httpForm u).serialize, headers := [], body := none, credentials := true, destination := "websocket" }
  let s : Sock :=
    { id, url := u.serialize, t, key := keyOf entropy, protocols, origin := page.origin, cb, pool := (entropy.extract 16 entropy.size).toList }
  if badPorts.contains (portOf u) then fail s else planStep s (PageFetch.plan t)

/-- Four bytes of the pool for a frame the engine sends on its own. -/
def takeKey (s : Sock) : Sock × List UInt8 :=
  match s.pool with
  | a :: b :: c :: d :: rest => ({ s with pool := rest }, [a, b, c, d])
  | _ => (s, [0x5a, 0xa5, 0x3c, 0xc3])

/-- The payload of a close frame: the code (two bytes) and the reason. -/
def closePayload (code : Option Nat) (reason : String) : List UInt8 :=
  match code with
  | some c => [(c / 256).toUInt8, (c % 256).toUInt8] ++ reason.toUTF8.toList
  | none => []

/-- A whole message from the server (§6.2): the page hears it while the connection is open. -/
def deliver (s : Sock) (op : Nat) (data : List UInt8) : Sock × List PageFetch.Wire :=
  if s.readyState != 1 then (s, []) else
  if op == 1 then
    match String.fromUTF8? (ByteArray.mk data.toArray) with
    | some text => ({ s with events := s.events.push (.text text) }, [])
    | none => fail s
  else ({ s with events := s.events.push (.binary (ByteArray.mk data.toArray)) }, [])

/-- One frame from the server. -/
def onFrame (s : Sock) (f : Frame) : Sock × List PageFetch.Wire :=
  match f.opcode with
  | 0 =>
    match s.frag with
    | none => fail s
    | some (op, acc) =>
      let acc := acc ++ f.payload
      if acc.length > maxMessage then fail s
      else if f.fin then deliver { s with frag := none } op acc
      else ({ s with frag := some (op, acc) }, [])
  | 1 | 2 =>
    if s.frag.isSome then fail s
    else if f.fin then deliver s f.opcode f.payload
    else ({ s with frag := some (f.opcode, f.payload) }, [])
  | 8 =>
    let code := match f.payload with
      | a :: b :: _ => some (a.toNat * 256 + b.toNat)
      | _ => none
    let reason := (String.fromUTF8? (ByteArray.mk (f.payload.drop 2).toArray)).getD ""
    let s := { s with closeRecv := some (code.getD 1005, reason), readyState := 2 }
    if s.closeSent then (s, []) else
    -- the reply echoes the code (RFC 6455 §5.5.1); the server then ends the connection
    let (s, k) := takeKey s
    ({ s with closeSent := true }, [sockWire s "WEBSOCKET-SEND" (some (ByteArray.mk (encodeClient k 8 (closePayload code "")).toArray))])
  | 9 =>
    let (s, k) := takeKey s
    (s, [sockWire s "WEBSOCKET-SEND" (some (ByteArray.mk (encodeClient k 10 f.payload).toArray))])
  | _ => (s, [])

/-- Read every whole frame of the buffer (at most `fuel`), the wires in order (a loop: a piece of
64 KiB can hold thousands of frames). -/
def drainGo (s : Sock) (acc : Array PageFetch.Wire) : Nat → Sock × Array PageFetch.Wire
  | 0 => (s, acc)
  | fuel + 1 =>
    if s.readyState == 3 then (s, acc) else
    match parse s.buf with
    | .more => (s, acc)
    | .bad _ _ => let (s, ws) := fail s; (s, acc ++ ws.toArray)
    | .frame f rest =>
      let (s, ws) := onFrame { s with buf := rest } f
      drainGo s (acc ++ ws.toArray) fuel

def drain (s : Sock) (fuel : Nat) : Sock × List PageFetch.Wire :=
  let (s, a) := drainGo s #[] fuel
  (s, a.toList)

/-- The host's answer for this connection. `sha1`: the engine's SHA-1. -/
def onAnswer (sha1 : ByteArray → ByteArray) (s : Sock) (a : PageFetch.Answer) : Sock × List PageFetch.Wire :=
  if s.readyState == 3 then (s, []) else
  if !s.handshaken then
    if s.t.phase == .resolve then planStep s (PageFetch.onAnswer s.t a)
    else if a.status == 0 then fail s
    else match handshakeCheck sha1 s.key s.protocols a.status a.headers with
      | .error _ => fail s
      | .ok p =>
        let s := { s with handshaken := true, readyState := 1, protocol := p, events := s.events.push (.opened p), buf := a.body.toList }
        drain s (s.buf.length + 1)
  else if a.status == 0 then
    -- the connection ended (RFC 6455 §7.1.4): clean when both close frames were exchanged
    let clean := s.closeSent && s.closeRecv.isSome
    let (code, reason) := if clean then s.closeRecv.getD (1005, "") else (1006, "")
    ({ s with readyState := 3, buffered := 0, events := s.events.push (.closed code reason clean) }, [])
  else
    let s := { s with buf := s.buf ++ a.body.toList, buffered := 0 }
    drain s (s.buf.length + 1)

/-- `send(data)` (§3.3) on an open connection with a fresh masking key: the frame for the host;
when closing or closed, only `bufferedAmount` grows. `none`: still connecting
(`InvalidStateError`). -/
def send (s : Sock) (binary : Bool) (data : List UInt8) (key : List UInt8) : Option (Sock × List PageFetch.Wire) :=
  if s.readyState == 0 then none
  else if s.readyState != 1 then some ({ s with buffered := s.buffered + data.length }, [])
  else some ({ s with buffered := s.buffered + data.length, pool := s.pool ++ key },
    [sockWire s "WEBSOCKET-SEND" (some (ByteArray.mk (encodeClient key (if binary then 2 else 1) data).toArray))])

/-- `close(code, reason)` (§3.2 steps 3 to 6), the arguments checked (`closeCheck`); a reason
without a code is sent with 1000. -/
def close (s : Sock) (code : Option Nat) (reason : String) (key : List UInt8) : Sock × List PageFetch.Wire :=
  let code := match code with
    | none => if reason.isEmpty then none else some 1000
    | c => c
  if s.readyState ≥ 2 then (s, [])
  else if s.readyState == 0 then fail s
  else ({ s with readyState := 2, closeSent := true },
    [sockWire s "WEBSOCKET-SEND" (some (ByteArray.mk (encodeClient key 8 (closePayload code reason)).toArray))])

/-! ## Examples (RFC 6455 §5.7) -/

-- a single-frame unmasked text message "Hello"
#guard (match parse [0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] with
  | .frame f [] => f.fin && f.opcode == 1 && f.payload == "Hello".toUTF8.toList | _ => false)
-- a fragmented unmasked text message: "Hel" then "lo"
#guard (match parse [0x01, 0x03, 0x48, 0x65, 0x6c, 0x80, 0x02, 0x6c, 0x6f] with
  | .frame f rest => !f.fin && f.opcode == 1 && rest == [0x80, 0x02, 0x6c, 0x6f] | _ => false)
-- a single-frame masked text message "Hello" (the client's form)
#guard encodeClient [0x37, 0xfa, 0x21, 0x3d] 1 "Hello".toUTF8.toList ==
  [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]
-- a server's masked frame is refused
#guard (match parse [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] with | .bad 1002 _ => true | _ => false)
-- 256 bytes of binary data in a single unmasked frame
#guard (match parse ([0x82, 0x7E, 0x01, 0x00] ++ List.replicate 256 7) with
  | .frame f [] => f.opcode == 2 && f.payload.length == 256 | _ => false)
#guard (match parse [0x82, 0x7E, 0x01] with | .more => true | _ => false)
#guard (match parse [0x89, 0x7E, 0x00, 0x7E] with | .bad 1002 _ => true | _ => false)
#guard (match parse [0xC1, 0x00] with | .bad 1002 _ => true | _ => false)
#guard validProtocols ["chat", "superchat"] && !validProtocols ["echo", "echo"] && !validProtocols [""] &&
  !validProtocols ["a b"] && !validProtocols ["a\u0080b"]
#guard (match openCheck "http://web-platform.test:8000/x.html" "ws://web-platform.test:8888/echo" [] false with
  | .ok u => u.serialize == "ws://web-platform.test:8888/echo" | _ => false)
#guard (match openCheck "https://a.test/x.html" "/echo" [] true with | .ok u => u.serialize == "wss://a.test/echo" | _ => false)
#guard (match openCheck "http://a.test/" "ws://a.test/#x" [] false with | .error ("SyntaxError", _) => true | _ => false)
#guard (match openCheck "http://a.test/" "ftp://a.test/" [] false with | .error ("SyntaxError", _) => true | _ => false)
#guard (match openCheck "https://a.test/" "ws://a.test/" [] true with | .error ("SecurityError", _) => true | _ => false)
#guard (match openCheck "http://a.test/" "ws://a.test/" ["echo", "echo"] false with | .error ("SyntaxError", _) => true | _ => false)
#guard closeCheck (some 1000) "" == none && (closeCheck (some 1001) "").isSome && closeCheck (some 3000) "" == none &&
  (closeCheck (some 5000) "").isSome && (closeCheck none (String.ofList (List.replicate 124 'a'))).isSome
-- RFC 6455 §1.3: the key "dGhlIHNhbXBsZSBub25jZQ==" is answered "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
#guard acceptOf L4Factoidal.Crypto.sha1 "dGhlIHNhbXBsZSBub25jZQ==" == "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="

-- a connection from a local page: the handshake with the RFC's key, a text frame, the end
private def evName : Ev → String
  | .opened p => "open " ++ p | .text t => "text " ++ t | .binary b => s!"binary {b.size}" | .error => "error"
  | .closed c r k => s!"close {c} {r} {k}"
private def flow : List String :=
  let page := PageFetch.Page.ofUrl "http://127.0.0.1:8000/x.html"
  let e := "the sample nonce".toUTF8 ++ ByteArray.mk (Array.replicate 64 7)
  match openCheck "http://127.0.0.1:8000/x.html" "ws://127.0.0.1:8888/echo" [] false with
  | .error _ => ["bad url"]
  | .ok u =>
    let (s, ws) := connect page 5 9 u [] e
    let first := ws.map fun w => w.method ++ " " ++ w.url ++ " " ++ ((PageFetch.headerGet w.headers "sec-websocket-key").getD "")
    let (s, _) := onAnswer L4Factoidal.Crypto.sha1 s { status := 101, headers := [("Upgrade", "websocket"), ("Connection", "Upgrade"),
      ("Sec-WebSocket-Accept", "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=")], body := ByteArray.mk #[0x81, 0x02, 0x48, 0x69] }
    let (s, _) := onAnswer L4Factoidal.Crypto.sha1 s { status := 1, body := ByteArray.mk #[0x82, 0x01] }
    let (s, _) := onAnswer L4Factoidal.Crypto.sha1 s { status := 1, body := ByteArray.mk #[0x00] }
    let (s, _) := onAnswer L4Factoidal.Crypto.sha1 s { status := 0 }
    first ++ s.events.toList.map evName
#guard flow == ["WEBSOCKET ws://127.0.0.1:8888/echo dGhlIHNhbXBsZSBub25jZQ==", "open ", "text Hi", "binary 1", "close 1006  false"]
-- a wrong accept fails the connection; a blocked port sends nothing
#guard (let page := PageFetch.Page.ofUrl "http://127.0.0.1:8000/x.html"
  match openCheck "http://127.0.0.1:8000/x.html" "ws://127.0.0.1:8888/echo" [] false with
  | .ok u => let (s, _) := connect page 5 9 u [] (ByteArray.mk (Array.replicate 80 1))
    let (s, ws) := onAnswer L4Factoidal.Crypto.sha1 s { status := 101, headers := [("Upgrade", "websocket"), ("Connection", "Upgrade"),
      ("Sec-WebSocket-Accept", "x")] }
    s.events.toList.map evName == ["error", "close 1006  false"] && ws.map (·.method) == ["WEBSOCKET-CLOSE"]
  | .error _ => false)
#guard (match openCheck "http://127.0.0.1:8000/x.html" "ws://127.0.0.1:25/" [] false with
  | .ok u => (connect (PageFetch.Page.ofUrl "http://127.0.0.1:8000/x.html") 5 9 u [] (ByteArray.mk (Array.replicate 80 1))).2.map (·.method) == ["WEBSOCKET-CLOSE"]
  | .error _ => false)

/-! ## Theorems -/

/-- Kind: correctness theorem (RFC 6455 §5.3). Says: masking is its own inverse for a key of
four bytes: the server unmasks what the client masked. -/
theorem mask_mask (key p : List UInt8) : mask key (mask key p) = p := by
  apply List.ext_getElem
  · simp [mask]
  · intro i h1 h2
    simp [mask, List.getElem_zipIdx, UInt8.xor_assoc]

/-- Kind: policy theorem (§3.1). Says: a URL `new WebSocket` accepts is `ws` or `wss`, has no
fragment, is `wss` on an `https` page, and the subprotocols asked for are valid. -/
theorem openCheck_ok (base input : String) (ps : List String) (secure : Bool) (u : URL.Url)
    (h : openCheck base input ps secure = .ok u) :
    (u.scheme = "ws" ∨ u.scheme = "wss") ∧ u.fragment = none ∧ (secure = true → u.scheme = "wss") ∧
      validProtocols ps = true := by
  unfold openCheck at h
  split at h
  · simp at h
  · rename_i u0 _
    generalize (if u0.scheme == "http" then { u0 with scheme := "ws" }
      else if u0.scheme == "https" then { u0 with scheme := "wss" } else u0) = v at h
    by_cases h1 : (v.scheme != "ws" && v.scheme != "wss") = true
    · simp only [h1, if_true] at h; simp at h
    · simp only [h1, if_false, Bool.false_eq_true] at h
      by_cases h2 : v.fragment.isSome = true
      · simp only [h2, if_true] at h; simp at h
      · simp only [h2, if_false, Bool.false_eq_true] at h
        by_cases h3 : (secure && v.scheme == "ws") = true
        · simp only [h3, if_true] at h; simp at h
        · simp only [h3, if_false, Bool.false_eq_true] at h
          by_cases h4 : (!validProtocols ps) = true
          · simp only [h4, if_true] at h; simp at h
          · simp only [h4, if_false, Bool.false_eq_true, Except.ok.injEq] at h
            subst h
            have hs : v.scheme = "ws" ∨ v.scheme = "wss" := by
              by_cases a : v.scheme = "ws"
              · exact .inl a
              · right; simpa [a] using h1
            refine ⟨hs, by simpa using h2, fun hsec => ?_, by simpa using h4⟩
            rcases hs with hs | hs
            · simp [hsec, hs] at h3
            · exact hs

/-- Kind: policy theorem (§3.2). Says: `close()` accepts a code only when it is 1000 or in
3000 to 4999. -/
theorem closeCheck_code (c : Nat) (r : String) (h : closeCheck (some c) r = none) :
    c = 1000 ∨ (3000 ≤ c ∧ c ≤ 4999) := by
  unfold closeCheck at h
  by_cases h1 : (!(c == 1000 || (decide (3000 ≤ c) && decide (c ≤ 4999)))) = true
  · simp only [h1, if_true] at h; simp at h
  · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq] at h1
    exact h1

theorem check_none (h : Head) (hc : check h = none) :
    h.masked = false ∧ (h.op ≥ 8 → h.fin = true ∧ h.len7 ≤ 125) := by
  unfold check at hc
  by_cases a : h.rsv = true
  · simp [a] at hc
  · by_cases b : (!knownOpcode h.op) = true
    · simp [a, b] at hc
    · by_cases c : h.masked = true
      · simp [a, b, c] at hc
      · by_cases d : (decide (h.op ≥ 8) && (!h.fin || decide (h.len7 > 125))) = true
        · simp [a, b, c, d] at hc
        · refine ⟨by simpa using c, fun hop => ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
            not_and, not_or] at d
          have := d hop
          simp only [Bool.not_eq_false, Nat.not_lt] at this
          exact this

/-- Kind: security theorem (RFC 6455 §5.1). Says: a frame from the server with the mask bit
set is never read as a frame (the client fails the connection). -/
theorem parse_masked (b0 b1 : UInt8) (rest : List UInt8) (hm : (headOf b0 b1).masked = true) (f : Frame) (r : List UInt8) :
    parse (b0 :: b1 :: rest) ≠ .frame f r := by
  intro h
  simp only [parse, parseWith] at h
  split at h
  · simp at h
  · rename_i hc
    have := (check_none _ hc).1
    rw [hm] at this; simp at this

/-- Kind: safety theorem (RFC 6455 §5.5, and the engine's bound). Says: a frame read from the
server is never larger than `maxMessage`, and a control frame read (opcode 8 or more) is
whole and at most 125 bytes. -/
theorem parse_frame (buf : List UInt8) (f : Frame) (r : List UInt8) (h : parse buf = .frame f r) :
    f.payload.length ≤ maxMessage ∧ (f.opcode ≥ 8 → f.fin = true ∧ f.payload.length ≤ 125) := by
  unfold parse at h
  split at h
  · rename_i b0 b1 rest
    unfold parseWith at h
    split at h
    · simp at h
    · rename_i hc
      have hcn := check_none _ hc
      split at h
      · simp at h
      · rename_i n after hl
        by_cases big : n > maxMessage
        · simp [big] at h
        · by_cases short : after.length < n
          · simp [big, short] at h
          · simp only [big, short, if_false] at h
            simp only [Read.frame.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine ⟨?_, fun hop => ?_⟩
            · simp only [List.length_take]; omega
            · obtain ⟨hf, h125⟩ := hcn.2 hop
              refine ⟨hf, ?_⟩
              have hlt : (headOf b0 b1).len7 < 126 := by omega
              simp only [lenOf, hlt, if_true, Option.some.injEq, Prod.mk.injEq] at hl
              simp only [List.length_take]; omega
  · simp at h

/-- Kind: lemma. Says: the wires of a failed connection only close it. -/
theorem fail_wires (s : Sock) (s' : Sock) (ws : List PageFetch.Wire) (h : fail s = (s', ws)) :
    ∀ w ∈ ws, w.method = "WEBSOCKET-CLOSE" := by
  unfold fail at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp [sockWire]

/-- Kind: policy theorem. Says: a connection to a blocked port (Fetch §2.10) sends nothing: the
only wire is the one that closes it. -/
theorem connect_badPort (page : PageFetch.Page) (id cb : Nat) (u : URL.Url) (ps : List String) (e : ByteArray)
    (hb : badPorts.contains (portOf u) = true) (s : Sock) (ws : List PageFetch.Wire)
    (h : connect page id cb u ps e = (s, ws)) : ∀ w ∈ ws, w.method = "WEBSOCKET-CLOSE" := by
  unfold connect at h
  simp only [hb, if_true] at h
  exact fail_wires _ _ _ h

/-- Kind: policy theorem. Says: the first wire of a connection that is not a close is the one
`PageFetch.plan` chose for its `http`/`https` form (so it passes `mayConnect`, mixed content
and the address rule, `PageFetch.plan_send_allowed`), sent on as a resolve or as the
connection to the same address and port. -/
theorem connect_planned (page : PageFetch.Page) (id cb : Nat) (u : URL.Url) (ps : List String) (e : ByteArray)
    (s : Sock) (ws : List PageFetch.Wire) (h : connect page id cb u ps e = (s, ws)) (w : PageFetch.Wire)
    (hw : w ∈ ws) (hm : w.method ≠ "WEBSOCKET-CLOSE") :
    ∃ t w0, PageFetch.plan s.t = .send t w0 ∨ (PageFetch.plan
      { id, page, method := "GET", url := (httpForm u).serialize, headers := [], body := none, credentials := true, destination := "websocket" } = .send t w0 ∧
      (w = w0 ∨ (w.address = w0.address ∧ w.port = w0.port))) := by
  unfold connect at h
  split at h
  · exact absurd (fail_wires _ _ _ h w hw) hm
  · unfold planStep at h
    simp only at h
    split at h
    · rename_i t w0 hp
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [List.mem_singleton] at hw
      subst hw
      refine ⟨t, w0, .inr ⟨hp, ?_⟩⟩
      unfold connectWire
      split
      · exact .inl rfl
      · split
        · exact .inr ⟨rfl, rfl⟩
        · exact .inl rfl
    · exact absurd (fail_wires _ _ _ h w hw) hm

end L4Factoidal.Net.WebSocket
