/-
L4Factoidal.HTTP.WebSocket — the server side of RFC 6455, The WebSocket
Protocol (https://www.rfc-editor.org/rfc/rfc6455): the opening handshake
and the framing, as total functions. A socket host hands this module the
bytes it read and performs what it is told; it decides nothing (iron
rule 7).

  * `upgrade` (section 4.2): is this HTTP request an acceptable opening
    handshake, and what is the `101` response? The decision includes the
    browser-facing checks: the `Origin` allow list (section 10.2) and the
    subprotocol the caller requires (section 1.9; `xmpp` for RFC 7395).
  * `decode` (section 5.2): one frame from the front of a buffer, or
    "need more bytes", or a protocol failure with its close code
    (section 7.4.1). A server MUST close on an unmasked client frame
    (section 5.1), on reserved bits it did not negotiate (section 5.2),
    on an unknown opcode, and on a fragmented or long control frame
    (section 5.5).
  * `Reader.push` (section 5.4): reassemble fragments into messages, with
    a size limit, and refuse text that is not UTF-8 (section 8.1).
  * `encode` (section 5.2): a server frame, unmasked, with the minimal
    length encoding.

The accept key uses SHA-1 (`Crypto/SHA1.lean`) over PUBLIC data — the
client's nonce and a fixed GUID. RFC 6455 section 1.3 and section 10.3
state that it proves only that the server read the handshake; it is not
integrity or authentication. That is tier 1 of `skills/crypto-policy`.

Not implemented: extensions (section 9; `Sec-WebSocket-Extensions` is
ignored, so no RSV bit is ever negotiated) and the client side.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Crypto.SHA1
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.HTTP.WebSocket

/-! ## The opening handshake (section 4.2) -/

/-- Section 1.3. -/
def guid : String := "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- Section 4.2.2 item 5.4: base64 of SHA-1 of the key and the GUID. -/
def acceptKey (key : String) : String :=
  L4Factoidal.XSD.base64OfBytes ((Crypto.sha1 (key ++ guid).toUTF8).toList.map UInt8.toNat)

-- Section 1.3's example.
#guard acceptKey "dGhlIHNhbXBsZSBub25jZQ==" == "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="

private def lowerAscii (s : String) : String := s.map Char.toLower

/-- The comma-separated members of a header value, trimmed and lowercased. -/
def tokens (v : String) : List String :=
  (v.splitOn ",").map (fun t => lowerAscii t.trim) |>.filter (!·.isEmpty)

/-- The value of a header; names are lowercase (`HTTP.Wire.parseHeaderLine`).
Repeated fields are joined with a comma (RFC 9110 section 5.3). -/
def header (hs : List (String × String)) (name : String) : Option String :=
  match hs.filter (·.1 == name) with
  | [] => none
  | xs => some (String.intercalate "," (xs.map (·.2)))

/-- Who may open a WebSocket here. -/
structure Policy where
  /-- Exact `Origin` values (RFC 6454 serialisation, e.g.
  `https://app.example`) a browser page may connect from. -/
  allowedOrigins : List String
  /-- Accept a request that carries no `Origin`: a client that is not a
  browser (section 4.2.1 item 7 makes `Origin` a browser obligation). -/
  allowNoOrigin : Bool
  /-- The subprotocol the client must offer (`xmpp`, RFC 7395 section 3.1). -/
  protocol : String
  deriving Repr, Inhabited

inductive Upgrade where
  /-- Write `response`; from then on the connection carries frames. -/
  | accept (response : String)
  /-- Answer with this status and close. -/
  | refuse (status : Nat) (reason : String)
  deriving Repr, DecidableEq, Inhabited

/-- The origin check alone (section 10.2). -/
def originAllowed (p : Policy) (origin : Option String) : Bool :=
  match origin with
  | none => p.allowNoOrigin
  | some o => p.allowedOrigins.contains (lowerAscii o.trim)

/-- Section 4.2.1: the client's key must be base64 of 16 bytes. -/
def keyValid (key : String) : Bool :=
  match L4Factoidal.XSD.parseBase64Lex key with
  | some bytes => bytes.length == 16
  | none => false

/-- Section 4.2.1 and 4.2.2: accept or refuse an opening handshake. -/
def upgrade (p : Policy) (method : String) (headers : List (String × String)) : Upgrade :=
  let get := header headers
  if method != "GET" then .refuse 405 "the opening handshake is a GET (RFC 6455 section 4.2.1)"
  else if !((get "upgrade").map tokens |>.getD [] |>.contains "websocket") then
    .refuse 400 "Upgrade: websocket is required"
  else if !((get "connection").map tokens |>.getD [] |>.contains "upgrade") then
    .refuse 400 "Connection: Upgrade is required"
  else if (get "sec-websocket-version").map String.trim != some "13" then
    .refuse 426 "Sec-WebSocket-Version 13 is required"
  else if !originAllowed p (get "origin") then
    .refuse 403 "this Origin may not open a WebSocket here (RFC 6455 section 10.2)"
  else if !((get "sec-websocket-protocol").map tokens |>.getD [] |>.contains (lowerAscii p.protocol)) then
    .refuse 400 s!"the subprotocol {p.protocol} is required"
  else
    match get "sec-websocket-key" with
    | none => .refuse 400 "Sec-WebSocket-Key is required"
    | some key =>
      if !keyValid key.trim then .refuse 400 "Sec-WebSocket-Key is not base64 of 16 bytes"
      else .accept
        ("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n" ++
         s!"Sec-WebSocket-Accept: {acceptKey key.trim}\r\nSec-WebSocket-Protocol: {p.protocol}\r\n\r\n")

/-- An accepted handshake passed every check: GET, version 13, an allowed
`Origin` (or none, when the policy permits that), and the required
subprotocol. A refactor that drops a check fails here. -/
theorem upgrade_accept_checked (p : Policy) (method : String) (hs : List (String × String))
    (r : String) (h : upgrade p method hs = .accept r) :
    method = "GET" ∧ (header hs "sec-websocket-version").map String.trim = some "13" ∧
    originAllowed p (header hs "origin") = true ∧
    ((header hs "sec-websocket-protocol").map tokens |>.getD [] |>.contains (lowerAscii p.protocol)) = true := by
  unfold upgrade at h
  simp only at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all)

/-! ## Frames (section 5.2) -/

inductive Opcode where
  | continuation | text | binary | close | ping | pong
  deriving Repr, DecidableEq, Inhabited

def Opcode.ofNat? : Nat → Option Opcode
  | 0 => some .continuation | 1 => some .text | 2 => some .binary
  | 8 => some .close | 9 => some .ping | 10 => some .pong
  | _ => none

def Opcode.toNat : Opcode → Nat
  | .continuation => 0 | .text => 1 | .binary => 2
  | .close => 8 | .ping => 9 | .pong => 10

/-- Section 5.5: close, ping and pong. -/
def Opcode.isControl : Opcode → Bool
  | .close | .ping | .pong => true
  | _ => false

structure Frame where
  fin : Bool
  opcode : Opcode
  /-- Unmasked. -/
  payload : ByteArray
  deriving Inhabited

inductive Decoded where
  /-- The buffer holds less than one frame. -/
  | needMore
  /-- One frame, and how many bytes of the buffer it used. -/
  | frame (f : Frame) (used : Nat)
  /-- Close the connection with this status code (section 7.4.1). -/
  | fail (code : Nat) (reason : String)
  deriving Inhabited

/-- Section 5.3: XOR with the 4-byte masking key. Its own inverse. -/
def unmask (key : ByteArray) (payload : ByteArray) : ByteArray :=
  ⟨payload.data.mapIdx (fun i x => x ^^^ key[i % 4]!)⟩

theorem unmask_size (key payload : ByteArray) : (unmask key payload).size = payload.size := by
  show (payload.data.mapIdx _).size = payload.data.size
  exact Array.size_mapIdx

/-- A big-endian unsigned integer of `n` bytes at `pos`, onto `acc`. A
tail call. -/
def beNatAcc (b : ByteArray) (pos : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => beNatAcc b (pos + 1) n (acc * 256 + b[pos]!.toNat)

/-- A big-endian unsigned integer of `n` bytes at `pos`. -/
def beNat (b : ByteArray) (pos n : Nat) : Nat := beNatAcc b pos n 0

#guard beNat ⟨#[0x01, 0x02]⟩ 0 2 == 258

/-- Section 5.2: the header length and the payload length, when the
header has arrived (`b` holds at least two bytes). -/
def lengthField (b : ByteArray) : Option (Nat × Nat) :=
  if b[1]!.toNat % 128 < 126 then some (2, b[1]!.toNat % 128)
  else if b[1]!.toNat % 128 == 126 then (if b.size < 4 then none else some (4, beNat b 2 2))
  else (if b.size < 10 then none else some (10, beNat b 2 8))

/-- Section 5.2: "the minimal number of bytes MUST be used to encode the
length", and the 64-bit form has its most significant bit 0. -/
def minimalLength (len7 len : Nat) : Bool :=
  (len7 != 126 || len ≥ 126) && (len7 != 127 || (len ≥ 65536 && len < 2 ^ 63))

/-- Section 5.2: one client frame from the front of `b`, refusing every
frame a server must refuse, and any payload above `maxPayload` (1009,
section 7.4.1). -/
def decode (b : ByteArray) (maxPayload : Nat) : Decoded :=
  if b.size < 2 then .needMore
  else if (b[0]!.toNat / 16) % 8 != 0 then .fail 1002 "reserved bits set with no extension negotiated"
  else match Opcode.ofNat? (b[0]!.toNat % 16) with
  | none => .fail 1002 "unknown opcode"
  | some op =>
    if b[1]!.toNat < 128 then .fail 1002 "a client frame must be masked (RFC 6455 section 5.1)"
    else match lengthField b with
    | none => .needMore
    | some (hdr, len) =>
      if !minimalLength (b[1]!.toNat % 128) len then .fail 1002 "length not in minimal form"
      else if op.isControl && (len > 125 || b[0]!.toNat < 128) then
        .fail 1002 "a control frame is short and not fragmented (RFC 6455 section 5.5)"
      else if len > maxPayload then .fail 1009 "frame too large"
      else if b.size < hdr + 4 + len then .needMore
      else .frame ⟨b[0]!.toNat ≥ 128, op,
          unmask (b.extract hdr (hdr + 4)) (b.extract (hdr + 4) (hdr + 4 + len))⟩ (hdr + 4 + len)

/-- Every frame `decode` returns came masked: the server never acts on an
unmasked client frame (section 5.1, which exists so that a browser page
cannot make a transparent proxy cache attacker-chosen bytes; section
10.3). -/
theorem decode_frame_masked (b : ByteArray) (m : Nat) (f : Frame) (n : Nat)
    (h : decode b m = .frame f n) : 2 ≤ b.size ∧ 128 ≤ b[1]!.toNat := by
  unfold decode at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals (refine ⟨?_, ?_⟩ <;> omega)

/-- A frame never carries more than `maxPayload` bytes, and uses at least
one byte and no more than the buffer holds (so a read loop advances). -/
theorem decode_frame_bounded (b : ByteArray) (m : Nat) (f : Frame) (n : Nat)
    (h : decode b m = .frame f n) : f.payload.size ≤ m ∧ 0 < n ∧ n ≤ b.size := by
  unfold decode at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals (cases h; simp only [unmask_size, ByteArray.size_extract]; omega)

/-- Section 5.2: a server frame — FIN set, unmasked, minimal length. -/
def encode (op : Opcode) (payload : ByteArray) : ByteArray :=
  let n := payload.size
  let b0 : UInt8 := UInt8.ofNat (128 + op.toNat)
  let lenBytes : List UInt8 :=
    if n < 126 then [UInt8.ofNat n]
    else if n < 65536 then [126, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]
    else 127 :: (List.range 8).reverse.map (fun i => UInt8.ofNat (n / 256 ^ i % 256))
  ⟨(b0 :: lenBytes).toArray⟩ ++ payload

/-- A close frame with a status code (section 5.5.1). -/
def closeFrame (code : Nat) : ByteArray :=
  encode .close ⟨#[UInt8.ofNat (code / 256), UInt8.ofNat (code % 256)]⟩

/-- A client frame, masked with `key`: for tests, so `decode` is checked
against the encoding a client actually sends. -/
def encodeClient (op : Opcode) (key : ByteArray) (payload : ByteArray) (fin : Bool := true) : ByteArray :=
  let n := payload.size
  let b0 : UInt8 := UInt8.ofNat ((if fin then 128 else 0) + op.toNat)
  let lenBytes : List UInt8 :=
    if n < 126 then [UInt8.ofNat (128 + n)]
    else if n < 65536 then [254, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]
    else 255 :: (List.range 8).reverse.map (fun i => UInt8.ofNat (n / 256 ^ i % 256))
  ⟨(b0 :: lenBytes).toArray⟩ ++ key ++ unmask key payload

/-! ## Messages (section 5.4) -/

inductive Event where
  /-- A complete text message, valid UTF-8. -/
  | text (s : String)
  /-- Answer with a pong carrying the same bytes (section 5.5.2). -/
  | ping (payload : ByteArray)
  /-- The peer closed (section 5.5.1); its status code if it gave one. -/
  | close (code : Option Nat)
  /-- Close with this code and stop reading (section 7.4.1). -/
  | fail (code : Nat) (reason : String)
  deriving Inhabited

structure Reader where
  /-- A text message whose final fragment has not arrived. -/
  pending : Option ByteArray := none
  /-- The largest frame payload accepted. -/
  maxFrame : Nat := 1024 * 1024
  /-- The largest reassembled message accepted. -/
  maxMessage : Nat := 1024 * 1024
  /-- After a `fail` or a `close`, nothing more is read. -/
  done : Bool := false
  deriving Inhabited

private def finishText (r : Reader) (bytes : ByteArray) : Reader × List Event :=
  match String.fromUTF8? bytes with
  | some s => ({ r with pending := none }, [.text s])
  | none => ({ r with done := true }, [.fail 1007 "a text message is not UTF-8 (RFC 6455 section 8.1)"])

/-- Apply one frame. Binary messages are refused with 1003: the only user
of this module, RFC 7395, uses text frames only (section 3.2). -/
def Reader.push (r : Reader) (f : Frame) : Reader × List Event :=
  if r.done then (r, []) else
  match f.opcode with
  | .ping => (r, [.ping f.payload])
  | .pong => (r, [])
  | .close =>
    let code := if f.payload.size ≥ 2 then some (f.payload[0]!.toNat * 256 + f.payload[1]!.toNat) else none
    ({ r with done := true }, [.close code])
  | .binary => ({ r with done := true }, [.fail 1003 "binary messages are not accepted here"])
  | .text =>
    if r.pending.isSome then ({ r with done := true }, [.fail 1002 "a new message inside a fragmented one"])
    else if f.fin then finishText r f.payload
    else ({ r with pending := some f.payload }, [])
  | .continuation =>
    match r.pending with
    | none => ({ r with done := true }, [.fail 1002 "a continuation with no message to continue"])
    | some acc =>
      let acc' := acc ++ f.payload
      if acc'.size > r.maxMessage then ({ r with done := true }, [.fail 1009 "message too large"])
      else if f.fin then finishText r acc'
      else ({ r with pending := some acc' }, [])

/-- Read every complete frame in `buf`. Returns the reader, the bytes not
yet part of a complete frame, and the events, in order. A tail call;
`fuel` is the buffer size, and every frame uses at least one byte
(`decode_frame_bounded`). -/
def Reader.feed (r : Reader) (buf : ByteArray) (acc : List Event := []) : Nat → Reader × ByteArray × List Event
  | 0 => (r, buf, acc)
  | fuel + 1 =>
    if r.done then (r, ByteArray.empty, acc) else
    match decode buf r.maxFrame with
    | .needMore => (r, buf, acc)
    | .fail code reason => ({ r with done := true }, ByteArray.empty, acc ++ [.fail code reason])
    | .frame f n =>
      let (r', evs) := r.push f
      r'.feed (buf.extract n buf.size) (acc ++ evs) fuel

/-- After the reader is done, nothing is read: no event is produced and
the buffer is dropped. -/
theorem feed_done (r : Reader) (buf : ByteArray) (acc : List Event) (fuel : Nat)
    (h : r.done = true) : r.feed buf acc (fuel + 1) = (r, ByteArray.empty, acc) := by
  simp [Reader.feed, h]

/-! ## Checks -/

private def key4 : ByteArray := ⟨#[0x37, 0xfa, 0x21, 0x3d]⟩

private def texts (evs : List Event) : List String :=
  evs.filterMap (fun e => match e with | .text s => some s | _ => none)

private def failCode (evs : List Event) : Option Nat :=
  evs.findSome? (fun e => match e with | .fail c _ => some c | _ => none)

-- Section 5.7's example: a single-frame masked text message "Hello".
#guard
  let b : ByteArray := ⟨#[0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]⟩
  match decode b 1000 with
  | .frame f 11 => f.fin && f.opcode == .text && String.fromUTF8? f.payload == some "Hello"
  | _ => false

-- encodeClient agrees with section 5.7.
#guard encodeClient .text key4 "Hello".toUTF8 ==
  ⟨#[0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]⟩

-- Section 5.7: the unmasked server frame "Hello".
#guard encode .text "Hello".toUTF8 == ⟨#[0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]⟩

-- An unmasked client frame is refused with 1002 (section 5.1).
#guard match decode ⟨#[0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]⟩ 1000 with
  | .fail 1002 _ => true | _ => false

-- Two-byte and eight-byte lengths round-trip through the client encoding.
#guard
  let p := ByteArray.mk (Array.replicate 300 0x41)
  match decode (encodeClient .text key4 p) 100000 with
  | .frame f n => f.payload == p && n == 2 + 2 + 4 + 300 | _ => false
#guard
  let p := ByteArray.mk (Array.replicate 70000 0x42)
  match decode (encodeClient .text key4 p) 100000 with
  | .frame f _ => f.payload == p | _ => false

-- A frame above the limit is 1009, before its payload has arrived.
#guard match decode (encodeClient .text key4 (ByteArray.mk (Array.replicate 300 0)) |>.extract 0 8) 100 with
  | .fail 1009 _ => true | _ => false

-- A partial frame asks for more bytes.
#guard match decode (encodeClient .text key4 "Hello".toUTF8 |>.extract 0 7) 1000 with
  | .needMore => true | _ => false

-- Fragments reassemble (section 5.4), split across reads.
#guard
  let bytes := encodeClient .text key4 "<mes".toUTF8 (fin := false) ++
    encodeClient .continuation key4 "sage/>".toUTF8
  let (r1, rest, ev1) := ({} : Reader).feed (bytes.extract 0 5) [] 100
  let (_, _, ev2) := r1.feed (rest ++ bytes.extract 5 bytes.size) [] 100
  texts ev1 == [] && texts ev2 == ["<message/>"]

-- A ping between fragments is answered and does not break the message.
#guard
  let bytes := encodeClient .text key4 "ab".toUTF8 (fin := false) ++
    encodeClient .ping key4 "p".toUTF8 ++ encodeClient .continuation key4 "c".toUTF8
  let (_, _, evs) := ({} : Reader).feed bytes [] 100
  texts evs == ["abc"] && evs.any (fun e => match e with | .ping _ => true | _ => false)

-- Not UTF-8 is 1007; binary is 1003; a stray continuation is 1002.
#guard failCode (({} : Reader).feed (encodeClient .text key4 ⟨#[0xff, 0xfe]⟩) [] 10).2.2 == some 1007
#guard failCode (({} : Reader).feed (encodeClient .binary key4 ⟨#[1]⟩) [] 10).2.2 == some 1003
#guard failCode (({} : Reader).feed (encodeClient .continuation key4 ⟨#[1]⟩) [] 10).2.2 == some 1002

-- A reassembled message above maxMessage is 1009.
#guard
  let r : Reader := { maxMessage := 4 }
  let bytes := encodeClient .text key4 "abc".toUTF8 (fin := false) ++
    encodeClient .continuation key4 "def".toUTF8
  failCode (r.feed bytes [] 10).2.2 == some 1009

-- The handshake: section 1.3's request, from an allowed origin.
private def xmppPolicy : Policy :=
  { allowedOrigins := ["https://app.example"], allowNoOrigin := false, protocol := "xmpp" }
private def hs (extra : List (String × String)) : List (String × String) :=
  [("host", "server.example"), ("upgrade", "websocket"), ("connection", "keep-alive, Upgrade"),
   ("sec-websocket-key", "dGhlIHNhbXBsZSBub25jZQ=="), ("sec-websocket-version", "13"),
   ("sec-websocket-protocol", "xmpp")] ++ extra

#guard match upgrade xmppPolicy "GET" (hs [("origin", "https://app.example")]) with
  | .accept r => (r.splitOn "Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=").length == 2 &&
                 (r.splitOn "Sec-WebSocket-Protocol: xmpp").length == 2
  | _ => false
#guard upgrade xmppPolicy "GET" (hs [("origin", "https://evil.example")]) matches .refuse 403 _
#guard upgrade xmppPolicy "GET" (hs []) matches .refuse 403 _
#guard upgrade { xmppPolicy with allowNoOrigin := true } "GET" (hs []) matches .accept _
#guard upgrade xmppPolicy "POST" (hs [("origin", "https://app.example")]) matches .refuse 405 _
#guard upgrade xmppPolicy "GET"
  ((hs [("origin", "https://app.example")]).map (fun (k, v) =>
    if k == "sec-websocket-protocol" then (k, "chat") else (k, v))) matches .refuse 400 _

end L4Factoidal.HTTP.WebSocket
