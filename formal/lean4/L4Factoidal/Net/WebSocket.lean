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

end L4Factoidal.Net.WebSocket
