/-
L4Factoidal.XMPP.WebSocket — RFC 7395, An XMPP Subprotocol for WebSocket
(https://www.rfc-editor.org/rfc/rfc7395), as a translation at the edge of
`Server.step`, which stays the one place where protocol decisions are made.

RFC 7395 changes only the framing of a stream (section 3.3):

  * each WebSocket text message is ONE complete XML element (section
    3.3.3), so no `Framing.nextUnit` cut is needed;
  * the stream is opened with `<open xmlns='urn:ietf:params:xml:ns:xmpp-
    framing' .../>` and closed with `<close .../>` in the same namespace,
    in place of `<stream:stream>` and `</stream:stream>` (sections 3.3.1,
    3.3.2, 3.6);
  * every element carries its own namespace declarations; a
    `<stream:features>` or `<stream:error>` therefore declares
    `xmlns:stream` (section 3.3.3).

Inbound, `unitOfMessage` turns one message into one `Framing.Unit`.
Outbound, `messageOfSend` turns one `Out.send` text into one message. It
recognises the stream-open and stream-close texts by EQUALITY with what
`Server` produces (`Server.streamOpenText`, `Server.streamCloseText`),
not by a pattern, so `messageOfSend_open` and `messageOfSend_close` are
statements about exactly those values.

STARTTLS (RFC 6120 section 5) does not apply: a WebSocket connection is
protected by its own TLS (`wss:`) or by nothing, and RFC 7395 section 3.6
says the XMPP stream never negotiates TLS. `Wasm/Ops/XmppSession.lean`
opens WebSocket sessions with `startTls := false`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Server

namespace L4Factoidal.XMPP.WebSocket

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP.Server (Config)

def nsFraming : String := "urn:ietf:params:xml:ns:xmpp-framing"

/-- RFC 7395 section 3.3.2: the server's `<open/>`, the counterpart of
`Server.streamOpenText`. -/
def openText (cfg : Config) : String :=
  s!"<open xmlns='{nsFraming}' from='{cfg.domain}' id='{cfg.streamId}' version='1.0' xml:lang='en'/>"

/-- RFC 7395 section 3.6. -/
def closeText : String := s!"<close xmlns='{nsFraming}'/>"

/-- RFC 7395 section 3.3.3: add `xmlns:stream` after the element name of
a `<stream:...>` element, which a WebSocket message must declare itself. -/
def declareStreamNs (t : String) : String :=
  let decl := s!" xmlns:stream='{Server.nsStreams}'"
  if t.startsWith "<stream:features" then
    "<stream:features" ++ decl ++ (t.drop "<stream:features".length).toString
  else if t.startsWith "<stream:error" then
    "<stream:error" ++ decl ++ (t.drop "<stream:error".length).toString
  else t

/-- One `Out.send` text as one WebSocket message. -/
def messageOfSend (cfg : Config) (t : String) : String :=
  if t == Server.streamOpenText cfg then openText cfg
  else if t == Server.streamCloseText then closeText
  else declareStreamNs t

theorem messageOfSend_open (cfg : Config) :
    messageOfSend cfg (Server.streamOpenText cfg) = openText cfg := by
  simp [messageOfSend]

/-- The two texts `messageOfSend` recognises are different, so neither
rule can shadow the other: the header text begins with a 21-character
declaration, longer than the whole close text. -/
theorem streamClose_ne_open (cfg : Config) : Server.streamCloseText ≠ Server.streamOpenText cfg := by
  intro heq
  have h1 : Server.streamCloseText.length = 16 := by decide
  have h2 : 21 ≤ (Server.streamOpenText cfg).length := by
    unfold Server.streamOpenText
    simp only [String.length_append]
    have : ("<?xml version='1.0'?>" : String).length = 21 := by decide
    omega
  rw [heq] at h1
  omega

theorem messageOfSend_close (cfg : Config) :
    messageOfSend cfg Server.streamCloseText = closeText := by
  simp [messageOfSend, streamClose_ne_open cfg]

/-- One WebSocket message as one `Framing.Unit`. `<open/>` in the framing
namespace becomes a stream header with its `to`, `version` and `xml:lang`
(rendered as the `<stream:stream>` text `Core.StreamHeader.parse` reads);
`<close/>` in that namespace becomes the stream close; anything else is
one element, for `Server.step` to parse and judge. A `<stream:stream>`
sent over a WebSocket is NOT a stream header (RFC 7395 section 3.3.1): it
reaches `Server.step` as an element, which refuses it. -/
def unitOfMessage (msg : String) : Framing.Unit :=
  match Wire.parseOpenTag msg with
  | some ("open", attrs, true, rest) =>
    if Core.findAttr attrs "xmlns" == some nsFraming && rest.trim.isEmpty then
      let attr (n : String) : String :=
        match Core.findAttr attrs n with
        | some v => s!" {n}='{Wire.escapeAttr v}'"
        | none => ""
      .streamOpen s!"<stream:stream xmlns='jabber:client' xmlns:stream='{Server.nsStreams}'{attr "to"}{attr "version"}{attr "xml:lang"}>"
    else .element msg
  | some ("close", attrs, true, rest) =>
    if Core.findAttr attrs "xmlns" == some nsFraming && rest.trim.isEmpty then .streamClose
    else .element msg
  | _ => .element msg

/-! ## Checks -/

private def cfg : Config :=
  { domain := "example.com", streamId := "SID-1", serverNonce := "N", saltB64 := "W22ZaJ0SNY7soEsUEjb6gQ=="
    iterationCount := 4096, accounts := [⟨"juliet", "r0m30"⟩], tlsCarrier := true }

private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

-- RFC 7395 section 3.3.1 example: the client's open becomes a header that
-- `Server` reads, and the server answers with `<open/>`, then features
-- that declare `xmlns:stream`.
#guard
  let u := unitOfMessage s!"<open xmlns=\"{nsFraming}\" to=\"example.com\" version=\"1.0\"/>"
  match u with
  | .streamOpen _ =>
    let (s, _, outs) := Server.step (Server.Session.init cfg) { roster := [] } u
    let msgs := outs.filterMap (fun o => match o with | .send t => some (messageOfSend cfg t) | _ => none)
    s.stage == .awaitingAuth && msgs.length == 2 &&
    msgs[0]! == openText cfg &&
    has msgs[1]! s!"<stream:features xmlns:stream='{Server.nsStreams}'" &&
    has msgs[1]! "SCRAM-SHA-256"
  | _ => false

#guard unitOfMessage s!"<close xmlns='{nsFraming}'/>" == .streamClose
#guard unitOfMessage "<close xmlns='urn:example'/>" == .element "<close xmlns='urn:example'/>"
#guard unitOfMessage "<message to='a@b'><body>x</body></message>" ==
  .element "<message to='a@b'><body>x</body></message>"

-- A `<stream:stream>` over a WebSocket is not a header; the server refuses it.
#guard
  let u := unitOfMessage "<stream:stream to='example.com' version='1.0'>"
  let (s, _, _) := Server.step (Server.Session.init cfg) { roster := [] } u
  s.stage == .closed

-- A stream error carries the `xmlns:stream` declaration, and the stream
-- close becomes `<close/>`.
#guard
  let (_, _, outs) := Server.step (Server.Session.init cfg) { roster := [] } (.element "<message/>")
  let msgs := outs.filterMap (fun o => match o with | .send t => some (messageOfSend cfg t) | _ => none)
  has (String.join msgs) s!"<stream:error xmlns:stream='{Server.nsStreams}'" &&
  msgs.getLast? == some closeText

end L4Factoidal.XMPP.WebSocket
