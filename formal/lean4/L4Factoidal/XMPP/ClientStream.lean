/-
L4Factoidal.XMPP.ClientStream — the CLIENT half of RFC 6120, as one total
state machine. https://github.com/danbri/factoidal/issues/1107 (step 1 of
the order the owner approved on 2026-10-28: the outgoing XMPP client stream
plus the WebDAV server target). Design record:
`docs/designissues/2026-10-28-http-over-xmpp.md`.

A server behind NAT connects OUT to an XMPP server with an account, so no
port opens inbound. This module is everything that connection decides:

  RFC 6120 section 4.2, 4.3   open the stream (`start`), read the
                              server's stream header
  RFC 6120 section 6          SASL, mechanism SCRAM-SHA-256 only
  RFC 5802, RFC 7677          the SCRAM client arithmetic (proof, and the
                              check of the server signature)
  RFC 6120 section 6.4.6      the stream restart after SASL success
  RFC 6120 section 7          resource binding
  RFC 6120 section 4.4, 4.9   stream close and stream errors
  RFC 6120 section 8.4        `service-unavailable` for an IQ get or set
                              that nothing here serves (`answerUnserved`)

The host moves bytes: it opens the socket (plain TCP, or direct TLS,
XEP-0368, which is what `factoidal xmpp-serve` serves), gives every text it
reads to `feed`, writes every `Out.send`, and closes the socket on
`Out.close`. Once `Out.bound` arrives, `Out.stanza` carries each incoming
stanza; the caller (the wasm op `xmppClient*`, `Wasm/Ops/XmppClient.lean`)
gives it to `HttpOverXmpp.plan`.

Choices (implementer; the RFCs leave them to the client):

1. TLS: none in this module. The host terminates direct TLS (XEP-0368) or
   uses plain TCP to a loopback address; `Config.secureTransport` says which,
   and without it the client does not authenticate
   (https://github.com/danbri/factoidal/issues/1125). STARTTLS (RFC 6120 section 5) is not implemented: a
   server that lists `<starttls><required/></starttls>` and no SCRAM
   mechanism is refused with a reason, never answered with PLAIN.
2. SASL: SCRAM-SHA-256 only. PLAIN would send the password; SCRAM-SHA-1
   needs HMAC-SHA-1, which `L4Factoidal/Crypto/` does not have. No channel
   binding (`c=biws`, gs2 header `n,,`).
3. SCRAM iteration count: at least `minIterations` (default 4096, RFC 7677
   section 4 "at least 4096") and at most `maxIterations` (default
   1,000,000, a bound against a server that makes the client compute
   without end).
4. The combined nonce must start with the client nonce and be longer (RFC
   5802 section 5.1); the server signature in `v=` must verify (RFC 5802
   section 3: "The client then authenticates the server"). Either failure
   closes the stream.
5. After binding, the client sends initial presence `<presence/>` (RFC
   6121 section 4.2), so a server that routes by availability delivers.

The SCRAM username is the local part with `=` and `,` escaped (RFC 5802
section 5.1). SASLprep (RFC 4013) is not applied
(https://github.com/danbri/factoidal/issues/676, the PRECIS issue).

No `partial`, no `sorry`, no `axiom`. `feed` is a tail-recursive loop over
the units of the buffer.
-/
import L4Factoidal.XMPP.Server

namespace L4Factoidal.XMPP.ClientStream

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP.Server (nsStreams nsClient nsSasl nsBind nsStreamErr
  elemName elemAttr elemChildren childByNs textOf render)
open L4Factoidal.Crypto (hmacSha256 pbkdf2Sha256 sha256 xorBytes sha256DigestBytes)

/-- One client account and its limits. `clientNonce` comes from the host's
random source (RFC 5802 section 5.1); this module has none. -/
structure Config where
  /-- The local part of the account JID. -/
  user : String
  domain : String
  resource : String
  password : String
  clientNonce : String
  minIterations : Nat := 4096
  /-- The host's transport is TLS, or a plain TCP connection to a loopback
  address (`isLoopbackHost`). Without it the client refuses to
  authenticate (https://github.com/danbri/factoidal/issues/1125): the
  allow list of HTTP over XMPP trusts the `from` that the server stamps,
  which is sound only on a stream nobody else can read or change. -/
  secureTransport : Bool := false
  maxIterations : Nat := 1000000
  deriving Inhabited

inductive Stage where
  /-- Our stream header is sent; waiting for the server's. `restarted`:
  this is the stream after SASL success. -/
  | awaitHeader (restarted : Bool)
  | awaitFeatures (restarted : Bool)
  /-- `auth` sent with this client-first-message-bare. -/
  | awaitChallenge (clientFirstBare : String)
  /-- `response` sent; the server signature that must come back. -/
  | awaitSuccess (serverSignature : String)
  | awaitBind
  | bound (jid : String)
  | closed
  deriving Repr, DecidableEq, Inhabited

structure State where
  stage : Stage
  /-- Text received and not yet a complete unit. -/
  buffer : String := ""
  deriving Inhabited

/-- What the host does. -/
inductive Out where
  /-- Write these bytes (UTF-8) to the socket. -/
  | send (text : String)
  /-- Resource binding succeeded: the full JID of this connection. -/
  | bound (jid : String)
  /-- A stanza that arrived after binding, as its wire text. -/
  | stanza (text : String)
  /-- Close the socket. `reason` is empty for a normal end of stream. -/
  | close (reason : String)
  deriving Repr, DecidableEq, Inhabited

def bindId : String := "fxb1"

/-- RFC 6120 section 4.7: the initiating entity's stream header. -/
def streamHeader (cfg : Config) : String :=
  "<?xml version='1.0'?>" ++
  s!"<stream:stream xmlns='{nsClient}' xmlns:stream='{nsStreams}'" ++
  s!" to='{L4Factoidal.XMPP.Wire.escapeAttr cfg.domain}' version='1.0' xml:lang='en'>"

/-- Open the connection: send the stream header. -/
def start (cfg : Config) : State × List Out :=
  ({ stage := .awaitHeader false }, [.send (streamHeader cfg)])

/-- End the stream with a reason. -/
def fail (st : State) (reason : String) : State × List Out :=
  ({ st with stage := .closed }, [.send "</stream:stream>", .close reason])

/-- RFC 5802 section 5.1: `=` as `=3D` and `,` as `=2C` in a SCRAM name. -/
def saslName (u : String) : String :=
  (u.replace "=" "=3D").replace "," "=2C"

def clientFirstBare (cfg : Config) : String :=
  s!"n={saslName cfg.user},r={cfg.clientNonce}"

/-- `c=` for the gs2 header `n,,` (no channel binding). -/
def gs2Base64 : String := Scram.b64Encode "n,,".toUTF8

/-- The SCRAM client step (RFC 5802 section 3): from the server-first
message, the client-final message and the server signature to expect. -/
def scramFinal (cfg : Config) (cfb serverFirst : String) : Except String (String × String) := do
  let some sf := Sasl.ServerFirstMessage.parse serverFirst
    | throw "the SCRAM server-first message did not parse"
  if !(sf.nonce.startsWith cfg.clientNonce) || sf.nonce.length ≤ cfg.clientNonce.length then
    throw "the SCRAM server nonce does not extend the client nonce"
  if sf.iterationCount < cfg.minIterations then
    throw s!"the SCRAM iteration count {sf.iterationCount} is below {cfg.minIterations}"
  if sf.iterationCount > cfg.maxIterations then
    throw s!"the SCRAM iteration count {sf.iterationCount} is above {cfg.maxIterations}"
  let some salt := Scram.b64Decode sf.salt
    | throw "the SCRAM salt is not base64"
  let salted := pbkdf2Sha256 cfg.password.toUTF8 salt sf.iterationCount sha256DigestBytes
  let clientKey := hmacSha256 salted Scram.clientKeyLabel
  let storedKey := sha256 clientKey
  let noProof := s!"c={gs2Base64},r={sf.nonce}"
  let auth := Scram.authMessage cfb serverFirst noProof
  let proof := xorBytes clientKey (hmacSha256 storedKey auth.toUTF8)
  let serverKey := hmacSha256 salted Scram.serverKeyLabel
  let serverSig := Scram.b64Encode (hmacSha256 serverKey auth.toUTF8)
  pure (noProof ++ ",p=" ++ Scram.b64Encode proof, serverSig)

/-- A literal loopback address: IPv4 `127.0.0.0/8` in dotted decimal, or
IPv6 `::1` (with or without brackets). A host name, `localhost` included,
is not loopback here: its resolution is outside this module. -/
def isLoopbackHost (h : String) : Bool :=
  if h == "::1" || h == "[::1]" then true
  else
    match h.splitOn "." with
    | [a, b, c, d] =>
      [a, b, c, d].all (fun x => !x.isEmpty && x.length ≤ 3 && x.all Char.isDigit && x.toNat! ≤ 255) &&
      a.toNat! == 127
    | _ => false

#guard isLoopbackHost "127.0.0.1" && isLoopbackHost "127.9.8.7" && isLoopbackHost "::1"
#guard !isLoopbackHost "localhost" && !isLoopbackHost "128.0.0.1" && !isLoopbackHost "127.0.0.256"
#guard !isLoopbackHost "xmpp.example.org" && !isLoopbackHost "127.0.0" && !isLoopbackHost ""

/-- The condition of a SASL `failure` or a `stream:error`. -/
def conditionOf (n : Node) : String :=
  match (elemChildren n).filterMap (fun c =>
      match elemName c with
      | some t => if t == "text" then none else some t
      | none => none) with
  | t :: _ => t
  | [] => "undefined-condition"

def isSasl (n : Node) (tag : String) : Bool :=
  elemName n == some tag && elemAttr n "xmlns" == some nsSasl

/-- The mechanisms a `stream:features` element offers. -/
def mechanismsOf (features : Node) : List String :=
  match childByNs (elemChildren features) nsSasl (some "mechanisms") with
  | none => []
  | some m => (elemChildren m).filterMap (fun c =>
      if elemName c == some "mechanism" then some (textOf c).trimAscii.toString else none)

def startTlsRequired (features : Node) : Bool :=
  (elemChildren features).any (fun c =>
    elemName c == some "starttls" &&
    (elemChildren c).any (fun d => elemName d == some "required"))

def bindRequest (cfg : Config) : String :=
  render (.element "iq" [⟨"type", "set"⟩, ⟨"id", bindId⟩]
    [.element "bind" [⟨"xmlns", nsBind⟩] [.element "resource" [] [.text cfg.resource]]])

/-- One element during negotiation, or after binding. -/
def onElement (cfg : Config) (st : State) (text : String) (n : Node) : State × List Out :=
  let tag := (elemName n).getD ""
  if tag == "stream:error" then fail st s!"stream error: {conditionOf n}" else
  match st.stage with
  | .awaitFeatures false =>
    if !cfg.secureTransport then
      fail st "refusing to authenticate: the transport is neither TLS nor a loopback connection"
    else if tag != "stream:features" then fail st s!"expected stream features, got <{tag}>"
    else if (mechanismsOf n).contains "SCRAM-SHA-256" then
      let cfb := clientFirstBare cfg
      ({ st with stage := .awaitChallenge cfb },
       [.send s!"<auth xmlns='{nsSasl}' mechanism='SCRAM-SHA-256'>{Scram.b64Encode ("n,," ++ cfb).toUTF8}</auth>"])
    else if startTlsRequired n then
      fail st "the server requires STARTTLS; this client expects direct TLS (XEP-0368) or plain TCP from the host"
    else fail st "the server does not offer SASL SCRAM-SHA-256"
  | .awaitFeatures true =>
    if tag != "stream:features" then fail st s!"expected stream features, got <{tag}>"
    else if (childByNs (elemChildren n) nsBind (some "bind")).isSome then
      ({ st with stage := .awaitBind }, [.send (bindRequest cfg)])
    else fail st "the server does not offer resource binding"
  | .awaitChallenge cfb =>
    if isSasl n "failure" then fail st s!"SASL failure: {conditionOf n}"
    else if !(isSasl n "challenge") then fail st s!"expected a SASL challenge, got <{tag}>"
    else
      match (Scram.b64Decode (textOf n).trimAscii.toString).bind String.fromUTF8? with
      | none => fail st "the SASL challenge is not base64 UTF-8"
      | some sf =>
        match scramFinal cfg cfb sf with
        | .error e => fail st e
        | .ok (final, sig) =>
          ({ st with stage := .awaitSuccess sig },
           [.send s!"<response xmlns='{nsSasl}'>{Scram.b64Encode final.toUTF8}</response>"])
  | .awaitSuccess sig =>
    if isSasl n "failure" then fail st s!"SASL failure: {conditionOf n}"
    else if !(isSasl n "success") then fail st s!"expected SASL success, got <{tag}>"
    else
      let verified := match (Scram.b64Decode (textOf n).trimAscii.toString).bind String.fromUTF8? with
        | some t => (Sasl.ServerFinalMessage.parse t).bind (·.verifier) == some sig
        | none => false
      if !verified then fail st "the SCRAM server signature does not verify"
      else ({ st with stage := .awaitHeader true }, [.send (streamHeader cfg)])
  | .awaitBind =>
    if tag == "iq" && elemAttr n "id" == some bindId then
      if elemAttr n "type" == some "result" then
        let jid := match childByNs (elemChildren n) nsBind (some "bind") with
          | some b => ((elemChildren b).find? (fun c => elemName c == some "jid")).map textOf
          | none => none
        match jid with
        | some j => ({ st with stage := .bound j }, [.bound j, .send "<presence/>"])
        | none => fail st "the bind result names no JID"
      else fail st "resource binding was refused"
    else fail st s!"expected the bind result, got <{tag}>"
  | .bound _ =>
    if tag == "message" || tag == "presence" || tag == "iq" then (st, [.stanza text])
    else (st, [])
  | .awaitHeader _ => fail st s!"expected the stream header, got <{tag}>"
  | .closed => (st, [])

/-- One framed unit. -/
def onUnit (cfg : Config) (st : State) : Framing.Unit → State × List Out
  | .decl _ => (st, [])
  | .streamClose => ({ st with stage := .closed }, [.send "</stream:stream>", .close ""])
  | .streamOpen text =>
    match st.stage with
    | .awaitHeader r =>
      match Core.StreamHeader.parse text with
      | some _ => ({ st with stage := .awaitFeatures r }, [])
      | none => fail st "the server's stream header did not parse"
    | _ => fail st "a stream header in this state"
  | .element text =>
    match L4Factoidal.XMPP.Wire.parseElement text with
    | none => fail st "an element from the server did not parse"
    | some n => onElement cfg st text n

def expectsHeader (st : State) : Bool :=
  match st.stage with
  | .awaitHeader _ => true
  | _ => false

/-- Every complete unit in the buffer, in order. Tail recursive; `fuel`
is the buffer length plus one (every unit consumes at least one
character). -/
def drain (cfg : Config) : Nat → State → List Out → State × List Out
  | 0, st, acc => (st, acc)
  | fuel + 1, st, acc =>
    if st.stage == .closed then (st, acc) else
    match Framing.nextUnit (!expectsHeader st) st.buffer with
    | none => (st, acc)
    | some (u, rest) =>
      let (st', outs) := onUnit cfg { st with buffer := rest } u
      drain cfg fuel st' (acc ++ outs)

/-- Text the socket read. -/
def feed (cfg : Config) (st : State) (text : String) : State × List Out :=
  let st := { st with buffer := st.buffer ++ text }
  drain cfg (st.buffer.length + 1) st []

/-- A stanza to send on the bound stream, or nothing before binding. -/
def outgoing (st : State) (text : String) : List Out :=
  match st.stage with
  | .bound _ => [.send text]
  | _ => []

/-- The host ends the connection. -/
def close (st : State) : State × List Out :=
  match st.stage with
  | .closed => (st, [])
  | _ => ({ st with stage := .closed }, [.send "</stream:stream>"])

/-- RFC 6120 section 8.4: an IQ get or set that nothing here serves gets
`service-unavailable`; any other stanza gets nothing. -/
def answerUnserved (text : String) : List String :=
  match L4Factoidal.XMPP.Wire.parseElement text with
  | some n =>
    let ty := elemAttr n "type"
    if elemName n == some "iq" && (ty == some "get" || ty == some "set") then
      [Server.stanzaError .iq (elemAttr n "id") (elemAttr n "from") (elemAttr n "to") "cancel" "service-unavailable"]
    else []
  | none => []

/-! ## Checks: this client against `Server.step` -/

#guard saslName "a=b,c" == "a=3Db=2Cc"
#guard gs2Base64 == "biws"

private def sends (outs : List Out) : List String :=
  outs.filterMap (fun o => match o with | .send t => some t | _ => none)

/-- The server side of a test: framing and `Server.step`, collecting what
the server sends. Tail recursive. -/
private def srvDrain : Nat → Server.Session → String → List String → Server.Session × String × List String
  | 0, s, b, acc => (s, b, acc)
  | f + 1, s, b, acc =>
    match Framing.nextUnit (!s.awaitingStreamOpen) b with
    | none => (s, b, acc)
    | some (u, rest) =>
      let (s', _, outs) := Server.step s ⟨[]⟩ u
      let sent := outs.filterMap (fun o => match o with | .send t => some t | _ => none)
      srvDrain f s' rest (acc ++ sent)

/-- Run the client against the server until neither has anything to send. -/
private def converse (cfg : Config) : Nat → State → Server.Session → String → String → List Out →
    State × Server.Session × List Out
  | 0, c, s, _, _, acc => (c, s, acc)
  | f + 1, c, s, sbuf, toServer, acc =>
    if toServer.isEmpty then (c, s, acc) else
    let (s', sbuf', fromServer) := srvDrain (sbuf.length + toServer.length + 1) s (sbuf ++ toServer) []
    let (c', outs) := feed cfg c (String.join fromServer)
    converse cfg f c' s' sbuf' (String.join (sends outs)) (acc ++ outs)

private def srvCfg : Server.Config :=
  { domain := "example.org", streamId := "SID", serverNonce := "SRVNONCE"
    saltB64 := "W22ZaJ0SNY7soEsUEjb6gQ==", iterationCount := 2
    accounts := [⟨"bob", "secret"⟩], tlsCarrier := false }

private def bob (pw : String) : Config :=
  { user := "bob", domain := "example.org", resource := "dav", password := pw
    clientNonce := "CLIENTNONCE", minIterations := 1, secureTransport := true }

private def session (cfg : Config) : State × Server.Session × List Out :=
  let (c, outs) := start cfg
  converse cfg 20 c (Server.Session.init srvCfg) "" (String.join (sends outs)) outs

-- The whole negotiation against our server: SCRAM-SHA-256, the server
-- signature verified, the restart, binding, initial presence.
#guard
  let (c, s, outs) := session (bob "secret")
  c.stage == .bound "bob@example.org/dav" && s.canDeliver &&
  outs.contains (.bound "bob@example.org/dav") && outs.contains (.send "<presence/>")

-- On a transport that is neither TLS nor loopback the client sends no
-- `auth` at all (https://github.com/danbri/factoidal/issues/1125).
#guard
  let cfg := { bob "secret" with secureTransport := false }
  let (c, _, outs) := session cfg
  c.stage == .closed && !(String.join (sends outs)).contains "<auth" &&
  outs.contains (.close "refusing to authenticate: the transport is neither TLS nor a loopback connection")

-- A wrong password: the server answers `not-authorized`, the stream closes.
#guard
  let (c, _, outs) := session (bob "wrong")
  c.stage == .closed && outs.contains (.close "SASL failure: not-authorized")

-- The default minimum iteration count refuses the test server's 2.
#guard
  let cfg := { bob "secret" with minIterations := 4096 }
  let (c, _, outs) := session cfg
  c.stage == .closed && outs.any (fun o => match o with
    | .close r => r.startsWith "the SCRAM iteration count 2"
    | _ => false)

-- A server nonce that does not extend the client nonce is refused.
#guard
  (scramFinal (bob "secret") "n=bob,r=CLIENTNONCE" "r=OTHER,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=2").toOption.isNone

-- A forged server signature closes the stream before the restart.
#guard
  let cfg := bob "secret"
  let st : State := { stage := .awaitSuccess "expected" }
  let (st', outs) := feed cfg st s!"<success xmlns='{nsSasl}'>{Scram.b64Encode "v=forged".toUTF8}</success>"
  st'.stage == .closed && outs.contains (.close "the SCRAM server signature does not verify")

-- A server that offers only PLAIN is refused; the password is not sent.
#guard
  let cfg := bob "secret"
  let st : State := { stage := .awaitFeatures false }
  let (st', outs) := feed cfg st
    s!"<stream:features><mechanisms xmlns='{nsSasl}'><mechanism>PLAIN</mechanism></mechanisms></stream:features>"
  st'.stage == .closed && !(String.join (sends outs)).contains "secret"

-- After binding, stanzas pass to the caller; a stream error closes.
#guard
  let cfg := bob "secret"
  let st : State := { stage := .bound "bob@example.org/dav" }
  let (st1, o1) := feed cfg st "<message to='bob@example.org/dav'><body>x</body></message>"
  let (st2, o2) := feed cfg st1 s!"<stream:error><conflict xmlns='{nsStreamErr}'/></stream:error>"
  o1 == [.stanza "<message to='bob@example.org/dav'><body>x</body></message>"] &&
  st1.stage == .bound "bob@example.org/dav" && st2.stage == .closed &&
  o2.contains (.close "stream error: conflict")

-- A unit split across two reads waits for its end.
#guard
  let cfg := bob "secret"
  let st : State := { stage := .bound "j" }
  let (st1, o1) := feed cfg st "<message><bo"
  let (_, o2) := feed cfg st1 "dy>x</body></message>"
  o1 == [] && o2 == [.stanza "<message><body>x</body></message>"]

-- Nothing is sent before binding; an unserved IQ get gets
-- `service-unavailable` with the addresses swapped.
#guard outgoing { stage := .awaitBind } "<message/>" == []
#guard (answerUnserved "<iq type='get' id='q1' from='a@x/r' to='b@y/s'><query xmlns='urn:x'/></iq>").length == 1
#guard ((answerUnserved "<iq type='get' id='q1' from='a@x/r' to='b@y/s'/>").headD "").contains "to=\"a@x/r\" from=\"b@y/s\""
#guard answerUnserved "<iq type='result' id='q1'/>" == []

end L4Factoidal.XMPP.ClientStream
