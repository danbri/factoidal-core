/-
L4Factoidal.XMPP.Server — every protocol decision an XMPP server makes
for ONE client connection, as a total function.

  step : Session → Env → Framing.Unit → Session × Env × List Out

The host that carries the bytes (see `Harness/XmppServe.lean` and
`deploy/fly/xmpp/`) does four things and decides nothing: it reads bytes
into a buffer, asks `Framing.nextUnit` where the next unit ends, calls
`step`, and performs the `Out` actions it gets back — write these bytes
to the socket, append these bytes to that file, replace that file's
contents, close. Which stanza goes where, what a stream error is, when
authentication succeeded, what a roster looks like on disk: all of it is
here.

Specifications implemented, by section:

  RFC 6120 section 4.2   stream open, `<stream:features>`
  RFC 6120 section 4.4   `</stream:stream>` close
  RFC 6120 section 4.9   stream errors
  RFC 6120 section 5     STARTTLS, when `Config.startTls` is set: see
                         `stepPreTls` and the theorems at the end
  RFC 6120 section 6     SASL, with the mechanism list from `Core`
  RFC 6120 section 7     resource binding
  RFC 6120 section 8     stanza addressing and the three stanza kinds
  RFC 6120 section 8.4   `service-unavailable` for unhandled IQ
  RFC 6121 section 2     the roster: get, set, push, remove
  RFC 6121 section 3     presence subscription
  RFC 6121 section 4     presence broadcast to the roster
  RFC 6121 section 8     message delivery
  RFC 7677               SASL SCRAM-SHA-256 (via `XMPP.Scram`)
  XEP-0368               direct TLS: the carrier terminates it, and
                         STARTTLS is not offered — see `tlsCarrier`.
  XEP-0045               multi-user chat, when `Config.mucDomain` is set: a
                         stanza to that domain is handed to `XMPP/Muc.lean`
                         as `Out.muc` (2026-11-03)

NOT implemented, stated rather than silently skipped:
  * TLS itself. STARTTLS is decided here (offer it, require it, accept
    `<starttls/>`, answer `<proceed/>`, refuse everything else, cut the
    stream), but the handshake is the host's: `Out.startTls` tells it to
    upgrade the socket, and `Session.tlsEstablished` is how it says the
    handshake finished. A listener with neither `tlsCarrier` nor
    `startTls` has no confidentiality at all; `featuresFor` is asked for
    the post-TLS stage there, as `initialFeatures` says.
  * SCRAM channel binding (`p=tls-server-end-point`). The Lean process
    cannot see the TLS layer, so only `n`/`y` gs2 headers are accepted.
  * SASL mechanisms other than PLAIN and SCRAM-SHA-256. SCRAM-SHA-1 is
    NOT offered: `L4Factoidal/Crypto/` has SHA-1 only as a pure-Lean
    codec for the SPARQL `SHA1()` builtin, explicitly forbidden by its
    own module header from being used "for integrity or authentication".
    RFC 7677 is the current mechanism; offering it and PLAIN is the
    honest set given what is vendored.
  * Server-to-server (RFC 6120 section 4.9.3.4 dialback, and federation
    generally). One process, one client connection.
  * GC3 rooms. `L4Factoidal/XMPP/Gc3.lean` is a scope-only stub because
    the XSF specification is unfinished; implementing rooms here would be
    inventing a wire format, not implementing one.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Core
import L4Factoidal.XMPP.Framing
import L4Factoidal.XMPP.Scram

namespace L4Factoidal.XMPP.Server

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)
open L4Factoidal.XMPP.Core (Stanza StanzaKind ConnStage featuresFor findAttr)

/-! ## Namespaces -/

def nsStreams : String := "http://etherx.jabber.org/streams"
def nsClient : String := "jabber:client"
def nsSasl : String := "urn:ietf:params:xml:ns:xmpp-sasl"
def nsBind : String := "urn:ietf:params:xml:ns:xmpp-bind"
def nsSession : String := "urn:ietf:params:xml:ns:xmpp-session"
def nsStanzas : String := "urn:ietf:params:xml:ns:xmpp-stanzas"
def nsStreamErr : String := "urn:ietf:params:xml:ns:xmpp-streams"
def nsRoster : String := "jabber:iq:roster"
def nsDiscoInfo : String := "http://jabber.org/protocol/disco#info"
def nsTls : String := "urn:ietf:params:xml:ns:xmpp-tls"
def nsDiscoItems : String := "http://jabber.org/protocol/disco#items"

/-! ## The roster (RFC 6121 section 2)

An item's on-disk form is decided here, not by the host: one line per
item, four tab-separated fields, so the host's whole job is
`IO.FS.writeFile` of a string this module produced. -/

structure RosterItem where
  jid : String
  name : String
  /-- RFC 6121 section 2.1.2.5: `none`, `to`, `from` or `both`. -/
  subscription : String
  /-- RFC 6121 section 2.1.2.2: a pending outbound subscription request. -/
  ask : Bool
  deriving Repr, DecidableEq, Inhabited

namespace RosterItem

def encode (i : RosterItem) : String :=
  s!"{i.jid}\t{i.name}\t{i.subscription}\t{if i.ask then "1" else "0"}"

def decode (line : String) : Option RosterItem :=
  match line.splitOn "\t" with
  | [j, n, sub, a] => if j.isEmpty then none else some ⟨j, n, sub, a == "1"⟩
  | _ => none

/-- The `<item/>` a roster result or push carries. -/
def toXml (i : RosterItem) : Node :=
  let attrs :=
    [Attribute.mk "jid" i.jid] ++
    (if i.name.isEmpty then [] else [Attribute.mk "name" i.name]) ++
    [Attribute.mk "subscription" i.subscription] ++
    (if i.ask then [Attribute.mk "ask" "subscribe"] else [])
  .element "item" attrs []

end RosterItem

abbrev Roster := List RosterItem

def rosterEncode (r : Roster) : String :=
  String.intercalate "\n" (r.map RosterItem.encode)

def rosterDecode (s : String) : Roster :=
  (s.splitOn "\n").filterMap (fun l =>
    if l.trim.isEmpty then none else RosterItem.decode l)

def rosterFind (r : Roster) (jid : String) : Option RosterItem :=
  r.find? (fun i => i.jid == jid)

/-- Insert or replace by JID, keeping the existing order so a roster does
not reshuffle on every edit. -/
def rosterPut (r : Roster) (item : RosterItem) : Roster :=
  if (rosterFind r item.jid).isSome then
    r.map (fun i => if i.jid == item.jid then item else i)
  else r ++ [item]

def rosterRemove (r : Roster) (jid : String) : Roster :=
  r.filter (fun i => i.jid != jid)

/-- RFC 6121 section 4.4.2: presence is broadcast to contacts whose
subscription state means they are allowed to see it — `from` or `both`. -/
def presenceTargets (r : Roster) : List String :=
  (r.filter (fun i => i.subscription == "from" || i.subscription == "both")).map (·.jid)

/-! ## Accounts and configuration -/

structure Account where
  username : String
  password : String
  deriving Repr, Inhabited

structure Config where
  /-- The domain this server is authoritative for (RFC 6120 section 4.3.2's
  `to` on the initial stream). -/
  domain : String
  /-- Supplied by the host from a random source. RFC 6120 section 4.7.3
  requires the stream `id` to be unpredictable. -/
  streamId : String
  /-- Supplied by the host from a random source; the server half of the
  SCRAM nonce (RFC 5802 section 5.1). -/
  serverNonce : String
  /-- The SCRAM salt, base64, and its iteration count (RFC 7677 section 3
  recommends at least 4096). -/
  saltB64 : String
  iterationCount : Nat
  accounts : List Account
  /-- True when the carrier already terminated TLS (XEP-0368 direct TLS on
  port 5223). False on the plaintext test listener. It changes no wire
  behaviour today — there is no STARTTLS to offer or withhold — and is
  carried so a later STARTTLS implementation has one place to branch, and
  so the value is visible rather than assumed. -/
  tlsCarrier : Bool
  /-- True when the host can upgrade this connection to TLS in place (it
  holds a certificate and key). On a connection that is not already
  secure (`tlsCarrier` false) the server then offers STARTTLS as
  REQUIRED and refuses everything before it: RFC 6120 section 5.3.1 lets
  a server make TLS mandatory-to-negotiate, and with a key in hand there
  is no reason to accept credentials in clear. -/
  startTls : Bool := false
  /-- The XEP-0045 room service's domain (e.g. `conference.example.com`), or
  none for no MUC. A bound session's stanza addressed there becomes
  `Out.muc`; the room logic is `L4Factoidal.XMPP.Muc`. -/
  mucDomain : Option String := none
  deriving Inhabited

def Config.accountOf (c : Config) (user : String) : Option Account :=
  c.accounts.find? (fun a => a.username == user)

/-! ## What the host must do -/

inductive Out where
  /-- Write these bytes to this connection's socket. -/
  | send (text : String)
  /-- Append these bytes to the mailbox of that bare JID, as one framed
  stanza. The host chooses the file name; the bytes and the destination
  are decided here. A stanza routed this way may be HELD until a session of
  that account binds, so it is never used for an IQ get or set
  (`handleIq_no_route`). -/
  | route (bareJid : String) (text : String)
  /-- Deliver these bytes to the ONE session bound to that full JID, now;
  never hold them. When there is no such session, deliver `bounce` (if
  any) to THIS session instead. RFC 6120 section 10.5.3.2 and RFC 6121
  section 8.5.3.2.1: an IQ to a full JID with no matching resource is
  answered `service-unavailable`. The bounce text is decided here; the host
  only knows which full JIDs are bound. -/
  | routeFull (fullJid : String) (text : String) (bounce : Option String)
  /-- A stanza from this bound session to the MUC domain (`Config.mucDomain`):
  hand it to the room service with the sender's full JID, taken from the
  session, never from the stanza. The service answers with `routeFull`s. -/
  | muc (fromFull : String) (text : String)
  /-- Replace that bare JID's roster file with this exact text. -/
  | saveRoster (bareJid : String) (encoded : String)
  /-- Record this full JID as available or not, so other connections can
  see it. -/
  | presence (bareJid : String) (fullJid : String) (available : Bool)
  /-- Close the connection after flushing. -/
  | close
  /-- RFC 6120 section 5.4.3.3: flush the sends before this one (the
  `<proceed/>`), then start the TLS handshake on this socket as the
  server, reading nothing more in clear. When the handshake finishes,
  call `Session.tlsEstablished`; when it fails, close. Any bytes that
  arrived after `<starttls/>` and before the handshake are discarded by
  the caller of `step` (see `Wasm/Ops/XmppSession.lean`): they were
  sent in clear and must not be read as part of the secured stream. -/
  | startTls
  deriving Repr, DecidableEq, Inhabited

/-! ## Session state -/

/-- What the server is waiting for. The constructors are the RFC 6120
section 4.3 negotiation sequence in order. -/
inductive Stage where
  /-- No stream open seen yet. -/
  | initial
  /-- Stream open seen on a connection that is not secure, STARTTLS
  offered as required (RFC 6120 section 5.4.1); waiting for
  `<starttls/>`. -/
  | awaitingStartTls
  /-- `<proceed/>` sent (RFC 6120 section 5.4.2.3). The host is doing the
  TLS handshake; no unit is accepted until `Session.tlsEstablished`. -/
  | tlsPending
  /-- Stream open seen, SASL features sent, waiting for `<auth/>`. -/
  | awaitingAuth
  /-- SCRAM client-first seen and challenged; waiting for `<response/>`.
  Carries the state RFC 5802 section 3 needs to finish: the account, the
  combined nonce, and the two AuthMessage parts already exchanged. -/
  | awaitingScramResponse (user : String) (nonce : String)
      (clientFirstBare : String) (serverFirst : String)
  /-- SASL succeeded; RFC 6120 section 6.4.6 requires a NEW stream. -/
  | authenticated (user : String)
  /-- The restarted stream is open and bind is offered. -/
  | awaitingBind (user : String)
  /-- Bound (RFC 6120 section 7); stanzas flow. -/
  | bound (user : String) (resource : String)
  /-- The stream is finished; nothing further is processed. -/
  | closed
  deriving Repr, DecidableEq, Inhabited

structure Session where
  cfg : Config
  stage : Stage
  /-- Is this connection protected by TLS — by the carrier (XEP-0368) or
  by a completed STARTTLS? Only `Session.init` and
  `Session.tlsEstablished` set it. -/
  tls : Bool := false
  deriving Inhabited

/-- STARTTLS must happen before anything else on this connection. -/
def Session.requiresStartTls (s : Session) : Bool :=
  !s.tls && s.cfg.startTls

def Session.user (s : Session) : Option String :=
  match s.stage with
  | .awaitingScramResponse u _ _ _ => some u
  | .authenticated u => some u
  | .awaitingBind u => some u
  | .bound u _ => some u
  | _ => none

def Session.bareJid (s : Session) : Option String :=
  s.user.map (fun u => u ++ "@" ++ s.cfg.domain)

def Session.fullJid (s : Session) : Option String :=
  match s.stage, s.bareJid with
  | .bound _ r, some b => some (b ++ "/" ++ r)
  | _, _ => none

/-- What the host read from disk before calling `step`, and hands back
after. Only the authenticated user's roster is ever needed. -/
structure Env where
  roster : Roster
  deriving Inhabited

def Session.init (cfg : Config) : Session :=
  { cfg := cfg, stage := .initial, tls := cfg.tlsCarrier }

/-- The host reports that the TLS handshake asked for by `Out.startTls`
finished. Only a session in `tlsPending` accepts it; the result expects
a NEW stream header (RFC 6120 section 5.4.3.3: "the initiating entity
MUST initiate a new stream"). Anything else is `none`: a host that calls
it at another time has a bug, and the session must not become `tls`. -/
def Session.tlsEstablished (s : Session) : Option Session :=
  match s.stage with
  | .tlsPending => some { s with tls := true, stage := .initial }
  | _ => none

/-- Is the next unit expected to be a `<stream:stream>` opening tag? True
twice per connection: at the start (RFC 6120 section 4.2) and again right
after SASL succeeds (section 6.4.6, the stream restart). The framer needs
this, because a `<stream:stream>` that never closes can only be cut as a
unit when it is expected; at any other point the same text is an
ill-formed child element. Deciding it here rather than in the host keeps
the host free of protocol state. -/
def Session.awaitingStreamOpen (s : Session) : Bool :=
  match s.stage with
  | .initial => true
  | .authenticated _ => true
  | _ => false

/-! ## Rendering -/

def render (n : Node) : String := Wire.render n

/-- RFC 6120 section 4.2: the server's response stream header. The `from`
is the server's domain, and `id` is the unpredictable stream id. -/
def streamOpenText (cfg : Config) : String :=
  "<?xml version='1.0'?>" ++
  s!"<stream:stream xmlns='{nsClient}' xmlns:stream='{nsStreams}'" ++
  s!" from='{cfg.domain}' id='{cfg.streamId}' version='1.0' xml:lang='en'>"

/-- RFC 6120 section 4.4: the end of the stream. One definition, so
`XMPP/WebSocket.lean` can recognise it by equality. -/
def streamCloseText : String := "</stream:stream>"

/-- RFC 6120 section 6.4.1: the mechanisms this build actually
implements. Nothing else is advertised — a mechanism in this list that
`handleAuth` cannot finish would be a lie the client pays for. -/
def mechanisms : List String := ["SCRAM-SHA-256", "PLAIN"]

/-- The features offered on the FIRST stream. `Core.featuresFor .postTls`
is the source: this build has no STARTTLS to offer (the carrier holds
TLS, XEP-0368), so the stage that names "TLS settled, authenticate now"
is the correct one, and the RFC 6120 ordering theorems in `Core` apply
unchanged. -/
def initialFeatures (_cfg : Config) : String :=
  render (Core.StreamFeatures.toXml (featuresFor .postTls mechanisms))

/-- The features offered on the RESTARTED stream (RFC 6120 section 7.4):
resource binding, plus the legacy session element clients still ask for. -/
def postAuthFeatures : String :=
  render (Core.StreamFeatures.toXml (featuresFor .authenticated []))

/-- RFC 6120 section 5.4.1: the features of the first stream on a
connection that is not secure, when the host can do STARTTLS: STARTTLS
alone, marked required, and no SASL mechanism, so no client is invited to
send credentials in clear. `Core.featuresFor_startTls_iff_preTls` and
`Core.featuresFor_sasl_iff_postTls` say what `.preTls` contains. -/
def preTlsFeatures : String :=
  render (Core.StreamFeatures.toXml (featuresFor .preTls mechanisms))

/-- RFC 6120 section 5.4.2.3. -/
def proceedText : String := s!"<proceed xmlns='{nsTls}'/>"

/-- RFC 6120 section 4.9: a stream error closes the stream. -/
def streamError (condition : String) (text : String) : List Out :=
  let body : List Node :=
    [.element condition [⟨"xmlns", nsStreamErr⟩] []] ++
    (if text.isEmpty then []
     else [.element "text" [⟨"xmlns", nsStreamErr⟩, ⟨"xml:lang", "en"⟩] [.text text]])
  [ .send (render (.element "stream:error" [] body)), .send streamCloseText, .close ]

/-- RFC 6120 section 8.3: a stanza error reply, `type='error'`, keeping
the original id and swapping the addresses. -/
def stanzaError (kind : StanzaKind) (id : Option String) (to : Option String)
    (from_ : Option String) (errType : String) (condition : String) : String :=
  let attrs :=
    (to.map (Attribute.mk "to")).toList ++
    (from_.map (Attribute.mk "from")).toList ++
    [Attribute.mk "type" "error"] ++
    (id.map (Attribute.mk "id")).toList
  render (.element kind.tagName attrs
    [.element "error" [⟨"type", errType⟩] [.element condition [⟨"xmlns", nsStanzas⟩] []]])

/-! ## XML helpers over a stanza payload -/

def elemName : Node → Option String
  | .element t _ _ => some t
  | _ => none

def elemAttr (n : Node) (name : String) : Option String :=
  match n with
  | .element _ attrs _ => findAttr attrs name
  | _ => none

def elemChildren : Node → List Node
  | .element _ _ cs => cs
  | _ => []

/-- The first child element whose `xmlns` is `ns` (and, when `tag` is
given, whose name matches). Namespace handling is by the literal `xmlns`
attribute: XMPP payload elements always carry it explicitly. -/
def childByNs (payload : List Node) (ns : String) (tag : Option String) : Option Node :=
  payload.find? (fun n =>
    elemAttr n "xmlns" == some ns &&
    (match tag with | none => true | some t => elemName n == some t))

/-- The concatenated text directly inside an element. -/
def textOf (n : Node) : String :=
  String.join ((elemChildren n).filterMap (fun c =>
    match c with | .text t => some t | _ => none))

/-! ## SASL -/

/-- Split a decoded SASL PLAIN payload on its NUL separators
(RFC 4616 section 2: `authzid NUL authcid NUL passwd`). -/
def splitNul (b : ByteArray) : List String :=
  let parts := b.toList.foldl
    (fun (acc : List (List UInt8)) (c : UInt8) =>
      if c == 0 then [] :: acc
      else match acc with
        | [] => [[c]]
        | h :: t => (c :: h) :: t)
    [[]]
  (parts.map (fun bs => String.fromUTF8! (ByteArray.mk bs.reverse.toArray))).reverse

def saslSuccess (payload : String) : String :=
  if payload.isEmpty then s!"<success xmlns='{nsSasl}'/>"
  else s!"<success xmlns='{nsSasl}'>{payload}</success>"

/-- RFC 6120 section 6.5: a SASL failure element. The condition is
`not-authorized` for a bad password and `invalid-mechanism` /
`malformed-request` for the two structural refusals. -/
def saslFailure (condition : String) : String :=
  s!"<failure xmlns='{nsSasl}'><{condition}/></failure>"

def saslChallenge (payload : String) : String :=
  s!"<challenge xmlns='{nsSasl}'>{payload}</challenge>"

/-- Verify a PLAIN payload against the configured accounts. Returns the
authenticated username. RFC 4616: an authzid different from the authcid
is refused rather than ignored — ignoring it would let a client believe
it had authorised as somebody else. -/
def checkPlain (cfg : Config) (decoded : List String) : Option String :=
  match decoded with
  | [authzid, authcid, password] =>
    if !authzid.isEmpty && authzid != authcid && authzid != authcid ++ "@" ++ cfg.domain then none
    else match cfg.accountOf authcid with
      | some a => if a.password == password then some authcid else none
      | none => none
  | _ => none

/-! ## The step function -/

private def bindResult (id : Option String) (fullJid : String) : String :=
  render (.element "iq"
    ([Attribute.mk "type" "result"] ++ (id.map (Attribute.mk "id")).toList)
    [.element "bind" [⟨"xmlns", nsBind⟩] [.element "jid" [] [.text fullJid]]])

private def iqResult (id : Option String) (to : Option String) (children : List Node) : String :=
  render (.element "iq"
    ((to.map (Attribute.mk "to")).toList ++ [Attribute.mk "type" "result"] ++
      (id.map (Attribute.mk "id")).toList)
    children)

/-- The bare form of a JID string. -/
def bareOf (s : String) : String :=
  match (Jid.parse s) with
  | some j => Jid.render { j with resourcepart := none }
  | none => s

/-- Handle `<auth/>` — the SASL first step (RFC 6120 section 6.4.2). -/
def handleAuth (s : Session) (n : Node) : Session × List Out :=
  let mech := (elemAttr n "mechanism").getD ""
  let payload := textOf n
  if mech == "PLAIN" then
    match Scram.b64Decode payload with
    | none => (s, [.send (saslFailure "incorrect-encoding")])
    | some bytes =>
      match checkPlain s.cfg (splitNul bytes) with
      | some user => ({ s with stage := .authenticated user }, [.send (saslSuccess "")])
      | none => (s, [.send (saslFailure "not-authorized")])
  else if mech == "SCRAM-SHA-256" then
    match Scram.b64Decode payload with
    | none => (s, [.send (saslFailure "incorrect-encoding")])
    | some bytes =>
      let text := String.fromUTF8! bytes
      match Sasl.ClientFirstMessage.parse text with
      | none => (s, [.send (saslFailure "malformed-request")])
      | some cf =>
        match s.cfg.accountOf cf.username with
        | none => (s, [.send (saslFailure "not-authorized")])
        | some acct =>
          match Scram.credentialsOfPassword acct.password s.cfg.saltB64 s.cfg.iterationCount with
          | none => (s, [.send (saslFailure "temporary-auth-failure")])
          | some cred =>
            let nonce := cf.clientNonce ++ s.cfg.serverNonce
            let serverFirst := Scram.serverFirstOf cred nonce
            ({ s with stage := .awaitingScramResponse cf.username nonce
                        (Scram.clientFirstBare cf) serverFirst },
             [.send (saslChallenge (Scram.b64Encode serverFirst.toUTF8))])
  else (s, [.send (saslFailure "invalid-mechanism")])

/-- Handle `<response/>` — the SCRAM second step (RFC 5802 section 3). -/
def handleScramResponse (s : Session) (user nonce cfb sf : String) (n : Node) :
    Session × List Out :=
  match Scram.b64Decode (textOf n) with
  | none => (s, [.send (saslFailure "incorrect-encoding")])
  | some bytes =>
    match Sasl.ClientFinalMessage.parse (String.fromUTF8! bytes) with
    | none => (s, [.send (saslFailure "malformed-request")])
    | some cfin =>
      -- RFC 5802 section 5.1: the client MUST echo the combined nonce. A
      -- server that skips this check accepts a replayed client-first.
      if cfin.nonce != nonce then (s, [.send (saslFailure "not-authorized")])
      else
        match s.cfg.accountOf user with
        | none => (s, [.send (saslFailure "not-authorized")])
        | some acct =>
          match Scram.credentialsOfPassword acct.password s.cfg.saltB64 s.cfg.iterationCount with
          | none => (s, [.send (saslFailure "temporary-auth-failure")])
          | some cred =>
            let auth := Scram.authMessage cfb sf (Scram.clientFinalNoProof cfin)
            match Scram.verifyClientProof cred auth cfin.proof with
            | none => (s, [.send (saslFailure "not-authorized")])
            | some serverSig =>
              ({ s with stage := .authenticated user },
               [.send (saslSuccess (Scram.b64Encode ("v=" ++ serverSig).toUTF8))])

/-- Is this stanza addressed to the MUC service of this server? -/
def Config.isMuc (c : Config) (st : Stanza) : Bool :=
  match c.mucDomain, st.to with
  | some d, some t => t.domainpart == d
  | _, _ => false

/-- Does this JID text carry a resourcepart? -/
def hasResource (t : String) : Bool :=
  ((Jid.parse t).bind (·.resourcepart)).isSome

/-- The `service-unavailable` answer to an IQ that cannot be delivered,
from the address it was sent to, back to its sender. -/
def iqBounce (st : Stanza) (sender target : String) : String :=
  stanzaError .iq st.id (some sender) (some target) "cancel" "service-unavailable"

/-- Handle an IQ once bound. -/
def handleIq (s : Session) (env : Env) (st : Stanza) (raw : String) (bare full : String) :
    Env × List Out :=
  let ty := st.type.getD "get"
  let target := st.to.map Jid.render
  match target with
  | some t =>
    if bareOf t == s.cfg.domain || t == full then handleLocal ty
    -- RFC 6120 section 10.5.3.2: to a full JID, of another account or
    -- another resource of this one, deliver to that resource or bounce.
    -- An IQ result or error is never bounced (RFC 6120 section 8.3.1).
    else if hasResource t then
      (env, [.routeFull t (Wire.render (Core.Stanza.toXml { st with from_ := Jid.parse full }))
        (if ty == "get" || ty == "set" then some (iqBounce st full t) else none)])
    -- RFC 6121 section 8.5.2.1.3: to the bare JID of an account, the server
    -- answers for the account. It handles no namespace there, so a get or
    -- set is `service-unavailable` (RFC 6120 section 8.4).
    else if bareOf t == bare then handleLocal ty
    else if ty == "get" || ty == "set" then (env, [.send (iqBounce st full t)])
    else (env, [])
  | none => handleLocal ty
where
  handleLocal (ty : String) : Env × List Out :=
    let roster := childByNs st.payload nsRoster (some "query")
    let session := childByNs st.payload nsSession (some "session")
    let disco := childByNs st.payload nsDiscoInfo (some "query")
    match roster with
    | some q =>
      if ty == "get" then
        -- RFC 6121 section 2.1.3: the roster result.
        (env, [.send (iqResult st.id none
          [.element "query" [⟨"xmlns", nsRoster⟩] (env.roster.map RosterItem.toXml)])])
      else
        -- RFC 6121 section 2.3 / 2.5: set and remove, then push.
        let items := (elemChildren q).filter (fun c => elemName c == some "item")
        let applyOne : (Roster × List Node) → Node → (Roster × List Node) :=
          fun (r, pushes) it =>
            match elemAttr it "jid" with
            | none => (r, pushes)
            | some j =>
              let jb := bareOf j
              if elemAttr it "subscription" == some "remove" then
                let gone : RosterItem := ⟨jb, "", "remove", false⟩
                (rosterRemove r jb, pushes ++ [RosterItem.toXml gone])
              else
                let existing := rosterFind r jb
                let item : RosterItem :=
                  { jid := jb
                    name := (elemAttr it "name").getD ((existing.map (·.name)).getD "")
                    subscription := (existing.map (·.subscription)).getD "none"
                    ask := (existing.map (·.ask)).getD false }
                (rosterPut r item, pushes ++ [RosterItem.toXml item])
        let (r', pushes) := items.foldl applyOne (env.roster, [])
        ({ env with roster := r' },
         [ .send (iqResult st.id none []),
           .saveRoster bare (rosterEncode r'),
           .send (render (.element "iq"
             [⟨"to", (s.fullJid).getD bare⟩, ⟨"type", "set"⟩, ⟨"id", "push-" ++ st.id.getD "0"⟩]
             [.element "query" [⟨"xmlns", nsRoster⟩] pushes])) ])
    | none =>
      match session with
      | some _ => (env, [.send (iqResult st.id none [])])
      | none =>
        match disco with
        | some _ =>
          (env, [.send (iqResult st.id none
            [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
              [ .element "identity"
                  [⟨"category", "server"⟩, ⟨"type", "im"⟩, ⟨"name", "Factoidal XMPP"⟩] [],
                .element "feature" [⟨"var", nsRoster⟩] [],
                .element "feature" [⟨"var", nsDiscoInfo⟩] [] ]])])
        | none =>
          match childByNs st.payload nsDiscoItems (some "query") with
          | some _ =>
            -- XEP-0030 items on the server: the MUC service, when there is one,
            -- so a client can find it (XEP-0045 section 6.1).
            (env, [.send (iqResult st.id none
              [.element "query" [⟨"xmlns", nsDiscoItems⟩]
                (s.cfg.mucDomain.toList.map (fun d => .element "item" [⟨"jid", d⟩] []))])])
          | none =>
          if ty == "result" || ty == "error" then (env, [])
          else
            -- RFC 6120 section 8.4: an unhandled IQ gets
            -- `service-unavailable`, never silence.
            (env, [.send (stanzaError .iq st.id none (some s.cfg.domain)
              "cancel" "service-unavailable")])

/-- Handle a presence stanza once bound (RFC 6121 sections 3 and 4). -/
def handlePresence (s : Session) (env : Env) (st : Stanza) (bare full : String) :
    Env × List Out :=
  let ty := st.type.getD "available"
  match st.to with
  | none =>
    -- RFC 6121 section 4.4.2: broadcast to every contact allowed to see
    -- it, and back to this session (section 4.4.3).
    let available := ty != "unavailable"
    let out := Core.Stanza.toXml { st with from_ := Jid.parse full }
    (env,
     [.presence bare full available] ++
     (presenceTargets env.roster).map (fun t => Out.route t (render out)) ++
     [.send (render out)])
  | some target =>
    let t := bareOf (Jid.render target)
    let out := render (Core.Stanza.toXml { st with from_ := Jid.parse bare })
    if ty == "subscribe" then
      -- RFC 6121 section 3.1.2: record the pending request, push the
      -- item, then forward.
      let existing := rosterFind env.roster t
      let item : RosterItem :=
        { jid := t, name := (existing.map (·.name)).getD ""
          subscription := (existing.map (·.subscription)).getD "none", ask := true }
      let r' := rosterPut env.roster item
      ({ env with roster := r' },
       [.saveRoster bare (rosterEncode r'), .route t out])
    else if ty == "subscribed" then
      -- RFC 6121 section 3.1.4: the contact may now see our presence.
      let existing := rosterFind env.roster t
      let sub := match (existing.map (·.subscription)).getD "none" with
        | "to" => "both"
        | "both" => "both"
        | _ => "from"
      let item : RosterItem :=
        { jid := t, name := (existing.map (·.name)).getD ""
          subscription := sub, ask := (existing.map (·.ask)).getD false }
      let r' := rosterPut env.roster item
      ({ env with roster := r' },
       [.saveRoster bare (rosterEncode r'), .route t out])
    else (env, [.route t out])

/-- Handle one framed unit on a connection that is secure, or on which
STARTTLS is not required. See `step`. -/
def stepMain (s : Session) (env : Env) (u : Framing.Unit) : Session × Env × List Out :=
  match s.stage with
  | .closed => (s, env, [])
  | _ =>
  match u with
  | .decl _ => (s, env, [])
  | .streamClose =>
    ({ s with stage := .closed }, env, [.send streamCloseText, .close])
  | .streamOpen text =>
    (match Core.StreamHeader.parse text with
     | none =>
       ({ s with stage := .closed }, env,
        [.send (streamOpenText s.cfg)] ++
          streamError "invalid-xml" "the stream header did not parse")
     | some (h, _) =>
       -- RFC 6120 section 4.9.3.6: a `to` naming a domain this server is
       -- not authoritative for is `host-unknown`.
       if (h.to.map (·.domainpart)).elim false (fun d => d != s.cfg.domain) then
         ({ s with stage := .closed }, env,
          [.send (streamOpenText s.cfg)] ++
            streamError "host-unknown" "this server is not authoritative for that domain")
       else match s.stage with
         | .authenticated user =>
           -- RFC 6120 section 6.4.6: the post-SASL stream restart.
           ({ s with stage := .awaitingBind user }, env,
            [.send (streamOpenText s.cfg), .send postAuthFeatures])
         | .initial =>
           ({ s with stage := .awaitingAuth }, env,
            [.send (streamOpenText s.cfg), .send (initialFeatures s.cfg)])
         | _ =>
           ({ s with stage := .closed }, env,
            streamError "not-well-formed" "a second stream header in this state"))
  | .element text =>
    match Wire.parseElement text with
    | none =>
      ({ s with stage := .closed }, env,
       streamError "not-well-formed" "the element did not parse")
    | some node =>
      let tag := (elemName node).getD ""
      match s.stage with
      | .initial =>
        ({ s with stage := .closed }, env,
         streamError "not-well-formed" "a stanza before the stream header")
      | .awaitingAuth =>
        if tag == "auth" then
          let (s', outs) := handleAuth s node
          (s', env, outs)
        else (s, env, [.send (saslFailure "malformed-request")])
      | .awaitingScramResponse user nonce cfb sf =>
        if tag == "response" then
          let (s', outs) := handleScramResponse s user nonce cfb sf node
          (s', env, outs)
        else if tag == "abort" then
          ({ s with stage := .awaitingAuth }, env, [.send (saslFailure "aborted")])
        else (s, env, [.send (saslFailure "malformed-request")])
      | .authenticated _ =>
        ({ s with stage := .closed }, env,
         streamError "not-authorized" "a stanza before the stream restart")
      | .awaitingStartTls | .tlsPending =>
        -- Only `stepPreTls` handles these stages; a session reaches
        -- `stepMain` in one only through a host bug. Fail closed.
        ({ s with stage := .closed }, env, [.close])
      | .awaitingBind user =>
        -- RFC 6120 section 7.5/7.6: bind, with a client-proposed
        -- resource or a server-generated one.
        if tag == "iq" then
          match childByNs (elemChildren node) nsBind (some "bind") with
          | none =>
            (s, env, [.send (stanzaError .iq (elemAttr node "id") none (some s.cfg.domain)
              "cancel" "not-allowed")])
          | some b =>
            let proposed := (elemChildren b).find? (fun c => elemName c == some "resource")
            let resource := match proposed.map textOf with
              | some r => if r.isEmpty then s.cfg.streamId else r
              | none => s.cfg.streamId
            let full := user ++ "@" ++ s.cfg.domain ++ "/" ++ resource
            ({ s with stage := .bound user resource }, env,
             [.send (bindResult (elemAttr node "id") full)])
        else (s, env, [.send (saslFailure "malformed-request")])
      | .bound user resource =>
        let bare := user ++ "@" ++ s.cfg.domain
        let full := bare ++ "/" ++ resource
        match Core.Stanza.ofXml node with
        | none =>
          ({ s with stage := .closed }, env,
           streamError "unsupported-stanza-type" s!"unsupported top-level element `{tag}`")
        | some st =>
          if s.cfg.isMuc st then
            (s, env, [.muc full (render (Core.Stanza.toXml { st with from_ := Jid.parse full }))])
          else
          match st.kind with
          | .iq =>
            let (env', outs) := handleIq s env st text bare full
            (s, env', outs)
          | .presence =>
            let (env', outs) := handlePresence s env st bare full
            (s, env', outs)
          | .message =>
            -- RFC 6121 section 8.1: a message with no `to` is addressed
            -- to the sender's own account.
            match st.to with
            | none => (s, env, [.send (render (Core.Stanza.toXml
                { st with from_ := Jid.parse full, to := Jid.parse bare }))])
            | some target =>
              (s, env, [.route (bareOf (Jid.render target))
                (render (Core.Stanza.toXml { st with from_ := Jid.parse full }))])
      | .closed => (s, env, [])

/-- Is a stage one that a connection which still requires STARTTLS may
be in? None of these has a user, so no credential has been accepted. -/
def Stage.preTls : Stage → Bool
  | .initial | .awaitingStartTls | .tlsPending | .closed => true
  | _ => false

/-- Every decision on a connection that must negotiate STARTTLS first
(RFC 6120 section 5). Small on purpose: the theorems below are about this
function, and through `step_requiresStartTls` about `step`.

  * a stream header is answered with `preTlsFeatures` (STARTTLS required,
    no SASL);
  * `<starttls xmlns='urn:ietf:params:xml:ns:xmpp-tls'/>` is answered
    with `<proceed/>` and `Out.startTls`, and the session waits;
  * any other element is `policy-violation` (RFC 6120 section 4.9.3.14),
    so a client that sends `<auth/>` in clear is disconnected rather than
    told which mechanisms exist;
  * in `tlsPending` every unit closes the connection with nothing sent:
    a client MUST NOT send anything between `<starttls/>` and the
    handshake (RFC 6120 section 5.4.3.3), so whatever arrives there was
    injected or is broken. -/
def stepPreTls (s : Session) (env : Env) (u : Framing.Unit) : Session × Env × List Out :=
  match s.stage with
  | .closed => (s, env, [])
  | .tlsPending => ({ s with stage := .closed }, env, [.close])
  | .initial =>
    match u with
    | .decl _ => (s, env, [])
    | .streamOpen text =>
      match Core.StreamHeader.parse text with
      | none =>
        ({ s with stage := .closed }, env,
         [.send (streamOpenText s.cfg)] ++
           streamError "invalid-xml" "the stream header did not parse")
      | some (h, _) =>
        if (h.to.map (·.domainpart)).elim false (fun d => d != s.cfg.domain) then
          ({ s with stage := .closed }, env,
           [.send (streamOpenText s.cfg)] ++
             streamError "host-unknown" "this server is not authoritative for that domain")
        else
          ({ s with stage := .awaitingStartTls }, env,
           [.send (streamOpenText s.cfg), .send preTlsFeatures])
    | _ =>
      ({ s with stage := .closed }, env,
       streamError "not-well-formed" "a stanza before the stream header")
  | .awaitingStartTls =>
    match u with
    | .decl _ => (s, env, [])
    | .streamClose => ({ s with stage := .closed }, env, [.send streamCloseText, .close])
    | .streamOpen _ =>
      ({ s with stage := .closed }, env,
       streamError "not-well-formed" "a second stream header in this state")
    | .element text =>
      match Wire.parseElement text with
      | none =>
        ({ s with stage := .closed }, env,
         streamError "not-well-formed" "the element did not parse")
      | some node =>
        if elemName node == some "starttls" && elemAttr node "xmlns" == some nsTls then
          ({ s with stage := .tlsPending }, env, [.send proceedText, .startTls])
        else
          ({ s with stage := .closed }, env,
           streamError "policy-violation" "STARTTLS is required before anything else")
  | _ =>
    -- A stage with a user on a connection that still requires STARTTLS is
    -- unreachable (`stepPreTls_preTls`). Fail closed rather than trust it.
    ({ s with stage := .closed }, env, [.close])

/-- Handle one framed unit. Total: every input produces a session, an
environment and a list of actions, and no input can fail to be answered. -/
def step (s : Session) (env : Env) (u : Framing.Unit) : Session × Env × List Out :=
  if s.requiresStartTls then stepPreTls s env u else stepMain s env u

/-- May this session receive a stanza that arrived for it from another
connection? Only a BOUND session may (RFC 6121 section 8.5.3: an
unavailable resource is not a delivery target). The host asks BEFORE it
touches the mailbox, because a host that reads and unlinks a stanza this
function would refuse has destroyed it — measured 2026-09-07, when
exactly that lost a message between two sessions in
`tests/xmpp/server.mjs`. -/
def Session.canDeliver (s : Session) : Bool :=
  match s.stage with
  | .bound _ _ => true
  | _ => false

/-- A stanza that arrived from another connection through the host's
mailbox. It reaches the client only once the session is bound — RFC 6121
section 8.5.3 says an unavailable resource is not a delivery target — so
the gate is here, not in the host. -/
def deliver (s : Session) (text : String) : List Out :=
  match s.stage with
  | .bound _ _ => [.send text]
  | _ => []

/-- What the server sends the moment the connection opens: nothing. RFC
6120 section 4.2 makes the INITIATING entity send the first stream
header. -/
def greeting : List Out := []

/-! ## Checks

The negotiation sequence, exercised as the RFC prints it. `sends` keeps
only the bytes that go to the socket, which is what a client sees. -/

/-- Is `needle` anywhere in `hay`? Used by the checks below to assert on
the bytes a client would actually see. -/
private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def sends (outs : List Out) : List String :=
  outs.filterMap (fun o => match o with | .send t => some t | _ => none)

private def testCfg : Config :=
  { domain := "example.com", streamId := "SID-1", serverNonce := "SRVNONCE"
    saltB64 := "W22ZaJ0SNY7soEsUEjb6gQ==", iterationCount := 4096
    accounts := [⟨"juliet", "r0m30"⟩, ⟨"romeo", "juli3t"⟩], tlsCarrier := true }

private def run (s : Session) (env : Env) : List Framing.Unit →
    Session × Env × List Out
  | [] => (s, env, [])
  | u :: us =>
    let (s', env', outs) := step s env u
    let (s'', env'', outs') := run s' env' us
    (s'', env'', outs ++ outs')

-- RFC 6120 section 4.2: the stream header is answered with a header and
-- features, and the features offer SASL.
#guard
  let (s, _, outs) := step (Session.init testCfg) ⟨[]⟩
    (.streamOpen "<stream:stream to='example.com' version='1.0'>")
  s.stage == .awaitingAuth &&
  (sends outs).length == 2 &&
  has ((sends outs)[1]!) "SCRAM-SHA-256"

-- RFC 6120 section 4.9.3.6: a stream for the wrong domain is
-- `host-unknown` and the stream closes.
#guard
  let (s, _, outs) := step (Session.init testCfg) ⟨[]⟩
    (.streamOpen "<stream:stream to='elsewhere.example' version='1.0'>")
  s.stage == .closed && has (String.join (sends outs)) "host-unknown"

-- SASL PLAIN, RFC 4616: base64 of NUL "juliet" NUL "r0m30" authenticates.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, _) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>" ]
  s.stage == .authenticated "juliet"

-- The wrong password is `not-authorized` and the stage does not advance.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet wrong").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>" ]
  s.stage == .awaitingAuth &&
  has (String.join (sends outs)) "not-authorized"

-- An unknown mechanism is refused rather than accepted by default.
#guard
  let (s, _, outs) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='ANONYMOUS'/>" ]
  s.stage == .awaitingAuth &&
  has (String.join (sends outs)) "invalid-mechanism"

-- RFC 6120 section 6.4.6 and section 7: restart, bind, then the full JID
-- comes back in the bind result.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'><resource>balcony</resource></bind></iq>" ]
  s.stage == .bound "juliet" "balcony" &&
  has (String.join (sends outs)) "juliet@example.com/balcony"

-- RFC 6120 section 7.6: no resource proposed means the server assigns one.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, _) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'/></iq>" ]
  s.stage == .bound "juliet" "SID-1"

-- RFC 6120 section 6: a stanza sent before authentication is a stream
-- error, not a silently dropped stanza.
#guard
  let (s, _, outs) := step (Session.init testCfg) ⟨[]⟩ (.element "<message to='x'/>")
  s.stage == .closed &&
  has (String.join (sends outs)) "not-well-formed"

-- RFC 6121 section 8.1: a message to another account is routed to that
-- bare JID with a `from` the server stamped, not the one the client
-- claimed.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step s ⟨[]⟩
    (.element "<message to='romeo@example.com' from='mallory@evil.example' type='chat'><body>hi</body></message>")
  outs.any (fun o => match o with
    | .route t x => t == "romeo@example.com" &&
        has x "from=\"juliet@example.com/balcony\""
    | _ => false)

-- RFC 6121 section 2.1.3: the roster get returns every stored item.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := ⟨[⟨"romeo@example.com", "Romeo", "both", false⟩]⟩
  let (_, _, outs) := step s env (.element s!"<iq type='get' id='r1'><query xmlns='{nsRoster}'/></iq>")
  has (String.join (sends outs)) "romeo@example.com"

-- RFC 6121 section 2.3: a roster set stores the item, saves the file and
-- pushes the change back.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, env', outs) := step s ⟨[]⟩
    (.element s!"<iq type='set' id='r2'><query xmlns='{nsRoster}'><item jid='nurse@example.com' name='Nurse'/></query></iq>")
  env'.roster == [⟨"nurse@example.com", "Nurse", "none", false⟩] &&
  outs.any (fun o => match o with
    | .saveRoster b _ => b == "juliet@example.com" | _ => false)

-- RFC 6121 section 2.5: `subscription='remove'` deletes the item.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := ⟨[⟨"romeo@example.com", "Romeo", "both", false⟩]⟩
  let (_, env', _) := step s env
    (.element s!"<iq type='set' id='r3'><query xmlns='{nsRoster}'><item jid='romeo@example.com' subscription='remove'/></query></iq>")
  env'.roster == []

-- RFC 6121 section 4.4.2: available presence with no `to` goes to every
-- contact with subscription `from` or `both`, and back to the sender.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := ⟨[⟨"romeo@example.com", "", "both", false⟩,
                     ⟨"nurse@example.com", "", "to", false⟩]⟩
  let (_, _, outs) := step s env (.element "<presence/>")
  (outs.filterMap (fun o => match o with | .route t _ => some t | _ => none))
    == ["romeo@example.com"]

-- RFC 6121 section 3.1.2: a subscription request sets `ask` and is
-- forwarded.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, env', outs) := step s ⟨[]⟩
    (.element "<presence to='romeo@example.com' type='subscribe'/>")
  env'.roster == [⟨"romeo@example.com", "", "none", true⟩] &&
  outs.any (fun o => match o with | .route t _ => t == "romeo@example.com" | _ => false)

-- RFC 6120 section 8.4: an IQ nobody handles gets `service-unavailable`.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step s ⟨[]⟩
    (.element "<iq type='get' id='q1'><query xmlns='urn:example:nothing'/></iq>")
  has (String.join (sends outs)) "service-unavailable"

-- RFC 6120 section 4.4: the close is answered with a close and the
-- session ends.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (s', _, outs) := step s ⟨[]⟩ .streamClose
  s'.stage == .closed && outs.contains .close

-- A stanza that arrives for an unbound session is held, not delivered.
#guard deliver (Session.init testCfg) "<message/>" == []
#guard deliver { cfg := testCfg, stage := .bound "juliet" "balcony" } "<message/>"
  == [.send "<message/>"]

-- Nothing at all happens after the stream is closed.
#guard
  let s : Session := { cfg := testCfg, stage := .closed }
  let (_, _, outs) := step s ⟨[]⟩ (.element "<message to='x'/>")
  outs == []

-- The roster's on-disk form round-trips.
#guard rosterDecode (rosterEncode [⟨"a@b", "A", "both", false⟩, ⟨"c@d", "", "to", true⟩])
  == [⟨"a@b", "A", "both", false⟩, ⟨"c@d", "", "to", true⟩]

/-! ## STARTTLS: checks -/

private def tlsCfg : Config := { testCfg with tlsCarrier := false, startTls := true }

private def openHdr : Framing.Unit := .streamOpen "<stream:stream to='example.com' version='1.0'>"

-- RFC 6120 section 5.4.1: on a connection that is not secure, the first
-- features are STARTTLS, required, and nothing else.
#guard
  let (s, _, outs) := step (Session.init tlsCfg) ⟨[]⟩ openHdr
  s.stage == .awaitingStartTls &&
  has (String.join (sends outs)) "<starttls xmlns=\"urn:ietf:params:xml:ns:xmpp-tls\"><required/></starttls>" &&
  !has (String.join (sends outs)) "mechanism"

-- RFC 6120 section 5.4.2.3: `<starttls/>` is answered with `<proceed/>`
-- and the host is told to upgrade.
#guard
  let (s, _, outs) := run (Session.init tlsCfg) ⟨[]⟩
    [openHdr, .element s!"<starttls xmlns='{nsTls}'/>"]
  s.stage == .tlsPending && outs.contains .startTls &&
  has (String.join (sends outs)) "<proceed"

-- SASL in clear when STARTTLS is required: policy-violation, closed, and
-- no SASL answer of any kind.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    ((("\x00juliet\x00r0m30").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init tlsCfg) ⟨[]⟩
    [openHdr, .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>"]
  s.stage == .closed && s.user == none &&
  has (String.join (sends outs)) "policy-violation" &&
  !has (String.join (sends outs)) "success"

-- `<starttls/>` in a wrong namespace is not STARTTLS.
#guard
  let (s, _, _) := run (Session.init tlsCfg) ⟨[]⟩
    [openHdr, .element "<starttls xmlns='urn:example:not-tls'/>"]
  s.stage == .closed

-- RFC 6120 section 5.4.3.3: after `<proceed/>`, any unit closes the
-- connection and nothing is sent in clear.
#guard
  let (s, _, outs) := run (Session.init tlsCfg) ⟨[]⟩
    [openHdr, .element s!"<starttls xmlns='{nsTls}'/>", .element "<message to='x'/>"]
  s.stage == .closed && (sends outs).getLast? == some proceedText

-- The whole sequence: STARTTLS, handshake, a NEW stream offering SASL,
-- PLAIN, restart, bind.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    ((("\x00juliet\x00r0m30").toUTF8).toList.toArray))
  let (s1, _, _) := run (Session.init tlsCfg) ⟨[]⟩
    [openHdr, .element s!"<starttls xmlns='{nsTls}'/>"]
  match s1.tlsEstablished with
  | none => false
  | some s2 =>
    let (s3, _, outs) := run s2 ⟨[]⟩
      [ openHdr,
        .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
        openHdr,
        .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'><resource>r</resource></bind></iq>" ]
    s2.tls && s3.stage == .bound "juliet" "r" &&
    has (String.join (sends outs)) "SCRAM-SHA-256" &&
    !has (String.join (sends outs)) "starttls"

-- `tlsEstablished` is refused outside `tlsPending`.
#guard (Session.init tlsCfg).tlsEstablished.isNone
#guard ({ cfg := tlsCfg, stage := .bound "juliet" "r" } : Session).tlsEstablished.isNone

-- With the carrier holding TLS, STARTTLS is never offered (XEP-0368).
#guard
  let (_, _, outs) := step (Session.init { tlsCfg with tlsCarrier := true }) ⟨[]⟩ openHdr
  !has (String.join (sends outs)) "starttls" && has (String.join (sends outs)) "SCRAM-SHA-256"

/-! ## STARTTLS: theorems

What a deployment relies on, stated over `step` itself. Together they say:
on a connection that requires STARTTLS, until the host reports a finished
handshake, (1) no unit, in any number and any order, gets the session a
user (so no password or SCRAM proof is ever checked in clear), (2) no
stanza is routed, no roster is written and no presence is published, and
(3) after `<proceed/>` nothing more is accepted. -/

/-- The only actions a pre-TLS connection can produce. -/
def Out.preTlsSafe : Out → Bool
  | .send _ | .close | .startTls => true
  | _ => false

theorem step_requiresStartTls (s : Session) (env : Env) (u : Framing.Unit)
    (h : s.requiresStartTls = true) : step s env u = stepPreTls s env u := by
  simp [step, h]

theorem stepPreTls_keeps (s : Session) (env : Env) (u : Framing.Unit) :
    (stepPreTls s env u).1.tls = s.tls ∧ (stepPreTls s env u).1.cfg = s.cfg ∧
    (stepPreTls s env u).2.1 = env := by
  unfold stepPreTls
  repeat' split
  all_goals simp_all

theorem stepPreTls_preTls (s : Session) (env : Env) (u : Framing.Unit) :
    (stepPreTls s env u).1.stage.preTls = true := by
  unfold stepPreTls
  repeat' split
  all_goals simp_all [Stage.preTls]

theorem stepPreTls_safe (s : Session) (env : Env) (u : Framing.Unit) :
    ∀ o ∈ (stepPreTls s env u).2.2, o.preTlsSafe = true := by
  unfold stepPreTls
  repeat' split
  all_goals simp_all [Out.preTlsSafe, streamError]

/-- After `<proceed/>`, every unit closes the connection and sends nothing. -/
theorem step_tlsPending (s : Session) (env : Env) (u : Framing.Unit)
    (hr : s.requiresStartTls = true) (hp : s.stage = .tlsPending) :
    step s env u = ({ s with stage := .closed }, env, [.close]) := by
  rw [step_requiresStartTls s env u hr]
  unfold stepPreTls
  simp [hp]

/-- `Out.startTls` comes only from `awaitingStartTls`, and leaves the
session in `tlsPending`. -/
theorem stepPreTls_startTls (s : Session) (env : Env) (u : Framing.Unit)
    (h : Out.startTls ∈ (stepPreTls s env u).2.2) :
    s.stage = .awaitingStartTls ∧ (stepPreTls s env u).1.stage = .tlsPending := by
  revert h
  unfold stepPreTls
  repeat' split
  all_goals simp_all [streamError]

theorem Stage.preTls_user (s : Session) (h : s.stage.preTls = true) : s.user = none := by
  unfold Session.user
  cases hs : s.stage <;> simp_all [Stage.preTls]

/-- `step` over a list of units, in order; `acc` holds the actions so far.
A tail call, so a long sequence does not grow the stack
(`tools/lean-tail-recursion-audit.py`). -/
def stepsAcc (s : Session) (env : Env) : List Framing.Unit → List Out → Session × Env × List Out
  | [], acc => (s, env, acc)
  | u :: us, acc =>
    let r := step s env u
    stepsAcc r.1 r.2.1 us (acc ++ r.2.2)

/-- `step` over a list of units, in order. -/
def steps (s : Session) (env : Env) (us : List Framing.Unit) : Session × Env × List Out :=
  stepsAcc s env us []

theorem stepsAcc_requiresStartTls (us : List Framing.Unit) :
    ∀ (s : Session) (env : Env) (acc : List Out),
    s.requiresStartTls = true → s.stage.preTls = true → (∀ o ∈ acc, o.preTlsSafe = true) →
    let r := stepsAcc s env us acc
    r.1.requiresStartTls = true ∧ r.1.user = none ∧ r.2.1 = env ∧
    ∀ o ∈ r.2.2, o.preTlsSafe = true := by
  induction us with
  | nil => intro s env acc hr hp ha; simp [stepsAcc, hr, Stage.preTls_user s hp]; exact ha
  | cons u us ih =>
    intro s env acc hr hp ha
    simp only [stepsAcc]
    rw [step_requiresStartTls s env u hr]
    have ⟨htls, hcfg, henv⟩ := stepPreTls_keeps s env u
    have hr' : (stepPreTls s env u).1.requiresStartTls = true := by
      simp_all [Session.requiresStartTls]
    have ha' : ∀ o ∈ acc ++ (stepPreTls s env u).2.2, o.preTlsSafe = true := by
      intro o ho
      simp only [List.mem_append] at ho
      rcases ho with ho | ho
      · exact ha o ho
      · exact stepPreTls_safe s env u o ho
    have ⟨h1, h2, h3, h4⟩ := ih (stepPreTls s env u).1 (stepPreTls s env u).2.1 _ hr'
      (stepPreTls_preTls s env u) ha'
    exact ⟨h1, h2, by simp_all, h4⟩

/-- The main property. A connection that requires STARTTLS, fed ANY
sequence of units without the host reporting a finished handshake: still
requires STARTTLS, has no user, has an unchanged environment, and has
asked the host for nothing but socket writes, a close or the upgrade. -/
theorem steps_requiresStartTls (us : List Framing.Unit) (s : Session) (env : Env)
    (hr : s.requiresStartTls = true) (hp : s.stage.preTls = true) :
    let r := steps s env us
    r.1.requiresStartTls = true ∧ r.1.user = none ∧ r.2.1 = env ∧
    ∀ o ∈ r.2.2, o.preTlsSafe = true :=
  stepsAcc_requiresStartTls us s env [] hr hp (by simp)

/-- The handshake report: only from `tlsPending`, and the result is
secure and waits for a new stream header. -/
theorem tlsEstablished_spec (s s' : Session) (h : s.tlsEstablished = some s') :
    s.stage = .tlsPending ∧ s'.tls = true ∧ s'.stage = .initial ∧ s'.cfg = s.cfg ∧
    s'.requiresStartTls = false := by
  unfold Session.tlsEstablished at h
  split at h <;> simp_all [Session.requiresStartTls]
  subst h; simp_all

/-- The first stream on a connection that requires STARTTLS offers no SASL
mechanism: the features are exactly `featuresFor .preTls`. -/
theorem preTlsFeatures_no_sasl :
    (featuresFor .preTls mechanisms).saslMechanisms = [] ∧
    (featuresFor .preTls mechanisms).startTls = some true := by
  simp [featuresFor]

/-! ### IQ routing checks (2026-11-03) -/

private def boundJuliet : Session := { Session.init testCfg with stage := .bound "juliet" "balcony" }

-- To a full JID of another account: delivered to that resource, or bounced
-- `service-unavailable`, from the target, back to the sender, same id.
#guard
  let (_, _, outs) := step boundJuliet ⟨[]⟩ (.element "<iq type='get' id='q1' to='romeo@example.com/orchard'><query xmlns='jabber:iq:version'/></iq>")
  match outs with
  | [.routeFull to text (some bounce)] =>
    to == "romeo@example.com/orchard" && has text "from=\"juliet@example.com/balcony\"" &&
    has bounce "service-unavailable" && has bounce "id=\"q1\"" &&
    has bounce "to=\"juliet@example.com/balcony\"" && has bounce "from=\"romeo@example.com/orchard\""
  | _ => false

-- To another resource of the SAME account (issue 1139): routed, not handled here.
#guard
  let (_, _, outs) := step boundJuliet ⟨[]⟩ (.element "<iq type='get' id='q2' to='juliet@example.com/tower'><query xmlns='jabber:iq:version'/></iq>")
  match outs with
  | [.routeFull "juliet@example.com/tower" _ (some _)] => true
  | _ => false

-- An IQ result to a full JID is delivered and never bounced.
#guard
  let (_, _, outs) := step boundJuliet ⟨[]⟩ (.element "<iq type='result' id='q3' to='romeo@example.com/orchard'/>")
  match outs with
  | [.routeFull "romeo@example.com/orchard" _ none] => true
  | _ => false

-- To the bare JID of another account: the server answers for it.
#guard
  let (_, _, outs) := step boundJuliet ⟨[]⟩ (.element "<iq type='get' id='q4' to='romeo@example.com'><query xmlns='jabber:iq:version'/></iq>")
  match outs with
  | [.send t] => has t "service-unavailable" && has t "id=\"q4\""
  | _ => false

-- Roster get to one's own bare JID is still handled locally.
#guard
  let (_, _, outs) := step boundJuliet ⟨[]⟩ (.element s!"<iq type='get' id='q5' to='juliet@example.com'><query xmlns='{nsRoster}'/></iq>")
  match outs with
  | [.send t] => has t "type=\"result\""
  | _ => false

/-! ### MUC hand-off checks (2026-11-03) -/

private def boundMuc : Session :=
  { Session.init { testCfg with mucDomain := some "conference.example.com" } with stage := .bound "juliet" "balcony" }

-- A stanza to the MUC domain goes to the room service, with the SESSION's
-- full JID as sender, whatever `from` the client claimed.
#guard
  let (_, _, outs) := step boundMuc ⟨[]⟩ (.element "<presence to='tea@conference.example.com/jul' from='mallory@evil.example/x'/>")
  match outs with
  | [.muc "juliet@example.com/balcony" text] => has text "from=\"juliet@example.com/balcony\"" && !has text "mallory"
  | _ => false

-- No MUC configured: the same stanza is routed as before, not handed off.
#guard
  let (_, _, outs) := step boundJuliet ⟨[]⟩ (.element "<message to='tea@conference.example.com' type='groupchat'><body>x</body></message>")
  outs.all (fun o => match o with | .muc .. => false | _ => true)

-- disco#items on the server names the MUC service.
#guard
  let (_, _, outs) := step boundMuc ⟨[]⟩ (.element "<iq type='get' id='d1' to='example.com'><query xmlns='http://jabber.org/protocol/disco#items'/></iq>")
  match outs with
  | [.send t] => has t "jid=\"conference.example.com\""
  | _ => false

/-! ## IQ routing (2026-11-03): never held

https://github.com/danbri/factoidal/issues/1234 and /1139. An IQ get or set
must be answered: delivered to its full JID now, or bounced
(`Out.routeFull`). `Out.route` may be held in a mailbox, so no IQ uses it. -/

theorem handleIq_no_route (s : Session) (env : Env) (st : Stanza) (raw bare full : String)
    (b t : String) : Out.route b t ∉ (handleIq s env st raw bare full).2 := by
  unfold handleIq handleIq.handleLocal
  generalize Option.map Jid.render st.to = tgt
  generalize childByNs st.payload nsRoster (some "query") = r
  generalize childByNs st.payload nsSession (some "session") = se
  generalize childByNs st.payload nsDiscoInfo (some "query") = di
  generalize childByNs st.payload nsDiscoItems (some "query") = dit
  cases tgt <;> cases r <;> cases se <;> cases di <;> cases dit <;> simp only [] <;>
    simp [apply_ite (f := Prod.snd), apply_ite (f := fun l : List Out => Out.route b t ∈ l)]

end L4Factoidal.XMPP.Server
