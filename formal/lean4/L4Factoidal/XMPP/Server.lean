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
  XEP-0369, XEP-0405     MIX channels, when `Config.mixDomain` is set: a
                         stanza to that domain, and a MIX-PAM join or leave
                         to the user's own JID, go to `XMPP/Mix.lean` as
                         `Out.mix` (2026-11-03)
  GC3 (prototype)        Groupchat 3.0, when `Config.gc3Domain` is set; NO
                         published spec: `XMPP/Gc3.lean` names every invented
                         wire choice (2026-11-03)

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
import L4Factoidal.Net.LoginLimit

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
def nsMixPam : String := "urn:xmpp:mix:pam:2"

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
  /-- The XEP-0369 MIX service's domain (e.g. `mix.example.com`), or none for
  no MIX. A stanza addressed there, and a MIX-PAM `<client-join/>` or
  `<client-leave/>` (XEP-0405) in an IQ to the user's own JID, become
  `Out.mix`; the channel logic is `L4Factoidal.XMPP.Mix`. -/
  mixDomain : Option String := none
  /-- The GC3 prototype service's domain (`L4Factoidal.XMPP.Gc3`; there is no
  published GC3 specification), or none. -/
  gc3Domain : Option String := none
  /-- Supplied by the host from a random source, the same for every session of
  a server. It gives each name its salt (`saltFor`). Empty: every name has
  `saltB64`. -/
  saltSeed : String := ""
  /-- The SCRAM keys of each account, derived once when the server opens, so a
  login runs no PBKDF2. An account that is not here is derived at login. -/
  credentials : List (String × Scram.StoredCredentials) := []
  /-- RFC 6120 section 6.4.5: failed SASL attempts on one stream before it is
  closed (`Session.afterSasl`). -/
  maxAuthFailures : Nat := 3
  /-- The most items in one roster (`Env.rosterFits`). -/
  maxRosterItems : Nat := 1000
  deriving Inhabited

def Config.accountOf (c : Config) (user : String) : Option Account :=
  c.accounts.find? (fun a => a.username == user)

/-! ## The accounts file

One account per line; a blank line and a `#` line are skipped.

  name:password
  name:SCRAM-SHA-256$<iterations>:<salt>$<StoredKey>:<ServerKey>

The second form holds no password: the three values are base64, and SCRAM is the
one mechanism that can use it (`checkPlain` refuses an empty stored password).
`verifierLine` writes it. A line that is neither form stops the start
(`accountsOfText`), so a mistake in the file never makes an account. The error
names the line by its number and never quotes it: it may hold a password. -/

def verifierPrefix : String := "SCRAM-SHA-256$"

/-- The text after `name:` of a verifier line. -/
def verifierText (c : Scram.StoredCredentials) : String :=
  verifierPrefix ++ toString c.iterationCount ++ ":" ++ c.saltB64 ++ "$" ++
    Scram.b64Encode c.storedKey ++ ":" ++ Scram.b64Encode c.serverKey

/-- Read the text after `name:` of a verifier line. -/
def verifierOf (t : String) : Option Scram.StoredCredentials :=
  if !t.startsWith verifierPrefix then none
  else match (t.drop verifierPrefix.length).toString.splitOn "$" with
    | [a, b] =>
      match a.splitOn ":", b.splitOn ":" with
      | [i, salt], [stored, server] =>
        match i.toNat?, Scram.b64Decode salt, Scram.b64Decode stored, Scram.b64Decode server with
        | some n, some _, some k, some v =>
          if n == 0 || k.size != 32 || v.size != 32 then none
          else some { saltB64 := salt, iterationCount := n, storedKey := k, serverKey := v }
        | _, _, _, _ => none
      | _, _ => none
    | _ => none

/-- One line of the accounts file, read: the account, and its keys when the line
is a verifier. -/
def accountOfLine (line : String) : Except String (Account × Option Scram.StoredCredentials) :=
  match line.splitOn ":" with
  | [_] => .error "no colon"
  | u :: rest =>
    let secret := String.intercalate ":" rest
    if u.isEmpty then .error "no name"
    else if secret.isEmpty then .error "no password"
    else if secret.startsWith verifierPrefix then
      match verifierOf secret with
      | some c => .ok (⟨u, ""⟩, some c)
      | none => .error "a verifier that does not read"
    else .ok (⟨u, secret⟩, none)
  | [] => .error "no colon"

/-- The accounts of a file, with the keys of its verifier lines. A left fold over
the lines, tail-recursive in compiled code. The first bad line, or a name that
comes twice, is an error. -/
def accountsOfText (text : String) :
    Except String (List Account × List (String × Scram.StoredCredentials)) :=
  let step (acc : Nat × Except String (List Account × List (String × Scram.StoredCredentials))) (raw : String) :=
    let n := acc.1 + 1
    let l := raw.trim
    match acc.2 with
    | .error e => (n, .error e)
    | .ok (as, cs) =>
      if l.isEmpty || l.startsWith "#" then (n, .ok (as, cs))
      else match accountOfLine l with
        | .error e => (n, .error s!"accounts: line {n}: {e}")
        | .ok (a, c) =>
          if as.any (·.username == a.username) then (n, .error s!"accounts: line {n}: a name that came before")
          else (n, .ok (as ++ [a], cs ++ (c.map (a.username, ·)).toList))
  ((text.splitOn "\n").foldl step (0, .ok ([], []))).2

/-- The salt of a name, known to this server or not: an HMAC of the name under
`saltSeed`, so two accounts have different salts and a name with no account has
one of the same form. -/
def Config.saltFor (c : Config) (user : String) : String :=
  if c.saltSeed.isEmpty then c.saltB64
  else Scram.b64Encode ((L4Factoidal.Crypto.hmacSha256 c.saltSeed.toUTF8 ("salt:" ++ user).toUTF8).extract 0 16)

/-- The SCRAM keys of an account. -/
def Config.credentialOf (c : Config) (user : String) : Option Scram.StoredCredentials :=
  match c.credentials.find? (·.1 == user) with
  | some (_, cred) => some cred
  | none => (c.accountOf user).bind (fun a =>
      Scram.credentialsOfPassword a.password (c.saltFor user) c.iterationCount)

/-- Keys for a name with no account: a SASL exchange for such a name runs like
any other, and ends in `not-authorized` at the same step (`handleScramResponse`
gives success only to an account). -/
def Config.decoyCredential (c : Config) (user : String) : Scram.StoredCredentials :=
  { saltB64 := c.saltFor user, iterationCount := c.iterationCount
    storedKey := L4Factoidal.Crypto.hmacSha256 c.saltSeed.toUTF8 ("stored:" ++ user).toUTF8
    serverKey := L4Factoidal.Crypto.hmacSha256 c.saltSeed.toUTF8 ("server:" ++ user).toUTF8 }

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
  /-- A stanza for the MIX service (`Config.mixDomain`), with the sender's full
  JID from the session. The service answers with `route` (a channel message
  to an account, which may be held) and `routeFull` (an IQ answer). -/
  | mix (fromFull : String) (text : String)
  /-- A stanza for the GC3 prototype service (`Config.gc3Domain`), with the
  sender's full JID from the session. Answered like `mix`. -/
  | gc3 (fromFull : String) (text : String)
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

/-! ## The failed SASL login limit (https://github.com/danbri/factoidal/issues/1128)

Audit row C2 of `docs/designissues/2026-10-28-feature-combination-safety.md`
(invariant I2) and the owner's rule of 2026-10-28 (a login surface limits
failed logins by default; `--dangerously-disable-ratelimits` turns it off,
with a warning at start). The counters are `L4Factoidal.Net.LoginLimit`, the
same as the WebDAV login's. The numbers are the implementer's: at most 5
failures in 60 seconds for one account name (`account:` and the name as
sent; a name with no account counts the same way) and for one client address
(`address:` and `clientPrefix`; IPv6 by its /64). An address also has a slower
limit, which backs it off for longer: at most 20 failures in an hour
(`backoffLimits`). An attempt whose name or address is blocked gets
`temporary-auth-failure` (RFC 6120 §6.5.12) before any password check: the
right password too, until the window ends. A failure is a PLAIN payload whose
password does not match, and a SCRAM proof or nonce that does not verify, for a
name with an account or without one. A malformed payload (`incorrect-encoding`,
`malformed-request`, `invalid-mechanism`) checks no password and is not
counted. A key with an empty part (no name, no address) is not used. -/

structure AuthGuard where
  limits : L4Factoidal.Net.LoginLimit.Limits := {}
  failures : L4Factoidal.Net.LoginLimit.Failures := {}
  /-- The host's clock, in seconds. -/
  now : Nat := 0
  /-- The client's address as the socket gives it (`""`: unknown). -/
  address : String := ""
  /-- The slower limit of one client address, and its counters. -/
  backoffLimits : L4Factoidal.Net.LoginLimit.Limits := { maxFailures := 20, window := 3600 }
  backoff : L4Factoidal.Net.LoginLimit.Failures := {}
  deriving Inhabited

/-- The key of the client's address, when it is known. -/
def AuthGuard.addressKeys (g : AuthGuard) : List String :=
  let q : L4Factoidal.Net.LoginLimit.Requester := .tcp g.address
  if q.valid then [L4Factoidal.Net.LoginLimit.requesterKey q] else []

/-- The keys of a SASL attempt for the account name `user`. -/
def AuthGuard.keys (g : AuthGuard) (user : String) : List String :=
  (if user.isEmpty then [] else ["account:" ++ user]) ++ g.addressKeys

/-- `backoffLimits`, turned off with `limits`. -/
def AuthGuard.slowLimits (g : AuthGuard) : L4Factoidal.Net.LoginLimit.Limits :=
  { g.backoffLimits with enabled := g.limits.enabled }

def AuthGuard.blocked (g : AuthGuard) (user : String) : Bool :=
  (g.failures.check g.limits g.now (g.keys user)).isSome ||
  (g.backoff.check g.slowLimits g.now g.addressKeys).isSome

def AuthGuard.fail (g : AuthGuard) (user : String) : AuthGuard :=
  { g with failures := g.failures.record g.limits g.now (g.keys user)
           backoff := g.backoff.record g.slowLimits g.now g.addressKeys }

/-- The start warning of `xmpp-serve --dangerously-disable-ratelimits`. -/
def saslLimitWarnings (l : L4Factoidal.Net.LoginLimit.Limits) : List String :=
  if l.enabled then []
  else ["--dangerously-disable-ratelimits: failed SASL logins are NOT limited; any client that can reach this port " ++
        "can try passwords without end (https://github.com/danbri/factoidal/issues/1128). " ++
        "Held stanzas have no sender rate; their caps stay on"]

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
  /-- SASL attempts on this stream that failed. -/
  authFailures : Nat := 0
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
  /-- The failed SASL login limit and its counters (issue 1128). The host
  keeps `guard.failures` between connections of one server and gives the
  clock and the client's address. -/
  guard : AuthGuard := {}
  /-- May this account's roster be written now? The host keeps a rate on the
  writes, each of which may be a write of the whole roster to its state. -/
  rosterOpen : Bool := true
  /-- The full JIDs of the server's live sessions, for a bind to choose a free one. A host with no
  shared session table gives none. -/
  bound : List String := []
  deriving Inhabited

/-- May the roster become `r'`? Not past the rate; and not past `max` unless it
does not grow. -/
def Env.rosterFits (env : Env) (max : Nat) (r' : Roster) : Bool :=
  env.rosterOpen && (decide (r'.length ≤ max) || decide (r'.length ≤ env.roster.length))

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
      | some a => if !a.password.isEmpty && a.password == password then some authcid else none
      | none => none
  | _ => none

/-- An account with no stored password (a verifier) has no PLAIN login, and
an empty password from a client matches nothing. -/
theorem checkPlain_empty (cfg : Config) (z u p : String) (a : Account)
    (ha : cfg.accountOf u = some a) (he : a.password = "") :
    checkPlain cfg [z, u, p] = none := by
  simp [checkPlain, ha, he]

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

/-- The result of a disco query, `from` the address it was sent to (RFC 6120
section 8.1.2.1). Profanity 0.19.0 stops with a segmentation fault without it. -/
private def iqResultFrom (st : Stanza) (children : List Node) : String :=
  render (.element "iq"
    ((st.to.map (fun j => Attribute.mk "from" (Jid.render j))).toList ++ [Attribute.mk "type" "result"] ++
      (st.id.map (Attribute.mk "id")).toList)
    children)

/-- The bare form of a JID string. -/
def bareOf (s : String) : String :=
  match (Jid.parse s) with
  | some j => Jid.render { j with resourcepart := none }
  | none => s

/-- The account name of an `<auth/>` element, when it can be read: the
authcid of a PLAIN payload, the username of a SCRAM client-first. -/
def authUser? (n : Node) : Option String :=
  let mech := (elemAttr n "mechanism").getD ""
  match Scram.b64Decode (textOf n) with
  | none => none
  | some bytes =>
    if mech == "PLAIN" then
      match splitNul bytes with
      | [_, authcid, _] => some authcid
      | _ => none
    else if mech == "SCRAM-SHA-256" then
      (Sasl.ClientFirstMessage.parse (String.fromUTF8! bytes)).map (·.username)
    else none

/-- `<auth/>` after the limit check. -/
def handleAuthChecked (s : Session) (g : AuthGuard) (n : Node) : Session × AuthGuard × List Out :=
  let mech := (elemAttr n "mechanism").getD ""
  let payload := textOf n
  if mech == "PLAIN" then
    match Scram.b64Decode payload with
    | none => (s, g, [.send (saslFailure "incorrect-encoding")])
    | some bytes =>
      match checkPlain s.cfg (splitNul bytes) with
      | some user => ({ s with stage := .authenticated user }, g, [.send (saslSuccess "")])
      | none => (s, g.fail ((authUser? n).getD ""), [.send (saslFailure "not-authorized")])
  else if mech == "SCRAM-SHA-256" then
    match Scram.b64Decode payload with
    | none => (s, g, [.send (saslFailure "incorrect-encoding")])
    | some bytes =>
      let text := String.fromUTF8! bytes
      match Sasl.ClientFirstMessage.parse text with
      | none => (s, g, [.send (saslFailure "malformed-request")])
      | some cf =>
        match s.cfg.accountOf cf.username, s.cfg.credentialOf cf.username with
        | some _, none => (s, g, [.send (saslFailure "temporary-auth-failure")])
        | _, known =>
          -- A name with no account gets a challenge of the same form, so this
          -- step does not say which names exist.
          let cred := known.getD (s.cfg.decoyCredential cf.username)
          let nonce := cf.clientNonce ++ s.cfg.serverNonce
          let serverFirst := Scram.serverFirstOf cred nonce
          ({ s with stage := .awaitingScramResponse cf.username nonce
                      (Scram.clientFirstBare cf) serverFirst }, g,
           [.send (saslChallenge (Scram.b64Encode serverFirst.toUTF8))])
  else (s, g, [.send (saslFailure "invalid-mechanism")])

/-- Handle `<auth/>` — the SASL first step (RFC 6120 section 6.4.2). An
attempt whose account name or client address is blocked by the failed-login
limit gets `temporary-auth-failure` with no password check
(`handleAuth_blocked`). -/
def handleAuth (s : Session) (g : AuthGuard) (n : Node) : Session × AuthGuard × List Out :=
  match authUser? n with
  | some u => if g.blocked u then (s, g, [.send (saslFailure "temporary-auth-failure")]) else handleAuthChecked s g n
  | none => handleAuthChecked s g n

/-- A blocked account name or address: `temporary-auth-failure`, the stage
and the counters unchanged, no password checked. -/
theorem handleAuth_blocked (s : Session) (g : AuthGuard) (n : Node) (u : String)
    (hu : authUser? n = some u) (hb : g.blocked u = true) :
    handleAuth s g n = (s, g, [.send (saslFailure "temporary-auth-failure")]) := by
  simp [handleAuth, hu, hb]

/-- Handle `<response/>` — the SCRAM second step (RFC 5802 section 3). A
proof or nonce that does not verify is a failure of `user`. Every failure ends
the exchange: the next attempt is a new `<auth/>`, with a new nonce. The proof
is checked for a name with no account too, against its decoy keys, and only an
account can succeed. -/
def handleScramResponse (s : Session) (g : AuthGuard) (user nonce cfb sf : String) (n : Node) :
    Session × AuthGuard × List Out :=
  let over := { s with stage := .awaitingAuth }
  match Scram.b64Decode (textOf n) with
  | none => (over, g, [.send (saslFailure "incorrect-encoding")])
  | some bytes =>
    match Sasl.ClientFinalMessage.parse (String.fromUTF8! bytes) with
    | none => (over, g, [.send (saslFailure "malformed-request")])
    | some cfin =>
      -- RFC 5802 section 5.1: the client MUST echo the combined nonce. A
      -- server that skips this check accepts a replayed client-first.
      if cfin.nonce != nonce then (over, g.fail user, [.send (saslFailure "not-authorized")])
      else
        let cred := (s.cfg.credentialOf user).getD (s.cfg.decoyCredential user)
        let auth := Scram.authMessage cfb sf (Scram.clientFinalNoProof cfin)
        match Scram.verifyClientProof cred auth cfin.proof, s.cfg.accountOf user with
        | some serverSig, some _ =>
          ({ s with stage := .authenticated user }, g,
           [.send (saslSuccess (Scram.b64Encode ("v=" ++ serverSig).toUTF8))])
        | _, _ => (over, g.fail user, [.send (saslFailure "not-authorized")])

/-- A success needs an account: decoy keys can never authenticate a name. -/
theorem handleScramResponse_account (s : Session) (g : AuthGuard) (user nonce cfb sf : String) (n : Node)
    (h : s.cfg.accountOf user = none) :
    ∀ u, (handleScramResponse s g user nonce cfb sf n).1.stage ≠ .authenticated u := by
  intro u
  unfold handleScramResponse
  simp only [h]
  repeat' split
  all_goals simp_all

/-- One step of SASL ended back at `<auth/>`: a failed attempt. RFC 6120 section
6.4.5 lets the receiving entity limit retries and close the stream, so the
attempt that reaches `maxAuthFailures` ends with `policy-violation`, whatever
else waits in the buffer. -/
def Session.afterSasl (s : Session) (env : Env) (outs : List Out) : Session × Env × List Out :=
  if s.stage != .awaitingAuth then (s, env, outs)
  else
    let n := s.authFailures + 1
    if n ≥ s.cfg.maxAuthFailures then
      ({ s with stage := .closed, authFailures := n }, env,
       outs ++ streamError "policy-violation" "too many failed logins")
    else ({ s with authFailures := n }, env, outs)

/-- The attempt that reaches the limit closes the stream. -/
theorem afterSasl_closes (s : Session) (env : Env) (outs : List Out)
    (hs : s.stage = .awaitingAuth) (hn : s.authFailures + 1 ≥ s.cfg.maxAuthFailures) :
    (s.afterSasl env outs).1.stage = .closed := by
  simp [Session.afterSasl, hs, hn]

/-- A step that succeeded or that goes on is not counted. -/
theorem afterSasl_other (s : Session) (env : Env) (outs : List Out)
    (hs : s.stage ≠ .awaitingAuth) : s.afterSasl env outs = (s, env, outs) := by
  simp [Session.afterSasl, hs]

/-- May this stanza wait for an account with no bound session? A message (RFC
6121 section 8.5.2.1.1), and a subscription request or answer (section 3.1.3).
Presence that says who is online has no use later, and an error is for a sender
that may be gone. -/
def holdable (st : Stanza) : Bool :=
  match st.kind with
  | .message => st.type != some "error"
  | .presence => ["subscribe", "subscribed", "unsubscribe", "unsubscribed"].contains (st.type.getD "")
  | .iq => false

/-- Is this stanza addressed to the MUC service of this server? -/
def Config.isMuc (c : Config) (st : Stanza) : Bool :=
  match c.mucDomain, st.to with
  | some d, some t => t.domainpart == d
  | _, _ => false

/-- Is this stanza addressed to the MIX service of this server? -/
def Config.isMix (c : Config) (st : Stanza) : Bool :=
  match c.mixDomain, st.to with
  | some d, some t => t.domainpart == d
  | _, _ => false

/-- Is this stanza addressed to the GC3 prototype service of this server? -/
def Config.isGc3 (c : Config) (st : Stanza) : Bool :=
  match c.gc3Domain, st.to with
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
    -- XEP-0405 section 5: MIX-PAM, a join or leave sent to the user's own
    -- server, which acts for the account at the MIX service.
    if s.cfg.mixDomain.isSome &&
       ((childByNs st.payload nsMixPam (some "client-join")).isSome ||
        (childByNs st.payload nsMixPam (some "client-leave")).isSome) then
      (env, [.mix full (render (Core.Stanza.toXml { st with from_ := Jid.parse full }))])
    else
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
        -- RFC 6120 section 8.3.3.18.
        if !env.rosterFits s.cfg.maxRosterItems r' then
          (env, [.send (stanzaError .iq st.id none (some s.cfg.domain) "wait" "resource-constraint")])
        else
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
          (env, [.send (iqResultFrom st
            [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
              ([ .element "identity"
                  [⟨"category", "server"⟩, ⟨"type", "im"⟩, ⟨"name", "Factoidal XMPP"⟩] [],
                .element "feature" [⟨"var", nsRoster⟩] [],
                .element "feature" [⟨"var", nsDiscoInfo⟩] [] ] ++
                (if s.cfg.mixDomain.isSome then [.element "feature" [⟨"var", nsMixPam⟩] []] else []))])])
        | none =>
          match childByNs st.payload nsDiscoItems (some "query") with
          | some _ =>
            -- XEP-0030 items on the server: the MUC service, when there is one,
            -- so a client can find it (XEP-0045 section 6.1).
            (env, [.send (iqResultFrom st
              [.element "query" [⟨"xmlns", nsDiscoItems⟩]
                ((s.cfg.mucDomain.toList ++ s.cfg.mixDomain.toList ++ s.cfg.gc3Domain.toList).map (fun d => .element "item" [⟨"jid", d⟩] []))])])
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
      if !env.rosterFits s.cfg.maxRosterItems r' then (env, [])
      else
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
      if !env.rosterFits s.cfg.maxRosterItems r' then (env, [])
      else
      ({ env with roster := r' },
       [.saveRoster bare (rosterEncode r'), .route t out])
    else (env, [.route t out])

/-! ## Which resource a bind gets (RFC 6120 section 7.7.2.2)

A live session keeps its full JID. A client that asks for a resource a live session holds gets a
server-generated one, and the bind result names it: of the options of section 7.7.2.2, the one that
overrides the client's resource. A resource with no live session is free, whatever session held it
before. -/

/-- The full JID of a resource of this session's account, as `Session.fullJid` gives it once bound. -/
def Session.fullOf (s : Session) (user resource : String) : String :=
  user ++ "@" ++ s.cfg.domain ++ "/" ++ resource

/-- The length of the longest text. -/
def longest (l : List String) : Nat :=
  l.foldr (fun t m => max t.length m) 0

theorem length_le_longest {l : List String} {t : String} (h : t ∈ l) : t.length ≤ longest l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [longest, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A server-generated resource: the stream id. A client can see the stream id of its own second
stream and bind it first, so the id can be held; then it is padded past every full JID in `bound`,
which no held full JID can equal. -/
def Session.generated (s : Session) (bound : List String) (user : String) : String :=
  if bound.contains (s.fullOf user s.cfg.streamId) then
    s.cfg.streamId ++ String.ofList (List.replicate (longest bound + 1) '-')
  else s.cfg.streamId

/-- The resource of a bind: the one the client proposed if it is free, or else a generated one. -/
def Session.resourceFor (s : Session) (bound : List String) (user : String)
    (proposed : Option String) : String :=
  match proposed with
  | some r => if r.isEmpty || bound.contains (s.fullOf user r) then s.generated bound user else r
  | none => s.generated bound user

theorem generated_free (s : Session) (bound : List String) (user : String) :
    s.fullOf user (s.generated bound user) ∉ bound := by
  unfold Session.generated
  split
  · intro hm
    have hl := length_le_longest hm
    simp [Session.fullOf, String.length_append] at hl
    omega
  · rename_i h
    simpa using h

/-- 1. The full JID a bind gets is held by no live session. -/
theorem resourceFor_free (s : Session) (bound : List String) (user : String)
    (proposed : Option String) : s.fullOf user (s.resourceFor bound user proposed) ∉ bound := by
  unfold Session.resourceFor
  split
  · split
    · exact generated_free s bound user
    · rename_i h
      simp only [Bool.or_eq_true, not_or] at h
      simpa using h.2
  · exact generated_free s bound user

/-- 2. A proposed resource that no live session holds is the one the client gets. -/
theorem resourceFor_proposed (s : Session) (bound : List String) (user r : String)
    (hr : r.isEmpty = false) (h : s.fullOf user r ∉ bound) :
    s.resourceFor bound user (some r) = r := by
  simp [Session.resourceFor, hr, h]

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
          let r := handleAuth s env.guard node
          r.1.afterSasl { env with guard := r.2.1 } r.2.2
        else s.afterSasl env [.send (saslFailure "malformed-request")]
      | .awaitingScramResponse user nonce cfb sf =>
        if tag == "response" then
          let r := handleScramResponse s env.guard user nonce cfb sf node
          r.1.afterSasl { env with guard := r.2.1 } r.2.2
        else if tag == "abort" then
          Session.afterSasl { s with stage := .awaitingAuth } env [.send (saslFailure "aborted")]
        else Session.afterSasl { s with stage := .awaitingAuth } env [.send (saslFailure "malformed-request")]
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
            let resource := s.resourceFor env.bound user (proposed.map textOf)
            ({ s with stage := .bound user resource }, env,
             [.send (bindResult (elemAttr node "id") (s.fullOf user resource))])
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
          else if s.cfg.isMix st then
            (s, env, [.mix full (render (Core.Stanza.toXml { st with from_ := Jid.parse full }))])
          else if s.cfg.isGc3 st then
            (s, env, [.gc3 full (render (Core.Stanza.toXml { st with from_ := Jid.parse full }))])
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

/-! ## A step and the full JID of a session -/

theorem fullJid_none (s : Session) (h : ∀ u r, s.stage ≠ .bound u r) : s.fullJid = none := by
  unfold Session.fullJid
  split
  · rename_i hs _
    exact absurd hs (h _ _)
  · rfl

/-- What one step may do to the full JID of a session: nothing, end it, or give a session with none
one that no live session holds. -/
def FullStep (s : Session) (env : Env) (s' : Session) : Prop :=
  s'.fullJid = s.fullJid ∨ s'.fullJid = none ∨
    (s.fullJid = none ∧ ∃ f, s'.fullJid = some f ∧ f ∉ env.bound)

theorem fullStep_same (s : Session) (env : Env) : FullStep s env s := Or.inl rfl

theorem fullStep_none (s s' : Session) (env : Env) (h : ∀ u r, s'.stage ≠ .bound u r) :
    FullStep s env s' := Or.inr (Or.inl (fullJid_none s' h))

theorem handleAuth_notBound (s : Session) (g : AuthGuard) (n : Node)
    (h : s.stage = .awaitingAuth) : ∀ u r, (handleAuth s g n).1.stage ≠ .bound u r := by
  intro u r
  simp only [handleAuth, handleAuthChecked]
  repeat' split
  all_goals simp [h]

theorem handleScramResponse_notBound (s : Session) (g : AuthGuard) (user nonce cfb sf : String)
    (n : Node) : ∀ u r, (handleScramResponse s g user nonce cfb sf n).1.stage ≠ .bound u r := by
  intro u r
  simp only [handleScramResponse]
  repeat' split
  all_goals simp

theorem afterSasl_notBound (s : Session) (env : Env) (outs : List Out)
    (h : ∀ u r, s.stage ≠ .bound u r) : ∀ u r, (s.afterSasl env outs).1.stage ≠ .bound u r := by
  intro u r
  simp only [Session.afterSasl]
  repeat' split
  all_goals simp [h]

theorem stepPreTls_fullStep (s : Session) (env : Env) (u : Framing.Unit) :
    FullStep s env (stepPreTls s env u).1 := by
  unfold stepPreTls
  repeat' split
  all_goals first
    | exact fullStep_same s env
    | (apply fullStep_none; simp)

theorem fullStep_bind (s : Session) (env : Env) (user : String) (p : Option String)
    (h : s.stage = .awaitingBind user) :
    FullStep s env { s with stage := .bound user (s.resourceFor env.bound user p) } := by
  refine Or.inr (Or.inr ⟨fullJid_none s (by simp [h]), s.fullOf user (s.resourceFor env.bound user p), ?_,
    resourceFor_free s env.bound user p⟩)
  simp [Session.fullJid, Session.bareJid, Session.user, Session.fullOf]

/-- 3. One step of `stepMain` keeps to `FullStep`. -/
theorem stepMain_fullStep (s : Session) (env : Env) (u : Framing.Unit) :
    FullStep s env (stepMain s env u).1 := by
  unfold stepMain
  repeat' first | split | dsimp only
  all_goals first
    | exact fullStep_same s env
    | (apply fullStep_none; simp; done)
    | (apply fullStep_none; apply afterSasl_notBound; apply handleAuth_notBound; assumption; done)
    | (apply fullStep_none; apply afterSasl_notBound; apply handleScramResponse_notBound; done)
    | (apply fullStep_none; apply afterSasl_notBound; intro u r; simp [*]; done)
    | (exact fullStep_bind s env _ _ ‹_›)

/-- 4. So does one step of `step`. -/
theorem step_fullStep (s : Session) (env : Env) (u : Framing.Unit) :
    FullStep s env (step s env u).1 := by
  unfold step
  split
  · exact stepPreTls_fullStep s env u
  · exact stepMain_fullStep s env u

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
  let (s, _, outs) := step (Session.init testCfg) { roster := [] }
    (.streamOpen "<stream:stream to='example.com' version='1.0'>")
  s.stage == .awaitingAuth &&
  (sends outs).length == 2 &&
  has ((sends outs)[1]!) "SCRAM-SHA-256"

-- RFC 6120 section 4.9.3.6: a stream for the wrong domain is
-- `host-unknown` and the stream closes.
#guard
  let (s, _, outs) := step (Session.init testCfg) { roster := [] }
    (.streamOpen "<stream:stream to='elsewhere.example' version='1.0'>")
  s.stage == .closed && has (String.join (sends outs)) "host-unknown"

-- SASL PLAIN, RFC 4616: base64 of NUL "juliet" NUL "r0m30" authenticates.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, _) := run (Session.init testCfg) { roster := [] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>" ]
  s.stage == .authenticated "juliet"

-- The wrong password is `not-authorized` and the stage does not advance.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet wrong").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) { roster := [] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>" ]
  s.stage == .awaitingAuth &&
  has (String.join (sends outs)) "not-authorized"

-- An unknown mechanism is refused rather than accepted by default.
#guard
  let (s, _, outs) := run (Session.init testCfg) { roster := [] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='ANONYMOUS'/>" ]
  s.stage == .awaitingAuth &&
  has (String.join (sends outs)) "invalid-mechanism"

-- A roster stops at its cap, and an edit of an item already there still goes through.
#guard
  let s : Session := { cfg := { testCfg with maxRosterItems := 1 }, stage := .bound "juliet" "balcony" }
  let set (j : String) := Framing.Unit.element s!"<iq type='set' id='r'><query xmlns='{nsRoster}'><item jid='{j}'/></query></iq>"
  let (_, e1, _) := step s { roster := [] } (set "a@example.com")
  let (_, e2, o2) := step s e1 (set "b@example.com")
  let (_, e3, o3) := step s e1 (set "a@example.com")
  e1.roster.length == 1 && e2.roster.length == 1 && has (String.join (sends o2)) "resource-constraint" &&
  e3.roster.length == 1 && !has (String.join (sends o3)) "resource-constraint"

-- A roster closed by the rate refuses a write and does not save.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, e, o) := step s { roster := [], rosterOpen := false }
    (.element s!"<iq type='set' id='r'><query xmlns='{nsRoster}'><item jid='a@example.com'/></query></iq>")
  e.roster.isEmpty && has (String.join (sends o)) "resource-constraint" &&
  !o.any (fun x => match x with | .saveRoster .. => true | _ => false)

-- The accounts file: a good file, and what stops the start.
#guard (accountsOfText "# who\n\nalice:a:b\n bob:pw \n").toOption.map (·.1.map (·.password)) == some ["a:b", "pw"]
#guard (accountsOfText "alice").toOption.isNone
#guard (accountsOfText "alice:").toOption.isNone
#guard (accountsOfText ":pw").toOption.isNone
#guard (accountsOfText "alice:a\nalice:b").toOption.isNone
#guard (match accountsOfText "alice:a\nbob" with | .error e => e == "accounts: line 2: no colon" | _ => false)
-- A verifier reads back to the same keys, and has no password.
#guard
  let c := testCfg.decoyCredential "x"
  match accountsOfText ("alice:" ++ verifierText c) with
  | .ok ([a], [(u, k)]) => a.password == "" && u == "alice" && k.storedKey == c.storedKey &&
      k.serverKey == c.serverKey && k.saltB64 == c.saltB64 && k.iterationCount == 4096
  | _ => false
#guard (accountsOfText "alice:SCRAM-SHA-256$0:AA==$AA==:AA==").toOption.isNone
#guard (accountsOfText "alice:SCRAM-SHA-256$oops").toOption.isNone
-- A verifier account has no PLAIN login.
#guard checkPlain { testCfg with accounts := [⟨"alice", ""⟩] } ["", "alice", ""] == none

-- Salts: one per name, the same each time, and a name with no account gets one
-- of the same form.
#guard
  let c := { testCfg with saltSeed := "seed" }
  c.saltFor "juliet" != c.saltFor "romeo" && c.saltFor "juliet" == c.saltFor "juliet" &&
  (c.saltFor "nobody").length == (c.saltFor "juliet").length &&
  ((Scram.b64Decode (c.saltFor "juliet")).map (·.size)) == some 16

-- SCRAM for a name with no account: a challenge, then `not-authorized` at the
-- step where a wrong password gets it. The keys are in `credentials`, so no
-- PBKDF2 runs in this check.
#guard
  let cred : Scram.StoredCredentials := { (testCfg.decoyCredential "juliet") with iterationCount := 4096 }
  let c := { testCfg with saltSeed := "seed", credentials := [("juliet", cred)] }
  let first (u : String) := Scram.b64Encode s!"n,,n={u},r=abc".toUTF8
  let final := Scram.b64Encode "c=biws,r=abcSRVNONCE,p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ=".toUTF8
  let flow (u : String) := run (Session.init c) { roster := [] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='SCRAM-SHA-256'>{first u}</auth>",
      .element s!"<response xmlns='{nsSasl}'>{final}</response>" ]
  let (s1, _, o1) := flow "juliet"
  let (s2, _, o2) := flow "nobody"
  s1.stage == .awaitingAuth && s2.stage == .awaitingAuth &&
  has (String.join (sends o1)) "<challenge" && has (String.join (sends o2)) "<challenge" &&
  has (String.join (sends o2)) "not-authorized" && (sends o1).length == (sends o2).length

-- The address backs off for longer than its short window, and the right
-- password does not pass it: 20 failures over 400 seconds, then still blocked
-- when the short window is over.
#guard
  let g0 : AuthGuard := { address := "10.0.0.1", now := 0 }
  let g1 := (List.range 20).foldl (fun (g : AuthGuard) i =>
    { (AuthGuard.fail { g with now := i * 20 } s!"n{i}") with now := i * 20 }) g0
  { g1 with now := 1000 }.blocked "juliet" && !{ g1 with now := 3700 }.blocked "juliet" &&
  !{ g1 with now := 1000, address := "10.0.0.2" }.blocked "juliet"

-- With the limits off nothing is blocked.
#guard
  let g0 : AuthGuard := { address := "10.0.0.1", limits := { enabled := false } }
  let g1 := (List.range 30).foldl (fun (g : AuthGuard) i => g.fail s!"n{i}") g0
  !g1.blocked "juliet"

-- RFC 6120 section 6.4.6 and section 7: restart, bind, then the full JID
-- comes back in the bind result.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) { roster := [] }
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
  let (s, _, _) := run (Session.init testCfg) { roster := [] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'/></iq>" ]
  s.stage == .bound "juliet" "SID-1"

-- RFC 6120 section 7.7.2.2: a proposed resource that a live session holds is replaced by a generated
-- one, and the result names it. The same name on another account is free.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    ((("\x00juliet\x00r0m30").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) { roster := [], bound := ["juliet@example.com/balcony"] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'><resource>balcony</resource></bind></iq>" ]
  s.stage == .bound "juliet" "SID-1" && has (String.join (sends outs)) "juliet@example.com/SID-1"

#guard
  let payload := Scram.b64Encode (ByteArray.mk
    ((("\x00juliet\x00r0m30").toUTF8).toList.toArray))
  let (s, _, _) := run (Session.init testCfg) { roster := [], bound := ["romeo@example.com/balcony"] }
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'><resource>balcony</resource></bind></iq>" ]
  s.stage == .bound "juliet" "balcony"

-- A stream id that a live session holds is not given out again.
#guard
  let s := Session.init testCfg
  let held := ["juliet@example.com/SID-1"]
  let r := s.resourceFor held "juliet" none
  r != "SID-1" && !held.contains (s.fullOf "juliet" r)

-- RFC 6120 section 6: a stanza sent before authentication is a stream
-- error, not a silently dropped stanza.
#guard
  let (s, _, outs) := step (Session.init testCfg) { roster := [] } (.element "<message to='x'/>")
  s.stage == .closed &&
  has (String.join (sends outs)) "not-well-formed"

-- RFC 6121 section 8.1: a message to another account is routed to that
-- bare JID with a `from` the server stamped, not the one the client
-- claimed.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step s { roster := [] }
    (.element "<message to='romeo@example.com' from='mallory@evil.example' type='chat'><body>hi</body></message>")
  outs.any (fun o => match o with
    | .route t x => t == "romeo@example.com" &&
        has x "from=\"juliet@example.com/balcony\""
    | _ => false)

-- RFC 6121 section 2.1.3: the roster get returns every stored item.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := { roster := [⟨"romeo@example.com", "Romeo", "both", false⟩] }
  let (_, _, outs) := step s env (.element s!"<iq type='get' id='r1'><query xmlns='{nsRoster}'/></iq>")
  has (String.join (sends outs)) "romeo@example.com"

-- RFC 6121 section 2.3: a roster set stores the item, saves the file and
-- pushes the change back.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, env', outs) := step s { roster := [] }
    (.element s!"<iq type='set' id='r2'><query xmlns='{nsRoster}'><item jid='nurse@example.com' name='Nurse'/></query></iq>")
  env'.roster == [⟨"nurse@example.com", "Nurse", "none", false⟩] &&
  outs.any (fun o => match o with
    | .saveRoster b _ => b == "juliet@example.com" | _ => false)

-- RFC 6121 section 2.5: `subscription='remove'` deletes the item.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := { roster := [⟨"romeo@example.com", "Romeo", "both", false⟩] }
  let (_, env', _) := step s env
    (.element s!"<iq type='set' id='r3'><query xmlns='{nsRoster}'><item jid='romeo@example.com' subscription='remove'/></query></iq>")
  env'.roster == []

-- RFC 6121 section 4.4.2: available presence with no `to` goes to every
-- contact with subscription `from` or `both`, and back to the sender.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := { roster := [⟨"romeo@example.com", "", "both", false⟩,
                     ⟨"nurse@example.com", "", "to", false⟩] }
  let (_, _, outs) := step s env (.element "<presence/>")
  (outs.filterMap (fun o => match o with | .route t _ => some t | _ => none))
    == ["romeo@example.com"]

-- RFC 6121 section 3.1.2: a subscription request sets `ask` and is
-- forwarded.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, env', outs) := step s { roster := [] }
    (.element "<presence to='romeo@example.com' type='subscribe'/>")
  env'.roster == [⟨"romeo@example.com", "", "none", true⟩] &&
  outs.any (fun o => match o with | .route t _ => t == "romeo@example.com" | _ => false)

-- RFC 6120 section 8.4: an IQ nobody handles gets `service-unavailable`.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step s { roster := [] }
    (.element "<iq type='get' id='q1'><query xmlns='urn:example:nothing'/></iq>")
  has (String.join (sends outs)) "service-unavailable"

-- RFC 6120 section 4.4: the close is answered with a close and the
-- session ends.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (s', _, outs) := step s { roster := [] } .streamClose
  s'.stage == .closed && outs.contains .close

-- A stanza that arrives for an unbound session is held, not delivered.
#guard deliver (Session.init testCfg) "<message/>" == []
#guard deliver { cfg := testCfg, stage := .bound "juliet" "balcony" } "<message/>"
  == [.send "<message/>"]

-- Nothing at all happens after the stream is closed.
#guard
  let s : Session := { cfg := testCfg, stage := .closed }
  let (_, _, outs) := step s { roster := [] } (.element "<message to='x'/>")
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
  let (s, _, outs) := step (Session.init tlsCfg) { roster := [] } openHdr
  s.stage == .awaitingStartTls &&
  has (String.join (sends outs)) "<starttls xmlns=\"urn:ietf:params:xml:ns:xmpp-tls\"><required/></starttls>" &&
  !has (String.join (sends outs)) "mechanism"

-- RFC 6120 section 5.4.2.3: `<starttls/>` is answered with `<proceed/>`
-- and the host is told to upgrade.
#guard
  let (s, _, outs) := run (Session.init tlsCfg) { roster := [] }
    [openHdr, .element s!"<starttls xmlns='{nsTls}'/>"]
  s.stage == .tlsPending && outs.contains .startTls &&
  has (String.join (sends outs)) "<proceed"

-- SASL in clear when STARTTLS is required: policy-violation, closed, and
-- no SASL answer of any kind.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    ((("\x00juliet\x00r0m30").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init tlsCfg) { roster := [] }
    [openHdr, .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>"]
  s.stage == .closed && s.user == none &&
  has (String.join (sends outs)) "policy-violation" &&
  !has (String.join (sends outs)) "success"

-- `<starttls/>` in a wrong namespace is not STARTTLS.
#guard
  let (s, _, _) := run (Session.init tlsCfg) { roster := [] }
    [openHdr, .element "<starttls xmlns='urn:example:not-tls'/>"]
  s.stage == .closed

-- RFC 6120 section 5.4.3.3: after `<proceed/>`, any unit closes the
-- connection and nothing is sent in clear.
#guard
  let (s, _, outs) := run (Session.init tlsCfg) { roster := [] }
    [openHdr, .element s!"<starttls xmlns='{nsTls}'/>", .element "<message to='x'/>"]
  s.stage == .closed && (sends outs).getLast? == some proceedText

-- The whole sequence: STARTTLS, handshake, a NEW stream offering SASL,
-- PLAIN, restart, bind.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    ((("\x00juliet\x00r0m30").toUTF8).toList.toArray))
  let (s1, _, _) := run (Session.init tlsCfg) { roster := [] }
    [openHdr, .element s!"<starttls xmlns='{nsTls}'/>"]
  match s1.tlsEstablished with
  | none => false
  | some s2 =>
    let (s3, _, outs) := run s2 { roster := [] }
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
  let (_, _, outs) := step (Session.init { tlsCfg with tlsCarrier := true }) { roster := [] } openHdr
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
  let (_, _, outs) := step boundJuliet { roster := [] } (.element "<iq type='get' id='q1' to='romeo@example.com/orchard'><query xmlns='jabber:iq:version'/></iq>")
  match outs with
  | [.routeFull to text (some bounce)] =>
    to == "romeo@example.com/orchard" && has text "from=\"juliet@example.com/balcony\"" &&
    has bounce "service-unavailable" && has bounce "id=\"q1\"" &&
    has bounce "to=\"juliet@example.com/balcony\"" && has bounce "from=\"romeo@example.com/orchard\""
  | _ => false

-- To another resource of the SAME account (issue 1139): routed, not handled here.
#guard
  let (_, _, outs) := step boundJuliet { roster := [] } (.element "<iq type='get' id='q2' to='juliet@example.com/tower'><query xmlns='jabber:iq:version'/></iq>")
  match outs with
  | [.routeFull "juliet@example.com/tower" _ (some _)] => true
  | _ => false

-- An IQ result to a full JID is delivered and never bounced.
#guard
  let (_, _, outs) := step boundJuliet { roster := [] } (.element "<iq type='result' id='q3' to='romeo@example.com/orchard'/>")
  match outs with
  | [.routeFull "romeo@example.com/orchard" _ none] => true
  | _ => false

-- To the bare JID of another account: the server answers for it.
#guard
  let (_, _, outs) := step boundJuliet { roster := [] } (.element "<iq type='get' id='q4' to='romeo@example.com'><query xmlns='jabber:iq:version'/></iq>")
  match outs with
  | [.send t] => has t "service-unavailable" && has t "id=\"q4\""
  | _ => false

-- Roster get to one's own bare JID is still handled locally.
#guard
  let (_, _, outs) := step boundJuliet { roster := [] } (.element s!"<iq type='get' id='q5' to='juliet@example.com'><query xmlns='{nsRoster}'/></iq>")
  match outs with
  | [.send t] => has t "type=\"result\""
  | _ => false

/-! ### MUC hand-off checks (2026-11-03) -/

private def boundMuc : Session :=
  { Session.init { testCfg with mucDomain := some "conference.example.com" } with stage := .bound "juliet" "balcony" }

-- A stanza to the MUC domain goes to the room service, with the SESSION's
-- full JID as sender, whatever `from` the client claimed.
#guard
  let (_, _, outs) := step boundMuc { roster := [] } (.element "<presence to='tea@conference.example.com/jul' from='mallory@evil.example/x'/>")
  match outs with
  | [.muc "juliet@example.com/balcony" text] => has text "from=\"juliet@example.com/balcony\"" && !has text "mallory"
  | _ => false

-- No MUC configured: the same stanza is routed as before, not handed off.
#guard
  let (_, _, outs) := step boundJuliet { roster := [] } (.element "<message to='tea@conference.example.com' type='groupchat'><body>x</body></message>")
  outs.all (fun o => match o with | .muc .. => false | _ => true)

-- disco#items on the server names the MUC service.
#guard
  let (_, _, outs) := step boundMuc { roster := [] } (.element "<iq type='get' id='d1' to='example.com'><query xmlns='http://jabber.org/protocol/disco#items'/></iq>")
  match outs with
  | [.send t] => has t "jid=\"conference.example.com\"" && has t "from=\"example.com\""
  | _ => false

-- disco#info on the server says who answers.
#guard
  let (_, _, outs) := step boundMuc { roster := [] } (.element "<iq type='get' id='d2' to='example.com'><query xmlns='http://jabber.org/protocol/disco#info'/></iq>")
  match outs with
  | [.send t] => has t "from=\"example.com\"" && has t "Factoidal XMPP"
  | _ => false

/-! ### MIX hand-off checks (2026-11-03) -/

private def boundMix : Session :=
  { Session.init { testCfg with mixDomain := some "mix.example.com" } with stage := .bound "juliet" "balcony" }

-- MIX-PAM: a client-join to one's own bare JID goes to the MIX service, sender from the session.
#guard
  let (_, _, outs) := step boundMix { roster := [] } (.element "<iq type='set' id='j1' to='juliet@example.com' from='mallory@evil.example/x'><client-join xmlns='urn:xmpp:mix:pam:2' channel='coven@mix.example.com'><join xmlns='urn:xmpp:mix:core:1'/></client-join></iq>")
  match outs with
  | [.mix "juliet@example.com/balcony" text] => has text "client-join" && !has text "mallory"
  | _ => false

-- Without MIX the same IQ is handled locally (service-unavailable), not handed off.
#guard
  let (_, _, outs) := step boundJuliet { roster := [] } (.element "<iq type='set' id='j2' to='juliet@example.com'><client-join xmlns='urn:xmpp:mix:pam:2' channel='coven@mix.example.com'/></iq>")
  match outs with
  | [.send t] => has t "service-unavailable"
  | _ => false

-- A channel message goes to the MIX service; the server's disco#info offers MIX-PAM.
#guard
  let (_, _, a) := step boundMix { roster := [] } (.element "<message to='coven@mix.example.com' type='groupchat'><body>x</body></message>")
  let (_, _, b) := step boundMix { roster := [] } (.element "<iq type='get' id='d3' to='juliet@example.com'><query xmlns='http://jabber.org/protocol/disco#info'/></iq>")
  (match a with | [.mix _ _] => true | _ => false) &&
  (match b with | [.send t] => has t "urn:xmpp:mix:pam:2" | _ => false)

-- GC3: a stanza to the prototype service is handed off, sender from the session.
#guard
  let b : Session := { Session.init { testCfg with gc3Domain := some "gc3.example.com" } with stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step b { roster := [] } (.element "<iq type='set' id='g1' to='tea@gc3.example.com'><join xmlns='urn:xmpp:gc3:prototype:0' nick='jul'/></iq>")
  match outs with
  | [.gc3 "juliet@example.com/balcony" _] => true
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
  generalize childByNs st.payload nsMixPam (some "client-join") = pj
  generalize childByNs st.payload nsMixPam (some "client-leave") = pl
  cases tgt <;> cases r <;> cases se <;> cases di <;> cases dit <;> cases pj <;> cases pl <;> simp only [] <;>
    simp [apply_ite (f := Prod.snd), apply_ite (f := fun l : List Out => Out.route b t ∈ l)]

-- The failed SASL login limit (https://github.com/danbri/factoidal/issues/1128).
private def plainAuth (user pw : String) : Framing.Unit :=
  let payload := Scram.b64Encode ((String.singleton (Char.ofNat 0) ++ user ++ String.singleton (Char.ofNat 0) ++ pw).toUTF8)
  .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>"

private def openUnit : Framing.Unit := .streamOpen "<stream:stream to='example.com' version='1.0'>"

private def guard0 : AuthGuard := { now := 100, address := "192.0.2.7" }

/-- For the checks of the limit, which make more attempts on one stream than a
stream allows. -/
private def manyTries : Config := { testCfg with maxAuthFailures := 100 }

-- RFC 6120 section 6.4.5: the third failed attempt on a stream closes it, and
-- a fourth in the same read is not looked at.
#guard
  let (s, _, outs) := run (Session.init testCfg) { roster := [] }
    (openUnit :: (List.replicate 4 (plainAuth "juliet" "wrong")))
  s.stage == .closed && (sends outs).length == 7 && has (String.join (sends outs)) "policy-violation"

-- Two failed attempts, then the right password: the stream stays open.
#guard
  let (s, _, _) := run (Session.init testCfg) { roster := [] }
    [openUnit, plainAuth "juliet" "wrong", plainAuth "juliet" "wrong", plainAuth "juliet" "r0m30"]
  s.stage == .authenticated "juliet"

-- Five wrong passwords on one stream are `not-authorized`; the sixth attempt
-- is `temporary-auth-failure`, also with the right password.
#guard
  let (s, env, outs) := run (Session.init manyTries) { roster := [], guard := guard0 }
    (openUnit :: (List.replicate 5 (plainAuth "juliet" "wrong")))
  let (s2, _, outs2) := step s env (plainAuth "juliet" "r0m30")
  s.stage == .awaitingAuth && ((sends outs).filter (has · "not-authorized")).length == 5 &&
  s2.stage == .awaitingAuth && has (String.join (sends outs2)) "temporary-auth-failure"

-- New streams from one address: the counters are the server's, so the sixth
-- stream's attempt is refused, for another account name too.
#guard
  let g := (List.range 5).foldl (fun g _ =>
    (run (Session.init manyTries) { roster := [], guard := g } [openUnit, plainAuth "juliet" "wrong"]).2.1.guard) guard0
  let (s2, _, outs2) := run (Session.init manyTries) { roster := [], guard := g } [openUnit, plainAuth "romeo" "juli3t"]
  s2.stage == .awaitingAuth && has (String.join (sends outs2)) "temporary-auth-failure"

-- ... but from another address, another account logs in.
#guard
  let g := (List.range 5).foldl (fun g _ =>
    (run (Session.init manyTries) { roster := [], guard := g } [openUnit, plainAuth "juliet" "wrong"]).2.1.guard) guard0
  let (s2, _, _) := run (Session.init manyTries) { roster := [], guard := { g with address := "198.51.100.9" } }
    [openUnit, plainAuth "romeo" "juli3t"]
  s2.stage == .authenticated "romeo"

-- After the window (60 s of the host's clock) the account logs in again.
#guard
  let (_, env, _) := run (Session.init manyTries) { roster := [], guard := guard0 }
    (openUnit :: (List.replicate 5 (plainAuth "juliet" "wrong")))
  let (s2, _, _) := run (Session.init testCfg) { env with guard := { env.guard with now := 160 } }
    [openUnit, plainAuth "juliet" "r0m30"]
  s2.stage == .authenticated "juliet"

-- A name with no account counts the same way; a malformed payload does not.
#guard
  let (_, env, _) := run (Session.init manyTries) { roster := [], guard := guard0 }
    (openUnit :: (List.replicate 5 (plainAuth "nobody" "x")))
  (env.guard.failures.counters.map (·.key)) == #["account:nobody", "address:192.0.2.7"]
#guard
  let (_, env, _) := run (Session.init manyTries) { roster := [], guard := guard0 }
    [openUnit, .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>***</auth>"]
  env.guard.failures.counters.isEmpty

-- No address: only the account key; never an empty key.
#guard
  let (_, env, _) := run (Session.init manyTries) { roster := [], guard := { guard0 with address := "" } }
    [openUnit, plainAuth "juliet" "wrong"]
  (env.guard.failures.counters.map (·.key)) == #["account:juliet"]

-- Disabled: eight failures, then the right password logs in; the warning.
#guard
  let gOff : AuthGuard := { guard0 with limits := { enabled := false } }
  let (s, env, _) := run (Session.init manyTries) { roster := [], guard := gOff }
    (openUnit :: (List.replicate 8 (plainAuth "juliet" "wrong")))
  let (s2, _, _) := step s env (plainAuth "juliet" "r0m30")
  s.stage == .awaitingAuth && s2.stage == .authenticated "juliet"
#guard (saslLimitWarnings { enabled := false }).length == 1 && (saslLimitWarnings {}).isEmpty

end L4Factoidal.XMPP.Server