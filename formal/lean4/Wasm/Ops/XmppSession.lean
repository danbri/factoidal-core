/-
Wasm.Ops.XmppSession — the XMPP SERVER as handles: open a server, open
one session per client connection on it, feed the session the bytes a
socket read, perform what it answers.

  xmppOpen(configJson)          (configJson may hold "disableRateLimits":true)
    -> {"ok":true,"handle":"xmpp1","domain":"…","accounts":N,"warnings":[…]}
  xmppSessionOpen(serverHandle, optionsJson)
    -> {"ok":true,"handle":"xmpps1"}
  xmppSessionFeed(sessionHandle, text)
    -> {"ok":true,"send":[…],"route":[{"to":bare,"text":…},…],
        "presence":[{"bare","full","available"},…],
        "rostersSaved":[bare,…],"close":bool,
        "stage":"…","bare":s|null,"full":s|null,"bufferedBytes":N}
  xmppSessionDeliver(sessionHandle, text)
    -> {"ok":true,"delivered":bool,"send":[…]}
  xmppSessionClose(sessionHandle)
    -> {"ok":true,"send":[…]}
  xmppRosterGet(serverHandle, bareJid)
    -> {"ok":true,"encoded":"…","items":[{"jid","name","subscription","ask"},…]}
  xmppRosterSet(serverHandle, bareJid, encoded)
    -> {"ok":true}
  xmppClock(serverHandle, seconds)
    -> {"ok":true}
  xmppVerifier(username, password, saltB64, iterations)
    -> {"ok":true,"line":"…"}
  xmppClose(serverHandle)
    -> {"ok":true,"sessions":N}

This module is to `Harness/XmppServe.lean` what `Wasm/Ops/Lws.lean` is to
`npm/factoidal/lws/server.mjs`: the same protocol library behind a handle
table instead of behind a process. Every protocol decision is still
`L4Factoidal.XMPP.Server.step` (and `deliver`, `streamError`,
`Session.awaitingStreamOpen`, `Session.canDeliver`); every cut of the
byte stream is still `L4Factoidal.XMPP.Framing.nextUnit`. What the
native harness does with files — the roster of a bare JID, who is
available, the mailbox a stanza is routed to — is here held in the
server handle or handed back to the host:

  * `Out.saveRoster` updates the server handle's roster table, so a
    second session on the same server reads what the first wrote, as
    the harness reads the roster file fresh before every `step`.
  * `Out.presence` updates the server handle's presence table and is
    also reported, so a host that keeps its own view can.
  * `Out.route` is REPORTED, not performed: the host owns the sockets,
    so the host finds the session bound to that bare JID and calls
    `xmppSessionDeliver` on it, or holds the stanza until one binds.
    `xmppSessionDeliver` asks `Session.canDeliver` before anything else,
    which is the gate the harness learned to ask first (see the design
    record's "two defects").
  * `Out.send` and `Out.close` are reported as `send` and `close`.

What the host supplies and this module never invents: the stream id and
the SCRAM server nonce of each session (RFC 6120 section 4.7.3 and
RFC 5802 section 5.1 want them unpredictable; the module has no random
source), the account list, `saltSeed` (`Config.saltFor`: one salt per name),
and the bytes. With no `saltSeed`, every name has `saltB64`, the harness's
one-salt limitation, kept for a transcript that must replay.

State lives HERE, in `Wasm/*`, in `IO.Ref`s, exactly as `Wasm/Ops/Lws.lean`
holds a storage; `L4Factoidal/XMPP/` stays pure. Reachable only through
`L4Wasm.callIO`.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import L4Factoidal.XMPP.Server
import L4Factoidal.XMPP.WebSocket
import L4Factoidal.XMPP.Muc
import L4Factoidal.XMPP.Mix
import L4Factoidal.XMPP.Gc3
import L4Factoidal.XMPP.Held
import L4Factoidal.XMPP.StateCodec
import L4Factoidal.HTTP.WebSocket
import L4Factoidal.HTTP.Wire
import L4Factoidal.Net.LoginLimit

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XMPP
open L4Factoidal.XMPP.Server (Session Env Out Config Account Roster RosterItem
  rosterDecode rosterEncode)

/-! ## Reading the JSON contract -/

private def jsonOfOptString (o : Option String) : Json :=
  o.elim .null .string

private def natField? (j : Json) (key : String) : Option Nat :=
  match j.field? key with
  | some (.number s) => s.toNat?
  | _ => none

/-- `accounts`: an array of `{"username","password"}` objects. An entry with no
name or no password is an error: it must not become an account. -/
private def accountsOfArray (items : List Json) : Except String (List Account) :=
  items.mapM (fun it =>
    match it.getString? "username", it.getString? "password" with
    | some u, some p => if u.isEmpty || p.isEmpty then .error "accounts: an entry has no name or no password" else .ok ⟨u, p⟩
    | _, _ => .error "accounts: an entry has no name or no password")

/-- `mucMembers`: an array of `{"room","members":[bare JID]}` objects. `none` when
an entry is malformed: a room whose list was lost would be open to everyone. -/
private def mucMembersOfArray (items : List Json) : Option (List Muc.MemberList) :=
  items.mapM (fun it =>
    match it.getString? "room", it.getArray? "members" with
    | some room, some members =>
      if room.isEmpty then none
      else (members.mapM (fun m => match m with | Json.string s => some s | _ => none)).map (Muc.MemberList.mk room)
    | _, _ => none)

/-- `mucOwners`: an array of `{"room","owners":[bare JID]}` objects; the room `*` means every room.
`none` when an entry is malformed, or a name is not a bare JID: an owner list that lost a name would
leave a room with no owner, and the server would say nothing. -/
private def mucOwnersOfArray (items : List Json) : Option (List Muc.MemberList) :=
  items.mapM (fun it =>
    match it.getString? "room", it.getArray? "owners" with
    | some room, some owners =>
      if room.isEmpty then none
      else (owners.mapM (fun m => match m with
        | Json.string s =>
          match Jid.parse s with
          | some ⟨some _, _, none⟩ => some (Muc.keyOf s)
          | _ => none
        | _ => none)).map (Muc.MemberList.mk room)
    | _, _ => none)

/-- `mucReservedNicks`: an array of `{"nick","jid"}` objects. `none` when an entry is malformed. -/
private def mucReservedOfArray (items : List Json) : Option (List (String × String)) :=
  items.mapM (fun it =>
    match it.getString? "nick", it.getString? "jid" with
    | some n, some b => if n.isEmpty || b.isEmpty then none else some (Muc.nickKey n, b)
    | _, _ => none)

/-- The server configuration: every per-session value (`streamId`,
`serverNonce`) is left empty here and filled by `xmppSessionOpen`. -/
structure XmppServerConfig where
  domain : String
  saltB64 : String
  iterationCount : Nat
  accounts : List Account
  tlsCarrier : Bool
  /-- XEP-0045 room service domain, from `"mucDomain"`; none: no MUC. -/
  mucDomain : Option String := none
  /-- Members-only rooms, from `"mucMembers"`. -/
  mucMembers : List Muc.MemberList := []
  /-- Owners, from `"mucOwners"`. `none`: no owner configuration, so the first occupant of a room
  is its owner. `some`, also an empty list: nobody becomes an owner by being first. -/
  mucOwners : Option (List Muc.MemberList) := none
  /-- From the host's random source: the key of the XEP-0421 occupant ids, from `"occupantSeed"`. -/
  occupantSeed : String := ""
  /-- Reserved room nicks, from `"mucReservedNicks"`: (`Muc.nickKey` of the nick, bare JID). -/
  mucReserved : List (String × String) := []
  /-- XEP-0369 MIX service domain, from `"mixDomain"`; none: no MIX. -/
  mixDomain : Option String := none
  /-- GC3 prototype service domain, from `"gc3Domain"`; none: no GC3. -/
  gc3Domain : Option String := none
  /-- Does the host keep this server's state across restarts (`"persist": true`,
  set with a state key)? Only then does a feed answer carry `store`/`unstore`. -/
  persist : Bool := false
  /-- The failed SASL login limit (on unless `disableRateLimits`). -/
  limits : L4Factoidal.Net.LoginLimit.Limits := {}
  /-- The keys of the accounts file's verifier lines. -/
  verifiers : List (String × Scram.StoredCredentials) := []
  /-- From the host's random source (`Config.saltSeed`), from `"saltSeed"`. -/
  saltSeed : String := ""
  /-- The accounts' SCRAM keys, derived by `xmppOpen` (`Config.credentials`). -/
  credentials : List (String × Scram.StoredCredentials) := []
  /-- The caps of the stanzas held for offline accounts, from `"heldLimits"`. -/
  heldCaps : Held.Caps := {}
  /-- How many stanzas one account may have held in one window (on unless
  `disableRateLimits`), from `"heldLimits"`. -/
  senderLimits : L4Factoidal.Net.LoginLimit.Limits := { maxFailures := 60, window := 60 }
  deriving Inhabited

/-- The SCRAM iteration count of a server that names none. RFC 7677 section 4 says at least 4096;
each account pays it once, when the server opens. -/
def defaultIterations : Nat := 10000

/-- `heldLimits`: any of `perAccount`, `perAccountBytes`, `total`, `totalBytes`, `senderPerWindow`
and `senderWindow`, each a number; what is absent keeps its default. -/
private def heldLimitsOf (j : Json) (disabled : Bool) :
    Held.Caps × L4Factoidal.Net.LoginLimit.Limits :=
  let l := (j.field? "heldLimits").getD (.object [])
  let d : Held.Caps := {}
  let r : L4Factoidal.Net.LoginLimit.Limits := { maxFailures := 60, window := 60 }
  ({ perAccount := (natField? l "perAccount").getD d.perAccount
     perAccountBytes := (natField? l "perAccountBytes").getD d.perAccountBytes
     total := (natField? l "total").getD d.total
     totalBytes := (natField? l "totalBytes").getD d.totalBytes },
   { r with enabled := !disabled
            maxFailures := (natField? l "senderPerWindow").getD r.maxFailures
            window := (natField? l "senderWindow").getD r.window })

def xmppServerConfigOfJson (text : String) : Except String XmppServerConfig :=
  match parseJson text with
  | .error e => .error s!"config: {toString e}"
  | .ok j =>
    let domain := (j.getString? "domain").getD "localhost"
    if domain.isEmpty then .error "config: \"domain\" must not be empty"
    else
      match accountsOfArray ((j.getArray? "accounts").getD []),
            Server.accountsOfText ((j.getString? "accountsText").getD "") with
      | .error e, _ | _, .error e => .error e
      | .ok fromArray, .ok (fromText, verifiers) =>
      let accounts := fromArray ++ fromText
      -- RFC 5802 section 5.1 salt and RFC 7677 section 3 iteration count.
      -- The default salt is the one `Harness/XmppServe.lean` fixes per
      -- deployment, so a transcript recorded against the harness replays
      -- here byte for byte.
      let saltB64 := (j.getString? "saltB64").getD "W22ZaJ0SNY7soEsUEjb6gQ=="
      let iterationCount := (natField? j "iterationCount").getD defaultIterations
      let mucDomain := j.getString? "mucDomain"
      let mixDomain := j.getString? "mixDomain"
      let gc3Domain := j.getString? "gc3Domain"
      let mucMembers := (j.getArray? "mucMembers").map mucMembersOfArray
      let mucReserved := (j.getArray? "mucReservedNicks").map mucReservedOfArray
      let mucOwners := (j.getArray? "mucOwners").map mucOwnersOfArray
      if mucMembers == some none then .error "config: \"mucMembers\" needs {\"room\",\"members\"} objects"
      else if mucOwners == some none then .error "config: \"mucOwners\" needs {\"room\",\"owners\"} objects, and each owner a bare JID"
      else if mucReserved == some none then .error "config: \"mucReservedNicks\" needs {\"nick\",\"jid\"} objects"
      else if iterationCount < 1 then .error "config: \"iterationCount\" must be at least 1"
      else if mucDomain == some "" || mucDomain == some domain then
        .error "config: \"mucDomain\" must be a domain other than \"domain\""
      else if mixDomain == some "" || mixDomain == some domain || (mixDomain.isSome && mixDomain == mucDomain) then
        .error "config: \"mixDomain\" must be a domain other than \"domain\" and \"mucDomain\""
      else if gc3Domain == some "" || gc3Domain == some domain ||
          (gc3Domain.isSome && (gc3Domain == mucDomain || gc3Domain == mixDomain)) then
        .error "config: \"gc3Domain\" must be a domain of its own"
      else
        let disabled := (j.getBool? "disableRateLimits").getD false
        let (heldCaps, senderLimits) := heldLimitsOf j disabled
        .ok { domain, saltB64, iterationCount, accounts, heldCaps, senderLimits, verifiers,
              saltSeed := (j.getString? "saltSeed").getD "",
              occupantSeed := (j.getString? "occupantSeed").getD "",
              tlsCarrier := (j.getBool? "tlsCarrier").getD false, mucDomain, mixDomain, gc3Domain,
              mucMembers := (mucMembers.bind id).getD [],
              mucOwners := mucOwners.bind id,
              mucReserved := (mucReserved.bind id).getD [],
              persist := (j.getBool? "persist").getD false,
              limits := if disabled then { enabled := false } else {} }

-- A member list reaches the config; a malformed one stops the start.
#guard
  match xmppServerConfigOfJson "{\"mucDomain\":\"c.example.com\",\"mucMembers\":[{\"room\":\"bus\",\"members\":[\"a@example.com\"]}]}" with
  | .ok c => c.mucMembers == [⟨"bus", ["a@example.com"]⟩]
  | .error _ => false
#guard
  match xmppServerConfigOfJson "{\"mucDomain\":\"c.example.com\",\"mucMembers\":[{\"room\":\"bus\"}]}" with
  | .ok _ => false
  | .error _ => true

-- An owner list reaches the config; a name that is not a bare JID stops the start.
#guard
  match xmppServerConfigOfJson "{\"mucOwners\":[{\"room\":\"*\",\"owners\":[\"Me@example.com\"]}]}" with
  | .ok c => c.mucOwners == some [⟨"*", ["me@example.com"]⟩]
  | .error _ => false
#guard
  match xmppServerConfigOfJson "{\"mucOwners\":[{\"room\":\"*\",\"owners\":[\"me\"]}]}" with
  | .ok _ => false
  | .error _ => true
#guard
  match xmppServerConfigOfJson "{\"mucOwners\":[]}", xmppServerConfigOfJson "{}" with
  | .ok a, .ok b => a.mucOwners == some [] && b.mucOwners == none
  | _, _ => false

/-! ## The handle tables -/

/-- One open server: its configuration, and the two things the native
harness keeps as files — the roster of each bare JID and the full JIDs
currently available under each bare JID. -/
structure XmppOpenServer where
  cfg : XmppServerConfig
  rosters : Std.HashMap String Roster
  presence : Std.HashMap String (List String)
  /-- The XEP-0045 rooms, when `cfg.mucDomain` is set. -/
  muc : Option Muc.Service := none
  /-- The XEP-0369 channels, when `cfg.mixDomain` is set. -/
  mix : Option Mix.Service := none
  /-- The GC3 prototype groups, when `cfg.gc3Domain` is set. -/
  gc3 : Option Gc3.Service := none
  /-- The full JIDs of this server's live sessions, each once (`Unique`), kept by the ops layer
  (`bindTransition`, `sessionGone`), so a bind can choose a free resource and the hold-or-deliver
  decision is made here, not in the host. -/
  bound : List String := []
  /-- Stanzas held for accounts with no bound session (`XMPP/Held.lean`). -/
  held : Held.Held := {}
  /-- The counters of the failed SASL login limit, shared by every session
  of this server (https://github.com/danbri/factoidal/issues/1128). -/
  failures : L4Factoidal.Net.LoginLimit.Failures := {}
  /-- The counters of the slower limit of a client address. -/
  backoff : L4Factoidal.Net.LoginLimit.Failures := {}
  /-- The counters of the sender rate on held stanzas (`Held.admit`). -/
  senders : L4Factoidal.Net.LoginLimit.Failures := {}
  /-- The host's clock, in seconds: the latest `now` of `xmppSessionOpen` or
  `xmppClock`. -/
  now : Nat := 0

/-- One open client connection on a server. -/
structure XmppOpenSession where
  server : String
  session : Session
  /-- Bytes received and not yet cut into a complete unit. -/
  buffer : String
  /-- Top-level units processed, against `maxUnits`. -/
  units : Nat
  /-- See `Harness.XmppServe.Options.maxUnits`: exceeding it is
  RFC 6120 section 4.9.3.14 `policy-violation`, a stated refusal rather
  than an unbounded loop. -/
  maxUnits : Nat
  closed : Bool
  /-- The client's address as the socket gives it (`remoteAddress`). -/
  address : String := ""

/-- The full JID this session holds: its bound one, while its stream is open. A session whose stream
has ended holds nothing, even before the host closes its handle. -/
def XmppOpenSession.liveFull (os : XmppOpenSession) : Option String :=
  if os.closed then none else os.session.fullJid

initialize xmppServerCounter : IO.Ref Nat ← IO.mkRef 0
initialize xmppSessionCounter : IO.Ref Nat ← IO.mkRef 0
initialize xmppServers : IO.Ref (Std.HashMap String XmppOpenServer) ← IO.mkRef ∅
initialize xmppSessions : IO.Ref (Std.HashMap String XmppOpenSession) ← IO.mkRef ∅

/-- Is this bare JID an account of this server? -/
def XmppServerConfig.isAccountBare (c : XmppServerConfig) (bare : String) : Bool :=
  c.accounts.any (fun a => a.username ++ "@" ++ c.domain == bare)

/-- The configuration of one session of a server. -/
def XmppOpenServer.sessionConfig (srv : XmppOpenServer) (streamId nonce : String)
    (tlsCarrier startTls : Bool) : Config :=
  { domain := srv.cfg.domain, streamId, serverNonce := nonce
    saltB64 := srv.cfg.saltB64, iterationCount := srv.cfg.iterationCount
    accounts := srv.cfg.accounts, tlsCarrier, startTls
    mucDomain := srv.cfg.mucDomain, mixDomain := srv.cfg.mixDomain, gc3Domain := srv.cfg.gc3Domain
    saltSeed := srv.cfg.saltSeed, credentials := srv.cfg.credentials }

/-- The login limit as a session sees it: the server's counters and clock, the
session's address. -/
def XmppOpenServer.guardFor (srv : XmppOpenServer) (os : XmppOpenSession) : Server.AuthGuard :=
  { limits := srv.cfg.limits, failures := srv.failures, backoff := srv.backoff
    now := srv.now, address := os.address }

def unknownXmppServer (h : String) : String :=
  errJson s!"unknown XMPP server handle: {h}"

def unknownXmppSession (h : String) : String :=
  errJson s!"unknown XMPP session handle: {h}"

/-! ## Performing `Out` actions

What the harness does to a file or a socket, this does to the server
handle or to the answer document. -/

/-- The host-facing result of one feed. -/
structure XmppCollected where
  send : List String := []
  route : List (String × String) := []
  /-- `Out.routeFull`: (full JID, text, bounce). Deliver to that one bound
  session now; if there is none, deliver the bounce (when present) to the
  session this answer is for. Never held. -/
  routeFull : List (String × String × Option String) := []
  presence : List (String × String × Bool) := []
  /-- Bare JIDs whose roster `Out.saveRoster` replaced during this feed, so
  a host that persists rosters knows which to fetch with `xmppRosterGet`. -/
  rostersSaved : List String := []
  close : Bool := false
  /-- State to keep across a restart (issue 1237): (path, text) pairs to write
  to the server's LWS state storage, and paths to delete, in order. Paths and
  texts are `XMPP/StateCodec.lean`'s; the host only performs them. -/
  store : List (String × String) := []
  unstore : List String := []
  /-- `Out.startTls`: flush `send`, then start the TLS handshake as the
  server and call `xmppSessionTlsUp` when it finishes. -/
  startTls : Bool := false

/-- The rate key of an account's roster writes; `senderLimits` is their rate. -/
private def rosterKeys (bare : String) : List String := ["roster:" ++ bare]

/-- May this account's roster be written now? -/
private def rosterOpen (srv : XmppOpenServer) (bare : Option String) : Bool :=
  match bare with
  | some b => (srv.senders.check srv.cfg.senderLimits srv.now (rosterKeys b)).isNone
  | none => true

/-- Hold a stanza for an account with no bound session (RFC 6121 section 8.5.2.1.1), within the
caps and, for a stanza a session sent, the sender's rate. Held, it is one new item of the kept
state. A stanza that may not wait (`Server.holdable`) is dropped. A message to a name with no
account is answered `service-unavailable` (RFC 6121 section 8.5.2.2.1), and one past a limit
`resource-constraint` (RFC 6120 section 8.3.3.18); anything else is dropped, as a stanza of a
service (no `sender`) is. -/
private def holdStanza (srv : XmppOpenServer) (c : XmppCollected) (sender : Option String)
    (bare text : String) : XmppOpenServer × XmppCollected :=
  let st? := (Wire.parseElement text).bind Core.Stanza.ofXml
  if sender.isSome && !(st?.map Server.holdable).getD false && srv.cfg.isAccountBare bare then (srv, c)
  else
  let (h', senders', v) := Held.admit srv.held srv.cfg.senderLimits srv.senders srv.now
    (srv.cfg.isAccountBare bare) sender bare text
  let srv' := { srv with held := h', senders := senders' }
  let refuse (errType cond : String) : XmppOpenServer × XmppCollected :=
    match sender, st? with
    | some _, some st =>
      if st.kind == .message && st.type != some "error" then
        (srv', { c with send := c.send ++ [Server.stanzaError .message st.id
          (st.from_.map Jid.render) (some bare) errType cond] })
      else (srv', c)
    | _, _ => (srv', c)
  match v with
  | .held seq =>
    (srv', { c with store := c.store ++ (if srv.cfg.persist then
      [(StateCodec.heldItemPath bare seq, StateCodec.encodeHeld [text])] else []) })
  | .noAccount => refuse "cancel" "service-unavailable"
  | .tooFast | .full => refuse "wait" "resource-constraint"

/-- Hand a stanza to the host for a bound account, or hold it. -/
private def routeOrHold (srv : XmppOpenServer) (c : XmppCollected) (sender : Option String)
    (bare text : String) : XmppOpenServer × XmppCollected :=
  if srv.bound.any (fun f => Server.bareOf f == bare) then
    (srv, { c with route := c.route ++ [(bare, text)] })
  else holdStanza srv c sender bare text

/-- A service's stanzas to accounts: delivered or held, with no sender rate. -/
private def routeHeldAll (srv : XmppOpenServer) (c : XmppCollected) (ds : List (String × String)) :
    XmppOpenServer × XmppCollected :=
  ds.foldl (fun acc d => routeOrHold acc.1 acc.2 none d.1 d.2) (srv, c)

/-- `sender`: the bare JID of the session the actions are for. -/
private def perform (sender : Option String) (srv : XmppOpenServer) (c : XmppCollected) :
    Out → XmppOpenServer × XmppCollected
  | .send text => (srv, { c with send := c.send ++ [text] })
  | .route bare text => routeOrHold srv c sender bare text
  | .routeFull full text bounce => (srv, { c with routeFull := c.routeFull ++ [(full, text, bounce)] })
  | .muc fromFull text =>
    -- The room service: one step over the server's shared rooms; every
    -- delivery goes to one occupant's own full JID and is never held.
    match srv.muc, (Wire.parseElement text).bind Core.Stanza.ofXml with
    | some svc, some st =>
      let (svc', ds) := Muc.step svc fromFull st
      -- Only a server with an owner configuration keeps affiliations: without one they go
      -- with the room, so they do not outlive a restart either.
      let keep := srv.cfg.persist && !svc.firstOwner
      let changed := svc'.acls.filter (fun a => svc.acl? a.room != some a)
      let gone := svc.acls.filter (fun a => (svc'.acl? a.room).isNone)
      ({ srv with muc := some svc' },
       { c with routeFull := c.routeFull ++ ds.map (fun d => (d.to, d.render, none)),
                store := c.store ++ (if keep then changed.map (fun a => (StateCodec.pathOf "muc" a.room, StateCodec.encodeAcl a)) else []),
                unstore := c.unstore ++ (if keep then gone.map (fun a => StateCodec.pathOf "muc" a.room) else []) })
    | _, _ => (srv, c)
  | .mix fromFull text =>
    -- MIX: a channel message to an account may be held (`route`); an IQ
    -- answer goes to the one session that asked (`routeFull`).
    match srv.mix, (Wire.parseElement text).bind Core.Stanza.ofXml with
    | some svc, some st =>
      let (svc', ds) := Mix.step svc fromFull st
      let changed := svc'.channels.filter (fun ch => svc.channel? ch.name != some ch)
      let gone := svc.channels.filter (fun ch => (svc'.channel? ch.name).isNone)
      routeHeldAll { srv with mix := some svc' }
        { c with routeFull := c.routeFull ++ (ds.filter (!·.held)).map (fun d => (d.to, d.render, none)),
                 store := c.store ++ (if srv.cfg.persist then changed.map (fun ch => (StateCodec.pathOf "mix" ch.name, StateCodec.encodeChannel ch)) else []),
                 unstore := c.unstore ++ (if srv.cfg.persist then gone.map (fun ch => StateCodec.pathOf "mix" ch.name) else []) }
        ((ds.filter (·.held)).map (fun d => (d.to, d.render)))
    | _, _ => (srv, c)
  | .gc3 fromFull text =>
    -- GC3 prototype: membership is the account's, so group traffic to a member
    -- may be held (`route`); an IQ answer goes to the asking session.
    match srv.gc3, (Wire.parseElement text).bind Core.Stanza.ofXml with
    | some svc, some st =>
      let (svc', ds) := Gc3.step svc fromFull st
      let changed := svc'.groups.filter (fun g => svc.group? g.name != some g)
      let gone := svc.groups.filter (fun g => (svc'.group? g.name).isNone)
      routeHeldAll { srv with gc3 := some svc' }
        { c with routeFull := c.routeFull ++ (ds.filter (!·.held)).map (fun d => (d.to, d.render, none)),
                 store := c.store ++ (if srv.cfg.persist then changed.map (fun g => (StateCodec.pathOf "gc3" g.name, StateCodec.encodeGroup g)) else []),
                 unstore := c.unstore ++ (if srv.cfg.persist then gone.map (fun g => StateCodec.pathOf "gc3" g.name) else []) }
        ((ds.filter (·.held)).map (fun d => (d.to, d.render)))
    | _, _ => (srv, c)
  | .saveRoster bare encoded =>
      ({ srv with rosters := srv.rosters.insert bare (rosterDecode encoded)
                  senders := srv.senders.record srv.cfg.senderLimits srv.now (rosterKeys bare) },
       { c with rostersSaved := if c.rostersSaved.contains bare then c.rostersSaved
                                else c.rostersSaved ++ [bare]
                store := c.store ++ (if srv.cfg.persist then [(StateCodec.pathOf "roster" bare, encoded)] else []) })
  | .presence bare full available =>
      let others := (srv.presence.getD bare []).filter (· != full)
      let now := if available then full :: others else others
      ({ srv with presence := srv.presence.insert bare now },
       { c with presence := c.presence ++ [(bare, full, available)] })
  | .close => (srv, { c with close := true })
  | .startTls => (srv, { c with startTls := true })

private def performAll (sender : Option String) (srv : XmppOpenServer) (c : XmppCollected) :
    List Out → XmppOpenServer × XmppCollected
  | [] => (srv, c)
  | o :: os =>
    let (srv', c') := perform sender srv c o
    performAll sender srv' c' os

/-- The session holding `f` is gone: `f` is free, and it leaves every room it was in (XEP-0045
section 7.14). The other occupants' deliveries go in `routeFull`. It runs when the stream ends, not
when the host closes the handle, as a new session can bind `f` between the two. -/
def sessionGone (srv : XmppOpenServer) (c : XmppCollected) (f : String) :
    XmppOpenServer × XmppCollected :=
  let kept := { srv with bound := srv.bound.erase f }
  match srv.muc with
  | some svc =>
    let (svc', ds) := Muc.leaveAll svc f
    ({ kept with muc := some svc' },
     { c with routeFull := c.routeFull ++ ds.map (fun d => (d.to, d.render, none)) })
  | none => (kept, c)

/-- The full JID a session holds changed by one step (it bound, or its stream ended): keep `bound`,
and hand a newly bound account what was held for it, oldest first. -/
def bindTransition (srv : XmppOpenServer) (c : XmppCollected) (before after : Option String) :
    XmppOpenServer × XmppCollected :=
  if before == after then (srv, c)
  else
    let (srv1, c1) := match before with
      | some f => sessionGone srv c f
      | none => (srv, c)
    match after with
    | none => (srv1, c1)
    | some f =>
      let bare := Server.bareOf f
      let (out, h') := Held.release srv1.held bare
      ({ srv1 with bound := srv1.bound ++ [f], held := h' },
       { c1 with route := c1.route ++ out.map (fun i => (bare, i.text)),
                 -- The older one-resource form too: it may be there, and a delete of nothing is nothing.
                 unstore := if out.isEmpty || !srv1.cfg.persist then c1.unstore
                   else c1.unstore ++ [StateCodec.pathOf "held" bare] ++ out.map (fun i => StateCodec.heldItemPath bare i.seq) })

/-- What `Server.step` reads from the server for a unit of this session. -/
private def XmppOpenServer.envFor (srv : XmppOpenServer) (os : XmppOpenSession) : Env :=
  { roster := match os.session.bareJid with
      | some b => srv.rosters.getD b []
      | none => []
    guard := srv.guardFor os, rosterOpen := rosterOpen srv os.session.bareJid, bound := srv.bound }

/-- One unit on an open session, for the byte stream and the framed transports alike: `Server.step`
with the server's live full JIDs, its actions, and the change to `bound`. Also the actions, for
`bufferAfter`. -/
def stepSession (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (unit : Framing.Unit) : XmppOpenServer × XmppOpenSession × XmppCollected × List Out :=
  let (s', env', outs) := Server.step os.session (srv.envFor os) unit
  let (srv', c') := performAll os.session.bareJid
    { srv with failures := env'.guard.failures, backoff := env'.guard.backoff } c outs
  let closed := c'.close || s'.stage == .closed
  let (srv'', c'') := bindTransition srv' c' os.liveFull (if closed then none else s'.fullJid)
  (srv'', { os with session := s', units := os.units + 1, closed }, c'', outs)

/-- The stream of a session ended outside `Server.step`: its full JID is free from now on. -/
def endStream (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected) :
    XmppOpenServer × XmppOpenSession × XmppCollected :=
  let (srv', c') := bindTransition srv c os.liveFull none
  (srv', { os with closed := true }, { c' with close := true })

/-- A session past `maxUnits`: RFC 6120 section 4.9.3.14 `policy-violation`, and its stream ends. -/
def refuseSession (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected) :
    XmppOpenServer × XmppOpenSession × XmppCollected :=
  let (srv', c') := performAll os.session.bareJid srv c
    (Server.streamError "policy-violation" "too many stream units")
  endStream srv' os c'

/-- The buffer left after a unit's actions. When they ask for the TLS
upgrade it is EMPTY: those bytes arrived in clear after `<starttls/>`,
and reading them as part of the secured stream is the plaintext-injection
fault of STARTTLS implementations (CVE-2011-0411 and its successors;
RFC 6120 section 5.4.3.3). -/
def bufferAfter (outs : List Out) (rest : String) : String :=
  if outs.contains .startTls then "" else rest

theorem bufferAfter_startTls (outs : List Out) (rest : String)
    (h : Out.startTls ∈ outs) : bufferAfter outs rest = "" := by
  simp [bufferAfter, h]

/-- Process every complete unit in the buffer, as `Harness.XmppServe.drainBuffer`
does. `fuel` bounds the recursion: every unit consumes at least one
character, so the buffer's length is always enough. The roster handed to
`step` is read from the server table fresh for every unit, so a change
another session made is seen, as the harness reads the file fresh. -/
def drain (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected) :
    Nat → XmppOpenServer × XmppOpenSession × XmppCollected
  | 0 => (srv, os, c)
  | fuel + 1 =>
    -- `tlsPending`: the host is doing the handshake; nothing is read.
    if os.closed || os.session.stage == .tlsPending then (srv, os, c)
    else
      match Framing.nextUnit (!os.session.awaitingStreamOpen) os.buffer with
      | none => (srv, os, c)
      | some (unit, rest) =>
        if os.units ≥ os.maxUnits then
          let (srv', os', c') := refuseSession srv os c
          (srv', { os' with buffer := rest }, c')
        else
          let (srv', os', c', outs) := stepSession srv os c unit
          drain srv' { os' with buffer := bufferAfter outs rest } c' fuel

/-- While the handshake runs, a feed changes nothing and reports nothing.
With `bufferAfter_startTls` (the buffer is empty when `tlsPending` is
entered) and `Server.step_tlsPending`, no byte sent in clear after
`<starttls/>` is ever read. -/
theorem drain_tlsPending (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (fuel : Nat) (h : os.session.stage = .tlsPending) : drain srv os c fuel = (srv, os, c) := by
  cases fuel <;> simp [drain, h]

private def stageName : Server.Stage → String
  | .initial => "initial"
  | .awaitingStartTls => "awaitingStartTls"
  | .tlsPending => "tlsPending"
  | .awaitingAuth => "awaitingAuth"
  | .awaitingScramResponse .. => "awaitingScramResponse"
  | .authenticated _ => "authenticated"
  | .awaitingBind _ => "awaitingBind"
  | .bound .. => "bound"
  | .closed => "closed"

private def jsonOfCollected (os : XmppOpenSession) (c : XmppCollected) : List (String × Json) :=
  [ ("send", .array (c.send.map .string))
  , ("route", .array (c.route.map (fun (to, text) =>
      .object [("to", .string to), ("text", .string text)])))
  , ("routeFull", .array (c.routeFull.map (fun (to, text, bounce) =>
      .object [("to", .string to), ("text", .string text), ("bounce", jsonOfOptString bounce)])))
  , ("presence", .array (c.presence.map (fun (bare, full, available) =>
      .object [("bare", .string bare), ("full", .string full), ("available", .bool available)])))
  , ("rostersSaved", .array (c.rostersSaved.map .string))
  , ("store", .array (c.store.map (fun (p, t) => .object [("path", .string p), ("text", .string t)])))
  , ("unstore", .array (c.unstore.map .string))
  , ("close", .bool c.close)
  , ("startTls", .bool c.startTls)
  , ("stage", .string (stageName os.session.stage))
  -- The carrier applies its transport limit to the actual residual buffer,
  -- independently of whether a complete unit happened to produce output.
  , ("bufferedBytes", .number (toString os.buffer.utf8ByteSize))
  , ("bare", jsonOfOptString os.session.bareJid)
  , ("full", jsonOfOptString os.liveFull) ]

/-! ## The ops -/

def xmppOpen (configJson : String) : IO String := do
  match xmppServerConfigOfJson (if configJson.trim.isEmpty then "{}" else configJson) with
  | .error e => pure (errJson e)
  | .ok cfg =>
      let n ← xmppServerCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"xmpp{n}"
      -- PBKDF2 runs here, once for each account, and never at a login.
      let probe : Config := { domain := cfg.domain, streamId := "", serverNonce := "", saltB64 := cfg.saltB64
                              iterationCount := cfg.iterationCount, accounts := [], tlsCarrier := false
                              saltSeed := cfg.saltSeed }
      let derived := (cfg.accounts.filter (fun a => !a.password.isEmpty)).filterMap (fun a =>
        (Scram.credentialsOfPassword a.password (probe.saltFor a.username) cfg.iterationCount).map (a.username, ·))
      let cfg := { cfg with credentials := cfg.verifiers ++ derived }
      -- Each account's name is its own nick, beside the nicks the host reserves.
      let reserved := cfg.mucReserved ++ cfg.accounts.map (fun a => (Muc.nickKey a.username, a.username ++ "@" ++ cfg.domain))
      let owners := cfg.mucOwners.getD []
      let muc : Option Muc.Service := cfg.mucDomain.map (fun d =>
        { domain := d, memberLists := cfg.mucMembers, reserved, idSeed := cfg.occupantSeed
          firstOwner := cfg.mucOwners.isNone
          serviceOwners := (owners.filter (·.room == "*")).flatMap (·.members)
          roomOwners := owners.filter (·.room != "*") })
      let mix : Option Mix.Service := cfg.mixDomain.map (fun d => { domain := d })
      let gc3 : Option Gc3.Service := cfg.gc3Domain.map (fun d => { domain := d })
      xmppServers.modify (·.insert h { cfg := cfg, rosters := ∅, presence := ∅, muc := muc, mix := mix, gc3 := gc3,
                                       held := { caps := cfg.heldCaps } })
      pure (okWith [ ("handle", .string h)
                   , ("domain", .string cfg.domain)
                   , ("accounts", .number (toString cfg.accounts.length))
                   , ("mucMembers", .number (toString cfg.mucMembers.length))
                   , ("mucOwners", .number (toString owners.length))
                   , ("warnings", .array ((Server.saslLimitWarnings cfg.limits).map Json.string)) ])

def xmppClose (h : String) : IO String := do
  let servers ← xmppServers.get
  if servers.contains h then
    xmppServers.set (servers.erase h)
    -- Every session of that server goes with it.
    let sessions ← xmppSessions.get
    let mine := sessions.fold (fun acc k v => if v.server == h then k :: acc else acc) []
    xmppSessions.set (mine.foldl (fun t k => t.erase k) sessions)
    pure (okWith [("sessions", .number (toString mine.length))])
  else
    pure (unknownXmppServer h)

/-- `xmppVerifier(username, password, saltB64, iterations)`: one line of an accounts file that
holds no password. The host supplies the salt: this module has no random source. -/
def xmppVerifier (username password saltB64 iterations : String) : IO String := do
  match iterations.toNat? with
  | none => pure (errJson "xmppVerifier: iterations must be a number")
  | some n =>
    if username.isEmpty || password.isEmpty then pure (errJson "xmppVerifier: a name and a password are required")
    else match Scram.credentialsOfPassword password saltB64 n with
      | none => pure (errJson "xmppVerifier: the salt is not base64, or the count is 0")
      | some c => pure (okWith [("line", .string (username ++ ":" ++ Server.verifierText c))])

/-- `xmppClock(serverHandle, seconds)`: the host's clock, which only moves forward. The rate
limits read it, so a host calls this when the second changes, not only when a connection opens. -/
def xmppClock (server seconds : String) : IO String := do
  match (← xmppServers.get)[server]?, seconds.toNat? with
  | none, _ => pure (unknownXmppServer server)
  | _, none => pure (errJson "xmppClock: seconds must be a number")
  | some srv, some now =>
    xmppServers.modify (·.insert server { srv with now := max srv.now now })
    pure (okWith [])

/-- `xmppSessionOpen(serverHandle, {"streamId","nonce","tlsCarrier"?,"maxUnits"?,
"remoteAddress"?,"now"?})`. `remoteAddress` (the socket's) and `now` (the
host's clock, seconds) feed the failed SASL login limit
(https://github.com/danbri/factoidal/issues/1128): failures count per
account name and per client address, across the sessions of the server.
`streamId` and `nonce` are required: they must be unpredictable and this
module has no random source. -/
def xmppSessionOpen (server optionsJson : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    match parseJson (if optionsJson.trim.isEmpty then "{}" else optionsJson) with
    | .error e => pure (errJson s!"options: {toString e}")
    | .ok j =>
      match j.getString? "streamId", j.getString? "nonce" with
      | none, _ => pure (errJson "xmppSessionOpen: \"streamId\" is required (RFC 6120 section 4.7.3: the host supplies an unpredictable value)")
      | _, none => pure (errJson "xmppSessionOpen: \"nonce\" is required (RFC 5802 section 5.1: the host supplies an unpredictable value)")
      | some streamId, some nonce =>
        if streamId.isEmpty || nonce.isEmpty then
          pure (errJson "xmppSessionOpen: \"streamId\" and \"nonce\" must not be empty")
        else
          let cfg := srv.sessionConfig streamId nonce ((j.getBool? "tlsCarrier").getD srv.cfg.tlsCarrier)
            ((j.getBool? "startTls").getD false)
          let n ← xmppSessionCounter.modifyGet fun n => (n + 1, n + 1)
          let h := s!"xmpps{n}"
          -- The host's clock (seconds) moves the server's clock forward.
          if let some now := natField? j "now" then
            xmppServers.modify (·.insert server { srv with now := max srv.now now })
          xmppSessions.modify (·.insert h
            { server, session := Session.init cfg, buffer := "", units := 0
              maxUnits := (natField? j "maxUnits").getD 1000000, closed := false
              address := (j.getString? "remoteAddress").getD "" })
          pure (okWith [("handle", .string h)])

/-- `xmppSessionFeed(sessionHandle, text)`: the bytes a socket read, as
UTF-8 text. An incomplete unit stays in the buffer until the rest
arrives. -/
def xmppSessionFeed (h text : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    match (← xmppServers.get)[os.server]? with
    | none => pure (unknownXmppServer os.server)
    | some srv =>
      let os := { os with buffer := os.buffer ++ text }
      let (srv', os', c) := drain srv os {} (os.buffer.length + 1)
      xmppServers.modify (·.insert os.server srv')
      xmppSessions.modify (·.insert h os')
      pure (okWith (jsonOfCollected os' c))

/-- `xmppSessionDeliver(sessionHandle, text)`: a stanza another session
routed to this one. Refused — `delivered:false`, nothing lost — unless
the session is bound (RFC 6121 section 8.5.3), so the host holds it
rather than this module destroying it. -/
def xmppSessionDeliver (h text : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    if os.closed || !os.session.canDeliver then
      pure (okWith [("delivered", .bool false), ("send", .array [])])
    else
      let sends := (Server.deliver os.session text).filterMap (fun o =>
        match o with | .send t => some t | _ => none)
      pure (okWith [("delivered", .bool true), ("send", .array (sends.map .string))])

/-- `xmppSessionPing(sessionHandle, id)`: the host heard nothing from this session for a while.
`sent:false` and nothing to write unless the session is bound (`Session.ping`). -/
def xmppSessionPing (h id : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    match if os.closed then none else os.session.ping id with
    | none => pure (okWith [("sent", .bool false), ("send", .array [])])
    | some t => pure (okWith [("sent", .bool true), ("send", .array [.string t])])

/-- The host is closing a session's handle. A session with a live full JID lost its transport, and
`sessionGone` runs now; one whose stream ended has already been through it. The deliveries, as
`routeFull` JSON, for the host to perform. -/
def sessionClosed (os : XmppOpenSession) : IO Json := do
  match os.liveFull, (← xmppServers.get)[os.server]? with
  | some f, some srv =>
    let (srv', c) := sessionGone srv {} f
    xmppServers.modify (·.insert os.server srv')
    pure (.array (c.routeFull.map (fun (to, text, bounce) =>
      .object [("to", .string to), ("text", .string text), ("bounce", jsonOfOptString bounce)])))
  | _, _ => pure (.array [])

/-- `xmppSessionClose(sessionHandle)`: the socket reached end of input or
is being closed by the host. A half-closed stream is answered the way
RFC 6120 section 4.4 asks, then the handle is released. The presence
table is NOT touched: an available full JID stays available until an
`unavailable` presence is seen, as in the harness. -/
def xmppSessionClose (h : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    let closing : List String :=
      if os.closed || os.session.stage == .closed then [] else ["</stream:stream>"]
    xmppSessions.modify (·.erase h)
    let left ← sessionClosed os
    pure (okWith [("send", .array (closing.map .string)), ("routeFull", left)])

/-- `xmppSessionTlsUp(sessionHandle)`: the TLS handshake that a feed asked
for (`startTls: true`) finished. Refused unless the session is in
`tlsPending` with an empty buffer (`Server.Session.tlsEstablished`); the
client must now send a new stream header. -/
def xmppSessionTlsUp (h : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    if os.closed || !os.buffer.isEmpty then
      pure (errJson "xmppSessionTlsUp: the session is closed or holds unread bytes")
    else
      match os.session.tlsEstablished with
      | none => pure (errJson s!"xmppSessionTlsUp: no STARTTLS is pending (stage {stageName os.session.stage})")
      | some s' =>
        xmppSessions.modify (·.insert h { os with session := s' })
        pure (okWith [("stage", .string (stageName s'.stage))])

private def jsonOfRosterItem (i : RosterItem) : Json :=
  .object [ ("jid", .string i.jid), ("name", .string i.name)
          , ("subscription", .string i.subscription), ("ask", .bool i.ask) ]

/-- `xmppRosterGet(serverHandle, bareJid)`: the roster as the server
encodes it on disk (`rosterEncode`) and as items. A host that persists
rosters stores `encoded` and hands it back through `xmppRosterSet`;
it never has to read the format. -/
def xmppRosterGet (server bare : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    let r := srv.rosters.getD bare []
    pure (okWith [ ("encoded", .string (rosterEncode r))
                 , ("items", .array (r.map jsonOfRosterItem)) ])

/-- `xmppRosterSet(serverHandle, bareJid, encoded)`: load a roster the
host persisted. The bytes are the server's own format; lines it does not
recognise are dropped by `rosterDecode`, as the harness drops them. -/
def xmppRosterSet (server bare encoded : String) : IO String := do
  let servers ← xmppServers.get
  match servers[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    xmppServers.set (servers.insert server
      { srv with rosters := srv.rosters.insert bare (rosterDecode encoded) })
    pure (okWith [])

/-! ## XMPP over WebSocket (RFC 7395 over RFC 6455)

One connection, from its first byte: an HTTP/1.1 opening handshake
(`HTTP.Wire.frameRequest`, `HTTP.WebSocket.upgrade`, the path check
here), then frames (`HTTP.WebSocket.Reader`), each text message one unit
for `Server.step` (`XMPP.WebSocket.unitOfMessage`), each `Out.send` one
text frame (`XMPP.WebSocket.messageOfSend`, `HTTP.WebSocket.encode`). The
host moves bytes; every decision is here or below.

The ops cross the blob ABI (`Dispatch.blobIoOpNames`): the IN region is
what the socket read, the OUT region is what the host must write. -/

open L4Factoidal.HTTP.WebSocket (Policy Reader Event) in
inductive XmppWsPhase where
  /-- Reading the opening handshake. -/
  | handshake (buf : ByteArray)
  /-- Frames. -/
  | frames (reader : L4Factoidal.HTTP.WebSocket.Reader) (buf : ByteArray)
  /-- Closed; nothing more is read. -/
  | done

structure XmppWsSession where
  inner : XmppOpenSession
  policy : L4Factoidal.HTTP.WebSocket.Policy
  /-- The request path the handshake must name (e.g. `/xmpp-websocket`). -/
  path : String
  phase : XmppWsPhase

initialize xmppWsCounter : IO.Ref Nat ← IO.mkRef 0
initialize xmppWsSessions : IO.Ref (Std.HashMap String XmppWsSession) ← IO.mkRef ∅

/-- An HTTP error response that closes the connection. -/
def wsHttpRefusal (status : Nat) (reason : String) : ByteArray :=
  let phrase := L4Factoidal.HTTP.Wire.reasonPhrase status
  let body := reason ++ "\n"
  (s!"HTTP/1.1 {status} {phrase}\r\nContent-Type: text/plain; charset=utf-8\r\n" ++
   (if status == 426 then "Sec-WebSocket-Version: 13\r\n" else "") ++
   s!"Content-Length: {body.utf8ByteSize}\r\nConnection: close\r\n\r\n{body}").toUTF8

/-- One unit through `Server.step`, as `drain` does for one unit: the
roster read fresh, `maxUnits` enforced, actions performed. -/
def stepOneUnit (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (unit : Framing.Unit) : XmppOpenServer × XmppOpenSession × XmppCollected :=
  if os.closed then (srv, os, c)
  else if os.units ≥ os.maxUnits then refuseSession srv os c
  else
    let (srv', os', c', _) := stepSession srv os c unit
    (srv', os', c')

/-- The frames for the `send` texts of one step, in order. -/
def wsFramesOf (cfg : Config) (sends : List String) : ByteArray :=
  sends.foldl (fun acc t =>
    acc ++ L4Factoidal.HTTP.WebSocket.encode .text (L4Factoidal.XMPP.WebSocket.messageOfSend cfg t).toUTF8)
    ByteArray.empty

/-- Apply the events of one read, in order. A tail call over the list. -/
def wsApplyEvents (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected) (out : ByteArray) :
    List L4Factoidal.HTTP.WebSocket.Event → XmppOpenServer × XmppOpenSession × XmppCollected × ByteArray × Bool
  | [] => (srv, os, c, out, false)
  | e :: es =>
    match e with
    | .text msg =>
      let before := c.send.length
      let (srv', os', c') := stepOneUnit srv os c (L4Factoidal.XMPP.WebSocket.unitOfMessage msg)
      let out' := out ++ wsFramesOf os'.session.cfg (c'.send.drop before)
      if os'.closed then
        (srv', os', c', out' ++ L4Factoidal.HTTP.WebSocket.closeFrame 1000, true)
      else wsApplyEvents srv' os' c' out' es
    | .ping p => wsApplyEvents srv os c (out ++ L4Factoidal.HTTP.WebSocket.encode .pong p) es
    | .close _ =>
      -- RFC 6455 section 5.5.1: answer a close with a close. The XMPP
      -- stream ends with it (RFC 7395 section 3.6).
      let (srv', os', c') := endStream srv os c
      (srv', os', c', out ++ L4Factoidal.HTTP.WebSocket.closeFrame 1000, true)
    | .fail code _ =>
      let (srv', os', c') := endStream srv os c
      (srv', os', c', out ++ L4Factoidal.HTTP.WebSocket.closeFrame code, true)

/-- One read from the socket. -/
def wsFeedPure (srv : XmppOpenServer) (ws : XmppWsSession) (bytes : ByteArray) :
    XmppOpenServer × XmppWsSession × XmppCollected × ByteArray :=
  let frames (srv : XmppOpenServer) (ws : XmppWsSession) (r : L4Factoidal.HTTP.WebSocket.Reader)
      (buf : ByteArray) (out : ByteArray) : XmppOpenServer × XmppWsSession × XmppCollected × ByteArray :=
    let (r', rest, evs) := r.feed buf [] (buf.size + 1)
    let (srv', os', c', out', ended) := wsApplyEvents srv ws.inner {} out evs
    let phase := if ended || r'.done then XmppWsPhase.done else .frames r' rest
    (srv', { ws with inner := os', phase }, { c' with close := c'.close || ended || r'.done }, out')
  match ws.phase with
  | .done => (srv, ws, {}, ByteArray.empty)
  | .frames r buf => frames srv ws r (buf ++ bytes) ByteArray.empty
  | .handshake buf =>
    let buf := buf ++ bytes
    match L4Factoidal.HTTP.Wire.frameRequest buf (bodyLimit := 0) with
    | .incomplete _ => (srv, { ws with phase := .handshake buf }, {}, ByteArray.empty)
    | .reject status reason =>
      (srv, { ws with phase := .done }, { close := true }, wsHttpRefusal status reason)
    | .request req used _ =>
      if req.path != ws.path then
        (srv, { ws with phase := .done }, { close := true }, wsHttpRefusal 404 "no WebSocket endpoint at this path")
      else
        match L4Factoidal.HTTP.WebSocket.upgrade ws.policy req.method req.headers with
        | .refuse status reason =>
          (srv, { ws with phase := .done }, { close := true }, wsHttpRefusal status reason)
        | .accept response =>
          frames srv ws {} (buf.extract used buf.size) response.toUTF8

/-- Before the handshake is accepted, no unit reaches `Server.step`: a
connection whose opening handshake is refused (or incomplete) never
authenticates anybody and routes nothing. -/
theorem wsFeedPure_handshake_refused (srv : XmppOpenServer) (ws : XmppWsSession)
    (buf bytes : ByteArray) (h : ws.phase = .handshake buf)
    (hr : ∀ r u x, L4Factoidal.HTTP.Wire.frameRequest (buf ++ bytes) (bodyLimit := 0) ≠ .request r u x) :
    (wsFeedPure srv ws bytes).2.1.inner = ws.inner ∧ (wsFeedPure srv ws bytes).2.2.1.route = [] := by
  unfold wsFeedPure
  simp only [h]
  split
  · simp
  · simp
  · rename_i r u x heq; exact absurd heq (hr r u x)

def xmppWsJson (ws : XmppWsSession) (c : XmppCollected) : String :=
  okWith ((jsonOfCollected ws.inner c).filter (fun (k, _) => k != "send" && k != "bufferedBytes") ++
    [("phase", .string (match ws.phase with
        | .handshake _ => "handshake" | .frames .. => "frames" | .done => "done")),
     ("bufferedBytes", .number (toString (match ws.phase with
        | .handshake b => b.size | .frames _ b => b.size | .done => 0)))])

/-- `xmppWsOpen(serverHandle, {"streamId","nonce","path","allowedOrigins"?,
"allowNoOrigin"?,"tlsCarrier"?,"maxUnits"?,"maxFrame"?,"maxMessage"?,"remoteAddress"?})`. -/
def xmppWsOpen (server optionsJson : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    match parseJson (if optionsJson.trim.isEmpty then "{}" else optionsJson) with
    | .error e => pure (errJson s!"options: {toString e}")
    | .ok j =>
      match j.getString? "streamId", j.getString? "nonce", j.getString? "path" with
      | some streamId, some nonce, some path =>
        if streamId.isEmpty || nonce.isEmpty || !path.startsWith "/" then
          pure (errJson "xmppWsOpen: \"streamId\" and \"nonce\" must not be empty, and \"path\" must start with /")
        else
          let cfg := srv.sessionConfig streamId nonce ((j.getBool? "tlsCarrier").getD false) false
          let origins := ((j.getArray? "allowedOrigins").getD []).filterMap Json.asString?
          let policy : L4Factoidal.HTTP.WebSocket.Policy :=
            { allowedOrigins := origins.map (·.toLower), allowNoOrigin := (j.getBool? "allowNoOrigin").getD false
              protocol := "xmpp" }
          let n ← xmppWsCounter.modifyGet fun n => (n + 1, n + 1)
          let h := s!"xmppws{n}"
          xmppWsSessions.modify (·.insert h
            { inner := { server, session := Session.init cfg, buffer := "", units := 0
                         maxUnits := (natField? j "maxUnits").getD 1000000, closed := false
                         address := (j.getString? "remoteAddress").getD "" }
              policy, path, phase := .handshake ByteArray.empty })
          pure (okWith [("handle", .string h)])
      | _, _, _ => pure (errJson "xmppWsOpen: \"streamId\", \"nonce\" and \"path\" are required")

/-- `xmppWsFeed(handle)` with the bytes the socket read as the IN region;
the OUT region is what to write. -/
def xmppWsFeedWith (h : String) (bytes : ByteArray) : IO (String × ByteArray) := do
  match (← xmppWsSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP WebSocket session handle: {h}", ByteArray.empty)
  | some ws =>
    match (← xmppServers.get)[ws.inner.server]? with
    | none => pure (unknownXmppServer ws.inner.server, ByteArray.empty)
    | some srv =>
      let (srv', ws', c, out) := wsFeedPure srv ws bytes
      xmppServers.modify (·.insert ws.inner.server srv')
      xmppWsSessions.modify (·.insert h ws')
      pure (xmppWsJson ws' c, out)

/-- `xmppWsDeliver(handle, text)`: a stanza routed to this session. OUT
region: its frame, when the session is bound. -/
def xmppWsDeliverWith (h text : String) : IO (String × ByteArray) := do
  match (← xmppWsSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP WebSocket session handle: {h}", ByteArray.empty)
  | some ws =>
    let live := match ws.phase with | .frames .. => true | _ => false
    if !live || ws.inner.closed || !ws.inner.session.canDeliver then
      pure (okWith [("delivered", .bool false)], ByteArray.empty)
    else
      let sends := (Server.deliver ws.inner.session text).filterMap (fun o =>
        match o with | .send t => some t | _ => none)
      pure (okWith [("delivered", .bool true)], wsFramesOf ws.inner.session.cfg sends)

/-- `xmppWsPing(handle)`: the host heard nothing from this session for a while. OUT region: a ping
frame (RFC 6455 section 5.5.2), when the session is bound. The peer's WebSocket layer answers
it, so a browser needs no XMPP code and no page script to stay connected; the pong is dropped by
the reader, and the bytes are the proof of life. -/
def xmppWsPingWith (h : String) : IO (String × ByteArray) := do
  match (← xmppWsSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP WebSocket session handle: {h}", ByteArray.empty)
  | some ws =>
    let live := match ws.phase with | .frames .. => true | _ => false
    if !live || ws.inner.closed || !ws.inner.session.canDeliver then
      pure (okWith [("sent", .bool false)], ByteArray.empty)
    else
      pure (okWith [("sent", .bool true)], L4Factoidal.HTTP.WebSocket.encode .ping ByteArray.empty)

/-- `xmppWsClose(handle)`: release the handle. OUT region: `<close/>` and
a close frame when the stream was open (RFC 7395 section 3.6). -/
def xmppWsCloseWith (h : String) : IO (String × ByteArray) := do
  match (← xmppWsSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP WebSocket session handle: {h}", ByteArray.empty)
  | some ws =>
    xmppWsSessions.modify (·.erase h)
    let left ← sessionClosed ws.inner
    match ws.phase with
    | .frames .. =>
      if ws.inner.closed then pure (okWith [("routeFull", left)], ByteArray.empty)
      else pure (okWith [("routeFull", left)], wsFramesOf ws.inner.session.cfg [Server.streamCloseText] ++
                          L4Factoidal.HTTP.WebSocket.closeFrame 1000)
    | _ => pure (okWith [("routeFull", left)], ByteArray.empty)

def xmppWsBlobIoOpNames : List String := ["xmppWsFeed", "xmppWsDeliver", "xmppWsPing", "xmppWsClose"]

/-! ## A message carrier: RFC 7395 without the socket

A carrier that already delivers whole messages, in order and to one peer
(a browser `MessagePort`, a `postMessage` channel between a page and a
worker), needs neither the HTTP handshake nor the WebSocket frames. Each
message is one RFC 7395 message, exactly as over a WebSocket: `<open/>`
and `<close/>` in the framing namespace, then one complete element per
message (section 3.3.3). Inbound, `WebSocket.unitOfMessage`; outbound,
`WebSocket.messageOfSend`; between them the same `stepOneUnit`, so every
decision is still `Server.step`'s. The carrier is not a network: it has no
Origin to check, and it is up to the host which code may hold one. -/

initialize xmppMsgCounter : IO.Ref Nat ← IO.mkRef 0
initialize xmppMsgSessions : IO.Ref (Std.HashMap String XmppOpenSession) ← IO.mkRef ∅

/-- One message through `Server.step`; the answer is whole messages. -/
def msgFeedPure (srv : XmppOpenServer) (os : XmppOpenSession) (msg : String) :
    XmppOpenServer × XmppOpenSession × XmppCollected × List String :=
  if os.closed then (srv, os, {}, [])
  else
    let (srv', os', c) := stepOneUnit srv os {} (L4Factoidal.XMPP.WebSocket.unitOfMessage msg)
    (srv', os', { c with close := c.close || os'.closed },
     c.send.map (L4Factoidal.XMPP.WebSocket.messageOfSend os'.session.cfg))

/-- A closed message session reads nothing more: the server and the session
are unchanged, and nothing is sent or routed. -/
theorem msgFeedPure_closed (srv : XmppOpenServer) (os : XmppOpenSession) (msg : String)
    (h : os.closed = true) :
    msgFeedPure srv os msg = (srv, os, {}, []) := by
  simp [msgFeedPure, h]

/-! ## One full JID, one live session

`Unique srv oss`: `oss` are the sessions of `srv`, and `srv.bound` lists each live full JID of them
once. No two live sessions then hold one full JID (`Unique.nodup`). An open keeps it, every unit on
any transport keeps it, and so does a close. -/

/-- The full JIDs held by these sessions. -/
def liveFulls (oss : List XmppOpenSession) : List String := oss.filterMap (·.liveFull)

def Unique (srv : XmppOpenServer) (oss : List XmppOpenSession) : Prop :=
  srv.bound.Nodup ∧ (liveFulls oss).Perm srv.bound

/-- 1. No two live sessions hold one full JID. -/
theorem Unique.nodup {srv : XmppOpenServer} {oss : List XmppOpenSession} (h : Unique srv oss) :
    (liveFulls oss).Nodup :=
  h.2.nodup_iff.mpr h.1

/-- 2. So a session's full JID is no other live session's. -/
theorem Unique.distinct {srv : XmppOpenServer} {a : XmppOpenSession} {rest : List XmppOpenSession}
    {f : String} (h : Unique srv (a :: rest)) (ha : a.liveFull = some f) : f ∉ liveFulls rest := by
  have hn := h.nodup
  simp only [liveFulls, List.filterMap_cons, ha] at hn
  exact (List.nodup_cons.mp hn).1

private theorem holdStanza_bound (srv : XmppOpenServer) (c : XmppCollected) (sender : Option String)
    (bare text : String) : (holdStanza srv c sender bare text).1.bound = srv.bound := by
  unfold holdStanza
  repeat' first | split | dsimp only
  all_goals rfl

private theorem routeOrHold_bound (srv : XmppOpenServer) (c : XmppCollected) (sender : Option String)
    (bare text : String) : (routeOrHold srv c sender bare text).1.bound = srv.bound := by
  unfold routeOrHold
  split
  · rfl
  · exact holdStanza_bound ..

private theorem routeHeldAll_bound (srv : XmppOpenServer) (c : XmppCollected)
    (ds : List (String × String)) : (routeHeldAll srv c ds).1.bound = srv.bound := by
  unfold routeHeldAll
  induction ds generalizing srv c with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact routeOrHold_bound ..

private theorem perform_bound (sender : Option String) (srv : XmppOpenServer) (c : XmppCollected)
    (o : Out) : (perform sender srv c o).1.bound = srv.bound := by
  unfold perform
  repeat' first | split | dsimp only
  all_goals first
    | rfl
    | exact routeOrHold_bound ..
    | exact routeHeldAll_bound ..

private theorem performAll_bound (sender : Option String) (srv : XmppOpenServer) (c : XmppCollected)
    (outs : List Out) : (performAll sender srv c outs).1.bound = srv.bound := by
  induction outs generalizing srv c with
  | nil => rfl
  | cons o os ih =>
    simp only [performAll]
    rw [ih, perform_bound]

theorem sessionGone_bound (srv : XmppOpenServer) (c : XmppCollected) (f : String) :
    (sessionGone srv c f).1.bound = srv.bound.erase f := by
  unfold sessionGone
  split <;> rfl

/-- What a step may do to the full JID a session holds, seen from `srv`. -/
def Transition (srv : XmppOpenServer) (before after : Option String) : Prop :=
  after = before ∨ after = none ∨ (before = none ∧ ∃ f, after = some f ∧ f ∉ srv.bound)

theorem bindTransition_unique (srv : XmppOpenServer) (c : XmppCollected) (os os' : XmppOpenSession)
    (rest : List XmppOpenSession) (h : Unique srv (os :: rest))
    (ht : Transition srv os.liveFull os'.liveFull) :
    Unique (bindTransition srv c os.liveFull os'.liveFull).1 (os' :: rest) := by
  obtain ⟨hn, hp⟩ := h
  simp only [liveFulls, List.filterMap_cons] at hp
  rcases ht with ht | ht | ⟨hb, f, ha, hf⟩
  · have : bindTransition srv c os.liveFull os'.liveFull = (srv, c) := by
      simp [bindTransition, ht]
    rw [this]
    refine ⟨hn, ?_⟩
    simp only [liveFulls, List.filterMap_cons, ht]
    exact hp
  · rw [ht]
    cases hb : os.liveFull with
    | none =>
      rw [hb] at hp
      have : bindTransition srv c none none = (srv, c) := by simp [bindTransition]
      rw [this]
      exact ⟨hn, by simpa [liveFulls, ht] using hp⟩
    | some f =>
      rw [hb] at hp
      have : (bindTransition srv c (some f) none).1.bound = srv.bound.erase f := by
        simp [bindTransition, sessionGone_bound]
      refine ⟨by rw [this]; exact hn.erase f, ?_⟩
      rw [this]
      simpa [liveFulls, ht] using hp.erase f
  · rw [hb] at hp ⊢
    rw [ha]
    simp only at hp
    have : (bindTransition srv c none (some f)).1.bound = srv.bound ++ [f] := by
      simp [bindTransition]
    refine ⟨?_, ?_⟩
    · rw [this]
      exact List.nodup_append.mpr ⟨hn, by simp, by simp; intro x hx hxf; exact hf (hxf ▸ hx)⟩
    · rw [this]
      simp only [liveFulls, List.filterMap_cons, ha]
      exact (hp.cons f).trans (List.perm_append_comm (l₁ := [f]) (l₂ := srv.bound))

theorem Unique.congr {a b : XmppOpenServer} {x y : List XmppOpenSession} (h : Unique a x)
    (hb : b.bound = a.bound) (hl : liveFulls y = liveFulls x) : Unique b y := by
  obtain ⟨hn, hp⟩ := h
  exact ⟨hb ▸ hn, by rw [hl, hb]; exact hp⟩

private theorem liveFulls_head {a b : XmppOpenSession} (rest : List XmppOpenSession)
    (h : b.liveFull = a.liveFull) : liveFulls (b :: rest) = liveFulls (a :: rest) := by
  simp [liveFulls, List.filterMap_cons, h]

/-- 3. One unit on an open session keeps `Unique`: the session keeps its full JID, loses it, or gets
one that no live session holds. -/
theorem stepSession_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (unit : Framing.Unit) (rest : List XmppOpenSession) (hopen : os.closed = false)
    (h : Unique srv (os :: rest)) :
    Unique (stepSession srv os c unit).1 ((stepSession srv os c unit).2.1 :: rest) := by
  have hfs := Server.step_fullStep os.session (srv.envFor os) unit
  unfold stepSession
  cases hs : Server.step os.session (srv.envFor os) unit with
  | mk s' r =>
    obtain ⟨env', outs⟩ := r
    rw [hs] at hfs
    simp only at hfs ⊢
    have hb := performAll_bound os.session.bareJid
      { srv with failures := env'.guard.failures, backoff := env'.guard.backoff } c outs
    cases hp : performAll os.session.bareJid
        { srv with failures := env'.guard.failures, backoff := env'.guard.backoff } c outs with
    | mk srv' c' =>
      rw [hp] at hb
      simp only at hb ⊢
      have hbefore : os.liveFull = os.session.fullJid := by simp [XmppOpenSession.liveFull, hopen]
      let os' : XmppOpenSession :=
        { os with session := s', units := os.units + 1, closed := c'.close || s'.stage == .closed }
      have hu : Unique srv' (os :: rest) := h.congr hb rfl
      have ht : Transition srv' os.liveFull os'.liveFull := by
        by_cases hc : (c'.close || s'.stage == .closed) = true
        · exact Or.inr (Or.inl (by simp [os', XmppOpenSession.liveFull, hc]))
        · have hl : os'.liveFull = s'.fullJid := by simp only [os', XmppOpenSession.liveFull, if_neg hc]
          rw [hl, hbefore]
          rcases hfs with e | e | ⟨e1, f, e2, e3⟩
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr ⟨e1, f, e2, by rw [hb]; exact e3⟩)
      have hk := bindTransition_unique srv' c' os os' rest hu ht
      have hl2 : (if (c'.close || s'.stage == .closed) = true then none else s'.fullJid) = os'.liveFull := rfl
      rw [hl2]
      cases hbt : bindTransition srv' c' os.liveFull os'.liveFull with
      | mk a b =>
        rw [hbt] at hk
        exact hk

theorem endStream_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (rest : List XmppOpenSession) (h : Unique srv (os :: rest)) :
    Unique (endStream srv os c).1 ((endStream srv os c).2.1 :: rest) := by
  have e : ({ os with closed := true } : XmppOpenSession).liveFull = none := by
    simp [XmppOpenSession.liveFull]
  have hk := bindTransition_unique srv c os { os with closed := true } rest h (Or.inr (Or.inl e))
  rw [e] at hk
  unfold endStream
  cases hbt : bindTransition srv c os.liveFull none with
  | mk a b =>
    rw [hbt] at hk
    exact hk

theorem refuseSession_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (rest : List XmppOpenSession) (h : Unique srv (os :: rest)) :
    Unique (refuseSession srv os c).1 ((refuseSession srv os c).2.1 :: rest) := by
  have hb := performAll_bound os.session.bareJid srv c
    (Server.streamError "policy-violation" "too many stream units")
  unfold refuseSession
  cases hp : performAll os.session.bareJid srv c
      (Server.streamError "policy-violation" "too many stream units") with
  | mk srv' c' =>
    rw [hp] at hb
    exact endStream_unique srv' os c' rest (h.congr hb rfl)

/-- 4. The byte stream transports (TCP and direct TLS, and STARTTLS after the upgrade). -/
theorem drain_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (rest : List XmppOpenSession) (fuel : Nat) (h : Unique srv (os :: rest)) :
    Unique (drain srv os c fuel).1 ((drain srv os c fuel).2.1 :: rest) := by
  induction fuel generalizing srv os c with
  | zero => exact h
  | succ n ih =>
    unfold drain
    split
    · exact h
    · rename_i hc
      have hopen : os.closed = false := by
        simp only [Bool.or_eq_true, not_or] at hc
        simpa using hc.1
      split
      · exact h
      · rename_i unit restBuf _
        split
        · have hk := refuseSession_unique srv os c rest h
          cases hr : refuseSession srv os c with
          | mk a b =>
            obtain ⟨b1, b2⟩ := b
            rw [hr] at hk
            exact hk.congr rfl (liveFulls_head rest rfl)
        · have hk := stepSession_unique srv os c unit rest hopen h
          cases hr : stepSession srv os c unit with
          | mk a b =>
            obtain ⟨b1, b2, b3⟩ := b
            rw [hr] at hk
            exact ih a { b1 with buffer := bufferAfter b3 restBuf } b2
              (hk.congr rfl (liveFulls_head rest rfl))

theorem stepOneUnit_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (unit : Framing.Unit) (rest : List XmppOpenSession) (h : Unique srv (os :: rest)) :
    Unique (stepOneUnit srv os c unit).1 ((stepOneUnit srv os c unit).2.1 :: rest) := by
  unfold stepOneUnit
  split
  · exact h
  · rename_i hc
    split
    · exact refuseSession_unique srv os c rest h
    · have hk := stepSession_unique srv os c unit rest (by simpa using hc) h
      cases hr : stepSession srv os c unit with
      | mk a b =>
        obtain ⟨b1, b2, b3⟩ := b
        rw [hr] at hk
        exact hk

/-- 5. A WebSocket read's events. -/
theorem wsApplyEvents_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (out : ByteArray) (evs : List L4Factoidal.HTTP.WebSocket.Event)
    (rest : List XmppOpenSession) (h : Unique srv (os :: rest)) :
    Unique (wsApplyEvents srv os c out evs).1 ((wsApplyEvents srv os c out evs).2.1 :: rest) := by
  induction evs generalizing srv os c out with
  | nil => exact h
  | cons e es ih =>
    cases e with
    | text msg =>
      have hk := stepOneUnit_unique srv os c (L4Factoidal.XMPP.WebSocket.unitOfMessage msg) rest h
      simp only [wsApplyEvents]
      cases hr : stepOneUnit srv os c (L4Factoidal.XMPP.WebSocket.unitOfMessage msg) with
      | mk a b =>
        obtain ⟨b1, b2⟩ := b
        rw [hr] at hk
        simp only
        split
        · exact hk
        · exact ih a b1 b2 _ hk
    | ping p => exact ih srv os c _ h
    | close _ =>
      have hk := endStream_unique srv os c rest h
      simp only [wsApplyEvents]
      cases hr : endStream srv os c with
      | mk a b =>
        obtain ⟨b1, b2⟩ := b
        rw [hr] at hk
        exact hk
    | fail code _ =>
      have hk := endStream_unique srv os c rest h
      simp only [wsApplyEvents]
      cases hr : endStream srv os c with
      | mk a b =>
        obtain ⟨b1, b2⟩ := b
        rw [hr] at hk
        exact hk

/-- 6. One WebSocket read: the handshake, then the events. -/
theorem wsFeedPure_unique (srv : XmppOpenServer) (ws : XmppWsSession) (bytes : ByteArray)
    (rest : List XmppOpenSession) (h : Unique srv (ws.inner :: rest)) :
    Unique (wsFeedPure srv ws bytes).1 ((wsFeedPure srv ws bytes).2.1.inner :: rest) := by
  unfold wsFeedPure
  repeat' first | split | dsimp only
  all_goals first
    | exact h
    | exact wsApplyEvents_unique _ _ _ _ _ rest h

/-- 7. The whole-message transport of the in-page server. -/
theorem msgFeedPure_unique (srv : XmppOpenServer) (os : XmppOpenSession) (msg : String)
    (rest : List XmppOpenSession) (h : Unique srv (os :: rest)) :
    Unique (msgFeedPure srv os msg).1 ((msgFeedPure srv os msg).2.1 :: rest) := by
  unfold msgFeedPure
  split
  · exact h
  · have hk := stepOneUnit_unique srv os {} (L4Factoidal.XMPP.WebSocket.unitOfMessage msg) rest h
    cases hr : stepOneUnit srv os {} (L4Factoidal.XMPP.WebSocket.unitOfMessage msg) with
    | mk a b =>
      obtain ⟨b1, b2⟩ := b
      rw [hr] at hk
      exact hk

/-- 8. A new session holds nothing. -/
theorem Unique.opened {srv : XmppOpenServer} {oss : List XmppOpenSession} (h : Unique srv oss)
    (os : XmppOpenSession) (hn : os.liveFull = none) : Unique srv (os :: oss) :=
  h.congr rfl (by simp [liveFulls, hn])

/-- 9. A closed handle: a live session goes through `sessionGone` (`sessionClosed`), and its full
JID is free. -/
theorem sessionGone_unique (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected)
    (rest : List XmppOpenSession) (f : String) (ha : os.liveFull = some f)
    (h : Unique srv (os :: rest)) : Unique (sessionGone srv c f).1 rest := by
  obtain ⟨hn, hp⟩ := h
  simp only [liveFulls, List.filterMap_cons, ha] at hp
  rw [Unique, sessionGone_bound]
  exact ⟨hn.erase f, by simpa [liveFulls] using hp.erase f⟩

/-- 10. A session that holds nothing closes, and nothing changes. -/
theorem Unique.closed {srv : XmppOpenServer} {os : XmppOpenSession} {rest : List XmppOpenSession}
    (h : Unique srv (os :: rest)) (hn : os.liveFull = none) : Unique srv rest :=
  h.congr rfl (by simp [liveFulls, hn])

def xmppMsgJson (os : XmppOpenSession) (c : XmppCollected) (msgs : List String) : String :=
  okWith ((jsonOfCollected os c).filter (fun (k, _) => k != "send" && k != "bufferedBytes") ++
    [("send", .array (msgs.map .string))])

/-- `xmppMsgOpen(serverHandle, {"streamId","nonce","maxUnits"?})`. -/
def xmppMsgOpen (server optionsJson : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    match parseJson (if optionsJson.trim.isEmpty then "{}" else optionsJson) with
    | .error e => pure (errJson s!"options: {toString e}")
    | .ok j =>
      match j.getString? "streamId", j.getString? "nonce" with
      | some streamId, some nonce =>
        if streamId.isEmpty || nonce.isEmpty then
          pure (errJson "xmppMsgOpen: \"streamId\" and \"nonce\" must not be empty")
        else
          let cfg := srv.sessionConfig streamId nonce false false
          let n ← xmppMsgCounter.modifyGet fun n => (n + 1, n + 1)
          let h := s!"xmppmsg{n}"
          xmppMsgSessions.modify (·.insert h
            { server, session := Session.init cfg, buffer := "", units := 0
              maxUnits := (natField? j "maxUnits").getD 1000000, closed := false })
          pure (okWith [("handle", .string h)])
      | _, _ => pure (errJson "xmppMsgOpen: \"streamId\" and \"nonce\" are required (the host supplies unpredictable values)")

/-- `xmppMsgFeed(handle, message)`: one whole message; `send` is the whole
messages to give back, in order. -/
def xmppMsgFeed (h msg : String) : IO String := do
  match (← xmppMsgSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP message session handle: {h}")
  | some os =>
    match (← xmppServers.get)[os.server]? with
    | none => pure (unknownXmppServer os.server)
    | some srv =>
      let (srv', os', c, msgs) := msgFeedPure srv os msg
      xmppServers.modify (·.insert os.server srv')
      xmppMsgSessions.modify (·.insert h os')
      pure (xmppMsgJson os' c msgs)

/-- `xmppMsgDeliver(handle, text)`: a stanza routed to this session, as one
message; refused (`delivered:false`) unless the session is bound. -/
def xmppMsgDeliver (h text : String) : IO String := do
  match (← xmppMsgSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP message session handle: {h}")
  | some os =>
    if os.closed || !os.session.canDeliver then
      pure (okWith [("delivered", .bool false), ("send", .array [])])
    else
      let sends := (Server.deliver os.session text).filterMap (fun o =>
        match o with | .send t => some t | _ => none)
      pure (okWith [("delivered", .bool true),
        ("send", .array (sends.map (fun t => .string (L4Factoidal.XMPP.WebSocket.messageOfSend os.session.cfg t))))])

/-- `xmppMsgClose(handle)`: release the handle; `<close/>` when the stream
was open, and the deliveries of leaving every MUC room. -/
def xmppMsgClose (h : String) : IO String := do
  match (← xmppMsgSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP message session handle: {h}")
  | some os =>
    xmppMsgSessions.modify (·.erase h)
    let left ← sessionClosed os
    let closing : List String :=
      if os.closed || os.session.stage == .closed then [] else [L4Factoidal.XMPP.WebSocket.closeText]
    pure (okWith [("send", .array (closing.map .string)), ("routeFull", left)])

/-- `xmppStateLoad(serverHandle, path, text)`: at start, install one item the
host read from the server's LWS state storage (issue 1237): a roster, the
stanzas held for an account, a MIX channel or a GC3 group, decoded by
`XMPP/StateCodec.lean` (round-trip theorems there). An item that does not
decode, or names a service this server does not run, is REFUSED with a
reason: the host stops the start rather than run on a partial state. -/
def xmppStateLoad (server path text : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    match path.splitOn "/" with
    | ["", "xmpp", kind, segment] =>
      match (StateCodec.segmentOf segment).bind (fun (hex, seq) => (StateCodec.nameOfHex hex).map (·, seq)) with
      | none => pure (errJson s!"xmppStateLoad: {path}: the name is not hex of UTF-8")
      | some (name, seq) =>
        let install (srv' : XmppOpenServer) : IO String := do
          xmppServers.modify (·.insert server srv')
          pure (okWith [("loaded", .string kind)])
        match kind with
        | "roster" => install { srv with rosters := srv.rosters.insert name (rosterDecode text) }
        | "held" =>
          match StateCodec.decodeHeld text with
          | some q =>
            -- An item for a name that is no account is not loaded, and the host deletes it.
            if !srv.cfg.isAccountBare name then pure (okWith [("loaded", .string kind), ("stale", .bool true)])
            -- A numbered item is one stanza; an unnumbered resource is a queue of an older run.
            else install { srv with held := q.foldl (fun h t => Held.restore h ⟨name, seq.getD 0, t⟩) srv.held }
          | none => pure (errJson s!"xmppStateLoad: {path}: not a held queue")
        | "mix" =>
          match srv.mix, StateCodec.decodeChannel text with
          | some svc, some ch => install { srv with mix := some (svc.put ch) }
          | none, _ => pure (errJson s!"xmppStateLoad: {path}: this server runs no MIX service")
          | _, none => pure (errJson s!"xmppStateLoad: {path}: not a MIX channel")
        | "gc3" =>
          match srv.gc3, StateCodec.decodeGroup text with
          | some svc, some g => install { srv with gc3 := some (svc.put g) }
          | none, _ => pure (errJson s!"xmppStateLoad: {path}: this server runs no GC3 service")
          | _, none => pure (errJson s!"xmppStateLoad: {path}: not a GC3 group")
        | "muc" =>
          match StateCodec.decodeAcl text, srv.muc with
          | none, _ => pure (errJson s!"xmppStateLoad: {path}: not a MUC room's affiliations")
          -- Without an owner configuration nothing of a room is kept, so this item is not used. It
          -- is not deleted either: an operator who takes the flag away for one start keeps the bans.
          | some _, none => pure (okWith [("loaded", .string kind)])
          | some a, some svc =>
            if svc.firstOwner then pure (okWith [("loaded", .string kind)])
            else install { srv with muc := some { svc with acls := svc.acls.filter (·.room != a.room) ++ [a] } }
        | _ => pure (errJson s!"xmppStateLoad: {path}: unknown kind {kind}")
    | _ => pure (errJson s!"xmppStateLoad: {path}: not /xmpp/<kind>/<hex>")

/-- The op names this module serves, through `callIO` only. -/
def xmppSessionOpNames : List String :=
  [ "xmppOpen", "xmppClose"
  , "xmppSessionOpen", "xmppSessionFeed", "xmppSessionDeliver", "xmppSessionPing", "xmppSessionClose"
  , "xmppSessionTlsUp", "xmppRosterGet", "xmppRosterSet", "xmppWsOpen", "xmppStateLoad", "xmppClock", "xmppVerifier"
  , "xmppMsgOpen", "xmppMsgFeed", "xmppMsgDeliver", "xmppMsgClose" ]


end L4Wasm.Ops
