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

/-- `user:password` lines, the accounts-file format of the harness
(`Harness.XmppServe.parseAccounts`), accepted here as `accountsText` so one
file serves both hosts. -/
private def accountsOfText (text : String) : List Account :=
  (text.splitOn "\n").filterMap (fun line =>
    let l := line.trim
    if l.isEmpty || l.startsWith "#" then none
    else match l.splitOn ":" with
      | u :: rest => if u.isEmpty then none else some ⟨u, String.intercalate ":" rest⟩
      | [] => none)

/-- `accounts`: an array of `{"username","password"}` objects. -/
private def accountsOfArray (items : List Json) : List Account :=
  items.filterMap (fun it =>
    match it.getString? "username", it.getString? "password" with
    | some u, some p => if u.isEmpty then none else some ⟨u, p⟩
    | _, _ => none)

/-- `mucMembers`: an array of `{"room","members":[bare JID]}` objects. `none` when
an entry is malformed: a room whose list was lost would be open to everyone. -/
private def mucMembersOfArray (items : List Json) : Option (List Muc.MemberList) :=
  items.mapM (fun it =>
    match it.getString? "room", it.getArray? "members" with
    | some room, some members =>
      if room.isEmpty then none
      else (members.mapM (fun m => match m with | Json.string s => some s | _ => none)).map (Muc.MemberList.mk room)
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
  /-- XEP-0369 MIX service domain, from `"mixDomain"`; none: no MIX. -/
  mixDomain : Option String := none
  /-- GC3 prototype service domain, from `"gc3Domain"`; none: no GC3. -/
  gc3Domain : Option String := none
  /-- Does the host keep this server's state across restarts (`"persist": true`,
  set with a state key)? Only then does a feed answer carry `store`/`unstore`. -/
  persist : Bool := false
  /-- The failed SASL login limit (on unless `disableRateLimits`). -/
  limits : L4Factoidal.Net.LoginLimit.Limits := {}
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
      let fromArray := (j.getArray? "accounts").map accountsOfArray
      let fromText := (j.getString? "accountsText").map accountsOfText
      let accounts := (fromArray.getD []) ++ (fromText.getD [])
      -- RFC 5802 section 5.1 salt and RFC 7677 section 3 iteration count.
      -- The default salt is the one `Harness/XmppServe.lean` fixes per
      -- deployment, so a transcript recorded against the harness replays
      -- here byte for byte.
      let saltB64 := (j.getString? "saltB64").getD "W22ZaJ0SNY7soEsUEjb6gQ=="
      let iterationCount := (natField? j "iterationCount").getD 4096
      let mucDomain := j.getString? "mucDomain"
      let mixDomain := j.getString? "mixDomain"
      let gc3Domain := j.getString? "gc3Domain"
      let mucMembers := (j.getArray? "mucMembers").map mucMembersOfArray
      if mucMembers == some none then .error "config: \"mucMembers\" needs {\"room\",\"members\"} objects"
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
        .ok { domain, saltB64, iterationCount, accounts, heldCaps, senderLimits,
              saltSeed := (j.getString? "saltSeed").getD "",
              tlsCarrier := (j.getBool? "tlsCarrier").getD false, mucDomain, mixDomain, gc3Domain,
              mucMembers := (mucMembers.bind id).getD [],
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
  /-- The full JIDs of this server's bound sessions, kept by the ops layer
  (`bindTransition`, `sessionGone`), so the hold-or-deliver decision is made
  here, not in the host. -/
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
      ({ srv with muc := some svc' },
       { c with routeFull := c.routeFull ++ ds.map (fun d => (d.to, d.render, none)) })
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
      ({ srv with rosters := srv.rosters.insert bare (rosterDecode encoded) },
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

/-- A session's full JID changed by one step (it bound, or it closed): keep
`bound`, and hand a newly bound account what was held for it, oldest first. -/
def bindTransition (srv : XmppOpenServer) (c : XmppCollected) (before after : Option String) :
    XmppOpenServer × XmppCollected :=
  if before == after then (srv, c)
  else
    let kept := srv.bound.filter (fun f => some f != before)
    match after with
    | none => ({ srv with bound := kept }, c)
    | some f =>
      let bare := Server.bareOf f
      let (out, h') := Held.release srv.held bare
      ({ srv with bound := kept ++ [f], held := h' },
       { c with route := c.route ++ out.map (fun i => (bare, i.text)),
                -- The older one-resource form too: it may be there, and a delete of nothing is nothing.
                unstore := if out.isEmpty || !srv.cfg.persist then c.unstore
                  else c.unstore ++ [StateCodec.pathOf "held" bare] ++ out.map (fun i => StateCodec.heldItemPath bare i.seq) })

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
          let (srv', c') := performAll os.session.bareJid srv c
            (Server.streamError "policy-violation" "too many stream units")
          (srv', { os with buffer := rest, closed := true }, { c' with close := true })
        else
          let roster := match os.session.bareJid with
            | some b => srv.rosters.getD b []
            | none => []
          let (s', env', outs) := Server.step os.session { roster, guard := srv.guardFor os } unit
          let (srv', c') := performAll os.session.bareJid
            { srv with failures := env'.guard.failures, backoff := env'.guard.backoff } c outs
          let (srv'', c'') := bindTransition srv' c' os.session.fullJid s'.fullJid
          let closed := c''.close || s'.stage == .closed
          drain srv''
            { os with session := s', buffer := bufferAfter outs rest, units := os.units + 1, closed }
            c'' fuel

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
  , ("full", jsonOfOptString os.session.fullJid) ]

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
      let credentials := cfg.accounts.filterMap (fun a =>
        (Scram.credentialsOfPassword a.password (probe.saltFor a.username) cfg.iterationCount).map (a.username, ·))
      let cfg := { cfg with credentials }
      let muc : Option Muc.Service := cfg.mucDomain.map (fun d => { domain := d, memberLists := cfg.mucMembers })
      let mix : Option Mix.Service := cfg.mixDomain.map (fun d => { domain := d })
      let gc3 : Option Gc3.Service := cfg.gc3Domain.map (fun d => { domain := d })
      xmppServers.modify (·.insert h { cfg := cfg, rosters := ∅, presence := ∅, muc := muc, mix := mix, gc3 := gc3,
                                       held := { caps := cfg.heldCaps } })
      pure (okWith [ ("handle", .string h)
                   , ("domain", .string cfg.domain)
                   , ("accounts", .number (toString cfg.accounts.length))
                   , ("mucMembers", .number (toString cfg.mucMembers.length))
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

/-- A session went away: it leaves every room it was in (XEP-0045 section
7.14), and the other occupants are told. The deliveries, as `routeFull`
JSON, for the host to perform. -/
def mucLeaveAll (server : String) (full : Option String) : IO Json := do
  -- The session is gone: it is no longer a delivery target.
  match full, (← xmppServers.get)[server]? with
  | some f, some srv0 =>
    let srv := { srv0 with bound := srv0.bound.filter (· != f) }
    xmppServers.modify (·.insert server srv)
    match srv.muc with
    | some svc =>
      let (svc', ds) := Muc.leaveAll svc f
      xmppServers.modify (·.insert server { srv with muc := some svc' })
      pure (.array (ds.map (fun d => .object [("to", .string d.to), ("text", .string d.render), ("bounce", .null)])))
    | none => pure (.array [])
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
    let left ← mucLeaveAll os.server os.session.fullJid
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
  else if os.units ≥ os.maxUnits then
    let (srv', c') := performAll os.session.bareJid srv c (Server.streamError "policy-violation" "too many stream units")
    (srv', { os with closed := true }, { c' with close := true })
  else
    let roster := match os.session.bareJid with
      | some b => srv.rosters.getD b []
      | none => []
    let (s', env', outs) := Server.step os.session { roster, guard := srv.guardFor os } unit
    let (srv', c') := performAll os.session.bareJid
      { srv with failures := env'.guard.failures, backoff := env'.guard.backoff } c outs
    let (srv'', c'') := bindTransition srv' c' os.session.fullJid s'.fullJid
    (srv'', { os with session := s', units := os.units + 1, closed := c''.close || s'.stage == .closed }, c'')

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
      (srv, { os with closed := true }, { c with close := true },
       out ++ L4Factoidal.HTTP.WebSocket.closeFrame 1000, true)
    | .fail code _ =>
      (srv, { os with closed := true }, { c with close := true },
       out ++ L4Factoidal.HTTP.WebSocket.closeFrame code, true)

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

/-- `xmppWsClose(handle)`: release the handle. OUT region: `<close/>` and
a close frame when the stream was open (RFC 7395 section 3.6). -/
def xmppWsCloseWith (h : String) : IO (String × ByteArray) := do
  match (← xmppWsSessions.get)[h]? with
  | none => pure (errJson s!"unknown XMPP WebSocket session handle: {h}", ByteArray.empty)
  | some ws =>
    xmppWsSessions.modify (·.erase h)
    let left ← mucLeaveAll ws.inner.server ws.inner.session.fullJid
    match ws.phase with
    | .frames .. =>
      if ws.inner.closed then pure (okWith [("routeFull", left)], ByteArray.empty)
      else pure (okWith [("routeFull", left)], wsFramesOf ws.inner.session.cfg [Server.streamCloseText] ++
                          L4Factoidal.HTTP.WebSocket.closeFrame 1000)
    | _ => pure (okWith [("routeFull", left)], ByteArray.empty)

def xmppWsBlobIoOpNames : List String := ["xmppWsFeed", "xmppWsDeliver", "xmppWsClose"]

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
    let left ← mucLeaveAll os.server os.session.fullJid
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
        | _ => pure (errJson s!"xmppStateLoad: {path}: unknown kind {kind}")
    | _ => pure (errJson s!"xmppStateLoad: {path}: not /xmpp/<kind>/<hex>")

/-- The op names this module serves, through `callIO` only. -/
def xmppSessionOpNames : List String :=
  [ "xmppOpen", "xmppClose"
  , "xmppSessionOpen", "xmppSessionFeed", "xmppSessionDeliver", "xmppSessionClose"
  , "xmppSessionTlsUp", "xmppRosterGet", "xmppRosterSet", "xmppWsOpen", "xmppStateLoad", "xmppClock"
  , "xmppMsgOpen", "xmppMsgFeed", "xmppMsgDeliver", "xmppMsgClose" ]


end L4Wasm.Ops
