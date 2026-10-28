/-
Wasm.Ops.XmppClient — the outgoing XMPP CLIENT stream as a handle, with
HTTP over XMPP (XEP-0332) served from it
(https://github.com/danbri/factoidal/issues/1107, step 1: `factoidal
webdav-serve CONFIGDIR --xmpp JID`).

  xmppClientOpen(configJson)
    configJson: {"jid":"bob@example.org","password":"…","resource":"dav",
                 "clientNonce":"…","allow":["alice@example.org",…],
                 "host":"xmpp.example.org","tls":true,
                 "mounts":[…the ready.mounts of webdavLoad…],
                 "dangerouslyAllowWritableWithoutLogin"?:bool,
                 "inlineLimit"?:N,"chunkSize"?:N,"minIterations"?:N}
    -> {"ok":true,"handle":"xmppc1","domain":"example.org","host":"…","tls":bool,
        "writableWithoutLogin":[NAME,…],"send":[streamHeader]}
     | {"ok":false,"error":"xmppClientOpen: …"}   (`xcStartRefusal`)
  xmppClientFeed(handle, text)
    -> {"ok":true,"send":[…],"requests":[{"id","method","target","headers",
        "bodyBase64"},…],"bound":jid|null,"close":bool,"reason":s|null,
        "stage":"…","bufferedBytes":N}
  xmppClientAnswer(handle, requestId, responseJson)
    responseJson: {"status":N,"headers":[[name,value],…],"bodyBase64":"…"}
    -> {"ok":true,"send":[…]}
  xmppClientClose(handle) -> {"ok":true,"send":[…]}

Every decision is in Lean: the stream negotiation, SASL SCRAM-SHA-256 and
binding (`L4Factoidal.XMPP.ClientStream`); which stanza is an HTTP request,
the access decision, the refusals, chunk assembly and the response stanzas
(`HttpOverXmpp.plan` and `HttpOverXmpp.finish`, the two halves of the
stage 1 `step`); `service-unavailable` for an unserved IQ
(`ClientStream.answerUnserved`). The host moves bytes: it writes `send`,
closes the socket on `close`, and carries each entry of `requests` to the
WebDAV handle it already runs for HTTP (`webdavStep`/`webdavResume`, the
same `serve` function of `npm/factoidal/webdav/server.mjs`), then gives the
response to `xmppClientAnswer`. Request ids are this handle's; responses
may come back in any order (XEP-0332 allows it).

The host supplies the SCRAM client nonce (RFC 5802 section 5.1); this
module has no random source. State lives here in `IO.Ref`s, as the other
handle ops keep theirs. Targeted imports only.
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import L4Factoidal.XMPP.ClientStream
import L4Factoidal.XMPP.HttpOverXmpp
import L4Factoidal.XML.Enc

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XMPP

/-- A request handed to the host, waiting for its response. -/
structure XcPending where
  env : HttpOverXmpp.Envelope
  req : HttpOverXmpp.Req

structure XcHandle where
  cfg : ClientStream.Config
  http : HttpOverXmpp.Config
  st : ClientStream.State
  hst : HttpOverXmpp.State := {}
  pending : List (Nat × XcPending) := []
  serial : Nat := 0
  boundJid : Option String := none

initialize xcCounter : IO.Ref Nat ← IO.mkRef 0
initialize xcTable : IO.Ref (Std.HashMap String XcHandle) ← IO.mkRef ∅

def unknownXc (h : String) : String := errJson s!"unknown XMPP client handle: {h}"

private def xcNat? (j : Json) (key : String) : Option Nat :=
  match j.field? key with
  | some (.number s) => s.toNat?
  | _ => none

private def xcStrs (xs : List String) : Json := .array (xs.map Json.string)

private def xcHeadersJ (hs : List (String × String)) : Json :=
  .array (hs.map (fun (n, v) => .array [.string n, .string v]))

private def xcHeadersOf (j : Json) : List (String × String) :=
  ((j.getArray? "headers").getD []).filterMap (fun it =>
    match it with
    | .array [.string n, .string v] => some (n, v)
    | _ => none)

private def xcSends (outs : List ClientStream.Out) : List String :=
  outs.filterMap (fun o => match o with | .send t => some t | _ => none)

/-- Why the WebDAV target may not start over XMPP, or `none`
(https://github.com/danbri/factoidal/issues/1120 and
https://github.com/danbri/factoidal/issues/1125). The JID allow list is the
only access control on this path (`HttpOverXmpp.step` runs `WebDAV.handle`,
and a local mount acts as the storage owner), so:

* the allow list is not empty, and each entry is a bare JID (no resource);
* the transport is TLS, or plain TCP to a literal loopback address;
* no mount is a writable local mount, unless the operator opted in with
  `--dangerously-allow-writable-without-login` (no login exists on this
  path yet: https://github.com/danbri/factoidal/issues/1125). -/
def xcStartRefusal (allow : List String) (tls : Bool) (host : String)
    (writableLocal : List String) (optIn : Bool) : Option String :=
  if allow.isEmpty then some "the allow list is empty: give --xmpp-allow JID[,JID]"
  else match allow.find? (fun a => match Jid.parse a with
      | some j => j.resourcepart.isSome
      | none => true) with
  | some a => some s!"the allow list holds only bare JIDs (no resource): {a}"
  | none =>
  if !tls && !ClientStream.isLoopbackHost host then
    some s!"plain TCP to {host} is refused: use --xmpp-tls (direct TLS), or a loopback address"
  else if !writableLocal.isEmpty && !optIn then
    some s!"writable local mounts ({", ".intercalate writableLocal}) would be open to every allowed JID with no login; make them read-only, or start with --dangerously-allow-writable-without-login"
  else none

#guard xcStartRefusal [] true "h" [] false == some "the allow list is empty: give --xmpp-allow JID[,JID]"
#guard (xcStartRefusal ["alice@example.org/phone"] true "h" [] false).isSome
#guard (xcStartRefusal ["alice@example.org"] false "xmpp.example.org" [] false).isSome
#guard (xcStartRefusal ["alice@example.org"] false "127.0.0.1" [] false).isNone
#guard (xcStartRefusal ["alice@example.org"] true "xmpp.example.org" ["notes"] false).isSome
#guard (xcStartRefusal ["alice@example.org"] true "xmpp.example.org" ["notes"] true).isNone

/-- `xmppClientOpen(configJson)`. -/
def xmppClientOpen (configJson : String) : IO String := do
  match parseJson configJson with
  | .error e => pure (errJson s!"xmppClientOpen: the configuration is not JSON: {toString e}")
  | .ok j =>
    let jidText := (j.getString? "jid").getD ""
    match Jid.parse jidText with
    | none => pure (errJson s!"xmppClientOpen: \"jid\" is not a JID: {jidText}")
    | some jid =>
    match jid.localpart with
    | none => pure (errJson "xmppClientOpen: \"jid\" needs a local part (an account)")
    | some user =>
    let password := (j.getString? "password").getD ""
    let nonce := (j.getString? "clientNonce").getD ""
    if password.isEmpty then return errJson "xmppClientOpen: \"password\" is required"
    if nonce.length < 16 || nonce.contains ',' then
      return errJson "xmppClientOpen: \"clientNonce\" must be at least 16 characters with no comma"
    let resource := (j.getString? "resource").getD (jid.resourcepart.getD "factoidal")
    let allow := ((j.getArray? "allow").getD []).filterMap Json.asString?
    let tls := (j.getBool? "tls").getD false
    let host := (j.getString? "host").getD jid.domainpart
    -- `mounts`: the `ready.mounts` of `webdavLoad`, passed unread by the host.
    let writableLocal := ((j.getArray? "mounts").getD []).filterMap (fun m =>
      if m.getString? "kind" == some "local" && m.field? "writable" == some (.bool true)
      then m.getString? "name" else none)
    let optIn := (j.getBool? "dangerouslyAllowWritableWithoutLogin").getD false
    if let some why := xcStartRefusal allow tls host writableLocal optIn then
      return errJson s!"xmppClientOpen: {why}"
    let base : ClientStream.Config :=
      { user, domain := jid.domainpart, resource, password, clientNonce := nonce
        secureTransport := tls || ClientStream.isLoopbackHost host }
    let cfg := match xcNat? j "minIterations" with
      | some m => { base with minIterations := m }
      | none => base
    let http0 : HttpOverXmpp.Config := { allow }
    let http := { http0 with
      inlineLimit := (xcNat? j "inlineLimit").getD http0.inlineLimit
      chunkSize := (xcNat? j "chunkSize").getD http0.chunkSize }
    let (st, outs) := ClientStream.start cfg
    let n ← xcCounter.modifyGet (fun c => (c + 1, c + 1))
    let h := s!"xmppc{n}"
    xcTable.modify (·.insert h { cfg, http, st })
    pure (okWith [("handle", .string h), ("domain", .string jid.domainpart), ("host", .string host),
                  ("tls", .bool tls), ("writableWithoutLogin", xcStrs (if optIn then writableLocal else [])),
                  ("send", xcStrs (xcSends outs))])

/-- One incoming stanza after binding: an HTTP request for the host, the
stanzas to send now, or `service-unavailable`. -/
private def xcStanza (hd : XcHandle) (text : String) (sends : List String) (reqs : List Json) :
    XcHandle × List String × List Json :=
  match HttpOverXmpp.plan hd.http hd.hst text with
  | .answer out hst => ({ hd with hst }, sends ++ out.flatMap (fun t => xcSends (ClientStream.outgoing hd.st t)), reqs)
  | .skip => (hd, sends ++ (ClientStream.answerUnserved text).flatMap (fun t => xcSends (ClientStream.outgoing hd.st t)), reqs)
  | .serve hst env r body =>
    let id := hd.serial + 1
    let d := r.toDavWith body
    let q : Json := .object [ ("id", .number (toString id)), ("method", .string d.method)
      , ("target", .string d.target), ("headers", xcHeadersJ d.headers)
      , ("bodyBase64", .string (L4Factoidal.XML.Enc.base64 d.body)) ]
    ({ hd with hst, serial := id, pending := hd.pending ++ [(id, { env, req := r })] }, sends, reqs ++ [q])

private def xcStageName : ClientStream.Stage → String
  | .awaitHeader _ => "awaitHeader"
  | .awaitFeatures _ => "awaitFeatures"
  | .awaitChallenge _ => "awaitChallenge"
  | .awaitSuccess _ => "awaitSuccess"
  | .awaitBind => "awaitBind"
  | .bound _ => "bound"
  | .closed => "closed"

/-- `xmppClientFeed(handle, text)`. -/
def xmppClientFeed (h text : String) : IO String := do
  match (← xcTable.get)[h]? with
  | none => pure (unknownXc h)
  | some hd =>
    let (st, outs) := ClientStream.feed hd.cfg hd.st text
    let mut hd := { hd with st }
    let mut sends : List String := []
    let mut reqs : List Json := []
    let mut closeReason : Option String := none
    for o in outs do
      match o with
      | .send t => sends := sends ++ [t]
      | .bound j => hd := { hd with boundJid := some j }
      | .close r => closeReason := some r
      | .stanza t =>
        let (hd', s', r') := xcStanza hd t sends reqs
        hd := hd'
        sends := s'
        reqs := r'
    xcTable.modify (·.insert h hd)
    pure (okWith [ ("send", xcStrs sends), ("requests", .array reqs)
                 , ("bound", hd.boundJid.elim .null .string)
                 , ("close", .bool closeReason.isSome)
                 , ("reason", closeReason.elim .null .string)
                 , ("stage", .string (xcStageName hd.st.stage))
                 , ("bufferedBytes", .number (toString hd.st.buffer.utf8ByteSize)) ])

/-- `xmppClientAnswer(handle, requestId, responseJson)`. -/
def xmppClientAnswer (h idText responseJson : String) : IO String := do
  match (← xcTable.get)[h]? with
  | none => pure (unknownXc h)
  | some hd =>
    match idText.toNat? with
    | none => pure (errJson s!"xmppClientAnswer: request id is not a number: {idText}")
    | some id =>
    match hd.pending.lookup id with
    | none => pure (errJson s!"xmppClientAnswer: no request {id} is waiting")
    | some p =>
    match parseJson responseJson with
    | .error e => pure (errJson s!"xmppClientAnswer: not JSON: {toString e}")
    | .ok j =>
      let status := (xcNat? j "status").getD 0
      let body := match j.getString? "bodyBase64" with
        | some t => (L4Factoidal.XML.Enc.base64Decode? t).getD ByteArray.empty
        | none => ByteArray.empty
      let d : L4Factoidal.WebDAV.DavResponse := { status, headers := xcHeadersOf j, body }
      let (out, hst) := HttpOverXmpp.finish hd.http hd.hst p.env p.req d
      let hd := { hd with hst, pending := hd.pending.filter (·.1 != id) }
      xcTable.modify (·.insert h hd)
      pure (okWith [("send", xcStrs (out.flatMap (fun t => xcSends (ClientStream.outgoing hd.st t))))])

/-- `xmppClientClose(handle)`. -/
def xmppClientClose (h : String) : IO String := do
  match (← xcTable.get)[h]? with
  | none => pure (unknownXc h)
  | some hd =>
    let (_, outs) := ClientStream.close hd.st
    xcTable.modify (·.erase h)
    pure (okWith [("send", xcStrs (xcSends outs))])

def xmppClientOpNames : List String :=
  ["xmppClientOpen", "xmppClientFeed", "xmppClientAnswer", "xmppClientClose"]

end L4Wasm.Ops
