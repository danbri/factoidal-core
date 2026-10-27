/-
Wasm.Ops.Authz — handles of the authorization server component
(https://github.com/danbri/factoidal/issues/916). Design record:
`docs/designissues/2026-10-22-authorization-server.md`; the protocol is
`L4Factoidal/Authz/`.

  authzOpen(configJson)
    -> {"ok":true,"handle":"authz1","issuer":I,"resources":[R],"jwks":SET,"kid":K,"changed":B}
  authzStep(handle, requestJson)
    -> {"ok":true,"response":{status,headers,body},"changed":B}
     | {"ok":true,"resolve":{"host":H},"changed":B}
     | {"ok":true,"fetch":{"url":U,"accept":A,"address":X},"changed":B}
  authzFetched(handle, {"url","status","body","now"} | {"host","addresses","now"})
    -> {"ok":true}
  authzKeys(handle, {"nonce"?, "private"?})
    -> {"ok":true,"keys":DOC} | {"ok":true,"jwks":{"keys":[private JWKs]}}
  authzRotate(handle, {"now","random"})
    -> {"ok":true,"changed":true,"kid":K}
  authzOwns(handle, target)
    -> {"ok":true,"owns":B}
  authzClose(handle) -> {"ok":true}

Config members: `issuer` (required), `resources` (array), `alg` (`ES256`
default, or `EdDSA`), `tokenLifetime` (1..300, default 300), `leeway`,
`rotateAfter`, `allowHttp`, `allowPrivateFetch`, `docTtl`, `cors` (absent or
`true`: echo the request Origin; `false`; or a list of origins: issue 923),
`tokenPath` and `jwksPath` (relative to the issuer, default `/token` and
`/jwks`), `mountedOn` (in place of `issuer`: the root IRI of the LWS storage
that shares this issuer; sets the issuer, the resource (or `audience`) and
the two paths, `L4Factoidal/Authz/Mount.lean`), `now`, `entropy`
(base64, at least 64 bytes: two private key candidates for a new key
store), `keys` (the key file document, clear or sealed), `storageKey` (the
`FACTOIDAL_LWS_KEY` text: the key file is sealed under it, as the LWS
snapshot is, `L4Factoidal/LWS/SnapshotSeal.lean`).

A request document is the LWS one (`requestOfJson`: method, target,
headers, body) plus `now` and `random` (base64, at least 112 bytes from the
host's random source). `changed: true` means the keys changed and the host
writes `authzKeys` to the key file.

`authzOwns` answers whether a request target is one of this server's paths
(`L4Factoidal.Authz.owns`): a host that serves this server and a storage on
one port (`lws-serve --authz`) asks it for each request.

`private: true` in `authzKeys` gives the private JWKs of the published keys.
It exists for the conformance harness (Touchstone's `as.signingKey`); the
CLI prints it only for `factoidal authz-keys DIR --private`. The HTTP
interface never serves it (`jwks_no_private_member`).
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import Wasm.Ops.Lws
import L4Factoidal.Authz.Server
import L4Factoidal.Authz.Mount
import L4Factoidal.LWS.SnapshotSeal

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Authz
open L4Factoidal.HTTP (Request Response)

/-- One open authorization server. -/
structure OpenAuthz where
  cfg : AuthzConfig
  st : AuthzState
  storageKey : Option ByteArray := none
  clock : Nat := 0

initialize authzCounter : IO.Ref Nat ← IO.mkRef 0
initialize authzTable : IO.Ref (Std.HashMap String OpenAuthz) ← IO.mkRef ∅

def unknownAuthzHandle (h : String) : String := errJson s!"unknown authorization server handle: {h}"

private def natOf? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number s) => s.toNat?
  | _ => none

private def bytesOf? (j : Json) (k : String) : Option ByteArray :=
  (j.getString? k).bind L4Factoidal.LWS.Base64.decode?

/-- The issuer identifier: `http(s)`, no query, no fragment, no trailing
slash. -/
def issuerOk? (s : String) : Except String String :=
  let t := trimSlash s
  if !(t.startsWith "https://" || t.startsWith "http://") then
    .error "authz: issuer must be an http or https IRI"
  else if (t.splitOn "?").length > 1 || (t.splitOn "#").length > 1 then
    .error "authz: issuer must have no query and no fragment"
  else .ok t

/-- The storage key text: none when absent or empty. -/
def storageKeyOf? : Option String → Except String (Option ByteArray)
  | none => .ok none
  | some t =>
      if t.trimAscii.toString == "" then .ok none
      else (L4Factoidal.LWS.Seal.parseStorageKey t).map some

/-- An endpoint path relative to the issuer: absent gives the default; it
begins with a slash, is longer than one, and has no query, fragment, empty or
dot segment. -/
def endpointPathOf? (j : Json) (k dflt : String) : Except String String :=
  match j.field? k with
  | none => .ok dflt
  | some (.string p) =>
      let segs := (p.drop 1).toString.splitOn "/"
      if p.startsWith "/" && p.length > 1 && !p.contains '?' && !p.contains '#'
          && segs.all (fun s => s != "" && s != "." && s != "..") then .ok p
      else .error s!"authz: {k} must be a path such as /token (no query, fragment, empty or dot segment)"
  | some _ => .error s!"authz: {k} must be a string"

/-- Read the configuration and open the key store. -/
def openAuthzOfJson (text : String) : Except String (OpenAuthz × Bool) := do
  let j ← match parseJson text with
    | .ok j => .ok j
    | .error e => .error s!"authz: config is not JSON: {toString e}"
  -- `mountedOn`: the storage root IRI of an LWS storage that shares this
  -- issuer (`L4Factoidal.Authz.mountedOn`, `lws-serve --authz`).
  let mounted? := j.getString? "mountedOn"
  let issuer ← match mounted?, j.getString? "issuer" with
    | some _, some _ => .error "authz: give \"issuer\" or \"mountedOn\", not both"
    | some b, none => issuerOk? (trimSlash b)
    | none, some i => issuerOk? i
    | none, none => .error "authz: member \"issuer\" is required"
  let resources := (j.getArray? "resources").getD [] |>.filterMap Json.asString?
  let alg ← match j.getString? "alg" with
    | none => .ok SigAlg.es256
    | some a => (SigAlg.ofString? a).elim (.error s!"authz: alg {a} is not ES256 or EdDSA") .ok
  let lifetime := (natOf? j "tokenLifetime").getD 300
  if lifetime == 0 || lifetime > 300 then
    throw "authz: tokenLifetime must be 1 to 300 seconds (lws10-core: RECOMMENDED 300 seconds or less)"
  let flag (k : String) : Bool := (j.getBool? k).getD false
  -- CORS (issue 923): absent or true echoes the request Origin, false turns
  -- it off, a list names the origins.
  let cors ← L4Factoidal.HTTP.Cors.policyOfJson (j.field? "cors")
  let tokenPath ← endpointPathOf? j "tokenPath" "/token"
  let jwksPath ← endpointPathOf? j "jwksPath" "/jwks"
  if tokenPath == jwksPath then throw "authz: tokenPath and jwksPath must differ"
  let cfg : AuthzConfig :=
    { issuer, resources, alg, tokenLifetime := lifetime
      leeway := (natOf? j "leeway").getD 60
      rotateAfter := (natOf? j "rotateAfter").getD 0
      fetch := { allowHttp := flag "allowHttp", allowPrivateFetch := flag "allowPrivateFetch"
                 docTtl := (natOf? j "docTtl").getD 60 }
      cors, tokenPath, jwksPath }
  let cfg := match mounted? with
    | some b =>
        let base := if b.endsWith "/" then b else b ++ "/"
        mountedOn cfg base ((j.getString? "audience").getD
          (L4Factoidal.LWS.iriOfPath base L4Factoidal.LWS.storagePath))
    | none => cfg
  let now := (natOf? j "now").getD 0
  let key? ← storageKeyOf? (j.getString? "storageKey")
  let doc? ← L4Factoidal.LWS.Seal.openSnapshot L4Factoidal.LWS.Seal.hacl key? (j.field? "keys")
  match doc? with
  | some d =>
      let ks ← keyStoreOfDoc hacl d
      if ks.current?.isNone then
        throw "authz: the key file holds no current key"
      pure ({ cfg, st := { keys := ks }, storageKey := key?, clock := now }, false)
  | none =>
      let e ← (bytesOf? j "entropy").elim
        (.error "authz: a new key store needs \"entropy\" (base64, 64 bytes from the host)") .ok
      if e.size < 64 then throw "authz: entropy must be at least 64 bytes"
      let k ← (mkKeyFirst hacl alg now [e.extract 0 32, e.extract 32 64]).elim
        (.error "authz: the primitive refused both key candidates") .ok
      pure ({ cfg, st := { keys := { keys := [k] } }, storageKey := key?, clock := now }, true)

def authzOpen (configJson : String) : IO String := do
  match openAuthzOfJson configJson with
  | .error e => pure (errJson e)
  | .ok (oa, changed) =>
      let n ← authzCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"authz{n}"
      authzTable.modify (·.insert h oa)
      pure (okWith [ ("handle", .string h), ("issuer", .string oa.cfg.issuer)
                   , ("resources", .array (oa.cfg.resources.map Json.string))
                   , ("jwks", jwksJson oa.st.keys oa.clock oa.cfg.grace)
                   , ("kid", .string ((oa.st.keys.current?.map (·.kid)).getD ""))
                   , ("changed", .bool changed) ])

def needJson : Need → List (String × Json)
  | .resolve host => [("resolve", .object [("host", .string host)])]
  | .fetch url accept address =>
      [("fetch", .object [("url", .string url), ("accept", .string accept), ("address", .string address)])]

def authzStep (h requestJson : String) : IO String := do
  match (← authzTable.get)[h]? with
  | none => pure (unknownAuthzHandle h)
  | some oa =>
      match parseJson requestJson with
      | .error e => pure (errJson s!"request: {toString e}")
      | .ok j =>
          match requestOfJson j with
          | .error e => pure (errJson e)
          | .ok (r, now?, _) =>
              let rnd := (bytesOf? j "random").getD ByteArray.empty
              if rnd.size < 112 then
                pure (errJson "request: member \"random\" (base64, 112 bytes from the host) is required")
              else
                let now := now?.getD oa.clock
                let r := { r with path := (r.path.splitOn "?").headD r.path }
                let (res, st, changed) := stepCors hacl oa.cfg oa.st now rnd r
                authzTable.modify (·.insert h { oa with st, clock := now })
                pure <| match res with
                  | .respond resp => okWith [("response", jsonOfResponse resp), ("changed", .bool changed)]
                  | .need n => okWith (needJson n ++ [("changed", .bool changed)])

def authzFetched (h docJson : String) : IO String := do
  match (← authzTable.get)[h]? with
  | none => pure (unknownAuthzHandle h)
  | some oa =>
      match parseJson docJson with
      | .error e => pure (errJson s!"fetched: {toString e}")
      | .ok j =>
          let now := (natOf? j "now").getD oa.clock
          match j.getString? "url", j.getString? "host" with
          | some url, _ =>
              let st := recordFetched oa.cfg oa.st url ((natOf? j "status").getD 0)
                ((j.getString? "body").getD "") now
              authzTable.modify (·.insert h { oa with st })
              pure (okWith [])
          | none, some host =>
              let addrs := ((j.getArray? "addresses").getD []).filterMap Json.asString?
              let st := recordResolved oa.cfg oa.st host addrs now
              authzTable.modify (·.insert h { oa with st })
              pure (okWith [])
          | none, none => pure (errJson "fetched: member \"url\" or \"host\" is required")

def authzKeys (h optsJson : String) : IO String := do
  match (← authzTable.get)[h]? with
  | none => pure (unknownAuthzHandle h)
  | some oa =>
      let opts : Json := if optsJson.trimAscii.toString == "" then .object []
        else (parseJson optsJson).toOption.getD (.object [])
      if (opts.getBool? "private").getD false then
        pure (okWith [("jwks", .object [("keys", .array
          ((published oa.st.keys oa.clock oa.cfg.grace).map privateJson))])])
      else
        let nonce? := bytesOf? opts "nonce"
        match L4Factoidal.LWS.Seal.sealSnapshot L4Factoidal.LWS.Seal.hacl oa.storageKey nonce?
            (keysDoc oa.st.keys) with
        | .ok d => pure (okWith [("keys", d)])
        | .error e => pure (errJson e)

def authzRotate (h optsJson : String) : IO String := do
  match (← authzTable.get)[h]? with
  | none => pure (unknownAuthzHandle h)
  | some oa =>
      match parseJson optsJson with
      | .error e => pure (errJson s!"rotate: {toString e}")
      | .ok j =>
          let now := (natOf? j "now").getD oa.clock
          let rnd := (bytesOf? j "random").getD ByteArray.empty
          if rnd.size < 64 then pure (errJson "rotate: member \"random\" (base64, 64 bytes) is required")
          else
            match mkKeyFirst hacl oa.cfg.alg now [rnd.extract 0 32, rnd.extract 32 64] with
            | none => pure (errJson "rotate: the primitive refused both key candidates")
            | some k =>
                let st := { oa.st with keys := rotateWith oa.st.keys k now oa.cfg.grace }
                authzTable.modify (·.insert h { oa with st, clock := now })
                pure (okWith [("changed", .bool true), ("kid", .string k.kid)])

def authzOwns (h target : String) : IO String := do
  match (← authzTable.get)[h]? with
  | none => pure (unknownAuthzHandle h)
  | some oa => pure (okWith [("owns", .bool (owns oa.cfg target))])

def authzClose (h : String) : IO String := do
  let t ← authzTable.get
  if t.contains h then
    authzTable.set (t.erase h)
    pure (okWith [])
  else pure (unknownAuthzHandle h)

def authzOpNames : List String :=
  ["authzOpen", "authzStep", "authzFetched", "authzKeys", "authzRotate", "authzOwns", "authzClose"]

end L4Wasm.Ops
