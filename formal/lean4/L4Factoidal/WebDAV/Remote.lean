/-
L4Factoidal.WebDAV.Remote — the storage operations through the LWS client.
https://github.com/danbri/factoidal/issues/1066

An `lws` mount is a remote LWS storage. Each storage operation is ONE
operation of the LWS client state machine (`L4Factoidal.LWS.Client`,
https://github.com/danbri/factoidal/issues/917), which names every HTTP
request (the 401 flow and the token exchange included) and ends with `done`
or `fail`; the host only carries its `fetch` requests.

This is the ONE module of the WebDAV server that uses the client's API
(`Op`, `Session`, `SelfIssued`, `TokenEntry`, the `done`/`fail` result
documents). The client is being changed at the same time
(https://github.com/danbri/factoidal/issues/1065); keeping every use here
keeps that merge to this file.

    head p    kind head
    list p    kind list (the client follows every `next` page)
    get p     kind read
    put p     kind update, precondition none, or ifNoneMatchStar (only new)
    delete p  kind delete, recursive for a container, precondition none

Credentials (mount file key `auth`):

* `did-key`: a P-256 private key in a JWK file (`key-file`). The client signs
  a self-issued credential (lws10-authn-ssi-cid) whose subject is the
  key's `did:key` (multicodec 0x1200, the compressed point, base58btc) and
  whose `kid` is `did:key:z…#z…`, which the authorization server checks
  (`Authz.SubjectToken.selfIssuedKey`). The identifier and the key id are
  the LWS client's (`LWS.Client.agentOfSecret`), so
  `LWS.Client.KeysTheorems` (the server reads back the key the client
  names) covers this mount too. A key file that does not exist is made from
  32 bytes of the host's random source (`newKey`).
* `bearer`: an access token in a file (`token-file`), sent to every URL
  under the mount's `url`.
-/
import L4Factoidal.WebDAV.Local
import L4Factoidal.WebDAV.Config
import L4Factoidal.LWS.Client.Machine
import L4Factoidal.LWS.Client.Keys
import L4Factoidal.VC.Multibase
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.WebDAV

open L4Factoidal.JSON
open L4Factoidal.LWS.Client (Op Session SelfIssued TokenEntry)

/-- The URL of a storage path under the mount's storage root (`url` ends
with `/`, a storage path starts with `/`). -/
def remoteUrl (url path : String) : String := url ++ dropS path 1

/-- The client operation of a storage operation. -/
def remoteOp (url : String) : BOp → Op
  | .head p => { kind := "head", url := remoteUrl url p }
  | .list p => { kind := "list", url := remoteUrl url p }
  | .get p => { kind := "read", url := remoteUrl url p }
  | .put p ct body onlyNew =>
    { kind := "update", url := remoteUrl url p, body, mediaType := ct
      precondition := if onlyNew then "ifNoneMatchStar" else "none" }
  | .delete p =>
    { kind := "delete", url := remoteUrl url p, recursive := p.endsWith "/", precondition := "none" }

def jHeadersOf (j : Json) : List (String × String) :=
  ((j.getArray? "headers").getD []).filterMap (fun h =>
    match h with
    | .array [.string n, .string v] => some (n, v)
    | _ => none)

def jBodyOf (j : Json) : ByteArray :=
  match j.getString? "bodyBase64" with
  | some t => (L4Factoidal.LWS.Base64.decode? t).getD ByteArray.empty
  | none => ((j.getString? "body").getD "").toUTF8

def jStatusOf (j : Json) : Nat :=
  match j.field? "status" with
  | some (.number n) => n.toNat?.getD 0
  | _ => 0

/-- The answer to a storage operation from the client's `done` document. -/
def answerOfDone (url : String) (op : BOp) (res : Json) : BAns :=
  match op with
  | .list p => answerOf url op 200 [] ByteArray.empty (some ((res.getArray? "members").getD []))
      |> fun a => { a with info := some { path := p, isColl := true } }
  | _ => answerOf url op (jStatusOf res) (jHeadersOf res) (jBodyOf res)

/-- The answer from the client's `fail` document: the storage's status
when the storage answered (`code` `status`), otherwise 0 with the client's
code (a transport failure, a refused discovery check). -/
def answerOfFail (url : String) (op : BOp) (err : Json) : BAns :=
  if err.getString? "code" == some "status" then
    answerOf url op (jStatusOf err) (jHeadersOf err) (jBodyOf err)
  else
    { status := 0, detail := "LWS client: " ++ ((err.getString? "code").getD "unknown") }

/-! ## Credentials -/

/-- The private key (`d`) of a P-256 JWK document. -/
def secretOfJwk (text : String) : Except String ByteArray := do
  let j ← match parseJson? text with
    | some j => pure j
    | none => throw "the key file is not JSON"
  if j.getString? "kty" != some "EC" || j.getString? "crv" != some "P-256" then
    throw "the key file is not a P-256 JWK (kty EC, crv P-256)"
  match (j.getString? "d").bind L4Factoidal.JOSE.Base64Url.decode with
  | some d => if d.size == 32 then pure d else throw "the key file's d is not 32 bytes"
  | none => throw "the key file has no private key (d)"

/-- A JWK document for a new private key, with its public point. -/
def jwkText (d xy : ByteArray) : String :=
  let b := L4Factoidal.JOSE.Base64Url.encode
  toStringCompact (.object [ ("kty", .string "EC"), ("crv", .string "P-256")
    , ("x", .string (b (xy.extract 0 32))), ("y", .string (b (xy.extract 32 64)))
    , ("d", .string (b d)) ]) ++ "\n"

/-- A new key from the host's random bytes: SHA-256 of a label, the bytes
and a counter, the first candidate that is a valid P-256 scalar
(`toPublic` gives a point). At most 8 tries. -/
def newKey (sha : ByteArray → ByteArray) (toPublic : ByteArray → Option ByteArray)
    (entropy : ByteArray) : Option (ByteArray × ByteArray) :=
  (List.range 8).findSome? (fun i =>
    let d := sha ("factoidal-webdav-key:".toUTF8 ++ entropy ++ (toString i).toUTF8)
    (toPublic d).map (fun xy => (d, xy)))

/-- The client session of a mount: a self-issued credential signed with the
key (`did-key`), the access token for every URL under the mount (`bearer`),
or nothing (`none`). -/
def sessionOf (m : Mount) (C : L4Factoidal.Authz.Crypto)
    (key : Option ByteArray) (token : Option String) : Except String Session :=
  match m.auth with
  | .none => .ok {}
  | .bearer =>
    match token with
    | some t => .ok { tokens := [{ storage := "", root := m.url, token := trimS t }] }
    | none => .error s!"{m.name}: no access token was read from {m.tokenFile}"
  | .didKey =>
    match key with
    | none => .error s!"{m.name}: no key was read from {m.keyFile}"
    | some d =>
      match L4Factoidal.LWS.Client.agentOfSecret C .es256 d with
      | none => .error s!"{m.name}: the key in {m.keyFile} is not a valid P-256 private key"
      | some a => .ok { selfIssued := some a.key }

/-- The identity a session acts as, for the start message of the host. -/
def sessionSubject (s : Session) : Option String := s.selfIssued.map (·.subject)

#guard (remoteOp "https://s.example/a/" (.get "/x/y.txt")).url == "https://s.example/a/x/y.txt"
#guard (remoteOp "https://s.example/a/" (.put "/c/" "" ByteArray.empty true)).precondition == "ifNoneMatchStar"
#guard (remoteOp "https://s.example/a/" (.delete "/c/")).recursive
#guard (answerOfFail "u" (.head "/x") (.object [("code", .string "status"), ("status", .number "404")])).status == 404
#guard (answerOfFail "u" (.head "/x") (.object [("code", .string "transport")])).status == 0
#guard (match secretOfJwk "{\"kty\":\"EC\",\"crv\":\"P-256\",\"d\":\"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAE\"}" with
        | .ok d => d.size == 32 | .error _ => false)
#guard (secretOfJwk "{\"kty\":\"OKP\"}").toOption.isNone

end L4Factoidal.WebDAV
