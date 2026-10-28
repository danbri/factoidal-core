/-
Wasm.Ops.WebDAV — the WebDAV server handle (https://github.com/danbri/factoidal/issues/1066).

  webdavOpen(configJson)
    -> {"ok":true,"handle":"webdav1","need":{"read":[NAME,…],"exists":[]}}
  webdavLoad(handle, filesJson)
    -> {"ok":true,"need":{"read":[PATH,…],"exists":[PATH,…]}}
     | {"ok":true,"ready":{"mounts":[…],"local":[…],"write":[…]}}
     | {"ok":false,"error":"alice.md:3: unknown key …"}
  webdavStep(handle, requestJson)          (+ the request content as a region)
  webdavResume(handle, answerJson)         (+ the answer content as a region)
    -> {"ok":true,"response":{status,headers,bodyBytes}}  (the response)
     | {"ok":true,"lws":{"mount":M,"request":{method,target,headers,bodyBytes}}}
     | {"ok":true,"fetch":{method,url,headers,bodyBytes}}
  webdavClose(handle) -> {"ok":true}

The configuration of `webdavOpen` is `{listing: [NAME, …], entropy}`: the
names in CONFIGDIR (the host lists the directory; `Config.isMountFile`
decides which are mount files) and at least 32 random bytes (base64, the
seed of a key file this engine makes). `webdavLoad` takes `{files: [{name,
text} | {name, missing: true}], exists: [{path, present}]}`: the files and
existence checks the last answer named, paths relative to CONFIGDIR.

`ready` names, for each local mount, the directory and the `lwsOpen`
configuration to open it with (`local: [{name, dir, config}]`); the host
opens it with the ops `lws-serve` uses and carries each `lws` request to it.
`write: [{path, text, mode}]` is a key file this engine made.

A request document is `{method, target, headers, now, randomBase64}`; the
content is the region (`webdavStep` through `l4_call_blob_io`) or
`body`/`bodyBase64` (the string entry). An answer to `lws` is `{status,
headers}` and the response content; an answer to `fetch` is `{status,
headers, now, randomBase64}` (48 random bytes: the client signs a
credential with them) and the content, or `{error}` for a transport
failure.

Every decision is in `L4Factoidal/WebDAV/`. State lives here, in an
`IO.Ref`, as the other handle ops keep theirs: the configuration, the
dead properties and locks (`DavState`), the client sessions of remote
mounts, and the request in flight (its program's continuation and, for a
remote mount, the client's state).
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import L4Factoidal.WebDAV.Server
import L4Factoidal.WebDAV.Local
import L4Factoidal.WebDAV.Remote
import L4Factoidal.Authz.Keys
import L4Factoidal.Crypto.SHA2

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.WebDAV

/-- The request in flight. -/
structure DavPending where
  mount : Mount
  op : BOp
  k : BAns → Prog (DavResponse × DavState)
  client : Option L4Factoidal.LWS.Client.ClientState := none

/-- The loading phases. -/
inductive DavLoad where
  /-- The mount files were named. -/
  | mountFiles (files : List String)
  /-- The key, token and storage files were named. -/
  | credentials (mounts : List Mount)
  | ready

structure DavHandle where
  load : DavLoad
  entropy : ByteArray := ByteArray.empty
  mounts : List Mount := []
  sessions : List (String × L4Factoidal.LWS.Client.Session) := []
  dav : DavState := {}
  pending : Option DavPending := none

initialize davCounter : IO.Ref Nat ← IO.mkRef 0
initialize davTable : IO.Ref (Std.HashMap String DavHandle) ← IO.mkRef ∅

def unknownDavHandle (h : String) : String := errJson s!"unknown WebDAV handle: {h}"

def davStrs (xs : List String) : Json := .array (xs.map Json.string)

def davNeedJson (read exists_ : List String) : Json :=
  .object [("read", davStrs read), ("exists", davStrs exists_)]

/-- The crypto of remote mounts: the vendored HACL* code. -/
def davCrypto : L4Factoidal.Authz.Crypto := L4Factoidal.Authz.hacl

def davB64 (b : ByteArray) : String := L4Factoidal.LWS.Base64.encode b
def davUnb64 (t : String) : Option ByteArray := L4Factoidal.LWS.Base64.decode? t

/-- `webdavOpen(configJson)`. -/
def webdavOpen (configJson : String) : IO String := do
  match parseJson configJson with
  | .error e => pure (errJson s!"webdavOpen: the configuration is not JSON: {toString e}")
  | .ok j =>
    let listing := ((j.getArray? "listing").getD []).filterMap Json.asString?
    let entropy := ((j.getString? "entropy").bind davUnb64).getD ByteArray.empty
    if entropy.size < 32 then
      return errJson "webdavOpen: \"entropy\" holds fewer than 32 bytes (base64)"
    let files := (listing.filter isMountFile).mergeSort (· ≤ ·)
    if files.isEmpty then
      return errJson "webdavOpen: the configuration directory holds no mount file (NAME.md)"
    let n ← davCounter.modifyGet (fun c => (c + 1, c + 1))
    let h := s!"webdav{n}"
    davTable.modify (·.insert h { load := .mountFiles files, entropy })
    pure (okWith [("handle", .string h), ("need", davNeedJson files [])])

/-- A file the host read: its text, or `none` when it does not exist. -/
def davFileOf (j : Json) (name : String) : Option (Option String) :=
  ((j.getArray? "files").getD []).findSome? (fun f =>
    if f.getString? "name" == some name then
      if f.field? "missing" == some (.bool true) then some none else some (f.getString? "text")
    else none)

def davExistsOf (j : Json) (path : String) : Bool :=
  ((j.getArray? "exists").getD []).any (fun e =>
    e.getString? "path" == some path && e.field? "present" == some (.bool true))

def davDirOf (path : String) : String := if path.endsWith "/" then (path.dropEnd 1).toString else path

/-- What the second load names: the key and token files of remote mounts,
and, for each local mount, its directory and the two storage files. -/
def davCredentialNeeds (ms : List Mount) : List String × List String :=
  let read := ms.filterMap (fun m =>
    if m.kind == .lws && m.auth == .didKey then some m.keyFile
    else if m.kind == .lws && m.auth == .bearer then some m.tokenFile else none)
  let ex := ms.foldl (fun acc m =>
    if m.kind == .localStore then
      acc ++ [davDirOf m.path, davDirOf m.path ++ "/lws-state.json", davDirOf m.path ++ "/lws-files.json"]
    else acc) []
  (read, ex)

/-- The storage format a local mount opens with: what the mount file says,
else what the directory holds. A mount file that says `snapshot` for a
directory that holds only a storage kept in files is refused: it would open
that storage empty. -/
def davStorageModeOf (m : Mount) (j : Json) : Except String String :=
  let d := davDirOf m.path
  let hasFiles := davExistsOf j (d ++ "/lws-files.json")
  let hasSnap := davExistsOf j (d ++ "/lws-state.json")
  if !davExistsOf j d then .error s!"{m.name}.md: the storage directory {m.path} does not exist"
  else match m.storage with
    | some "snapshot" =>
      if hasFiles && !hasSnap then
        .error s!"{m.name}.md: {m.path} holds a storage kept in files (lws-files.json); `storage: snapshot` would open it empty"
      else .ok "snapshot"
    | some s => .ok s
    | none => .ok (if hasFiles then "files" else "snapshot")

def davMountJson (m : Mount) (ses : Option L4Factoidal.LWS.Client.Session) : Json :=
  .object ([ ("name", .string m.name), ("title", .string m.title), ("kind", .string m.kind.name)
           , ("writable", .bool m.writable) ] ++
    (if m.kind == .lws then [("url", .string m.url), ("auth", .string m.auth.name)] else [("path", .string m.path)]) ++
    (match ses.bind sessionSubject with
     | some s => [("agent", .string s)]
     | none => []))

/-- A key file's path with its `.` segments and empty segments removed, so
`alice.jwk` and `./alice.jwk` name one file. Two `did-key` mounts that name
one absent key file get one key: the first mount makes it, the next ones use
it, and the host writes it once. -/
def davKeyPathKey (p : String) : String :=
  "/".intercalate ((p.splitOn "/").filter (fun s => s != "." && s != ""))

#guard davKeyPathKey "./alice.jwk" == davKeyPathKey "alice.jwk"
#guard davKeyPathKey "keys//./a.jwk" == "keys/a.jwk"

/-- The second load: credentials and storage formats. -/
def davFinishLoad (hd : DavHandle) (ms : List Mount) (j : Json) : Except String (DavHandle × Json) := do
  let toPublic := davCrypto.es256Public
  let mut sessions : List (String × L4Factoidal.LWS.Client.Session) := []
  let mut writes : List Json := []
  let mut locals : List Json := []
  let mut made : List (String × ByteArray) := []
  for m in ms do
    match m.kind with
    | .localStore =>
      let mode ← davStorageModeOf m j
      locals := locals ++ [.object [ ("name", .string m.name), ("dir", .string m.path)
        , ("config", .object [ ("storage", .string mode), ("baseIri", .string m.base)
                             , ("pageSize", .number "0"), ("insecureNoAuth", .bool true) ]) ]]
    | .lws =>
      match m.auth with
      | .none => sessions := sessions ++ [(m.name, ({ } : L4Factoidal.LWS.Client.Session))]
      | .bearer =>
        match davFileOf j m.tokenFile with
        | some (some t) => sessions := sessions ++ [(m.name, ← sessionOf m toPublic none (some t))]
        | _ => throw s!"{m.name}.md: the token file {m.tokenFile} does not exist"
      | .didKey =>
        match davFileOf j m.keyFile with
        | some (some t) =>
          let d ← (secretOfJwk t).mapError (fun e => s!"{m.name}.md: {m.keyFile}: {e}")
          sessions := sessions ++ [(m.name, ← sessionOf m toPublic (some d) none)]
        | _ =>
          match made.lookup (davKeyPathKey m.keyFile) with
          | some d => sessions := sessions ++ [(m.name, ← sessionOf m toPublic (some d) none)]
          | none =>
          -- No key file: a new key, written for the host to keep.
          let seed := hd.entropy ++ m.name.toUTF8
          match newKey L4Factoidal.Crypto.sha256 toPublic seed with
          | none => throw s!"{m.name}.md: no P-256 key could be made"
          | some (d, xy) =>
            writes := writes ++ [.object [("path", .string m.keyFile), ("text", .string (jwkText d xy)), ("mode", .string "0600")]]
            made := made ++ [(davKeyPathKey m.keyFile, d)]
            sessions := sessions ++ [(m.name, ← sessionOf m toPublic (some d) none)]
  let mountsJ := ms.map (fun m => davMountJson m (sessions.lookup m.name))
  pure ({ hd with load := .ready, mounts := ms, sessions },
        .object [("mounts", .array mountsJ), ("local", .array locals), ("write", .array writes)])

/-- `webdavLoad(handle, filesJson)`. -/
def webdavLoad (h filesJson : String) : IO String := do
  match (← davTable.get)[h]? with
  | none => pure (unknownDavHandle h)
  | some hd =>
    let fail (e : String) : IO String := do
      davTable.modify (·.erase h)
      pure (errJson e)
    match parseJson filesJson with
    | .error e => fail s!"webdavLoad: not JSON: {toString e}"
    | .ok j =>
      match hd.load with
      | .ready => pure (errJson "webdavLoad: the handle is ready")
      | .mountFiles files =>
        let parsed := files.mapM (fun f =>
          match davFileOf j f with
          | some (some t) => mountOfMarkdown f t
          | _ => .error s!"{f}: the file could not be read")
        match parsed with
        | .error e => fail e
        | .ok ms =>
          let (read, ex) := davCredentialNeeds ms
          davTable.modify (·.insert h { hd with load := .credentials ms })
          pure (okWith [("need", davNeedJson read ex)])
      | .credentials ms =>
        match davFinishLoad hd ms j with
        | .error e => fail e
        | .ok (hd', ready) =>
          davTable.modify (·.insert h hd')
          pure (okWith [("ready", ready)])

/-! ## Requests -/

/-- The answer of one step: what the host does next. -/
inductive DavOut where
  | response (r : DavResponse)
  | lws (mount : String) (q : LwsReq)
  | fetch (r : L4Factoidal.LWS.Client.Req)

def davHeadersJ (hs : List (String × String)) : Json := .array (hs.map (fun (n, v) => .array [.string n, .string v]))

/-- The content in the envelope (string entry) or as the region. -/
def davContentMembers (body : ByteArray) (blobOut : Bool) : List (String × Json) :=
  if blobOut then [("bodyBytes", .number (toString body.size))]
  else match String.fromUTF8? body with
    | some t => [("body", .string t)]
    | none => [("bodyBase64", .string (davB64 body))]

def davOutEnvelope (o : DavOut) (blobOut : Bool) : String × ByteArray :=
  let region (b : ByteArray) := if blobOut then b else ByteArray.empty
  match o with
  | .response r =>
    (okWith [("response", .object ([("status", .number (toString r.status)), ("headers", davHeadersJ r.headers)] ++
      davContentMembers r.body blobOut))], region r.body)
  | .lws m q =>
    (okWith [("lws", .object [("mount", .string m), ("request", .object ([("method", .string q.method),
      ("target", .string q.target), ("headers", davHeadersJ q.headers)] ++ davContentMembers q.body blobOut))])],
     region q.body)
  | .fetch r =>
    (okWith [("fetch", .object ([("method", .string r.method), ("url", .string r.url),
      ("headers", davHeadersJ r.headers)] ++ davContentMembers r.body blobOut))], region r.body)

def davInternalError (msg : String) : DavResponse := textResp 500 msg

/-- The answer of a finished client operation, or `none` for a request. -/
def davClientDone (m : Mount) (op : BOp) : L4Factoidal.LWS.Client.Action → Option BAns
  | .done res => some (answerOfDone m.url op res)
  | .fail err => some (answerOfFail m.url op err)
  | .fetch _ => none

/-- Run a program until it needs the host, or ends. At most `fuel`
operations that need no host (a client operation refused before any
request). -/
def davDrive (hd : DavHandle) (mount? : Option Mount) : Nat → Prog (DavResponse × DavState) → DavHandle × DavOut
  | _, .pure (resp, st) => ({ hd with dav := st, pending := none }, .response resp)
  | 0, .call _ _ => ({ hd with pending := none }, .response (davInternalError "webdav: operation limit"))
  | n + 1, .call op k =>
    match mount? with
    | none => ({ hd with pending := none }, .response (davInternalError "webdav: an operation with no mount"))
    | some m =>
      match m.kind with
      | .localStore => ({ hd with pending := some { mount := m, op, k } }, .lws m.name (localRequest op))
      | .lws =>
        let ses := (hd.sessions.lookup m.name).getD ({ } : L4Factoidal.LWS.Client.Session)
        let (cs, act) := L4Factoidal.LWS.Client.start davCrypto (remoteOp m.url op) ses
        match act with
        | .fetch r => ({ hd with pending := some { mount := m, op, k, client := some cs } }, .fetch r)
        | _ =>
          let ans := (davClientDone m op act).getD { status := 0 }
          davDrive { hd with sessions := (m.name, cs.session) :: hd.sessions.filter (·.1 != m.name) } mount? n (k ans)

def davDriveFuel : Nat := 1000000

/-- Read a request document. -/
def davRequestOf (j : Json) (blob : Option ByteArray) : Except String (DavRequest × Nat × ByteArray) := do
  let method ← (j.getString? "method").elim (.error "request: member \"method\" is required") .ok
  let target ← (j.getString? "target").elim (.error "request: member \"target\" is required") .ok
  let headers := ((j.getArray? "headers").getD []).filterMap (fun it =>
    match it with
    | .array [.string n, .string v] => some (n.toLower, v)
    | _ => none)
  let body := match blob with
    | some b => b
    | none => match j.getString? "bodyBase64" with
      | some t => (davUnb64 t).getD ByteArray.empty
      | none => ((j.getString? "body").getD "").toUTF8
  let now := match j.field? "now" with
    | some (.number s) => s.toNat?.getD 0
    | _ => 0
  let random := ((j.getString? "randomBase64").bind davUnb64).getD ByteArray.empty
  pure ({ method, target, headers, body }, now, random)

def davViewsOf (hd : DavHandle) : List MountView :=
  hd.mounts.map (fun m => { name := m.name, title := m.title, writable := m.writable })

def davFinishOut (h : String) (hd : DavHandle) (o : DavOut) (blobOut : Bool) : IO (String × ByteArray) := do
  davTable.modify (·.insert h hd)
  pure (davOutEnvelope o blobOut)

/-- `webdavStep(handle, requestJson)`. -/
def webdavStepWith (h requestJson : String) (blob : Option ByteArray) : IO (String × ByteArray) := do
  let blobOut := blob.isSome
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← davTable.get)[h]? with
  | none => pure (noBytes (unknownDavHandle h))
  | some hd =>
    match hd.load with
    | .ready =>
      if hd.pending.isSome then
        return noBytes (errJson "webdavStep: a request is in flight; answer it with webdavResume first")
      match parseJson requestJson with
      | .error e => pure (noBytes (errJson s!"request: {toString e}"))
      | .ok j =>
        match davRequestOf j blob with
        | .error e => pure (noBytes (errJson e))
        | .ok (r, now, random) =>
          let cx : Ctx := { mounts := davViewsOf hd, now, random }
          let mount? := (mountOf r).bind (fun n => hd.mounts.find? (·.name == n))
          let (hd', o) := davDrive hd mount? davDriveFuel (handle cx hd.dav r)
          davFinishOut h hd' o blobOut
    | _ => pure (noBytes (errJson "webdavStep: the handle is still loading (webdavLoad)"))

def davRespHeaders (j : Json) : List (String × String) :=
  ((j.getArray? "headers").getD []).filterMap (fun it =>
    match it with
    | .array [.string n, .string v] => some (n, v)
    | _ => none)

/-- `webdavResume(handle, answerJson)`. -/
def webdavResumeWith (h answerJson : String) (blob : Option ByteArray) : IO (String × ByteArray) := do
  let blobOut := blob.isSome
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← davTable.get)[h]? with
  | none => pure (noBytes (unknownDavHandle h))
  | some hd =>
    match hd.pending with
    | none => pure (noBytes (errJson "webdavResume: no request is in flight"))
    | some p =>
      match parseJson answerJson with
      | .error e => pure (noBytes (errJson s!"answer: {toString e}"))
      | .ok j =>
        let body := match blob with
          | some b => b
          | none => match j.getString? "bodyBase64" with
            | some t => (davUnb64 t).getD ByteArray.empty
            | none => ((j.getString? "body").getD "").toUTF8
        let status := match j.field? "status" with
          | some (.number s) => s.toNat?.getD 0
          | _ => 0
        let hd := { hd with pending := none }
        match p.client with
        | none =>
          -- A local mount: the storage handle's response.
          let ans := answerOf p.mount.base p.op status (davRespHeaders j) body
          let (hd', o) := davDrive hd (some p.mount) davDriveFuel (p.k ans)
          davFinishOut h hd' o blobOut
        | some cs =>
          let ev : L4Factoidal.LWS.Client.Event :=
            match j.getString? "error" with
            | some msg => .transportError msg
            | none => .response { status, headers := davRespHeaders j, body
                                  now := match j.field? "now" with
                                    | some (.number s) => s.toNat?.getD 0
                                    | _ => 0
                                  random := ((j.getString? "randomBase64").bind davUnb64).getD ByteArray.empty }
          let (cs', act) := L4Factoidal.LWS.Client.step davCrypto cs ev
          match act with
          | .fetch r => davFinishOut h { hd with pending := some { p with client := some cs' } } (.fetch r) blobOut
          | _ =>
            let ans := (davClientDone p.mount p.op act).getD { status := 0 }
            let hd := { hd with sessions := (p.mount.name, cs'.session) :: hd.sessions.filter (·.1 != p.mount.name) }
            let (hd', o) := davDrive hd (some p.mount) davDriveFuel (p.k ans)
            davFinishOut h hd' o blobOut

def webdavStep (h requestJson : String) : IO String := do
  pure (← webdavStepWith h requestJson none).1

def webdavResume (h answerJson : String) : IO String := do
  pure (← webdavResumeWith h answerJson none).1

/-- `webdavClose(handle)`. -/
def webdavClose (h : String) : IO String := do
  if (← davTable.get).contains h then
    davTable.modify (·.erase h)
    pure (okWith [])
  else pure (unknownDavHandle h)

def webdavOpNames : List String := ["webdavOpen", "webdavLoad", "webdavStep", "webdavResume", "webdavClose"]

def webdavBlobIoOpNames : List String := ["webdavStep", "webdavResume"]

end L4Wasm.Ops
