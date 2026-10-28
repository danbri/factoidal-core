/-
Wasm.Ops.WebDAV — the WebDAV server handle (https://github.com/danbri/factoidal/issues/1066).

  webdavOpen(configJson)
    -> {"ok":true,"handle":"webdav1","need":{"read":[NAME,…,".webdav-state.json"],"exists":[]}}
  webdavLoad(handle, filesJson)
    -> {"ok":true,"need":{"read":[PATH,…],"exists":[PATH,…]}}
     | {"ok":true,"ready":{"mounts":[…],"local":[…],"write":[…]}}
     | {"ok":false,"error":"alice.md:3: unknown key …"}
  webdavStep(handle, requestJson)          (+ the request content as a region)
  webdavResume(handle, answerJson)         (+ the answer content as a region)
    -> {"ok":true,"response":{status,headers,bodyBytes}}  (the response)
       with "write":{"path":".webdav-state.json","text":…,"mode":"0600"}
       when the request changed the dead properties or locks
     | {"ok":true,"lws":{"mount":M,"request":{method,target,headers,bodyBytes}}}
     | {"ok":true,"fetch":{method,url,headers,bodyBytes}}
     | {"ok":true,"need":{"op":"pbkdf2-hmac-sha256","key":B64,"data":B64,"iterations":N,"bits":256}}
       (a login: the host runs that one WebCrypto derivation, cipher-host.mjs,
       and gives `{"ok":B64}` or `{"refused":true}` to webdavResume)
  webdavClose(handle) -> {"ok":true}
  webdavUser(argsJson) -> {"ok":true,"need":{…}} | {"ok":true,"text":…,"replaced":B}

Login (https://github.com/danbri/factoidal/issues/1108, expert review
https://github.com/danbri/factoidal/issues/1117): the configuration may hold `login: {users:
PATH|null, tls: B, host: ADDRESS}`. With `users`, the first `need` names that
file too; `Login.usersForServer` reads it (a malformed line stops the start
with FILE:LINE), and `Login.transportAllowsBasic` refuses a plain-HTTP
listener that is not on a loopback address. Each request then passes
`Login.gate` first: a 401, an allowed user, or one PBKDF2 derivation the host
runs (`need`), whose answer `Login.finish` compares with the stored hash. The
login cache (`Login.Cache`) and its secret stay in this handle.

The failed-login limit (https://github.com/danbri/factoidal/issues/1119):
`login` may also hold `limit` and `window` (the text of `--login-limit` and
`--login-window`, unread) and `disableRateLimits: true`
(`--dangerously-disable-ratelimits`); `Login.limitsOf` reads them, and a bad
value stops the start. `ready` carries `warnings: [TEXT, …]` for the host to
print at start (`Login.limitsWarnings`). A request document carries
`remoteAddress`, the client's address as the socket gives it; `Login.gate`
counts failures under it and the user name, and answers 429 with
`Retry-After` with no derivation when either is over its limit.

`webdavUser` (`factoidal webdav-user FILE NAME`): `{name, file, text|null,
passwordBase64, saltBase64, iterations?, answers: [{request, answer}]}` →
the one derivation as `need` (as `runWithCipher` in cipher-host.mjs expects),
then, with its answer, the file's new text (`Login.withUser`).

The configuration of `webdavOpen` is `{listing: [NAME, …], entropy, now}`:
the names in CONFIGDIR (the host lists the directory; `Config.isMountFile`
decides which are mount files), at least 32 random bytes (base64, the seed
of a key file this engine makes) and the host's clock (seconds since the
Unix epoch; locks that expired before it are not loaded).

The dead properties and locks are kept in `CONFIGDIR/.webdav-state.json`
(`State.stateFileName`, form in `L4Factoidal/WebDAV/State.lean`,
https://github.com/danbri/factoidal/issues/1078). The first `need` names it;
a missing file is an empty state, and a text that `stateOfText` refuses
stops the start with the file's name. A response whose request changed the
state carries `write`: the host replaces the file with that text (a new file
in the same directory, then a rename) before it sends the response. `webdavLoad` takes `{files: [{name,
text} | {name, missing: true}], exists: [{path, present}]}`: the files and
existence checks the last answer named, paths relative to CONFIGDIR.

`ready` names, for each local mount, the directory and the `lwsOpen`
configuration to open it with (`local: [{name, dir, config}]`); the host
opens it with the ops `lws-serve` uses and carries each `lws` request to it.
`write: [{path, text, mode}]` is a key file this engine made.

A request document is `{method, target, headers, now, randomBase64,
remoteAddress}`; the
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
import L4Factoidal.WebDAV.State
import L4Factoidal.WebDAV.Local
import L4Factoidal.WebDAV.Remote
import L4Factoidal.WebDAV.Login
import L4Factoidal.Crypto.SHA2Native
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

/-- A login waiting for the host's derivation: the request it guards. -/
structure DavLoginPending where
  derive : Login.Derive
  request : DavRequest
  now : Nat
  random : ByteArray

/-- The login of the listener (`--users`). -/
structure DavLogin where
  settings : Login.Settings
  cache : Login.Cache := {}
  pending : Option DavLoginPending := none

structure DavHandle where
  load : DavLoad
  /-- The users file named at `webdavOpen`, read at the first load. -/
  usersFile : Option String := none
  /-- The failed-login limit, from the options at `webdavOpen`. -/
  limits : Login.Limits := {}
  login : Option DavLogin := none
  entropy : ByteArray := ByteArray.empty
  mounts : List Mount := []
  sessions : List (String × L4Factoidal.LWS.Client.Session) := []
  dav : DavState := {}
  /-- The host's clock at `webdavOpen`. -/
  now : Nat := 0
  /-- The state text last read from or written to the state file. -/
  saved : String := ""
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
    let now := match j.field? "now" with
      | some (.number s) => s.toNat?.getD 0
      | _ => 0
    let files := (listing.filter isMountFile).mergeSort (· ≤ ·)
    if files.isEmpty then
      return errJson "webdavOpen: the configuration directory holds no mount file (NAME.md)"
    -- The login: a users file needs TLS or a loopback address (Basic sends
    -- the password in clear).
    let login := (j.field? "login").getD (.object [])
    let usersFile := login.getString? "users"
    let tls := login.field? "tls" == some (.bool true)
    let host := (login.getString? "host").getD "127.0.0.1"
    if usersFile.isSome && !Login.transportAllowsBasic tls host then
      return errJson (Login.transportRefusal host)
    let limits ← match Login.limitsOf usersFile.isSome (login.getString? "limit") (login.getString? "window")
        (login.field? "disableRateLimits" == some (.bool true)) with
      | .ok l => pure l
      | .error e => return errJson e
    let n ← davCounter.modifyGet (fun c => (c + 1, c + 1))
    let h := s!"webdav{n}"
    davTable.modify (·.insert h { load := .mountFiles files, entropy, now, usersFile, limits })
    pure (okWith [("handle", .string h), ("need", davNeedJson (files ++ [stateFileName] ++ usersFile.toList) [])])

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
        | some (some t) => sessions := sessions ++ [(m.name, ← sessionOf m davCrypto none (some t))]
        | _ => throw s!"{m.name}.md: the token file {m.tokenFile} does not exist"
      | .didKey =>
        match davFileOf j m.keyFile with
        | some (some t) =>
          let d ← (secretOfJwk t).mapError (fun e => s!"{m.name}.md: {m.keyFile}: {e}")
          sessions := sessions ++ [(m.name, ← sessionOf m davCrypto (some d) none)]
        | _ =>
          match made.lookup (davKeyPathKey m.keyFile) with
          | some d => sessions := sessions ++ [(m.name, ← sessionOf m davCrypto (some d) none)]
          | none =>
          -- No key file: a new key, written for the host to keep.
          let seed := hd.entropy ++ m.name.toUTF8
          match newKey L4Factoidal.Crypto.sha256 toPublic seed with
          | none => throw s!"{m.name}.md: no P-256 key could be made"
          | some (d, xy) =>
            writes := writes ++ [.object [("path", .string m.keyFile), ("text", .string (jwkText d xy)), ("mode", .string "0600")]]
            made := made ++ [(davKeyPathKey m.keyFile, d)]
            sessions := sessions ++ [(m.name, ← sessionOf m davCrypto (some d) none)]
  let mountsJ := ms.map (fun m => davMountJson m (sessions.lookup m.name))
  pure ({ hd with load := .ready, mounts := ms, sessions },
        .object [("mounts", .array mountsJ), ("local", .array locals), ("write", .array writes)
                , ("warnings", .array ((Login.limitsWarnings hd.limits).map Json.string))])

/-- The hash of the login cache: SHA-256 through HACL\* (crypto policy: a
password goes through HACL\*, never the pure-Lean specification hash). -/
def davLoginHash (b : ByteArray) : ByteArray := L4Factoidal.Crypto.sha256Hacl b

/-- The 32-byte secret of the login cache, from the host's entropy. -/
def davLoginSecret (entropy : ByteArray) : ByteArray :=
  davLoginHash ("factoidal webdav login cache".toUTF8 ++ entropy)

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
        -- The state file: absent is an empty state; a text the engine does
        -- not read stops the start.
        let state : Except String DavState :=
          match davFileOf j stateFileName with
          | some (some t) => (stateOfText t).mapError (fun e => s!"{stateFileName}: {e}")
          | _ => .ok {}
        -- The users file: absent or malformed stops the start.
        let login : Except String (Option DavLogin) :=
          match hd.usersFile with
          | none => .ok none
          | some uf =>
            match davFileOf j uf with
            | some (some t) =>
              (Login.usersForServer uf t).map (fun us =>
                some { settings := { users := us, secret := davLoginSecret hd.entropy, limits := hd.limits } })
            | _ => .error s!"{uf}: the users file could not be read"
        match parsed, state, login with
        | .error e, _, _ => fail e
        | _, .error e, _ => fail e
        | _, _, .error e => fail e
        | .ok ms, .ok st0, .ok lg =>
          let st := stateAtStart st0 hd.now
          let (read, ex) := davCredentialNeeds ms
          davTable.modify (·.insert h { hd with load := .credentials ms, dav := st, saved := stateText st, login := lg })
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
  /-- The response, and the state file's new text when the request changed
  the state. -/
  | response (r : DavResponse) (write : Option String := none)
  | lws (mount : String) (q : LwsReq)
  | fetch (r : L4Factoidal.LWS.Client.Req)
  /-- A login: one PBKDF2 derivation for the host to run. -/
  | need (d : Login.Derive)

def davHeadersJ (hs : List (String × String)) : Json := .array (hs.map (fun (n, v) => .array [.string n, .string v]))

/-- The content in the envelope (string entry) or as the region. -/
def davContentMembers (body : ByteArray) (blobOut : Bool) : List (String × Json) :=
  if blobOut then [("bodyBytes", .number (toString body.size))]
  else match String.fromUTF8? body with
    | some t => [("body", .string t)]
    | none => [("bodyBase64", .string (davB64 body))]

/-- A PBKDF2 request in the form of `cipher-host.mjs` (`key` the password,
`data` the salt, both base64). -/
def davKdfRequest (password salt : ByteArray) (iterations : Nat) : Json :=
  .object [ ("op", .string Login.kdfOpName), ("key", .string (davB64 password)), ("data", .string (davB64 salt))
          , ("iterations", .number (toString iterations)), ("bits", .number (toString (Login.hashBytes * 8))) ]

/-- The derived bytes of a host's answer to a PBKDF2 request. -/
def davKdfAnswer (j : Json) : Option ByteArray := (j.getString? "ok").bind davUnb64

def davOutEnvelope (o : DavOut) (blobOut : Bool) : String × ByteArray :=
  let region (b : ByteArray) := if blobOut then b else ByteArray.empty
  match o with
  | .response r write =>
    (okWith ([("response", .object ([("status", .number (toString r.status)), ("headers", davHeadersJ r.headers)] ++
      davContentMembers r.body blobOut))] ++
      (match write with
       | some t => [("write", .object [("path", .string stateFileName), ("text", .string t), ("mode", .string "0600")])]
       | none => [])), region r.body)
  | .lws m q =>
    (okWith [("lws", .object [("mount", .string m), ("request", .object ([("method", .string q.method),
      ("target", .string q.target), ("headers", davHeadersJ q.headers)] ++ davContentMembers q.body blobOut))])],
     region q.body)
  | .fetch r =>
    (okWith [("fetch", .object ([("method", .string r.method), ("url", .string r.url),
      ("headers", davHeadersJ r.headers)] ++ davContentMembers r.body blobOut))], region r.body)
  | .need d => (okWith [("need", davKdfRequest d.password d.salt d.iterations)], ByteArray.empty)

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
  | _, .pure (resp, st) =>
    -- The state file is written when its text changes: after PROPPATCH,
    -- LOCK (new or refreshed), UNLOCK, a COPY, MOVE or DELETE that moved or
    -- removed properties or locks, and a request that found a lock expired.
    let t := stateText st
    if t == hd.saved then ({ hd with dav := st, pending := none }, .response resp)
    else ({ hd with dav := st, saved := t, pending := none }, .response resp (some t))
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

/-- One request after the login: the WebDAV program, driven until it needs
the host. -/
def davServe (hd : DavHandle) (r : DavRequest) (now : Nat) (random : ByteArray) : DavHandle × DavOut :=
  let cx : Ctx := { mounts := davViewsOf hd, now, random }
  let mount? := (mountOf r).bind (fun n => hd.mounts.find? (·.name == n))
  davDrive hd mount? davDriveFuel (handle cx hd.dav r)

/-- `webdavStep(handle, requestJson)`. -/
def webdavStepWith (h requestJson : String) (blob : Option ByteArray) : IO (String × ByteArray) := do
  let blobOut := blob.isSome
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← davTable.get)[h]? with
  | none => pure (noBytes (unknownDavHandle h))
  | some hd =>
    match hd.load with
    | .ready =>
      if hd.pending.isSome || (hd.login.bind (·.pending)).isSome then
        return noBytes (errJson "webdavStep: a request is in flight; answer it with webdavResume first")
      match parseJson requestJson with
      | .error e => pure (noBytes (errJson s!"request: {toString e}"))
      | .ok j =>
        match davRequestOf j blob with
        | .error e => pure (noBytes (errJson e))
        | .ok (r, now, random) =>
          match hd.login with
          | none =>
            let (hd', o) := davServe hd r now random
            davFinishOut h hd' o blobOut
          | some lg =>
            let address := (j.getString? "remoteAddress").getD ""
            match Login.gate davLoginHash lg.settings lg.cache now address (r.header? "authorization") with
            | (.refuse, c) => davFinishOut h { hd with login := some { lg with cache := c } } (.response Login.unauthorized) blobOut
            | (.limited seconds, c) =>
              davFinishOut h { hd with login := some { lg with cache := c } } (.response (Login.tooManyFailures seconds)) blobOut
            | (.allow _, c) =>
              let (hd', o) := davServe { hd with login := some { lg with cache := c } } r now random
              davFinishOut h hd' o blobOut
            | (.derive d, c) =>
              let p : DavLoginPending := { derive := d, request := r, now, random }
              davFinishOut h { hd with login := some { lg with cache := c, pending := some p } } (.need d) blobOut
    | _ => pure (noBytes (errJson "webdavStep: the handle is still loading (webdavLoad)"))

def davRespHeaders (j : Json) : List (String × String) :=
  ((j.getArray? "headers").getD []).filterMap (fun it =>
    match it with
    | .array [.string n, .string v] => some (n, v)
    | _ => none)

/-- The host's answer to a login's derivation: the request it guarded runs,
or the answer is 401. -/
def davLoginResume (h : String) (hd : DavHandle) (lg : DavLogin) (p : DavLoginPending) (answerJson : String)
    (blobOut : Bool) : IO (String × ByteArray) := do
  match parseJson answerJson with
  | .error e => pure (errJson s!"answer: {toString e}", ByteArray.empty)
  | .ok j =>
    let (ok, c) := Login.finish davLoginHash lg.settings lg.cache p.now p.derive (davKdfAnswer j)
    let hd := { hd with login := some { lg with cache := c, pending := none } }
    if ok then
      let (hd', o) := davServe hd p.request p.now p.random
      davFinishOut h hd' o blobOut
    else davFinishOut h hd (.response Login.unauthorized) blobOut

/-- `webdavResume(handle, answerJson)`. -/
def webdavResumeWith (h answerJson : String) (blob : Option ByteArray) : IO (String × ByteArray) := do
  let blobOut := blob.isSome
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← davTable.get)[h]? with
  | none => pure (noBytes (unknownDavHandle h))
  | some hd =>
    if let some lg := hd.login then
      if let some p := lg.pending then
        return (← davLoginResume h hd lg p answerJson blobOut)
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

/-- `webdavUser(argsJson)`: one line of a users file added or replaced
(`factoidal webdav-user FILE NAME`). The first call answers the PBKDF2
derivation as `need`; called again with `answers` holding that request and
the host's answer, it gives the file's new text. The host writes the text
(mode 0600, a new file renamed over the old one). -/
def webdavUser (argsJson : String) : IO String := do
  match parseJson argsJson with
  | .error e => pure (errJson s!"webdavUser: the arguments are not JSON: {toString e}")
  | .ok j =>
    let name := (j.getString? "name").getD ""
    let file := (j.getString? "file").getD "users"
    let text := (j.getString? "text").getD ""
    let input := ((j.getString? "passwordBase64").bind davUnb64).getD ByteArray.empty
    let salt := ((j.getString? "saltBase64").bind davUnb64).getD ByteArray.empty
    -- `--iterations N` arrives as text; a value that is not a decimal count
    -- is 0, which `planAdd` refuses.
    let iterations := match j.field? "iterations" with
      | some (.number s) => s.toNat?.getD 0
      | some (.string s) => (Login.countOf? s).getD 0
      | _ => Login.defaultIterations
    match Login.planAdd file name input salt iterations text with
    | .error e => pure (errJson s!"webdav-user: {e}")
    | .ok plan =>
      let req := davKdfRequest plan.password plan.salt plan.iterations
      let answers := (j.getArray? "answers").getD []
      match answers.find? (fun a => a.field? "request" == some req) with
      | none => pure (okWith [("need", req)])
      | some a =>
        match (a.field? "answer").bind davKdfAnswer with
        | none => pure (errJson "webdav-user: the host refused the PBKDF2 derivation")
        | some d =>
          match Login.finishAdd plan d text with
          | .error e => pure (errJson s!"webdav-user: {e}")
          | .ok (t, replaced) => pure (okWith [("text", .string t), ("replaced", .bool replaced)])

def webdavOpNames : List String := ["webdavOpen", "webdavLoad", "webdavStep", "webdavResume", "webdavClose", "webdavUser"]

def webdavBlobIoOpNames : List String := ["webdavStep", "webdavResume"]

end L4Wasm.Ops
