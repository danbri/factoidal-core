/-
L4Factoidal.WebDAV.Server — HTTP Extensions for Web Distributed Authoring
and Versioning (WebDAV), RFC 4918, classes 1 and 2, over the storages of
the mounts. https://github.com/danbri/factoidal/issues/1066

    handle : Ctx → DavState → DavRequest → Prog (DavResponse × DavState)

One request is one program over storage operations (`Backend.Prog`); its
result is the response and the server's next state. The state holds what a
storage cannot: the dead properties (RFC 4918 §4.4) and the locks (§6, §7).
A refused request returns the state it was given (theorem
`refused_keeps_state` names the refusals checked before any operation).

The root collection `/` holds one collection per mount; it is the server's
own and no storage is asked about it. `/<mount>/...` is a path in the
mount's storage (`Path.storagePath`).

Methods (RFC 4918 §9): OPTIONS, GET, HEAD, PUT, DELETE, MKCOL, COPY, MOVE,
PROPFIND (Depth 0 and 1; Depth infinity refused with 403 and
`DAV:propfind-finite-depth`, §9.1), PROPPATCH, LOCK, UNLOCK. Lock tokens
are `urn:uuid:` URIs from the host's random bytes (§6.5). The `If` header
(§10.4) is evaluated for every method; a write to a locked resource needs
the lock token in it (§7.4, §7.5), else 423 with
`DAV:lock-token-submitted` (§16).

Clients (design record § "What each client needs"): macOS Finder writes
only to a server that answers LOCK (class 2); Windows Explorer needs
`MS-Author-Via: DAV` on OPTIONS; GNOME Files (gvfs) and KDE Dolphin need
Depth 1 PROPFIND with `getlastmodified`, `getcontentlength` and
`resourcetype`.
-/
import L4Factoidal.WebDAV.Backend
import L4Factoidal.WebDAV.Xml
import L4Factoidal.WebDAV.If
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.WebDAV

open L4Factoidal.XML

/-! ## Requests, responses, state -/

structure DavRequest where
  method : String
  target : String
  /-- Header names in lower case. -/
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
deriving Inhabited

def DavRequest.header? (r : DavRequest) (name : String) : Option String :=
  (r.headers.find? (fun (n, _) => n == name)).map (·.2)

structure DavResponse where
  status : Nat
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
deriving Inhabited

/-- One lock (RFC 4918 §6). `root` is the key of the locked resource
(`DavPath.key`). -/
structure Lock where
  token : String
  root : DavPath
  infinite : Bool
  exclusive : Bool
  owner : Option DeadValue := none
  timeout : Nat
  expires : Nat
deriving Inhabited

structure DavState where
  /-- Dead properties per resource key. -/
  props : List (String × List DeadProp) := []
  locks : List Lock := []
  serial : Nat := 0
deriving Inhabited

/-- What the server knows of a mount. -/
structure MountView where
  name : String
  title : String
  writable : Bool
deriving Inhabited

structure Ctx where
  mounts : List MountView
  /-- Seconds since the Unix epoch, from the host's clock. -/
  now : Nat := 0
  /-- Random bytes from the host (at least 16 make a lock token). -/
  random : ByteArray := ByteArray.empty
deriving Inhabited

/-! ## Small helpers -/

def textResp (status : Nat) (msg : String) (hs : List (String × String) := []) : DavResponse :=
  { status, headers := [("content-type", "text/plain; charset=utf-8")] ++ hs, body := (msg ++ "\n").toUTF8 }

def xmlResp (status : Nat) (body : String) (hs : List (String × String) := []) : DavResponse :=
  { status, headers := [("content-type", "application/xml; charset=utf-8")] ++ hs, body := body.toUTF8 }

def errResp (status : Nat) (condition : Node) : DavResponse :=
  xmlResp status (errorBody condition)

/-- The status a WebDAV client gets for a storage's refusal. A 401 or 403
of a remote storage is 403 here: the WebDAV client has no credential to
offer this server. No answer, or a 5xx, is 502 (RFC 9110 §15.6.3). -/
def davStatusOf (a : BAns) : Nat :=
  if a.ok then a.status
  else if a.status == 401 || a.status == 403 then 403
  else if a.status == 400 || a.status == 404 || a.status == 405 || a.status == 409 ||
          a.status == 412 || a.status == 415 then a.status
  else if a.status == 413 || a.status == 507 then 507
  else 502

def storageRefusal (a : BAns) : DavResponse :=
  textResp (davStatusOf a) (s!"the storage answered {a.status}" ++
    (if a.detail == "" then "" else ": " ++ a.detail))

/-- The `D:href` text of a path: the root, a collection with `/`. -/
def hrefOf (p : DavPath) (coll : Bool) : String := (if coll then p.asColl else p.asFile).href

/-- The segments of a path inside its mount. -/
def inner (p : DavPath) : List String := p.segs.drop 1

/-- Does `l` cover the resource `p` (RFC 4918 §6.1, §7.5)? -/
def Lock.covers (l : Lock) (p : DavPath) : Bool :=
  l.root.segs == p.segs || (l.infinite && p.asFile.within l.root.asFile)

/-- Is the lock's root inside `p` (a lock that a change of `p` and all it
contains reaches)? -/
def Lock.within (l : Lock) (p : DavPath) : Bool := l.root.asFile.within p.asFile

/-- The locks a change to `p` needs the tokens of: those that cover `p`;
with `subtree`, those inside it too; with `member` (the change adds or
removes `p` as a member of its parent), those whose root is the parent
(§7.4: a lock on a collection protects its membership). -/
def neededLocks (st : DavState) (p : DavPath) (subtree member : Bool) : List Lock :=
  st.locks.filter (fun l =>
    l.covers p || (subtree && l.within p) ||
    (member && (p.parent?.map (fun q => l.root.segs == q.segs)).getD false))

/-- The first needed lock whose token the request did not submit. -/
def missingToken (needed : List Lock) (submitted : List String) : Option Lock :=
  needed.find? (fun l => !submitted.contains l.token)

def lockedResp (l : Lock) : DavResponse :=
  errResp 423 (dav "lock-token-submitted" [davText "href" (hrefOf l.root false)])

/-- A lock token: `urn:uuid:` and a version 4 UUID (RFC 9562 §5.4) from 16
of the host's random bytes, or, with fewer, from the server's counter. -/
def lockToken (random : ByteArray) (serial : Nat) : String :=
  let b : ByteArray :=
    if random.size ≥ 16 then random.extract 0 16
    else L4Factoidal.Crypto.sha256 (("webdav-lock-" ++ toString serial).toUTF8) |>.extract 0 16
  let b := (b.set! 6 ((b.get! 6 &&& 0x0f) ||| 0x40)).set! 8 ((b.get! 8 &&& 0x3f) ||| 0x80)
  let h := L4Factoidal.Crypto.bytesToHex b
  let part (i n : Nat) := ((h.drop i).take n).toString
  "urn:uuid:" ++ part 0 8 ++ "-" ++ part 8 4 ++ "-" ++ part 12 4 ++ "-" ++ part 16 4 ++ "-" ++ part 20 12

#guard (lockToken (ByteArray.mk (Array.replicate 16 0xff)) 0) == "urn:uuid:ffffffff-ffff-4fff-bfff-ffffffffffff"
#guard (lockToken ByteArray.empty 1).length == 45

/-- The `Timeout` header (RFC 4918 §10.7): the first `Second-N`, or
`Infinite`; the server grants at most a week, and an hour when the client
names none. -/
def timeoutOf (v : Option String) : Nat :=
  let cap := 604800
  match v with
  | none => 3600
  | some s =>
    let parts := (s.splitOn ",").map trimS
    match parts.findSome? (fun t =>
      if t == "Infinite" then some cap
      else if t.startsWith "Second-" then (dropS t 7).toNat? else none) with
    | some n => if n == 0 then 3600 else min n cap
    | none => 3600

#guard timeoutOf (some "Second-60") == 60
#guard timeoutOf (some "Infinite, Second-4100000000") == 604800
#guard timeoutOf none == 3600

/-- An `ETag` compared with an `If` header etag (RFC 4918 §10.4.8: strong
comparison of the entity tags). -/
def etagMatches (have_ want : String) : Bool := trimS have_ == trimS want

/-! ## Properties -/

def davName (local_ : String) : ExpandedName := { namespace_ := some davNs, localPart := local_ }

/-- The live properties the server defines (RFC 4918 §15). Each is
protected: PROPPATCH of one answers 403. -/
def liveNames : List String :=
  [ "resourcetype", "displayname", "getcontenttype", "getcontentlength", "getlastmodified"
  , "getetag", "creationdate", "supportedlock", "lockdiscovery" ]

def isLive (n : ExpandedName) : Bool := n.namespace_ == some davNs && liveNames.contains n.localPart

def lockEntry (exclusive : Bool) : Node :=
  dav "lockentry" [dav "lockscope" [dav (if exclusive then "exclusive" else "shared")],
                   dav "locktype" [dav "write"]]

def activeLock (l : Lock) (now : Nat) : Node :=
  dav "activelock" (
    [ dav "locktype" [dav "write"]
    , dav "lockscope" [dav (if l.exclusive then "exclusive" else "shared")]
    , davText "depth" (if l.infinite then "infinity" else "0") ] ++
    (match l.owner with | some o => [o.node] | none => []) ++
    [ davText "timeout" ("Second-" ++ toString (l.expires - now))
    , dav "locktoken" [davText "href" l.token]
    , dav "lockroot" [davText "href" (hrefOf l.root false)] ])

/-- The live properties of a resource: the ones its metadata knows. -/
def liveProps (st : DavState) (now : Nat) (p : DavPath) (title : Option String) (m : Meta) :
    List (String × Node) :=
  let name := (title.getD ((p.segs.getLast?).getD ""))
  [ ("resourcetype", dav "resourcetype" (if m.isColl then [dav "collection"] else []))
  , ("displayname", davText "displayname" name) ] ++
  (if m.isColl then [] else
    (match m.contentType with
     | some t => [("getcontenttype", davText "getcontenttype" t)] | none => []) ++
    (match m.length with
     | some n => [("getcontentlength", davText "getcontentlength" (toString n))] | none => [])) ++
  (match m.modified with
   | some d => [("getlastmodified", davText "getlastmodified" d)] | none => []) ++
  (match m.etag with
   | some e => [("getetag", davText "getetag" e)] | none => []) ++
  [ ("supportedlock", dav "supportedlock" [lockEntry true, lockEntry false])
  , ("lockdiscovery", dav "lockdiscovery" ((st.locks.filter (·.covers p)).map (activeLock · now))) ]

def deadOf (st : DavState) (p : DavPath) : List DeadProp :=
  ((st.props.find? (fun (k, _) => k == p.key)).map (·.2)).getD []

/-- One `DAV:response` for a PROPFIND. -/
def propfindResponse (st : DavState) (now : Nat) (req : PropReq) (p : DavPath)
    (title : Option String) (m : Meta) : Node :=
  let live := liveProps st now p title m
  let dead := deadOf st p
  let href := hrefOf p m.isColl
  match req with
  | .allprop _ => propResponse href [(200, live.map (·.2) ++ dead.map (·.value.node))]
  | .propname =>
    propResponse href [(200, live.map (fun (n, _) => dav n) ++ dead.map (fun d => nameNode d.name))]
  | .prop names =>
    let found := names.filterMap (fun n =>
      if n.namespace_ == some davNs then (live.find? (·.1 == n.localPart)).map (·.2)
      else (dead.find? (·.name == n)).map (·.value.node))
    let missing := names.filter (fun n =>
      if n.namespace_ == some davNs then !(live.any (·.1 == n.localPart))
      else !(dead.any (·.name == n)))
    propResponse href [(200, found), (404, missing.map nameNode)]

/-! ## Reading the storage -/

/-- The parent collection's storage path of a path inside a mount. -/
def parentStorage (segs : List String) : String := storagePath segs.dropLast true

/-- The metadata of the resource at `segs` in the mount, as a collection
(`coll`) or as a data resource. `withLength`: a data resource's length,
from its parent's listing (an LWS `HEAD` carries no length). -/
def statAs (segs : List String) (coll : Bool) (withLength : Bool) : Prog (Option Meta) := do
  let path := storagePath segs coll
  let a ← ask (.head path)
  if !a.ok then return none
  let m : Meta := (a.info.getD { path, isColl := coll })
  let m := { m with path, isColl := coll || segs.isEmpty }
  if coll || !withLength || segs.isEmpty then return some m
  let l ← ask (.list (parentStorage segs))
  match l.members.find? (·.path == path) with
  | some e => return some { m with length := e.length,
                                   contentType := m.contentType.orElse (fun _ => e.contentType),
                                   modified := m.modified.orElse (fun _ => e.modified) }
  | none => return some m

/-- The resource a path names: as written, and a path with no `/` at the end
as a collection too (a client may name a collection either way). -/
def resolve (segs : List String) (slash : Bool) (withLength : Bool := false) : Prog (Option Meta) := do
  if segs.isEmpty || slash then statAs segs true withLength
  else
    match ← statAs segs false withLength with
    | some m => return some m
    | none => statAs segs true withLength

/-- Does the parent collection of `segs` exist? -/
def parentExists (segs : List String) : Prog Bool := do
  if segs.length ≤ 1 then return true
  return (← statAs segs.dropLast true false).isSome

/-! ## The `If` header -/

/-- The path a resource tag names, inside this server. -/
def tagPath (host : Option String) (tag : String) : Option DavPath :=
  match parseDestination host tag with
  | .ok p => some p
  | .error _ => none

/-- Does one list hold for its resource (RFC 4918 §10.4.2, §10.4.3,
§10.4.4)? -/
def listHolds (st : DavState) (target : DavPath) (host : Option String) (l : IfList) : Prog Bool := do
  let p := match l.tag with
    | none => some target
    | some t => tagPath host t
  match p with
  | none => return false
  | some p =>
    -- The entity tag of the resource, only when a condition names one.
    let etag ← if l.conds.any (·.etag.isSome) && p.segs.length ≥ 1 then do
        let m ← resolve (inner p) p.slash
        pure (m.bind (·.etag))
      else pure none
    return l.conds.all (fun c =>
      let v := match c.token, c.etag with
        | some t, _ => st.locks.any (fun lk => lk.token == t && lk.covers p)
        | none, some e => (etag.map (etagMatches · e)).getD false
        | none, none => false
      if c.negated then !v else v)

/-- Is the `If` header true: does any list hold (§10.4.2)? -/
def ifHolds (st : DavState) (target : DavPath) (host : Option String) (ls : List IfList) : Prog Bool := do
  for l in ls do
    if ← listHolds st target host l then return true
  return false

/-! ## Copying a tree -/

/-- Copy the resource `src` to `dst` (both storage segments in one mount),
the members of a collection when `deep`. At most 64 levels. The result is
`none`, or the first refusal (the storage path and the answer). -/
def copyTree : Nat → List String → List String → Bool → Bool → Prog (Option (String × BAns))
  | 0, src, _, _, _ => return some (storagePath src true, { status := 507, detail := "the tree is deeper than 64 levels" })
  | n + 1, src, dst, isColl, deep => do
    if !isColl then
      let g ← ask (.get (storagePath src false))
      if !g.ok then return some (storagePath src false, g)
      let ct := ((g.info.bind (·.contentType)).getD "application/octet-stream")
      let w ← ask (.put (storagePath dst false) ct g.body false)
      if !w.ok then return some (storagePath dst false, w)
      return none
    let w ← ask (.put (storagePath dst true) "" ByteArray.empty false)
    if !w.ok then return some (storagePath dst true, w)
    if !deep then return none
    let l ← ask (.list (storagePath src true))
    if !l.ok then return some (storagePath src true, l)
    for m in l.members do
      let name := lastName m.path
      match ← copyTree n (src ++ [name]) (dst ++ [name]) m.isColl true with
      | some f => return some f
      | none => pure ()
    return none

/-- The dead properties of every resource at or under `src`, copied to the
same place under `dst`. -/
def copyProps (st : DavState) (src dst : DavPath) : DavState :=
  let moved := st.props.filterMap (fun (k, ps) =>
    match parseTarget k with
    | some kp =>
      if kp.within src.asFile then some ((DavPath.key { segs := dst.segs ++ kp.segs.drop src.segs.length }), ps)
      else none
    | none => none)
  let keys := moved.map (·.1)
  { st with props := st.props.filter (fun (k, _) => !keys.contains k) ++ moved }

/-- Forget the dead properties and the locks of every resource at or under
`p`. -/
def forget (st : DavState) (p : DavPath) (locks : Bool) : DavState :=
  { st with
    props := st.props.filter (fun (k, _) => match parseTarget k with
      | some kp => !kp.within p.asFile
      | none => true)
    locks := if locks then st.locks.filter (fun l => !l.within p) else st.locks }

/-! ## The methods -/

def allowed : String := "OPTIONS, GET, HEAD, PUT, DELETE, MKCOL, COPY, MOVE, PROPFIND, PROPPATCH, LOCK, UNLOCK"

def optionsResp : DavResponse :=
  { status := 200, headers := [("dav", "1, 2"), ("ms-author-via", "DAV"), ("allow", allowed),
                               ("content-length", "0")] }

/-- A collection as a page of links, for a web browser. -/
def htmlIndex (title : String) (items : List (String × String)) : DavResponse :=
  let li := items.foldl (fun acc (href, name) =>
    acc ++ "<li><a href=\"" ++ escapeAttrValue href ++ "\">" ++ escapeText name ++ "</a></li>\n") ""
  { status := 200, headers := [("content-type", "text/html; charset=utf-8")]
    body := ("<!doctype html>\n<html><head><meta charset=\"utf-8\"><title>" ++ escapeText title ++
             "</title></head><body><h1>" ++ escapeText title ++ "</h1><ul>\n" ++ li ++
             "</ul></body></html>\n").toUTF8 }

def rootMeta : Meta := { path := "/", isColl := true }

/-- PROPFIND (RFC 4918 §9.1). -/
def propfind (cx : Ctx) (st : DavState) (r : DavRequest) (p : DavPath) : Prog DavResponse := do
  let depth := (r.header? "depth").map (fun d => (trimS d).toLower)
  let depth1 ← match depth with
    | some "0" => pure false
    | some "1" => pure true
    | _ => return errResp 403 (dav "propfind-finite-depth")
  let req ← match propfindOf (String.fromUTF8? r.body |>.getD "\uFFFD") with
    | .ok q => pure q
    | .error e => return textResp 400 e
  match p.segs with
  | [] =>
    let self := propfindResponse st cx.now req { segs := [], slash := true } (some "Factoidal") rootMeta
    let kids := if depth1 then cx.mounts.map (fun mv =>
        propfindResponse st cx.now req { segs := [mv.name], slash := true } (some mv.title) rootMeta) else []
    return xmlResp 207 (multistatus (self :: kids))
  | mount :: rest =>
    let title := if rest.isEmpty then (cx.mounts.find? (·.name == mount)).map (·.title) else none
    match ← resolve rest p.slash true with
    | none => return textResp 404 "no resource at this path"
    | some m =>
      let self := propfindResponse st cx.now req p title m
      if !(depth1 && m.isColl) then return xmlResp 207 (multistatus [self])
      let l ← ask (.list (storagePath rest true))
      if !l.ok then return storageRefusal l
      let kids := l.members.map (fun e =>
        propfindResponse st cx.now req { segs := p.segs ++ [lastName e.path], slash := e.isColl } none e)
      return xmlResp 207 (multistatus (self :: kids))

/-- PROPPATCH (RFC 4918 §9.2): every instruction or none. -/
def proppatch (st : DavState) (r : DavRequest) (p : DavPath) (m : Meta) : DavResponse × DavState :=
  match proppatchOf (String.fromUTF8? r.body |>.getD "") with
  | .error e => (textResp 400 e, st)
  | .ok ops =>
    let href := hrefOf p m.isColl
    if ops.any (fun (n, _) => isLive n) then
      let groups := [(403, (ops.filter (isLive ·.1)).map (fun (n, _) => nameNode n)),
                     (424, (ops.filter (!isLive ·.1)).map (fun (n, _) => nameNode n))]
      (xmlResp 207 (multistatus [propResponse href groups]), st)
    else
      let props := ops.foldl (fun (acc : List DeadProp) (n, v) =>
        let rest := acc.filter (·.name != n)
        match v with
        | some value => rest ++ [{ name := n, value }]
        | none => rest) (deadOf st p)
      let others := st.props.filter (·.1 != p.key)
      let st' := { st with props := if props.isEmpty then others else others ++ [(p.key, props)] }
      (xmlResp 207 (multistatus [propResponse href [(200, ops.map (fun (n, _) => nameNode n))]]), st')

/-- The answer to LOCK: the lock in `DAV:lockdiscovery` (RFC 4918 §9.10.1). -/
def lockAnswer (status : Nat) (l : Lock) (now : Nat) : DavResponse :=
  xmlResp status (davDocument (dav "prop" [dav "lockdiscovery" [activeLock l now]]))
    [("lock-token", "<" ++ l.token ++ ">")]

/-- LOCK (RFC 4918 §9.10). -/
def lock (cx : Ctx) (st : DavState) (r : DavRequest) (p : DavPath) (submitted : List String) :
    Prog (DavResponse × DavState) := do
  let timeout := timeoutOf (r.header? "timeout")
  let bodyText := (String.fromUTF8? r.body).getD ""
  if trimS bodyText == "" then
    -- A refresh (§9.10.2): the If header names the lock.
    match st.locks.find? (fun l => submitted.contains l.token && l.covers p) with
    | none => return (errResp 412 (dav "lock-token-submitted"), st)
    | some l =>
      let l' := { l with timeout, expires := cx.now + timeout }
      let st' := { st with locks := st.locks.map (fun x => if x.token == l.token then l' else x) }
      return (lockAnswer 200 l' cx.now, st')
  let info ← match lockinfoOf bodyText with
    | .ok i => pure i
    | .error e => return (textResp 400 e, st)
  let infinite ← match (r.header? "depth").map (fun d => (trimS d).toLower) with
    | none | some "infinity" => pure true
    | some "0" => pure false
    | _ => return (textResp 400 "LOCK takes Depth 0 or infinity", st)
  -- Conflicts (§6.1, §7): an exclusive lock shares the resource with no
  -- other lock; shared locks share it with shared locks.
  match st.locks.find? (fun l =>
      (l.covers p || (infinite && l.within p)) && (l.exclusive || info.exclusive)) with
  | some l =>
    return (errResp 423 (dav "no-conflicting-lock" [davText "href" (hrefOf l.root false)]), st)
  | none =>
  let rest := inner p
  let existing ← resolve rest p.slash
  let created ← match existing with
    | some _ => pure false
    | none => do
      -- A LOCK of an unmapped URL makes an empty resource (§9.10.4).
      if !(← parentExists rest) then return (textResp 409 "the parent collection does not exist", st)
      let w ← ask (.put (storagePath rest false) "application/octet-stream" ByteArray.empty true)
      if !w.ok then return (storageRefusal w, st)
      pure true
  let token := lockToken cx.random st.serial
  let l : Lock := { token, root := p.asFile, infinite := infinite && (existing.map (·.isColl)).getD false,
                    exclusive := info.exclusive, owner := info.owner, timeout,
                    expires := cx.now + timeout }
  let st' := { st with locks := st.locks ++ [l], serial := st.serial + 1 }
  return (lockAnswer (if created then 201 else 200) l cx.now, st')

/-- UNLOCK (RFC 4918 §9.11). -/
def unlock (st : DavState) (r : DavRequest) (p : DavPath) : DavResponse × DavState :=
  match r.header? "lock-token" with
  | none => (textResp 400 "UNLOCK needs a Lock-Token header", st)
  | some v =>
    let t := trimS v
    let t := if t.startsWith "<" && t.endsWith ">" then ((t.drop 1).dropEnd 1).toString else t
    match st.locks.find? (fun l => l.token == t && l.covers p) with
    | none => (errResp 409 (dav "lock-token-matches-request-uri"), st)
    | some _ => ({ status := 204 }, { st with locks := st.locks.filter (·.token != t) })

/-- COPY and MOVE (RFC 4918 §9.8, §9.9). -/
def copyMove (st : DavState) (r : DavRequest) (p : DavPath) (isMove : Bool)
    (submitted : List String) (writable : Bool) : Prog (DavResponse × DavState) := do
  let dst ← match r.header? "destination" with
    | none => return (textResp 400 "COPY and MOVE need a Destination header", st)
    | some v => match parseDestination (r.header? "host") v with
      | .ok d => pure d
      | .error 502 => return (textResp 502 "the destination is on another server", st)
      | .error s => return (textResp s "the Destination header is not a path of this server", st)
  if dst.segs.head? != p.segs.head? then
    return (textResp 502 "the destination is in another mount (RFC 4918 §9.9.4)", st)
  if dst.segs.length ≤ 1 || p.segs.length ≤ 1 then
    return (textResp 403 "the root of a mount is not copied, moved or replaced", st)
  if !writable then return (textResp 403 "this mount is read-only", st)
  let src := inner p
  let dstIn := inner dst
  match ← resolve src p.slash with
  | none => return (textResp 404 "no resource at this path", st)
  | some m =>
  if dst.asFile.within p.asFile || (isMove && p.asFile.within dst.asFile) then
    return (textResp 403 "the source and the destination overlap", st)
  let depth := (r.header? "depth").map (fun d => (trimS d).toLower)
  let deep ← match depth, isMove with
    | none, _ | some "infinity", _ => pure true
    | some "0", false => pure false
    | _, _ => return (textResp 400 "COPY takes Depth 0 or infinity; MOVE takes infinity", st)
  let overwrite := (r.header? "overwrite").map (fun o => (trimS o).toUpper) != some "F"
  if !(← parentExists dstIn) then return (textResp 409 "the destination's parent collection does not exist", st)
  let existing ← resolve dstIn dst.slash
  if existing.isSome && !overwrite then
    return (textResp 412 "the destination exists and Overwrite is F", st)
  -- Locks: the destination is replaced or added; a moved source is removed.
  let needed := neededLocks st dst true true ++ (if isMove then neededLocks st p true true else [])
  match missingToken needed submitted with
  | some l => return (lockedResp l, st)
  | none =>
  if let some e := existing then
    let d ← ask (.delete (storagePath dstIn e.isColl))
    if !d.ok then return (storageRefusal d, st)
  match ← copyTree 64 src dstIn m.isColl deep with
  | some (_, a) => return (storageRefusal a, st)
  | none =>
  let st1 := (forget st dst false)
  let st2 := copyProps st1 p dst
  let st3 ← if isMove then do
      let d ← ask (.delete (storagePath src m.isColl))
      if !d.ok then return (storageRefusal d, st2)
      pure (forget st2 p true)
    else pure st2
  return ({ status := if existing.isSome then 204 else 201 }, st3)

/-- Methods that change a mount. -/
def writeMethods : List String := ["PUT", "DELETE", "MKCOL", "COPY", "MOVE", "PROPPATCH", "LOCK", "UNLOCK"]

/-- The checks made before any storage operation: the method, the target,
the mount, read-only mounts, a malformed `If` header. `some r`: the
request is refused with `r` and changes nothing. -/
def precheck (cx : Ctx) (r : DavRequest) : Option DavResponse :=
  match parseTarget r.target with
  | none => some (textResp 400 "the request target is not a path this server reads")
  | some p =>
    if !(allowed.splitOn ", ").contains r.method then
      some { (textResp 405 "the method is not supported") with headers := [("allow", allowed)] }
    else if (r.header? "if").any (fun v => (parseIf v).isNone) then
      some (textResp 400 "the If header is malformed (RFC 4918 §10.4)")
    else match p.segs with
      | [] =>
        if r.method == "OPTIONS" || r.method == "GET" || r.method == "HEAD" || r.method == "PROPFIND" then none
        else some (textResp 403 "the root collection holds the mounts and is not changed")
      | m :: _ =>
        match cx.mounts.find? (·.name == m) with
        | none => some (textResp 404 "no mount of this name")
        | some mv =>
          if !mv.writable && writeMethods.contains r.method then some (textResp 403 "this mount is read-only")
          else none

/-- The mount a request's storage operations go to. -/
def mountOf (r : DavRequest) : Option String :=
  (parseTarget r.target).bind (fun p => p.segs.head?)

/-- One request. -/
def handle (cx : Ctx) (st0 : DavState) (r : DavRequest) : Prog (DavResponse × DavState) := do
  if let some resp := precheck cx r then return (resp, st0)
  -- Expired locks are gone (§6.6).
  let st := { st0 with locks := st0.locks.filter (·.expires > cx.now) }
  let p := (parseTarget r.target).getD { segs := [] }
  let host := r.header? "host"
  let ifLists := ((r.header? "if").bind parseIf).getD []
  if !ifLists.isEmpty then
    if !(← ifHolds st p host ifLists) then
      return (textResp 412 "the If header is false (RFC 4918 §10.4)", st)
  let submitted := submittedTokens ifLists
  let writable := ((p.segs.head?.bind (fun n => cx.mounts.find? (·.name == n))).map (·.writable)).getD false
  let rest := inner p
  match r.method with
  | "OPTIONS" => return (optionsResp, st)
  | "PROPFIND" => return (← propfind cx st r p, st)
  | "GET" | "HEAD" =>
    match p.segs with
    | [] =>
      let resp := htmlIndex "Factoidal" (cx.mounts.map (fun mv => (hrefOf { segs := [mv.name] } true, mv.title)))
      return ({ resp with body := if r.method == "HEAD" then ByteArray.empty else resp.body }, st)
    | _ =>
    match ← resolve rest p.slash with
    | none => return (textResp 404 "no resource at this path", st)
    | some m =>
      if m.isColl then
        let l ← ask (.list (storagePath rest true))
        if !l.ok then return (storageRefusal l, st)
        let resp := htmlIndex (lastName (storagePath rest true)) (l.members.map (fun e =>
          (hrefOf { segs := p.segs ++ [lastName e.path] } e.isColl, lastName e.path)))
        return ({ resp with body := if r.method == "HEAD" then ByteArray.empty else resp.body }, st)
      let g ← ask (.get (storagePath rest false))
      if !g.ok then return (storageRefusal g, st)
      let hs := [("content-type", ((g.info.bind (·.contentType)).getD "application/octet-stream"))] ++
        ((g.info.bind (·.etag)).map (fun e => [("etag", e)])).getD [] ++
        ((g.info.bind (·.modified)).map (fun d => [("last-modified", d)])).getD [] ++
        [("content-length", toString g.body.size)]
      return ({ status := 200, headers := hs, body := if r.method == "HEAD" then ByteArray.empty else g.body }, st)
  | "PUT" =>
    if rest.isEmpty || p.slash then return (textResp 405 "PUT does not write a collection", st)
    if !(← parentExists rest) then return (textResp 409 "the parent collection does not exist", st)
    if (← statAs rest true false).isSome then return (textResp 405 "a collection has this name", st)
    let exists_ := (← statAs rest false false).isSome
    match missingToken (neededLocks st p false (!exists_)) submitted with
    | some l => return (lockedResp l, st)
    | none =>
    let ct := ((r.header? "content-type").filter (· != "")).getD "application/octet-stream"
    let w ← ask (.put (storagePath rest false) ct r.body false)
    if !w.ok then return (storageRefusal w, st)
    let hs := ((w.info.bind (·.etag)).map (fun e => [("etag", e)])).getD []
    return ({ status := if exists_ then 204 else 201, headers := hs }, st)
  | "DELETE" =>
    if rest.isEmpty then return (textResp 403 "the root of a mount is not deleted", st)
    match ← resolve rest p.slash with
    | none => return (textResp 404 "no resource at this path", st)
    | some m =>
      if m.isColl && (r.header? "depth").any (fun d => (trimS d).toLower != "infinity") then
        return (textResp 400 "DELETE of a collection takes Depth infinity (RFC 4918 §9.6.1)", st)
      match missingToken (neededLocks st p true true) submitted with
      | some l => return (lockedResp l, st)
      | none =>
      let d ← ask (.delete (storagePath rest m.isColl))
      if !d.ok then return (storageRefusal d, st)
      return ({ status := 204 }, forget st p true)
  | "MKCOL" =>
    if r.body.size > 0 then return (textResp 415 "MKCOL takes no body (RFC 4918 §9.3)", st)
    if rest.isEmpty then return (textResp 405 "the mount root exists", st)
    if (← resolve rest false).isSome then return (textResp 405 "a resource has this name", st)
    if !(← parentExists rest) then return (textResp 409 "the parent collection does not exist", st)
    match missingToken (neededLocks st p false true) submitted with
    | some l => return (lockedResp l, st)
    | none =>
    let w ← ask (.put (storagePath rest true) "" ByteArray.empty true)
    if !w.ok then return (storageRefusal w, st)
    return ({ status := 201 }, st)
  | "COPY" => copyMove st r p false submitted writable
  | "MOVE" => copyMove st r p true submitted writable
  | "PROPPATCH" =>
    match ← resolve rest p.slash with
    | none => return (textResp 404 "no resource at this path", st)
    | some m =>
      match missingToken (neededLocks st p false false) submitted with
      | some l => return (lockedResp l, st)
      | none => return proppatch st r p m
  | "LOCK" =>
    if rest.isEmpty then return (textResp 403 "the root of a mount is not locked", st)
    lock cx st r p submitted
  | "UNLOCK" => return unlock st r p
  | _ => return ({ (textResp 405 "the method is not supported") with headers := [("allow", allowed)] }, st)

/-- A request refused before any storage operation keeps the state it was
given, and names no operation. -/
theorem refused_keeps_state (cx : Ctx) (st : DavState) (r : DavRequest) (resp : DavResponse)
    (h : precheck cx r = some resp) : handle cx st r = .pure (resp, st) := by
  unfold handle
  simp only [h]
  rfl

end L4Factoidal.WebDAV
