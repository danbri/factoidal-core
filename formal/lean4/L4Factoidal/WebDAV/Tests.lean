/-
L4Factoidal.WebDAV.Tests — `#guard`s for the WebDAV server.
https://github.com/danbri/factoidal/issues/1066

Two loopbacks, in process, with no host:

* local: the server's programs run against this repository's own LWS server
  (`LWS.step MemStore`), each storage operation translated by
  `Local.localRequest` and read back by `Local.answerOf`, as the wasm handle
  does with a storage directory;
* remote: the same programs, each storage operation run as an LWS client
  operation (`Remote.remoteOp`, `LWS.Client.step`) whose requests go to
  `LWS.step MemStore`, as the wasm handle does with the host's `fetch`.

Every method and every status the server writes is reached at least once.
-/
import L4Factoidal.WebDAV.Server
import L4Factoidal.WebDAV.Local
import L4Factoidal.WebDAV.Remote

namespace L4Factoidal.WebDAV.Tests

open L4Factoidal.WebDAV
open L4Factoidal.LWS (MemState MemStore)

def lcfg : L4Factoidal.LWS.Config := { baseIri := "http://localhost/", pageSize := 0 }

def emptyStorage : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := ByteArray.empty, mtime := 0 }], clock := 1000000000 }

def toLws (q : LwsReq) : L4Factoidal.HTTP.Request :=
  { method := q.method, path := q.target, queryStr := "", headers := q.headers, body := "", bytes := some q.body }

/-- One storage operation against the reference LWS server, as a local mount
does it. -/
def lwsRun (st : MemState) (op : BOp) : BAns × MemState :=
  let (resp, st') := L4Factoidal.LWS.step MemStore lcfg (toLws (localRequest op)) st
  (answerOf "http://localhost/" op resp.status resp.headers resp.content, st')

/-! ### The remote loopback -/

def RB : String := "http://example.org/"
def rcfg : L4Factoidal.LWS.Config := { baseIri := RB, pageSize := 2 }

/-- A stand-in for the crypto: no credential is used in the loopback. -/
def Vt : L4Factoidal.Authz.Crypto :=
  { verifiers := { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }
    es256Sign := fun _ _ _ => none, es256Public := fun _ => none
    eddsaSign := fun _ _ => ByteArray.empty, eddsaPublic := fun _ => none
    p256Decompress := fun _ => none }

def toServer (r : L4Factoidal.LWS.Client.Req) : L4Factoidal.HTTP.Request :=
  { method := r.method, path := String.ofList (r.url.toList.drop (RB.length - 1)), queryStr := ""
    headers := r.headers.map (fun (n, v) => (n.toLower, v)), body := "", bytes := some r.body }

def clientLoop (st : MemState) (s : L4Factoidal.LWS.Client.ClientState) (a : L4Factoidal.LWS.Client.Action) :
    Nat → L4Factoidal.LWS.Client.Action × MemState
  | 0 => (a, st)
  | n + 1 => match a with
    | .fetch r =>
      let (resp, st') := L4Factoidal.LWS.step MemStore rcfg (toServer r) st
      let (s', a') := L4Factoidal.LWS.Client.step Vt s
        (.response { status := resp.status, headers := resp.headers, body := resp.content })
      clientLoop st' s' a' n
    | _ => (a, st)

/-- One storage operation through the LWS client, as an lws mount does it. -/
def remoteRun (st : MemState) (op : BOp) : BAns × MemState :=
  let (s, a) := L4Factoidal.LWS.Client.start Vt (remoteOp RB op) {}
  match clientLoop st s a 64 with
  | (.done res, st') => (answerOfDone RB op res, st')
  | (.fail err, st') => (answerOfFail RB op err, st')
  | (.fetch _, st') => ({ status := 0, detail := "step limit" }, st')

/-! ### Driving requests -/

def mounts : List MountView :=
  [{ name := "m", title := "My files", writable := true }, { name := "ro", title := "Read only", writable := false },
   { name := "n", title := "Other", writable := true }]

structure W where
  st : DavState := {}
  store : MemState := emptyStorage
  last : DavResponse := { status := 0 }
  /-- Was the last request answered within the operation bound? -/
  ran : Bool := true

abbrev Runner := MemState → BOp → BAns × MemState

def reqOf (method target : String) (headers : List (String × String) := []) (body : String := "") : DavRequest :=
  { method, target, headers := (("host", "localhost:8090") :: headers), body := body.toUTF8 }

def step (run : Runner) (w : W) (r : DavRequest) (now : Nat := 2000000000) : W :=
  let cx : Ctx := { mounts, now, random := ByteArray.mk (Array.replicate 16 (UInt8.ofNat (w.st.serial + 1))) }
  match (handle cx w.st r).runPure run 100000 w.store with
  | some ((resp, st), store) => { st, store, last := resp, ran := true }
  | none => { w with ran := false, last := { status := 0 } }

def go (run : Runner) (rs : List DavRequest) : W := rs.foldl (step run) {}

def statuses (run : Runner) (rs : List DavRequest) : List Nat :=
  (rs.foldl (fun (acc : W × List Nat) r => let w := step run acc.1 r; (w, acc.2 ++ [w.last.status])) ({}, [])).2

def hdr (r : DavResponse) (n : String) : Option String := (r.headers.find? (·.1 == n)).map (·.2)
def bodyText (r : DavResponse) : String := (String.fromUTF8? r.body).getD ""
def has (r : DavResponse) (s : String) : Bool := ((bodyText r).splitOn s).length > 1
def count (r : DavResponse) (s : String) : Nat := ((bodyText r).splitOn s).length - 1

def put (t body : String) (hs : List (String × String) := []) : DavRequest :=
  reqOf "PUT" t (("content-type", "text/plain") :: hs) body
def pf (t depth : String) (body : String := "") : DavRequest := reqOf "PROPFIND" t [("depth", depth)] body

def lockBody (exclusive : Bool := true) : String :=
  "<?xml version=\"1.0\"?><D:lockinfo xmlns:D=\"DAV:\"><D:lockscope>" ++
  (if exclusive then "<D:exclusive/>" else "<D:shared/>") ++
  "</D:lockscope><D:locktype><D:write/></D:locktype><D:owner>litmus</D:owner></D:lockinfo>"

/-- Every check runs on both kinds of mount. -/
def both (f : Runner → Bool) : Bool := f lwsRun && f remoteRun

/-! ## OPTIONS and the root -/

#guard both fun run =>
  let w := go run [reqOf "OPTIONS" "/m/"]
  w.last.status == 200 && hdr w.last "dav" == some "1, 2" && hdr w.last "ms-author-via" == some "DAV"
#guard both fun run =>
  let w := go run [pf "/" "1"]
  w.last.status == 207 && has w.last "<D:href>/m/</D:href>" && has w.last "<D:href>/ro/</D:href>" &&
  has w.last "<D:displayname>My files</D:displayname>"
#guard both fun run => (go run [reqOf "PUT" "/" [] "x"]).last.status == 403
#guard both fun run => (go run [reqOf "GET" "/nomount/a"]).last.status == 404
#guard both fun run => (go run [reqOf "GET" "/m/a/../b"]).last.status == 400
#guard both fun run => (go run [reqOf "PATCH" "/m/a"]).last.status == 405

/-! ## PUT, GET, HEAD, DELETE -/

#guard both fun run => statuses run
  [put "/m/a.txt" "hello", reqOf "GET" "/m/a.txt", put "/m/a.txt" "hello again", reqOf "HEAD" "/m/a.txt",
   reqOf "DELETE" "/m/a.txt", reqOf "GET" "/m/a.txt", reqOf "DELETE" "/m/a.txt"] ==
  [201, 200, 204, 200, 204, 404, 404]
#guard both fun run =>
  let w := go run [put "/m/a.txt" "hello", reqOf "GET" "/m/a.txt"]
  bodyText w.last == "hello" && hdr w.last "content-type" == some "text/plain" && (hdr w.last "etag").isSome
-- No parent collection: 409 (RFC 4918 §9.7.1).
#guard both fun run => (go run [put "/m/no/a.txt" "x"]).last.status == 409
-- A UTF-8 name, written in two spellings of its percent-encoding.
#guard both fun run => statuses run [put "/m/%C3%A9t%C3%A9.txt" "x", reqOf "GET" "/m/%c3%a9t%c3%a9.txt"] == [201, 200]
-- Read-only mount.
#guard both fun run => (go run [put "/ro/a.txt" "x"]).last.status == 403

/-! ## MKCOL -/

#guard both fun run => statuses run
  [reqOf "MKCOL" "/m/c", reqOf "MKCOL" "/m/c/", reqOf "MKCOL" "/m/q/r", reqOf "MKCOL" "/m/d" [] "<x/>",
   put "/m/f" "x", reqOf "MKCOL" "/m/f", put "/m/c/" "x"] ==
  [201, 405, 409, 415, 201, 405, 405]

/-! ## PROPFIND -/

#guard both fun run =>
  let w := go run [put "/m/a.txt" "hello", pf "/m/a.txt" "0"]
  w.last.status == 207 && has w.last "<D:getcontentlength>5</D:getcontentlength>" &&
  has w.last "<D:resourcetype/>" && has w.last "<D:getlastmodified>" && has w.last "<D:getetag>"
-- Depth 1 lists each member once, collections with `/`.
#guard both fun run =>
  let w := go run [put "/m/a.txt" "hello", reqOf "MKCOL" "/m/c", put "/m/c/b.txt" "b", pf "/m/" "1"]
  w.last.status == 207 && count w.last "<D:href>/m/a.txt</D:href>" == 1 &&
  count w.last "<D:href>/m/c/</D:href>" == 1 && count w.last "<D:href>/m/</D:href>" == 1 &&
  !has w.last "/m/c/b.txt" && has w.last "<D:collection/>"
-- A collection named without `/`.
#guard both fun run => (go run [reqOf "MKCOL" "/m/c", pf "/m/c" "0"]).last.status == 207
#guard both fun run =>
  let w := go run [pf "/m/" "infinity"]
  w.last.status == 403 && has w.last "propfind-finite-depth"
#guard both fun run => (go run [pf "/m/" "infinity" "", reqOf "PROPFIND" "/m/"]).last.status == 403
#guard both fun run => (go run [pf "/m/none" "0"]).last.status == 404
#guard both fun run => (go run [pf "/m/" "0" "<D:propfind xmlns:D=\"DAV:\"><D:prop>"]).last.status == 400
#guard both fun run =>
  let w := go run [pf "/m/" "0" "<D:propfind xmlns:D=\"DAV:\"><D:propname/></D:propfind>"]
  w.last.status == 207 && has w.last "<D:supportedlock/>"
#guard both fun run =>
  let w := go run [pf "/m/" "0" "<D:propfind xmlns:D=\"DAV:\"><D:prop><D:resourcetype/><Z:x xmlns:Z=\"http://z/\"/></D:prop></D:propfind>"]
  w.last.status == 207 && has w.last "HTTP/1.1 404 Not Found" && has w.last "<D:collection/>"

/-! ## PROPPATCH -/

def setProp (v : String) : String :=
  "<D:propertyupdate xmlns:D=\"DAV:\" xmlns:Z=\"http://z/\"><D:set><D:prop><Z:colour>" ++ v ++
  "</Z:colour></D:prop></D:set></D:propertyupdate>"
def removeProp : String :=
  "<D:propertyupdate xmlns:D=\"DAV:\" xmlns:Z=\"http://z/\"><D:remove><D:prop><Z:colour/></D:prop></D:remove></D:propertyupdate>"
def getProp : String :=
  "<D:propfind xmlns:D=\"DAV:\"><D:prop><Z:colour xmlns:Z=\"http://z/\"/></D:prop></D:propfind>"

#guard both fun run =>
  let w := go run [put "/m/a.txt" "x", reqOf "PROPPATCH" "/m/a.txt" [] (setProp "red"), pf "/m/a.txt" "0" getProp]
  w.last.status == 207 && has w.last ">red</Z:colour>" && has w.last "HTTP/1.1 200 OK"
#guard both fun run =>
  let w := go run [put "/m/a.txt" "x", reqOf "PROPPATCH" "/m/a.txt" [] (setProp "red"),
                   reqOf "PROPPATCH" "/m/a.txt" [] removeProp, pf "/m/a.txt" "0" getProp]
  has w.last "HTTP/1.1 404 Not Found"
-- A live property is protected: 403, and the others fail with it (424).
#guard both fun run =>
  let w := go run [put "/m/a.txt" "x", reqOf "PROPPATCH" "/m/a.txt" []
    "<D:propertyupdate xmlns:D=\"DAV:\"><D:set><D:prop><D:getetag>x</D:getetag><D:foo>y</D:foo></D:prop></D:set></D:propertyupdate>"]
  w.last.status == 207 && has w.last "403 Forbidden" && has w.last "424 Failed Dependency"
-- Dead properties move with MOVE and are copied by COPY.
#guard both fun run =>
  let w := go run [put "/m/a.txt" "x", reqOf "PROPPATCH" "/m/a.txt" [] (setProp "blue"),
                   reqOf "MOVE" "/m/a.txt" [("destination", "http://localhost:8090/m/b.txt")],
                   pf "/m/b.txt" "0" getProp]
  w.last.status == 207 && has w.last ">blue</Z:colour>"

/-! ## COPY and MOVE -/

#guard both fun run => statuses run
  [put "/m/a.txt" "x", reqOf "COPY" "/m/a.txt" [("destination", "/m/b.txt")],
   reqOf "COPY" "/m/a.txt" [("destination", "/m/b.txt")],
   reqOf "COPY" "/m/a.txt" [("destination", "/m/b.txt"), ("overwrite", "F")],
   reqOf "COPY" "/m/a.txt" [("destination", "/m/no/b.txt")],
   reqOf "COPY" "/m/a.txt" [("destination", "/n/b.txt")],
   reqOf "COPY" "/m/a.txt" [("destination", "http://elsewhere/m/b.txt")],
   reqOf "COPY" "/m/a.txt" [],
   reqOf "GET" "/m/b.txt"] ==
  [201, 201, 204, 412, 409, 502, 502, 400, 200]
#guard both fun run => statuses run
  [reqOf "MKCOL" "/m/c", put "/m/c/x.txt" "x", reqOf "MKCOL" "/m/c/s", put "/m/c/s/y.txt" "y",
   reqOf "COPY" "/m/c/" [("destination", "/m/d/")], reqOf "GET" "/m/d/s/y.txt",
   reqOf "COPY" "/m/c/" [("destination", "/m/e/"), ("depth", "0")], reqOf "GET" "/m/e/x.txt",
   reqOf "MOVE" "/m/c/" [("destination", "/m/f/")], reqOf "GET" "/m/c/x.txt", reqOf "GET" "/m/f/s/y.txt",
   reqOf "MOVE" "/m/f/" [("destination", "/m/f/g/")]] ==
  [201, 201, 201, 201, 201, 200, 201, 404, 201, 404, 200, 403]

/-! ## LOCK and UNLOCK -/

def tokenOf (r : DavResponse) : String :=
  let t := (hdr r "lock-token").getD ""
  ((t.drop 1).dropEnd 1).toString

#guard both fun run =>
  let w := go run [put "/m/a.txt" "x", reqOf "LOCK" "/m/a.txt" [] (lockBody)]
  w.last.status == 200 && (hdr w.last "lock-token").isSome && has w.last "<D:lockdiscovery>" &&
  has w.last ">litmus</D:owner>"
#guard both fun run =>
  let w0 := go run [put "/m/a.txt" "x", reqOf "LOCK" "/m/a.txt" [("timeout", "Second-60")] (lockBody)]
  let t := tokenOf w0.last
  let seq := [ put "/m/a.txt" "y"
             , put "/m/a.txt" "y" [("if", "(<" ++ t ++ ">)")]
             , put "/m/a.txt" "y" [("if", "(<urn:uuid:wrong>) (Not <DAV:no-lock>)")]
             , put "/m/a.txt" "y" [("if", "(<urn:uuid:wrong>)")]
             , reqOf "LOCK" "/m/a.txt" [] (lockBody)
             , reqOf "LOCK" "/m/a.txt" [("if", "(<" ++ t ++ ">)")]
             , reqOf "UNLOCK" "/m/a.txt" [("lock-token", "<urn:uuid:wrong>")]
             , reqOf "UNLOCK" "/m/a.txt" [("lock-token", "<" ++ t ++ ">")]
             , put "/m/a.txt" "z" ]
  let (_, ss) := seq.foldl (fun (acc : W × List Nat) r => let w := step run acc.1 r; (w, acc.2 ++ [w.last.status])) (w0, [])
  ss == [423, 204, 423, 412, 423, 200, 409, 204, 204]
-- A lock expires.
#guard both fun run =>
  let w0 := go run [put "/m/a.txt" "x", reqOf "LOCK" "/m/a.txt" [("timeout", "Second-60")] (lockBody)]
  (step run w0 (put "/m/a.txt" "y") 2000000061).last.status == 204
-- Shared locks share; an exclusive lock does not.
#guard both fun run => statuses run
  [put "/m/a.txt" "x", reqOf "LOCK" "/m/a.txt" [] (lockBody false), reqOf "LOCK" "/m/a.txt" [] (lockBody false),
   reqOf "LOCK" "/m/a.txt" [] (lockBody true)] == [201, 200, 200, 423]
-- A depth-infinity lock on a collection covers a new member.
#guard both fun run =>
  let w0 := go run [reqOf "MKCOL" "/m/c", reqOf "LOCK" "/m/c/" [] (lockBody)]
  let t := tokenOf w0.last
  (step run w0 (put "/m/c/n.txt" "x")).last.status == 423 &&
  (step run w0 (put "/m/c/n.txt" "x" [("if", "(<" ++ t ++ ">)")])).last.status == 201 &&
  (step run w0 (reqOf "DELETE" "/m/c/")).last.status == 423
-- A LOCK of an unmapped URL makes an empty resource (201).
#guard both fun run =>
  let w := go run [reqOf "LOCK" "/m/new.txt" [] (lockBody), reqOf "GET" "/m/new.txt"]
  w.last.status == 200 && w.last.body.size == 0
#guard both fun run => (go run [reqOf "LOCK" "/m/no/new.txt" [] (lockBody)]).last.status == 409
#guard both fun run => (go run [put "/m/a.txt" "x", reqOf "LOCK" "/m/a.txt" [] "<bad"]).last.status == 400
#guard both fun run => (go run [put "/m/a.txt" "x", reqOf "UNLOCK" "/m/a.txt"]).last.status == 400
-- An If header with an entity tag (RFC 4918 §10.4.8).
#guard both fun run =>
  let w0 := go run [put "/m/a.txt" "x", reqOf "HEAD" "/m/a.txt"]
  let e := (hdr w0.last "etag").getD ""
  (step run w0 (put "/m/a.txt" "y" [("if", "([" ++ e ++ "])")])).last.status == 204 &&
  (step run w0 (put "/m/a.txt" "y" [("if", "([\"nope\"])")])).last.status == 412
#guard both fun run => (go run [put "/m/a.txt" "x" [("if", "(<urn:x>")]]).last.status == 400

/-! ## GET of a collection -/

#guard both fun run =>
  let w := go run [put "/m/a b.txt" "x", reqOf "GET" "/m/"]
  w.last.status == 200 && has w.last "href=\"/m/a%20b.txt\""

/-! ## Theorems -/

/-- A request the precheck refuses leaves the state and the storage as they
were, in every loopback. -/
theorem refused_no_change (run : Runner) (cx : Ctx) (st : DavState) (store : MemState)
    (r : DavRequest) (resp : DavResponse) (h : precheck cx r = some resp) :
    (handle cx st r).runPure run 1 store = some ((resp, st), store) := by
  rw [refused_keeps_state cx st r resp h]
  rfl

end L4Factoidal.WebDAV.Tests
