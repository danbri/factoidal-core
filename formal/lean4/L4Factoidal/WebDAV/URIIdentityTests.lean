import L4Factoidal.WebDAV.Tests

/- Opaque resource identity across public LWS operations and DAV routing.
   No direct MemStore entry insertion: seeds use the same public storage
   requests/client loopback as production. This is not a socket/WASM test. -/
namespace L4Factoidal.WebDAV.URIIdentityTests
open L4Factoidal.WebDAV L4Factoidal.WebDAV.Tests L4Factoidal.JSON

def names : List String :=
  ["colon:name","colon%3Aname","colon%253Aname","a","%C3%A9"]

def seed (run : Runner) (keys : List String) : W := Id.run do
  let (_,container) := run emptyStorage (.put "/names/" "" ByteArray.empty true)
  let mut store := container
  for key in keys do
    let (_,next) := run store (.put ("/names/"++key) "text/plain" ("bytes:"++key).toUTF8 true)
    store := next
  return {store}

def readsOwnBytes (run : Runner) (w : W) (mount directory : String) : Bool :=
  names.all fun name =>
    let get := stepAs true "u" run w (reqOf "GET" (mount++directory++name))
    let head := stepAs true "u" run w (reqOf "HEAD" (mount++directory++name))
    get.ran && head.ran && get.last.status == 200 && head.last.status == 200 &&
      bodyText get.last == "bytes:"++name && head.last.body.isEmpty &&
      hdr get.last "etag" == hdr head.last "etag" &&
      hdr get.last "content-length" == hdr head.last "content-length"

-- Exact key seeding makes the raw-only and escaped-only regressions independent.
#guard both fun run =>
  let raw := seed run ["colon:name"]
  let escaped := seed run ["colon%3Aname"]
  (stepAs true "u" run raw (reqOf "GET" "/m/names/colon:name")).last.status == 200 &&
  (stepAs true "u" run raw (reqOf "GET" "/m/names/colon%3Aname")).last.status == 404 &&
  (stepAs true "u" run escaped (reqOf "GET" "/m/names/colon%3Aname")).last.status == 200 &&
  (stepAs true "u" run escaped (reqOf "GET" "/m/names/colon:name")).last.status == 404

-- Required equivalent URI aliases; currently RED against the lexical-key
-- LWS boundary. Do not weaken these to 404 to accommodate that defect.
#guard both fun run =>
  let w := seed run ["a","%C3%A9"]
  (stepAs true "u" run w (reqOf "GET" "/m/names/%61")).last.status == 200 &&
  (stepAs true "u" run w (reqOf "GET" "/m/names/%c3%a9")).last.status == 200

#guard both fun run => readsOwnBytes run (seed run names) "/m" "/names/"
#guard both fun run => readsOwnBytes run (seed run names) "/%6d" "/names/"

#guard both fun run =>
  let w := seed run names
  let listed := stepAs true "u" run w (pf "/%6d/names/" "1")
  let index := stepAs true "u" run w (reqOf "GET" "/m/names/")
  listed.last.status == 207 && index.last.status == 200 &&
  names.all fun name => has listed.last ("<D:href>/m/names/"++name++"</D:href>") &&
    has index.last ("href=\"/m/names/"++name++"\"")

#guard both fun run =>
  let copied := step run (seed run names) (reqOf "COPY" "/m/names/" [("destination","/m/copied/")])
  copied.last.status == 201 && readsOwnBytes run copied "/m" "/copied/"

#guard both fun run =>
  let moved := step run (seed run names) (reqOf "MOVE" "/m/names/" [("destination","/m/moved/")])
  moved.last.status == 201 && readsOwnBytes run moved "/m" "/moved/" &&
    (step run moved (reqOf "GET" "/m/names/colon%3Aname")).last.status == 404

#guard both fun run =>
  let locked := step run (seed run names) (reqOf "LOCK" "/%6d/names/colon%3Aname" [] (lockBody true))
  locked.last.status == 200 &&
    (step run locked (put "/m/names/colon%3Aname" "blocked")).last.status == 423 &&
    (step run locked (put "/m/names/colon:name" "independent")).last.status == 204

#guard both fun run =>
  let changed := step run (seed run names) (reqOf "PROPPATCH" "/%6d/names/colon%3Aname" [] (setProp "encoded-only"))
  let encoded := step run changed (pf "/m/names/colon%3Aname" "0" getProp)
  let raw := step run changed (pf "/m/names/colon:name" "0" getProp)
  let copied := step run changed (reqOf "COPY" "/m/names/" [("destination","/m/properties/")])
  changed.last.status == 207 && has encoded.last ">encoded-only</Z:colour>" &&
    !has raw.last ">encoded-only</Z:colour>" &&
    has (step run copied (pf "/m/properties/colon%3Aname" "0" getProp)).last ">encoded-only</Z:colour>" &&
    !has (step run copied (pf "/m/properties/colon:name" "0" getProp)).last ">encoded-only</Z:colour>"

#guard ["/m/%2e%2e/x","/m/a%2Fb","/m/a%5Cb","/m/a%00b","/m/../x",
  "/m/a\\b","/m/%zz","/m/%FF","/m/#frag"].all fun path => (parseTarget path).isNone
#guard (parseTarget "/m/%252e%252e/%252f").map DavPath.href == some "/m/%252e%252e/%252f"
#guard ((parseTarget "/%6d/names/colon%3Aname").map DavPath.key) == some "/m/names/colon%3Aname"

private def legacy (labels : String) : String :=
  "{\"format\":\"factoidal-webdav-state\",\"version\":1,\"serial\":0,\"props\":[],\"locks\":[" ++
  "{\"token\":\"t\",\"root\":{\"segs\":"++labels++",\"slash\":false},\"infinite\":false," ++
  "\"exclusive\":true,\"owner\":null,\"timeout\":3600,\"expires\":3000000000}]}"

#guard match stateOfText (legacy "[\"m\",\"colon%3Aname\"]") with
  | .ok st => st.locks.head?.map (·.root.key) == some "/m/colon%253Aname" && roundTrips st
  | _ => false
#guard match stateOfText (legacy "[\"m\",\"colon:name\"]") with
  | .ok st => st.locks.head?.map (·.root.key) == some "/m/colon:name"
  | _ => false

private def stateFor (root : DavPath) : DavState :=
  {locks := [{token:="t",root,infinite:=false,exclusive:=true,timeout:=3600,expires:=3000000000}],
   props := [(root.key,[])]}
#guard names.all fun name =>
  match parseTarget ("/m/names/"++name) with
  | some root => roundTrips (stateFor root)
  | none => false
#guard (stateOfText (stateText (stateFor {segs:=["m","raw"],encodedInner:=some ["different"]}))).toOption.isNone
#guard (stateOfText (stateText (stateFor {segs:=["m","raw"],encodedInner:=some ["raw?ignored"]}))).toOption.isNone
#guard (stateOfText (legacy "[\"m\",\"..\"]")).toOption.isNone

end L4Factoidal.WebDAV.URIIdentityTests
