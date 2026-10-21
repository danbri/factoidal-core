/-
L4Factoidal.LWS.Operations — the create, read, update and delete operations
of the Linked Web Storage Protocol 1.0 Core, as ONE total function

  step : Store σ → Config → Request → σ → Response × σ

Source: https://w3c.github.io/lws-protocol/lws10-core/ (editor's draft, read
2026-09-06), section "Resource Access":

  "An operation is any of the following actions that can be performed on a
  served resource: create resource, read resource, update resource, delete
  resource."

  "success - the operation is believed to have completed. This may be
  accompanied by a resource representation conveying the contents of a
  served resource. A success response is not defined for the create resource
  operation. See instead created."

and from the draft's CG-to-ED delta list:

  "HTTP Server MUST generate a Last-Modified header field in response to GET
  and HEAD requests."

**The draft has no HTTP binding.** Its `Operations`, `Containers` and
`Discovery` sections are headings with empty bodies, and it names no status
codes. Every status code below therefore comes from the Solid Protocol
v0.11.0 binding (https://solidproject.org/TR/protocol §5), which the LWS
draft's Acknowledgements name as its source, and the conformance registry
row for each one records both citations. The day the LWS draft fixes its own
binding, the rows are the difference.

Nothing here reads a clock, a socket or a file. The time comes from the
store's `now`, which the host sets; every mutation stamps `Last-Modified`
from it and then calls `tick`, so a sequence of writes has strictly
increasing modification times and the server-assigned names of POST are
distinct without a separate counter.
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Discovery
import L4Factoidal.LWS.Binding
import L4Factoidal.HTTP.Server

namespace L4Factoidal.LWS

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.HTTP (Request Response)

/-! ## The clock

`Last-Modified` is an HTTP-date (RFC 9110 §5.6.7), which is a civil date in
GMT. The conversion from a count of days to a civil date is Howard
Hinnant's era algorithm, in `Nat` throughout: the offset 719468 puts day
zero of the algorithm at 0000-03-01, and every intermediate subtraction is
between a value and a quotient of itself, so none of them underflows. -/

private def two (n : Nat) : String :=
  if n < 10 then "0" ++ toString n else toString n

private def monthName : Nat → String
  | 1 => "Jan" | 2 => "Feb" | 3 => "Mar" | 4 => "Apr"
  | 5 => "May" | 6 => "Jun" | 7 => "Jul" | 8 => "Aug"
  | 9 => "Sep" | 10 => "Oct" | 11 => "Nov" | _ => "Dec"

private def dayName : Nat → String
  | 0 => "Sun" | 1 => "Mon" | 2 => "Tue" | 3 => "Wed"
  | 4 => "Thu" | 5 => "Fri" | _ => "Sat"

/-- The civil year, month and day of a count of days since 1970-01-01. -/
def civilFromDays (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- An RFC 9110 §5.6.7 IMF-fixdate from seconds since the Unix epoch.
`httpDate 0 = "Thu, 01 Jan 1970 00:00:00 GMT"`. -/
def httpDate (unix : Nat) : String :=
  let days := unix / 86400
  let secs := unix % 86400
  let (y, m, d) := civilFromDays days
  dayName ((days + 4) % 7) ++ ", " ++ two d ++ " " ++ monthName m ++ " " ++
    toString y ++ " " ++ two (secs / 3600) ++ ":" ++ two (secs % 3600 / 60) ++
    ":" ++ two (secs % 60) ++ " GMT"

/-! ## Configuration -/

/-- What a storage knows about itself, and about the agent of the request
in flight. The agent is a WebID the HOST verified; the engine only decides
access from it (see `L4Factoidal.Solid.Server.WAC`). -/
structure Config where
  baseIri : String := "http://localhost/"
  owner   : Option String := none
  agent   : Option String := none
  /-- The patch media types the `Accept-Patch` field advertises. The LWS
  binding of this module applies `application/json-patch+json`; the Solid
  layer adds `text/n3`, which it applies itself. -/
  acceptPatch : List String := [mediaJsonPatch]
deriving Repr, Inhabited

/-! ## Helpers over the store -/

variable {σ : Type}

/-- The paths of the resources a container DIRECTLY contains, in the store's
own order. -/
def containedPaths (S : Store σ) (st : σ) (c : String) : List String :=
  (S.paths st).filter (fun p => contains c p)

/-- Create every missing ancestor container of `p`, newest clock first.

Solid Protocol §5.3: "Servers MUST create intermediate containers and
include corresponding containment triples in container representations
derived from the URI path component of PUT and PATCH requests." The
containment triples are derived from the path hierarchy rather than stored
(`L4Factoidal.Solid.Server.Containment`), so creating the container entry is
the whole of it. -/
def ensureAncestors (S : Store σ) : List String → σ → σ
  | [], st => st
  | a :: rest, st =>
      let st := match S.lookup st a with
        | some _ => st
        | none =>
            let kind := if a == rootPath then ResourceKind.storageRoot else .container
            S.tick (S.put st
              { path := a, kind, contentType := "text/turtle",
                body := ByteArray.empty, mtime := S.now st })
      ensureAncestors S rest st

/-- Touch a container so its `Last-Modified` reflects a change to its
containment triples — Solid Protocol §4.2: "Servers can determine the field
value of the HTTP Last-Modified header field in response to HEAD and GET
requests targeting a container based on changes to containment triples." -/
def touchContainer (S : Store σ) (st : σ) (p : String) : σ :=
  match parent? p with
  | none => st
  | some c =>
      match S.lookup st c with
      | none => st
      | some e => S.tick (S.put st { e with mtime := S.now st })

/-! ## Responses -/

/-- The methods a target accepts. A storage root refuses DELETE, so the
`Allow` field it generates must not list it — Solid Protocol §5.4:
"Server MUST exclude the DELETE method in the field value of the Allow
header field, in response to requests to these resources." -/
def allowFor (kind : ResourceKind) (isRoot : Bool) : List String :=
  if isRoot then ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH"]
  else if kind.isContainer then ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH", "DELETE"]
  else ["GET", "HEAD", "OPTIONS", "PUT", "PATCH", "DELETE"]

/-- Replace a header field, or add it when it is absent. -/
def setHeader (hs : List (String × String)) (k v : String) : List (String × String) :=
  if hs.any (·.1 == k) then hs.map (fun (a, b) => if a == k then (a, v) else (a, b))
  else hs ++ [(k, v)]

/-- The header fields every successful response to a read carries: the
Solid discovery links and the links the LWS draft requires (`linkset`, `up`,
`type`, `lws#storage`) in one `Link` field. -/
def readHeaders (cfg : Config) (e : Entry) (isRoot : Bool) : List (String × String) :=
  [ ("content-type", e.contentType)
  , ("last-modified", httpDate e.mtime)
  , ("allow", String.intercalate ", " (allowFor e.kind isRoot))
  , ("accept-patch", String.intercalate ", " cfg.acceptPatch)
  , ("accept-put", "text/turtle")
  , ("link", renderLinks (discoveryLinks cfg.baseIri cfg.owner e.path e.kind isRoot ++
                          lwsLinks cfg.baseIri e.path e.kind)) ]
  ++ (if e.kind.isContainer then [("accept-post", "text/turtle")] else [])

/-- The header fields of a 201 or 204 that wrote `e`. LWS §Create Resource:
"The server MUST include `Link` headers for key server-managed metadata,
including a link to the parent container (`rel="up"`), and a link to the
created resource's dedicated linkset resource". -/
def writtenHeaders (cfg : Config) (e : Entry) : List (String × String) :=
  [ ("last-modified", httpDate e.mtime)
  , ("etag", etagFor e (if e.kind.isContainer then mediaLwsJson else e.contentType))
  , ("link", renderLinks (lwsLinks cfg.baseIri e.path e.kind)) ]

/-! ## The step function -/

/-- The name a POST assigns. The store's clock is strictly increasing over
mutations (`StoreLaws.nowTick`), so two POSTs to one container never collide
and no counter is needed beside the clock. -/
def assignedName (S : Store σ) (st : σ) : String := "res" ++ toString (S.now st)

/-- Is a `Slug` usable as one path segment? -/
def slugUsable (s : String) : Bool :=
  s != "" && s != "." && s != ".." &&
  !(s.any (fun c => c == '/' || c == '?' || c == '#' || c == '%' || c == '\\' || c.toNat < 32))

/-- The path of a new child of `target`. LWS §Create Resource: "If an
identity hint was provided, the server attempts to incorporate it while
ensuring uniqueness and validity within the container." A clash with an
existing data resource or container of the same name gets the clock as a
suffix; the clock is strictly increasing, so the suffixed name is new. -/
def childPathFor (S : Store σ) (st : σ) (target : String) (hint : Option String)
    (asContainer : Bool) : String :=
  let name := match hint with
    | some s => if slugUsable s then s else assignedName S st
    | none => assignedName S st
  let taken (n : String) : Bool :=
    (S.lookup st (target ++ n)).isSome || (S.lookup st (target ++ n ++ "/")).isSome
  let name := if taken name then name ++ "-" ++ toString (S.now st) else name
  target ++ name ++ (if asContainer then "/" else "")

/-- The resources a container lists: its direct members, auxiliary
resources excluded. -/
def listedMembers (S : Store σ) (st : σ) (c : String) : List Entry :=
  (containedPaths S st c).filterMap (S.lookup st) |>.filter (fun e => !e.kind.isAuxiliary)

/-- The linkset resource of `path` (LWS §Metadata). The links are all
server-managed here, so a PATCH that would change them is refused, which
§Metadata permits: "Servers MAY restrict modifications to specific links
... Servers MUST preserve the links a client is not permitted to modify". -/
def linksetStep (S : Store σ) (cfg : Config) (r : Request) (st : σ)
    (path : String) : Response × σ :=
  match S.lookup st path with
  | none => (problem 404 "no resource has this linkset" (linksetTargetOf path), st)
  | some e =>
      let doc := linksetJson cfg.baseIri path e.kind
      let tag := "\"" ++ toString e.mtime ++ "-ls\""
      let allow := "GET, HEAD, OPTIONS, PATCH"
      let hs : List (String × String) :=
        [ ("content-type", mediaLinkset), ("etag", tag)
        , ("last-modified", httpDate e.mtime), ("allow", allow)
        , ("accept-patch", mediaJsonPatch)
        , ("link", renderLinks [{ target := iriOfPath cfg.baseIri storagePath,
                                  rel := lwsStorageRel }]) ]
      let tagListed (h : String) : Bool :=
        ((r.header? h).map (fun v => (parseTagList v).any (fun t => t == tag || t == "*"))).getD false
      match r.method with
      | "GET" | "HEAD" =>
          if tagListed "if-none-match" then (⟨304, [("etag", tag)], "", none⟩, st)
          else (⟨200, hs, if r.method == "HEAD" then "" else toStringCompact doc, none⟩, st)
      | "OPTIONS" => (⟨204, [("allow", allow), ("accept-patch", mediaJsonPatch)], "", none⟩, st)
      | "PATCH" =>
          let ct := (r.header? "content-type").map (fun c => ((c.splitOn ";").headD c).trim)
          if ct != some mediaJsonPatch then
            (problem 415 "a linkset accepts application/json-patch+json" (linksetTargetOf path)
              [("accept-patch", mediaJsonPatch)], st)
          else if (r.header? "if-match").isSome && !tagListed "if-match" then
            (problem 412 "If-Match did not match the linkset" (linksetTargetOf path), st)
          else match parseJson ((String.fromUTF8? r.content).getD "") with
            | .error _ => (problem 400 "the patch document is not JSON" (linksetTargetOf path), st)
            | .ok p =>
                match applyJsonPatch p doc with
                | .error msg => (problem 409 msg (linksetTargetOf path), st)
                | .ok d' =>
                    if decide (d' = doc) then (⟨204, [("etag", tag)], "", none⟩, st)
                    else (problem 409 "every link of this linkset is server-managed"
                            (linksetTargetOf path), st)
      | _ => (problem 405 "a linkset accepts GET, HEAD, OPTIONS and PATCH"
                (linksetTargetOf path) [("allow", allow)], st)

/-- The storage description resource (LWS §Discovery). -/
def storageStep (cfg : Config) (r : Request) : Response :=
  let allow := "GET, HEAD, OPTIONS"
  match r.method with
  | "GET" | "HEAD" =>
      ⟨200, [ ("content-type", mediaLwsCid), ("allow", allow)
            , ("etag", "\"storage\"")
            , ("link", renderLinks [{ target := iriOfPath cfg.baseIri storagePath,
                                      rel := lwsStorageRel }]) ],
       if r.method == "HEAD" then "" else storageDescription cfg.baseIri, none⟩
  | "OPTIONS" => ⟨204, [("allow", allow)], "", none⟩
  | _ => problem 405 "the storage description is server-managed" storagePath [("allow", allow)]

/-- One operation on a storage path. See `step`. -/
def stepPath (S : Store σ) (cfg : Config) (r : Request) (st : σ) : Response × σ :=
  let target := r.path
  let isRoot := target == rootPath
  let existing := S.lookup st target
  let allowHdr (kind : ResourceKind) : List (String × String) :=
    [("allow", String.intercalate ", " (allowFor kind isRoot))]
  match r.method with
  | "GET" | "HEAD" =>
      match existing with
      | none => (problem 404 "no resource at this path" target, st)
      | some e =>
          let media := if e.kind.isContainer then chooseContainerMedia (r.header? "accept")
                       else e.contentType
          let tag := etagFor e media
          let lm := httpDate e.mtime
          match preconditionFailure r existing (some tag) (some lm) with
          | some resp => (resp, st)
          | none =>
              let base := readHeaders cfg e isRoot ++ [("etag", tag)]
              if e.kind.isContainer then
                let items := listedMembers S st target
                let hs := setHeader base "content-type" (containerContentType media) ++
                  [("vary", "accept")]
                (⟨200, hs, if r.method == "HEAD" then ""
                           else containerBody media cfg.baseIri target items, none⟩, st)
              else
                let hs := base ++ [("accept-ranges", "bytes")]
                let len := e.body.size
                let rangeHdr : Option String :=
                  if r.method != "GET" then none
                  else match r.header? "if-range" with
                    | some ir => if ir.trim == tag then r.header? "range" else none
                    | none => r.header? "range"
                match rangeHdr.bind (fun v => parseRange v len) with
                | none =>
                    (⟨200, hs, "", some (if r.method == "HEAD" then ByteArray.empty else e.body)⟩, st)
                | some none =>
                    (problem 416 "the range is not satisfiable" target
                      [("content-range", "bytes */" ++ toString len)], st)
                | some (some (a, b)) =>
                    (⟨206, hs ++ [("content-range",
                        "bytes " ++ toString a ++ "-" ++ toString b ++ "/" ++ toString len)],
                      "", some (rangeBytes e.body a b)⟩, st)
  | "OPTIONS" =>
      let kind := (match existing with
                   | some e => e.kind
                   | none => if pathIsContainer target then ResourceKind.container else .dataResource)
      (⟨204, [ ("allow", String.intercalate ", " (allowFor kind isRoot))
             , ("accept-patch", String.intercalate ", " cfg.acceptPatch)
             , ("accept-put", "text/turtle")
             , ("accept-post", "text/turtle") ], "", none⟩, st)
  | "PUT" =>
      match r.header? "content-type" with
      | none => (problem 400 "PUT with content requires a Content-Type header field" target, st)
      | some ct =>
          match preconditionFailure r existing
                  (existing.map (fun e => etagFor e e.contentType)) none with
          | some resp => (resp, st)
          | none =>
          match rdfContentRefused ct r.content target with
          | some resp => (resp, st)
          | none =>
              let st := ensureAncestors S (ancestors target) st
              let kind := if pathIsContainer target then
                            (if isRoot then ResourceKind.storageRoot else .container)
                          else .dataResource
              let e : Entry := { path := target, kind, contentType := ct,
                                 body := r.content, mtime := S.now st }
              let st' := touchContainer S (S.tick (S.put st e)) target
              match existing with
              | none   => (⟨201, ("location", target) :: writtenHeaders cfg e, "", none⟩, st')
              | some _ => (⟨204, writtenHeaders cfg e, "", none⟩, st')
  | "POST" =>
      match existing with
      | none => (problem 404 "the target container does not exist" target, st)
      | some parentEntry =>
          if !parentEntry.kind.isContainer then
            (problem 405 "POST creates resources in a container" target
              (allowHdr parentEntry.kind), st)
          else
            match r.header? "content-type" with
            | none => (problem 400 "POST with content requires a Content-Type header field"
                        target, st)
            | some ct =>
                match rdfContentRefused ct r.content target with
                | some resp => (resp, st)
                | none =>
                let linkHdr := (r.header? "link").getD ""
                let asContainer := (linkHdr.splitOn "ldp#BasicContainer").length > 1 ||
                                   (linkHdr.splitOn lwsContainerType).length > 1
                let childPath := childPathFor S st target (r.header? "slug") asContainer
                let kind := if asContainer then ResourceKind.container else .dataResource
                let e : Entry := { path := childPath, kind, contentType := ct,
                                   body := r.content, mtime := S.now st }
                let st' := touchContainer S (S.tick (S.put st e)) childPath
                (⟨201, ("location", childPath) :: writtenHeaders cfg e, "", none⟩, st')
  | "PATCH" =>
      let ct := (r.header? "content-type").map (fun c => ((c.splitOn ";").headD c).trim)
      match ct with
      | none => (problem 400 "PATCH requires a Content-Type header field" target, st)
      | some ct =>
          if ct != mediaJsonPatch then
            (problem 415 "PATCH accepts application/json-patch+json" target
              [("accept-patch", String.intercalate ", " cfg.acceptPatch)], st)
          else match existing with
            | none => (problem 404 "no resource at this path" target, st)
            | some e =>
                if e.kind.isContainer then
                  (problem 409 "a container representation is server-managed" target, st)
                else match preconditionFailure r existing (some (etagFor e e.contentType)) none with
                  | some resp => (resp, st)
                  | none =>
                      match (String.fromUTF8? r.content).map parseJson with
                      | none => (problem 400 "the patch document is not UTF-8" target, st)
                      | some (.error _) => (problem 400 "the patch document is not JSON" target, st)
                      | some (.ok p) =>
                          match parseJson e.text with
                          | .error _ =>
                              (problem 409 "the resource is not a JSON document" target, st)
                          | .ok d =>
                              match applyJsonPatch p d with
                              | .error msg => (problem 409 msg target, st)
                              | .ok d' =>
                                  let e' : Entry := { e with body := textBytes (toStringCompact d'),
                                                             mtime := S.now st }
                                  let st' := touchContainer S (S.tick (S.put st e')) target
                                  (⟨204, writtenHeaders cfg e', "", none⟩, st')
  | "DELETE" =>
      if isRoot then
        (problem 405 "the storage root cannot be deleted" target (allowHdr .storageRoot), st)
      else
        match existing with
        | none => (problem 404 "no resource at this path" target, st)
        | some e =>
            match preconditionFailure r existing (some (etagFor e e.contentType)) none with
            | some resp => (resp, st)
            | none =>
                let recursive := ((r.header? "depth").map (fun d => d.trim.toLower)) == some "infinity"
                if e.kind.isContainer && !(containedPaths S st target).isEmpty && !recursive then
                  (problem 409 "the container is not empty" target, st)
                else
                  let descendants := (S.paths st).filter (fun p => p != target && p.startsWith target &&
                                                                     pathIsContainer target)
                  let st1 := descendants.foldl (fun s p => S.remove s p) st
                  let st' := touchContainer S (S.tick (S.remove st1 target)) target
                  (⟨204, [], "", none⟩, st')
  | _ =>
      let kind := (match existing with
                   | some e => e.kind
                   | none => ResourceKind.dataResource)
      (problem 405 "the method is not supported by the target" target (allowHdr kind), st)

/-- One operation. Total: every request, well formed or not, has a response.

The request target is split into its path and its query first, and a path
with a dot segment, an empty segment, a backslash, an encoded slash or a NUL
is refused with 400 (`validTarget`). The query `linkset` names the linkset
resource of the path; the path `/.well-known/lws-storage` names the storage
description. Every other target is a storage path:

Read (GET, HEAD) — 200 with `ETag`, `Last-Modified` and the LWS links; a
container answers its `application/lws+json` listing or the Turtle LWS
profile; a data resource honours a single byte `Range`; 304 or 412 on a
failed precondition; 404.
Create/Update (PUT) — 201 when the resource did not exist, 204 when it did;
412 on a failed precondition.
Create (POST) — 201 with `Location` and the LWS links; 404 when the target
does not exist; 405 when it is not a container.
Update (PATCH) — JSON Patch (RFC 6902) on a JSON data resource; 415 for
another patch format; 409 when the patch cannot apply.
Delete (DELETE) — 204; 405 on the storage root; 404 when absent; 409 when
a container is not empty and `Depth: infinity` was not sent.
OPTIONS — 204 with `Allow` and the `Accept-*` fields.
Anything else — 405 with `Allow`. Every 4xx carries an RFC 9457
`application/problem+json` body. -/
def step (S : Store σ) (cfg : Config) (r : Request) (st : σ) : Response × σ :=
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  let r := { r with path, queryStr := query }
  if !validTarget path then
    (problem 400 "the request target is not a valid storage path" path, st)
  else if query == linksetQuery then linksetStep S cfg r st path
  else if path == storagePath then (storageStep cfg r, st)
  else stepPath S cfg r st

end L4Factoidal.LWS
