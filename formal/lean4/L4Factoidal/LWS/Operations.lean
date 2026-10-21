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
from it and then calls `tick`. Within ONE request the clock increases. A
host with a real clock sets it to the current second before EVERY request
(`Wasm/Ops/Lws.lean`), so across requests in one second it repeats. No
rule here may depend on the clock being new: entity tags carry a digest of
the representation (`tagIn`), and POST names are made unique by a search
(`childPathFor`, theorem `childPathFor_fresh`). Until 2026-10-21 this
paragraph said the clock made POST names distinct; under a real clock it
did not, and a POST replaced another resource
(https://github.com/danbri/factoidal/issues/911, F3 and F6).
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Discovery
import L4Factoidal.LWS.Binding
import L4Factoidal.LWS.Linkset
import L4Factoidal.LWS.Pagination
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
  /-- The pagination threshold and page size of container listings (LWS
  §LWS Media Type, Pagination: "a server-determined threshold"). A
  container with more members than this is listed in pages of this many
  members; 0 turns pagination off. -/
  pageSize : Nat := 100
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
def writtenHeaders (cfg : Config) (e : Entry) (tag : String) : List (String × String) :=
  [ ("last-modified", httpDate e.mtime)
  , ("etag", tag)
  , ("link", renderLinks (lwsLinks cfg.baseIri e.path e.kind)) ]

/-- The media type a write stores when the request names none.

RFC 9110 §8.3: "A sender that generates a message containing content SHOULD
generate a Content-Type header field in that message". A message with no
content needs none, and the LWS draft's own example of creating a container
(lws10-core `Operations/create-resource.md`) is a POST with
`Content-Length: 0`, the container type link and no `Content-Type`
(https://github.com/danbri/factoidal/issues/911, F1). Such a write stores an
empty container as `text/turtle` (as `ensureAncestors` does) and an empty
data resource as `application/octet-stream` (RFC 9110 §8.3: "the recipient
MAY either assume a media type of "application/octet-stream" ... or examine
the data"). Content without a `Content-Type` is still refused with 400
(`none`): Solid Protocol §2.1, "Server MUST reject PUT, POST, and PATCH
requests that contain content but lack the Content-Type header field, with
a status code of 400." -/
def writeMediaType (r : Request) (asContainer : Bool) : Option String :=
  match r.header? "content-type" with
  | some ct => some ct
  | none =>
      if r.content.size == 0 then some (if asContainer then "text/turtle" else mediaOctetStream)
      else none

/-! ## The step function -/

/-- The name a POST assigns when the request gives no usable hint: `res`
and the clock. Two POSTs can get the same clock value, because a host with a
real clock sets the clock to the current second on every request
(`Wasm/Ops/Lws.lean`), so the name is only a first candidate:
`childPathFor` makes it unique (https://github.com/danbri/factoidal/issues/911,
F6). -/
def assignedName (S : Store σ) (st : σ) : String := "res" ++ toString (S.now st)

/-- Is a `Slug` usable as one path segment? -/
def slugUsable (s : String) : Bool :=
  s != "" && s != "." && s != ".." &&
  !(s.any (fun c => c == '/' || c == '?' || c == '#' || c == '%' || c == '\\' || c.toNat < 32))

/-- The `i`-th candidate for a name: the name itself, then `name-1`,
`name-2`, and so on. -/
def nameCandidate (name : String) (i : Nat) : String :=
  if i == 0 then name else name ++ "-" ++ toString i

/-- The first candidate from the `i`-th on that is not `taken`, trying at
most `fuel` of them. One loop step per candidate (structural recursion on
the fuel, a tail call). -/
def freeName (taken : String → Bool) (name : String) : Nat → Nat → Option String
  | 0, _ => none
  | fuel + 1, i =>
      if taken (nameCandidate name i) then freeName taken name fuel (i + 1)
      else some (nameCandidate name i)

/-- A name `freeName` answers is not taken. -/
theorem freeName_free (taken : String → Bool) (name : String) :
    ∀ (fuel i : Nat) (n : String), freeName taken name fuel i = some n → taken n = false := by
  intro fuel
  induction fuel with
  | zero => intro i n h; simp [freeName] at h
  | succ k ih =>
      intro i n h
      unfold freeName at h
      by_cases ht : taken (nameCandidate name i) = true
      · simp only [ht, if_true] at h
        exact ih (i + 1) n h
      · simp only [ht, Bool.false_eq_true, if_false, Option.some.injEq] at h
        rw [← h]
        simpa using ht

/-- The path of a new child of `target`. LWS §Create Resource: "If an
identity hint was provided, the server attempts to incorporate it while
ensuring uniqueness and validity within the container." The first name not
held by a data resource or a container is used: the hint (or `res` and the
clock), then the same with `-1`, `-2`, ... Up to one more candidate than
the store has paths is tried; each taken candidate is held by a different
path, so one of them is free. `none` (never reached) answers 409.

Until 2026-10-21 a clash got the clock as its one suffix, on the
assumption that the clock never repeats; under a host's real clock three
POSTs in one second gave the third the second's name, and the third POST
REPLACED the second resource (Touchstone, five POSTs in one second: two
members, https://github.com/danbri/factoidal/issues/911, F6). Theorem
`childPathFor_fresh`: the path is free. -/
def childPathFor (S : Store σ) (st : σ) (target : String) (hint : Option String)
    (asContainer : Bool) : Option String :=
  let name := match hint with
    | some s => if slugUsable s then s else assignedName S st
    | none => assignedName S st
  let taken (n : String) : Bool :=
    (S.lookup st (target ++ n)).isSome || (S.lookup st (target ++ n ++ "/")).isSome
  (freeName taken name ((S.paths st).length + 1) 0).map
    (fun n => target ++ n ++ (if asContainer then "/" else ""))

/-- A POST never replaces a resource: the path `childPathFor` assigns holds
nothing in the store. -/
theorem childPathFor_fresh (S : Store σ) (st : σ) (target : String) (hint : Option String)
    (asContainer : Bool) (p : String)
    (h : childPathFor S st target hint asContainer = some p) : S.lookup st p = none := by
  unfold childPathFor at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨n, hn, rfl⟩ := h
  have hfree := freeName_free _ _ _ _ _ hn
  simp only [Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hfree
  cases asContainer
  · simpa using hfree.1
  · simpa using hfree.2

/-- Is the resource at `p` one a container listing shows (it exists and is
not an auxiliary resource)? -/
def listable (S : Store σ) (st : σ) (p : String) : Bool :=
  match S.lookup st p with
  | some e => !e.kind.isAuxiliary
  | none => false

/-- The paths a container lists, in listing order: its direct members,
auxiliary resources excluded, in increasing path order, each path once
(`orderPaths`). -/
def orderedMemberPaths (S : Store σ) (st : σ) (c : String) : List String :=
  (orderPaths (containedPaths S st c)).filter (listable S st)

/-- The resources a container lists, in listing order. -/
def listedMembers (S : Store σ) (st : σ) (c : String) : List Entry :=
  (orderedMemberPaths S st c).filterMap (S.lookup st)

/-- The resources on page `n` (from 1) of a container listing at page size
`k`. -/
def pageItems (S : Store σ) (st : σ) (c : String) (k n : Nat) : List Entry :=
  (pageAt (orderedMemberPaths S st c) k (n - 1)).filterMap (S.lookup st)

/-- The number of pages of a container listing at page size `k`. -/
def memberPageCount (S : Store σ) (st : σ) (c : String) (k : Nat) : Nat :=
  pageCount (orderedMemberPaths S st c).length k

/-- Each member path of the listing occurs once, and the listing is in
strictly increasing path order. -/
theorem orderedMemberPaths_sorted (S : Store σ) (st : σ) (c : String) :
    List.Pairwise (· < ·) (orderedMemberPaths S st c) :=
  (orderPaths_sorted _).filter _

theorem orderedMemberPaths_nodup (S : Store σ) (st : σ) (c : String) :
    (orderedMemberPaths S st c).Nodup :=
  (orderPaths_nodup _).filter _

/-- The listing holds exactly the container's direct members that resolve
to a non-auxiliary resource. With `StoreLaws.pathsLookup`, every path that
resolves is enumerated, so no member is missing. -/
theorem mem_orderedMemberPaths (S : Store σ) (st : σ) (c p : String) :
    p ∈ orderedMemberPaths S st c ↔
      p ∈ S.paths st ∧ contains c p = true ∧ listable S st p = true := by
  simp [orderedMemberPaths, mem_orderPaths, containedPaths, and_assoc]

/-- Pagination is exact: for a container that does not change between the
requests, concatenating the items of pages 1 to `memberPageCount` gives
exactly the listing, each member once, in listing order. -/
theorem pageItems_concat (S : Store σ) (st : σ) (c : String) (k : Nat) :
    (List.range (memberPageCount S st c k)).flatMap (fun i => pageItems S st c k (i + 1)) =
      listedMembers S st c := by
  unfold pageItems listedMembers memberPageCount
  simp only [Nat.add_sub_cancel]
  rw [← List.filterMap_flatMap, pages_concat]

/-- The entity tag of `e` in `media`: for a data resource `etagFor`; for a
container `containerTag` over its listing in that media type, so the tag
changes whenever the listing does (https://github.com/danbri/factoidal/issues/911,
F3). -/
def tagIn (S : Store σ) (cfg : Config) (st : σ) (e : Entry) (media : String) : String :=
  if e.kind.isContainer then
    containerTag e media (containerBody media cfg.baseIri e.path (listedMembers S st e.path))
  else etagFor e media

/-- Every current tag of `e`: one for a data resource, one per media type for
a container. These are what `If-Match` and `If-None-Match` compare with. -/
def tagsIn (S : Store σ) (cfg : Config) (st : σ) (e : Entry) : List String :=
  if e.kind.isContainer then containerMedia.map (tagIn S cfg st e) else [etagFor e e.contentType]

/-- The preconditions of a request on an existing resource or on none. -/
def preconditionsOn (S : Store σ) (cfg : Config) (st : σ) (r : Request)
    (existing : Option Entry) : Option Response :=
  preconditionFailure r (S.now st) existing.isSome none (existing.map (·.mtime)) none
    ((existing.map (tagsIn S cfg st)).getD [])

/-- The entity tag of a linkset: the resource's clock and the FNV-1a digest
of the document, so a change to the client links changes the tag. -/
def linksetTag (e : Entry) (docText : String) : String :=
  "\"" ++ toString e.mtime ++ "-ls-" ++ hex8 (fnv1a32 docText.toUTF8) ++ "\""

/-- The linkset resource of `path` (LWS §Metadata). Its document holds the
server-managed links and the resource's client links
(`L4Factoidal.LWS.Linkset`).

* GET, HEAD — 200 with `application/linkset+json`, or 304.
* PATCH — JSON Patch (RFC 6902), "the primary mechanism for metadata
  management". The patched document must keep every server-managed link as
  it is ("Servers MUST preserve the links a client is not permitted to
  modify"); a change to one is refused with 409; every other relation
  becomes the resource's client links, each checked (400 when malformed).
* PUT — a full `application/linkset+json` replacement ("If advertised in
  the Allow header, a client MAY replace the entire linkset"). The
  server-managed relations may be left out, and are kept; when present they
  must be unchanged (409).
* A linkset change does not change the resource's content, its
  modification time or its entity tag; it advances the store clock, so the
  host persists it. -/
def linksetStep (S : Store σ) (cfg : Config) (r : Request) (st : σ)
    (path : String) : Response × σ :=
  match S.lookup st path with
  | none => (problem 404 "no resource has this linkset" (linksetTargetOf path), st)
  | some e =>
      let doc := linksetDoc cfg.baseIri path e.kind e.links
      let docText := toStringCompact doc
      let tag := linksetTag e docText
      let allow := "GET, HEAD, OPTIONS, PATCH, PUT"
      let hs : List (String × String) :=
        [ ("content-type", mediaLinkset), ("etag", tag)
        , ("last-modified", httpDate e.mtime), ("allow", allow)
        , ("accept-patch", mediaJsonPatch)
        , ("link", renderLinks [{ target := iriOfPath cfg.baseIri storagePath,
                                  rel := lwsStorageRel }]) ]
      let tagListed (h : String) : Bool :=
        ((r.header? h).map (fun v => (parseTagList v).any (fun t => t == tag || t == "*"))).getD false
      let target := linksetTargetOf path
      let ct := (r.header? "content-type").map baseMedia
      let store (ls : List Link) : Response × σ :=
        if ls == e.links then (⟨204, [("etag", tag)], "", none⟩, st)
        else
          let e' := { e with links := ls }
          let tag' := linksetTag e' (toStringCompact (linksetDoc cfg.baseIri path e.kind ls))
          (⟨204, [("etag", tag')], "", none⟩, S.tick (S.put st e'))
      let readDoc (keepAbsent : Bool) (d : Json) : Response × σ :=
        match clientLinksOfDoc cfg.baseIri path e.kind keepAbsent d with
        | .error (status, msg) => (problem status msg target, st)
        | .ok ls => store ls
      match r.method with
      | "GET" | "HEAD" =>
          if tagListed "if-none-match" then (⟨304, [("etag", tag)], "", none⟩, st)
          else (⟨200, hs, if r.method == "HEAD" then "" else docText, none⟩, st)
      | "OPTIONS" => (⟨204, [("allow", allow), ("accept-patch", mediaJsonPatch)], "", none⟩, st)
      | "PATCH" =>
          if ct != some mediaJsonPatch then
            (problem 415 "a linkset accepts application/json-patch+json" target
              [("accept-patch", mediaJsonPatch)], st)
          else if (r.header? "if-match").isSome && !tagListed "if-match" then
            (problem 412 "If-Match did not match the linkset" target, st)
          else match parseJson ((String.fromUTF8? r.content).getD "") with
            | .error _ => (problem 400 "the patch document is not JSON" target, st)
            | .ok p =>
                match applyJsonPatch p doc with
                | .error msg => (problem 409 msg target, st)
                | .ok d' => readDoc false d'
      | "PUT" =>
          if ct != some mediaLinkset then
            (problem 415 "a linkset is replaced with application/linkset+json" target, st)
          else if (r.header? "if-match").isSome && !tagListed "if-match" then
            (problem 412 "If-Match did not match the linkset" target, st)
          else match parseJson ((String.fromUTF8? r.content).getD "") with
            | .error _ => (problem 400 "the linkset document is not JSON" target, st)
            | .ok d => readDoc true d
      | _ => (problem 405 "a linkset accepts GET, HEAD, OPTIONS, PATCH and PUT"
                target [("allow", allow)], st)

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

/-- Does the request carry `Prefer: set-linkset` (LWS §Update Resource)? -/
def preferred (r : Request) : Bool :=
  ((r.header? "prefer").map preferSetLinkset).getD false

/-- A read of a paginated container (LWS §LWS Media Type, Pagination). The
request target without a query, or with `page=1`, names the first page;
`page=N` names page N. Each page answers 200 with `rel="first"` and
`rel="last"`, `rel="next"` on every page but the last, and `rel="prev"` on
every page but the first. `totalItems` counts the full membership. A page
number above the last page answers 404.

Each page has its own entity tag: the container's tag, the page number and
the FNV-1a digest of the page's representation. The container's clock
leads the tag and advances with every change to its membership, so a client
that reads two pages with different leading clocks knows that the container
changed between the requests. -/
def pagedRead (S : Store σ) (cfg : Config) (r : Request) (st : σ) (e : Entry)
    (media : String) (isRoot : Bool) : Response × σ :=
  let target := r.path
  let k := cfg.pageSize
  let total := (orderedMemberPaths S st target).length
  let count := pageCount total k
  let pageNo : Option Nat :=
    if r.queryStr == "" then some 1
    else match pageOfQuery? r.queryStr with
      | some n => some n
      | none => if r.queryStr.startsWith "page=" then none else some 1
  match pageNo with
  | none => (problem 404 "no page of this container has this name" target, st)
  | some n =>
      if n == 0 || n > count then
        (problem 404 "the container has no such page" target, st)
      else
        let items := pageItems S st target k n
        let body := containerBody media cfg.baseIri target items (some total)
        let base := etagFor e media
        let tag := String.ofList (base.toList.dropLast) ++ "-p" ++ toString n ++ "-" ++
          hex8 (fnv1a32 body.toUTF8) ++ "\""
        match preconditionFailure r (S.now st) true (some tag) (some e.mtime)
                (some (httpDate e.mtime)) [tag] with
        | some resp => (resp, st)
        | none =>
            let pageLink (rel : String) (m : Nat) : Link :=
              { target := target ++ "?" ++ pageQuery m, rel }
            let pageLinks : List Link :=
              [pageLink "first" 1, pageLink "last" count] ++
              (if n < count then [pageLink "next" (n + 1)] else []) ++
              (if n > 1 then [pageLink "prev" (n - 1)] else [])
            let hs0 := readHeaders cfg e isRoot
            let linkV := ((hs0.lookup "link").getD "")
            let hs := setHeader (setHeader hs0 "content-type" (containerContentType media))
                        "link" (linkV ++ ", " ++ renderLinks pageLinks) ++
                      [("etag", tag), ("vary", "accept")]
            (⟨200, hs, if r.method == "HEAD" then "" else body, none⟩, st)

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
          if e.kind.isContainer && paginated (orderedMemberPaths S st target).length cfg.pageSize then
            pagedRead S cfg r st e media isRoot
          else
          let tag := tagIn S cfg st e media
          let lm := httpDate e.mtime
          match preconditionFailure r (S.now st) true (some tag) (some e.mtime) (some lm)
                  (tagsIn S cfg st e) with
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
      match writeMediaType r (pathIsContainer target) with
      | none => (problem 400 "PUT with content requires a Content-Type header field" target, st)
      | some ct =>
          match preconditionsOn S cfg st r existing with
          | some resp => (resp, st)
          | none =>
          match rdfContentRefused ct r.content target with
          | some resp => (resp, st)
          | none =>
          let linksR : Except (Nat × String) (List Link) :=
            if preferred r then clientLinksOf (r.header? "link")
            else .ok ((existing.map (·.links)).getD [])
          match linksR with
          | .error (status, msg) => (problem status msg target, st)
          | .ok links =>
              let st := ensureAncestors S (ancestors target) st
              let kind := if pathIsContainer target then
                            (if isRoot then ResourceKind.storageRoot else .container)
                          else .dataResource
              let e : Entry := { path := target, kind, contentType := ct,
                                 body := r.content, mtime := S.now st, links }
              let st' := touchContainer S (S.tick (S.put st e)) target
              let tag := tagIn S cfg st' e (if e.kind.isContainer then mediaLwsJson else ct)
              match existing with
              | none   => (⟨201, ("location", target) :: writtenHeaders cfg e tag, "", none⟩, st')
              | some _ => (⟨204, writtenHeaders cfg e tag, "", none⟩, st')
  | "POST" =>
      match existing with
      | none => (problem 404 "the target container does not exist" target, st)
      | some parentEntry =>
          if !parentEntry.kind.isContainer then
            (problem 405 "POST creates resources in a container" target
              (allowHdr parentEntry.kind), st)
          else
            let linkHdr := (r.header? "link").getD ""
            let asContainer := (linkHdr.splitOn "ldp#BasicContainer").length > 1 ||
                               (linkHdr.splitOn lwsContainerType).length > 1
            match writeMediaType r asContainer with
            | none => (problem 400 "POST with content requires a Content-Type header field"
                        target, st)
            | some ct =>
                match rdfContentRefused ct r.content target with
                | some resp => (resp, st)
                | none =>
                match postLinksOf (r.header? "link") with
                | .error (status, msg) => (problem status msg target, st)
                | .ok links =>
                match childPathFor S st target (r.header? "slug") asContainer with
                | none => (problem 409 "the container has no free name for a new resource" target, st)
                | some childPath =>
                let kind := if asContainer then ResourceKind.container else .dataResource
                let e : Entry := { path := childPath, kind, contentType := ct,
                                   body := r.content, mtime := S.now st, links }
                let st' := touchContainer S (S.tick (S.put st e)) childPath
                let tag := tagIn S cfg st' e (if asContainer then mediaLwsJson else ct)
                (⟨201, ("location", childPath) :: writtenHeaders cfg e tag, "", none⟩, st')
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
                else match preconditionsOn S cfg st r existing with
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
                                  let linksR : Except (Nat × String) (List Link) :=
                                    if preferred r then
                                      (clientLinksOf (r.header? "link")).map (mergeLinks e.links)
                                    else .ok e.links
                                  match linksR with
                                  | .error (status, msg) => (problem status msg target, st)
                                  | .ok links =>
                                  let e' : Entry := { e with body := textBytes (toStringCompact d'),
                                                             mtime := S.now st, links }
                                  let st' := touchContainer S (S.tick (S.put st e')) target
                                  (⟨204, writtenHeaders cfg e' (etagFor e' e'.contentType), "",
                                    none⟩, st')
  | "DELETE" =>
      if isRoot then
        (problem 405 "the storage root cannot be deleted" target (allowHdr .storageRoot), st)
      else
        match existing with
        | none => (problem 404 "no resource at this path" target, st)
        | some e =>
            match preconditionsOn S cfg st r existing with
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
