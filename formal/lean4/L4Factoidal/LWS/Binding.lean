/-
L4Factoidal.LWS.Binding — the HTTP binding of the Linked Web Storage
Protocol 1.0 Core that the editor's draft now states.

Source: the W3C Linked Web Storage Working Group editor's draft,
https://w3c.github.io/lws-protocol/lws10-core/, read 2026-10-20 at
w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(2026-10-19). The sections this module implements, with the statements it
decides (verbatim):

* §Read Resource: "Responses MUST include an `ETag` header as defined in
  [RFC9110]." and "Servers MUST support range requests per [RFC7233] for
  partial retrieval." and "Servers SHOULD support conditional requests as
  defined in [RFC9110] ... respond with `304 Not Modified`".
* §Update Resource: "If the `If-Match` precondition did not match
  (concurrent modification), the server responds with `412 Precondition
  Failed`." and "LWS server MUST minimally support JSON Patch
  (`application/json-patch+json`) as defined in [RFC6902]."
* §Container Representation: the `id`, `type`, `totalItems` and `items`
  members, and for each item `id`, `type`, `format`, `size`, `modified`.
* §LWS Media Type: "An LWS container representation MUST support the media
  type `application/lws+json`." and the LWS profile and content
  negotiation rules.
* §Metadata: "For each resource in storage, a server MUST make metadata
  links available as a standalone resource according to [RFC9264]." and
  "A linkset resource MUST be available as `application/linkset+json`."
* §Discovery: the storage description data model and "All responses to GET
  and HEAD requests targeting storage resources MUST include a Link header
  whose target is the canonical URI of the storage, including a relation
  (rel) parameter whose value equals https://www.w3.org/ns/lws#storage."
* §Summary of HTTP Status Mappings: "Servers SHOULD use the standard format
  defined in [RFC9457] for structured error responses".

Everything here is a pure function. `L4Factoidal.LWS.Operations.step` calls
it; no host decides any of it.

Server choices the draft leaves to the server, each stated once:

* The linkset resource of a resource at path `p` is `p?linkset`. The draft
  only requires that it be discoverable through `rel="linkset"` and be
  server-managed.
* The storage description is at `/.well-known/lws-storage`. The draft only
  requires that the `lws#storage` link targets it.
* An entity tag is the resource's modification clock in quotes. The clock
  is strictly increasing over mutations (`StoreLaws.nowTick`), so two
  versions of one resource never share a tag. A container has one
  representation per media type, and each gets its own tag suffix, because
  RFC 9110 §8.8.3 requires a strong tag to change when the representation
  data changes.
-/
import L4Factoidal.LWS.Discovery
import L4Factoidal.JSON.Serialize
import L4Factoidal.JSON.Parser
import L4Factoidal.HTTP.Server

namespace L4Factoidal.LWS

open L4Factoidal.JSON
open L4Factoidal.HTTP (Request Response)

/-! ## Vocabulary -/

def lwsNs : String := "https://www.w3.org/ns/lws#"
def lwsContainerType : String := lwsNs ++ "Container"
def lwsDataResourceType : String := lwsNs ++ "DataResource"
def lwsStorageRel : String := lwsNs ++ "storage"
def lwsProfile : String := "https://www.w3.org/ns/lws/v1"
def cidContext : String := "https://www.w3.org/ns/cid/v1"
def mediaLwsJson : String := "application/lws+json"
def mediaLwsCid : String := "application/lws+cid"
def mediaLinkset : String := "application/linkset+json"
def mediaJsonPatch : String := "application/json-patch+json"
def mediaProblem : String := "application/problem+json"

/-- The path of the storage description resource (a server choice). -/
def storagePath : String := "/.well-known/lws-storage"

/-- The query that names the linkset resource of a path (a server choice). -/
def linksetQuery : String := "linkset"

/-- The linkset resource of a path. -/
def linksetTargetOf (p : String) : String := p ++ "?" ++ linksetQuery

/-! ## Request targets -/

/-- Split a request target into its path and its query. -/
def splitTarget (t : String) : String × String :=
  match t.splitOn "?" with
  | [] => ("", "")
  | [p] => (p, "")
  | p :: rest => (p, String.intercalate "?" rest)

private def isDotSegment (s : String) : Bool :=
  let l := s.toLower
  l == "." || l == ".." || l == "%2e" || l == "%2e%2e" || l == ".%2e" || l == "%2e."

/-- Is a request path acceptable as a storage path? It must be absolute
(start with `/`), and must hold no dot segment (`.`, `..`, or either one
percent-encoded), no empty segment (`//`), no backslash, and no NUL.

RFC 3986 §5.2.4 removes dot segments before a path is resolved; a request
that still carries one names no resource of this storage, and a storage that
persists resources under a directory must not let one through, since it
would address a file outside the directory. -/
def validTarget (p : String) : Bool :=
  p.startsWith "/" &&
  !((p.splitOn "/").any isDotSegment) &&
  (p.splitOn "//").length == 1 &&
  !(p.any (fun c => c == '\\' || c == Char.ofNat 0)) &&
  !((p.toLower.splitOn "%2f").length > 1) &&
  !((p.toLower.splitOn "%5c").length > 1) &&
  !((p.splitOn "%00").length > 1)

/-! ## Problem details (RFC 9457) -/

def reasonPhrase : Nat → String
  | 400 => "Bad Request"
  | 401 => "Unauthorized"
  | 403 => "Forbidden"
  | 404 => "Not Found"
  | 405 => "Method Not Allowed"
  | 406 => "Not Acceptable"
  | 409 => "Conflict"
  | 412 => "Precondition Failed"
  | 415 => "Unsupported Media Type"
  | 416 => "Range Not Satisfiable"
  | _ => "Error"

/-- An error response with an RFC 9457 `application/problem+json` body. -/
def problem (status : Nat) (detail target : String)
    (extra : List (String × String) := []) : Response :=
  ⟨status, ("content-type", mediaProblem) :: extra,
   toStringCompact (.object
     [ ("type", .string "about:blank")
     , ("title", .string (reasonPhrase status))
     , ("status", .number (toString status))
     , ("detail", .string detail)
     , ("instance", .string target) ])⟩

/-! ## Dates -/

private def pad2 (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n
private def pad4 (n : Nat) : String :=
  if n < 10 then "000" ++ toString n
  else if n < 100 then "00" ++ toString n
  else if n < 1000 then "0" ++ toString n
  else toString n

/-- Days since 1970-01-01 to a civil date; the same era algorithm as
`Operations.civilFromDays`, repeated here because this module sits below
`Operations`. -/
def civilOfDays (days : Nat) : Nat × Nat × Nat :=
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

/-- An ISO 8601 / XML Schema `dateTime` in UTC from seconds since the Unix
epoch. `isoDateTime 0 = "1970-01-01T00:00:00Z"`. -/
def isoDateTime (unix : Nat) : String :=
  let (y, m, d) := civilOfDays (unix / 86400)
  let s := unix % 86400
  pad4 y ++ "-" ++ pad2 m ++ "-" ++ pad2 d ++ "T" ++ pad2 (s / 3600) ++ ":" ++
    pad2 (s % 3600 / 60) ++ ":" ++ pad2 (s % 60) ++ "Z"

/-! ## Entity tags and conditional requests (RFC 9110 §8.8.3, §13) -/

/-- The short name a container representation's tag carries. -/
def mediaTagSuffix (media : String) : String :=
  if media == mediaLwsJson then ""
  else if media == "text/turtle" then "-ttl"
  else if media == "application/ld+json" then "-jsonld"
  else "-x"

/-- The tag of one representation of an entry. -/
def etagFor (e : Entry) (media : String) : String :=
  "\"" ++ toString e.mtime ++ (if e.kind.isContainer then mediaTagSuffix media else "") ++ "\""

/-- The container media types this binding serves, server preference first. -/
def containerMedia : List String := [mediaLwsJson, "application/ld+json", "text/turtle"]

/-- Every current tag of an entry: one for a data resource, one per
representation for a container. -/
def currentTags (e : Entry) : List String :=
  if e.kind.isContainer then containerMedia.map (etagFor e) else [etagFor e e.contentType]

private def trimSp (s : String) : String :=
  String.ofList (((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse)

/-- The entity tags of an `If-Match` or `If-None-Match` field value. -/
def parseTagList (v : String) : List String :=
  (v.splitOn ",").map trimSp |>.filter (· != "")

private def stripWeak (t : String) : String :=
  if t.startsWith "W/" then String.ofList (t.toList.drop 2) else t

/-- RFC 9110 §13.1.1: `If-Match` uses the strong comparison; `*` matches any
current representation. -/
def ifMatchHolds (v : String) (e : Option Entry) : Bool :=
  match e with
  | none => false
  | some e =>
      let ts := parseTagList v
      ts.contains "*" || ts.any (fun t => !t.startsWith "W/" && (currentTags e).contains t)

/-- RFC 9110 §13.1.2: `If-None-Match` uses the weak comparison. The
condition HOLDS when no listed tag matches. -/
def ifNoneMatchHolds (v : String) (e : Option Entry) : Bool :=
  match e with
  | none => true
  | some e =>
      let ts := parseTagList v
      !(ts.contains "*" || ts.any (fun t => (currentTags e).contains (stripWeak t)))

/-- Evaluate the preconditions of a request in the order of RFC 9110
§13.2.2, returning the response that ends the request when one fails.
`If-Modified-Since` is evaluated only for an exact match with the
`Last-Modified` the server sends, which is the date a client echoes. -/
def preconditionFailure (r : Request) (e : Option Entry) (tag : Option String)
    (lastModified : Option String) : Option Response :=
  let safe := r.method == "GET" || r.method == "HEAD"
  let notModified : Response :=
    ⟨304, (match tag with | some t => [("etag", t)] | none => []) ++
          (match lastModified with | some d => [("last-modified", d)] | none => []), ""⟩
  match r.header? "if-match" with
  | some v =>
      if !ifMatchHolds v e then
        some (problem 412 "If-Match did not match a current representation" r.path)
      else none
  | none => none
  |>.orElse fun _ =>
  match r.header? "if-none-match" with
  | some v =>
      if ifNoneMatchHolds v e then none
      else if safe then some notModified
      else some (problem 412 "If-None-Match matched a current representation" r.path)
  | none =>
      if safe then
        match r.header? "if-modified-since", lastModified with
        | some ims, some lm => if trimSp ims == lm then some notModified else none
        | _, _ => none
      else none

/-! ## Range requests (RFC 9110 §14) -/

private def natOf? (s : String) : Option Nat :=
  if s != "" && s.all Char.isDigit then s.toNat? else none

/-- Read a `Range` field value against a representation of `len` bytes.

* `none` — the field is not one this server acts on (another unit, several
  ranges, or bad syntax); RFC 9110 §14.2 lets a server ignore it.
* `some none` — the range is unsatisfiable (§14.1.1).
* `some (some (first, last))` — the inclusive byte range to send. -/
def parseRange (v : String) (len : Nat) : Option (Option (Nat × Nat)) :=
  let v := trimSp v
  if !v.startsWith "bytes=" then none else
  let spec := trimSp (String.ofList (v.toList.drop 6))
  if (spec.splitOn ",").length != 1 then none else
  match spec.splitOn "-" with
  | ["", suffix] =>
      match natOf? suffix with
      | none => none
      | some n =>
          if n == 0 || len == 0 then some none
          else some (some (len - min n len, len - 1))
  | [a, b] =>
      match natOf? a with
      | none => none
      | some first =>
          if first ≥ len then some none
          else if b == "" then some (some (first, len - 1))
          else match natOf? b with
            | none => none
            | some last => if last < first then none else some (some (first, min last (len - 1)))
  | _ => none

/-- The partial response for a satisfiable byte range of `body`, or nothing
when the range would cut a UTF-8 sequence. The ABI carries bodies as
strings, so a cut sequence cannot be transported; the server then sends the
full representation, which RFC 9110 §14.2 permits. -/
def rangeBody (body : String) (first last : Nat) : Option String :=
  let bytes := body.toUTF8
  String.fromUTF8? (bytes.extract first (last + 1))

/-! ## Links -/

/-- The links the LWS draft requires on every GET and HEAD of a storage
resource: `linkset`, `up` (non-root), `type`, and `lws#storage`. -/
def lwsLinks (baseIri path : String) (kind : ResourceKind) : List Link :=
  [ { target := linksetTargetOf path, rel := "linkset", attrs := [("type", mediaLinkset)] } ] ++
  (match parent? path with
   | some p => [{ target := p, rel := "up" }]
   | none => []) ++
  [ { target := if kind.isContainer then lwsContainerType else lwsDataResourceType, rel := "type" }
  , { target := iriOfPath baseIri storagePath, rel := lwsStorageRel } ]

/-! ## Representations -/

/-- One item of a container representation (§Container Representation,
"Contained Resource Description"). -/
def itemJson (baseIri : String) (e : Entry) : Json :=
  .object (
    [ ("id", .string (iriOfPath baseIri e.path))
    , ("type", .string (if e.kind.isContainer then "Container" else "DataResource")) ] ++
    (if e.kind.isContainer then [] else
      [ ("format", .string e.contentType)
      , ("size", .number (toString e.body.utf8ByteSize)) ]) ++
    [ ("modified", .string (isoDateTime e.mtime)) ])

/-- The `application/lws+json` representation of a container. -/
def containerJson (baseIri path : String) (items : List Entry) : String :=
  toStringCompact (.object
    [ ("@context", .string lwsProfile)
    , ("id", .string (iriOfPath baseIri path))
    , ("type", .string "Container")
    , ("totalItems", .number (toString items.length))
    , ("items", .array (items.map (itemJson baseIri))) ])

private def ttlString (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else if c == '\r' then acc ++ "\\r"
    else acc.push c) "" ++ "\""

private def ttlIri (s : String) : String := "<" ++ s ++ ">"

/-- The Turtle representation in the LWS profile: the same RDF the
`application/lws+json` representation encodes. -/
def containerTurtle (baseIri path : String) (items : List Entry) : String :=
  let header :=
    "@prefix lws: <https://www.w3.org/ns/lws#> .\n" ++
    "@prefix dcterms: <http://purl.org/dc/terms/> .\n" ++
    "@prefix schema: <https://schema.org/> .\n" ++
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\n"
  let self := ttlIri (iriOfPath baseIri path) ++ " a lws:Container ;\n  lws:totalItems " ++
    toString items.length ++
    (if items.isEmpty then " .\n"
     else " ;\n  lws:items " ++
       String.intercalate ", " (items.map (fun e => ttlIri (iriOfPath baseIri e.path))) ++ " .\n")
  let item (e : Entry) : String :=
    ttlIri (iriOfPath baseIri e.path) ++
    (if e.kind.isContainer then " a lws:Container ;\n"
     else " a lws:DataResource ;\n  dcterms:format " ++ ttlString e.contentType ++
       " ;\n  schema:size \"" ++ toString e.body.utf8ByteSize ++ "\"^^xsd:long ;\n") ++
    "  dcterms:modified \"" ++ isoDateTime e.mtime ++ "\"^^xsd:dateTime .\n"
  header ++ self ++ String.join (items.map item)

/-- The `Content-Type` value of a container representation in a media type. -/
def containerContentType (media : String) : String :=
  if media == mediaLwsJson then mediaLwsJson
  else media ++ "; profile=\"" ++ lwsProfile ++ "\""

/-- The container representation in a negotiated media type. -/
def containerBody (media baseIri path : String) (items : List Entry) : String :=
  if media == "text/turtle" then containerTurtle baseIri path items
  else containerJson baseIri path items

/-- Choose a container media type from `Accept`. The draft: "Servers MUST
honor requests for `application/lws+json` on containers". A request whose
`Accept` names none of them gets `application/lws+json`, since RFC 9110
§12.5.1 lets a server disregard the field rather than answer 406. -/
def chooseContainerMedia (accept : Option String) : String :=
  match accept with
  | none => mediaLwsJson
  | some a => (HTTP.negotiate a containerMedia).getD mediaLwsJson

/-- The `application/linkset+json` document (RFC 9264 §4.2) of a resource. -/
def linksetJson (baseIri path : String) (kind : ResourceKind) : Json :=
  let rel (r : String) (targets : List String) : String × Json :=
    (r, .array (targets.map (fun t => Json.object [("href", .string t)])))
  .object [ ("linkset", .array [ .object (
    [ ("anchor", .string (iriOfPath baseIri path)) ] ++
    (match parent? path with
     | some p => [rel "up" [iriOfPath baseIri p]]
     | none => []) ++
    [ rel "type" [if kind.isContainer then lwsContainerType else lwsDataResourceType]
    , rel lwsStorageRel [iriOfPath baseIri storagePath] ]) ]) ]

/-- The storage description (§Discovery, "Storage Description Resource"),
serialised as `application/lws+cid`. No `MoveResource` capability is
described: this server does not let a client change an `up` link. -/
def storageDescription (baseIri : String) : String :=
  toStringCompact (.object
    [ ("@context", .array [.string cidContext, .string lwsProfile])
    , ("id", .string (iriOfPath baseIri storagePath))
    , ("type", .string "Storage")
    , ("service", .array [ .object
        [ ("type", .string "StorageRoot")
        , ("serviceEndpoint", .string (iriOfPath baseIri rootPath)) ] ]) ])

/-! ## JSON Patch (RFC 6902) -/

/-- A JSON Pointer (RFC 6901) as its reference tokens. -/
def parsePointer (p : String) : Option (List String) :=
  if p == "" then some []
  else if p.startsWith "/" then
    some ((String.ofList (p.toList.drop 1)).splitOn "/" |>.map
      (fun t => (t.replace "~1" "/").replace "~0" "~"))
  else none

/-- An array index token: digits, no leading zero (RFC 6901 §4). -/
def arrayIndex? (t : String) : Option Nat :=
  if t != "" && t.all Char.isDigit && (t == "0" || !t.startsWith "0") then t.toNat? else none

def getAt : Json → List String → Option Json
  | j, [] => some j
  | .object fs, t :: ts => (fs.lookup t).bind (fun c => getAt c ts)
  | .array xs, t :: ts => (arrayIndex? t).bind (fun i => xs[i]?.bind (fun c => getAt c ts))
  | _, _ :: _ => none

private def setField (fs : List (String × Json)) (k : String) (v : Json) : List (String × Json) :=
  if fs.any (·.1 == k) then fs.map (fun (a, b) => if a == k then (a, v) else (a, b))
  else fs ++ [(k, v)]

/-- RFC 6902 §4.1 `add`. -/
def addAt : Json → List String → Json → Option Json
  | _, [], v => some v
  | .object fs, [t], v => some (.object (setField fs t v))
  | .array xs, [t], v =>
      if t == "-" then some (.array (xs ++ [v]))
      else (arrayIndex? t).bind (fun i =>
        if i ≤ xs.length then some (.array (xs.take i ++ [v] ++ xs.drop i)) else none)
  | .object fs, t :: ts, v =>
      (fs.lookup t).bind (fun c => (addAt c ts v).map (fun c' => .object (setField fs t c')))
  | .array xs, t :: ts, v =>
      (arrayIndex? t).bind (fun i => xs[i]?.bind (fun c =>
        (addAt c ts v).map (fun c' => .array (xs.set i c'))))
  | _, _ :: _, _ => none

/-- RFC 6902 §4.2 `remove`. The whole document cannot be removed. -/
def removeAt : Json → List String → Option Json
  | _, [] => none
  | .object fs, [t] =>
      if fs.any (·.1 == t) then some (.object (fs.filter (·.1 != t))) else none
  | .array xs, [t] =>
      (arrayIndex? t).bind (fun i =>
        if i < xs.length then some (.array (xs.take i ++ xs.drop (i + 1))) else none)
  | .object fs, t :: ts =>
      (fs.lookup t).bind (fun c => (removeAt c ts).map (fun c' => .object (setField fs t c')))
  | .array xs, t :: ts =>
      (arrayIndex? t).bind (fun i => xs[i]?.bind (fun c =>
        (removeAt c ts).map (fun c' => .array (xs.set i c'))))
  | _, _ :: _ => none

/-- Replace the value at an existing location, keeping its position:
RFC 6902 §4.3 `replace`, which is "functionally identical to a remove
operation for a value, followed immediately by an add operation at the same
location", without moving an object member to the end. -/
def setAt : Json → List String → Json → Option Json
  | _, [], v => some v
  | .object fs, t :: ts, v =>
      (fs.lookup t).bind (fun c => (setAt c ts v).map (fun c' => .object (setField fs t c')))
  | .array xs, t :: ts, v =>
      (arrayIndex? t).bind (fun i => xs[i]?.bind (fun c =>
        (setAt c ts v).map (fun c' => .array (xs.set i c'))))
  | _, _ :: _, _ => none

/-- Apply one operation object. -/
def applyPatchOp (doc op : Json) : Except String Json := do
  let name ← (op.getString? "op").elim (.error "an operation has no \"op\" member") .ok
  let path ← match (op.getString? "path").bind parsePointer with
    | some p => .ok p
    | none => .error "an operation has no valid \"path\" member"
  let fromPtr : Option (List String) := (op.getString? "from").bind parsePointer
  let value? := op.field? "value"
  let need (o : Option Json) (what : String) : Except String Json :=
    o.elim (.error what) .ok
  match name with
  | "add" =>
      let v ← need value? "add needs \"value\""
      need (addAt doc path v) "add: the target location does not exist"
  | "remove" => need (removeAt doc path) "remove: the target location does not exist"
  | "replace" =>
      let v ← need value? "replace needs \"value\""
      need (setAt doc path v) "replace: the target location does not exist"
  | "move" =>
      let f ← need' fromPtr "move needs \"from\""
      if f.isPrefixOf path && f != path then .error "move: from is a prefix of path" else
      let v ← need (getAt doc f) "move: from does not exist"
      let d ← need (removeAt doc f) "move: from does not exist"
      need (addAt d path v) "move: the target location does not exist"
  | "copy" =>
      let f ← need' fromPtr "copy needs \"from\""
      let v ← need (getAt doc f) "copy: from does not exist"
      need (addAt doc path v) "copy: the target location does not exist"
  | "test" =>
      let v ← need value? "test needs \"value\""
      match getAt doc path with
      | some w => if decide (w = v) then .ok doc else .error "test: the values differ"
      | none => .error "test: the target location does not exist"
  | other => .error s!"unknown operation \"{other}\""
where
  need' (o : Option (List String)) (what : String) : Except String (List String) :=
    o.elim (.error what) .ok

/-- Apply a JSON Patch document. RFC 6902 §5: the operations are applied in
order and any error stops the whole patch, leaving the target unchanged. -/
def applyJsonPatch (patch : Json) (doc : Json) : Except String Json :=
  match patch with
  | .array ops => ops.foldlM applyPatchOp doc
  | _ => .error "a JSON Patch document is an array"

end L4Factoidal.LWS
