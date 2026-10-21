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
* An entity tag is the resource's modification clock and the FNV-1a
  digest of the representation data: the bytes of a data resource
  (`etagFor`), the listing of a container in the negotiated media type
  (`containerTag`). RFC 9110 §8.8.1: a strong validator "changes value
  whenever a change occurs to the representation data that would be
  observable in the content of a 200 (OK) response to GET". The clock alone
  does not do that: a host with a real clock sets it to the current second
  on every request, so two changes in one second gave one tag
  (https://github.com/danbri/factoidal/issues/911, F3). A container has one
  representation per media type, and each gets its own tag suffix.
-/
import L4Factoidal.LWS.Discovery
import L4Factoidal.LWS.HttpDate
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
def mediaOctetStream : String := "application/octet-stream"

/-- The path of the storage description resource (a server choice). -/
def storagePath : String := "/.well-known/lws-storage"

/-- The subscription endpoint of the notification service (a server
choice): the `serviceEndpoint` of the `NotificationService` the storage
description advertises (LWS §Notification Discovery), and, by the webhook
notification suite's §Subscription Management, the container that lists a
subscriber's subscriptions. Each subscription is a member path below it. -/
def subscriptionsPath : String := "/.well-known/lws-subscriptions/"

/-- Is the path the subscription endpoint or one subscription below it? -/
def isSubscriptionPath (p : String) : Bool := p.startsWith subscriptionsPath

/-- The access request endpoint (LWS §Access Requests and Grants, a server
choice): the `serviceEndpoint` of the `AccessRequestService`, an LWS
container whose members are access requests.
https://github.com/danbri/factoidal/issues/913 -/
def accessRequestsPath : String := "/.well-known/lws-access-requests/"

/-- The access grant endpoint (a server choice): the `serviceEndpoint` of
the `AccessGrantService`, an LWS container whose members are access grants. -/
def accessGrantsPath : String := "/.well-known/lws-access-grants/"

/-- Is the path one of the two access endpoints, or a member below one? -/
def isAccessPath (p : String) : Bool :=
  p.startsWith accessRequestsPath || p.startsWith accessGrantsPath

/-- The access profile of LWS §Access Profile: "identified with the URL:
https://www.w3.org/ns/lws#AccessProfile". -/
def lwsAccessProfile : String := "https://www.w3.org/ns/lws#AccessProfile"

/-- The endpoint of the Type Index Service (lws10-index §Discovery: "the
entry for the Type Index Service MUST have a type equal to TypeIndexService"
and "Each service object MUST include a serviceEndpoint property"). The path
is a server choice. https://github.com/danbri/factoidal/issues/912 -/
def typeIndexPath : String := "/.well-known/lws-type-index"

/-- The endpoint of the Type Search Service (a server choice). -/
def typeSearchPath : String := "/.well-known/lws-type-search"

/-- Is the path one of the two index service endpoints? -/
def isIndexServicePath (p : String) : Bool := p == typeIndexPath || p == typeSearchPath

/-- ANTICIPATORY AND UNSTABLE (https://github.com/danbri/factoidal/issues/922):
the prefix of the search results resources a QUERY answer names with
`Content-Location` when `Config.searchResults` is on
(`L4Factoidal.LWS.SearchResults`). lws10-index defines no such resource; the
path is a server choice and is likely to change. -/
def searchResultsPrefix : String := typeSearchPath ++ "/results/"

/-- The path of the search results resource with this identifier. -/
def searchResultsPath (id : String) : String := searchResultsPrefix ++ id

/-- The identifier a search results path names (the text after the prefix). -/
def searchResultsIdOf (p : String) : String :=
  String.ofList (p.toList.drop searchResultsPrefix.length)

/-- Is the path a search results resource: the prefix, then an identifier of
base64url characters (RFC 4648 §5) only? -/
def isSearchResultsPath (p : String) : Bool :=
  p.startsWith searchResultsPrefix &&
    (searchResultsIdOf p != "" &&
     (searchResultsIdOf p).all (fun c => c.isAlphanum || c == '-' || c == '_'))

/-- The extension member of the `TypeSearchService` entry of the storage
description when the search results resources are on. It is a full IRI, so
it is no LWS term, and it says what it is: anticipatory, unstable, not
defined by lws10-index. -/
def unstableResultsMember : String :=
  "https://github.com/danbri/factoidal/issues/922#unstableResultsResource"

/-- The baseline filter format of the Type Search Service (lws10-index
§IANA Considerations). -/
def mediaLwsQuery : String := "application/lws-query+json"

/-- The subscription type of the webhook notification suite (LWS 1.0
Notification Suite: Webhooks, §Subscription Type Identifier: "A Webhook
subscription MUST use the WebhookSubscription string"). -/
def webhookSubscriptionType : String := "WebhookSubscription"

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
  | 410 => "Gone"
  | 412 => "Precondition Failed"
  | 415 => "Unsupported Media Type"
  | 416 => "Range Not Satisfiable"
  | 422 => "Unprocessable Content"
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
     , ("instance", .string target) ]), none⟩

/-! ## Dates -/

private def pad2 (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n
private def pad4 (n : Nat) : String :=
  if n < 10 then "000" ++ toString n
  else if n < 100 then "00" ++ toString n
  else if n < 1000 then "0" ++ toString n
  else toString n

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

/-- FNV-1a, 32 bits, over a byte region: the offset basis 2166136261 and the
prime 16777619 of the FNV specification (draft-eastlake-fnv). A content
digest for entity tags, not a cryptographic one.

This is the reference definition, over `Nat`. It is not the one that runs:
on wasm32 a `Nat` above 2^31 - 1 is a heap number, so each byte allocated
two of them, and this fold was most of the cost of an LWS PUT or GET of a
large body (https://github.com/danbri/factoidal/issues/903). `fnv1a32`
below runs `fnv1a32U32`, and theorem `fnv1a32_eq_spec` says the two agree. -/
def fnv1a32Spec (b : ByteArray) : Nat :=
  b.foldl (fun h x => ((h ^^^ x.toNat) * 16777619) % 4294967296) 2166136261

/-- FNV-1a, 32 bits, in `UInt32` arithmetic: multiplication modulo 2^32 is
`UInt32` multiplication, so no number leaves the machine word. -/
def fnv1a32U32 (b : ByteArray) : UInt32 :=
  b.foldl (fun h x => (h ^^^ x.toUInt32) * 16777619) 2166136261

/-- `ByteArray.foldl` commutes with a map that commutes with one step. -/
private theorem foldlLoop_hom {α β : Type} (f : α → β) (g₁ : α → UInt8 → α)
    (g₂ : β → UInt8 → β) (hg : ∀ x y, g₂ (f x) y = f (g₁ x y)) (as : ByteArray)
    (stop : Nat) (hs : stop ≤ as.size) :
    ∀ (i j : Nat) (x : α),
      ByteArray.foldlM.loop (m := Id) (fun b y => pure (g₂ b y)) as stop hs i j (f x)
        = f (ByteArray.foldlM.loop (m := Id) (fun b y => pure (g₁ b y)) as stop hs i j x) := by
  intro i
  induction i with
  | zero =>
    intro j x
    unfold ByteArray.foldlM.loop
    split <;> rfl
  | succ n ih =>
    intro j x
    unfold ByteArray.foldlM.loop
    split
    · simp only [bind, pure]
      rw [hg]
      exact ih (j + 1) (g₁ x as[j])
    · rfl

private theorem byteArrayFoldl_hom {α β : Type} (f : α → β) (g₁ : α → UInt8 → α)
    (g₂ : β → UInt8 → β) (hg : ∀ x y, g₂ (f x) y = f (g₁ x y)) (as : ByteArray) (x : α) :
    as.foldl g₂ (f x) = f (as.foldl g₁ x) := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [Nat.le_refl, dite_true]
  exact foldlLoop_hom f g₁ g₂ hg as as.size (Nat.le_refl _) _ _ x

/-- FNV-1a, 32 bits, as a `Nat`: the value of `fnv1a32Spec`, computed by
`fnv1a32U32`. -/
def fnv1a32 (b : ByteArray) : Nat := (fnv1a32U32 b).toNat

theorem fnv1a32_eq_spec (b : ByteArray) : fnv1a32 b = fnv1a32Spec b := by
  unfold fnv1a32 fnv1a32U32 fnv1a32Spec
  have := byteArrayFoldl_hom (fun (h : UInt32) => h.toNat)
    (fun h x => (h ^^^ x.toUInt32) * 16777619)
    (fun h x => ((h ^^^ x.toNat) * 16777619) % 4294967296)
    (by intro h y; simp [UInt32.toNat_mul, UInt32.toNat_xor, UInt8.toNat_toUInt32])
    b 2166136261
  simpa using this.symm

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Eight lower-case hexadecimal digits of a 32-bit value. -/
def hex8 (n : Nat) : String :=
  String.ofList ((List.range 8).reverse.map (fun i => hexDigit (n / 16 ^ i % 16)))

/-- The tag of a data resource: its modification clock and the FNV-1a digest
of its bytes, so the tag is computed on the representation data that RFC 9110
§8.8.3 says a strong validator changes with
(https://github.com/danbri/factoidal/issues/889).

For a container this is only the prefix of a tag (the clock and the media
suffix); the tag a container sends is `containerTag`, which adds the digest
of the listing. -/
def etagFor (e : Entry) (media : String) : String :=
  "\"" ++ toString e.mtime ++
    (if e.kind.isContainer then mediaTagSuffix media else "-" ++ hex8 (fnv1a32 e.body)) ++ "\""

/-- The tag of one representation of a container: its clock, the media
suffix, and the FNV-1a digest of `body`, the representation in that media
type. The listing changes when a member is added, removed or changed (its
`size`, `format` or `modified`), so the tag changes with it, also when the
clock does not (https://github.com/danbri/factoidal/issues/911, F3). -/
def containerTag (e : Entry) (media body : String) : String :=
  "\"" ++ toString e.mtime ++ mediaTagSuffix media ++ "-" ++ hex8 (fnv1a32 body.toUTF8) ++ "\""

/-- The container media types this binding serves, server preference first. -/
def containerMedia : List String := [mediaLwsJson, "application/ld+json", "text/turtle"]

private def trimSp (s : String) : String :=
  String.ofList (((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse)

/-- The entity tags of an `If-Match` or `If-None-Match` field value. -/
def parseTagList (v : String) : List String :=
  (v.splitOn ",").map trimSp |>.filter (· != "")

private def stripWeak (t : String) : String :=
  if t.startsWith "W/" then String.ofList (t.toList.drop 2) else t

/-- RFC 9110 §13.1.1: `If-Match` uses the strong comparison; `*` matches any
current representation. `tags` are the current tags of the selected
resource; `present` says whether it has a current representation. -/
def ifMatchHolds (v : String) (present : Bool) (tags : List String) : Bool :=
  if !present then false
  else
    let ts := parseTagList v
    ts.contains "*" || ts.any (fun t => !t.startsWith "W/" && tags.contains t)

/-- RFC 9110 §13.1.2: `If-None-Match` uses the weak comparison. The
condition HOLDS when no listed tag matches. -/
def ifNoneMatchHolds (v : String) (present : Bool) (tags : List String) : Bool :=
  if !present then true
  else
    let ts := parseTagList v
    !(ts.contains "*" || ts.any (fun t => tags.contains (stripWeak t)))

/-- RFC 9110 §13.1.4, If-Unmodified-Since: "If the selected representation's
last modification date is earlier than or equal to the date provided in the
field value, the condition is true." A value that is not an HTTP-date is
ignored ("A recipient MUST ignore the If-Unmodified-Since header field if
the received field value is not a valid HTTP-date"), and so is the field
when the resource has no modification date. `none`: ignored. -/
def ifUnmodifiedSinceHolds (now : Nat) (v : String) (lastModified : Option Nat) : Option Bool :=
  match lastModified, parseHttpDate now v with
  | some lm, some d => some (decide ((lm : Int) ≤ d))
  | _, _ => none

/-- RFC 9110 §13.1.3, If-Modified-Since: "If the selected representation's
last modification date is earlier or equal to the date provided in the
field value, the condition is false." A value that is not an HTTP-date is
ignored. `none`: ignored. -/
def ifModifiedSinceHolds (now : Nat) (v : String) (lastModified : Option Nat) : Option Bool :=
  match lastModified, parseHttpDate now v with
  | some lm, some d => some (!decide ((lm : Int) ≤ d))
  | _, _ => none

/-- Evaluate the preconditions of a request in the order of RFC 9110
§13.2.2, returning the response that ends the request when one fails:

1. `If-Match` (§13.1.1): 412 when false.
2. Without `If-Match`, `If-Unmodified-Since` (§13.1.4), for every method:
   412 when false. "An origin server that evaluates an If-Unmodified-Since
   condition MUST NOT perform the requested method if the condition
   evaluates to false."
3. `If-None-Match` (§13.1.2): 304 for GET and HEAD, 412 otherwise.
4. Without `If-None-Match`, for GET and HEAD, `If-Modified-Since`
   (§13.1.3): 304 when false.

The dates are compared as instants (`parseHttpDate`), in any of the three
HTTP-date formats. `tags` are the current tags of the selected resource
(one page of a paginated container has its own tag); `lastModified` is its
modification time in seconds since the epoch, and `lastModifiedText` the
`Last-Modified` value a 304 repeats; `now` reads a two-digit rfc850 year. -/
def preconditionFailure (r : Request) (now : Nat) (present : Bool) (tag : Option String)
    (lastModified : Option Nat) (lastModifiedText : Option String) (tags : List String) :
    Option Response :=
  let safe := r.method == "GET" || r.method == "HEAD"
  let notModified : Response :=
    ⟨304, (match tag with | some t => [("etag", t)] | none => []) ++
          (match lastModifiedText with | some d => [("last-modified", d)] | none => []),
     "", none⟩
  (match r.header? "if-match" with
   | some v =>
       if !ifMatchHolds v present tags then
         some (problem 412 "If-Match did not match a current representation" r.path)
       else none
   | none =>
       match r.header? "if-unmodified-since" with
       | some v =>
           if ifUnmodifiedSinceHolds now v lastModified == some false then
             some (problem 412 "the resource was modified after the If-Unmodified-Since date"
               r.path)
           else none
       | none => none)
  |>.orElse fun _ =>
  match r.header? "if-none-match" with
  | some v =>
      if ifNoneMatchHolds v present tags then none
      else if safe then some notModified
      else some (problem 412 "If-None-Match matched a current representation" r.path)
  | none =>
      if safe then
        match r.header? "if-modified-since" with
        | some v =>
            if ifModifiedSinceHolds now v lastModified == some false then some notModified
            else none
        | none => none
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

/-- The bytes of the inclusive byte range `first`-`last` of `body`
(RFC 9110 §14.1.2: "byte offsets ... are inclusive"). The range is a range
of BYTES of the representation data, so it may begin or end inside a UTF-8
sequence; that is what a client resuming a download asks for
(https://github.com/danbri/factoidal/issues/889). -/
def rangeBytes (body : ByteArray) (first last : Nat) : ByteArray :=
  body.extract first (last + 1)

/-- `rangeBytes` is the slice: the bytes at offsets `first` through `last`
of `body`, in order. -/
theorem rangeBytes_toList (body : ByteArray) (first last : Nat) :
    (rangeBytes body first last).data.toList =
      (body.data.toList.drop first).take (last + 1 - first) := by
  simp [rangeBytes, ByteArray.data_extract, Array.toList_extract, List.extract]

theorem rangeBytes_size (body : ByteArray) (first last : Nat) (h : last < body.size) :
    (rangeBytes body first last).size = last + 1 - first := by
  simp [rangeBytes, ByteArray.size_extract]; omega

/-- A satisfiable range that `parseRange` answers lies inside the
representation: `first ≤ last < len` (RFC 9110 §14.1.1, a satisfiable
range). -/
theorem parseRange_bounds {v : String} {len a b : Nat}
    (h : parseRange v len = some (some (a, b))) : a ≤ b ∧ b < len := by
  unfold parseRange at h
  simp only at h
  repeat' split at h
  all_goals (simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h)
  all_goals (simp only [Bool.or_eq_true, beq_iff_eq, not_or] at *; omega)

/-- Range selection returns exactly the requested slice: when the `Range`
field `v` names the satisfiable range `a`-`b` of `body`, the content of the
206 has `b - a + 1` bytes and they are the bytes of `body` at offsets `a`
through `b`. `Operations.stepPath` answers `rangeBytes e.body a b` for that
case. -/
theorem range_selection_exact {v : String} {body : ByteArray} {a b : Nat}
    (h : parseRange v body.size = some (some (a, b))) :
    a ≤ b ∧ b < body.size ∧
    (rangeBytes body a b).size = b + 1 - a ∧
    (rangeBytes body a b).data.toList = (body.data.toList.drop a).take (b + 1 - a) := by
  have hb := parseRange_bounds h
  exact ⟨hb.1, hb.2, rangeBytes_size body a b hb.2, rangeBytes_toList body a b⟩

/-! ## RDF content is UTF-8 -/

/-- The media types whose content this storage reads as RDF text. Each one's
specification fixes the encoding as UTF-8: RDF 1.1 Turtle §2 "The encoding
for Turtle is always UTF-8", N-Triples §2 and N-Quads §2 "the encoding is
always UTF-8", TriG §2 the same as Turtle, JSON-LD 1.1 §C (application/ld+json
is JSON, and RFC 8259 §8.1 "JSON text exchanged between systems ... MUST be
encoded using UTF-8"), and Notation3 ("N3 files are always UTF-8"). The
storage stores every other media type byte for byte. -/
def rdfTextMedia : List String :=
  [ "text/turtle", "application/n-triples", "application/n-quads", "application/trig"
  , "application/ld+json", "text/n3", mediaJsonPatch ]

/-- The media type of a `Content-Type` field value, without parameters and
in lower case. -/
def baseMedia (ct : String) : String := (((ct.splitOn ";").headD ct).trim).toLower

/-- Is content of this `Content-Type` read as UTF-8 text by the storage? -/
def isRdfTextMedia (ct : String) : Bool := rdfTextMedia.contains (baseMedia ct)

/-- The 400 for content declared as an RDF text media type whose bytes are not
UTF-8. RFC 9110 §15.5.1: "400 (Bad Request) ... the server cannot or will
not process the request due to something that is perceived to be a client
error (e.g., malformed request syntax ...)". The media type is supported, so
the refusal is not 415; the content is malformed for it, so it is 400. -/
def rdfContentRefused (ct : String) (content : ByteArray) (target : String) :
    Option Response :=
  if isRdfTextMedia ct && (String.fromUTF8? content).isNone then
    some (problem 400 ("the content is not UTF-8, which " ++ baseMedia ct ++ " requires") target)
  else none

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
      , ("size", .number (toString e.body.size)) ]) ++
    [ ("modified", .string (isoDateTime e.mtime)) ])

/-- The `application/lws+json` representation of a container. `total` is
the size of the full membership when `items` is one page of it (§LWS Media
Type, Pagination: "`totalItems` properties reflect the full membership,
while `items` contains only the resources on the current page"). -/
def containerJson (baseIri path : String) (items : List Entry) (total : Option Nat := none) : String :=
  toStringCompact (.object
    [ ("@context", .string lwsProfile)
    , ("id", .string (iriOfPath baseIri path))
    , ("type", .string "Container")
    , ("totalItems", .number (toString (total.getD items.length)))
    , ("items", .array (items.map (itemJson baseIri))) ])

private def ttlString (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else if c == '\r' then acc ++ "\\r"
    else acc.push c) "" ++ "\""

private def ttlIri (s : String) : String := "<" ++ s ++ ">"

/-- The Turtle representation in the LWS profile: the same RDF the
`application/lws+json` representation encodes. lws10-core
`lws-media-type.md` §LWS Profile: "it MUST be RDF isomorphic to the
`application/lws+json` representation".

`schema:` is `http://schema.org/`, the namespace the `application/lws+json`
context `https://www.w3.org/ns/lws/v1` gives `size`
(https://github.com/danbri/factoidal/issues/911, F2). The W3C LWS WG
documents disagree (w3c/lws-protocol 9a08ff65):

* `lws10-core/container-representation.md` (the Turtle and N-Triples tabs
  of the container example) and `lws10-core/Operations/read-resource.md`
  use `http://schema.org/`; the 2026-07-14 vocabulary snapshot
  `lws10-vocab/SNAPSHOTS/DNOTE-lws10-vocab-20260714/vocabulary.jsonld`
  maps `schema` to `http://schema.org/`; Touchstone's copy of the context
  maps `size` to `http://schema.org/size`.
* `lws10-vocab/vocabulary.yml` (the current vocabulary source) declares
  the prefix `schema: https://schema.org/`.

The context URL answers 404 today. This module follows the core draft, the
document whose media type is under test, and the context the draft's JSON
form refers to; the conflict is for the WG to settle.

A contained CONTAINER gets no `dcterms:modified` here, although its JSON item
has `modified` (§Contained Resource Description: "SHOULD include ...
`modified`"). The vocabulary gives `dcterms:modified` (and `format`, `size`)
the domain `lws:DataResource` (`lws10-vocab/vocabulary.yml`), so the context
defines the term `modified` only in the type-scoped context of
`DataResource`, and a `Container` item's `modified` maps to no triple. The
Turtle form must give the same RDF (Touchstone,
`core/containers#container-lws-profile-turtle`: 10 quads against 9 while
this line was written; https://github.com/danbri/factoidal/issues/911). -/
def containerTurtle (baseIri path : String) (items : List Entry) (total : Option Nat := none) : String :=
  let header :=
    "@prefix lws: <https://www.w3.org/ns/lws#> .\n" ++
    "@prefix dcterms: <http://purl.org/dc/terms/> .\n" ++
    "@prefix schema: <http://schema.org/> .\n" ++
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\n"
  let self := ttlIri (iriOfPath baseIri path) ++ " a lws:Container ;\n  lws:totalItems " ++
    toString (total.getD items.length) ++
    (if items.isEmpty then " .\n"
     else " ;\n  lws:items " ++
       String.intercalate ", " (items.map (fun e => ttlIri (iriOfPath baseIri e.path))) ++ " .\n")
  let item (e : Entry) : String :=
    ttlIri (iriOfPath baseIri e.path) ++
    (if e.kind.isContainer then " a lws:Container .\n"
     else " a lws:DataResource ;\n  dcterms:format " ++ ttlString e.contentType ++
       " ;\n  schema:size \"" ++ toString e.body.size ++ "\"^^xsd:long ;\n" ++
       "  dcterms:modified \"" ++ isoDateTime e.mtime ++ "\"^^xsd:dateTime .\n")
  header ++ self ++ String.join (items.map item)

/-- The `Content-Type` value of a container representation in a media type. -/
def containerContentType (media : String) : String :=
  if media == mediaLwsJson then mediaLwsJson
  else media ++ "; profile=\"" ++ lwsProfile ++ "\""

/-- The container representation in a negotiated media type. -/
def containerBody (media baseIri path : String) (items : List Entry) (total : Option Nat := none) :
    String :=
  if media == "text/turtle" then containerTurtle baseIri path items total
  else containerJson baseIri path items total

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

/-- The identifier of the storage: the storage description IRI. It is the
target of every `lws#storage` link, the `id` of the description, and the
`storage` member of a notification envelope. -/
def storageIdOf (baseIri : String) : String := iriOfPath baseIri storagePath

/-- The verification method identifier of the notification signing key
whose public key is the base64url string `x`. The webhook suite
(§Signature Verification) requires a `keyid` that "MUST be a URL with a
fragment component" whose fragment-free part is the storage identifier; the
fragment carries a digest of the key, so a new key gets a new identifier. -/
def notificationKeyId (baseIri x : String) : String :=
  storageIdOf baseIri ++ "#notification-key-" ++ hex8 (fnv1a32 x.toUTF8)

/-- The `MoveResource` capability (§Storage Capabilities; moves are decided
by `L4Factoidal.LWS.Move`): data resources move, and containers too when
`containers` holds (§Moving Resources: a server that does not move
containers "MUST NOT include Container in the `appliesTo` property"); a
moved resource gets a new identifier. -/
def moveCapability (containers : Bool := true) : Json :=
  .object [ ("type", .string "MoveResource")
          , ("appliesTo", .array ([.string "DataResource"] ++
              (if containers then [.string "Container"] else [])))
          , ("preservesIdentifier", .bool false) ]

#guard (moveCapability true).field? "appliesTo" == some (.array [.string "DataResource", .string "Container"])
#guard (moveCapability false).field? "appliesTo" == some (.array [.string "DataResource"])

/-- The storage description (§Discovery, "Storage Description Resource"),
serialised as `application/lws+cid`. With `move`, it describes the
`MoveResource` capability; without it, none, and a change of an `up` link
is refused (§Moving Resources: "A server that does not allow it MUST reject
the request [...] and MUST NOT describe a `MoveResource` capability").

With `notify`, the description also carries the `NotificationService` of
LWS §Notification Discovery ("A storage that supports notifications MUST
advertise a service object in the service array of its storage description
resource with type equal to NotificationService", with a `serviceEndpoint`
and a `subscriptionType` array). With `keyX`, the base64url Ed25519 public
key that signs webhook deliveries, it carries that key as a `JsonWebKey`
verification method referenced from `authentication`, as the webhook
suite's §Webhook Authentication requires of "A server that supports HTTP
Message Signatures".

With `typeIndex`, the description also carries a `TypeIndexService` and a
`TypeSearchService` (lws10-index §Discovery: "A storage that supports one of
these services MUST advertise it with a service object in the service array
of its storage description resource" and "Each service object MUST include a
serviceEndpoint property"). -/
def storageDescription (baseIri : String) (notify : Bool := false)
    (keyX : Option String := none) (move : Bool := false) (typeIndex : Bool := false)
    (access : Bool := false) (results : Bool := false) (moveContainers : Bool := true) : String :=
  let sid := storageIdOf baseIri
  let keyMembers : List (String × Json) :=
    match notify, keyX with
    | true, some x =>
        let kid := notificationKeyId baseIri x
        [ ("verificationMethod", .array [ .object
            [ ("id", .string kid)
            , ("type", .string "JsonWebKey")
            , ("controller", .string sid)
            , ("publicKeyJwk", .object
                [ ("kty", .string "OKP"), ("crv", .string "Ed25519"), ("x", .string x) ]) ] ])
        , ("authentication", .array [.string kid]) ]
    | _, _ => []
  let notifService : List Json :=
    if notify then
      [ .object
        [ ("type", .string "NotificationService")
        , ("serviceEndpoint", .string (iriOfPath baseIri subscriptionsPath))
        , ("subscriptionType", .array [.string webhookSubscriptionType]) ] ]
    else []
  let indexServices : List Json :=
    if typeIndex then
      [ .object [ ("type", .string "TypeIndexService")
                , ("serviceEndpoint", .string (iriOfPath baseIri typeIndexPath)) ]
      , .object ([ ("type", .string "TypeSearchService")
                 , ("serviceEndpoint", .string (iriOfPath baseIri typeSearchPath)) ] ++
          -- ANTICIPATORY AND UNSTABLE (issue 922): an extension member, not
          -- a service type, so a client that knows only lws10-index sees the
          -- standard TypeSearchService entry.
          (if results then
            [ (unstableResultsMember, .string ("anticipatory and unstable: a QUERY answer " ++
                "carries Content-Location (RFC 10008 section 2.3) naming a results " ++
                "resource that lws10-index does not define; likely to change")) ]
           else [])) ]
    else []
  -- LWS §Access Requests and Grants, Discovery: "a service object
  -- describing an endpoint for access requests MUST have a type equal to
  -- the string AccessRequestService, and a service object describing an
  -- endpoint for access grants MUST have a type equal to the string
  -- AccessGrantService. A service object SHOULD include a conformsTo
  -- property whose value is a collection of one or more URIs identifying
  -- the access profiles supported at that endpoint."
  let accessServices : List Json :=
    if access then
      [ .object [ ("type", .string "AccessRequestService")
                , ("serviceEndpoint", .string (iriOfPath baseIri accessRequestsPath))
                , ("conformsTo", .array [.string lwsAccessProfile]) ]
      , .object [ ("type", .string "AccessGrantService")
                , ("serviceEndpoint", .string (iriOfPath baseIri accessGrantsPath))
                , ("conformsTo", .array [.string lwsAccessProfile]) ] ]
    else []
  toStringCompact (.object (
    [ ("@context", .array [.string cidContext, .string lwsProfile])
    , ("id", .string sid)
    , ("type", .string "Storage") ] ++ keyMembers ++
    (if move then [("capability", .array [moveCapability moveContainers])] else []) ++
    [ ("service", .array ([ .object
        [ ("type", .string "StorageRoot")
        , ("serviceEndpoint", .string (iriOfPath baseIri rootPath)) ] ] ++ notifService ++
        indexServices ++ accessServices)) ]))

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
